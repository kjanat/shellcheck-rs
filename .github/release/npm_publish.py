"""Publish the exact verified npm archives; safely resume partial publication."""

import argparse
import base64
import hashlib
import json
import subprocess
import time
from pathlib import Path
from typing import cast

from binding_packages import load_record, members
from binding_packages import verify as verify_bindings
from native_packages import load_record as load_native_record
from native_packages import verify as verify_native


def integrity(path: Path) -> str:
    return (
        "sha512-"
        + base64.b64encode(hashlib.sha512(path.read_bytes()).digest()).decode()
    )


def publish_one(path: Path) -> None:
    manifest = cast(dict[str, str], json.loads(members(path)["package/package.json"]))
    spec = f"{manifest['name']}@{manifest['version']}"
    result = subprocess.run(
        [
            "npm",
            "view",
            spec,
            "dist.integrity",
            "--json",
            "--registry=https://registry.npmjs.org",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode == 0:
        if json.loads(result.stdout) != integrity(path):
            raise ValueError(f"{spec} already exists with different contents")
        print(f"{spec}: identical archive already published", flush=True)
        return
    try:
        code = cast(dict[str, dict[str, str]], json.loads(result.stdout))["error"][
            "code"
        ]
    except (ValueError, KeyError, TypeError):
        raise RuntimeError(
            f"Cannot check npm package {spec}: {result.stderr}"
        ) from None
    if code != "E404":
        raise RuntimeError(f"Cannot check npm package {spec}: {result.stderr}")
    tag = "next" if "-" in manifest["version"] else "latest"
    try:
        published = subprocess.run(
            [
                "npm",
                "publish",
                str(path.resolve()),
                "--access=public",
                "--provenance",
                "--tag",
                tag,
                "--registry=https://registry.npmjs.org",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        print(published.stdout or "", end="", flush=True)
        print(published.stderr or "", end="", flush=True)
    except subprocess.CalledProcessError as error:
        message = cast(str, error.stderr) or ""
        if (
            "E403" not in message
            or "You cannot publish over the previously published versions:"
            not in message
        ):
            print(message, flush=True)
            raise
        print(
            f"{spec}: npm already accepted this version; verifying its integrity",
            flush=True,
        )
    wait_for_integrity(spec, integrity(path))


def wait_for_integrity(spec: str, expected: str) -> None:
    for attempt in range(31):
        try:
            actual = subprocess.check_output(
                [
                    "npm",
                    "view",
                    spec,
                    "dist.integrity",
                    "--json",
                    "--registry=https://registry.npmjs.org",
                ],
                text=True,
                stderr=subprocess.PIPE,
                timeout=30,
            )
        except subprocess.CalledProcessError as error:
            try:
                code = cast(
                    dict[str, dict[str, str]], json.loads(cast(str, error.output))
                )["error"]["code"]
            except (ValueError, KeyError, TypeError):
                raise error from None
            if code != "E404":
                raise
            if attempt == 30:
                raise TimeoutError(
                    f"{spec}: npm still processing after 5 minutes"
                ) from error
            print(
                f"{spec}: waiting for npm registry visibility ({attempt + 1}/30)",
                flush=True,
            )
            time.sleep(10)
            continue
        if json.loads(actual) != expected:
            raise ValueError(
                f"{spec}: registry integrity does not match published archive"
            )
        return


def publish(dest: Path) -> None:
    verify_bindings(dest)
    verify_native(dest)
    # Platform dependencies precede the wrapper so it is installable when visible.
    native = load_native_record(dest)["packages"]
    for package in native:
        publish_one(dest / package["file"])
    for package in load_record(dest)["packages"]:
        if package["kind"] == "npm":
            publish_one(dest / package["name"])


class Args(argparse.Namespace):
    directory: Path = Path()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("directory", type=Path)
    publish(parser.parse_args(namespace=Args()).directory)
