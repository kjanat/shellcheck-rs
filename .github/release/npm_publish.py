"""Publish the exact verified npm archives; safely resume partial publication."""

import argparse
import base64
import hashlib
import json
import os
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import cast

from binding_packages import load_record, members
from binding_packages import verify as verify_bindings
from native_packages import load_record as load_native_record
from native_packages import verify as verify_native
from registry_checks import NotVisibleYet, retry_read


def integrity(path: Path) -> str:
    return (
        "sha512-"
        + base64.b64encode(hashlib.sha512(path.read_bytes()).digest()).decode()
    )


def registry_integrity(spec: str, wait_missing: bool = False) -> str | None:
    def read(timeout: float) -> str | None:
        try:
            result = subprocess.run(
                [
                    "npm",
                    "view",
                    spec,
                    "dist.integrity",
                    "--json",
                    "--registry=https://registry.npmjs.org",
                    "--fetch-retries=0",
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as error:
            raise NotVisibleYet("npm view timed out") from error
        if result.returncode == 0:
            value = json.loads(result.stdout)
            if not isinstance(value, str) or not value:
                raise NotVisibleYet("integrity not yet visible")
            return value
        try:
            code = cast(dict[str, dict[str, str]], json.loads(result.stdout))["error"][
                "code"
            ]
        except (ValueError, KeyError, TypeError):
            raise RuntimeError(f"Cannot check {spec}: {result.stderr}") from None
        if code == "E404" and not wait_missing:
            return None
        if (
            code == "E404"
            or code
            in {
                "E408",
                "E429",
                "ETIMEDOUT",
                "ESOCKETTIMEDOUT",
                "ECONNRESET",
                "ECONNREFUSED",
                "EAI_AGAIN",
                "ENETUNREACH",
            }
            or (len(code) == 4 and code.startswith("E5") and code[1:].isdigit())
        ):
            raise NotVisibleYet(code)
        raise RuntimeError(f"Cannot check {spec}: {result.stderr}")

    return retry_read(spec, read, seconds=600 if wait_missing else 60)


def package_spec(path: Path) -> str:
    manifest = cast(dict[str, str], json.loads(members(path)["package/package.json"]))
    return f"{manifest['name']}@{manifest['version']}"


def already_published(path: Path) -> bool:
    spec = package_spec(path)
    actual = registry_integrity(spec)
    if actual is None:
        return False
    if actual != integrity(path):
        raise ValueError(f"{spec} already exists with different contents")
    print(f"{spec}: identical archive already published", flush=True)
    return True


def publish_one(path: Path) -> None:
    spec = package_spec(path)
    if already_published(path):
        return
    version = spec.rsplit("@", 1)[1]
    tag = "next" if "-" in version else "latest"
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
            timeout=120,
        )
        print(published.stdout or "", end="", flush=True)
        print(published.stderr or "", end="", flush=True)
    except subprocess.TimeoutExpired:
        print(
            f"{spec}: upload response timed out; checking registry before any retry",
            flush=True,
        )
    except subprocess.CalledProcessError as error:
        message = cast(str, error.stderr) or ""
        already_accepted = (
            "E403" in message
            and "You cannot publish over the previously published versions:" in message
        ) or (
            "E409" in message
            and "Cannot publish over previously staged version" in message
        )
        if not already_accepted:
            print(message, flush=True)
            raise
        print(
            f"{spec}: npm already accepted this version; verifying its integrity",
            flush=True,
        )
    wait_for_integrity(spec, integrity(path))


def wait_for_integrity(spec: str, expected: str) -> None:
    if registry_integrity(spec, wait_missing=True) != expected:
        raise ValueError(f"{spec}: registry integrity does not match published archive")


def archives(dest: Path) -> list[Path]:
    verify_bindings(dest)
    verify_native(dest)
    # In the workflow each dependency has its own job; the launcher runs last.
    paths = [dest / p["file"] for p in load_native_record(dest)["packages"]]
    paths.extend(
        dest / p["name"] for p in load_record(dest)["packages"] if p["kind"] == "npm"
    )
    return paths


def plan(dest: Path) -> dict[str, str]:
    paths = archives(dest)
    with ThreadPoolExecutor(max_workers=8) as pool:
        present = list(pool.map(already_published, paths))
    missing = [
        package_spec(p).rsplit("@", 1)[0]
        for p, exists in zip(paths, present, strict=True)
        if not exists
    ]
    native = [name for name in missing if name.startswith("@rshellcheck/")]
    print(
        f"npm: {sum(present)}/{len(paths)} identical packages already published; {len(missing)} missing",
        flush=True,
    )
    return {
        "matrix": json.dumps({"package": native}),
        "native": str(bool(native)).lower(),
        "wasm": str("@kjanat/rshellcheck-wasm" in missing).lower(),
        "launcher": str("@kjanat/rshellcheck" in missing).lower(),
    }


def publish(dest: Path, selected: str | None = None) -> None:
    paths = archives(dest)
    if selected is not None:
        paths = [
            path
            for path in paths
            if json.loads(members(path)["package/package.json"])["name"] == selected
        ]
        if len(paths) != 1:
            raise ValueError(f"Expected exactly one archive for {selected}")
    for path in paths:
        publish_one(path)


class Args(argparse.Namespace):
    directory: Path = Path()
    package: str | None = None
    plan: bool = False


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("directory", type=Path)
    _ = parser.add_argument("--package")
    _ = parser.add_argument("--plan", action="store_true")
    args = parser.parse_args(namespace=Args())
    if args.plan:
        outputs = plan(args.directory)
        if output := os.environ.get("GITHUB_OUTPUT"):
            with Path(output).open("a") as stream:
                for key, value in outputs.items():
                    _ = stream.write(f"{key}={value}\n")
        else:
            print(json.dumps(outputs))
    else:
        publish(args.directory, args.package)
