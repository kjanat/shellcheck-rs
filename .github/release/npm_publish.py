"""Publish the exact verified npm archives; safely resume partial publication."""

import argparse
import base64
import hashlib
import json
import subprocess
from pathlib import Path

from binding_packages import load_record, members
from binding_packages import verify as verify_bindings
from native_packages import MANIFEST
from native_packages import verify as verify_native


def integrity(path):
    return (
        "sha512-"
        + base64.b64encode(hashlib.sha512(path.read_bytes()).digest()).decode()
    )


def publish_one(path):
    manifest = json.loads(members(path)["package/package.json"])
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
        capture_output=True,
        text=True,
    )
    if result.returncode == 0:
        if json.loads(result.stdout) != integrity(path):
            raise ValueError(f"{spec} already exists with different contents")
        print(f"{spec}: identical archive already published", flush=True)
        return
    try:
        code = json.loads(result.stdout)["error"]["code"]
    except (ValueError, KeyError, TypeError):
        raise RuntimeError(
            f"Cannot check npm package {spec}: {result.stderr}"
        ) from None
    if code != "E404":
        raise RuntimeError(f"Cannot check npm package {spec}: {result.stderr}")
    tag = "next" if "-" in manifest["version"] else "latest"
    subprocess.run(
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
    )
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
    )
    if json.loads(actual) != integrity(path):
        raise ValueError(f"{spec}: registry integrity does not match published archive")


def publish(dest):
    verify_bindings(dest)
    verify_native(dest)
    # Platform dependencies precede the wrapper so it is installable when visible.
    native = json.loads((dest / MANIFEST).read_text())["packages"]
    for package in native:
        publish_one(dest / package["file"])
    for package in load_record(dest)["packages"]:
        if package["kind"] == "npm":
            publish_one(dest / package["name"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    publish(parser.parse_args().directory)
