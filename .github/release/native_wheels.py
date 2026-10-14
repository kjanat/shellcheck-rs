"""Package released native executables as installable platform wheels."""

import argparse
import base64
import hashlib
import json
import os
import platform
import re
import struct
import subprocess
import tempfile
import tomllib
import zipfile
from pathlib import Path
from typing import TypedDict, cast

from binding_packages import members
from registry_checks import verify_pypi
from release import ROOT, Triple, archive_name, git, metadata, smoke, verify_binary

SOURCE = ROOT / "bindings/native/python"
MANIFEST = "native-wheels.json"
TARGETS: dict[Triple, tuple[str, ...]] = {
    "x86_64-pc-windows-msvc": ("win_amd64",),
    "i686-pc-windows-msvc": ("win32",),
    "aarch64-pc-windows-msvc": ("win_arm64",),
    "x86_64-apple-darwin": (),
    "aarch64-apple-darwin": (),
    "x86_64-unknown-linux-musl": ("manylinux_2_17_x86_64", "musllinux_1_1_x86_64"),
    "i686-unknown-linux-musl": ("manylinux_2_17_i686", "musllinux_1_1_i686"),
    "aarch64-unknown-linux-musl": ("manylinux_2_17_aarch64", "musllinux_1_1_aarch64"),
    "armv7-unknown-linux-musleabihf": ("manylinux_2_17_armv7l", "musllinux_1_1_armv7l"),
}


class Package(TypedDict):
    name: str
    sha256: str
    target: Triple
    platform: str


class Record(TypedDict):
    version: str
    commit: str
    packages: list[Package]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_record(dest: Path) -> Record:
    return cast(Record, json.loads((dest / MANIFEST).read_text()))


def macos_tag(data: bytes, target: Triple) -> str:
    if len(data) < 32 or data[:4] != b"\xcf\xfa\xed\xfe":
        raise ValueError("Expected 64-bit Mach-O")
    offset = 32
    version = None
    count = struct.unpack_from("<I", data, 16)[0]
    for _ in range(count):
        command, size = struct.unpack_from("<II", data, offset)
        if size < 8 or offset + size > len(data):
            raise ValueError("Invalid Mach-O load command")
        if command == 0x32 and size >= 24:
            system, minimum = struct.unpack_from("<II", data, offset + 8)
            if system == 1:
                version = minimum
                break
        elif command == 0x24 and size >= 16:
            version = struct.unpack_from("<I", data, offset + 8)[0]
        offset += size
    if version is None:
        raise ValueError("Missing macOS deployment minimum")
    major, minor = version >> 16, (version >> 8) & 255
    if major >= 11 and minor:
        raise ValueError("Cannot represent macOS minor minimum in a wheel tag")
    arch = "arm64" if target.startswith("aarch64") else "x86_64"
    return f"macosx_{major}_{minor}_{arch}"


def wheel(
    dest: Path,
    version: str,
    target: Triple,
    tag: str,
    binary: bytes,
    license_text: bytes,
    build_info: bytes,
) -> Package:
    info = f"rshellcheck-{version}.dist-info"
    executable = "rshellcheck.exe" if "windows" in target else "rshellcheck"
    files = {
        "rshellcheck/__init__.py": (SOURCE / "rshellcheck/__init__.py").read_bytes(),
        f"rshellcheck/bin/{executable}": binary,
        "rshellcheck/BUILD.json": build_info,
        f"{info}/licenses/LICENSE.txt": license_text,
        f"{info}/METADATA": "\n".join([
            "Metadata-Version: 2.4",
            "Name: rshellcheck",
            f"Version: {version}",
            "Summary: Native Rust ShellCheck command-line tool",
            "Requires-Python: >=3.12",
            "License-Expression: GPL-3.0-or-later",
            "License-File: LICENSE.txt",
            "Project-URL: Repository, https://github.com/kjanat/shellcheck-rs",
            "Description-Content-Type: text/markdown",
            "",
            (SOURCE / "README.md").read_text(),
        ]).encode(),
        f"{info}/WHEEL": (
            f"Wheel-Version: 1.0\nGenerator: rshellcheck-release\n"
            f"Root-Is-Purelib: false\nTag: py3-none-{tag}\n"
        ).encode(),
        f"{info}/entry_points.txt": b"[console_scripts]\nrshellcheck = rshellcheck:main\n",
    }
    record_path = f"{info}/RECORD"
    files[record_path] = (
        "".join(
            f"{name},sha256={base64.urlsafe_b64encode(hashlib.sha256(data).digest()).decode().rstrip('=')},{len(data)}\n"
            for name, data in files.items()
        )
        + f"{record_path},,\n"
    ).encode()
    name = f"rshellcheck-{version}-py3-none-{tag}.whl"
    with zipfile.ZipFile(dest / name, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for path, data in files.items():
            entry = zipfile.ZipInfo(path, (1980, 1, 1, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = (0o100755 if "/bin/" in path else 0o100644) << 16
            entry.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(entry, data)
    return {
        "name": name,
        "sha256": digest((dest / name).read_bytes()),
        "target": target,
        "platform": tag,
    }


def build(dest: Path, label: str) -> None:
    meta = metadata()
    version = meta["version"]
    if not re.fullmatch(r"\d+\.\d+\.\d+", version):
        raise ValueError("Native wheels require a stable release version")
    project = tomllib.loads((SOURCE / "pyproject.toml").read_text())
    if project["project"]["version"] != version:
        raise ValueError("Native Python and Rust versions must agree")
    packages: list[Package] = []
    for target, tags in TARGETS.items():
        files = members(dest / archive_name(label, target))
        prefix = f"rshellcheck-{label}-{target}/"
        executable = "rshellcheck.exe" if "windows" in target else "rshellcheck"
        binary = files[prefix + executable]
        build_info = files[prefix + "BUILD.json"]
        expected = {
            **meta,
            "target": target,
            "label": label,
            "binary_sha256": digest(binary),
        }
        actual = cast(dict[str, str], json.loads(build_info))
        if any(actual.get(key) != value for key, value in expected.items()):
            raise ValueError(f"Binary source identity mismatch: {target}")
        verify_binary(binary, target)
        if not tags:
            tags = (macos_tag(binary, target),)
        for tag in tags:
            packages.append(
                wheel(
                    dest,
                    version,
                    target,
                    tag,
                    binary,
                    files[prefix + "LICENSE.txt"],
                    build_info,
                )
            )
    _ = (dest / MANIFEST).write_text(
        json.dumps(
            {
                **meta,
                "packaging_commit": git("rev-parse", "HEAD"),
                "packages": packages,
            },
            indent=2,
        )
        + "\n"
    )
    verify(dest)


def verify(dest: Path) -> None:
    record = load_record(dest)
    meta = metadata()
    if record["commit"] != meta["commit"] or record["version"] != meta["version"]:
        raise ValueError("Native wheels belong to another release")
    if len(record["packages"]) != 13 or {
        p["target"] for p in record["packages"]
    } != set(TARGETS):
        raise ValueError("Incomplete native wheel set")
    names: set[str] = set()
    for package in record["packages"]:
        name = package["name"]
        if Path(name).name != name or name in names:
            raise ValueError("Invalid or duplicate wheel filename")
        names.add(name)
        if digest((dest / name).read_bytes()) != package["sha256"]:
            raise ValueError(f"Wheel checksum mismatch: {name}")
        contents = members(dest / name)
        target = package["target"]
        executable = "rshellcheck.exe" if "windows" in target else "rshellcheck"
        binary = contents[f"rshellcheck/bin/{executable}"]
        info = cast(dict[str, str], json.loads(contents["rshellcheck/BUILD.json"]))
        if any(
            info.get(key) != value
            for key, value in {
                **meta,
                "target": target,
                "binary_sha256": digest(binary),
            }.items()
        ):
            raise ValueError(f"Wrong wheel binary identity: {name}")
        verify_binary(binary, target)
        tags = TARGETS[target] or (macos_tag(binary, target),)
        if (
            package["platform"] not in tags
            or name
            != f"rshellcheck-{meta['version']}-py3-none-{package['platform']}.whl"
        ):
            raise ValueError(f"Wrong wheel platform: {name}")


def test_install(dest: Path) -> None:
    verify(dest)
    with tempfile.TemporaryDirectory() as temp:
        env = Path(temp) / "venv"
        _ = subprocess.run(["uv", "venv", str(env)], check=True)
        bindir = env / ("Scripts" if os.name == "nt" else "bin")
        python = bindir / ("python.exe" if os.name == "nt" else "python")
        _ = subprocess.run(
            [
                "uv",
                "pip",
                "install",
                "--python",
                str(python),
                "--no-index",
                "--no-deps",
                "--find-links",
                str(dest.resolve()),
                f"rshellcheck=={metadata()['version']}",
            ],
            check=True,
        )
        binary = bindir / ("rshellcheck.exe" if os.name == "nt" else "rshellcheck")
        smoke([str(binary)], metadata()["version"])
        print(
            f"Native wheel installed and ran on {platform.system()} {platform.machine()}"
        )


def publish(dest: Path) -> None:
    verify(dest)
    record = load_record(dest)
    _ = subprocess.run(
        [
            "uv",
            "publish",
            "--trusted-publishing",
            "always",
            "--check-url",
            "https://pypi.org/simple/",
            *(str((dest / p["name"]).resolve()) for p in record["packages"]),
        ],
        check=True,
    )
    verify_pypi(
        "rshellcheck",
        record["version"],
        {p["name"]: p["sha256"] for p in record["packages"]},
    )


class Args(argparse.Namespace):
    command: str = ""
    directory: Path = Path()
    label: str | None = None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("command", choices=["build", "verify", "test", "publish"])
    _ = parser.add_argument("directory", type=Path)
    _ = parser.add_argument("--label")
    args = parser.parse_args(namespace=Args())
    if args.command == "build":
        build(args.directory, args.label or metadata()["version"])
    elif args.command == "test":
        test_install(args.directory)
    elif args.command == "publish":
        publish(args.directory)
    else:
        verify(args.directory)
