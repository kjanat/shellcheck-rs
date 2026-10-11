#!/usr/bin/env python3
"""Plan, build, smoke-test and package rshellcheck without third-party Python deps."""

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import struct
import subprocess
import tarfile
import tomllib
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "rshellcheck-v"
CROSS_VERSION = "0.2.5"
NDK_VERSION = "30.0.16248370"
ANDROID_API = 23
# One source of truth for the workflow matrix, archives and completeness gate.
TARGETS = [
    ("x86_64-pc-windows-msvc", "windows-2025", "cargo"),
    ("i686-pc-windows-msvc", "windows-2025", "cargo"),
    ("aarch64-pc-windows-msvc", "windows-11-arm", "cargo"),
    ("x86_64-unknown-linux-musl", "ubuntu-24.04", "cross"),
    ("i686-unknown-linux-musl", "ubuntu-24.04", "cross"),
    ("aarch64-unknown-linux-musl", "ubuntu-24.04", "cross"),
    ("armv7-unknown-linux-musleabihf", "ubuntu-24.04", "cross"),
    ("x86_64-apple-darwin", "macos-15-intel", "cargo"),
    ("aarch64-apple-darwin", "macos-15", "cargo"),
    ("x86_64-unknown-freebsd", "ubuntu-24.04", "cross"),
    ("i686-unknown-freebsd", "ubuntu-24.04", "cross"),
    ("aarch64-linux-android", "ubuntu-24.04", "android"),
    ("armv7-linux-androideabi", "ubuntu-24.04", "android"),
    ("x86_64-linux-android", "ubuntu-24.04", "android"),
    ("i686-linux-android", "ubuntu-24.04", "android"),
]


def run(*args, **kwargs):
    return subprocess.run(args, check=True, cwd=ROOT, **kwargs)


def git(*args):
    return run("git", *args, capture_output=True, text=True).stdout.strip()


def metadata():
    manifests = [
        ROOT / "rust/crates" / crate / "Cargo.toml"
        for crate in ("shellcheck-cli", "shellcheck-rs")
    ]
    versions = [
        tomllib.loads(path.read_text())["package"]["version"] for path in manifests
    ]
    if versions[0] != versions[1]:
        raise ValueError("CLI and library versions must agree")
    version = versions[0]
    if not re.fullmatch(r"\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?", version):
        raise ValueError(f"Unsupported release version: {version}")
    toolchain = tomllib.loads((ROOT / "Cargo.toml").read_text())["workspace"][
        "package"
    ]["rust-version"]
    if toolchain.count(".") == 1:
        toolchain += ".0"
    sha = git("rev-parse", "HEAD")
    return {"version": version, "commit": sha, "rust": toolchain}


def plan(ref="", event=""):
    meta = metadata()
    publishing = event == "push" and ref.startswith("refs/tags/")
    expected = PREFIX + meta["version"]
    if publishing and ref != "refs/tags/" + expected:
        raise ValueError(
            f"Tag must be {expected}, matching both Cargo package versions"
        )
    label = (
        meta["version"]
        if publishing
        else f"{meta['version']}-dev.{meta['commit'][:12]}"
    )
    return {
        **meta,
        "label": label,
        "tag": expected,
        "publish": publishing,
        "cross": CROSS_VERSION,
        "ndk": NDK_VERSION,
        "matrix": {
            "include": [{"target": t, "runner": r, "backend": b} for t, r, b in TARGETS]
        },
    }


def target_info(target):
    return next(
        {"target": t, "runner": r, "backend": b} for t, r, b in TARGETS if t == target
    )


def archive_name(label, target):
    extension = ".zip" if "windows" in target else ".tar.gz"
    return f"rshellcheck-{label}-{target}{extension}"


def verify_binary(data, target):
    """Reject host binaries accidentally packaged under a cross-target filename."""
    arch = target.split("-")[0]
    if "windows" in target:
        if data[:2] != b"MZ":
            raise ValueError("Expected PE executable")
        pe = struct.unpack_from("<I", data, 0x3C)[0]
        machine = {"x86_64": 0x8664, "i686": 0x14C, "aarch64": 0xAA64}[arch]
        valid = (
            data[pe : pe + 4] == b"PE\0\0"
            and struct.unpack_from("<H", data, pe + 4)[0] == machine
        )
    elif "darwin" in target:
        machine = {"x86_64": 0x1000007, "aarch64": 0x100000C}[arch]
        valid = struct.unpack_from("<II", data) == (0xFEEDFACF, machine)
    else:
        machine = {"x86_64": 62, "i686": 3, "aarch64": 183, "armv7": 40}[arch]
        bits = 2 if arch in ("x86_64", "aarch64") else 1
        valid = (
            data[:6] == b"\x7fELF" + bytes([bits, 1])
            and struct.unpack_from("<H", data, 18)[0] == machine
        )
        valid = valid and (data[7] == 9 if "freebsd" in target else data[7] in (0, 3))
        if valid and "musl" in target:
            # Static binaries must not depend on a host ELF interpreter.
            offset, size, count = (28, 42, 44) if bits == 1 else (32, 54, 56)
            phoff = struct.unpack_from("<I" if bits == 1 else "<Q", data, offset)[0]
            phsize, phcount = (
                struct.unpack_from("<H", data, size)[0],
                struct.unpack_from("<H", data, count)[0],
            )
            valid = all(
                struct.unpack_from("<I", data, phoff + i * phsize)[0] != 3
                for i in range(phcount)
            )
    if not valid:
        raise ValueError(
            f"Binary does not match {target} (or musl binary is not static)"
        )


def smoke(command, version):
    env = os.environ.copy()
    env.pop("SHELLCHECK_OPTS", None)
    banner = run(
        *command, "--version", capture_output=True, text=True, env=env, timeout=60
    ).stdout
    if f"version: {version}\n" not in banner:
        raise ValueError("Binary version differs from Cargo version")
    for script, status in [
        ("#!/bin/sh\nprintf '%s\\n' hello\n", 0),
        ("#!/bin/sh\necho $release_probe\n", 1),
    ]:
        result = subprocess.run(
            [*command, "--norc", "-s", "sh", "-f", "json1", "-"],
            input=script,
            capture_output=True,
            text=True,
            env=env,
            cwd=ROOT,
            timeout=60,
            check=False,
        )
        if result.returncode != status or result.stderr:
            raise ValueError(f"Smoke test failed: {result.returncode}: {result.stderr}")
        comments = json.loads(result.stdout)["comments"]
        if (status == 0 and comments) or (
            status == 1 and not any(c["code"] == 2086 for c in comments)
        ):
            raise ValueError("Smoke diagnostic mismatch")


def build(target):
    backend = target_info(target)["backend"]
    env = os.environ.copy()
    if backend == "cross":
        key = target.upper().replace("-", "_")
        env[f"CROSS_TARGET_{key}_IMAGE"] = f"ghcr.io/cross-rs/{target}:{CROSS_VERSION}"
    if backend == "android":
        sdk = Path(os.environ["ANDROID_HOME"])
        ndk = sdk / "ndk" / NDK_VERSION / "toolchains/llvm/prebuilt/linux-x86_64/bin"
        clang_target = target.replace(
            "armv7-linux-androideabi", "armv7a-linux-androideabi"
        )
        linker = ndk / f"{clang_target}{ANDROID_API}-clang"
        if not linker.is_file():
            raise ValueError(f"Missing pinned NDK linker: {linker}")
        key = target.upper().replace("-", "_")
        env[f"CARGO_TARGET_{key}_LINKER"] = str(linker)
    if "windows" in target:
        env["RUSTFLAGS"] = "-Dwarnings -C target-feature=+crt-static"
    if "darwin" in target:
        env["MACOSX_DEPLOYMENT_TARGET"] = "11.0"
    tool = "cross" if backend == "cross" else "cargo"
    run(
        tool,
        "build",
        "--release",
        "--locked",
        "-p",
        "shellcheck-cli",
        "--bin",
        "rshellcheck",
        "--target",
        target,
        env=env,
    )
    binary = (
        ROOT
        / "target"
        / target
        / "release"
        / ("rshellcheck.exe" if "windows" in target else "rshellcheck")
    )
    verify_binary(binary.read_bytes(), target)
    if backend == "cargo" or target in (
        "x86_64-unknown-linux-musl",
        "i686-unknown-linux-musl",
    ):
        smoke([str(binary)], metadata()["version"])
    # Invoke QEMU directly: old cross runners can drop CLI arguments on new Cargo.
    elif "musl" in target:
        smoke(
            [
                "docker",
                "run",
                "--rm",
                "--interactive",
                "--volume",
                f"{binary.parent}:/work:ro",
                "--entrypoint",
                "/usr/local/bin/qemu-aarch64"
                if target.startswith("aarch64")
                else "/usr/local/bin/qemu-arm",
                f"ghcr.io/cross-rs/{target}:{CROSS_VERSION}",
                "/work/rshellcheck",
            ],
            metadata()["version"],
        )


def pack(target, label, binary=None, dest=None):
    meta = metadata()
    binary = binary or ROOT / "target" / target / "release" / (
        "rshellcheck.exe" if "windows" in target else "rshellcheck"
    )
    dest = dest or ROOT / "dist"
    data = binary.read_bytes()
    verify_binary(data, target)
    stem = f"rshellcheck-{label}-{target}"
    readme = (ROOT / ".github/release/README.md").read_text()
    source_url = (
        f"https://github.com/kjanat/shellcheck-rs/blob/{meta['commit']}/.github"
    )
    readme = readme.replace(
        "(../workflows/release.yml)", f"({source_url}/workflows/release.yml)"
    )
    readme = readme.replace("(release.py)", f"({source_url}/release/release.py)")
    files = {
        binary.name: (data, 0o755),
        "LICENSE.txt": ((ROOT / "LICENSE").read_bytes(), 0o644),
        "README.md": (readme.encode(), 0o644),
        "BUILD.json": (
            (
                json.dumps(
                    {
                        **meta,
                        "target": target,
                        "label": label,
                        "binary_sha256": hashlib.sha256(data).hexdigest(),
                    },
                    indent=2,
                )
                + "\n"
            ).encode(),
            0o644,
        ),
    }
    dest.mkdir(parents=True, exist_ok=True)
    archive = dest / archive_name(label, target)
    epoch = int(git("show", "-s", "--format=%ct", "HEAD"))
    if archive.suffix == ".zip":
        with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as output:
            for name, (contents, mode) in sorted(files.items()):
                info = zipfile.ZipInfo(f"{stem}/{name}")
                info.create_system = 3
                info.external_attr = (0o100000 | mode) << 16
                output.writestr(info, contents, compress_type=zipfile.ZIP_DEFLATED)
    else:
        with (
            archive.open("wb") as raw,
            gzip.GzipFile(
                filename="", fileobj=raw, mode="wb", mtime=epoch
            ) as compressed,
            tarfile.open(fileobj=compressed, mode="w") as output,
        ):
            for name, (contents, mode) in sorted(files.items()):
                info = tarfile.TarInfo(f"{stem}/{name}")
                info.size, info.mode, info.mtime = len(contents), mode, epoch
                output.addfile(info, io.BytesIO(contents))
    return archive


def read_member(archive, name):
    file = archive.extractfile(name)
    if file is None:
        raise ValueError(f"{name} is not a regular file")
    return file.read()


def assemble(label, dest=None):
    """Check every target and source identity before making the release payload."""
    dest = dest or ROOT / "dist"
    meta = metadata()
    expected = {archive_name(label, t) for t, _, _ in TARGETS}
    actual = {p.name for p in dest.iterdir()}
    if actual != expected:
        raise ValueError(
            f"Incomplete release: missing={expected - actual}, unexpected={actual - expected}"
        )
    for target, _, _ in TARGETS:
        archive = dest / archive_name(label, target)
        prefix = f"rshellcheck-{label}-{target}/"
        binary = "rshellcheck.exe" if "windows" in target else "rshellcheck"
        if archive.suffix == ".zip":
            with zipfile.ZipFile(archive) as source:
                build_meta = json.loads(source.read(prefix + "BUILD.json"))
                data = source.read(prefix + binary)
        else:
            with tarfile.open(archive) as source:
                build_meta = json.loads(read_member(source, prefix + "BUILD.json"))
                data = read_member(source, prefix + binary)
        for key, value in {
            **meta,
            "label": label,
            "target": target,
            "binary_sha256": hashlib.sha256(data).hexdigest(),
        }.items():
            if build_meta.get(key) != value:
                raise ValueError(f"{archive.name}: mismatched {key}")
        verify_binary(data, target)
    source = dest / f"rshellcheck-{label}-source.tar.gz"
    run(
        "git",
        "archive",
        "--format=tar.gz",
        f"--prefix=rshellcheck-{label}/",
        f"--output={source.resolve()}",
        "HEAD",
    )
    assets = sorted([*expected, source.name])
    checksums = "".join(
        f"{hashlib.sha256((dest / name).read_bytes()).hexdigest()}  {name}\n"
        for name in assets
    )
    (dest / "SHA256SUMS").write_text(checksums, encoding="utf-8")
    return assets


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "build", "pack", "assemble"])
    parser.add_argument("--target", choices=[t for t, _, _ in TARGETS])
    parser.add_argument("--label")
    args = parser.parse_args()
    if args.command == "plan":
        result = plan(
            os.environ.get("GITHUB_REF", ""), os.environ.get("GITHUB_EVENT_NAME", "")
        )
        print(json.dumps(result, indent=2))
        if output := os.environ.get("GITHUB_OUTPUT"):
            with open(output, "a", encoding="utf-8") as stream:
                stream.writelines(
                    f"{key}={json.dumps(value, separators=(',', ':')) if isinstance(value, (dict, bool)) else value}\n"
                    for key, value in result.items()
                )
    elif args.command == "build" and args.target:
        build(args.target)
    elif args.command == "pack" and args.target and args.label:
        pack(args.target, args.label)
    elif args.command == "assemble" and args.label:
        assemble(args.label)
    else:
        parser.error(
            "build needs --target; pack needs --target and --label; assemble needs --label"
        )


if __name__ == "__main__":
    main()
