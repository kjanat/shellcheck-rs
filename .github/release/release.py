#!/usr/bin/env python3
"""Plan, build, smoke-test and package rshellcheck without third-party Python deps."""

import argparse
import datetime
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
from collections.abc import Mapping
from pathlib import Path
from typing import Literal, TypedDict, cast

type JSON = bool | int | float | str | list[JSON] | dict[str, JSON] | None
type TOML = (
    bool
    | int
    | float
    | str
    | datetime.datetime
    | datetime.date
    | datetime.time
    | list[TOML]
    | dict[str, TOML]
)
type Triple = Literal[
    "x86_64-pc-windows-msvc",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
    "x86_64-unknown-linux-musl",
    "i686-unknown-linux-musl",
    "aarch64-unknown-linux-musl",
    "armv7-unknown-linux-musleabihf",
    "x86_64-apple-darwin",
    "aarch64-apple-darwin",
    "x86_64-unknown-freebsd",
    "i686-unknown-freebsd",
    "aarch64-linux-android",
    "armv7-linux-androideabi",
    "x86_64-linux-android",
    "i686-linux-android",
]
type Backend = Literal["cargo", "cross", "android"]
type Runner = Literal[
    "windows-2025-vs2026",
    "windows-11-vs2026-arm",
    "ubuntu-26.04",
    "macos-15-intel",
    "macos-15",
]

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "rshellcheck-v"
GO_PREFIX = "go/v"
CROSS_VERSION = "0.2.5"
NDK_VERSION = "30.0.16248370"
ANDROID_API = 23
DYNAMIC_CRT = re.compile(
    r"((vcruntime|msvcp|msvcr)\w*|ucrtbased?|api-ms-win-crt-[\w-]+)\.dll",
    re.IGNORECASE,
)
# One source of truth for the workflow matrix, archives and completeness gate.
TARGETS: list[tuple[Triple, Runner, Backend]] = [
    ("x86_64-pc-windows-msvc", "windows-2025-vs2026", "cargo"),
    ("i686-pc-windows-msvc", "windows-2025-vs2026", "cargo"),
    ("aarch64-pc-windows-msvc", "windows-11-vs2026-arm", "cargo"),
    ("x86_64-unknown-linux-musl", "ubuntu-26.04", "cross"),
    ("i686-unknown-linux-musl", "ubuntu-26.04", "cross"),
    ("aarch64-unknown-linux-musl", "ubuntu-26.04", "cross"),
    ("armv7-unknown-linux-musleabihf", "ubuntu-26.04", "cross"),
    ("x86_64-apple-darwin", "macos-15-intel", "cargo"),
    ("aarch64-apple-darwin", "macos-15", "cargo"),
    ("x86_64-unknown-freebsd", "ubuntu-26.04", "cross"),
    ("i686-unknown-freebsd", "ubuntu-26.04", "cross"),
    ("aarch64-linux-android", "ubuntu-26.04", "android"),
    ("armv7-linux-androideabi", "ubuntu-26.04", "android"),
    ("x86_64-linux-android", "ubuntu-26.04", "android"),
    ("i686-linux-android", "ubuntu-26.04", "android"),
]


class Target(TypedDict):
    target: Triple
    runner: Runner
    backend: Backend


class Matrix(TypedDict):
    include: list[Target]


class Metadata(TypedDict):
    version: str
    commit: str
    rust: str


class Plan(Metadata):
    label: str
    tag: str
    publish: bool
    cross: str
    ndk: str
    matrix: Matrix


class Args(argparse.Namespace):
    command: str = ""
    target: Triple | None = None
    label: str | None = None


def run(
    *args: str,
    capture_output: bool = False,
    env: Mapping[str, str] | None = None,
    timeout: float | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        check=True,
        cwd=ROOT,
        capture_output=capture_output,
        text=True,
        env=env,
        timeout=timeout,
    )


def git(*args: str) -> str:
    return run("git", *args, capture_output=True).stdout.strip()


def toml_string(path: Path, *keys: str) -> str:
    value = cast(TOML, tomllib.loads(path.read_text()))
    for key in keys:
        if not isinstance(value, dict):
            raise TypeError(f"{path}: {key} is not inside a table")
        value = value[key]
    if not isinstance(value, str):
        raise TypeError(f"{path}: {'.'.join(keys)} is not a string")
    return value


def unpack(fmt: str, data: bytes, offset: int = 0) -> int:
    (value,) = cast(tuple[int], struct.unpack_from(fmt, data, offset))
    return value


def cargo_version() -> str:
    versions = [
        toml_string(ROOT / "crates" / crate / "Cargo.toml", "package", "version")
        for crate in ("shellcheck-cli", "shellcheck-rs")
    ]
    if versions[0] != versions[1]:
        raise ValueError("CLI and library versions must agree")
    version = versions[0]
    if not re.fullmatch(r"\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?", version):
        raise ValueError(f"Unsupported release version: {version}")
    return version


def upstream() -> dict[str, str]:
    pin = json.loads((ROOT / "tools/oracle.json").read_text())
    if not re.fullmatch(r"\d+\.\d+\.\d+", pin["version"]):
        raise ValueError("Upstream version must be a stable release version")
    if not re.fullmatch(r"[0-9a-f]{40}", pin["revision"]):
        raise ValueError("Upstream revision must be a full commit SHA")
    return {"upstream_version": pin["version"], "upstream_revision": pin["revision"]}


def metadata() -> Metadata:
    version = cargo_version()
    toolchain = toml_string(ROOT / "Cargo.toml", "workspace", "package", "rust-version")
    if toolchain.count(".") == 1:
        toolchain += ".0"
    return Metadata(version=version, commit=git("rev-parse", "HEAD"), rust=toolchain)


def target_entries() -> list[Target]:
    return [Target(target=t, runner=r, backend=b) for t, r, b in TARGETS]


def companion_tag(version: str, commit: str) -> str:
    """The Go installer at go/cmd/shellcheck resolves `go/v<version>` to the
    release `rshellcheck-v<version>`, so both tags must name the same commit."""
    tag = GO_PREFIX + version
    listing = git(
        "ls-remote", "--tags", "origin", f"refs/tags/{tag}", f"refs/tags/{tag}^{{}}"
    )
    found: dict[str, str] = {}
    for line in listing.splitlines():
        sha, _, name = line.partition("\t")
        found[name] = sha
    points_at = found.get(f"refs/tags/{tag}^{{}}", found.get(f"refs/tags/{tag}"))
    if points_at is None:
        raise ValueError(
            f"Tag {tag} is missing; the Go installer needs it on commit {commit[:12]}"
        )
    if points_at != commit:
        raise ValueError(
            f"Tag {tag} points at {points_at[:12]}, the release at {commit[:12]}"
        )
    return tag


def plan(ref: str = "", event: str = "") -> Plan:
    meta = metadata()
    publishing = event == "push" and ref.startswith("refs/tags/")
    expected = PREFIX + meta["version"]
    if publishing and ref != "refs/tags/" + expected:
        raise ValueError(
            f"Tag must be {expected}, matching both Cargo package versions"
        )
    if publishing:
        _ = companion_tag(meta["version"], meta["commit"])
    label = (
        meta["version"]
        if publishing
        else f"{meta['version']}-dev.{meta['commit'][:12]}"
    )
    return Plan(
        **meta,
        label=label,
        tag=expected,
        publish=publishing,
        cross=CROSS_VERSION,
        ndk=NDK_VERSION,
        matrix=Matrix(include=target_entries()),
    )


def target_info(target: Triple) -> Target:
    return next(entry for entry in target_entries() if entry["target"] == target)


def archive_name(label: str, target: Triple) -> str:
    extension = ".zip" if "windows" in target else ".tar.gz"
    return f"rshellcheck-{label}-{target}{extension}"


def pe_imports(data: bytes, pe: int) -> list[str]:
    optional = pe + 24
    directories = optional + (112 if unpack("<H", data, optional) == 0x20B else 96)
    if unpack("<I", data, directories - 4) < 2 or not unpack(
        "<I", data, directories + 8
    ):
        return []
    sections = optional + unpack("<H", data, pe + 20)

    def offset(rva: int) -> int:
        for header in range(sections, sections + 40 * unpack("<H", data, pe + 6), 40):
            start = unpack("<I", data, header + 12)
            size = max(unpack("<I", data, header + 8), unpack("<I", data, header + 16))
            if start <= rva < start + size:
                return rva - start + unpack("<I", data, header + 20)
        raise ValueError(f"PE address {rva:#x} lies outside every section")

    names: list[str] = []
    descriptor = offset(unpack("<I", data, directories + 8))
    while any(data[descriptor : descriptor + 20]):
        name = offset(unpack("<I", data, descriptor + 12))
        names.append(data[name : data.index(b"\0", name)].decode("ascii"))
        descriptor += 20
    return names


def elf_interpreter(data: bytes, wide: bool) -> bytes | None:
    phoff = unpack("<Q", data, 32) if wide else unpack("<I", data, 28)
    phsize = unpack("<H", data, 54 if wide else 42)
    phcount = unpack("<H", data, 56 if wide else 44)
    for header in (phoff + index * phsize for index in range(phcount)):
        if unpack("<I", data, header) == 3:
            start = (
                unpack("<Q", data, header + 8)
                if wide
                else unpack("<I", data, header + 4)
            )
            size = (
                unpack("<Q", data, header + 32)
                if wide
                else unpack("<I", data, header + 16)
            )
            return data[start : start + size].rstrip(b"\0")
    return None


def verify_binary(data: bytes, target: Triple) -> None:
    """Reject host binaries accidentally packaged under a cross-target filename."""
    arch = target.split("-", 1)[0]
    wide = arch in ("x86_64", "aarch64")
    if "windows" in target:
        pe = unpack("<I", data, 0x3C)
        machine = {"x86_64": 0x8664, "i686": 0x14C, "aarch64": 0xAA64}[arch]
        if (
            data[:2] != b"MZ"
            or data[pe : pe + 4] != b"PE\0\0"
            or unpack("<H", data, pe + 4) != machine
            or unpack("<H", data, pe + 24) != (0x20B if wide else 0x10B)
        ):
            raise ValueError(f"Binary is not a {target} PE executable")
        if dynamic := [n for n in pe_imports(data, pe) if DYNAMIC_CRT.fullmatch(n)]:
            raise ValueError(
                f"{target} binary imports the dynamic C runtime: {dynamic}"
            )
    elif "darwin" in target:
        machine = {"x86_64": 0x1000007, "aarch64": 0x100000C}[arch]
        if unpack("<I", data) != 0xFEEDFACF or unpack("<I", data, 4) != machine:
            raise ValueError(f"Binary is not a {target} Mach-O executable")
    else:
        machine = {"x86_64": 62, "i686": 3, "aarch64": 183, "armv7": 40}[arch]
        if (
            data[:6] != b"\x7fELF" + bytes([2 if wide else 1, 1])
            or unpack("<H", data, 18) != machine
            or data[7] not in ((9,) if "freebsd" in target else (0, 3))
        ):
            raise ValueError(f"Binary is not a {target} ELF executable")
        interpreter = elf_interpreter(data, wide)
        # Static binaries must not depend on a host ELF interpreter.
        if "musl" in target and interpreter is not None:
            raise ValueError(f"{target} binary is not static: {interpreter!r}")
        linker = b"/system/bin/linker64" if wide else b"/system/bin/linker"
        if "android" in target and interpreter != linker:
            raise ValueError(f"{target} binary needs {linker!r}, has {interpreter!r}")


def smoke(command: list[str], version: str) -> None:
    env = os.environ.copy()
    _ = env.pop("SHELLCHECK_OPTS", None)
    banner = run(*command, "--version", capture_output=True, env=env, timeout=60).stdout
    if f"version: {version}\n" not in banner:
        raise ValueError("Binary version differs from Cargo version")
    for script, status in [
        ("#!/bin/sh\nprintf '%s\\n' hello\n", 0),
        ("#!/bin/sh\necho $release_probe\n", 1),
    ]:
        result = subprocess.run(
            [*command, "--norc", "-s", "sh", "-f", "json1", "-"],
            # Text-mode stdin translates LF to CRLF on Windows, changing the
            # shell script and producing SC1017 even for the clean fixture.
            input=script.encode("utf-8"),
            capture_output=True,
            env=env,
            cwd=ROOT,
            timeout=60,
            check=False,
        )
        if result.returncode != status or result.stderr:
            raise ValueError(
                f"Smoke test failed: expected {status}, got {result.returncode}; "
                + f"stdout={result.stdout!r}; stderr={result.stderr!r}"
            )
        report = cast(JSON, json.loads(result.stdout))
        comments = report.get("comments") if isinstance(report, dict) else None
        if not isinstance(comments, list):
            raise TypeError("Smoke output lacks a comments array")
        codes = [c.get("code") for c in comments if isinstance(c, dict)]
        if (status == 0 and comments) or (status == 1 and 2086 not in codes):
            raise ValueError("Smoke diagnostic mismatch")


def build(target: Triple) -> None:
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
    _ = run(
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
    binary = built_binary(target)
    verify_binary(binary.read_bytes(), target)
    if backend == "cargo" or target in (
        "x86_64-unknown-linux-musl",
        "i686-unknown-linux-musl",
    ):
        smoke([str(binary)], cargo_version())
    # Invoke QEMU directly: old cross runners can drop CLI arguments on new Cargo.
    elif "musl" in target:
        qemu = "qemu-aarch64" if target.startswith("aarch64") else "qemu-arm"
        smoke(emulated(target, binary, f"/usr/local/bin/{qemu}"), cargo_version())
    elif backend == "android":
        arch = {
            "aarch64": "aarch64",
            "armv7": "arm",
            "x86_64": "x86_64",
            "i686": "i686",
        }
        runner = arch[target.split("-", 1)[0]]
        smoke(emulated(target, binary, "/android-runner", runner), cargo_version())


def built_binary(target: Triple) -> Path:
    name = "rshellcheck.exe" if "windows" in target else "rshellcheck"
    return ROOT / "target" / target / "release" / name


def emulated(target: Triple, binary: Path, entrypoint: str, *args: str) -> list[str]:
    return [
        "docker",
        "run",
        "--rm",
        "--interactive",
        # 32-bit bionic calls personality(2), which Docker's seccomp profile denies.
        "--security-opt",
        "seccomp=unconfined",
        "--volume",
        f"{binary.parent}:/work:ro",
        "--entrypoint",
        entrypoint,
        f"ghcr.io/cross-rs/{target}:{CROSS_VERSION}",
        *args,
        "/work/rshellcheck",
    ]


def pack(
    target: Triple, label: str, binary: Path | None = None, dest: Path | None = None
) -> Path:
    meta = metadata()
    binary = binary or built_binary(target)
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
    files: dict[str, tuple[bytes, int]] = {
        binary.name: (data, 0o755),
        "LICENSE.txt": ((ROOT / "LICENSE").read_bytes(), 0o644),
        "README.md": (readme.encode(), 0o644),
        "BUILD.json": (
            (
                json.dumps(
                    {
                        **meta,
                        **upstream(),
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


def read_member(archive: tarfile.TarFile, name: str) -> bytes:
    file = archive.extractfile(name)
    if file is None:
        raise ValueError(f"{name} is not a regular file")
    return file.read()


def assemble(label: str, dest: Path | None = None) -> list[str]:
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
                build_json = source.read(prefix + "BUILD.json")
                data = source.read(prefix + binary)
        else:
            with tarfile.open(archive) as source:
                build_json = read_member(source, prefix + "BUILD.json")
                data = read_member(source, prefix + binary)
        build_meta = cast(JSON, json.loads(build_json))
        if not isinstance(build_meta, dict):
            raise TypeError(f"{archive.name}: BUILD.json is not an object")
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
    _ = run(
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
    _ = (dest / "SHA256SUMS").write_text(checksums, encoding="utf-8")
    return assets


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "command", choices=["plan", "build", "smoke", "pack", "assemble"]
    )
    _ = parser.add_argument("--target", choices=[t for t, _, _ in TARGETS])
    _ = parser.add_argument("--label")
    args = parser.parse_args(namespace=Args())
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
    elif args.command == "smoke" and args.target:
        binary = built_binary(args.target)
        verify_binary(binary.read_bytes(), args.target)
        smoke([str(binary)], cargo_version())
    elif args.command == "pack" and args.target and args.label:
        _ = pack(args.target, args.label)
    elif args.command == "assemble" and args.label:
        _ = assemble(args.label)
    else:
        parser.error(
            "build and smoke need --target; pack needs --target and --label; "
            + "assemble needs --label"
        )


if __name__ == "__main__":
    main()
