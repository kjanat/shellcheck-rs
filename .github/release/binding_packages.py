"""Build and verify self-contained npm and Python release distributions."""

import argparse
import hashlib
import json
import shutil
import subprocess
import tarfile
import tempfile
import tomllib
import zipfile
from pathlib import Path
from typing import TypedDict, cast
from urllib.request import urlopen

from release import ROOT, metadata, read_member

MANIFEST = "binding-packages.json"


class Package(TypedDict):
    kind: str
    name: str
    sha256: str


class Record(TypedDict):
    commit: str
    version: str
    wasm_sha256: str
    packages: list[Package]


class Args(argparse.Namespace):
    command: str = ""
    directory: Path = Path()


def load_record(dest: Path) -> Record:
    return cast(Record, json.loads((dest / MANIFEST).read_text()))


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def members(path: Path) -> dict[str, bytes]:
    if path.suffix in {".whl", ".zip"}:
        with zipfile.ZipFile(path) as archive:
            return {
                n: archive.read(n) for n in archive.namelist() if not n.endswith("/")
            }
    with tarfile.open(path) as archive:
        return {
            m.name: read_member(archive, m.name)
            for m in archive.getmembers()
            if m.isfile()
        }


def verify(dest: Path) -> None:
    record = load_record(dest)
    meta = metadata()
    if record["commit"] != meta["commit"] or record["version"] != meta["version"]:
        raise ValueError("Binding packages are from another commit or version")
    packages = record["packages"]
    if len(packages) != 3 or {p["kind"] for p in packages} != {"npm", "wheel", "sdist"}:
        raise ValueError("Expected npm tarball, Python wheel and source distribution")
    for package in packages:
        name = package["name"]
        if Path(name).name != name:
            raise ValueError("Invalid package filename")
        path = dest / name
        if digest(path.read_bytes()) != package["sha256"]:
            raise ValueError(f"Package checksum mismatch: {name}")
        contents = members(path)
        wasm = [
            data for n, data in contents.items() if n.endswith("/shellcheck_wasm.wasm")
        ]
        if len(wasm) != 1 or digest(wasm[0]) != record["wasm_sha256"]:
            raise ValueError(f"Missing or mismatched WASM in {name}")
        if not any(
            n.endswith("/LICENSE") and data == (ROOT / "LICENSE").read_bytes()
            for n, data in contents.items()
        ):
            raise ValueError(f"Missing project license in {name}")


def build(dest: Path) -> None:
    dest = dest.resolve()
    dest.mkdir(parents=True, exist_ok=True)
    meta = metadata()
    js = ROOT / "bindings/wasm/js"
    py = ROOT / "bindings/wasm/python"
    if json.loads((js / "package.json").read_text())["version"] != meta["version"]:
        raise ValueError("JavaScript and Rust package versions must agree")
    if (
        tomllib.loads((py / "pyproject.toml").read_text())["project"]["version"]
        != meta["version"]
    ):
        raise ValueError("Python and Rust package versions must agree")
    wasm = ROOT / "target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm"
    if not wasm.read_bytes().startswith(b"\0asm\x01\0\0\0"):
        raise ValueError("Missing valid core WASM module")
    with tempfile.TemporaryDirectory() as temp:
        stage = Path(temp)
        npm = stage / "js"
        python = stage / "python"
        npm.mkdir()
        python.mkdir()
        for name in ("package.json", "shellcheck.mjs", "worker.mjs"):
            _ = shutil.copy2(js / name, npm / name)
        for name in ("pyproject.toml", "rshellcheck_wasm.py"):
            _ = shutil.copy2(py / name, python / name)
        from release import upstream

        pin = upstream()
        upstream_url = (
            f"https://github.com/koalaman/shellcheck/commit/{pin['upstream_revision']}"
        )
        project = python / "pyproject.toml"
        project.write_text(
            project.read_text().replace(
                "[project.urls]\n",
                f'[project.urls]\n"Upstream ShellCheck {pin["upstream_version"]}" = "{upstream_url}"\n',
            )
        )
        _ = shutil.copytree(
            py / "rshellcheck_wasm_data",
            python / "rshellcheck_wasm_data",
            ignore=shutil.ignore_patterns("__pycache__", "*.wasm"),
        )
        for directory in (npm, python):
            _ = shutil.copy2(ROOT / "LICENSE", directory / "LICENSE")
            _ = shutil.copy2(
                (py / "README.md")
                if directory == python
                else ROOT / "bindings/wasm/README.md",
                directory / "README.md",
            )
        _ = shutil.copy2(wasm, npm / wasm.name)
        with (python / "README.md").open("a") as readme:
            readme.write(
                f"\nTracks ShellCheck {pin['upstream_version']} with upstream changes through "
                f"[{pin['upstream_revision'][:12]}]({upstream_url}).\n"
            )
        _ = shutil.copy2(wasm, python / "rshellcheck_wasm_data" / wasm.name)
        _ = subprocess.run(
            ["npm", "pack", "--ignore-scripts", "--pack-destination", str(dest)],
            cwd=npm,
            check=True,
        )
        _ = subprocess.run(
            ["uv", "build", "--no-sources", "--out-dir", str(dest), str(python)],
            check=True,
        )
    packages: list[Package] = []
    for kind, pattern in (
        ("npm", "*.tgz"),
        ("wheel", "*.whl"),
        ("sdist", "rshellcheck_wasm-*.tar.gz"),
    ):
        paths = list(dest.glob(pattern))
        if len(paths) != 1:
            raise ValueError(f"Expected exactly one {kind} distribution")
        packages.append({
            "kind": kind,
            "name": paths[0].name,
            "sha256": digest(paths[0].read_bytes()),
        })
    _ = (dest / MANIFEST).write_text(
        json.dumps(
            {**meta, "wasm_sha256": digest(wasm.read_bytes()), "packages": packages},
            indent=2,
        )
        + "\n"
    )
    verify(dest)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument(
        "command", choices=["build", "verify", "test", "publish-pypi"]
    )
    _ = parser.add_argument("directory", type=Path)
    args = parser.parse_args(namespace=Args())
    if args.command == "build":
        build(args.directory)
    elif args.command == "verify":
        verify(args.directory)
    elif args.command == "publish-pypi":
        publish_pypi(args.directory)
    else:
        test_install(args.directory.resolve())


def publish_pypi(dest: Path) -> None:
    verify(dest)
    record = load_record(dest)
    packages = [p for p in record["packages"] if p["kind"] in {"wheel", "sdist"}]
    _ = subprocess.run(
        [
            "uv",
            "publish",
            "--trusted-publishing",
            "always",
            "--check-url",
            "https://pypi.org/simple/",
            "--publish-url",
            "https://upload.pypi.org/legacy/",
            *(str((dest / p["name"]).resolve()) for p in packages),
        ],
        check=True,
    )
    with urlopen(
        f"https://pypi.org/pypi/rshellcheck-wasm/{record['version']}/json", timeout=30
    ) as response:
        published = json.load(response)
    hashes = {p["filename"]: p["digests"]["sha256"] for p in published["urls"]}
    for package in packages:
        if hashes.get(package["name"]) != package["sha256"]:
            raise ValueError(f"PyPI digest mismatch: {package['name']}")


def test_install(dest: Path) -> None:
    verify(dest)
    packages = load_record(dest)["packages"]
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        for package in packages:
            path = dest / package["name"]
            if package["kind"] == "npm":
                _ = subprocess.run(
                    [
                        "npm",
                        "install",
                        "--ignore-scripts",
                        "--no-audit",
                        "--no-fund",
                        str(path),
                    ],
                    cwd=root,
                    check=True,
                )
                _ = subprocess.run(
                    [
                        "node",
                        "--input-type=module",
                        "-e",
                        """
import assert from 'node:assert/strict';
import { createChecker } from '@kjanat/rshellcheck-wasm';
const c = await createChecker();
assert.equal(c.check({script:'#!/bin/sh\\ntrue\\n'}).comments.length, 0);
assert.ok(c.check({script:'#!/bin/sh\\necho $x\\n'}).comments.some(x => x.code === 2086));
c.close();
""",
                    ],
                    cwd=root,
                    check=True,
                )
            else:
                env = root / package["kind"]
                _ = subprocess.run(["uv", "venv", str(env)], check=True)
                python = env / "bin/python"
                _ = subprocess.run(
                    ["uv", "pip", "install", "--python", str(python), str(path)],
                    check=True,
                )
                _ = subprocess.run(
                    [
                        str(python),
                        "-I",
                        "-c",
                        """
from rshellcheck_wasm import Checker
with Checker() as c:
    assert not c.check({"script": "#!/bin/sh\\ntrue\\n"})["comments"]
    assert any(x["code"] == 2086 for x in c.check({"script": "#!/bin/sh\\necho $x\\n"})["comments"])
""",
                    ],
                    cwd=root,
                    check=True,
                )


if __name__ == "__main__":
    main()
