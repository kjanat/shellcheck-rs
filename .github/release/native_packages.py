"""Package the verified release binaries for npm without install-time downloads."""

import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import TypedDict, cast

from binding_packages import members
from release import ROOT, TARGETS, Triple, archive_name, metadata, verify_binary

SOURCE = ROOT / "bindings/native/npm"
MANIFEST = "native-packages.json"


class Package(TypedDict):
    file: str
    sha256: str


class Record(TypedDict):
    version: str
    commit: str
    rust: str
    packages: list[Package]


class Args(argparse.Namespace):
    command: str = ""
    directory: Path = Path()
    label: str = ""


def load_record(dest: Path) -> Record:
    return cast(Record, json.loads((dest / MANIFEST).read_text()))


def platforms() -> dict[str, Triple]:
    result = cast(
        dict[str, Triple], json.loads((SOURCE / "platforms.json").read_text())
    )
    if set(result.values()) != {target for target, _, _ in TARGETS}:
        raise ValueError("npm platforms must cover exactly the release targets")
    return result


def pack(stage: Path, dest: Path) -> Package:
    output = subprocess.check_output(
        ["npm", "pack", "--json", "--ignore-scripts", "--pack-destination", str(dest)],
        cwd=stage,
        text=True,
    )
    name = cast(list[dict[str, str]], json.loads(output))[0]["filename"]
    return {
        "file": name,
        "sha256": hashlib.sha256((dest / name).read_bytes()).hexdigest(),
    }


def build(dest: Path, label: str) -> None:
    dest = dest.resolve()
    meta = metadata()
    wrapper = cast(dict[str, object], json.loads((SOURCE / "package.json").read_text()))
    if wrapper["version"] != meta["version"]:
        raise ValueError("Native npm and Rust versions must agree")
    records: list[Package] = []
    dependencies: dict[str, str] = {}
    for key, target in platforms().items():
        contents = members(dest / archive_name(label, target))
        prefix = f"rshellcheck-{label}-{target}/"
        binary = "rshellcheck.exe" if key.startswith("win32-") else "rshellcheck"
        data = contents[prefix + binary]
        build_meta = cast(dict[str, str], json.loads(contents[prefix + "BUILD.json"]))
        expected = {
            **meta,
            "label": label,
            "target": target,
            "binary_sha256": hashlib.sha256(data).hexdigest(),
        }
        if any(build_meta.get(k) != v for k, v in expected.items()):
            raise ValueError(f"Wrong binary source identity: {target}")
        verify_binary(data, target)
        name = f"@rshellcheck/rshellcheck-{key}"
        dependencies[name] = meta["version"]
        platform, arch = key.split("-")
        with tempfile.TemporaryDirectory() as temp:
            stage = Path(temp)
            (stage / "bin").mkdir()
            executable = stage / "bin" / binary
            _ = executable.write_bytes(data)
            executable.chmod(0o755)
            _ = shutil.copy2(ROOT / "LICENSE", stage / "LICENSE")
            _ = (stage / "BUILD.json").write_bytes(contents[prefix + "BUILD.json"])
            _ = (stage / "README.md").write_text(
                f"# {name}\n\nPlatform binary for @kjanat/rshellcheck. Install the main package.\n"
            )
            _ = (stage / "package.json").write_text(
                json.dumps({
                    "name": name,
                    "version": meta["version"],
                    "os": [platform],
                    "cpu": [arch],
                    "license": wrapper["license"],
                    "repository": wrapper["repository"],
                    "publishConfig": {"access": "public"},
                    "files": ["bin", "BUILD.json", "LICENSE", "README.md"],
                })
            )
            records.append(pack(stage, dest))
    with tempfile.TemporaryDirectory() as temp:
        stage = Path(temp)
        for name in ("bin.mjs", "index.mjs", "platforms.json", "README.md"):
            _ = shutil.copy2(SOURCE / name, stage / name)
        _ = shutil.copy2(ROOT / "LICENSE", stage / "LICENSE")
        (stage / "bin.mjs").chmod(0o755)
        wrapper["optionalDependencies"] = dependencies
        _ = (stage / "package.json").write_text(json.dumps(wrapper))
        records.append(pack(stage, dest))
    _ = (dest / MANIFEST).write_text(
        json.dumps({**meta, "packages": records}, indent=2) + "\n"
    )
    verify(dest)


def verify(dest: Path) -> None:
    record = load_record(dest)
    if any(record.get(k) != v for k, v in metadata().items()):
        raise ValueError("Native npm packages are from another source revision")
    expected = {f"@rshellcheck/rshellcheck-{key}" for key in platforms()} | {
        "@kjanat/rshellcheck"
    }
    actual: set[str] = set()
    for package in record["packages"]:
        name = package["file"]
        if Path(name).name != name:
            raise ValueError("Invalid package filename")
        path = dest / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != package["sha256"]:
            raise ValueError(f"Package checksum mismatch: {name}")
        files = members(path)
        manifest = cast(dict[str, str], json.loads(files["package/package.json"]))
        if manifest["version"] != record["version"] or manifest["name"] in actual:
            raise ValueError("Wrong version or duplicate npm package")
        actual.add(manifest["name"])
        if files["package/LICENSE"] != (ROOT / "LICENSE").read_bytes():
            raise ValueError("Missing project license")
    if actual != expected:
        raise ValueError("Incomplete native npm packages")


def test_install(dest: Path) -> None:
    verify(dest)
    key = subprocess.check_output(
        ["node", "-p", 'process.platform + "-" + process.arch'], text=True
    ).strip()
    if key not in platforms():
        raise ValueError(f"Cannot test native npm installation on {key}")
    records = load_record(dest)["packages"]
    packages: dict[str, Path] = {}
    for record in records:
        path = dest / record["file"]
        manifest = cast(
            dict[str, str], json.loads(members(path)["package/package.json"])
        )
        packages[manifest["name"]] = path.resolve()
    with tempfile.TemporaryDirectory() as temp:
        _ = subprocess.run(
            [
                "npm",
                "install",
                "--ignore-scripts",
                "--offline",
                "--no-audit",
                "--no-fund",
                str(packages["@kjanat/rshellcheck"]),
                str(packages[f"@rshellcheck/rshellcheck-{key}"]),
            ],
            cwd=temp,
            check=True,
        )
        executable = Path(temp) / "node_modules/@kjanat/rshellcheck/bin.mjs"
        _ = subprocess.run(["node", str(executable), "--version"], check=True)
        for script, status in [("#!/bin/sh\ntrue\n", 0), ("#!/bin/sh\necho $x\n", 1)]:
            result = subprocess.run(
                ["node", str(executable), "--norc", "-f", "quiet", "-"],
                check=False,
                input=script,
                text=True,
            )
            if result.returncode != status:
                raise ValueError(f"CLI returned {result.returncode}, expected {status}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("command", choices=["build", "verify", "test"])
    _ = parser.add_argument("directory", type=Path)
    _ = parser.add_argument("--label")
    args = parser.parse_args(namespace=Args())
    if args.command == "build":
        if not args.label:
            parser.error("build requires --label")
        build(args.directory, args.label)
    elif args.command == "verify":
        verify(args.directory)
    else:
        test_install(args.directory)
