"""Validate the source SBOM and checksum the complete unsigned release payload."""

import argparse
import hashlib
import json
import tomllib
from pathlib import Path
from typing import cast

from release import JSON, TOML


class Args(argparse.Namespace):
    directory: Path = Path()
    lockfile: Path = Path()


def locked_dependencies(lockfile: Path) -> set[tuple[str, str]]:
    lock = cast(dict[str, TOML], tomllib.loads(lockfile.read_text()))
    packages = lock.get("package")
    if not isinstance(packages, list):
        raise TypeError(f"{lockfile} has no [[package]] entries")
    expected: set[tuple[str, str]] = set()
    for package in packages:
        if not isinstance(package, dict) or "source" not in package:
            continue
        name, version = package.get("name"), package.get("version")
        if not isinstance(name, str) or not isinstance(version, str):
            raise TypeError(f"{lockfile} has a package without name or version")
        expected.add((name, version))
    return expected


def finalize(directory: Path, lockfile: Path | None = None) -> None:
    sbom = cast(JSON, json.loads((directory / "source.spdx.json").read_text()))
    if not isinstance(sbom, dict):
        raise TypeError("Expected a nonempty SPDX 2.3 source SBOM")
    entries = sbom.get("packages")
    if (
        sbom.get("spdxVersion") != "SPDX-2.3"
        or not isinstance(entries, list)
        or not entries
    ):
        raise ValueError("Expected a nonempty SPDX 2.3 source SBOM")
    creation = sbom.get("creationInfo")
    if (
        not sbom.get("documentNamespace")
        or not isinstance(creation, dict)
        or not creation.get("creators")
    ):
        raise ValueError("SBOM must identify its document and generator")
    packages: list[tuple[str, str | None, str]] = []
    for entry in entries:
        if not isinstance(entry, dict):
            raise TypeError("SBOM packages must be objects")
        name = entry.get("name")
        version = entry.get("versionInfo")
        license_id = entry.get("licenseDeclared", "NOASSERTION")
        if (
            not isinstance(name, str)
            or not isinstance(version, str | None)
            or not isinstance(license_id, str)
        ):
            raise TypeError(f"SBOM package fields must be strings: {entry}")
        packages.append((name, version, license_id))
    if lockfile is not None:
        found = {(name, version) for name, version, _ in packages}
        if missing := locked_dependencies(lockfile) - found:
            raise ValueError(
                f"SBOM is missing Cargo.lock dependencies: {sorted(missing)}"
            )
    rows = [
        "# Declared dependency licenses",
        "",
        "Source inventory from source.spdx.json; includes development dependencies.",
        "Declared expressions are not bundled license texts or a legal assessment.",
        "NOASSERTION means the scanner could not determine a license.",
        "",
    ]
    for name, version, license_id in sorted(packages, key=lambda p: (p[0], p[1] or "")):
        rows.append(
            f"- {name} {'unknown' if version is None else version}: {license_id}"
        )
    _ = (directory / "DEPENDENCY-LICENSES.md").write_text("\n".join(rows) + "\n")
    files = sorted(p for p in directory.iterdir() if p.name != "SHA256SUMS")
    if any(not p.is_file() or p.is_symlink() for p in files):
        raise ValueError("Release payload must contain only regular files")
    _ = (directory / "SHA256SUMS").write_text(
        "".join(
            f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.name}\n" for p in files
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("directory", type=Path)
    _ = parser.add_argument("--lockfile", type=Path, required=True)
    args = parser.parse_args(namespace=Args())
    finalize(args.directory, args.lockfile)


if __name__ == "__main__":
    main()
