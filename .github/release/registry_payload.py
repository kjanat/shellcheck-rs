"""Repackage verified immutable release binaries for first registry publication."""

import argparse
import hashlib
import os
import shutil
import tempfile
from pathlib import Path

import binding_packages
import native_packages
from release import PREFIX, TARGETS, archive_name, metadata, run


class Args(argparse.Namespace):
    directory: Path = Path()


def prepare(dest: Path) -> None:
    meta = metadata()
    tag = PREFIX + meta["version"]
    repo = os.environ["GITHUB_REPOSITORY"]
    dest.mkdir(parents=True, exist_ok=True)
    if any(dest.iterdir()):
        raise ValueError("Registry payload directory must be empty")
    with tempfile.TemporaryDirectory() as temp:
        original = Path(temp)
        _ = run("gh", "release", "download", tag, "--dir", str(original))
        # Verify the signed checksum inventory before trusting any downloaded file.
        _ = run(
            "gh",
            "attestation",
            "verify",
            str(original / "SHA256SUMS"),
            "--bundle",
            str(original / "provenance.sigstore.json"),
            "--repo",
            repo,
            "--signer-workflow",
            f"{repo}/.github/workflows/release.yml",
            "--source-digest",
            meta["commit"],
            "--source-ref",
            f"refs/tags/{tag}",
        )
        checked: set[str] = set()
        for line in (original / "SHA256SUMS").read_text().splitlines():
            expected, name = line.split("  ", 1)
            if Path(name).name != name or name in checked:
                raise ValueError("Invalid release checksum inventory")
            if hashlib.sha256((original / name).read_bytes()).hexdigest() != expected:
                raise ValueError(f"Release checksum mismatch: {name}")
            checked.add(name)
        required = {
            archive_name(meta["version"], target) for target, _, _ in TARGETS
        } | {binding_packages.MANIFEST}
        if not required <= checked:
            raise ValueError("Signed inventory is missing release payload files")
        record = binding_packages.load_record(original)
        if not {p["name"] for p in record["packages"]} <= checked:
            raise ValueError("Binding archives are absent from signed inventory")
        binding_packages.verify(original)
        npm = next(p for p in record["packages"] if p["kind"] == "npm")
        contents = binding_packages.members(original / npm["name"])
        wasm = original / "shellcheck_wasm.wasm"
        _ = wasm.write_bytes(
            next(
                data
                for name, data in contents.items()
                if name.endswith("/shellcheck_wasm.wasm")
            )
        )
        binding_packages.build(dest, wasm)
        binding_packages.test_install(dest.resolve())
        for target, _, _ in TARGETS:
            name = archive_name(meta["version"], target)
            _ = shutil.copy2(original / name, dest / name)
        native_packages.build(dest, meta["version"])
        native_packages.test_install(dest.resolve())
    names = (
        {archive_name(meta["version"], target) for target, _, _ in TARGETS}
        | {p["name"] for p in binding_packages.load_record(dest)["packages"]}
        | {p["file"] for p in native_packages.load_record(dest)["packages"]}
        | {binding_packages.MANIFEST, native_packages.MANIFEST}
    )
    _ = (dest / "SHA256SUMS").write_text(
        "".join(
            f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name}\n"
            for path in (dest / name for name in sorted(names))
        )
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    _ = parser.add_argument("directory", type=Path)
    prepare(parser.parse_args(namespace=Args()).directory)
