"""Package completeness is a publication gate, not just a file glob."""

import io
import json
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path

import binding_packages as packages
from release import ROOT, metadata


class PackageTests(unittest.TestCase):
    def make_payload(self, root: Path) -> None:
        records: list[packages.Package] = []
        for kind, name in (
            ("npm", "npm.tgz"),
            ("wheel", "python.whl"),
            ("sdist", "python.tar.gz"),
        ):
            contents = {
                "package/shellcheck_wasm.wasm": b"\0asm\x01\0\0\0",
                "package/LICENSE": (ROOT / "LICENSE").read_bytes(),
            }
            if kind == "wheel":
                with zipfile.ZipFile(root / name, "w") as archive:
                    for path, data in contents.items():
                        archive.writestr(path, data)
            else:
                with tarfile.open(root / name, "w:gz") as archive:
                    for path, data in contents.items():
                        entry = tarfile.TarInfo(path)
                        entry.size = len(data)
                        archive.addfile(entry, io.BytesIO(data))
            records.append({
                "kind": kind,
                "name": name,
                "sha256": packages.digest((root / name).read_bytes()),
            })
        _ = (root / packages.MANIFEST).write_text(
            json.dumps({
                **metadata(),
                "wasm_sha256": packages.digest(b"\0asm\x01\0\0\0"),
                "packages": records,
            })
        )

    def test_complete_payload_and_failure_cases(self):
        for scenario in (
            "complete",
            "missing",
            "tampered",
            "commit",
            "wasm",
            "duplicate",
        ):
            with self.subTest(scenario=scenario), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                self.make_payload(root)
                record = packages.load_record(root)
                if scenario == "missing":
                    (root / "python.whl").unlink()
                elif scenario == "tampered":
                    _ = (root / "npm.tgz").write_bytes(b"corrupt")
                elif scenario == "commit":
                    record["commit"] = "0" * 40
                elif scenario == "wasm":
                    record["wasm_sha256"] = "0" * 64
                elif scenario == "duplicate":
                    record["packages"][1] = record["packages"][0]
                _ = (root / packages.MANIFEST).write_text(json.dumps(record))
                if scenario == "complete":
                    packages.verify(root)
                else:
                    with self.assertRaises((ValueError, FileNotFoundError)):
                        packages.verify(root)
