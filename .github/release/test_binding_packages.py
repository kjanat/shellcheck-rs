"""Package completeness is a publication gate, not just a file glob."""

import io
import json
import subprocess
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path
from typing import cast
from unittest.mock import patch

import binding_packages as packages
from release import ROOT, metadata


class PackageTests(unittest.TestCase):
    def test_duplicate_archive_members_cannot_hide_a_second_module(self):
        for kind in ("wheel", "npm"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                self.make_payload(root)
                record = packages.load_record(root)
                package = next(p for p in record["packages"] if p["kind"] == kind)
                path = root / package["name"]
                name = "package/" + packages.WASM_NAME
                contents = packages.members(path)
                if kind == "wheel":
                    with zipfile.ZipFile(path, "a") as archive:
                        archive.writestr(name, contents[name])
                else:
                    with tarfile.open(path, "w:gz") as archive:
                        for member, data in [*contents.items(), (name, contents[name])]:
                            entry = tarfile.TarInfo(member)
                            entry.size = len(data)
                            archive.addfile(entry, io.BytesIO(data))
                package["sha256"] = packages.digest(path.read_bytes())
                _ = (root / packages.MANIFEST).write_text(json.dumps(record))
                with self.assertRaisesRegex(ValueError, "Duplicate archive member"):
                    packages.verify(root)

    def test_pypi_uploads_only_python_and_verifies_remote_hashes(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.make_payload(root)
            record = packages.load_record(root)
            python = [p for p in record["packages"] if p["kind"] != "npm"]
            response = {
                "urls": [
                    {"filename": p["name"], "digests": {"sha256": p["sha256"]}}
                    for p in python
                ]
            }
            with (
                patch.object(packages, "metadata", return_value=metadata()),
                patch.object(subprocess, "run") as run,
                patch("registry_checks.urlopen") as request,
            ):
                request.return_value = io.BytesIO(json.dumps(response).encode())
                packages.publish_pypi(root)
                command = cast(list[str], run.call_args.args[0])
                self.assertIn("always", command)
                self.assertEqual(command[-2:], [str(root / p["name"]) for p in python])
                response["urls"][0] = {
                    "filename": python[0]["name"],
                    "digests": {"sha256": "wrong"},
                }
                request.return_value = io.BytesIO(json.dumps(response).encode())
                with self.assertRaisesRegex(ValueError, "PyPI digest mismatch"):
                    packages.publish_pypi(root)

    def make_payload(
        self, root: Path, names: tuple[str, ...] = (packages.WASM_NAME,)
    ) -> None:
        records: list[packages.Package] = []
        for kind, name in (
            ("npm", "npm.tgz"),
            ("wheel", "python.whl"),
            ("sdist", "python.tar.gz"),
        ):
            contents = {
                **{f"package/{name}": b"\0asm\x01\0\0\0" for name in names},
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

    def test_resume_verifies_both_wasm_generations_and_rejects_ambiguity(self):
        for names in (
            ("shellcheck_wasm.wasm",),
            (packages.WASM_NAME,),
            ("shellcheck_wasm.wasm", packages.WASM_NAME),
        ):
            with self.subTest(names=names), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                self.make_payload(root, names)
                if len(names) == 1:
                    packages.verify(root)
                    record = packages.load_record(root)
                    record["wasm_sha256"] = "0" * 64
                    _ = (root / packages.MANIFEST).write_text(json.dumps(record))
                    with self.assertRaisesRegex(ValueError, "mismatched WASM"):
                        packages.verify(root)
                else:
                    with self.assertRaisesRegex(ValueError, "exactly one WASM"):
                        packages.verify(root)
