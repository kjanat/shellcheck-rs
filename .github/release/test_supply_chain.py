import hashlib
import json
import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

import release
from release import JSON
from supply_chain import finalize
from test_publish import read_calls


class SupplyChainTests(unittest.TestCase):
    def test_signature_gate_requires_every_subject_and_expected_identity(self):
        workflow = (release.ROOT / ".github/workflows/release.yml").read_text()
        step = workflow.split(
            "      - name: Verify signatures and workflow identity before publishing\n",
            1,
        )[1]
        script = textwrap.dedent(
            step.split("        run: |\n", 1)[1].split("      - name:", 1)[0]
        )
        for failure in ("none", "provenance", "sbom"):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                (root / "dist").mkdir()
                for name in (
                    "binary.zip",
                    "rshellcheck-test-source.tar.gz",
                    "SHA256SUMS",
                ):
                    _ = (root / "dist" / name).write_text("fixture")
                for name in ("provenance", "sbom"):
                    _ = (root / name).write_text("signed fixture")
                _ = (root / "gh").write_text("""#!/usr/bin/env python3
import json, os, sys
with open("calls.jsonl", "a") as f:
    f.write(json.dumps(sys.argv[1:]) + "\\n")
is_sbom = "--predicate-type" in sys.argv
sys.exit(int(os.environ["FAIL"] == ("sbom" if is_sbom else "provenance")))
""")
                (root / "gh").chmod(0o755)
                result = subprocess.run(
                    ["bash", "-euo", "pipefail", "-c", script],
                    check=False,
                    cwd=root,
                    capture_output=True,
                    text=True,
                    timeout=15,
                    env={
                        **os.environ,
                        "PATH": str(root) + os.pathsep + os.environ["PATH"],
                        "FAIL": failure,
                        "PROVENANCE_BUNDLE": str(root / "provenance"),
                        "SBOM_BUNDLE": str(root / "sbom"),
                        "LABEL": "test",
                        "GH_REPO": "kjanat/shellcheck-rs",
                        "GITHUB_SHA": "a" * 40,
                        "GITHUB_REF": "refs/tags/rshellcheck-vtest",
                    },
                )
                self.assertEqual(
                    result.returncode == 0, failure == "none", result.stderr
                )
                self.assertEqual(
                    (root / "dist/provenance.sigstore.json").exists(), failure == "none"
                )
                calls = read_calls(root / "calls.jsonl")
                if failure == "none":
                    self.assertEqual(len(calls), 4)
                for args in calls:
                    self.assertEqual(args[args.index("--source-digest") + 1], "a" * 40)
                    self.assertEqual(
                        args[args.index("--source-ref") + 1],
                        "refs/tags/rshellcheck-vtest",
                    )
                    self.assertEqual(
                        args[args.index("--signer-workflow") + 1],
                        "kjanat/shellcheck-rs/.github/workflows/release.yml",
                    )

    def test_inventory_and_checksums_cover_source_sbom_and_licenses(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            _ = (root / "source.tar.gz").write_bytes(b"source")
            _ = (root / "source.spdx.json").write_text(
                json.dumps({
                    "spdxVersion": "SPDX-2.3",
                    "documentNamespace": "https://example.org/inventory",
                    "creationInfo": {"creators": ["Tool: syft"]},
                    "packages": [
                        {
                            "name": "dependency",
                            "versionInfo": "1.2.3",
                            "licenseDeclared": "MIT",
                        },
                        {"name": "unknown"},
                    ],
                })
            )
            _ = (root / "SHA256SUMS").write_text("stale\n")
            finalize(root)
            licenses = (root / "DEPENDENCY-LICENSES.md").read_text()
            self.assertIn("dependency 1.2.3: MIT", licenses)
            self.assertIn("unknown unknown: NOASSERTION", licenses)
            lines = (root / "SHA256SUMS").read_text().splitlines()
            self.assertEqual(len(lines), 3)
            for line in lines:
                digest, name = line.split("  ")
                self.assertEqual(
                    digest, hashlib.sha256((root / name).read_bytes()).hexdigest()
                )
            before = (root / "SHA256SUMS").read_bytes()
            finalize(root)
            self.assertEqual(before, (root / "SHA256SUMS").read_bytes())
            lock = root / "Cargo.lock"
            _ = lock.write_text(
                '[[package]]\nname = "missing"\nversion = "1.0.0"\nsource = "registry+test"\n'
            )
            with self.assertRaisesRegex(ValueError, "missing Cargo.lock dependencies"):
                finalize(root, lock)
            self.assertEqual(before, (root / "SHA256SUMS").read_bytes())

    def test_missing_empty_or_wrong_format_sbom_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with self.assertRaises(FileNotFoundError):
                finalize(root)
            sboms: list[dict[str, JSON]] = [
                {},
                {"spdxVersion": "SPDX-2.3", "packages": []},
                {"spdxVersion": "SPDX-2.2", "packages": [{}]},
                {"spdxVersion": "SPDX-2.3", "packages": [{}]},
            ]
            for sbom in sboms:
                _ = (root / "source.spdx.json").write_text(json.dumps(sbom))
                with self.assertRaises(ValueError):
                    finalize(root)
                self.assertFalse((root / "SHA256SUMS").exists())
