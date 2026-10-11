"""Exercise the workflow's publish shell against a fake gh, never the network."""

import json
import os
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

import release

FAKE_GH = """#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
args = sys.argv[1:]
with Path("calls.jsonl").open("a") as stream:
    stream.write(json.dumps(args) + "\\n")
scenario = os.environ["SCENARIO"]
command = args[1]
if command == "view":
    fields = args[args.index("--json") + 1]
    if fields == "isDraft":
        if scenario in ("new", "prerelease"):
            print("release not found", file=sys.stderr)
            sys.exit(1)
        if scenario == "auth":
            print("HTTP 403: forbidden", file=sys.stderr)
            sys.exit(1)
        print(json.dumps({"isDraft": scenario != "published"}))
    elif fields == "assets":
        names = sorted(p.name for p in Path("dist").iterdir())
        if scenario == "missing": names.pop()
        print(json.dumps({"assets": [{"name": name} for name in names]}))
    else:
        print(json.dumps({"isDraft": False, "url": "https://example.invalid/release"}))
elif command == "upload" and scenario == "upload-failure":
    sys.exit(1)
"""


class PublicationTests(unittest.TestCase):
    def invoke(self, scenario):
        workflow = (release.ROOT / ".github/workflows/release.yml").read_text()
        script = textwrap.dedent(
            workflow.split(
                "      - name: Upload to a draft, then publish\n        run: |\n", 1
            )[1]
        )
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "gh").write_text(FAKE_GH)
            (root / "gh").chmod(0o755)
            (root / "dist").mkdir()
            (root / "dist/archive.tar.gz").write_bytes(b"archive")
            (root / "dist/SHA256SUMS").write_text("test fixture")
            env = {
                **os.environ,
                "PATH": str(root) + os.pathsep + os.environ["PATH"],
                "SCENARIO": scenario,
                "TAG": "rshellcheck-v0.11.0",
                "LABEL": "0.11.0-rc.1" if scenario == "prerelease" else "0.11.0",
            }
            result = subprocess.run(
                ["bash", "-c", script],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
                check=False,
                timeout=15,
            )
            calls = [
                json.loads(line)
                for line in (root / "calls.jsonl").read_text().splitlines()
            ]
            return result, calls

    def test_new_release_uploads_and_verifies_before_publication(self):
        result, calls = self.invoke("new")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            [call[1] for call in calls],
            ["view", "create", "upload", "view", "edit", "view"],
        )
        self.assertIn("--verify-tag", calls[1])
        self.assertIn("--draft", calls[1])
        self.assertIn("--draft=false", calls[-2])

    def test_draft_resumes_without_recreating_release(self):
        result, calls = self.invoke("draft")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("create", [call[1] for call in calls])

    def test_prerelease_is_marked(self):
        result, calls = self.invoke("prerelease")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(
            "--prerelease", next(call for call in calls if call[1] == "create")
        )

    def test_published_release_is_not_modified(self):
        result, calls = self.invoke("published")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual([call[1] for call in calls], ["view"])

    def test_auth_failure_is_not_treated_as_missing_release(self):
        result, calls = self.invoke("auth")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual([call[1] for call in calls], ["view"])

    def test_failed_or_incomplete_upload_never_publishes(self):
        for scenario in ("upload-failure", "missing"):
            with self.subTest(scenario=scenario):
                result, calls = self.invoke(scenario)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn("edit", [call[1] for call in calls])


if __name__ == "__main__":
    unittest.main()
