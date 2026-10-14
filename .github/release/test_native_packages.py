"""Exercise real npm archives and reject incomplete or mismatched payloads."""

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import native_packages as native
import npm_publish
import release
from test_release import executable


class NativeTests(unittest.TestCase):
    def test_all_platform_archives_and_dependencies(self):
        with tempfile.TemporaryDirectory() as temp:
            dest = Path(temp)
            for target, _, _ in release.TARGETS:
                binary = dest / (
                    "rshellcheck.exe" if "windows" in target else "rshellcheck"
                )
                binary.write_bytes(executable(target))
                release.pack(target, "test", binary, dest)
            native.build(dest, "test")
            record = json.loads((dest / native.MANIFEST).read_text())
            self.assertEqual(len(record["packages"]), 16)
            wrapper = native.members(dest / record["packages"][-1]["file"])
            manifest = json.loads(wrapper["package/package.json"])
            self.assertEqual(len(manifest["optionalDependencies"]), 15)
            self.assertNotIn("scripts", manifest)
            self.assertEqual(manifest["bin"]["rshellcheck"], "bin.mjs")
            path = dest / record["packages"][0]["file"]
            with patch.object(npm_publish.subprocess, "run") as run:
                run.return_value = subprocess.CompletedProcess(
                    [], 0, json.dumps(npm_publish.integrity(path)), ""
                )
                npm_publish.publish_one(path)
                self.assertEqual(run.call_count, 1)
                run.return_value = subprocess.CompletedProcess(
                    [], 0, '"sha512-wrong"', ""
                )
                with self.assertRaises(ValueError):
                    npm_publish.publish_one(path)
                run.return_value = subprocess.CompletedProcess(
                    [], 1, '{"error":{"code":"E401"}}', "unauthorized"
                )
                with self.assertRaises(RuntimeError):
                    npm_publish.publish_one(path)
            with (
                patch.object(npm_publish.subprocess, "run") as run,
                patch.object(npm_publish.subprocess, "check_output") as view,
            ):
                run.side_effect = [
                    subprocess.CompletedProcess([], 1, '{"error":{"code":"E404"}}', ""),
                    subprocess.CompletedProcess([], 0),
                ]
                view.return_value = json.dumps(npm_publish.integrity(path))
                npm_publish.publish_one(path)
                command = run.call_args_list[1].args[0]
                self.assertEqual(command[:2], ["npm", "publish"])
                self.assertIn("--provenance", command)
                self.assertEqual(command[command.index("--tag") + 1], "latest")
            path.write_bytes(b"corrupt")
            with self.assertRaises(ValueError):
                native.verify(dest)

    def test_wrong_source_commit_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            dest = Path(temp)
            target = next(iter(native.platforms().values()))
            binary = dest / "rshellcheck.exe"
            binary.write_bytes(executable(target))
            with patch.object(
                release,
                "metadata",
                return_value={**release.metadata(), "commit": "0" * 40},
            ):
                release.pack(target, "test", binary, dest)
            with self.assertRaisesRegex(ValueError, "source identity"):
                native.build(dest, "test")
