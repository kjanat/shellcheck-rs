"""Reject stale or modified oracle caches instead of silently accepting parity."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import oracle


class OracleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.cache = self.root / ".cache"
        self.source = self.cache / "upstream-shellcheck"
        self.source.mkdir(parents=True)
        (self.root / "tools").mkdir()
        self.pin = {
            "revision": "a" * 40,
            "repository": "koalaman/shellcheck",
            "version": "0.11.0",
        }
        (self.root / "tools/oracle.json").write_text(json.dumps(self.pin))
        self.binary = self.cache / "shellcheck-oracle"
        for name, value in [
            ("ROOT", self.root),
            ("CACHE", self.cache),
            ("SOURCE", self.source),
            ("BINARY", self.binary),
        ]:
            mock = patch.object(oracle, name, value)
            mock.start()
            self.addCleanup(mock.stop)

    def test_matching_clean_checkout(self):
        with patch.object(oracle, "run", side_effect=[self.pin["revision"], ""]):
            self.assertEqual(oracle.prepare(), self.pin)

    def test_wrong_revision_is_not_overwritten(self):
        with patch.object(oracle, "run", return_value="b" * 40):
            with self.assertRaisesRegex(ValueError, "different revision"):
                oracle.prepare()

    def test_modified_source_is_rejected(self):
        with patch.object(
            oracle,
            "run",
            side_effect=[self.pin["revision"], " M src/ShellCheck/Parser.hs"],
        ):
            with self.assertRaisesRegex(ValueError, "local changes"):
                oracle.prepare()

    def test_binary_digest_and_source_pin_are_checked(self):
        self.binary.write_bytes(b"oracle")
        metadata = {**self.pin, "sha256": hashlib.sha256(b"oracle").hexdigest()}
        (self.cache / "shellcheck-oracle.json").write_text(json.dumps(metadata))
        oracle.verify(self.pin)
        with self.assertRaisesRegex(ValueError, "does not match"):
            oracle.verify({**self.pin, "revision": "b" * 40})
        self.binary.write_bytes(b"stale oracle")
        with self.assertRaisesRegex(ValueError, "does not match"):
            oracle.verify(self.pin)


if __name__ == "__main__":
    unittest.main()
