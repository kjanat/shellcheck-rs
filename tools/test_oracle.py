"""Reject stale or modified oracle caches instead of silently accepting parity."""

import hashlib
import json
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from unittest.mock import patch

import oracle


@dataclass(frozen=True)
class Layout:
    cache: Path
    binary: Path
    pin: oracle.Pin


class OracleTests(unittest.TestCase):
    def layout(self) -> Layout:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        cache = root / ".cache"
        source = cache / "upstream-shellcheck"
        source.mkdir(parents=True)
        (root / "tools").mkdir()
        pin: oracle.Pin = {
            "revision": "a" * 40,
            "repository": "koalaman/shellcheck",
            "version": "0.11.0",
        }
        _ = (root / "tools/oracle.json").write_text(json.dumps(pin))
        binary = cache / "shellcheck-oracle"
        for name, value in [
            ("ROOT", root),
            ("CACHE", cache),
            ("SOURCE", source),
            ("BINARY", binary),
        ]:
            mock = patch.object(oracle, name, value)
            _ = mock.start()
            self.addCleanup(mock.stop)
        return Layout(cache, binary, pin)

    def test_matching_clean_checkout(self):
        pin = self.layout().pin
        with patch.object(oracle, "run", side_effect=[pin["revision"], ""]):
            self.assertEqual(oracle.prepare(), pin)

    def test_wrong_revision_is_not_overwritten(self):
        _ = self.layout()
        with (
            patch.object(oracle, "run", return_value="b" * 40),
            self.assertRaisesRegex(ValueError, "different revision"),
        ):
            _ = oracle.prepare()

    def test_modified_source_is_rejected(self):
        pin = self.layout().pin
        with (
            patch.object(
                oracle,
                "run",
                side_effect=[pin["revision"], " M src/ShellCheck/Parser.hs"],
            ),
            self.assertRaisesRegex(ValueError, "local changes"),
        ):
            _ = oracle.prepare()

    def test_binary_digest_and_source_pin_are_checked(self):
        layout = self.layout()
        _ = layout.binary.write_bytes(b"oracle")
        metadata = {**layout.pin, "sha256": hashlib.sha256(b"oracle").hexdigest()}
        _ = (layout.cache / "shellcheck-oracle.json").write_text(json.dumps(metadata))
        oracle.verify(layout.pin)
        with self.assertRaisesRegex(ValueError, "does not match"):
            oracle.verify({**layout.pin, "revision": "b" * 40})
        _ = layout.binary.write_bytes(b"stale oracle")
        with self.assertRaisesRegex(ValueError, "does not match"):
            oracle.verify(layout.pin)


if __name__ == "__main__":
    _ = unittest.main()
