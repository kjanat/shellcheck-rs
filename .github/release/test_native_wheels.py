"""Wheel contents, platform tags, reproducibility and binary identity."""

import base64
import hashlib
import struct
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import native_wheels as wheels
import release
from binding_packages import members
from test_release import executable


class NativeWheelTests(unittest.TestCase):
    def test_wheels_bundle_exact_binaries_and_valid_records(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            dest = Path(temp)
            for target in wheels.TARGETS:
                data = executable(target)
                if "darwin" in target:
                    macho = bytearray(data)
                    struct.pack_into("<I", macho, 16, 1)
                    struct.pack_into("<IIIIII", macho, 32, 0x32, 24, 1, 11 << 16, 0, 0)
                    data = bytes(macho)
                binary = dest / (
                    "rshellcheck.exe" if "windows" in target else "rshellcheck"
                )
                _ = binary.write_bytes(data)
                _ = release.pack(target, "test", binary, dest)
            wheels.build(dest, "test")
            first = wheels.load_record(dest)
            self.assertEqual(len(first["packages"]), 13)
            for package in first["packages"]:
                contents = members(dest / package["name"])
                records = next(
                    data for name, data in contents.items() if name.endswith("/RECORD")
                )
                for line in records.decode().splitlines():
                    name, checksum, size = line.split(",")
                    if name.endswith("/RECORD"):
                        self.assertEqual((checksum, size), ("", ""))
                        continue
                    data = contents[name]
                    self.assertEqual(int(size), len(data))
                    self.assertEqual(
                        checksum,
                        "sha256="
                        + base64
                        .urlsafe_b64encode(hashlib.sha256(data).digest())
                        .decode()
                        .rstrip("="),
                    )
                self.assertTrue(
                    any(name.endswith("/bin/rshellcheck.exe") for name in contents)
                    == ("windows" in package["target"])
                )
                metadata = next(
                    data
                    for name, data in contents.items()
                    if name.endswith("/METADATA")
                )
                self.assertNotIn(b"Requires-Dist:", metadata)
                self.assertIn(b"Name: rshellcheck", metadata)
            wheels.build(dest, "test")
            self.assertEqual(first, wheels.load_record(dest))
            path = dest / first["packages"][0]["name"]
            _ = path.write_bytes(b"corrupt")
            with self.assertRaisesRegex(ValueError, "checksum"):
                wheels.verify(dest)

    def test_macos_deployment_minimum_and_missing_commands(self) -> None:
        data = bytearray(executable("x86_64-apple-darwin"))
        with self.assertRaisesRegex(ValueError, "minimum"):
            _ = wheels.macos_tag(bytes(data), "x86_64-apple-darwin")
        struct.pack_into("<I", data, 16, 1)
        struct.pack_into("<IIII", data, 32, 0x24, 16, (10 << 16) | (12 << 8), 0)
        self.assertEqual(
            wheels.macos_tag(bytes(data), "x86_64-apple-darwin"), "macosx_10_12_x86_64"
        )
        struct.pack_into("<I", data, 40, (11 << 16) | (1 << 8))
        with self.assertRaisesRegex(ValueError, "minor minimum"):
            _ = wheels.macos_tag(bytes(data), "x86_64-apple-darwin")

    def test_wrong_binary_source_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            dest = Path(temp)
            target = next(iter(wheels.TARGETS))
            binary = dest / (
                "rshellcheck.exe" if "windows" in target else "rshellcheck"
            )
            _ = binary.write_bytes(executable(target))
            with patch.object(
                release,
                "metadata",
                return_value={**release.metadata(), "commit": "0" * 40},
            ):
                _ = release.pack(target, "test", binary, dest)
            with self.assertRaisesRegex(ValueError, "source identity"):
                wheels.build(dest, "test")
