"""Release-contract tests: wrong versions, architectures and incomplete payloads."""

import hashlib
import io
import struct
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest.mock import patch

import release


def executable(target):
    data = bytearray(128)
    arch = target.split("-")[0]
    if "windows" in target:
        data[:2] = b"MZ"
        struct.pack_into("<I", data, 0x3C, 64)
        data[64:68] = b"PE\0\0"
        struct.pack_into(
            "<H", data, 68, {"x86_64": 0x8664, "i686": 0x14C, "aarch64": 0xAA64}[arch]
        )
    elif "darwin" in target:
        struct.pack_into(
            "<II",
            data,
            0,
            0xFEEDFACF,
            {"x86_64": 0x1000007, "aarch64": 0x100000C}[arch],
        )
    else:
        data[:6] = b"\x7fELF" + bytes([2 if arch in ("x86_64", "aarch64") else 1, 1])
        if "freebsd" in target:
            data[7] = 9
        struct.pack_into(
            "<H", data, 18, {"x86_64": 62, "i686": 3, "aarch64": 183, "armv7": 40}[arch]
        )
    return bytes(data)


class ReleaseTests(unittest.TestCase):
    def test_only_exact_push_tag_publishes(self):
        tag = "refs/tags/" + release.PREFIX + release.metadata()["version"]
        self.assertTrue(release.plan(tag, "push")["publish"])
        for event in ("pull_request", "workflow_dispatch"):
            self.assertFalse(release.plan(tag, event)["publish"])
        with self.assertRaisesRegex(ValueError, "Tag must be"):
            release.plan("refs/tags/rshellcheck-v999.0.0", "push")

    def test_matrix_has_unique_archives(self):
        matrix = release.plan()["matrix"]["include"]
        self.assertEqual(len(matrix), 15)
        self.assertEqual(
            len({release.archive_name("0.11.0", t["target"]) for t in matrix}), 15
        )

    def test_architecture_headers(self):
        for target, _, _ in release.TARGETS:
            with self.subTest(target=target):
                release.verify_binary(executable(target), target)
                bad = bytearray(executable(target))
                bad[0] = 0
                with self.assertRaises(ValueError):
                    release.verify_binary(bad, target)
        with self.assertRaises(ValueError):
            release.verify_binary(
                executable("x86_64-unknown-linux-musl"), "i686-unknown-linux-musl"
            )

    def test_linux_binary_cannot_be_labelled_freebsd(self):
        with self.assertRaises(ValueError):
            release.verify_binary(
                executable("x86_64-unknown-linux-musl"), "x86_64-unknown-freebsd"
            )

    def test_musl_must_be_static(self):
        target = "x86_64-unknown-linux-musl"
        data = bytearray(executable(target))
        struct.pack_into("<Q", data, 32, 64)
        struct.pack_into("<HH", data, 54, 56, 1)
        struct.pack_into("<I", data, 64, 3)  # PT_INTERP
        with self.assertRaises(ValueError):
            release.verify_binary(data, target)

    def pack(self, directory, target, label="test"):
        binary = directory / (
            "rshellcheck.exe" if "windows" in target else "rshellcheck"
        )
        binary.write_bytes(executable(target))
        return release.pack(target, label, binary, directory / "dist")

    def test_archives_reproducible_and_executable(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for target in ("x86_64-pc-windows-msvc", "x86_64-unknown-linux-musl"):
                archive = self.pack(directory, target)
                first = archive.read_bytes()
                self.pack(directory, target)
                self.assertEqual(first, archive.read_bytes())
                if archive.suffix == ".zip":
                    with zipfile.ZipFile(archive) as contents:
                        self.assertEqual(len(contents.namelist()), 4)
                        binary = next(
                            x
                            for x in contents.infolist()
                            if x.filename.endswith(".exe")
                        )
                        self.assertEqual((binary.external_attr >> 16) & 0o777, 0o755)
                else:
                    with tarfile.open(archive) as contents:
                        self.assertEqual(len(contents.getmembers()), 4)
                        self.assertEqual(
                            contents.getmember(
                                f"rshellcheck-test-{target}/rshellcheck"
                            ).mode,
                            0o755,
                        )

    def test_archive_member_must_be_regular_file(self):
        buffer = io.BytesIO()
        with tarfile.open(fileobj=buffer, mode="w") as archive:
            info = tarfile.TarInfo("rshellcheck")
            info.type = tarfile.DIRTYPE
            archive.addfile(info)
        buffer.seek(0)
        with (
            tarfile.open(fileobj=buffer) as archive,
            self.assertRaisesRegex(ValueError, "not a regular file"),
        ):
            release.read_member(archive, "rshellcheck")

    def test_assembly_requires_every_target(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            self.pack(directory, release.TARGETS[0][0])
            with self.assertRaisesRegex(ValueError, "Incomplete release"):
                release.assemble("test", directory / "dist")

    def test_assembly_rejects_foreign_commit(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for target, _, _ in release.TARGETS:
                self.pack(directory, target)
            meta = {**release.metadata(), "commit": "0" * 40}
            with (
                patch.object(release, "metadata", return_value=meta),
                self.assertRaisesRegex(ValueError, "mismatched commit"),
            ):
                release.assemble("test", directory / "dist")

    def test_assembly_checksums_cover_all_binaries_and_source(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for target, _, _ in release.TARGETS:
                self.pack(directory, target)
            assets = release.assemble("test", directory / "dist")
            self.assertEqual(len(assets), 16)
            checksums = (directory / "dist/SHA256SUMS").read_text().splitlines()
            self.assertEqual(len(checksums), 16)
            for line in checksums:
                digest, name = line.split("  ")
                self.assertEqual(
                    digest,
                    hashlib.sha256(
                        (directory / "dist" / name).read_bytes()
                    ).hexdigest(),
                )
            with tarfile.open(
                directory / "dist/rshellcheck-test-source.tar.gz"
            ) as source:
                self.assertIn("rshellcheck-test/Cargo.lock", source.getnames())


if __name__ == "__main__":
    unittest.main()
