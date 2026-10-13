"""Release-contract tests: wrong versions, architectures and incomplete payloads."""

import hashlib
import io
import os
import struct
import subprocess
import tarfile
import tempfile
import unittest
import zipfile
from pathlib import Path
from typing import cast, get_args
from unittest.mock import patch

import release


def executable(
    target: release.Triple,
    imports: tuple[str, ...] = ("KERNEL32.dll",),
    interpreter: bytes | None = None,
) -> bytes:
    data = bytearray(1024)
    arch = target.split("-", 1)[0]
    wide = arch in ("x86_64", "aarch64")
    if "windows" in target:
        machine = {"x86_64": 0x8664, "i686": 0x14C, "aarch64": 0xAA64}[arch]
        optional_size = 240 if wide else 224
        data[:2] = b"MZ"
        struct.pack_into("<I", data, 0x3C, 64)
        data[64:68] = b"PE\0\0"
        struct.pack_into("<HH", data, 68, machine, 1)
        struct.pack_into("<H", data, 84, optional_size)
        struct.pack_into("<H", data, 88, 0x20B if wide else 0x10B)
        directories = 88 + (112 if wide else 96)
        struct.pack_into("<I", data, directories - 4, 16)
        struct.pack_into("<II", data, directories + 8, 0x1000, 20 * len(imports) + 20)
        struct.pack_into(
            "<IIII", data, 88 + optional_size + 8, 0x200, 0x1000, 0x200, 0x200
        )
        for index, name in enumerate(imports):
            struct.pack_into("<I", data, 0x200 + 20 * index + 12, 0x1100 + 32 * index)
            data[0x300 + 32 * index : 0x300 + 32 * index + len(name)] = name.encode()
    elif "darwin" in target:
        struct.pack_into(
            "<II",
            data,
            0,
            0xFEEDFACF,
            {"x86_64": 0x1000007, "aarch64": 0x100000C}[arch],
        )
    else:
        data[:6] = b"\x7fELF" + bytes([2 if wide else 1, 1])
        if "freebsd" in target:
            data[7] = 9
        struct.pack_into(
            "<H", data, 18, {"x86_64": 62, "i686": 3, "aarch64": 183, "armv7": 40}[arch]
        )
        if interpreter is None and "android" in target:
            interpreter = b"/system/bin/linker64" if wide else b"/system/bin/linker"
        if interpreter is not None:
            path = interpreter + b"\0"
            data[0x200 : 0x200 + len(path)] = path
            if wide:
                struct.pack_into("<Q", data, 32, 64)
                struct.pack_into("<HH", data, 54, 56, 1)
                struct.pack_into("<IIQ", data, 64, 3, 0, 0x200)
                struct.pack_into("<Q", data, 64 + 32, len(path))
            else:
                struct.pack_into("<I", data, 28, 52)
                struct.pack_into("<HH", data, 42, 32, 1)
                struct.pack_into("<II", data, 52, 3, 0x200)
                struct.pack_into("<I", data, 52 + 16, len(path))
    return bytes(data)


class ReleaseTests(unittest.TestCase):
    def test_smoke_preserves_lf_input_on_windows(self):
        def invoke(
            command: list[str], **kwargs: object
        ) -> subprocess.CompletedProcess[bytes]:
            script = kwargs["input"]
            if not isinstance(script, bytes):
                self.fail("smoke must pass stdin as bytes")
            self.assertNotIn("text", kwargs)
            self.assertNotIn(b"\r", script)
            dirty = b"$release_probe" in script
            return subprocess.CompletedProcess(
                command,
                int(dirty),
                b'{"comments":[{"code":2086}]}' if dirty else b'{"comments":[]}',
                b"",
            )

        with (
            patch.object(
                release,
                "run",
                return_value=subprocess.CompletedProcess([], 0, "version: 0.11.0\n"),
            ),
            patch.object(subprocess, "run", side_effect=invoke) as probe,
        ):
            release.smoke(["rshellcheck.exe"], "0.11.0")
        self.assertEqual(probe.call_count, 2)

    def test_only_exact_push_tag_publishes(self):
        tag = "refs/tags/" + release.PREFIX + release.metadata()["version"]
        with patch.object(release, "companion_tag", return_value="go/v0.11.0") as go:
            self.assertTrue(release.plan(tag, "push")["publish"])
        go.assert_called_once()
        for event in ("pull_request", "workflow_dispatch"):
            self.assertFalse(release.plan(tag, event)["publish"])
        with self.assertRaisesRegex(ValueError, "Tag must be"):
            _ = release.plan("refs/tags/rshellcheck-v999.0.0", "push")

    def test_publishing_requires_the_go_tag_on_the_same_commit(self):
        tag = "refs/tags/" + release.PREFIX + release.metadata()["version"]
        with (
            patch.object(release, "git", return_value=""),
            self.assertRaisesRegex(ValueError, "go/v0.11.0 is missing"),
        ):
            _ = release.plan(tag, "push")

    def test_companion_tag_accepts_annotated_and_lightweight_tags(self):
        commit = "a" * 40
        annotated = (
            f"{'b' * 40}\trefs/tags/go/v0.11.0\n{commit}\trefs/tags/go/v0.11.0^{{}}\n"
        )
        lightweight = f"{commit}\trefs/tags/go/v0.11.0\n"
        for listing in (annotated, lightweight):
            with patch.object(release, "git", return_value=listing) as git:
                self.assertEqual(release.companion_tag("0.11.0", commit), "go/v0.11.0")
            git.assert_called_once_with(
                "ls-remote",
                "--tags",
                "origin",
                "refs/tags/go/v0.11.0",
                "refs/tags/go/v0.11.0^{}",
            )
        with (
            patch.object(
                release, "git", return_value=f"{'c' * 40}\trefs/tags/go/v0.11.0\n"
            ),
            self.assertRaisesRegex(ValueError, "points at cccccccccccc"),
        ):
            _ = release.companion_tag("0.11.0", commit)

    def test_matrix_has_unique_archives(self):
        matrix = release.plan()["matrix"]["include"]
        self.assertEqual(len(matrix), 15)
        self.assertEqual(
            len({release.archive_name("0.11.0", t["target"]) for t in matrix}), 15
        )

    def test_triples_match_targets_and_rustc(self):
        triples = {t for t, _, _ in release.TARGETS}
        declared = cast(
            tuple[str, ...], get_args(cast(object, release.Triple.__value__))
        )
        self.assertEqual(set(declared), triples)
        rustc = subprocess.run(
            [
                "rustup",
                "run",
                release.metadata()["rust"],
                "rustc",
                "--print",
                "target-list",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        self.assertLessEqual(triples, set(rustc.stdout.split()))

    def test_architecture_headers(self):
        for target, _, _ in release.TARGETS:
            with self.subTest(target=target):
                release.verify_binary(executable(target), target)
                bad = bytearray(executable(target))
                bad[0] = 0
                with self.assertRaises(ValueError):
                    release.verify_binary(bytes(bad), target)
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
        for target in ("x86_64-unknown-linux-musl", "i686-unknown-linux-musl"):
            with (
                self.subTest(target=target),
                self.assertRaisesRegex(ValueError, "not static"),
            ):
                release.verify_binary(
                    executable(target, interpreter=b"/lib/ld-musl.so.1"), target
                )

    def test_android_needs_the_bionic_linker(self):
        wrong_linkers: list[tuple[release.Triple, bytes]] = [
            ("aarch64-linux-android", b"/system/bin/linker"),
            ("armv7-linux-androideabi", b"/system/bin/linker64"),
            ("x86_64-linux-android", b"/lib64/ld-linux-x86-64.so.2"),
            ("i686-linux-android", b"/lib/ld-linux.so.2"),
        ]
        for target, wrong in wrong_linkers:
            with (
                self.subTest(target=target),
                self.assertRaisesRegex(ValueError, "needs"),
            ):
                release.verify_binary(executable(target, interpreter=wrong), target)
        relabelled: list[tuple[release.Triple, release.Triple]] = [
            ("x86_64-unknown-linux-musl", "x86_64-linux-android"),
            ("i686-unknown-linux-musl", "i686-linux-android"),
        ]
        for musl, android in relabelled:
            with (
                self.subTest(target=android),
                self.assertRaisesRegex(ValueError, "needs"),
            ):
                release.verify_binary(executable(musl), android)

    def test_windows_rejects_dynamic_c_runtime(self):
        for name in (
            "VCRUNTIME140.dll",
            "vcruntime140_1.dll",
            "MSVCP140.dll",
            "ucrtbase.dll",
            "api-ms-win-crt-runtime-l1-1-0.dll",
        ):
            for target in (
                "x86_64-pc-windows-msvc",
                "i686-pc-windows-msvc",
                "aarch64-pc-windows-msvc",
            ):
                with (
                    self.subTest(target=target, dll=name),
                    self.assertRaisesRegex(ValueError, "dynamic C runtime"),
                ):
                    release.verify_binary(
                        executable(target, ("KERNEL32.dll", name)), target
                    )

    def test_windows_pe_format_matches_pointer_width(self):
        with self.assertRaisesRegex(ValueError, "not a i686-pc-windows-msvc PE"):
            data = bytearray(executable("i686-pc-windows-msvc"))
            struct.pack_into("<H", data, 88, 0x20B)
            release.verify_binary(bytes(data), "i686-pc-windows-msvc")
        with self.assertRaisesRegex(ValueError, "not a x86_64-pc-windows-msvc PE"):
            data = bytearray(executable("x86_64-pc-windows-msvc"))
            struct.pack_into("<H", data, 88, 0x10B)
            release.verify_binary(bytes(data), "x86_64-pc-windows-msvc")

    def test_build_smokes_each_target_where_it_runs(self):
        emulators: dict[release.Triple, tuple[str, ...]] = {
            "aarch64-unknown-linux-musl": ("/usr/local/bin/qemu-aarch64",),
            "armv7-unknown-linux-musleabihf": ("/usr/local/bin/qemu-arm",),
            "aarch64-linux-android": ("/android-runner", "aarch64"),
            "armv7-linux-androideabi": ("/android-runner", "arm"),
            "x86_64-linux-android": ("/android-runner", "x86_64"),
            "i686-linux-android": ("/android-runner", "i686"),
        }
        with tempfile.TemporaryDirectory() as temp:
            sdk = Path(temp)
            ndk = sdk / "ndk" / release.NDK_VERSION
            clang_dir = ndk / "toolchains/llvm/prebuilt/linux-x86_64/bin"
            clang_dir.mkdir(parents=True)
            for clang in (
                "aarch64-linux-android",
                "armv7a-linux-androideabi",
                "x86_64-linux-android",
                "i686-linux-android",
            ):
                _ = (clang_dir / f"{clang}{release.ANDROID_API}-clang").write_text("")
            for target, _, _ in release.TARGETS:
                with (
                    self.subTest(target=target),
                    patch.dict(os.environ, ANDROID_HOME=str(sdk)),
                    patch.object(release, "run"),
                    patch.object(release, "verify_binary"),
                    patch.object(Path, "read_bytes", return_value=b""),
                    patch.object(release, "smoke") as smoke,
                ):
                    release.build(target)
                    binary = release.built_binary(target)
                    if "freebsd" in target:
                        expected = []
                    elif target in emulators:
                        expected = [
                            release.emulated(target, binary, *emulators[target])
                        ]
                    else:
                        expected = [[str(binary)]]
                    self.assertEqual(
                        [call.args[0] for call in smoke.call_args_list], expected
                    )

    def pack(
        self, directory: Path, target: release.Triple, label: str = "test"
    ) -> Path:
        binary = directory / (
            "rshellcheck.exe" if "windows" in target else "rshellcheck"
        )
        _ = binary.write_bytes(executable(target))
        return release.pack(target, label, binary, directory / "dist")

    def test_archives_reproducible_and_executable(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for target in ("x86_64-pc-windows-msvc", "x86_64-unknown-linux-musl"):
                archive = self.pack(directory, target)
                first = archive.read_bytes()
                _ = self.pack(directory, target)
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
        _ = buffer.seek(0)
        with (
            tarfile.open(fileobj=buffer) as archive,
            self.assertRaisesRegex(ValueError, "not a regular file"),
        ):
            _ = release.read_member(archive, "rshellcheck")

    def test_assembly_requires_every_target(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            _ = self.pack(directory, release.TARGETS[0][0])
            with self.assertRaisesRegex(ValueError, "Incomplete release"):
                _ = release.assemble("test", directory / "dist")

    def test_assembly_rejects_foreign_commit(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for target, _, _ in release.TARGETS:
                _ = self.pack(directory, target)
            meta = release.Metadata(**release.metadata())
            meta["commit"] = "0" * 40
            with (
                patch.object(release, "metadata", return_value=meta),
                self.assertRaisesRegex(ValueError, "mismatched commit"),
            ):
                _ = release.assemble("test", directory / "dist")

    def test_assembly_checksums_cover_all_binaries_and_source(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for target, _, _ in release.TARGETS:
                _ = self.pack(directory, target)
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
    _ = unittest.main()
