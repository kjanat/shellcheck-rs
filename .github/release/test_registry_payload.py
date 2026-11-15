"""Regression tests for registry publication from immutable releases."""

import hashlib
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import binding_packages
import registry_payload
import release
import test_binding_packages


class RegistryDispatchTests(unittest.TestCase):
    def test_source_metadata_reads_pinned_commit(self) -> None:
        sha = "a" * 40
        with (
            patch.dict(os.environ, {"RELEASE_SOURCE_COMMIT": sha}),
            patch.object(release, "git", return_value="pinned") as git,
        ):
            self.assertEqual(release.source_text(release.ROOT / "Cargo.toml"), "pinned")
            git.assert_called_once_with("show", f"{sha}:Cargo.toml")

    def test_invalid_source_commit_is_rejected(self) -> None:
        with (
            patch.dict(os.environ, {"RELEASE_SOURCE_COMMIT": "master"}),
            self.assertRaisesRegex(ValueError, "full commit SHA"),
        ):
            _ = release.source_text(release.ROOT / "Cargo.toml")

    def test_dispatch_rejects_other_version_and_event(self) -> None:
        for tag, event in (
            ("rshellcheck-v99.0.0", "workflow_dispatch"),
            ("rshellcheck-v0.11.0", "push"),
        ):
            with (
                patch.dict(os.environ, {"PUBLISH_EXISTING": tag}),
                self.assertRaisesRegex(ValueError, "match the package version"),
            ):
                _ = release.plan("refs/heads/master", event)

    def test_mutable_or_draft_release_is_rejected(self) -> None:
        for state in (
            '{"isDraft":true,"isImmutable":true}',
            '{"isDraft":false,"isImmutable":false}',
        ):
            with (
                self.subTest(state=state),
                patch.dict(os.environ, {"PUBLISH_EXISTING": "rshellcheck-v0.11.0"}),
                patch.object(release, "cargo_version", return_value="0.11.0"),
                patch.object(
                    release,
                    "run",
                    return_value=subprocess.CompletedProcess([], 0, state),
                ),
                self.assertRaisesRegex(ValueError, "immutable published release"),
            ):
                _ = release.plan("", "workflow_dispatch")

    def test_unsigned_release_is_rejected(self) -> None:
        with (
            patch.dict(
                os.environ,
                {
                    "PUBLISH_EXISTING": "rshellcheck-v0.11.0",
                    "GITHUB_REPOSITORY": "kjanat/shellcheck-rs",
                },
            ),
            patch.object(release, "cargo_version", return_value="0.11.0"),
            patch.object(release, "git", return_value="a" * 40),
            patch.object(
                release,
                "run",
                side_effect=[
                    subprocess.CompletedProcess(
                        [], 0, '{"isDraft":false,"isImmutable":true}'
                    ),
                    subprocess.CompletedProcess([], 0, "false"),
                ],
            ),
            self.assertRaisesRegex(ValueError, "signature"),
        ):
            _ = release.plan("", "workflow_dispatch")


class LegacyRecoveryTests(unittest.TestCase):
    def test_existing_release_normalizes_verified_legacy_and_current_modules(self):
        for name in ("shellcheck_wasm.wasm", binding_packages.WASM_NAME):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                original, dest = root / "original", root / "dest"
                original.mkdir()
                test_binding_packages.PackageTests().make_payload(original, (name,))
                _ = (original / "SHA256SUMS").write_text(
                    "".join(
                        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.name}\n"
                        for path in original.iterdir()
                    )
                )

                def command(*args, source=original):
                    if args[:3] == ("gh", "release", "download"):
                        shutil.copytree(source, Path(args[-1]), dirs_exist_ok=True)

                def repackage(directory, wasm):
                    self.assertEqual(wasm.name, binding_packages.WASM_NAME)
                    self.assertEqual(wasm.read_bytes(), b"\0asm\x01\0\0\0")
                    test_binding_packages.PackageTests().make_payload(directory)

                def native(directory, _version):
                    for manifest in ("native-packages.json", "native-wheels.json"):
                        _ = (directory / manifest).write_text("{}")

                with (
                    patch.dict(os.environ, GITHUB_REPOSITORY="kjanat/shellcheck-rs"),
                    patch.object(registry_payload, "run", side_effect=command),
                    patch.object(registry_payload, "TARGETS", []),
                    patch.object(binding_packages, "build", side_effect=repackage),
                    patch.object(binding_packages, "test_install"),
                    patch.object(
                        registry_payload.native_packages, "build", side_effect=native
                    ),
                    patch.object(registry_payload.native_packages, "test_install"),
                    patch.object(
                        registry_payload.native_packages,
                        "load_record",
                        return_value={"packages": []},
                    ),
                    patch.object(
                        registry_payload.native_wheels, "build", side_effect=native
                    ),
                    patch.object(registry_payload.native_wheels, "test_install"),
                    patch.object(
                        registry_payload.native_wheels,
                        "load_record",
                        return_value={"packages": []},
                    ),
                ):
                    registry_payload.prepare(dest)
                binding_packages.verify(dest)
