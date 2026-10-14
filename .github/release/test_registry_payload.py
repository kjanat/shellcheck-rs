"""Regression tests for registry publication from immutable releases."""

import os
import subprocess
import unittest
from unittest.mock import patch

import release


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
