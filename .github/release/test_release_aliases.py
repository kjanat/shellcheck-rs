"""Moving aliases preserve release identity and do not promote prereleases."""

import base64
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import cast
from unittest.mock import patch

import release
import release_aliases as aliases
from native_packages import MANIFEST


class AliasTests(unittest.TestCase):
    def test_versions_only_move_forward(self):
        self.assertTrue(aliases.advance("0.11.0", None))
        self.assertTrue(aliases.advance("0.11.10", "0.11.9"))
        self.assertTrue(aliases.advance("0.11.0", "0.11.0"))
        self.assertFalse(aliases.advance("0.11.0", "0.11.1"))
        self.assertFalse(aliases.advance("0.12.0-rc.1", None))

    def test_image_alias_uses_and_verifies_exact_digest(self):
        digest = "sha256:" + "a" * 64
        with (
            patch.object(aliases, "output", side_effect=[digest, digest]),
            patch.object(subprocess, "run") as run,
        ):
            aliases.promote_image(
                "ghcr.io/example/image:1.0.0", "ghcr.io/example/image:upstream-0.11.0"
            )
            self.assertIn(
                "ghcr.io/example/image@" + digest,
                cast(list[str], run.call_args.args[0]),
            )
        with (
            patch.object(aliases, "output", side_effect=[digest, "sha256:" + "b" * 64]),
            patch.object(subprocess, "run"),
            self.assertRaisesRegex(ValueError, "digest mismatch"),
        ):
            aliases.promote_image(
                "ghcr.io/example/image:1.0.0",
                "ghcr.io/example/image:upstream-0.11.0",
            )

    def test_npm_alias_waits_for_visibility_without_rewriting(self):
        with (
            patch.object(
                aliases, "npm_tags", side_effect=[{}, {}, {"upstream-0.11.0": "0.11.1"}]
            ),
            patch.object(subprocess, "run") as run,
            patch("registry_checks.time.sleep"),
        ):
            aliases.promote_npm(
                "@rshellcheck/rshellcheck-linux-x64", "0.11.1", "upstream-0.11.0"
            )
            self.assertEqual(run.call_count, 1)
            self.assertEqual(
                cast(list[str], run.call_args.args[0])[1:5],
                [
                    "dist-tag",
                    "add",
                    "@rshellcheck/rshellcheck-linux-x64@0.11.1",
                    "upstream-0.11.0",
                ],
            )

    def test_existing_alias_does_not_get_written_again(self):
        with (
            patch.object(
                aliases, "npm_tags", return_value={"upstream-0.11.0": "0.11.1"}
            ),
            patch.object(subprocess, "run") as run,
        ):
            aliases.promote_npm("@kjanat/rshellcheck", "0.11.1", "upstream-0.11.0")
            run.assert_not_called()
        with (
            patch.object(
                aliases, "npm_tags", return_value={"upstream-0.11.0": "0.11.2"}
            ),
            patch.object(subprocess, "run") as run,
        ):
            with self.assertRaises(ValueError):
                aliases.promote_npm("@kjanat/rshellcheck", "0.11.1", "upstream-0.11.0")
            run.assert_not_called()

    def test_git_promotion_is_last_and_verified(self):
        meta = {"version": "0.11.1", "commit": "a" * 40, "rust": "1.99.0"}
        alias = "upstream-0.11.0"
        for exists in (False, True):
            with self.subTest(exists=exists), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                _ = (directory / MANIFEST).write_text('{"packages":[]}')
                responses: list[object] = [
                    [
                        {
                            "ref": f"refs/tags/{alias}",
                            "object": {"type": "commit", "sha": "b" * 40},
                        }
                    ]
                    if exists
                    else []
                ]
                if exists:
                    responses.append({
                        "content": base64.b64encode(
                            b'[package]\nversion="0.11.0"'
                        ).decode()
                    })
                responses += [
                    {"commit": {"verification": {"verified": True}}},
                    {},
                    {"object": {"sha": meta["commit"]}},
                ]
                with (
                    patch.dict(
                        os.environ,
                        {"GITHUB_REPOSITORY": "kjanat/shellcheck-rs"},
                    ),
                    patch.object(aliases, "metadata", return_value=meta),
                    patch.object(aliases, "verify_bindings"),
                    patch.object(aliases, "verify_native"),
                    patch.object(aliases, "load_record", return_value={"packages": []}),
                    patch.object(aliases, "api", side_effect=responses) as api,
                    patch.object(aliases, "promote_image") as image,
                ):
                    aliases.promote(directory)
                    self.assertEqual(image.call_count, 1 + len(release.TARGETS))
                    self.assertIn(
                        "PATCH" if exists else "POST", api.call_args_list[-2].args
                    )
                    self.assertTrue(
                        cast(str, api.call_args.args[0]).endswith(
                            f"/git/ref/tags/{alias}"
                        )
                    )

    def test_npm_only_promotion_does_not_write_git_or_docker_tags(self):
        with (
            patch.dict(
                os.environ,
                {"GITHUB_REPOSITORY": "kjanat/shellcheck-rs", "REGISTRY": "npm"},
            ),
            patch.object(
                aliases,
                "metadata",
                return_value={"version": "0.11.0", "commit": "a" * 40},
            ),
            patch.object(aliases, "verify_bindings"),
            patch.object(aliases, "verify_native"),
            patch.object(aliases, "load_native_record", return_value={"packages": []}),
            patch.object(aliases, "load_record", return_value={"packages": []}),
            patch.object(
                aliases,
                "api",
                side_effect=[[], {"commit": {"verification": {"verified": True}}}],
            ) as api,
            patch.object(aliases, "promote_image") as image,
        ):
            aliases.promote(Path("dist"))
            self.assertEqual(api.call_count, 2)
            image.assert_not_called()

    def test_alias_reads_retry_transient_errors_but_reject_permission_errors(self):
        with (
            patch.object(
                subprocess,
                "check_output",
                side_effect=subprocess.CalledProcessError(
                    1, ["npm", "view"], output='{"error":{"code":"E503"}}'
                ),
            ),
            self.assertRaises(aliases.NotVisibleYet),
        ):
            aliases.npm_tags("example", 30)
        with (
            patch.object(
                subprocess,
                "check_output",
                side_effect=subprocess.CalledProcessError(
                    1, ["npm", "view"], output='{"error":{"code":"E403"}}'
                ),
            ),
            self.assertRaises(subprocess.CalledProcessError),
        ):
            aliases.npm_tags("example", 30)

    def test_upstream_pin_is_validated(self):
        with (
            tempfile.TemporaryDirectory() as temp,
            patch.object(release, "ROOT", Path(temp)),
        ):
            (Path(temp) / "tools").mkdir()
            pin = Path(temp) / "tools/oracle.json"
            _ = pin.write_text(json.dumps({"version": "0.11.0", "revision": "a" * 40}))
            self.assertEqual(release.upstream()["upstream_version"], "0.11.0")
            _ = pin.write_text(
                json.dumps({"version": "0.11.0-dev", "revision": "a" * 40})
            )
            with self.assertRaises(ValueError):
                _ = release.upstream()
