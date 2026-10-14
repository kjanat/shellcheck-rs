"""Moving aliases preserve release identity and do not promote prereleases."""

import base64
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import release
import release_aliases as aliases


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
            patch.object(aliases.subprocess, "run") as run,
        ):
            aliases.promote_image(
                "ghcr.io/example/image:1.0.0", "ghcr.io/example/image:upstream-0.11.0"
            )
            self.assertIn("ghcr.io/example/image@" + digest, run.call_args.args[0])
        with (
            patch.object(aliases, "output", side_effect=[digest, "sha256:" + "b" * 64]),
            patch.object(aliases.subprocess, "run"),
        ):
            with self.assertRaisesRegex(ValueError, "digest mismatch"):
                aliases.promote_image(
                    "ghcr.io/example/image:1.0.0",
                    "ghcr.io/example/image:upstream-0.11.0",
                )

    def test_npm_alias_checks_registry_result(self):
        with (
            patch.object(
                aliases, "output", return_value='{"upstream-0.11.0":"0.11.1"}'
            ),
            patch.object(aliases.subprocess, "run") as run,
        ):
            aliases.promote_npm(
                "@rshellcheck/rshellcheck-linux-x64", "0.11.1", "upstream-0.11.0"
            )
            self.assertEqual(
                run.call_args.args[0][1:5],
                [
                    "dist-tag",
                    "add",
                    "@rshellcheck/rshellcheck-linux-x64@0.11.1",
                    "upstream-0.11.0",
                ],
            )
        with (
            patch.object(aliases, "output", return_value="{}"),
            patch.object(aliases.subprocess, "run"),
        ):
            with self.assertRaisesRegex(ValueError, "npm alias mismatch"):
                aliases.promote_npm("@kjanat/rshellcheck", "0.11.1", "upstream-0.11.0")

    def test_git_promotion_is_last_and_verified(self):
        meta = {"version": "0.11.1", "commit": "a" * 40, "rust": "1.99.0"}
        alias = "upstream-0.11.0"
        for exists in (False, True):
            with self.subTest(exists=exists), tempfile.TemporaryDirectory() as temp:
                directory = Path(temp)
                (directory / aliases.MANIFEST).write_text('{"packages":[]}')
                responses = [
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
                        aliases.os.environ,
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
                        api.call_args.args[0].endswith(f"/git/ref/tags/{alias}")
                    )

    def test_upstream_pin_is_validated(self):
        with (
            tempfile.TemporaryDirectory() as temp,
            patch.object(release, "ROOT", Path(temp)),
        ):
            (Path(temp) / "tools").mkdir()
            pin = Path(temp) / "tools/oracle.json"
            pin.write_text(json.dumps({"version": "0.11.0", "revision": "a" * 40}))
            self.assertEqual(release.upstream()["upstream_version"], "0.11.0")
            pin.write_text(json.dumps({"version": "0.11.0-dev", "revision": "a" * 40}))
            with self.assertRaises(ValueError):
                release.upstream()
