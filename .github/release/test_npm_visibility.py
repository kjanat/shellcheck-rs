"""Registry propagation must not turn an accepted publication into a failure."""

import subprocess
import unittest
from unittest.mock import patch

from npm_publish import wait_for_integrity


class VisibilityTests(unittest.TestCase):
    def test_waits_for_processing_without_republishing(self) -> None:
        missing = subprocess.CalledProcessError(
            1, ["npm", "view"], output='{"error":{"code":"E404"}}'
        )
        with (
            patch(
                "npm_publish.subprocess.check_output",
                side_effect=[missing, missing, '"sha512-ok"'],
            ) as view,
            patch("npm_publish.time.sleep") as sleep,
        ):
            wait_for_integrity("package@1.0.0", "sha512-ok")
            self.assertEqual(view.call_count, 3)
            self.assertEqual(sleep.call_count, 2)

    def test_authentication_and_integrity_errors_are_not_retried(self) -> None:
        with (
            patch(
                "npm_publish.subprocess.check_output",
                side_effect=subprocess.CalledProcessError(
                    1, ["npm", "view"], output='{"error":{"code":"E401"}}'
                ),
            ),
            patch("npm_publish.time.sleep") as sleep,
            self.assertRaises(subprocess.CalledProcessError),
        ):
            wait_for_integrity("package@1.0.0", "sha512-ok")
        sleep.assert_not_called()
        with (
            patch("npm_publish.subprocess.check_output", return_value='"sha512-wrong"'),
            self.assertRaises(ValueError),
        ):
            wait_for_integrity("package@1.0.0", "sha512-ok")

    def test_visibility_wait_is_bounded(self) -> None:
        with (
            patch(
                "npm_publish.subprocess.check_output",
                side_effect=subprocess.CalledProcessError(
                    1, ["npm", "view"], output='{"error":{"code":"E404"}}'
                ),
            ),
            patch("npm_publish.time.sleep") as sleep,
            self.assertRaises(TimeoutError),
        ):
            wait_for_integrity("package@1.0.0", "sha512-ok")
        self.assertEqual(sleep.call_count, 30)

    def test_resume_after_accepted_but_invisible_publication(self) -> None:
        from pathlib import Path

        from npm_publish import publish_one

        missing = subprocess.CompletedProcess([], 1, '{"error":{"code":"E404"}}', "")
        conflict = subprocess.CalledProcessError(
            1,
            ["npm", "publish"],
            stderr="npm error E403 You cannot publish over the previously published versions: 0.11.0.",
        )
        with (
            patch(
                "npm_publish.members",
                return_value={
                    "package/package.json": b'{"name":"example","version":"0.11.0"}'
                },
            ),
            patch("npm_publish.integrity", return_value="sha512-ok"),
            patch("npm_publish.subprocess.run", side_effect=[missing, conflict]),
            patch(
                "npm_publish.subprocess.check_output",
                side_effect=[
                    subprocess.CalledProcessError(
                        1, ["npm", "view"], output='{"error":{"code":"E404"}}'
                    ),
                    '"sha512-ok"',
                ],
            ) as view,
            patch("npm_publish.time.sleep"),
        ):
            publish_one(Path("package.tgz"))
            self.assertEqual(view.call_count, 2)

    def test_publish_permission_failure_is_not_a_version_conflict(self) -> None:
        from pathlib import Path

        from npm_publish import publish_one

        with (
            patch(
                "npm_publish.members",
                return_value={
                    "package/package.json": b'{"name":"example","version":"0.11.0"}'
                },
            ),
            patch(
                "npm_publish.subprocess.run",
                side_effect=[
                    subprocess.CompletedProcess([], 1, '{"error":{"code":"E404"}}', ""),
                    subprocess.CalledProcessError(
                        1, ["npm", "publish"], stderr="npm error E403 permission denied"
                    ),
                ],
            ),
            patch("npm_publish.wait_for_integrity") as wait,
            self.assertRaises(subprocess.CalledProcessError),
        ):
            publish_one(Path("package.tgz"))
        wait.assert_not_called()
