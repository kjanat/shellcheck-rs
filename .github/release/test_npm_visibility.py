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
