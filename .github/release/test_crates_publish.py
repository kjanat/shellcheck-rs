"""crates.io publication resumes safely and never hides a checksum mismatch."""

import hashlib
import io
import json
import subprocess
import tempfile
import unittest
from datetime import UTC, datetime
from email.message import Message
from pathlib import Path
from unittest.mock import MagicMock, patch
from urllib.error import HTTPError, URLError

import crates_publish
from crates_publish import publish, registry_checksum, retry_delay

API = "https://crates.io/api/v1/crates/example/1.0.0"


def response(checksum: str) -> io.BytesIO:
    return io.BytesIO(json.dumps({"version": {"checksum": checksum}}).encode())


def http_error(code: int) -> HTTPError:
    return HTTPError(API, code, "status", Message(), None)


def completed(code: int, stderr: str = "") -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(["cargo", "publish"], code, "", stderr)


class RegistryChecksumTests(unittest.TestCase):
    def test_missing_transient_and_refused_lookups(self) -> None:
        with patch("crates_publish.urlopen", return_value=response("abc")) as read:
            self.assertEqual(registry_checksum("example", "1.0.0"), "abc")
            request = read.call_args.args[0]
            self.assertEqual(request.full_url, API)
            self.assertIn("rshellcheck-release", request.get_header("User-agent"))
        with patch("crates_publish.urlopen", side_effect=http_error(404)):
            self.assertIsNone(registry_checksum("example", "1.0.0"))
        for failure in (
            http_error(503),
            http_error(429),
            URLError("reset"),
            TimeoutError(),
        ):
            with (
                patch("crates_publish.urlopen", side_effect=failure),
                self.assertRaises(crates_publish.NotVisibleYet),
            ):
                _ = registry_checksum("example", "1.0.0")
        with (
            patch("crates_publish.urlopen", side_effect=http_error(403)),
            self.assertRaises(HTTPError),
        ):
            _ = registry_checksum("example", "1.0.0")


class RetryDelayTests(unittest.TestCase):
    def test_rate_limits_wait_and_other_failures_do_not(self) -> None:
        now = datetime(2026, 11, 8, 12, 0, 0, tzinfo=UTC)
        refused = (
            "the remote server responded with an error (status 429 Too Many Requests): "
            "You have published too many new crates in a short period of time. "
            "Please try again after Sun, 08 Nov 2026 12:10:00 GMT or email help@crates.io"
        )
        self.assertEqual(retry_delay(refused, now), 605)
        self.assertEqual(
            retry_delay("Please try again after Sun, 08 Nov 2026 11:00:00 GMT", now), 0
        )
        self.assertEqual(retry_delay("status 429 Too Many Requests"), 90)
        self.assertIsNone(retry_delay("error: failed to verify package tarball"))


class PublishTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.archive = Path(directory.name) / "example-1.0.0.crate"
        _ = self.archive.write_bytes(b"crate bytes")
        self.checksum = hashlib.sha256(b"crate bytes").hexdigest()
        for target, value in (
            ("crates_publish.package", MagicMock(return_value=("1.0.0", self.archive))),
            ("crates_publish.time.sleep", MagicMock()),
            ("registry_checks.time.sleep", MagicMock()),
        ):
            patcher = patch(target, value)
            _ = patcher.start()
            self.addCleanup(patcher.stop)

    def test_an_identical_published_version_is_skipped(self) -> None:
        with (
            patch("crates_publish.registry_checksum", return_value=self.checksum),
            patch("crates_publish.subprocess.run") as run,
        ):
            publish("example")
            run.assert_not_called()

    def test_a_different_published_version_fails_without_uploading(self) -> None:
        with (
            patch("crates_publish.registry_checksum", return_value="other"),
            patch("crates_publish.subprocess.run") as run,
        ):
            with self.assertRaisesRegex(ValueError, "different contents"):
                publish("example")
            run.assert_not_called()

    def test_a_missing_version_is_uploaded_then_verified(self) -> None:
        with (
            patch(
                "crates_publish.registry_checksum",
                side_effect=[None, None, self.checksum],
            ) as lookup,
            patch("crates_publish.subprocess.run", return_value=completed(0)) as run,
        ):
            publish("example")
            self.assertEqual(
                run.call_args.args[0],
                ["cargo", "publish", "--locked", "--no-verify", "-p", "example"],
            )
            self.assertEqual(lookup.call_count, 3)

    def test_a_rate_limited_upload_waits_and_retries(self) -> None:
        refused = completed(101, "status 429 Too Many Requests")
        with (
            patch(
                "crates_publish.registry_checksum", side_effect=[None, self.checksum]
            ),
            patch(
                "crates_publish.subprocess.run", side_effect=[refused, completed(0)]
            ) as run,
            patch("crates_publish.time.sleep") as sleep,
        ):
            publish("example")
            self.assertEqual(run.call_count, 2)
            sleep.assert_called_once_with(90)

    def test_an_upload_that_already_landed_is_verified(self) -> None:
        landed = completed(
            101, "error: crate example@1.0.0 already exists on crates.io index"
        )
        with (
            patch(
                "crates_publish.registry_checksum", side_effect=[None, self.checksum]
            ),
            patch("crates_publish.subprocess.run", return_value=landed) as run,
        ):
            publish("example")
            run.assert_called_once()

    def test_a_refused_upload_fails_and_a_mismatched_upload_is_reported(self) -> None:
        with (
            patch("crates_publish.registry_checksum", return_value=None),
            patch(
                "crates_publish.subprocess.run",
                return_value=completed(101, "error: failed to verify package tarball"),
            ) as run,
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                publish("example")
            run.assert_called_once()
        with (
            patch("crates_publish.registry_checksum", side_effect=[None, "other"]),
            patch("crates_publish.subprocess.run", return_value=completed(0)),
            self.assertRaisesRegex(ValueError, "checksum differs"),
        ):
            publish("example")

    def test_rate_limits_give_up_after_the_last_attempt(self) -> None:
        refused = completed(101, "status 429 Too Many Requests")
        with (
            patch("crates_publish.registry_checksum", return_value=None),
            patch("crates_publish.subprocess.run", return_value=refused) as run,
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                publish("example")
            self.assertEqual(run.call_count, crates_publish.ATTEMPTS)


class PackageTests(unittest.TestCase):
    def test_the_archive_is_named_from_the_metadata(self) -> None:
        metadata = json.dumps({
            "packages": [
                {"name": "other", "version": "9.9.9"},
                {"name": "example", "version": "1.0.0"},
            ],
            "target_directory": "/work/target",
        })
        described = subprocess.CompletedProcess(["cargo", "metadata"], 0, metadata, "")
        with patch(
            "crates_publish.subprocess.run", side_effect=[described, completed(0)]
        ) as run:
            version, archive = crates_publish.package("example")
        self.assertEqual(version, "1.0.0")
        self.assertEqual(archive, Path("/work/target/package/example-1.0.0.crate"))
        self.assertEqual(
            run.call_args.args[0], ["cargo", "package", "--locked", "-p", "example"]
        )
