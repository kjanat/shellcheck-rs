"""PyPI visibility failures must not hide a real checksum mismatch."""

import io
import json
import unittest
from email.message import Message
from unittest.mock import patch
from urllib.error import HTTPError, URLError

from registry_checks import verify_pypi


def payload(digest: str | None = None) -> io.BytesIO:
    return io.BytesIO(
        json.dumps({
            "urls": []
            if digest is None
            else [{"filename": "example.whl", "digests": {"sha256": digest}}]
        }).encode()
    )


class PyPIVisibilityTests(unittest.TestCase):
    def test_waits_for_missing_files_and_transient_failures(self) -> None:
        with (
            patch(
                "registry_checks.urlopen",
                side_effect=[
                    HTTPError("https://pypi.org", 404, "missing", Message(), None),
                    HTTPError("https://pypi.org", 503, "unavailable", Message(), None),
                    URLError("connection reset"),
                    TimeoutError(),
                    payload(),
                    payload("ok"),
                ],
            ) as read,
            patch("registry_checks.time.sleep"),
        ):
            verify_pypi("example", "1.0.0", {"example.whl": "ok"})
            self.assertEqual(read.call_count, 6)

    def test_mismatch_and_auth_errors_fail_immediately(self) -> None:
        with patch("registry_checks.urlopen", return_value=payload("wrong")) as read:
            with self.assertRaises(ValueError):
                verify_pypi("example", "1.0.0", {"example.whl": "ok"})
            self.assertEqual(read.call_count, 1)
        with patch(
            "registry_checks.urlopen",
            side_effect=HTTPError(
                "https://pypi.org", 403, "forbidden", Message(), None
            ),
        ) as read:
            with self.assertRaises(HTTPError):
                verify_pypi("example", "1.0.0", {"example.whl": "ok"})
            self.assertEqual(read.call_count, 1)
