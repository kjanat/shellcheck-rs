"""Resume partial publication without uploading an accepted version twice."""

import json
import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch

from npm_publish import plan, publish_one, registry_integrity, wait_for_integrity


def response(
    code: str | None = None, digest: str = "sha512-ok"
) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(
        [],
        int(code is not None),
        json.dumps({"error": {"code": code}}) if code else json.dumps(digest),
        code or "",
    )


class VisibilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.enterContext(
            patch(
                "npm_publish.members",
                return_value={
                    "package/package.json": b'{"name":"example","version":"0.11.0"}'
                },
            )
        )
        self.enterContext(patch("npm_publish.integrity", return_value="sha512-ok"))
        self.enterContext(patch("registry_checks.time.sleep"))

    def test_existing_package_is_never_uploaded(self) -> None:
        with patch("npm_publish.subprocess.run", return_value=response()) as run:
            publish_one(Path("package.tgz"))
        self.assertEqual(run.call_count, 1)
        self.assertEqual(run.call_args.args[0][:2], ["npm", "view"])

    def test_accepted_upload_is_only_verified_after_conflicts_or_timeout(self) -> None:
        errors = [
            subprocess.CalledProcessError(1, ["npm", "publish"], stderr=message)
            for message in [
                "npm error E403 You cannot publish over the previously published versions: 0.11.0.",
                'npm error E409 Cannot publish over previously staged version "0.11.0".',
            ]
        ]
        for outcome in [
            *errors,
            subprocess.TimeoutExpired(["npm", "publish"], 120),
            response(),
        ]:
            with (
                self.subTest(outcome=outcome),
                patch(
                    "npm_publish.subprocess.run",
                    side_effect=[
                        response("E404"),
                        outcome,
                        response("E404"),
                        response("E503"),
                        response(),
                    ],
                ) as run,
            ):
                publish_one(Path("package.tgz"))
                commands = [c.args[0][:2] for c in run.call_args_list]
                self.assertEqual(commands.count(["npm", "publish"]), 1)
                self.assertEqual(commands.count(["npm", "view"]), 4)

    def test_transient_preflight_errors_do_not_trigger_publication(self) -> None:
        for failure in [
            response("E429"),
            response("E502"),
            response("ECONNRESET"),
            response("EAI_AGAIN"),
            subprocess.TimeoutExpired(["npm", "view"], 30),
        ]:
            with (
                self.subTest(failure=failure),
                patch(
                    "npm_publish.subprocess.run", side_effect=[failure, response()]
                ) as run,
            ):
                publish_one(Path("package.tgz"))
                self.assertTrue(
                    all(c.args[0][:2] == ["npm", "view"] for c in run.call_args_list)
                )

    def test_authentication_and_integrity_errors_fail(self) -> None:
        for code in ["E401", "E403", "E409"]:
            with (
                self.subTest(code=code),
                patch("npm_publish.subprocess.run", return_value=response(code)) as run,
            ):
                with self.assertRaises(RuntimeError):
                    publish_one(Path("package.tgz"))
                self.assertEqual(run.call_count, 1)
        for preexisting in [True, False]:
            replies = (
                [response(digest="sha512-wrong")]
                if preexisting
                else [response("E404"), response(), response(digest="sha512-wrong")]
            )
            with (
                self.subTest(preexisting=preexisting),
                patch("npm_publish.subprocess.run", side_effect=replies),
                self.assertRaises(ValueError),
            ):
                publish_one(Path("package.tgz"))

    def test_unrelated_publish_conflicts_are_not_swallowed(self) -> None:
        for message in [
            "npm error E403 permission denied",
            "npm error E409 unknown conflict",
        ]:
            with (
                self.subTest(message=message),
                patch(
                    "npm_publish.subprocess.run",
                    side_effect=[
                        response("E404"),
                        subprocess.CalledProcessError(
                            1, ["npm", "publish"], stderr=message
                        ),
                    ],
                ),
                patch("npm_publish.wait_for_integrity") as wait,
            ):
                with self.assertRaises(subprocess.CalledProcessError):
                    publish_one(Path("package.tgz"))
                wait.assert_not_called()

    def test_wait_uses_wall_clock_deadline_including_request_time(self) -> None:
        with (
            patch("registry_checks.time.monotonic", side_effect=[0, 590, 601]),
            patch("npm_publish.subprocess.run", return_value=response("E404")) as run,
        ):
            with self.assertRaises(TimeoutError):
                wait_for_integrity("example@0.11.0", "sha512-ok")
            self.assertEqual(run.call_args.kwargs["timeout"], 10)

    def test_missing_preflight_is_not_retried(self) -> None:
        with patch("npm_publish.subprocess.run", return_value=response("E404")) as run:
            self.assertIsNone(registry_integrity("example@0.11.0"))
            self.assertEqual(run.call_count, 1)

    def test_planner_only_schedules_missing_packages(self) -> None:
        names = [
            "@rshellcheck/rshellcheck-linux-x64",
            "@rshellcheck/rshellcheck-win32-x64",
            "@kjanat/rshellcheck-wasm",
            "@kjanat/rshellcheck",
        ]
        paths = [Path(str(i)) for i in range(len(names))]
        with (
            patch("npm_publish.archives", return_value=paths),
            patch(
                "npm_publish.package_spec",
                side_effect=lambda p: names[int(p.name)] + "@0.11.0",
            ),
            patch(
                "npm_publish.already_published",
                side_effect=lambda p: p.name in {"0", "2"},
            ),
        ):
            result = plan(Path("dist"))
        self.assertEqual(json.loads(result["matrix"]), {"package": [names[1]]})
        self.assertEqual(
            (result["native"], result["wasm"], result["launcher"]),
            ("true", "false", "true"),
        )
        with (
            patch("npm_publish.archives", return_value=paths),
            patch("npm_publish.already_published", return_value=True),
        ):
            result = plan(Path("dist"))
        self.assertEqual(json.loads(result["matrix"]), {"package": []})
        self.assertEqual(
            (result["native"], result["wasm"], result["launcher"]),
            ("false", "false", "false"),
        )
