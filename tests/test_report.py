import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from bench.analyze import analyze
from bench.report import label, ordered
from bench.schema import Manifest, Run, Samples
from tests.test_memory import SELFTEST_ORDERS, _synthetic_run


def manifest(name: str, kind: str, pin: str) -> Manifest:
    return Manifest.model_validate({
        "name": name,
        "kind": kind,
        "ref": "",
        "pin": pin,
        "binary": "",
        "binary_sha256": "",
        "binary_bytes": 0,
        "version_output": "",
    })


def rendered(run: Run) -> str:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "run.json").write_text(run.model_dump_json())
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            analyze(root, plots=False, resamples=200)
        return (root / "report.md").read_text()


def row(report: str, name: str) -> str:
    return next(line for line in report.splitlines() if line.startswith(f"| {name} |"))


class ReportTests(unittest.TestCase):
    def test_upstream_candidates_carry_the_revision_they_measured(self):
        head = manifest(
            "upstream-head", "git", "b8dd508a8b60723356cf5a091e8a9325764465c1"
        )
        self.assertEqual(label(head), "upstream-head-b8dd508")
        self.assertEqual(
            label(manifest("upstream-release", "release", "0.11.0")),
            "upstream-release-v0.11.0",
        )
        self.assertEqual(
            label(manifest("upstream-release", "release", "v0.11.0")),
            "upstream-release-v0.11.0",
        )
        self.assertEqual(
            label(manifest("rshellcheck", "git", "9f28baae")), "rshellcheck"
        )

    def test_candidates_follow_the_configured_order(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.candidates = [
            manifest(name, "git", "0")
            for name in (
                "upstream-release",
                "h2r",
                "unlisted",
                "upstream-head",
                "rshellcheck",
            )
        ]
        self.assertEqual(
            [c.name for c in ordered(run)],
            ["rshellcheck", "upstream-head", "upstream-release", "h2r", "unlisted"],
        )

    def test_a_baseline_timed_once_gives_a_point_ratio_and_says_why(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        base = run.precheck["medium"]["upstream"]
        base.status = "slow"
        base.wall_s = 3.0
        base.reason = "one run took 3.0s, over the 15s per-run budget; timed once only"
        run.samples["medium"]["upstream"] = Samples()
        report = rendered(run)
        line = row(report, "rshellcheck")
        self.assertNotIn("not comparable", line)
        self.assertIn("≈", line)
        self.assertIn("(no CI)", line)
        self.assertIn(
            "upstream timed once (3.0s, over the 15s per-run budget); ratio without interval",
            line,
        )
        self.assertIn("(once)", row(report, "upstream"))

    def test_sanctioned_output_is_compared_like_matching_output(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        check = run.precheck["medium"]["rshellcheck"]
        check.parity = "sanctioned"
        check.deviations = ["stable-trap-variables", "signal-only-cleanup-trap"]
        line = row(rendered(run), "rshellcheck")
        self.assertIn(
            "matches up to sanctioned deviations (stable-trap-variables, signal-only-cleanup-trap; "
            "[diff](precheck/medium/rshellcheck.diff))",
            line,
        )
        self.assertNotIn("not comparable", line)
        self.assertRegex(line, r"\| \d\.\d\d× \[\d\.\d\d, \d\.\d\d\] \|")


if __name__ == "__main__":
    unittest.main()
