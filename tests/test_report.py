import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from bench.analyze import analyze
from bench.report import label, quality
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


def where_to_look(report: str) -> str:
    return report.split("## Where to look first", 1)[1].split("## The results", 1)[0]


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
        self.assertRegex(line, r"\| ≈\d\.\d\d× \|")
        self.assertTrue(line.endswith("| baseline timed once |"), line)
        self.assertIn("| 3.000 s |", row(report, "upstream"))
        self.assertTrue(row(report, "upstream").endswith("| timed once |"))
        self.assertIn("one run exceeded the per-run budget of 15s", report)

    def test_sanctioned_output_is_compared_like_matching_output(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        check = run.precheck["medium"]["rshellcheck"]
        check.parity = "sanctioned"
        check.deviations = ["stable-trap-variables", "signal-only-cleanup-trap"]
        report = rendered(run)
        line = row(report, "rshellcheck")
        self.assertIn("| sanctioned ([diff](precheck/medium/rshellcheck.diff)) |", line)
        self.assertIn(
            "Sanctioned deviations:\n\n- rshellcheck: `stable-trap-variables`, "
            "`signal-only-cleanup-trap`\n",
            report,
        )
        self.assertNotIn("not comparable", line)
        self.assertRegex(line, r"\| \d\.\d\d× \[\d\.\d\d, \d\.\d\d\] \|")

    def test_equal_findings_in_different_bytes_are_compared_like_matching_output(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.precheck["medium"]["rshellcheck"].parity = "sanctioned"
        line = row(rendered(run), "rshellcheck")
        self.assertIn(
            "| same findings ([diff](precheck/medium/rshellcheck.diff)) |", line
        )
        self.assertNotIn("not comparable", line)

    def test_differing_output_against_a_baseline_timed_once_shows_its_ratio(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        base = run.precheck["medium"]["upstream"]
        base.status = "slow"
        base.wall_s = 3.0
        base.reason = "one run took 3.0s, over the 15s per-run budget; timed once only"
        run.samples["medium"]["upstream"] = Samples()
        run.precheck["medium"]["rshellcheck"].parity = "differs"
        line = row(rendered(run), "rshellcheck")
        self.assertIn("| differs ([diff](precheck/medium/rshellcheck.diff)) |", line)
        self.assertIn("| ≈0.05× |", line)
        self.assertIn("| not comparable |", line)
        self.assertNotIn("🏆", line)

    def test_the_fastest_matching_candidate_earns_the_trophy(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        report = rendered(run)
        self.assertIn("🏆", row(report, "h2r"))

    def test_no_trophy_when_the_fastest_candidate_differs_in_output(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.precheck["medium"]["h2r"].parity = "differs"
        report = rendered(run)
        for name in ("upstream", "h2r", "rshellcheck"):
            self.assertNotIn("🏆", row(report, name))

    def test_no_trophy_when_the_fastest_candidate_was_timed_once(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        check = run.precheck["medium"]["h2r"]
        check.status = "slow"
        check.wall_s = 0.05
        check.reason = "one run took 0.1s, over the 15s per-run budget; timed once only"
        run.samples["medium"]["h2r"] = Samples()
        report = rendered(run)
        self.assertIn("| 50.00 ms |", row(report, "h2r"))
        self.assertTrue(row(report, "h2r").endswith("| timed once |"))
        for name in ("upstream", "h2r", "rshellcheck"):
            self.assertNotIn("🏆", row(report, name))

    def test_a_baseline_timed_once_still_gives_memory_ratios(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        base = run.precheck["medium"]["upstream"]
        base.status = "slow"
        base.wall_s = 3.0
        base.reason = "one run took 3.0s, over the 15s per-run budget; timed once only"
        run.samples["medium"]["upstream"] = Samples()
        report = rendered(run)
        self.assertIn("| 1374 MiB | ≈6.25× |", row(report, "rshellcheck"))
        self.assertIn("| 767 MiB | ≈3.49× |", row(report, "h2r"))
        self.assertIn("| 1.00× | 220 MiB | ≈1.00× |", row(report, "upstream"))

    def test_another_build_of_the_baseline_project_stays_out_of_where_to_look(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        repos = {
            "upstream": "https://github.com/koalaman/shellcheck.git",
            "h2r": "https://github.com/koalaman/shellcheck",
            "rshellcheck": "https://github.com/kjanat/shellcheck-rs.git",
        }
        for candidate in run.candidates:
            candidate.repo = repos[candidate.name]
        for name in ("h2r", "rshellcheck"):
            run.precheck["medium"][name].parity = "differs"
        report = rendered(run)
        actions = where_to_look(report)
        self.assertIn(
            "- **rshellcheck**\n"
            "  - Output differs from the baseline\n"
            "    - **synthetic** ([diff](precheck/medium/rshellcheck.diff))\n",
            actions,
        )
        self.assertNotIn("h2r", actions)
        self.assertIn("[diff](precheck/medium/h2r.diff)", row(report, "h2r"))

    def test_another_build_of_the_baseline_project_leaves_memory_to_the_table(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        for candidate in run.candidates:
            candidate.repo = "https://github.com/koalaman/shellcheck"
        candidate = next(c for c in run.candidates if c.name == "rshellcheck")
        candidate.repo = "https://github.com/kjanat/shellcheck-rs"
        report = rendered(run)
        actions = where_to_look(report)
        self.assertIn(
            "- **rshellcheck**\n"
            "  - Highest memory ratio\n"
            "    - **synthetic**: **1374 MiB**, **6.25×**\n",
            actions,
        )
        self.assertNotIn("h2r", actions)
        self.assertIn("| 767 MiB | 3.49× |", row(report, "h2r"))

    def test_a_failed_build_of_the_baseline_project_stays_in_where_to_look(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        for candidate in run.candidates:
            candidate.repo = "https://github.com/koalaman/shellcheck"
        check = run.precheck["medium"]["h2r"]
        check.status = "failed"
        check.reason = "exit 3 without output"
        run.samples["medium"]["h2r"] = Samples()
        report = rendered(run)
        self.assertIn(
            "- **h2r**\n  - Failed\n    - **synthetic**: exit 3 without output\n",
            where_to_look(report),
        )
        self.assertTrue(row(report, "h2r").endswith("| exit 3 without output |"))

    def test_a_candidate_timed_once_gives_a_memory_ratio(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        check = run.precheck["medium"]["h2r"]
        check.status = "slow"
        check.wall_s = 3.0
        check.reason = "one run took 3.0s, over the 15s per-run budget; timed once only"
        run.samples["medium"]["h2r"] = Samples()
        self.assertIn("| 767 MiB | ≈3.49× |", row(rendered(run), "h2r"))

    def test_output_differences_of_a_candidate_share_one_entry(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.scenarios["labelled"] = run.scenarios["medium"].model_copy(
            update={"label": "Labelled"}
        )
        run.precheck["labelled"] = {
            name: check.model_copy() for name, check in run.precheck["medium"].items()
        }
        run.samples["labelled"] = run.samples["medium"]
        for scenario in ("medium", "labelled"):
            run.precheck[scenario]["rshellcheck"].parity = "differs"
        actions = where_to_look(rendered(run))
        self.assertIn(
            "- **rshellcheck**\n"
            "  - Output differs from the baseline\n"
            "    - **synthetic** ([diff](precheck/medium/rshellcheck.diff))\n"
            "    - **Labelled** (tty, [diff](precheck/labelled/rshellcheck.diff))\n",
            actions,
        )
        self.assertEqual(actions.count("Output differs"), 1)

    def test_budget_limits_read_as_budget_spent(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        check = run.precheck["medium"]["h2r"]
        check.status = "limited"
        check.parity = "unknown"
        check.wall_s = 4.0
        check.reason = "total candidate measurement budget of 600s exhausted; sweep did not complete"
        run.samples["medium"]["h2r"] = Samples()
        report = rendered(run)
        self.assertIn(
            "- **h2r**\n"
            "  - Budget ran out before the output check finished\n"
            "    - **synthetic**\n",
            where_to_look(report),
        )
        line = row(report, "h2r")
        self.assertIn("| unknown | 4.000 s (stopped) |", line)
        self.assertTrue(line.endswith("| budget spent |"), line)

        check.status = "skipped"
        self.assertTrue(row(rendered(run), "h2r").endswith("| - | budget spent |"))

    def test_a_budget_stop_before_sampling_reads_as_budget_spent(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.samples["medium"]["h2r"] = Samples(
            stop_reason="total candidate measurement budget of 600s exhausted; "
            "showing initial sweep only"
        )
        line = row(rendered(run), "h2r")
        self.assertRegex(line, r"\| ≈\d\.\d\d× \|")
        self.assertTrue(line.endswith("| budget spent |"), line)

    def test_quality_names_each_flag_kind_once(self):
        self.assertEqual(
            quality([
                "only 3 samples",
                "drift between rounds (p=0.01)",
                "noisy: CV 12%",
                "noisy: CV 15%",
                "outliers: 2",
            ]),
            ["noisy", "drift", "few samples"],
        )

    def test_notes_show_short_commits_in_a_callout(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.notes = [
            (
                f"upstream-head: default branch HEAD {'a' * 40} differs from the "
                f"v0.11.0 release commit {'b' * 40}"
            )
        ]
        self.assertIn(
            "> [!NOTE]\n> upstream-head: default branch HEAD `aaaaaaaaaaaa` "
            "differs from the v0.11.0 release commit `bbbbbbbbbbbb`\n",
            rendered(run),
        )

    def test_candidates_table_and_warm_up_count(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        report = rendered(run)
        self.assertIn("| candidate | revision | binary | SHA-256 |", report)
        self.assertIn("| rshellcheck | 0 | 0.0 MiB | [](run.json) |", report)
        self.assertIn(
            "  - 4 shuffled rounds of 6 timed runs\n  - 1 warm-up per round\n", report
        )
        run.config.rounds = 1
        run.config.runs = 1
        run.config.warmup = 2
        self.assertIn(
            "  - 1 shuffled round of 1 timed run\n  - 2 warm-ups per round\n",
            rendered(run),
        )


if __name__ == "__main__":
    unittest.main()
