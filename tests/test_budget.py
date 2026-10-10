import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

from bench.analyze import analyze
from bench.measure import Args, CandidateBudget, main, parser, precheck
from bench.schema import Samples, Scenario, Summary
from tests.test_memory import SELFTEST_ORDERS, _synthetic_run


class BudgetTests(unittest.TestCase):
    def test_h2r_defaults_to_ten_minutes_and_rejects_invalid_limits(self):
        self.assertEqual(
            parser().parse_args([], namespace=Args()).h2r_budget_seconds, 600
        )
        for value in ("0", "-1", "nan", "inf"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                main(["--h2r-budget-seconds", value])

    def exercise_budget(self, full_completes: bool):
        fixture, _ = _synthetic_run(True, SELFTEST_ORDERS)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "h2r"
            calls = root / "calls"
            child_pid = root / "child"
            binary.write_text(f"""#!{sys.executable}
import pathlib
import subprocess
import sys
import time
with pathlib.Path({str(calls)!r}).open('a') as output:
    output.write(sys.argv[1] + '\\n')
if sys.argv[1] == 'full':
    time.sleep(0.06)
else:
    child = subprocess.Popen(['sleep', '10'])
    pathlib.Path({str(child_pid)!r}).write_text(str(child.pid))
    child.wait()
""")
            binary.chmod(0o755)
            candidates = [
                c.model_copy(
                    update={
                        "binary": str(binary) if c.name == "h2r" else "/usr/bin/true"
                    }
                )
                for c in fixture.candidates
            ]
            scenarios = {
                "slow": Scenario(
                    description="slow fixture", args=["slow"], format="gcc"
                ),
                "unused": Scenario(
                    description="unexecuted fixture", args=["unused"], format="gcc"
                ),
                "omarchy-all": Scenario(
                    description="full sweep fixture",
                    args=["full" if full_completes else "slow"],
                    format="gcc",
                ),
            }
            budget = CandidateBudget(1)
            with contextlib.redirect_stderr(io.StringIO()):
                checks = precheck(
                    candidates,
                    fixture.baseline,
                    scenarios,
                    root,
                    root,
                    5,
                    2**30,
                    None,
                    0.01,
                    {"h2r": budget},
                )
            self.assertLessEqual(budget.spent_s, budget.seconds)
            self.assertEqual(budget.remaining, 0)
            self.assertEqual(
                calls.read_text().splitlines(),
                ["full", "slow"] if full_completes else ["slow"],
            )
            self.assertEqual(checks["unused"]["h2r"].status, "skipped")
            self.assertFalse((root / "precheck/unused/h2r.stdout").exists())
            self.assertEqual(
                checks["omarchy-all"]["h2r"].status,
                "slow" if full_completes else "limited",
            )
            self.assertEqual(
                checks["omarchy-all"]["h2r"].parity,
                "identical" if full_completes else "unknown",
            )
            for scenario in scenarios:
                self.assertIn(checks[scenario]["upstream"].status, ("ok", "slow"))
                self.assertIn(checks[scenario]["rust-port"].status, ("ok", "slow"))
            proc = Path("/proc") / child_pid.read_text() / "stat"
            self.assertTrue(not proc.exists() or proc.read_text().split()[2] == "Z")
            fixture.scenarios = scenarios
            fixture.precheck = checks
            fixture.config.candidate_budget_s = {"h2r": 1}
            fixture.candidate_elapsed_s = {"h2r": budget.spent_s}
            fixture.samples = {
                s: {c.name: Samples() for c in candidates} for s in scenarios
            }
            (root / "run.json").write_text(fixture.model_dump_json())
            with (
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                analyze(root, plots=False, resamples=200)
            summary = Summary.model_validate_json((root / "summary.json").read_text())
            self.assertIsNone(summary.descriptives["unused"]["h2r"])
            self.assertFalse(summary.comparisons)
            report = (root / "report.md").read_text()
            self.assertIn("h2r total measurement budget: 1.000 s", report)
            self.assertIn("| h2r | unknown | - | - | - | - |", report)
            self.assertIn("(stopped)", report)
            self.assertNotIn(
                "🏆",
                "\n".join(
                    line for line in report.splitlines() if line.startswith("| h2r |")
                ),
            )

    def test_full_sweep_runs_first_once_and_shared_budget_stops_later_work(self):
        self.exercise_budget(full_completes=True)

    def test_full_sweep_timeout_has_unknown_parity_and_incomplete_coverage(self):
        self.exercise_budget(full_completes=False)


if __name__ == "__main__":
    unittest.main()
