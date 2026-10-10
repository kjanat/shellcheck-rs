import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

from bench.analyze import Summary, analyze
from bench.measure import run_guarded
from bench.schema import HyperfineExport
from tests.test_memory import SELFTEST_ORDERS, _synthetic_run


class MetricsTests(unittest.TestCase):
    def test_hyperfine_export_versions_preserve_units_samples_and_exit_status(self):
        legacy = HyperfineExport.model_validate({
            "results": [
                {
                    "command": "fixture",
                    "mean": 2.0,
                    "user": 0.5,
                    "system": 0.1,
                    "times": [1.0, 3.0],
                    "memory_usage_byte": [100, 200],
                    "exit_codes": [0, 1],
                }
            ]
        })

        def export(unit: str):
            return {
                "schema_version": 2,
                "results": [
                    {
                        "command": "fixture",
                        "measurements": [
                            {
                                "time_wall_clock": {"value": wall, "unit": unit},
                                "time_user": {"value": 0.5, "unit": "second"},
                                "time_system": {"value": 0.1, "unit": "second"},
                                "memory_peak_resident": {
                                    "value": memory,
                                    "unit": "byte",
                                },
                                "exit_code": code,
                            }
                            for wall, memory, code in ((1.0, 100, 0), (3.0, 200, 1))
                        ],
                    }
                ],
            }

        self.assertEqual(legacy, HyperfineExport.model_validate(export("second")))
        with self.assertRaises(ValueError):
            HyperfineExport.model_validate(export("millisecond"))

    def analyze_run(self, run):
        with tempfile.TemporaryDirectory() as directory:
            results = Path(directory)
            (results / "run.json").write_text(run.model_dump_json())
            with (
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                analyze(results, plots=False, resamples=200)
            return Summary.model_validate_json(
                (results / "summary.json").read_text()
            ), (results / "report.md").read_text()

    def test_mismatched_output_never_earns_speed_verdict(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.precheck["medium"]["rust-port"].parity = "differs"
        summary, report = self.analyze_run(run)
        comparisons = [
            pair
            for pair in summary.comparisons
            if pair.candidate == "rust-port" and pair.reference == "upstream"
        ]
        self.assertEqual(comparisons[0].verdict, "n/a")
        row = next(
            line for line in report.splitlines() if line.startswith("| rust-port |")
        )
        self.assertIn("not comparable", row)
        self.assertNotIn("🏆", row)
        self.assertIn("output diff", report)

    def test_changed_exit_status_during_timing_is_not_comparable(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.samples["medium"]["rust-port"].exit_codes.append(2)
        summary, report = self.analyze_run(run)
        comparisons = [
            pair
            for pair in summary.comparisons
            if pair.candidate == "rust-port" and pair.reference == "upstream"
        ]
        self.assertEqual(comparisons[0].verdict, "n/a")
        self.assertIn(
            "exit status changed", " ".join(summary.flags["medium"]["rust-port"])
        )
        row = next(
            line for line in report.splitlines() if line.startswith("| rust-port |")
        )
        self.assertNotIn("faster", row)
        self.assertNotIn("🏆", row)

    def test_ratio_direction_and_intervals_match_recorded_statistics(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        summary, report = self.analyze_run(run)
        base = summary.descriptives["medium"]["upstream"]
        candidate = summary.descriptives["medium"]["rust-port"]
        self.assertIsNotNone(base)
        self.assertIsNotNone(candidate)
        assert base and candidate
        row = next(
            line for line in report.splitlines() if line.startswith("| rust-port |")
        )
        self.assertIn(f"{candidate.median / base.median:.2f}×", row)
        self.assertIn(f"{candidate.peak_rss_median / base.peak_rss_median:.2f}×", row)
        pair = next(
            pair
            for pair in summary.comparisons
            if pair.candidate == "rust-port" and pair.reference == "upstream"
        )
        low, high = pair.speedup_median_ci
        self.assertIn(f"[{1 / high:.2f}, {1 / low:.2f}]", row)

    def test_fastest_observed_result_keeps_highlight_and_noise_qualification(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        samples = run.samples["medium"]["rust-port"]
        for round_ in samples.rounds:
            round_.times = [0.001 if i % 2 else 0.009 for i in range(len(round_.times))]
        samples.times = [time for round_ in samples.rounds for time in round_.times]
        summary, report = self.analyze_run(run)
        self.assertTrue(
            any(
                flag.startswith("noisy")
                for flag in summary.flags["medium"]["rust-port"]
            )
        )
        row = next(
            line for line in report.splitlines() if line.startswith("| rust-port |")
        )
        self.assertIn("🏆", row)
        self.assertIn("repeat: noise/drift", row)
        self.assertNotIn(
            "🏆",
            next(
                line for line in report.splitlines() if line.startswith("| upstream |")
            ),
        )
        self.assertIn("lowest observed median", report)

    def test_timeout_kills_candidate_and_fast_children_are_reaped_once(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = run_guarded(
                ["sh", "-c", "sleep 10"], path, 0.1, 2**30, path / "out", path / "err"
            )
            self.assertIn("timeout", result.killed or "")
            self.assertLess(result.wall_s, 2)
            for _ in range(10):
                result = run_guarded(
                    ["true"], path, 1, 2**30, path / "out", path / "err"
                )
                self.assertEqual(result.exit, 0)

    def test_precheck_rss_does_not_inherit_the_large_python_parent(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = run_guarded(["true"], path, 1, 2**30, path / "out", path / "err")
            self.assertLess(result.peak_rss_bytes, 20 * 2**20)
            self.assertEqual(result.exit, 0)

    def test_memory_guard_kills_large_candidate_without_publishing_a_success(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            result = run_guarded(
                [
                    sys.executable,
                    "-S",
                    "-c",
                    "import time; data=bytearray(80*1024*1024); time.sleep(2)",
                ],
                path,
                5,
                32 * 2**20,
                path / "out",
                path / "err",
            )
            self.assertIn("RSS exceeded", result.killed or "")
            self.assertNotEqual(result.exit, 0)
            self.assertGreater(result.peak_rss_bytes, 32 * 2**20)


if __name__ == "__main__":
    unittest.main()
