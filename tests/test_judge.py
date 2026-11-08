import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

from bench.measure import precheck
from bench.schema import Manifest, Scenario
from tests.test_memory import SELFTEST_ORDERS, _synthetic_run


class JudgeTests(unittest.TestCase):
    """A candidate whose output differs from the baseline asks its own judge
    whether every file differs only by sanctioned deviations."""

    def exercise(self, verdicts: list[dict[str, object]], exit_code: int):
        fixture, _ = _synthetic_run(True, SELFTEST_ORDERS)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("a.sh", "b.sh"):
                (root / name).write_text("echo $x\n")
            baseline = root / "baseline"
            baseline.write_text("#!/bin/sh\necho upstream\nexit 1\n")
            port = root / "port"
            port.write_text("#!/bin/sh\necho port\nexit 1\n")
            calls = root / "calls.json"
            judge = root / "judge"
            judge.write_text(f"""#!{sys.executable}
import json, pathlib, sys
pathlib.Path({str(calls)!r}).write_text(json.dumps({{"argv": sys.argv[1:], "stdin": sys.stdin.read()}}))
print(json.dumps({{"files": {json.dumps(verdicts)}}}))
sys.exit({exit_code})
""")
            for path in (baseline, port, judge):
                path.chmod(0o755)
            binaries = {"upstream": baseline, "rshellcheck": port, "h2r": baseline}
            candidates: list[Manifest] = [
                c.model_copy(
                    update={
                        "binary": str(binaries[c.name]),
                        "judge": str(judge) if c.name == "rshellcheck" else None,
                    }
                )
                for c in fixture.candidates
            ]
            scenario = Scenario(
                description="judged",
                args=["-s", "bash", "-f", "gcc", "a.sh", "b.sh"],
                format="gcc",
            )
            with contextlib.redirect_stderr(io.StringIO()):
                checks = precheck(
                    candidates,
                    "upstream",
                    {"s": scenario},
                    root,
                    root,
                    5,
                    2**30,
                    None,
                    15,
                )
            call = json.loads(calls.read_text())
            self.assertEqual(
                call["argv"], ["judge", "--oracle", str(baseline), "--shell", "bash"]
            )
            self.assertEqual(call["stdin"], "a.sh\nb.sh\n")
            self.assertEqual(checks["s"]["h2r"].parity, "identical")
            self.assertTrue((root / "precheck/s/rshellcheck.diff").is_file())
            self.assertTrue((root / "precheck/s/rshellcheck.judge.json").is_file())
            return checks["s"]["rshellcheck"]

    def test_sanctioned_files_make_the_output_comparable(self):
        check = self.exercise(
            [
                {
                    "path": "a.sh",
                    "verdict": "sanctioned",
                    "deviations": ["stable-trap-variables"],
                },
                {
                    "path": "b.sh",
                    "verdict": "sanctioned",
                    "deviations": ["signal-only-cleanup-trap", "stable-trap-variables"],
                },
            ],
            0,
        )
        self.assertEqual(check.parity, "sanctioned")
        self.assertEqual(
            check.deviations, ["signal-only-cleanup-trap", "stable-trap-variables"]
        )

    def test_one_differing_file_keeps_the_output_different(self):
        check = self.exercise(
            [
                {
                    "path": "a.sh",
                    "verdict": "sanctioned",
                    "deviations": ["stable-trap-variables"],
                },
                {"path": "b.sh", "verdict": "differs", "deviations": []},
            ],
            1,
        )
        self.assertEqual(check.parity, "differs")
        self.assertEqual(check.deviations, [])

    def test_a_judge_that_fails_keeps_the_output_different(self):
        check = self.exercise([], 2)
        self.assertEqual(check.parity, "differs")


if __name__ == "__main__":
    unittest.main()
