"""Regression coverage for isolated and historical cumulative RSS measurements."""

import math
import unittest
from pathlib import Path

import numpy as np

from bench.analyze import Summary, analyze, legacy_round_medians, peak_rss
from bench.schema import (
    Config,
    CorpusRef,
    Environment,
    HyperfineExport,
    HyperfineResult,
    Manifest,
    Precheck,
    Round,
    Run,
    Samples,
    Scenario,
)

MIB = 2**20
# What each candidate really peaks at when it runs alone, MiB (the shape of the CI run
# that exposed the cumulative-maximum problem: upstream small, h2r and rust-port large).
TRUE_RSS = {"upstream": 220, "h2r": 767, "rust-port": 1374}
SELFTEST_ORDERS = [
    ["upstream", "h2r", "rust-port"],
    ["h2r", "upstream", "rust-port"],
    ["rust-port", "h2r", "upstream"],
    ["h2r", "rust-port", "upstream"],
]
# Orders in which upstream, the smallest, is never first: every cumulative value it
# reports is inflated by a larger candidate that ran before it.
NEVER_FIRST_ORDERS = [
    ["h2r", "upstream", "rust-port"],
    ["rust-port", "upstream", "h2r"],
    ["h2r", "rust-port", "upstream"],
    ["rust-port", "h2r", "upstream"],
]


def _synthetic_run(
    isolated: bool, orders: list[list[str]], with_round_memory: bool = True
) -> tuple[Run, dict[str, HyperfineExport]]:
    """A run.json-shaped dict with one scenario, plus the old-layout raw exports.

    isolated=True: every candidate's memory is its own (current run.py, one hyperfine
    process per candidate). isolated=False: the old runner, where memory is the running
    maximum over the commands of the round, in run order."""
    rng = np.random.default_rng(7)
    runs = 6
    names = list(TRUE_RSS)
    samples = {n: Samples() for n in names}
    raw: dict[str, HyperfineExport] = {}
    for rnd, order in enumerate(orders, 1):
        seen = 0
        results: list[HyperfineResult] = []
        for pos, n in enumerate(order):
            own = TRUE_RSS[n] * MIB
            seen = max(seen, own)
            # a few KiB of jitter between runs; hyperfine's own value never decreases
            mem = [int((own if isolated else seen) + 4096 * k) for k in range(runs)]
            times = [0.1 * (1 + pos * 0.3) + rng.normal(0, 0.002) for _ in range(runs)]
            e = samples[n]
            e.times += times
            e.memory_bytes += mem
            e.exit_codes += [1] * runs
            e.rounds.append(
                Round(
                    round=rnd,
                    position=pos,
                    times=times,
                    memory_bytes=mem if with_round_memory else [],
                    user_mean=0.1,
                    system_mean=0.0,
                )
            )
            results.append(
                HyperfineResult(
                    command=n,
                    mean=float(np.mean(times)),
                    user=0.1,
                    system=0.0,
                    times=times,
                    memory_usage_byte=mem,
                )
            )
        raw[f"round{rnd:02d}-medium.json"] = HyperfineExport(results=results)
    precheck = {
        # the pre-check ran every candidate alone: exact per-candidate peaks
        n: Precheck(
            exit=1,
            signal=None,
            wall_s=0.1,
            peak_rss_bytes=TRUE_RSS[n] * MIB,
            killed=None,
            stdout_bytes=0,
            stdout_sha256="",
            stderr_head="",
            status="ok",
            reason=None,
            parity="baseline" if n == "upstream" else "identical",
        )
        for n in names
    }
    run = Run(
        version=2 if isolated else 1,
        created="2026-01-01T00:00:00+00:00",
        config=Config(
            rounds=len(orders),
            runs=runs,
            warmup=1,
            seed=1,
            pin=None,
            max_rss_gib=8.0,
            timeout_s=60,
            max_run_s=15,
            hyperfine_flags=[],
            memory_isolated=isolated,
        ),
        environment=Environment(
            hostname="selftest",
            kernel="",
            os="",
            arch="",
            python="",
            cpu_count=None,
            ci=False,
            github={},
            hyperfine=None,
        ),
        baseline="upstream",
        candidates=[
            Manifest(
                name=n,
                kind="release",
                ref="",
                pin="0",
                binary="",
                binary_sha256="",
                binary_bytes=0,
                version_output="",
            )
            for n in names
        ],
        corpus=CorpusRef(dir="x", sha256="0" * 64, seed=1, files={}),
        scenarios={
            "medium": Scenario(description="synthetic", args=["a.sh"], format="tty")
        },
        precheck={"medium": precheck},
        samples={"medium": samples},
        elapsed_s=0.0,
    )
    return run, raw


def selftest() -> int:
    """Feed synthetic runs with cumulative per-round memory values through the analysis
    and check that the reported peak RSS of every candidate is its true isolated value."""
    import contextlib
    import io
    import shutil
    import tempfile

    failures: list[str] = []

    def check(label: str, got: dict[str, float]) -> None:
        for n, v in TRUE_RSS.items():
            ok = (
                abs(got[n] - v * MIB) < MIB
            )  # per-run jitter is KiB; a MiB off is another candidate's peak
            print(
                f"  {'ok  ' if ok else 'FAIL'} {label:52s} {n:10s} {got[n] / MIB:8.1f} MiB (true {v})"
            )
            if not ok:
                failures.append(
                    f"{label}: {n} reported {got[n] / MIB:.1f} MiB, true value {v} MiB"
                )

    def rss_of(run: Run, results: Path | None = None) -> dict[str, float]:
        s = run.samples["medium"]
        p = run.precheck["medium"]
        return {
            n: peak_rss(s[n], p[n], run.config, results, "medium", n)[0]
            for n in TRUE_RSS
        }

    def write_raw(d: Path, raw: dict[str, HyperfineExport]) -> None:
        for fn, data in raw.items():
            _ = (d / "raw" / fn).write_text(data.model_dump_json())

    print(
        "peak RSS on synthetic runs (true isolated peaks: "
        + ", ".join(f"{n} {v} MiB" for n, v in TRUE_RSS.items())
        + ")"
    )

    # 1. Current runner: one hyperfine process per candidate.
    run, _ = _synthetic_run(True, SELFTEST_ORDERS)
    check("isolated hyperfine processes", rss_of(run))

    # 2. Old runner, cumulative values, per-round memory in run.json. The per-round
    # medians alone would give upstream 767 MiB; the pre-check supplies the true value.
    run, _ = _synthetic_run(False, NEVER_FIRST_ORDERS)
    cumulative = min(
        float(np.median(r.memory_bytes))
        for r in run.samples["medium"]["upstream"].rounds
    )
    assert cumulative > 700 * MIB, "synthetic cumulative data should overstate upstream"
    check("legacy cumulative: per-round memory + pre-check", rss_of(run))

    # 3. Old runner, no per-round memory in run.json, only the old raw/ exports on disk.
    run, raw = _synthetic_run(False, NEVER_FIRST_ORDERS, with_round_memory=False)
    with tempfile.TemporaryDirectory() as d:
        (Path(d) / "raw").mkdir()
        write_raw(Path(d), raw)
        check("legacy cumulative: raw/ exports + pre-check", rss_of(run, Path(d)))
        # Raw exports alone are exact for a candidate that ran first, or behind smaller ones, in some round.
        # Upstream never did in NEVER_FIRST_ORDERS, so it gets the mixed orders.
        _, raw2 = _synthetic_run(False, SELFTEST_ORDERS, with_round_memory=False)
        write_raw(Path(d), raw2)
        check(
            "legacy raw/ exports alone, min over rounds",
            {n: min(legacy_round_medians(Path(d), "medium", n)) for n in TRUE_RSS},
        )

    # 4. Old runner, flat run.json memory only and no raw/: pre-check value.
    run, _ = _synthetic_run(False, NEVER_FIRST_ORDERS, with_round_memory=False)
    check("legacy cumulative: no per-round data", rss_of(run))

    # 5. Whole pipeline (analyze -> summary.json and report.md) on both kinds of run.json.
    for label, run in (
        ("end-to-end, isolated run", _synthetic_run(True, SELFTEST_ORDERS)[0]),
        ("end-to-end, legacy run", _synthetic_run(False, NEVER_FIRST_ORDERS)[0]),
    ):
        with tempfile.TemporaryDirectory() as d:
            _ = (Path(d) / "run.json").write_text(run.model_dump_json())
            with (
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                # the statistics are not under test here
                analyze(Path(d), plots=False, resamples=200)
            summary = Summary.model_validate_json(
                (Path(d) / "summary.json").read_text()
            )
            report = (Path(d) / "report.md").read_text()
            with tempfile.TemporaryDirectory() as again:
                copy = Path(again) / Path(d).name
                copy.mkdir()
                _ = shutil.copy(Path(d) / "run.json", copy)
                with (
                    contextlib.redirect_stdout(io.StringIO()),
                    contextlib.redirect_stderr(io.StringIO()),
                ):
                    analyze(copy, plots=False, resamples=200)
                if (copy / "report.md").read_text() != report:
                    failures.append(f"{label}: rerun on a copy of run.json differs")
                    print(f"  FAIL {label:52s} rerun on a copy of run.json differs")
        cells = summary.descriptives["medium"]
        check(
            label,
            {
                n: (cell.peak_rss_median if (cell := cells[n]) else math.nan)
                for n in TRUE_RSS
            },
        )
        for n, v in TRUE_RSS.items():
            row = next(l for l in report.splitlines() if l.startswith(f"| {n} | "))
            if f"| {v} MiB |" not in row:
                failures.append(f"{label}: report row for {n} lacks '{v} MiB': {row}")
                print(f"  FAIL {label:52s} {n:10s} report row lacks {v} MiB")

    if failures:
        print(f"\nselftest FAILED ({len(failures)}):\n  " + "\n  ".join(failures))
        return 1
    print("\nselftest passed")
    return 0


class MemoryTests(unittest.TestCase):
    def test_isolated_legacy_and_reproducible_reports(self):
        self.assertEqual(selftest(), 0)
