"""Turn a run.json from bench/measure.py into statistics, a Markdown report and plots.

For every scenario and candidate:
  n, mean, standard deviation, coefficient of variation, median, MAD, min/max,
  5th/95th percentile, 95% bootstrap confidence intervals (BCa, 10 000
  resamples) for the mean and the median, peak RSS (per candidate, see below).

For every candidate against the baseline (and every other pair):
  speed-up = baseline mean / candidate mean, with a 95% percentile-bootstrap
  interval; the same for medians; Welch's t-test; the Mann-Whitney U test
  (two-sided); Cliff's delta with its conventional magnitude label; Hedges' g.
  p-values are Holm-adjusted across every comparison in the report (one family
  per test) so scanning many scenarios does not manufacture significance.

A comparison only earns a "faster"/"slower" verdict when the Holm-adjusted
Mann-Whitney p is below 0.05 *and* the bootstrap interval of the speed-up
excludes 1. Everything else is "no significant difference" at this sample
size, and the interval says how much could hide there.

Quality flags per candidate x scenario: CV above 10 %, more than 5 % Tukey
outliers, drift across rounds (Kruskal-Wallis p < 0.01 and the round medians
more than 5 % apart: the machine changed while measuring), fewer than 20
samples, output differing from the baseline (not comparable), or excluded by
the pre-check.

Peak RSS comes from hyperfine's `memory_usage_byte`, which is the cumulative
RUSAGE_CHILDREN maximum of the hyperfine process: with several commands in one
hyperfine invocation each later command reports at least the maximum of every
command before it. bench/measure.py therefore runs one hyperfine process per
candidate and the numbers are then per candidate (`config.memory_isolated`).
Results written by the older runner (several commands per process) are repaired
here: per candidate, the minimum of the per-round medians and the isolated
pre-check peak (see `peak_rss`).

    analyze [results-dir]         (default: newest under .bench/results)
Writes report.md, summary.json and plots/<scenario>.png next to run.json.
The bootstrap is seeded from run.json, so a rerun on the same run.json writes the same report.
"""

import argparse
import math
import re
import sys
import warnings
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

import numpy as np
import numpy.typing as npt
from scipy import stats

from bench.schema import (
    CandidateSummary,
    Comparison,
    Config,
    Descriptives,
    HyperfineExport,
    Precheck,
    Round,
    Run,
    Samples,
    Summary,
    Verdict,
)

warnings.filterwarnings("ignore", category=RuntimeWarning)
warnings.filterwarnings("ignore", category=stats.DegenerateDataWarning)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BENCH = ROOT / ".bench"

ALPHA = 0.05
RESAMPLES = 10_000
CV_LIMIT = 0.10
OUTLIER_LIMIT = 0.05
DRIFT_P = 0.01
DRIFT_SPREAD = (
    0.05  # round medians must also differ by more than this to be worth a flag
)
MIN_N = 20

type FloatArray = npt.NDArray[np.float64]
type Stat = Literal["mean", "median"]


# --- statistics ---------------------------------------------------------------


def reduce(stat: Stat, x: FloatArray, axis: int = -1) -> FloatArray:
    return np.mean(x, axis=axis) if stat == "mean" else np.median(x, axis=axis)


def ci(
    x: FloatArray, stat: Stat, rng: np.random.Generator, resamples: int
) -> tuple[float, float]:
    if len(x) < 3 or np.ptp(x) == 0:
        v = float(reduce(stat, x))
        return v, v

    def f(v: FloatArray, axis: int = -1) -> FloatArray:
        return reduce(stat, v, axis)

    def interval(method: Literal["BCa", "percentile"]) -> tuple[float, float]:
        res = stats.bootstrap(
            (x,),
            f,
            n_resamples=resamples,
            confidence_level=1 - ALPHA,
            method=method,
            rng=rng,
            vectorized=True,
        )
        lo, hi = res.confidence_interval
        return float(lo), float(hi)

    lo, hi = interval("BCa")
    # scipy returns a NaN BCa interval (DegenerateDataWarning) and does not raise.
    if math.isnan(lo) or math.isnan(hi):
        return interval("percentile")
    return lo, hi


def ratio_ci(
    a: FloatArray, b: FloatArray, stat: Stat, rng: np.random.Generator, resamples: int
) -> tuple[float, float]:
    """95% percentile-bootstrap interval of statistic(a)/statistic(b) with the two
    samples resampled independently (they are independent process runs)."""
    if np.ptp(a) == 0 and np.ptp(b) == 0:
        v = float(reduce(stat, a)) / float(reduce(stat, b))
        return v, v

    def f(a: FloatArray, b: FloatArray, axis: int = -1) -> FloatArray:
        return reduce(stat, a, axis) / reduce(stat, b, axis)

    res = stats.bootstrap(
        (a, b),
        f,
        n_resamples=resamples,
        confidence_level=1 - ALPHA,
        method="percentile",
        rng=rng,
        vectorized=True,
    )
    lo, hi = res.confidence_interval
    return float(lo), float(hi)


def describe(
    e: Samples, rss: tuple[float, str], rng: np.random.Generator, resamples: int
) -> Descriptives:
    x = np.asarray(e.times, dtype=np.float64)
    q1 = float(np.percentile(x, 25))
    q3 = float(np.percentile(x, 75))
    iqr = q3 - q1
    outliers = int(np.sum((x < q1 - 1.5 * iqr) | (x > q3 + 1.5 * iqr)))
    mean = float(np.mean(x))
    sd = float(np.std(x, ddof=1)) if len(x) > 1 else 0.0
    drift_p, drift_spread = drift(e.rounds)
    return Descriptives(
        n=len(x),
        mean=mean,
        sd=sd,
        cv=sd / mean if mean else 0.0,
        sem=sd / math.sqrt(len(x)) if len(x) else 0.0,
        median=float(np.median(x)),
        mad=float(stats.median_abs_deviation(x, scale="normal")) if len(x) > 1 else 0.0,
        min=float(np.min(x)),
        max=float(np.max(x)),
        p5=float(np.percentile(x, 5)),
        p95=float(np.percentile(x, 95)),
        ci_mean=ci(x, "mean", rng, resamples),
        ci_median=ci(x, "median", rng, resamples),
        outliers=outliers,
        outlier_frac=outliers / len(x) if len(x) else 0.0,
        peak_rss_median=rss[0],
        peak_rss_source=rss[1],
        exit_codes=sorted(set(e.exit_codes), key=lambda c: (c is None, c or 0)),
        drift_p=drift_p,
        drift_spread=drift_spread,
    )


def cliffs_delta(a: FloatArray, b: FloatArray) -> float:
    # P(a > b) - P(a < b), via the Mann-Whitney U statistic.
    u = float(stats.mannwhitneyu(a, b, alternative="two-sided").statistic)
    return 2 * u / (len(a) * len(b)) - 1


def cliff_label(d: float) -> str:
    d = abs(d)
    return (
        "negligible"
        if d < 0.147
        else "small"
        if d < 0.33
        else "medium"
        if d < 0.474
        else "large"
    )


def hedges_g(a: FloatArray, b: FloatArray) -> float:
    na, nb = len(a), len(b)
    if na < 2 or nb < 2:
        return 0.0
    pooled = math.sqrt(
        ((na - 1) * float(np.var(a, ddof=1)) + (nb - 1) * float(np.var(b, ddof=1)))
        / (na + nb - 2)
    )
    if pooled == 0:
        return 0.0
    g = (float(np.mean(a)) - float(np.mean(b))) / pooled
    j = 1 - 3 / (4 * (na + nb) - 9)
    return g * j


@dataclass(frozen=True)
class Pair:
    scenario: str
    candidate: str
    reference: str
    speedup_mean: float
    speedup_mean_ci: tuple[float, float]
    speedup_median: float
    speedup_median_ci: tuple[float, float]
    diff_mean: float
    welch_p: float
    mwu_p: float
    cliffs_delta: float
    hedges_g: float


def compare(
    scenario: str,
    candidate: str,
    reference: str,
    a_times: list[float],
    b_times: list[float],
    rng: np.random.Generator,
    resamples: int,
) -> Pair:
    """a = candidate times, b = baseline times. speedup > 1 means a is faster."""
    a = np.asarray(a_times, dtype=np.float64)
    b = np.asarray(b_times, dtype=np.float64)
    varies = bool(np.ptp(np.concatenate([a, b])))
    return Pair(
        scenario=scenario,
        candidate=candidate,
        reference=reference,
        speedup_mean=float(np.mean(b)) / float(np.mean(a)),
        speedup_mean_ci=ratio_ci(b, a, "mean", rng, resamples),
        speedup_median=float(np.median(b)) / float(np.median(a)),
        speedup_median_ci=ratio_ci(b, a, "median", rng, resamples),
        diff_mean=float(np.mean(a)) - float(np.mean(b)),
        welch_p=float(stats.ttest_ind(a, b, equal_var=False).pvalue) if varies else 1.0,
        mwu_p=float(stats.mannwhitneyu(a, b, alternative="two-sided").pvalue)
        if varies
        else 1.0,
        cliffs_delta=cliffs_delta(a, b),
        hedges_g=hedges_g(a, b),
    )


def holm(pvalues: list[float]) -> list[float]:
    m = len(pvalues)
    order = sorted(range(m), key=lambda i: pvalues[i])
    adjusted = [0.0] * m
    running = 0.0
    for rank, i in enumerate(order):
        running = max(running, (m - rank) * pvalues[i])
        adjusted[i] = min(1.0, running)
    return adjusted


def drift(rounds: list[Round]) -> tuple[float | None, float]:
    """Kruskal-Wallis p across rounds and the spread of the round medians
    (max - min, relative to the overall median)."""
    groups = [
        np.asarray(r.times, dtype=np.float64) for r in rounds if len(r.times) >= 2
    ]
    if len(groups) < 2 or np.ptp(np.concatenate(groups)) == 0:
        return None, 0.0
    medians = [float(np.median(g)) for g in groups]
    spread = (max(medians) - min(medians)) / float(np.median(np.concatenate(groups)))
    try:
        return float(stats.kruskal(*groups).pvalue), spread
    except ValueError:
        return None, spread


# --- peak RSS -----------------------------------------------------------------


def legacy_round_medians(results: Path | None, scenario: str, name: str) -> list[float]:
    """Per-round median `memory_usage_byte` of `name`, read from the old-style raw
    exports raw/roundNN-<scenario>.json (all candidates of a round in one file)."""
    raw = results / "raw" if results else None
    if raw is None or not raw.is_dir():
        return []
    pat = re.compile(rf"round\d+-{re.escape(scenario)}\.json")
    out: list[float] = []
    for f in sorted(raw.iterdir()):
        if not pat.fullmatch(f.name):
            continue
        try:
            data = HyperfineExport.model_validate_json(f.read_text())
        except OSError, ValueError:
            continue
        for res in data.results:
            if res.command == name and res.memory_usage_byte:
                out.append(float(np.median(res.memory_usage_byte)))
    return out


def peak_rss(
    entry: Samples,
    pre: Precheck,
    config: Config,
    results: Path | None = None,
    scenario: str = "",
    name: str = "",
) -> tuple[float, str]:
    """Peak RSS in bytes for one candidate x scenario, and where the number came from.

    hyperfine's memory_usage_byte is the RUSAGE_CHILDREN maximum of the hyperfine
    *process*, so it is only per candidate when each candidate had its own process
    (run.json config.memory_isolated, written by the current bench/measure.py).

    Older runs put every candidate of a round into one process; there a candidate's
    value is >= the true peak of everything that ran before it and is right only
    when it ran first. The cumulative values are upper bounds of the truth, so the
    best estimate is the smallest evidence: the minimum over rounds of the per-round
    median, and the pre-check's peak (one isolated wait4/rusage run), whichever is
    lower. Without any per-round data the pre-check value is used on its own.
    """
    pre_rss = float(pre.peak_rss_bytes)
    if config.memory_isolated:
        if entry.memory_bytes:
            return float(
                np.median(entry.memory_bytes)
            ), "per-candidate hyperfine process"
        return pre_rss, "pre-check (no hyperfine memory data)"
    per_round = [
        float(np.median(r.memory_bytes)) for r in entry.rounds if r.memory_bytes
    ]
    if not per_round:
        per_round = legacy_round_medians(results, scenario, name)
    if per_round:
        return min([
            *per_round,
            pre_rss,
        ]), "legacy cumulative hyperfine memory: min of pre-check and per-round medians"
    return pre_rss, "pre-check (legacy run, hyperfine memory is cumulative)"


# --- report -------------------------------------------------------------------


def fmt_p(p: float) -> str:
    if p < 1e-4:
        return "<0.0001"
    return f"{p:.4f}"


def verdict(
    p: Pair, mwu_p_adj: float, flags_a: list[str], flags_b: list[str]
) -> tuple[Verdict, str]:
    lo, hi = p.speedup_median_ci
    blocked = [
        f
        for f in flags_a + flags_b
        if f.startswith(("not comparable", "excluded", "timed once"))
    ]
    if blocked:
        return "n/a", blocked[0]
    if mwu_p_adj < ALPHA and (lo > 1 or hi < 1):
        if p.speedup_median > 1:
            return "faster", f"{(1 - 1 / p.speedup_median) * 100:.0f}% less time"
        return "slower", f"{(1 / p.speedup_median - 1) * 100:.0f}% more time"
    if lo <= 1 <= hi:
        return (
            "no significant difference",
            f"speed-up interval {lo:.2f}× to {hi:.2f}× includes 1",
        )
    return (
        "no significant difference",
        f"Holm-adjusted Mann-Whitney p = {mwu_p_adj:.3g} ≥ {ALPHA}",
    )


class Args(argparse.Namespace):
    results: Path | None = None
    plots: bool = False


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(
        description=(__doc__ or "").split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    _ = ap.add_argument("results", nargs="?", type=Path)
    _ = ap.add_argument("--plots", action="store_true")
    args = ap.parse_args(argv, namespace=Args())

    results = args.results
    if results is None:
        runs = (
            sorted(p for p in (BENCH / "results").glob("*/run.json"))
            if (BENCH / "results").exists()
            else []
        )
        if not runs:
            sys.exit(
                "bench: no results under .bench/results; run `mise run bench:run` first"
            )
        results = runs[-1].parent
    analyze(results, plots=args.plots, resamples=RESAMPLES)


def analyze(results: Path, plots: bool, resamples: int) -> None:
    run = Run.model_validate_json((results / "run.json").read_text())
    rng = np.random.default_rng(run.config.seed)

    baseline = run.baseline
    names = [c.name for c in run.candidates]
    samples = run.samples
    pre = run.precheck

    # Per candidate x scenario descriptives and flags.
    desc: dict[str, dict[str, Descriptives | None]] = {}
    flags: dict[str, dict[str, list[str]]] = {}
    for s in run.scenarios:
        desc[s], flags[s] = {}, {}
        for n in names:
            e = samples[s][n]
            p = pre[s][n]
            fl: list[str] = []
            if e.stop_reason:
                fl.append(f"excluded: {e.stop_reason}")
            elif p.status == "slow":
                fl.append(f"timed once: {p.reason}")
            elif p.status != "ok":
                fl.append(f"excluded: {p.reason}")
            elif p.parity == "differs":
                fl.append(
                    f"not comparable: output differs from {baseline} ({p.diff_lines if p.diff_lines is not None else '?'} lines)"
                )
            if e.n and (set(e.exit_codes) - {p.exit}):
                fl.append("not comparable: exit status changed during timing")
            if e.n and p.parity == "unknown":
                fl.append("not comparable: output agreement is unknown")
            d: Descriptives | None = None
            if e.n and not e.stop_reason:
                d = describe(
                    e, peak_rss(e, p, run.config, results, s, n), rng, resamples
                )
                if d.cv > CV_LIMIT:
                    fl.append(f"noisy: CV {d.cv * 100:.1f}%")
                if d.outlier_frac > OUTLIER_LIMIT:
                    fl.append(f"{d.outliers} outliers ({d.outlier_frac * 100:.0f}%)")
                if (
                    d.drift_p is not None
                    and d.drift_p < DRIFT_P
                    and d.drift_spread > DRIFT_SPREAD
                ):
                    fl.append(
                        f"drift between rounds: round medians spread {d.drift_spread * 100:.0f}% (Kruskal-Wallis p={fmt_p(d.drift_p)})"
                    )
                if d.n < MIN_N:
                    fl.append(f"only {d.n} samples")
            desc[s][n] = d
            flags[s][n] = fl

    # Pairwise comparisons, then Holm across the whole report.
    raw: list[Pair] = []
    for s in run.scenarios:
        for i, a in enumerate(names):
            for b in names[i + 1 :]:
                if not (desc[s][a] and desc[s][b]):
                    continue
                # Orient every pair as (candidate, baseline) when the baseline is involved.
                cand, ref = (b, a) if a == baseline else (a, b)
                raw.append(
                    compare(
                        s,
                        cand,
                        ref,
                        samples[s][cand].times,
                        samples[s][ref].times,
                        rng,
                        resamples,
                    )
                )
    mwu_adj = holm([p.mwu_p for p in raw])
    welch_adj = holm([p.welch_p for p in raw])
    pairs: list[Comparison] = []
    for p, m_adj, w_adj in zip(raw, mwu_adj, welch_adj, strict=True):
        v, detail = verdict(
            p, m_adj, flags[p.scenario][p.candidate], flags[p.scenario][p.reference]
        )
        pairs.append(
            Comparison(
                speedup_mean=p.speedup_mean,
                speedup_mean_ci=p.speedup_mean_ci,
                speedup_median=p.speedup_median,
                speedup_median_ci=p.speedup_median_ci,
                diff_mean=p.diff_mean,
                welch_p=p.welch_p,
                mwu_p=p.mwu_p,
                cliffs_delta=p.cliffs_delta,
                hedges_g=p.hedges_g,
                scenario=p.scenario,
                candidate=p.candidate,
                reference=p.reference,
                mwu_p_adj=m_adj,
                welch_p_adj=w_adj,
                verdict=v,
                verdict_detail=detail,
            )
        )

    summary = Summary(
        results_dir=".",
        created=run.created,
        baseline=baseline,
        alpha=ALPHA,
        resamples=resamples,
        candidates={
            c.name: CandidateSummary.model_validate(c, from_attributes=True)
            for c in run.candidates
        },
        descriptives=desc,
        flags=flags,
        comparisons=pairs,
        environment=run.environment,
        config=run.config,
        corpus=run.corpus,
    )
    _ = (results / "summary.json").write_text(summary.model_dump_json(indent=1) + "\n")
    from bench.report import render

    plot_paths: dict[str, str] = {}
    if plots:
        from bench.plots import make_plots

        plot_paths = make_plots(results, run, names)
    report = render(run, summary, plot_paths)
    _ = (results / "report.md").write_text(report)
    print(report)
    print(
        f"\n(written to {results / 'report.md'} and {results / 'summary.json'})",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
