"""Turn a run.json from bench/run.py into statistics, a Markdown report and plots.

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
command before it. bench/run.py therefore runs one hyperfine process per
candidate and the numbers are then per candidate (`config.memory_isolated`).
Results written by the older runner (several commands per process) are repaired
here: per candidate, the minimum of the per-round medians and the isolated
pre-check peak (see `peak_rss`).

    analyze [results-dir]         (default: newest under .bench/results)
    analyze --selftest            (unit test for the peak-RSS logic, no benchmark run)
Writes report.md, summary.json and plots/<scenario>.png next to run.json.
"""

import argparse
import math
import os
import re
import sys
import warnings
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import TYPE_CHECKING, Literal, Protocol

import numpy as np
import numpy.typing as npt
from pydantic import BaseModel
from scipy import stats

from bench.schema import (
    Config,
    CorpusRef,
    Environment,
    HyperfineExport,
    HyperfineResult,
    Kind,
    Manifest,
    Precheck,
    Round,
    Run,
    Samples,
    Scenario,
)

if TYPE_CHECKING:
    from matplotlib.axes import Axes
    from matplotlib.cm import ScalarMappable
    from matplotlib.colors import Normalize
    from matplotlib.figure import Figure

warnings.filterwarnings("ignore", category=RuntimeWarning)
warnings.filterwarnings("ignore", category=stats.DegenerateDataWarning)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BENCH = Path(os.environ.get("BENCH_ROOT", ROOT / ".bench"))

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
type Verdict = Literal["faster", "slower", "no significant difference", "n/a"]


class Descriptives(BaseModel):
    n: int
    mean: float
    sd: float
    cv: float
    sem: float
    median: float
    mad: float
    min: float
    max: float
    p5: float
    p95: float
    ci_mean: tuple[float, float]
    ci_median: tuple[float, float]
    outliers: int
    outlier_frac: float
    peak_rss_median: float
    peak_rss_source: str
    exit_codes: list[int | None]
    drift_p: float | None
    drift_spread: float


class Comparison(BaseModel):
    speedup_mean: float
    speedup_mean_ci: tuple[float, float]
    speedup_median: float
    speedup_median_ci: tuple[float, float]
    diff_mean: float
    welch_p: float
    mwu_p: float
    cliffs_delta: float
    hedges_g: float
    scenario: str
    candidate: str
    reference: str
    mwu_p_adj: float
    welch_p_adj: float
    verdict: Verdict
    verdict_detail: str


class CandidateSummary(BaseModel):
    kind: Kind
    ref: str
    pin: str
    key: str
    binary_sha256: str
    binary_bytes: int
    toolchain: list[str]
    version_output: str


class Summary(BaseModel):
    results_dir: str
    created: str
    baseline: str
    alpha: float
    resamples: int
    candidates: dict[str, CandidateSummary]
    descriptives: dict[str, dict[str, Descriptives | None]]
    flags: dict[str, dict[str, list[str]]]
    comparisons: list[Comparison]
    environment: Environment
    config: Config
    corpus: CorpusRef


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
    # scipy returns a NaN BCa interval (DegenerateDataWarning) instead of raising.
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
    (run.json config.memory_isolated, written by the current bench/run.py).

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


def fmt_time(seconds: float) -> str:
    if seconds >= 1:
        return f"{seconds:.3f} s"
    return f"{seconds * 1000:.2f} ms"


def fmt_ci(lo: float, hi: float, unit_fn: Callable[[float], str] = fmt_time) -> str:
    return f"[{unit_fn(lo)}, {unit_fn(hi)}]"


def fmt_p(p: float) -> str:
    if p < 1e-4:
        return "<0.0001"
    return f"{p:.4f}"


def fmt_x(v: float) -> str:
    return f"{v:.2f}×"


def verdict(
    p: Pair, mwu_p_adj: float, flags_a: list[str], flags_b: list[str]
) -> tuple[Verdict, str]:
    lo, hi = p.speedup_mean_ci
    blocked = [
        f
        for f in flags_a + flags_b
        if f.startswith(("not comparable", "excluded", "timed once"))
    ]
    if blocked:
        return "n/a", blocked[0]
    if mwu_p_adj < ALPHA and (lo > 1 or hi < 1):
        if p.speedup_mean > 1:
            return "faster", f"{(1 - 1 / p.speedup_mean) * 100:.0f}% less time"
        return "slower", f"{(1 / p.speedup_mean - 1) * 100:.0f}% more time"
    return (
        "no significant difference",
        f"speed-up interval {lo:.2f}×–{hi:.2f}× includes 1",
    )


class Args(argparse.Namespace):
    results: Path | None = None
    no_plots: bool = False
    selftest: bool = False


def main() -> None:
    ap = argparse.ArgumentParser(
        description=(__doc__ or "").split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    _ = ap.add_argument("results", nargs="?", type=Path)
    _ = ap.add_argument("--no-plots", action="store_true")
    _ = ap.add_argument(
        "--selftest",
        action="store_true",
        help="check the peak-RSS logic on synthetic runs and exit",
    )
    args = ap.parse_args(namespace=Args())
    if args.selftest:
        sys.exit(selftest())

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
    analyze(results, plots=not args.no_plots, resamples=RESAMPLES)


def analyze(results: Path, plots: bool, resamples: int) -> None:
    run = Run.model_validate_json((results / "run.json").read_text())
    rng = np.random.default_rng(run.config.seed)

    baseline = run.baseline
    names = [c.name for c in run.candidates]
    others = [n for n in names if n != baseline]
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
            if p.status == "slow":
                fl.append(f"timed once: {p.reason}")
            elif p.status != "ok":
                fl.append(f"excluded: {p.reason}")
            elif p.parity == "differs":
                fl.append(
                    f"not comparable: output differs from {baseline} ({p.diff_lines if p.diff_lines is not None else '?'} lines)"
                )
            d: Descriptives | None = None
            if e.n:
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

    plot_paths = make_plots(results, run, names) if plots else {}

    report = render(
        run, results, names, others, desc, flags, pairs, plot_paths, resamples
    )
    _ = (results / "report.md").write_text(report)
    summary = Summary(
        results_dir=str(results),
        created=datetime.now(UTC).isoformat(timespec="seconds"),
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
    print(report)
    print(
        f"\n(written to {results / 'report.md'} and {results / 'summary.json'})",
        file=sys.stderr,
    )


class PlotAxes(Protocol):
    def boxplot(
        self,
        x: FloatArray,
        *,
        positions: Sequence[float],
        orientation: Literal["vertical", "horizontal"],
        widths: float,
        showfliers: bool,
        medianprops: dict[str, str],
    ) -> object: ...

    def scatter(
        self,
        x: FloatArray,
        y: FloatArray,
        *,
        c: npt.NDArray[np.int64],
        cmap: str,
        norm: Normalize,
        s: float,
        alpha: float,
        zorder: float,
    ) -> object: ...

    def set_yticks(self, ticks: Sequence[int]) -> object: ...

    def set_yticklabels(self, labels: Sequence[str]) -> object: ...

    def set_xlabel(self, xlabel: str) -> object: ...

    def set_title(self, label: str, *, fontsize: float) -> object: ...

    def grid(self, *, axis: Literal["both", "x", "y"], alpha: float) -> None: ...


class PlotFigure(Protocol):
    def colorbar(
        self,
        mappable: ScalarMappable,
        *,
        ax: Axes,
        label: str,
        fraction: float,
        ticks: Sequence[int],
    ) -> object: ...

    def tight_layout(self) -> None: ...

    def savefig(self, fname: Path, *, dpi: float) -> None: ...


def plot_axes(ax: Axes) -> PlotAxes:
    return ax


def plot_figure(fig: Figure) -> PlotFigure:
    return fig


def make_plots(results: Path, run: Run, names: list[str]) -> dict[str, str]:
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.cm import ScalarMappable
        from matplotlib.colors import Normalize
    except ImportError:
        return {}
    (results / "plots").mkdir(exist_ok=True)
    out: dict[str, str] = {}
    for s, sc in run.scenarios.items():
        data = [(n, run.samples[s][n]) for n in names if run.samples[s][n].n]
        if not data:
            continue
        nrounds = max((r.round for _, e in data for r in e.rounds), default=1)
        norm = Normalize(vmin=1, vmax=nrounds)
        mpl_fig, mpl_ax = plt.subplots(figsize=(7, 1.2 + 0.9 * len(data)))
        fig, ax = plot_figure(mpl_fig), plot_axes(mpl_ax)
        ys: list[str] = []
        for i, (n, e) in enumerate(data):
            t = np.asarray(e.times, dtype=np.float64) * 1000
            _ = ax.boxplot(
                t,
                positions=[i],
                orientation="horizontal",
                widths=0.5,
                showfliers=False,
                medianprops={"color": "black"},
            )
            rounds = np.asarray(
                [r.round for r in e.rounds for _ in r.times], dtype=np.int64
            )
            jitter = (np.random.default_rng(i).random(len(t)) - 0.5) * 0.3
            _ = ax.scatter(
                t,
                i + jitter,
                c=rounds,
                cmap="viridis",
                norm=norm,
                s=12,
                alpha=0.7,
                zorder=3,
            )
            ys.append(n)
        _ = ax.set_yticks(range(len(ys)))
        _ = ax.set_yticklabels(ys)
        _ = ax.set_xlabel("wall time (ms); points coloured by round")
        _ = ax.set_title(f"{s}: {sc.description}", fontsize=10)
        ax.grid(axis="x", alpha=0.3)
        _ = fig.colorbar(
            ScalarMappable(norm=norm, cmap="viridis"),
            ax=mpl_ax,
            label="round",
            fraction=0.05,
            ticks=range(1, nrounds + 1),
        )
        fig.tight_layout()
        fig.savefig(results / "plots" / f"{s}.png", dpi=110)
        plt.close(mpl_fig)
        out[s] = f"plots/{s}.png"
    return out


def render(
    run: Run,
    results: Path,
    names: list[str],
    others: list[str],
    desc: dict[str, dict[str, Descriptives | None]],
    flags: dict[str, dict[str, list[str]]],
    pairs: list[Comparison],
    plots: dict[str, str],
    resamples: int,
) -> str:
    baseline = run.baseline
    env = run.environment
    cfg = run.config
    L: list[str] = []
    w = L.append

    w(f"# ShellCheck benchmark — {run.created[:10]}")
    w("")
    n_samples = cfg.rounds * cfg.runs
    w(
        f"{len(names)} candidates × {len(run.scenarios)} scenarios, {cfg.rounds} shuffled rounds × {cfg.runs} runs "
        + f"= **{n_samples} timed runs per cell** (+{cfg.warmup} warm-up per round), hyperfine `-N` (no shell), "
        + f"{'pinned to CPU ' + cfg.pin if cfg.pin else 'not CPU-pinned'}. Baseline: **{baseline}**. "
        + f"Corpus `{run.corpus.sha256[:12]}` (seed {run.corpus.seed})."
    )
    w("")

    w("## Candidates")
    w("")
    w("| candidate | what | pinned to | binary | toolchain |")
    w("|---|---|---|---:|---|")
    for c in run.candidates:
        what = "koalaman GitHub release" if c.kind == "release" else f"branch `{c.ref}`"
        pin = c.pin if c.kind == "release" else f"`{c.pin[:12]}`"
        tc = "; ".join(c.toolchain[:3])
        w(
            f"| **{c.name}** | {what} | {pin} | {c.binary_bytes / 2**20:.1f} MiB | {tc} |"
        )
    w("")

    w("## Environment")
    w("")
    gh = env.github
    w(
        f"- {env.cpu_model or 'unknown CPU'}, {env.cpu_count} logical CPUs, "
        + f"{(env.mem_total_kib or 0) / 2**20:.1f} GiB RAM, {env.os}"
        + (f", governor `{env.cpu_governor}`" if env.cpu_governor else "")
    )
    w(
        f"- {env.hyperfine}; load average at start {', '.join(f'{x:.2f}' for x in env.loadavg_at_start or ())}"
        + (
            f"; GitHub Actions run {gh.get('GITHUB_RUN_ID')} on {gh.get('RUNNER_NAME')} ({gh.get('ImageOS')})"
            if gh
            else ""
        )
    )
    w("")

    # Summary table: speed-up vs baseline per scenario.
    w(f"## Summary: speed-up relative to {baseline}")
    w("")
    w(
        "Speed-up = baseline mean time ÷ candidate mean time (>1 is faster), with its 95 % bootstrap interval. "
        + "Bold = significant after Holm correction (adjusted Mann-Whitney p < 0.05 and interval excluding 1)."
    )
    w("")
    w("| scenario | " + f"{baseline} mean | " + " | ".join(others) + " |")
    w("|---|---:|" + "---:|" * len(others))
    for s in run.scenarios:
        cells: list[str] = []
        for o in others:
            p = next(
                (
                    p
                    for p in pairs
                    if p.scenario == s and p.candidate == o and p.reference == baseline
                ),
                None,
            )
            if p is None:
                st = run.precheck[s][o]
                b = desc[s][baseline]
                if st.status == "slow" and b:
                    cells.append(
                        f"≈{b.mean / st.wall_s:.3f}× (single run: {fmt_time(st.wall_s)}, over budget)"
                    )
                elif st.status == "slow":
                    cells.append(f"single run: {fmt_time(st.wall_s)} (over budget)")
                else:
                    cells.append(
                        f"excluded ({st.reason})" if st.status != "ok" else "—"
                    )
                continue
            lo, hi = p.speedup_mean_ci
            cell = f"{fmt_x(p.speedup_mean)} [{lo:.2f}, {hi:.2f}]"
            if p.verdict in ("faster", "slower"):
                cell = f"**{cell}** {p.verdict}"
            elif p.verdict == "n/a":
                cell = f"{cell} ⚠ {p.verdict_detail.split(':')[0]}"
            else:
                cell = f"{cell} ≈"
            cells.append(cell)
        b = desc[s][baseline]
        w(f"| {s} | {fmt_time(b.mean) if b else '—'} | " + " | ".join(cells) + " |")
    w("")

    for s, sc in run.scenarios.items():
        render_scenario(w, run, s, sc, names, desc, flags, pairs, plots)

    w("## How to read this")
    w("")
    w(
        "- **Design.** Every candidate runs the identical argument list on the identical files from the same directory. "
        + f"Order is re-shuffled each round so slow machine drift is shared out; the per-round data is kept and a Kruskal-Wallis test across rounds (with the round medians more than {DRIFT_SPREAD * 100:.0f} % apart) flags drift. "
        + "hyperfine `-N` launches the process directly, so no shell start-up is inside the measurement; `--output null` discards stdout the same way for everyone."
    )
    w(
        f"- **Intervals** are bias-corrected accelerated (BCa) bootstrap intervals from {resamples:,} resamples for means and medians, "
        + "and percentile-bootstrap intervals for the ratios (the two samples are resampled independently). If a speed-up interval includes 1, the data does not distinguish the two."
    )
    w(
        "- **Tests.** Mann-Whitney U is the primary test: timing distributions are skewed and it makes no normality assumption. Welch's t-test is shown for comparison. "
        + "Both are Holm-adjusted across every comparison in this report, so with many scenarios the family-wise false-positive rate stays at 5 %."
    )
    w(
        "- **Effect size.** Cliff's δ is the probability a random run of the first is slower than a random run of the second, minus the reverse (±1 = complete separation); "
        + "Hedges' g is the standardised mean difference. A significant p with a negligible δ is a real but tiny difference."
    )
    w(
        f"- **Pre-check.** Before timing, each candidate ran each scenario once under a {cfg.max_rss_gib:.1f} GiB peak-RSS cap (physical RAM minus 1 GiB unless overridden) and a {cfg.timeout_s:g} s timeout. "
        + "A crash, hang or blown cap excludes it from that scenario. Output is compared with the baseline's (JSON compared structurally); a difference does not exclude, but it does void the comparison: a faster program computing something else is not a faster ShellCheck."
    )
    w(
        f"- **Budget.** A candidate whose pre-check run took longer than {cfg.max_run_s:g} s is not sampled in the rounds (fifty runs of a minute each is not a benchmark, it is a wait); "
        + "that single run is reported instead, marked as such, and the ratio next to it is a rough single-run figure with no interval. Raise `--max-run-seconds` for a dedicated slow run."
    )
    if cfg.memory_isolated:
        w(
            "- **Peak RSS** is the maximum resident set size of the candidate's own process: every candidate runs under its own hyperfine process in every round, "
            + "and hyperfine's `memory_usage_byte` (the `RUSAGE_CHILDREN` maximum of that process) is taken as the median over runs. "
            + "Excluded and over-budget rows show the isolated pre-check run's peak instead. "
            + "It is a peak of the whole process, not an average, and it includes the warm-up runs of that process."
        )
    else:
        w(
            "- **Peak RSS** (legacy run: all candidates of a round shared one hyperfine process). hyperfine's memory figure is the cumulative `RUSAGE_CHILDREN` maximum, "
            + "so within a round each later candidate reports at least the peak of every earlier one. "
            + "The value shown is therefore the lowest of the isolated pre-check run's peak and the per-round medians; "
            + "it is exact only when the pre-check or some round measured that candidate without a larger one before it, otherwise an upper bound."
        )
    w("")
    w(
        f"Raw samples: `{results.name}/run.json`; every number here: `summary.json`; per-round hyperfine exports: `raw/`; pre-check outputs and diffs: `precheck/`."
    )
    w("")
    return "\n".join(L)


PARITY = {
    "baseline": "baseline",
    "identical": "identical ✓",
    "unknown": "unknown",
}


def parity_cell(st: Precheck) -> str:
    if st.parity == "differs":
        lines = st.diff_lines if st.diff_lines is not None else "?"
        return f"**differs** ({lines} lines)"
    return PARITY[st.parity]


def render_scenario(
    w: Callable[[str], None],
    run: Run,
    s: str,
    sc: Scenario,
    names: list[str],
    desc: dict[str, dict[str, Descriptives | None]],
    flags: dict[str, dict[str, list[str]]],
    pairs: list[Comparison],
    plots: dict[str, str],
) -> None:
    w(f"## {s}: {sc.description}")
    w("")
    w(
        f"`shellcheck {' '.join(sc.args[:6])}{' …' if len(sc.args) > 6 else ''}`"
        + (f" ({len(sc.args) - 2} files)" if len(sc.args) > 6 else "")
    )
    w("")
    w(
        "| candidate | n | mean [95 % CI] | median [95 % CI] | sd (CV) | min | p95 | peak RSS | output vs baseline | flags |"
    )
    w("|---|---:|---|---|---|---:|---:|---:|---|---|")
    for n in names:
        d, st = desc[s][n], run.precheck[s][n]
        parity = parity_cell(st)
        if not d:
            if st.status == "slow":
                w(
                    f"| {n} | 1 | {fmt_time(st.wall_s)} (single pre-check run, not in the rounds) | | | | | {st.peak_rss_bytes / 2**20:.0f} MiB | {parity} | over the {run.config.max_run_s:g} s per-run budget |"
                )
            else:
                w(
                    f"| {n} | 0 | excluded: {st.reason} | | | | | {st.peak_rss_bytes / 2**20:.0f} MiB | {parity} | |"
                )
            continue
        w(
            f"| {n} | {d.n} | {fmt_time(d.mean)} {fmt_ci(*d.ci_mean)} | {fmt_time(d.median)} {fmt_ci(*d.ci_median)} "
            + f"| {fmt_time(d.sd)} ({d.cv * 100:.1f} %) | {fmt_time(d.min)} | {fmt_time(d.p95)} | {d.peak_rss_median / 2**20:.0f} MiB "
            + f"| {parity} | {'; '.join(f for f in flags[s][n] if not f.startswith('not comparable')) or '—'} |"
        )
    w("")
    sp = [p for p in pairs if p.scenario == s]
    if sp:
        w(
            "| comparison | speed-up (means) [95 % CI] | speed-up (medians) [95 % CI] | Mann-Whitney p (Holm) | Welch p (Holm) | Cliff's δ | Hedges' g | verdict |"
        )
        w("|---|---|---|---|---|---|---:|---|")
        for p in sp:
            w(
                f"| {p.candidate} vs {p.reference} | {fmt_x(p.speedup_mean)} [{p.speedup_mean_ci[0]:.2f}, {p.speedup_mean_ci[1]:.2f}] "
                + f"| {fmt_x(p.speedup_median)} [{p.speedup_median_ci[0]:.2f}, {p.speedup_median_ci[1]:.2f}] "
                + f"| {fmt_p(p.mwu_p)} ({fmt_p(p.mwu_p_adj)}) | {fmt_p(p.welch_p)} ({fmt_p(p.welch_p_adj)}) "
                + f"| {p.cliffs_delta:+.2f} ({cliff_label(p.cliffs_delta)}) | {p.hedges_g:+.2f} | **{p.verdict}**: {p.verdict_detail} |"
            )
        w("")
    if s in plots:
        w(f"![{s}]({plots[s]})")
        w("")
    for n in names:
        st = run.precheck[s][n]
        if st.status != "ok" and st.stderr_head:
            w(
                f"<details><summary>{n} stderr</summary>\n\n```\n{st.stderr_head.strip()[:1500]}\n```\n</details>\n"
            )


# --- self-test ----------------------------------------------------------------

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
                key="",
                binary="",
                binary_sha256="",
                binary_bytes=0,
                version_output="",
                toolchain=[],
                built_at="",
                built_on="",
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
        # The raw exports alone are right for every candidate that ran first (or behind
        # smaller ones only) in at least one round: the minimum over rounds. Upstream
        # never did in NEVER_FIRST_ORDERS, so use the mixed orders for this one.
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


if __name__ == "__main__":
    main()
