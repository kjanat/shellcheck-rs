"""Time every built candidate on every scenario and record the raw samples.

Design, in the order it happens:

1. Pre-check. Each candidate runs each scenario once, under a wall-clock
   timeout and a peak-RSS watchdog. Its stdout and exit code are compared with
   the baseline's (JSON formats are compared structurally). A candidate that
   crashes, hangs or blows the memory cap is *excluded from timing* for that
   scenario and the report says so; a candidate whose output differs is still
   timed but flagged, because a faster program that computes something else is
   not a faster ShellCheck.

2. Timing. `rounds` rounds; in each round every scenario is run through one
   hyperfine invocation (`-N`, no shell) *per candidate*, with `runs` timed
   runs after `warmup` untimed ones. The candidate order is re-shuffled every
   round from a seeded PRNG, so slow drift of the machine (thermal state,
   background load, page cache) spreads evenly over all candidates. Rounds are kept apart in
   the output so the analysis can test for that drift.

   Why one hyperfine process per candidate: hyperfine reports memory from
   getrusage(RUSAGE_CHILDREN).ru_maxrss, which is the maximum over *all*
   children the hyperfine process has reaped so far. With
   several commands in one invocation every later command would report at
   least the largest peak of the commands before it (a small candidate that
   ran after a big one inherits the big one's number). A fresh hyperfine
   process per candidate makes each `memory_usage_byte` the candidate's own.
   The timing statistics are unaffected: same runs, warm-up, order and flags.

3. Everything (samples, per-run memory, exit codes, the pre-check, the
   environment, the candidate manifests, the corpus checksum) goes into
   <out>/run.json for analyze.py.

    bench run [--rounds 5] [--runs 10] [--warmup 3] [--seed 1] [--pin CPU]
          [--scenarios a,b] [--candidates x,y] [--max-rss-gib 4] [--timeout 600]
          [--corpus .bench/corpus] [--out .bench/results/<ts>]
"""

import argparse
import difflib
import hashlib
import json
import math
import os
import platform
import random
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time
import tomllib
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path, PurePosixPath

from pydantic import JsonValue, TypeAdapter

from bench.schema import (
    Config,
    CorpusManifest,
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
    ScenariosFile,
    Status,
)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BENCH = ROOT / ".bench"
JSON: TypeAdapter[JsonValue] = TypeAdapter(JsonValue)


def log(msg: str) -> None:
    print(f"\033[1;34m==> {msg}\033[0m", file=sys.stderr, flush=True)


def warn(msg: str) -> None:
    print(f"\033[1;33mwarning: {msg}\033[0m", file=sys.stderr, flush=True)


# --- inputs -----------------------------------------------------------------


def load_candidates(
    prepared: Path, only: list[str] | None, config: Path = HERE / "candidates.toml"
) -> tuple[list[Manifest], str]:
    from bench.candidates import read_manifest, selected, specs

    table = specs(config)
    names = selected(table, ",".join(only or []))
    baseline = next(name for name, spec in table.items() if spec.baseline)
    if baseline not in names or len(names) < 2:
        raise ValueError(f"select {baseline} and at least one other candidate")
    found = [read_manifest(prepared / name) for name in names]
    if [manifest.name for manifest in found] != names:
        raise ValueError("prepared manifest names do not match candidate selection")
    return found, baseline


def load_scenarios(corpus: Path, only: list[str] | None) -> dict[str, Scenario]:
    with open(HERE / "scenarios.toml", "rb") as f:
        table = ScenariosFile.model_validate(tomllib.load(f)).scenarios
    manifest = CorpusManifest.model_validate_json((corpus / "corpus.json").read_text())
    if only and set(only) - table.keys():
        raise ValueError(
            "unknown scenarios: " + ", ".join(sorted(set(only) - table.keys()))
        )
    out: dict[str, Scenario] = {}
    for name, sc in table.items():
        if only and name not in only:
            continue
        if sc.dataset and sc.dataset not in manifest.sources:
            if only:
                raise ValueError(
                    f"{name}: {sc.dataset} inputs missing; run bench corpus --omarchy --out {corpus}"
                )
            continue
        args: list[str] = []
        for a in sc.args:
            if any(ch in a for ch in "*?["):
                matches = sorted(
                    filename
                    for filename in manifest.files
                    if PurePosixPath(filename).full_match(a)
                )
                if not matches:
                    sys.exit(
                        f"bench: scenario {name}: glob {a!r} matches nothing in {corpus}"
                    )
                args.extend(matches)
            else:
                args.append(a)
        fmt = "tty"
        if "-f" in args:
            fmt = args[args.index("-f") + 1]
        out[name] = Scenario(
            description=sc.description,
            args=args,
            format=fmt,
            label=sc.label,
            cwd=manifest.sources[sc.dataset].prefix if sc.dataset else "",
            max_run_seconds=sc.max_run_seconds,
        )
    if not out:
        sys.exit("bench: no scenarios selected")
    return out


def environment(hyperfine: str) -> Environment:
    try:
        version: str | None = subprocess.run(
            [hyperfine, "--version"], capture_output=True, text=True, check=True
        ).stdout.strip()
    except OSError:
        version = None
    cpu_model: str | None = None
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("model name"):
                    cpu_model = line.split(":", 1)[1].strip()
                    break
    except OSError:
        pass
    mem_total_kib: int | None = None
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal"):
                    mem_total_kib = int(line.split()[1])
                    break
    except OSError:
        pass
    loadavg: tuple[float, float, float] | None = None
    try:
        loadavg = os.getloadavg()
    except OSError:
        pass
    gov = Path("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")
    return Environment(
        hostname=platform.node(),
        kernel=platform.release(),
        os=platform.platform(),
        arch=platform.machine(),
        python=platform.python_version(),
        cpu_count=os.cpu_count(),
        ci=bool(os.environ.get("CI")),
        github={
            k: os.environ[k]
            for k in (
                "GITHUB_RUN_ID",
                "GITHUB_REPOSITORY",
                "GITHUB_SHA",
                "RUNNER_NAME",
                "ImageOS",
            )
            if k in os.environ
        },
        hyperfine=version,
        cpu_model=cpu_model,
        mem_total_kib=mem_total_kib,
        loadavg_at_start=loadavg,
        cpu_governor=gov.read_text().strip() if gov.exists() else None,
    )


# --- pre-check ----------------------------------------------------------------


@dataclass(frozen=True)
class Guarded:
    exit: int | None
    signal: int | None
    wall_s: float
    peak_rss_bytes: int
    killed: str | None


@dataclass
class WatchdogState:
    reason: str | None = None
    peak_rss: int = 0


@dataclass
class CandidateBudget:
    seconds: float
    spent_s: float = 0.0
    exhausted: bool = False

    @property
    def remaining(self) -> float:
        # Leave time for process-group termination and reaping at the boundary.
        return (
            0.0
            if self.exhausted
            else max(0.0, self.seconds - self.spent_s - min(0.1, self.seconds / 10))
        )

    @property
    def reason(self) -> str:
        return f"total candidate measurement budget of {self.seconds:g}s exhausted"


def run_guarded(
    cmd: list[str], cwd: Path, timeout: float, max_rss: int, stdout: Path, stderr: Path
) -> Guarded:
    """Measure from a small native supervisor, avoiding Python's pre-exec RSS floor.

    GNU time records the completed command's peak. The watchdog bounds elapsed
    time and process-tree RSS, retaining sampled memory when the group is killed.
    """
    timer = Path("/usr/bin/time")
    if not timer.is_file():
        raise ValueError(
            "pre-check memory accounting requires GNU time (/usr/bin/time)"
        )
    memory = stdout.with_suffix(".rss").resolve()
    memory.unlink(missing_ok=True)
    watch = WatchdogState()
    done = threading.Event()
    with open(stdout, "wb") as out, open(stderr, "wb") as err:
        start = time.perf_counter()
        proc = subprocess.Popen(
            [str(timer), "-q", "-f", "%M", "-o", str(memory), "--", *cmd],
            cwd=cwd,
            stdout=out,
            stderr=err,
            start_new_session=True,
        )

        def watchdog() -> None:
            while not done.is_set():
                total = 0
                pending = [proc.pid]
                seen: set[int] = set()
                while pending:
                    pid = pending.pop()
                    if pid in seen:
                        continue
                    seen.add(pid)
                    try:
                        for line in (
                            Path(f"/proc/{pid}/status").read_text().splitlines()
                        ):
                            if line.startswith("VmRSS:"):
                                total += int(line.split()[1]) * 1024
                        pending.extend(
                            int(child)
                            for child in Path(f"/proc/{pid}/task/{pid}/children")
                            .read_text()
                            .split()
                        )
                    except OSError:
                        pass
                watch.peak_rss = max(watch.peak_rss, total)
                if time.perf_counter() - start > timeout:
                    watch.reason = f"timeout after {timeout:g}s"
                elif total > max_rss:
                    watch.reason = f"process-tree RSS exceeded {max_rss / 2**30:g} GiB"
                if watch.reason:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    return
                done.wait(0.02)

        thread = threading.Thread(target=watchdog, daemon=True)
        thread.start()
        proc.wait()
        done.set()
        wall = time.perf_counter() - start
        thread.join()
    if watch.reason:
        rss = watch.peak_rss
    else:
        value = memory.read_text().strip() if memory.is_file() else ""
        if not value.isdecimal():
            raise ValueError("GNU time did not record a valid peak RSS")
        rss = int(value) * 1024
    return Guarded(
        exit=proc.returncode if proc.returncode >= 0 else None,
        signal=-proc.returncode if proc.returncode < 0 else None,
        wall_s=wall,
        peak_rss_bytes=rss,
        killed=watch.reason,
    )


def classify(g: Guarded, max_run: float) -> tuple[Status, str | None]:
    # ShellCheck exits 0 (clean) or 1 (findings); anything else is a failure.
    if g.killed:
        return "failed", g.killed
    if g.signal is not None:
        return "failed", f"killed by signal {g.signal}"
    if g.exit not in (0, 1):
        return "failed", f"exit code {g.exit}"
    if g.wall_s > max_run:
        # Correct but too slow to sample dozens of times inside the budget:
        # keep this one measurement, skip the rounds.
        return (
            "slow",
            f"one run took {g.wall_s:.1f}s, over the {max_run:g}s per-run budget; timed once only",
        )
    return "ok", None


def canonical(fmt: str, data: bytes) -> bytes:
    if fmt in ("json", "json1"):
        try:
            return json.dumps(
                JSON.validate_json(data), sort_keys=True, indent=1
            ).encode()
        except ValueError:
            return data
    return data


def precheck(
    candidates: list[Manifest],
    baseline: str,
    scenarios: dict[str, Scenario],
    corpus: Path,
    out: Path,
    timeout: float,
    max_rss: int,
    pin: str | None,
    max_run: float,
    budgets: dict[str, CandidateBudget] | None = None,
) -> dict[str, dict[str, Precheck]]:
    budgets = budgets or {}
    results: dict[str, dict[str, Precheck]] = {s: {} for s in scenarios}

    def check(sname: str, c: Manifest) -> None:
        sc = scenarios[sname]
        pdir = out / "precheck" / sname
        pdir.mkdir(parents=True, exist_ok=True)
        budget = budgets.get(c.name)
        if budget and budget.remaining <= 0:
            results[sname][c.name] = Precheck(
                exit=None,
                signal=None,
                wall_s=0,
                peak_rss_bytes=0,
                killed=None,
                stdout_bytes=0,
                stdout_sha256="",
                stderr_head="",
                status="skipped",
                reason=budget.reason,
                parity="unknown",
            )
            log(f"pre-check {sname:12s} {c.name:10s} skipped: {budget.reason}")
            return
        limit = min(timeout, budget.remaining) if budget else timeout
        started = time.perf_counter()
        try:
            g = run_guarded(
                scenario_command(c, sc, pin),
                corpus / sc.cwd,
                limit,
                max_rss,
                pdir / f"{c.name}.stdout",
                pdir / f"{c.name}.stderr",
            )
        finally:
            if budget:
                budget.spent_s += time.perf_counter() - started
        stdout = (pdir / f"{c.name}.stdout").read_bytes()
        status, reason = classify(g, sc.max_run_seconds or max_run)
        if budget and limit < timeout and g.killed and g.killed.startswith("timeout"):
            status, reason = "limited", budget.reason + "; sweep did not complete"
            budget.exhausted = True
        r = Precheck(
            exit=g.exit,
            signal=g.signal,
            wall_s=g.wall_s,
            peak_rss_bytes=g.peak_rss_bytes,
            killed=g.killed,
            stdout_bytes=len(stdout),
            stdout_sha256=hashlib.sha256(stdout).hexdigest(),
            stderr_head=(pdir / f"{c.name}.stderr").read_text(errors="replace")[:2000],
            status=status,
            reason=reason,
            parity="unknown",
        )
        results[sname][c.name] = r
        log(
            f"pre-check {sname:12s} {c.name:10s} {r.status:6s} {r.wall_s:7.3f}s  rss {r.peak_rss_bytes / 2**20:8.1f} MiB  exit {r.exit}  {r.reason or ''}"
        )

    # Give a capped candidate its complete GCC sweep before overlapping groups
    # can spend the allowance. All other candidates retain the normal order.
    if "omarchy-all" in scenarios:
        for c in candidates:
            if c.name in budgets:
                check("omarchy-all", c)

    for sname, sc in scenarios.items():
        pdir = out / "precheck" / sname
        for c in candidates:
            if c.name not in results[sname]:
                check(sname, c)

        base = results[sname][baseline]
        base_out = (
            canonical(sc.format, (pdir / f"{baseline}.stdout").read_bytes())
            if base.status in ("ok", "slow")
            else b""
        )
        for c in candidates:
            r = results[sname][c.name]
            if c.name == baseline:
                r.parity = "baseline"
                continue
            if base.status not in ("ok", "slow") or r.status not in ("ok", "slow"):
                continue
            mine = canonical(sc.format, (pdir / f"{c.name}.stdout").read_bytes())
            same = mine == base_out and r.exit == base.exit
            r.parity = "identical" if same else "differs"
            if not same:
                diff = difflib.unified_diff(
                    base_out.decode(errors="replace").splitlines(),
                    mine.decode(errors="replace").splitlines(),
                    fromfile=f"{baseline} (exit {base.exit})",
                    tofile=f"{c.name} (exit {r.exit})",
                    lineterm="",
                    n=1,
                )
                lines = list(diff)
                r.diff_lines = sum(
                    1 for l in lines if l[:1] in "+-" and l[:3] not in ("+++", "---")
                )
                _ = (pdir / f"{c.name}.diff").write_text("\n".join(lines) + "\n")
                warn(
                    f"{sname}: {c.name} output differs from {baseline} ({r.diff_lines} lines; see {pdir / (c.name + '.diff')})"
                )
    return results


# --- timing -------------------------------------------------------------------


def wrap(pin: str | None, cmd: list[str]) -> list[str]:
    return ["taskset", "-c", pin, *cmd] if pin else cmd


def scenario_command(
    candidate: Manifest, scenario: Scenario, pin: str | None
) -> list[str]:
    prefix = scenario.cwd.rstrip("/") + "/" if scenario.cwd else ""
    args = [arg.removeprefix(prefix) if prefix else arg for arg in scenario.args]
    return wrap(pin, [candidate.binary, *args])


class TimedRoundTimeout(ValueError):
    """A candidate outgrew its sampling budget; its pre-check remains valid."""

    def __init__(self, message: str, candidate_limited: bool = False):
        super().__init__(message)
        self.candidate_limited = candidate_limited


def hyperfine_one(
    hyperfine: str,
    corpus: Path,
    export: Path,
    warmup: int,
    runs: int,
    name: str,
    cmd: list[str],
    timeout: float = 600.0,
    *,
    wall_timeout: float | None = None,
) -> HyperfineResult:
    """One hyperfine process for ONE command, so its `memory_usage_byte` (the
    cumulative RUSAGE_CHILDREN maximum of that process) belongs to this command
    alone. Returns the command's entry of hyperfine's JSON export."""
    argv = [
        hyperfine,
        "-N",
        "--warmup",
        str(warmup),
        "--runs",
        str(runs),
        "--ignore-failure",
        "--style",
        "none",
        "--output",
        "null",
        "--export-json",
        str(export),
        "-n",
        name,
        shlex.join(cmd),
    ]
    # hyperfine warns about every non-zero exit (ShellCheck exits 1 on findings); keep its stderr unless it actually fails.
    proc = subprocess.Popen(
        argv,
        cwd=corpus,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    batch_limit = (runs + warmup) * timeout + 10
    limit = min(batch_limit, wall_timeout) if wall_timeout is not None else batch_limit
    try:
        _, stderr = proc.communicate(timeout=limit)
    except subprocess.TimeoutExpired as error:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        if export.exists():
            export.rename(export.with_suffix(".incomplete"))
        raise TimedRoundTimeout(
            f"{name}: timed round exceeded its {error.timeout:g}s execution budget",
            candidate_limited=wall_timeout is not None and wall_timeout <= batch_limit,
        ) from error
    if proc.returncode != 0:
        raise ValueError(f"hyperfine failed ({proc.returncode}):\n{stderr}")
    return HyperfineExport.model_validate_json(export.read_text()).results[0]


class Args(argparse.Namespace):
    config: Path = HERE / "candidates.toml"
    prepared: Path = BENCH / "prepared"
    corpus: Path = BENCH / "corpus"
    out: Path | None = None
    rounds: int = 5
    runs: int = 10
    warmup: int = 3
    seed: int = 1
    scenarios: str = ""
    candidates: str = ""
    pin: str | None = None
    max_rss_gib: float | None = None
    timeout: float | None = None
    max_run_seconds: float | None = None
    h2r_budget_seconds: float = 600.0
    hyperfine: str = shutil.which("hyperfine") or "hyperfine"


def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(
        description=(__doc__ or "").split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    _ = ap.add_argument("--config", type=Path)
    _ = ap.add_argument("--prepared", type=Path)
    _ = ap.add_argument("--corpus", type=Path)
    _ = ap.add_argument("--out", type=Path)
    _ = ap.add_argument("--rounds", type=int)
    _ = ap.add_argument("--runs", type=int)
    _ = ap.add_argument("--warmup", type=int)
    _ = ap.add_argument("--seed", type=int)
    _ = ap.add_argument("--scenarios", help="comma-separated subset")
    _ = ap.add_argument("--candidates", help="comma-separated subset")
    _ = ap.add_argument(
        "--pin", help="CPU to pin every benchmarked process to (taskset)"
    )
    _ = ap.add_argument(
        "--max-rss-gib",
        type=float,
        help="pre-check memory cap (default: physical RAM minus 1 GiB)",
    )
    _ = ap.add_argument(
        "--timeout",
        type=float,
        help="override pre-check wall-clock cap, seconds (default: 600 synthetic-only, 1200 with Omarchy)",
    )
    _ = ap.add_argument(
        "--max-run-seconds",
        type=float,
        help="override workload sampling budgets (default: 15s synthetic, 60s Omarchy); slower candidates are timed once only",
    )
    _ = ap.add_argument("--hyperfine")
    _ = ap.add_argument(
        "--h2r-budget-seconds",
        type=float,
        help="total h2r measurement time across pre-checks, warm-ups and timed runs (default: 600s); prioritize the complete Omarchy GCC sweep",
    )
    return ap


def main(argv: list[str] | None = None) -> Path:
    args = parser().parse_args(argv, namespace=Args())

    if (
        args.warmup < 0
        or (args.timeout is not None and args.timeout <= 0)
        or (args.max_run_seconds is not None and args.max_run_seconds <= 0)
        or (args.max_rss_gib is not None and args.max_rss_gib <= 0)
        or not math.isfinite(args.h2r_budget_seconds)
        or args.h2r_budget_seconds <= 0
    ):
        raise ValueError(
            "warmup must be nonnegative and execution limits must be positive"
        )
    if args.rounds < 1 or args.runs < 1:
        sys.exit("bench: --rounds and --runs must be at least 1")
    if args.rounds * args.runs < 20:
        warn(
            f"only {args.rounds * args.runs} samples per candidate; confidence intervals will be wide"
        )
    if args.pin is not None and not shutil.which("taskset"):
        sys.exit("bench: --pin needs taskset (util-linux)")

    max_rss_gib = args.max_rss_gib
    if max_rss_gib is None:
        total = 0
        try:
            with open("/proc/meminfo") as f:
                total = next(
                    int(ln.split()[1]) * 1024 for ln in f if ln.startswith("MemTotal")
                )
        except OSError, StopIteration:
            pass
        max_rss_gib = max(1.0, total / 2**30 - 1) if total else 4.0

    corpus_manifest = args.corpus / "corpus.json"
    if not corpus_manifest.exists():
        sys.exit(f"bench: {corpus_manifest} missing; run `mise run bench:corpus` first")
    corpus_info = CorpusManifest.model_validate_json(corpus_manifest.read_text())

    out = (
        args.out or BENCH / "results" / datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    ).resolve()
    corpus = args.corpus.resolve()
    if (out / "run.json").exists():
        raise ValueError(f"{out} already contains a run; choose a new output directory")
    out.mkdir(parents=True, exist_ok=True)
    (out / "raw").mkdir(exist_ok=True)

    only_c = [s for s in args.candidates.split(",") if s] or None
    only_s = [s for s in args.scenarios.split(",") if s] or None
    candidates, baseline = load_candidates(args.prepared, only_c, args.config)
    scenarios = load_scenarios(corpus, only_s)
    timeout = args.timeout or (
        1200.0 if any(scenario.cwd for scenario in scenarios.values()) else 600.0
    )
    if args.max_run_seconds is not None:
        scenarios = {
            name: scenario.model_copy(update={"max_run_seconds": args.max_run_seconds})
            for name, scenario in scenarios.items()
        }
    for filename, entry in corpus_info.files.items():
        if hashlib.sha256((corpus / filename).read_bytes()).hexdigest() != entry.sha256:
            raise ValueError(f"corpus file changed: {filename}; regenerate the corpus")
    env = environment(args.hyperfine)
    log(
        f"{len(candidates)} candidates ({', '.join(c.name for c in candidates)}; baseline {baseline}), "
        + f"{len(scenarios)} scenarios, {args.rounds} rounds x {args.runs} runs (+{args.warmup} warm-up) -> {out}"
    )
    if env.loadavg_at_start and env.loadavg_at_start[0] > 1.0:
        warn(
            f"1-minute load average is {env.loadavg_at_start[0]:.2f}; something else is using this machine"
        )

    budgets = {
        c.name: CandidateBudget(args.h2r_budget_seconds)
        for c in candidates
        if c.name == "h2r"
    }
    checks = precheck(
        candidates,
        baseline,
        scenarios,
        corpus,
        out,
        timeout,
        int(max_rss_gib * 2**30),
        args.pin,
        args.max_run_seconds or 15.0,
        budgets,
    )

    rng = random.Random(args.seed)
    samples: dict[str, dict[str, Samples]] = {
        s: {c.name: Samples() for c in candidates} for s in scenarios
    }
    eligible = {
        s: [c for c in candidates if checks[s][c.name].status == "ok"]
        for s in scenarios
    }
    for s, cs in eligible.items():
        if len(cs) < 2:
            warn(
                f"scenario {s}: fewer than two candidates passed the pre-check; it will be measured but not compared"
            )

    started = time.time()
    for rnd in range(1, args.rounds + 1):
        for sname, sc in scenarios.items():
            order = eligible[sname][:]
            rng.shuffle(order)
            if not order:
                continue
            summary: list[str] = []
            for pos, c in enumerate(order):
                cmd = scenario_command(c, sc, args.pin)
                export = out / "raw" / f"round{rnd:02d}-{sname}-{c.name}.json"
                entry = samples[sname][c.name]
                budget = budgets.get(c.name)
                if budget and budget.remaining <= 0:
                    entry.stop_reason = budget.reason + "; showing initial sweep only"
                    eligible[sname].remove(c)
                    continue
                kwargs = {"wall_timeout": budget.remaining} if budget else {}
                candidate_started = time.perf_counter()
                try:
                    res = hyperfine_one(
                        args.hyperfine,
                        corpus / sc.cwd,
                        export,
                        args.warmup,
                        args.runs,
                        c.name,
                        cmd,
                        min(
                            timeout, sc.max_run_seconds or args.max_run_seconds or 15.0
                        ),
                        **kwargs,
                    )
                except TimedRoundTimeout as error:
                    if budget and error.candidate_limited:
                        budget.exhausted = True
                    entry.stop_reason = (
                        f"sampling stopped in round {rnd}: {budget.reason if budget and error.candidate_limited else error}; "
                        f"{entry.n} completed samples retained in raw data; showing initial sweep only"
                    )
                    eligible[sname].remove(c)
                    warn(f"{sname}: {entry.stop_reason}")
                    summary.append(f"{c.name} sampling stopped")
                    continue
                finally:
                    if budget:
                        budget.spent_s += time.perf_counter() - candidate_started
                entry.times.extend(res.times)
                entry.memory_bytes.extend(res.memory_usage_byte)
                entry.exit_codes.extend(res.exit_codes)
                entry.rounds.append(
                    Round(
                        round=rnd,
                        position=pos,
                        times=res.times,
                        memory_bytes=res.memory_usage_byte,
                        user_mean=res.user,
                        system_mean=res.system,
                    )
                )
                summary.append(f"{c.name} {res.mean * 1000:8.1f}ms")
            elapsed = time.time() - started
            log(
                f"round {rnd}/{args.rounds} {sname:12s} [{' > '.join(c.name for c in order)}]  "
                + "  ".join(summary)
                + f"   ({elapsed:.0f}s elapsed)"
            )

    run = Run(
        version=2,
        created=datetime.now(UTC).isoformat(timespec="seconds"),
        config=Config(
            rounds=args.rounds,
            runs=args.runs,
            warmup=args.warmup,
            seed=args.seed,
            pin=args.pin,
            max_rss_gib=max_rss_gib,
            timeout_s=timeout,
            max_run_s=args.max_run_seconds or 15.0,
            hyperfine_flags=["-N", "--ignore-failure", "--output", "null"],
            # one hyperfine process per candidate per round: memory_bytes are per candidate
            memory_isolated=True,
            candidate_budget_s={
                name: budget.seconds for name, budget in budgets.items()
            },
        ),
        environment=env,
        baseline=baseline,
        candidates=candidates,
        corpus=CorpusRef(
            dir=str(corpus),
            sha256=corpus_info.sha256,
            seed=corpus_info.seed,
            files={k: v.lines for k, v in corpus_info.files.items()},
            sources=corpus_info.sources,
        ),
        scenarios=scenarios,
        precheck=checks,
        samples=samples,
        elapsed_s=time.time() - started,
        candidate_elapsed_s={name: budget.spent_s for name, budget in budgets.items()},
    )
    _ = (out / "run.json").write_text(run.model_dump_json(indent=1) + "\n")
    log(f"wrote {out / 'run.json'} ({run.elapsed_s:.0f}s of timing)")
    return out


if __name__ == "__main__":
    main()
