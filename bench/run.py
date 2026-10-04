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
   background load, page cache) spreads over all candidates instead of
   landing on whichever one happened to go last. Rounds are kept apart in
   the output so the analysis can test for that drift.

   Why one hyperfine process per candidate: hyperfine reports memory from
   getrusage(RUSAGE_CHILDREN).ru_maxrss, which is the maximum over *all*
   children the hyperfine process has reaped so far, not per command. With
   several commands in one invocation every later command would report at
   least the largest peak of the commands before it (a small candidate that
   ran after a big one inherits the big one's number). A fresh hyperfine
   process per candidate makes each `memory_usage_byte` the candidate's own.
   The timing statistics are unaffected: same runs, warm-up, order and flags.

3. Everything (samples, per-run memory, exit codes, the pre-check, the
   environment, the candidate manifests, the corpus checksum) goes into
   <out>/run.json for bench/analyze.py.

    bench [--rounds 5] [--runs 10] [--warmup 3] [--seed 1] [--pin CPU]
          [--scenarios a,b] [--candidates x,y] [--max-rss-gib 4] [--timeout 600]
          [--bin-dir .bench/bin] [--corpus .bench/corpus] [--out .bench/results/<ts>]
"""

import argparse
import difflib
import glob
import hashlib
import json
import os
import platform
import random
import shlex
import shutil
import subprocess
import sys
import threading
import time
import tomllib
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path

from pydantic import JsonValue, TypeAdapter

from bench.schema import (
    CandidatesFile,
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
ROOT = HERE.parent
BENCH = Path(os.environ.get("BENCH_ROOT", ROOT / ".bench"))
JSON: TypeAdapter[JsonValue] = TypeAdapter(JsonValue)


def log(msg: str) -> None:
    print(f"\033[1;34m==> {msg}\033[0m", file=sys.stderr, flush=True)


def warn(msg: str) -> None:
    print(f"\033[1;33mwarning: {msg}\033[0m", file=sys.stderr, flush=True)


# --- inputs -----------------------------------------------------------------


def load_candidates(
    bin_dir: Path, only: list[str] | None
) -> tuple[list[Manifest], str]:
    with open(HERE / "candidates.toml", "rb") as f:
        table = CandidatesFile.model_validate(tomllib.load(f)).candidates
    baseline = next((n for n, c in table.items() if c.baseline), next(iter(table)))
    found: list[Manifest] = []
    for name in table:
        if only and name not in only:
            continue
        manifest = bin_dir / name / "manifest.json"
        if not manifest.exists():
            warn(f"candidate {name!r} is not built ({manifest} missing); skipping it")
            continue
        m = Manifest.model_validate_json(manifest.read_text())
        m.binary = str(bin_dir / name / "shellcheck")
        found.append(m)
    if len(found) < 2:
        sys.exit("bench: need at least two built candidates to compare")
    if baseline not in [c.name for c in found]:
        warn(
            f"baseline {baseline!r} is not among the candidates; using {found[0].name!r}"
        )
        baseline = found[0].name
    return found, baseline


def load_scenarios(corpus: Path, only: list[str] | None) -> dict[str, Scenario]:
    with open(HERE / "scenarios.toml", "rb") as f:
        table = ScenariosFile.model_validate(tomllib.load(f)).scenarios
    out: dict[str, Scenario] = {}
    for name, sc in table.items():
        if only and name not in only:
            continue
        args: list[str] = []
        for a in sc.args:
            if any(ch in a for ch in "*?["):
                matches = sorted(glob.glob(a, root_dir=corpus))
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
        out[name] = Scenario(description=sc.description, args=args, format=fmt)
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


def run_guarded(
    cmd: list[str], cwd: Path, timeout: float, max_rss: int, stdout: Path, stderr: Path
) -> Guarded:
    """Run once; kill on timeout or when RSS passes max_rss. Returns exit, signal,
    wall, peak RSS (bytes, from rusage) and the reason it was killed, if any."""
    killed: dict[str, str | None] = {"reason": None}
    with open(stdout, "wb") as out, open(stderr, "wb") as err:
        start = time.perf_counter()
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=out, stderr=err)

        def watchdog() -> None:
            status = Path(f"/proc/{proc.pid}/status")
            while proc.poll() is None and killed["reason"] is None:
                if time.perf_counter() - start > timeout:
                    killed["reason"] = f"timeout after {timeout:g}s"
                else:
                    try:
                        for line in status.read_text().splitlines():
                            if line.startswith("VmRSS:"):
                                if int(line.split()[1]) * 1024 > max_rss:
                                    killed["reason"] = (
                                        f"peak RSS exceeded {max_rss / 2**30:g} GiB"
                                    )
                                break
                    except OSError:
                        pass
                if killed["reason"]:
                    proc.kill()
                    return
                time.sleep(0.02)

        t = threading.Thread(target=watchdog, daemon=True)
        t.start()
        _, status, rusage = os.wait4(proc.pid, 0)
        wall = time.perf_counter() - start
        proc.returncode = (
            os.waitstatus_to_exitcode(status)
            if not os.WIFSIGNALED(status)
            else -os.WTERMSIG(status)
        )
        t.join()
    return Guarded(
        exit=proc.returncode if proc.returncode >= 0 else None,
        signal=-proc.returncode if proc.returncode < 0 else None,
        wall_s=wall,
        peak_rss_bytes=rusage.ru_maxrss * 1024,
        killed=killed["reason"],
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
) -> dict[str, dict[str, Precheck]]:
    results: dict[str, dict[str, Precheck]] = {}
    for sname, sc in scenarios.items():
        results[sname] = {}
        pdir = out / "precheck" / sname
        pdir.mkdir(parents=True, exist_ok=True)
        for c in candidates:
            cmd = wrap(pin, [c.binary, *sc.args])
            g = run_guarded(
                cmd,
                corpus,
                timeout,
                max_rss,
                pdir / f"{c.name}.stdout",
                pdir / f"{c.name}.stderr",
            )
            stdout = (pdir / f"{c.name}.stdout").read_bytes()
            status, reason = classify(g, max_run)
            r = Precheck(
                exit=g.exit,
                signal=g.signal,
                wall_s=g.wall_s,
                peak_rss_bytes=g.peak_rss_bytes,
                killed=g.killed,
                stdout_bytes=len(stdout),
                stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                stderr_head=(pdir / f"{c.name}.stderr").read_text(errors="replace")[
                    :2000
                ],
                status=status,
                reason=reason,
                parity="unknown",
            )
            results[sname][c.name] = r
            log(
                f"pre-check {sname:12s} {c.name:10s} {r.status:6s} {r.wall_s:7.3f}s  rss {r.peak_rss_bytes / 2**20:8.1f} MiB  exit {r.exit}  {r.reason or ''}"
            )

        base = results[sname][baseline]
        base_out = canonical(sc.format, (pdir / f"{baseline}.stdout").read_bytes())
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


def hyperfine_one(
    hyperfine: str,
    corpus: Path,
    export: Path,
    warmup: int,
    runs: int,
    name: str,
    cmd: list[str],
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
    proc = subprocess.run(
        argv,
        cwd=corpus,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
        text=True,
        check=True,
    )
    if proc.returncode != 0:
        sys.exit(f"bench: hyperfine failed ({proc.returncode}):\n{proc.stderr}")
    return HyperfineExport.model_validate_json(export.read_text()).results[0]


class Args(argparse.Namespace):
    bin_dir: Path = BENCH / "bin"
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
    timeout: float = 600.0
    max_run_seconds: float = 15.0
    hyperfine: str = shutil.which("hyperfine") or "hyperfine"


def main() -> None:
    ap = argparse.ArgumentParser(
        description=(__doc__ or "").split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    _ = ap.add_argument("--bin-dir", type=Path)
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
        help="pre-check memory cap (default: physical RAM minus 1 GiB, so a runaway run fails instead of the machine)",
    )
    _ = ap.add_argument(
        "--timeout",
        type=float,
        help="pre-check wall-clock cap per run, seconds",
    )
    _ = ap.add_argument(
        "--max-run-seconds",
        type=float,
        help="a candidate whose pre-check run takes longer is timed once only, not in the rounds",
    )
    _ = ap.add_argument("--hyperfine")
    args = ap.parse_args(namespace=Args())

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
    out.mkdir(parents=True, exist_ok=True)
    (out / "raw").mkdir(exist_ok=True)

    only_c = [s for s in args.candidates.split(",") if s] or None
    only_s = [s for s in args.scenarios.split(",") if s] or None
    candidates, baseline = load_candidates(args.bin_dir.resolve(), only_c)
    scenarios = load_scenarios(corpus, only_s)
    env = environment(args.hyperfine)
    log(
        f"{len(candidates)} candidates ({', '.join(c.name for c in candidates)}; baseline {baseline}), "
        + f"{len(scenarios)} scenarios, {args.rounds} rounds x {args.runs} runs (+{args.warmup} warm-up) -> {out}"
    )
    if env.loadavg_at_start and env.loadavg_at_start[0] > 1.0:
        warn(
            f"1-minute load average is {env.loadavg_at_start[0]:.2f}; something else is using this machine"
        )

    checks = precheck(
        candidates,
        baseline,
        scenarios,
        corpus,
        out,
        args.timeout,
        int(max_rss_gib * 2**30),
        args.pin,
        args.max_run_seconds,
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
                cmd = wrap(args.pin, [c.binary, *sc.args])
                export = out / "raw" / f"round{rnd:02d}-{sname}-{c.name}.json"
                res = hyperfine_one(
                    args.hyperfine,
                    corpus,
                    export,
                    args.warmup,
                    args.runs,
                    c.name,
                    cmd,
                )
                entry = samples[sname][c.name]
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
            timeout_s=args.timeout,
            max_run_s=args.max_run_seconds,
            hyperfine_flags=["-N", "--ignore-failure", "--output", "null"],
            # one hyperfine process per candidate per round: memory_bytes are per candidate
            memory_isolated=True,
        ),
        environment=env,
        baseline=baseline,
        candidates=candidates,
        corpus=CorpusRef(
            dir=str(corpus),
            sha256=corpus_info.sha256,
            seed=corpus_info.seed,
            files={k: v.lines for k, v in corpus_info.files.items()},
        ),
        scenarios=scenarios,
        precheck=checks,
        samples=samples,
        elapsed_s=time.time() - started,
    )
    _ = (out / "run.json").write_text(run.model_dump_json(indent=1) + "\n")
    log(f"wrote {out / 'run.json'} ({run.elapsed_s:.0f}s of timing)")
    print(out)


if __name__ == "__main__":
    main()
