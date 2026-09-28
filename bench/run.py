#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# ///
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
   hyperfine invocation (`-N`, no shell) with `runs` timed runs per candidate
   after `warmup` untimed ones. The candidate order is re-shuffled every
   round from a seeded PRNG, so slow drift of the machine (thermal state,
   background load, page cache) spreads over all candidates instead of
   landing on whichever one happened to go last. Rounds are kept apart in
   the output so the analysis can test for that drift.

3. Everything (samples, per-run memory, exit codes, the pre-check, the
   environment, the candidate manifests, the corpus checksum) goes into
   <out>/run.json for bench/analyze.py.

    run.py [--rounds 5] [--runs 10] [--warmup 3] [--seed 1] [--pin CPU]
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
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BENCH = Path(os.environ.get("BENCH_ROOT", ROOT / ".bench"))


def log(msg: str) -> None:
    print(f"\033[1;34m==> {msg}\033[0m", file=sys.stderr, flush=True)


def warn(msg: str) -> None:
    print(f"\033[1;33mwarning: {msg}\033[0m", file=sys.stderr, flush=True)


# --- inputs -----------------------------------------------------------------


def load_candidates(bin_dir: Path, only: list[str] | None) -> tuple[list[dict], str]:
    with open(HERE / "candidates.toml", "rb") as f:
        table = tomllib.load(f)["candidates"]
    baseline = next((n for n, c in table.items() if c.get("baseline")), next(iter(table)))
    found = []
    for name in table:
        if only and name not in only:
            continue
        manifest = bin_dir / name / "manifest.json"
        if not manifest.exists():
            warn(f"candidate {name!r} is not built ({manifest} missing); skipping it")
            continue
        m = json.loads(manifest.read_text())
        m["binary"] = str(bin_dir / name / "shellcheck")
        found.append(m)
    if len(found) < 2:
        sys.exit("bench: need at least two built candidates to compare")
    if baseline not in [c["name"] for c in found]:
        warn(f"baseline {baseline!r} is not among the candidates; using {found[0]['name']!r}")
        baseline = found[0]["name"]
    return found, baseline


def load_scenarios(corpus: Path, only: list[str] | None) -> dict[str, dict]:
    with open(HERE / "scenarios.toml", "rb") as f:
        table = tomllib.load(f)["scenarios"]
    out = {}
    for name, sc in table.items():
        if only and name not in only:
            continue
        args: list[str] = []
        for a in sc["args"]:
            if any(ch in a for ch in "*?["):
                matches = sorted(glob.glob(a, root_dir=corpus))
                if not matches:
                    sys.exit(f"bench: scenario {name}: glob {a!r} matches nothing in {corpus}")
                args.extend(matches)
            else:
                args.append(a)
        fmt = "tty"
        if "-f" in args:
            fmt = args[args.index("-f") + 1]
        out[name] = {"description": sc.get("description", ""), "args": args, "format": fmt}
    if not out:
        sys.exit("bench: no scenarios selected")
    return out


def environment(hyperfine: str) -> dict:
    env = {
        "hostname": platform.node(),
        "kernel": platform.release(),
        "os": platform.platform(),
        "arch": platform.machine(),
        "python": platform.python_version(),
        "cpu_count": os.cpu_count(),
        "ci": bool(os.environ.get("CI")),
        "github": {k: os.environ[k] for k in ("GITHUB_RUN_ID", "GITHUB_REPOSITORY", "GITHUB_SHA", "RUNNER_NAME", "ImageOS") if k in os.environ},
    }
    try:
        env["hyperfine"] = subprocess.run([hyperfine, "--version"], capture_output=True, text=True).stdout.strip()
    except OSError:
        env["hyperfine"] = None
    try:
        with open("/proc/cpuinfo") as f:
            for line in f:
                if line.startswith("model name"):
                    env["cpu_model"] = line.split(":", 1)[1].strip()
                    break
    except OSError:
        pass
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith("MemTotal"):
                    env["mem_total_kib"] = int(line.split()[1])
                    break
    except OSError:
        pass
    try:
        env["loadavg_at_start"] = os.getloadavg()
    except OSError:
        pass
    gov = Path("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor")
    if gov.exists():
        env["cpu_governor"] = gov.read_text().strip()
    return env


# --- pre-check ----------------------------------------------------------------


def run_guarded(cmd: list[str], cwd: Path, timeout: float, max_rss: int, stdout: Path, stderr: Path) -> dict:
    """Run once; kill on timeout or when RSS passes max_rss. Returns exit, signal,
    wall, peak RSS (bytes, from rusage) and the reason it was killed, if any."""
    killed = {"reason": None}
    with open(stdout, "wb") as out, open(stderr, "wb") as err:
        start = time.perf_counter()
        proc = subprocess.Popen(cmd, cwd=cwd, stdout=out, stderr=err)

        def watchdog():
            status = Path(f"/proc/{proc.pid}/status")
            while proc.poll() is None and killed["reason"] is None:
                if time.perf_counter() - start > timeout:
                    killed["reason"] = f"timeout after {timeout:g}s"
                else:
                    try:
                        for line in status.read_text().splitlines():
                            if line.startswith("VmRSS:"):
                                if int(line.split()[1]) * 1024 > max_rss:
                                    killed["reason"] = f"peak RSS exceeded {max_rss / 2**30:g} GiB"
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
        proc.returncode = os.waitstatus_to_exitcode(status) if not os.WIFSIGNALED(status) else -os.WTERMSIG(status)
        t.join()
    return {
        "exit": proc.returncode if proc.returncode >= 0 else None,
        "signal": -proc.returncode if proc.returncode < 0 else None,
        "wall_s": wall,
        "peak_rss_bytes": rusage.ru_maxrss * 1024,
        "killed": killed["reason"],
    }


def canonical(fmt: str, data: bytes) -> bytes:
    if fmt in ("json", "json1"):
        try:
            return json.dumps(json.loads(data), sort_keys=True, indent=1).encode()
        except ValueError:
            return data
    return data


def precheck(candidates, baseline, scenarios, corpus: Path, out: Path, timeout: float, max_rss: int, pin, max_run: float) -> dict:
    results: dict[str, dict[str, dict]] = {}
    for sname, sc in scenarios.items():
        results[sname] = {}
        pdir = out / "precheck" / sname
        pdir.mkdir(parents=True, exist_ok=True)
        for c in candidates:
            cmd = wrap(pin, [c["binary"], *sc["args"]])
            r = run_guarded(cmd, corpus, timeout, max_rss, pdir / f"{c['name']}.stdout", pdir / f"{c['name']}.stderr")
            stdout = (pdir / f"{c['name']}.stdout").read_bytes()
            r["stdout_bytes"] = len(stdout)
            r["stdout_sha256"] = hashlib.sha256(stdout).hexdigest()
            r["stderr_head"] = (pdir / f"{c['name']}.stderr").read_text(errors="replace")[:2000]
            # ShellCheck exits 0 (clean) or 1 (findings); anything else is a failure.
            if r["killed"]:
                r["status"] = "failed"
                r["reason"] = r["killed"]
            elif r["signal"] is not None:
                r["status"] = "failed"
                r["reason"] = f"killed by signal {r['signal']}"
            elif r["exit"] not in (0, 1):
                r["status"] = "failed"
                r["reason"] = f"exit code {r['exit']}"
            elif r["wall_s"] > max_run:
                # Correct but too slow to sample dozens of times inside the budget:
                # keep this one measurement, skip the rounds.
                r["status"] = "slow"
                r["reason"] = f"one run took {r['wall_s']:.1f}s, over the {max_run:g}s per-run budget; timed once only"
            else:
                r["status"] = "ok"
                r["reason"] = None
            results[sname][c["name"]] = r
            log(f"pre-check {sname:12s} {c['name']:10s} {r['status']:6s} {r['wall_s']:7.3f}s  rss {r['peak_rss_bytes'] / 2**20:8.1f} MiB  exit {r['exit']}  {r['reason'] or ''}")

        base = results[sname][baseline]
        base_out = canonical(sc["format"], (pdir / f"{baseline}.stdout").read_bytes())
        for c in candidates:
            r = results[sname][c["name"]]
            if c["name"] == baseline:
                r["parity"] = "baseline"
                continue
            if base["status"] not in ("ok", "slow") or r["status"] not in ("ok", "slow"):
                r["parity"] = "unknown"
                continue
            mine = canonical(sc["format"], (pdir / f"{c['name']}.stdout").read_bytes())
            same = mine == base_out and r["exit"] == base["exit"]
            r["parity"] = "identical" if same else "differs"
            if not same:
                diff = difflib.unified_diff(
                    base_out.decode(errors="replace").splitlines(),
                    mine.decode(errors="replace").splitlines(),
                    fromfile=f"{baseline} (exit {base['exit']})",
                    tofile=f"{c['name']} (exit {r['exit']})",
                    lineterm="",
                    n=1,
                )
                lines = list(diff)
                r["diff_lines"] = sum(1 for l in lines if l[:1] in "+-" and l[:3] not in ("+++", "---"))
                (pdir / f"{c['name']}.diff").write_text("\n".join(lines) + "\n")
                warn(f"{sname}: {c['name']} output differs from {baseline} ({r['diff_lines']} lines; see {pdir / (c['name'] + '.diff')})")
    return results


# --- timing -------------------------------------------------------------------


def wrap(pin, cmd: list[str]) -> list[str]:
    return ["taskset", "-c", str(pin), *cmd] if pin not in (None, "") else cmd


def hyperfine_round(hyperfine: str, corpus: Path, export: Path, warmup: int, runs: int, cmds: list[tuple[str, list[str]]]) -> dict:
    argv = [
        hyperfine, "-N", "--warmup", str(warmup), "--runs", str(runs),
        "--ignore-failure", "--style", "none", "--output", "null",
        "--export-json", str(export),
    ]
    for name, cmd in cmds:
        argv += ["-n", name, shlex.join(cmd)]
    # hyperfine warns about every non-zero exit (ShellCheck exits 1 on findings); keep
    # its stderr unless it actually fails.
    proc = subprocess.run(argv, cwd=corpus, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if proc.returncode != 0:
        sys.exit(f"bench: hyperfine failed ({proc.returncode}):\n{proc.stderr}")
    with open(export) as f:
        return json.load(f)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin-dir", type=Path, default=BENCH / "bin")
    ap.add_argument("--corpus", type=Path, default=BENCH / "corpus")
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--rounds", type=int, default=5)
    ap.add_argument("--runs", type=int, default=10)
    ap.add_argument("--warmup", type=int, default=3)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--scenarios", default="", help="comma-separated subset")
    ap.add_argument("--candidates", default="", help="comma-separated subset")
    ap.add_argument("--pin", default=None, help="CPU to pin every benchmarked process to (taskset)")
    ap.add_argument("--max-rss-gib", type=float, default=4.0, help="pre-check memory cap")
    ap.add_argument("--timeout", type=float, default=600.0, help="pre-check wall-clock cap per run, seconds")
    ap.add_argument("--max-run-seconds", type=float, default=15.0, help="a candidate whose pre-check run takes longer is timed once only, not in the rounds")
    ap.add_argument("--hyperfine", default=shutil.which("hyperfine") or "hyperfine")
    args = ap.parse_args()

    if args.rounds < 1 or args.runs < 1:
        sys.exit("bench: --rounds and --runs must be at least 1")
    if args.rounds * args.runs < 20:
        warn(f"only {args.rounds * args.runs} samples per candidate; confidence intervals will be wide")
    if args.pin is not None and not shutil.which("taskset"):
        sys.exit("bench: --pin needs taskset (util-linux)")

    corpus_manifest = args.corpus / "corpus.json"
    if not corpus_manifest.exists():
        sys.exit(f"bench: {corpus_manifest} missing; run `mise run bench:corpus` first")
    corpus_info = json.loads(corpus_manifest.read_text())

    out = (args.out or BENCH / "results" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")).resolve()
    args.corpus = args.corpus.resolve()
    args.bin_dir = args.bin_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    (out / "raw").mkdir(exist_ok=True)

    only_c = [s for s in args.candidates.split(",") if s] or None
    only_s = [s for s in args.scenarios.split(",") if s] or None
    candidates, baseline = load_candidates(args.bin_dir, only_c)
    scenarios = load_scenarios(args.corpus, only_s)
    env = environment(args.hyperfine)
    log(f"{len(candidates)} candidates ({', '.join(c['name'] for c in candidates)}; baseline {baseline}), "
        f"{len(scenarios)} scenarios, {args.rounds} rounds x {args.runs} runs (+{args.warmup} warm-up) -> {out}")
    if env.get("loadavg_at_start") and env["loadavg_at_start"][0] > 1.0:
        warn(f"1-minute load average is {env['loadavg_at_start'][0]:.2f}; something else is using this machine")

    checks = precheck(candidates, baseline, scenarios, args.corpus, out, args.timeout, int(args.max_rss_gib * 2**30), args.pin, args.max_run_seconds)

    rng = random.Random(args.seed)
    samples: dict[str, dict[str, dict]] = {
        s: {c["name"]: {"times": [], "memory_bytes": [], "exit_codes": [], "rounds": []} for c in candidates}
        for s in scenarios
    }
    eligible = {s: [c for c in candidates if checks[s][c["name"]]["status"] == "ok"] for s in scenarios}
    for s, cs in eligible.items():
        if len(cs) < 2:
            warn(f"scenario {s}: fewer than two candidates passed the pre-check; it will be measured but not compared")

    started = time.time()
    for rnd in range(1, args.rounds + 1):
        for sname, sc in scenarios.items():
            order = eligible[sname][:]
            rng.shuffle(order)
            if not order:
                continue
            cmds = [(c["name"], wrap(args.pin, [c["binary"], *sc["args"]])) for c in order]
            export = out / "raw" / f"round{rnd:02d}-{sname}.json"
            data = hyperfine_round(args.hyperfine, args.corpus, export, args.warmup, args.runs, cmds)
            summary = []
            for pos, res in enumerate(data["results"]):
                name = res["command"]
                if name not in samples[sname]:
                    continue
                entry = samples[sname][name]
                entry["times"].extend(res["times"])
                entry["memory_bytes"].extend(res.get("memory_usage_byte", []))
                entry["exit_codes"].extend(res.get("exit_codes", []))
                entry["rounds"].append({
                    "round": rnd, "position": pos, "times": res["times"],
                    "user_mean": res.get("user"), "system_mean": res.get("system"),
                })
                summary.append(f"{name} {res['mean'] * 1000:8.1f}ms")
            elapsed = time.time() - started
            log(f"round {rnd}/{args.rounds} {sname:12s} [{' > '.join(c['name'] for c in order)}]  " + "  ".join(summary) + f"   ({elapsed:.0f}s elapsed)")

    for sname in scenarios:
        for c in candidates:
            e = samples[sname][c["name"]]
            e["n"] = len(e["times"])

    run = {
        "version": 1,
        "created": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "config": {
            "rounds": args.rounds, "runs": args.runs, "warmup": args.warmup, "seed": args.seed,
            "pin": args.pin, "max_rss_gib": args.max_rss_gib, "timeout_s": args.timeout, "max_run_s": args.max_run_seconds,
            "hyperfine_flags": ["-N", "--ignore-failure", "--output", "null"],
        },
        "environment": env,
        "baseline": baseline,
        "candidates": candidates,
        "corpus": {"dir": str(args.corpus), "sha256": corpus_info["sha256"], "seed": corpus_info["seed"],
                   "files": {k: v["lines"] for k, v in corpus_info["files"].items()}},
        "scenarios": scenarios,
        "precheck": checks,
        "samples": samples,
        "elapsed_s": time.time() - started,
    }
    (out / "run.json").write_text(json.dumps(run, indent=1) + "\n")
    log(f"wrote {out / 'run.json'} ({run['elapsed_s']:.0f}s of timing)")
    print(out)


if __name__ == "__main__":
    main()
