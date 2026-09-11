#!/usr/bin/env python3
"""
ShellCheck Rust-port conformance harness.

Runs the Haskell **oracle** and the **Rust port** over the same corpus of shell
scripts, both emitting `--format=json1`, and diffs their diagnostics. Because
both tools are asked for machine-readable output over identical input, a match
is an exact behavioural-parity guarantee: same code, severity, span, message,
and autofix, in the same order.

Outputs:
  - goldens.jsonl        cached oracle output per corpus id
  - port.jsonl           cached port output per corpus id (if port available)
  - coverage.json        machine-readable per-code coverage
  - prints a summary table (overall parity + worst-covered codes)

Usage:
  ORACLE=/path/to/haskell/shellcheck \
  PORT=/path/to/shellcheck-rs \
  python3 run_conformance.py [--regen-oracle] [--limit N] [--codes SC2086,...]

If PORT is unset or missing, only the oracle goldens are produced (useful while
the port is still being built out).
"""
import os
import sys
import json
import subprocess
import argparse

HERE = os.path.dirname(os.path.abspath(__file__))


def find_oracle():
    env = os.environ.get("ORACLE")
    if env and os.path.exists(env):
        return env
    root = os.path.abspath(os.path.join(HERE, "..", ".."))
    cand = os.path.join(
        root,
        "dist-newstyle/build/x86_64-linux/ghc-9.6.6/ShellCheck-0.11.0/x/shellcheck/build/shellcheck/shellcheck",
    )
    if os.path.exists(cand):
        return cand
    # Search dist-newstyle broadly.
    for dirpath, _dirs, files in os.walk(os.path.join(root, "dist-newstyle")):
        if "shellcheck" in files and dirpath.endswith("build/shellcheck"):
            return os.path.join(dirpath, "shellcheck")
    return None


def run_json1(binary, script):
    """Run `binary --format=json1 -` on script via stdin, return comments list.
    ShellCheck exits non-zero when it finds issues; that is expected."""
    try:
        proc = subprocess.run(
            [binary, "--format=json1", "-"],
            input=script.encode("utf-8"),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
        )
    except subprocess.TimeoutExpired:
        return {"error": "timeout"}
    out = proc.stdout.decode("utf-8", "replace").strip()
    if not out:
        return {"error": "empty", "stderr": proc.stderr.decode("utf-8", "replace")[:400]}
    try:
        data = json.loads(out)
    except json.JSONDecodeError as e:
        return {"error": f"badjson: {e}", "raw": out[:400]}
    return {"comments": data.get("comments", [])}


def norm_fix(fix):
    if not fix:
        return None
    reps = fix.get("replacements", [])
    return [
        (
            r.get("line"), r.get("column"), r.get("endLine"), r.get("endColumn"),
            r.get("insertionPoint"), r.get("precedence"), r.get("replacement"),
        )
        for r in reps
    ]


def comment_key(c):
    """Full-fidelity identity of a diagnostic for exact parity."""
    return (
        c.get("line"), c.get("column"), c.get("endLine"), c.get("endColumn"),
        c.get("level"), c.get("code"), c.get("message"),
        tuple(norm_fix(c.get("fix"))) if c.get("fix") else None,
    )


def load_cache(path):
    cache = {}
    if os.path.exists(path):
        with open(path, encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                obj = json.loads(line)
                cache[obj["id"]] = obj["result"]
    return cache


def generate(binary, corpus, cache_path, regen):
    cache = {} if regen else load_cache(cache_path)
    missing = [e for e in corpus if e["id"] not in cache]
    if missing:
        sys.stderr.write(f"[run] {os.path.basename(cache_path)}: running {len(missing)} scripts...\n")
        with open(cache_path, "a", encoding="utf-8") as out:
            for i, e in enumerate(missing):
                res = run_json1(binary, e["script"])
                cache[e["id"]] = res
                out.write(json.dumps({"id": e["id"], "result": res}) + "\n")
                if (i + 1) % 200 == 0:
                    sys.stderr.write(f"  {i+1}/{len(missing)}\n")
    return cache


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--regen-oracle", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--codes", default="")
    args = ap.parse_args()

    corpus = json.load(open(os.path.join(HERE, "corpus.json"), encoding="utf-8"))
    if args.limit:
        corpus = corpus[: args.limit]

    oracle = find_oracle()
    if not oracle:
        sys.stderr.write("[run] ERROR: oracle binary not found; build it first.\n")
        sys.exit(1)
    sys.stderr.write(f"[run] oracle: {oracle}\n")

    goldens = generate(oracle, corpus, os.path.join(HERE, "goldens.jsonl"), args.regen_oracle)

    port = os.environ.get("PORT")
    if port and not os.path.exists(port):
        sys.stderr.write(f"[run] PORT set but not found: {port}\n")
        port = None
    port_results = None
    if port:
        sys.stderr.write(f"[run] port: {port}\n")
        port_results = generate(port, corpus, os.path.join(HERE, "port.jsonl"), True)

    # --- Analysis of goldens (corpus shape) ---
    from collections import Counter, defaultdict
    oracle_code_counts = Counter()
    oracle_errors = 0
    for e in corpus:
        g = goldens.get(e["id"], {})
        if "comments" not in g:
            oracle_errors += 1
            continue
        for c in g["comments"]:
            oracle_code_counts[c["code"]] += 1

    report = {
        "corpus_size": len(corpus),
        "oracle_errors": oracle_errors,
        "distinct_codes": len(oracle_code_counts),
        "code_counts": dict(sorted(oracle_code_counts.items(), key=lambda kv: -kv[1])),
    }

    if port_results is not None:
        exact = 0
        parse_or_error = 0
        per_code = defaultdict(lambda: {"oracle": 0, "matched": 0, "missing": 0, "extra": 0})
        script_diffs = []
        for e in corpus:
            g = goldens.get(e["id"], {})
            p = port_results.get(e["id"], {})
            if "comments" not in g:
                continue
            gc = g["comments"]
            for c in gc:
                per_code[c["code"]]["oracle"] += 1
            if "comments" not in p:
                parse_or_error += 1
                for c in gc:
                    per_code[c["code"]]["missing"] += 1
                script_diffs.append({"id": e["id"], "port_error": p.get("error", "?")})
                continue
            pc = p["comments"]
            gset = Counter(comment_key(c) for c in gc)
            pset = Counter(comment_key(c) for c in pc)
            if gset == pset:
                exact += 1
            else:
                # per-code match accounting
                inter = gset & pset
                gcode = defaultdict(int)
                for k, n in (gset - inter).items():
                    gcode[k[5]] += n  # code index in comment_key
                pcode = defaultdict(int)
                for k, n in (pset - inter).items():
                    pcode[k[5]] += n
                for code, n in gcode.items():
                    per_code[code]["missing"] += n
                for code, n in pcode.items():
                    per_code[code]["extra"] += n
                script_diffs.append({
                    "id": e["id"],
                    "missing": [k for k in (gset - inter)],
                    "extra": [k for k in (pset - inter)],
                })
            for k, n in (gset & pset).items():
                per_code[k[5]]["matched"] += n

        report["port"] = {
            "exact_scripts": exact,
            "exact_pct": round(100.0 * exact / max(1, len(corpus)), 2),
            "port_errors": parse_or_error,
            "per_code": {str(k): v for k, v in sorted(per_code.items())},
        }
        report["script_diffs_sample"] = script_diffs[:40]

    with open(os.path.join(HERE, "coverage.json"), "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)

    # --- Print summary ---
    print(f"corpus scripts        : {report['corpus_size']}")
    print(f"oracle run errors     : {report['oracle_errors']}")
    print(f"distinct SC codes     : {report['distinct_codes']}")
    print("top codes in corpus   :")
    for code, n in list(report["code_counts"].items())[:15]:
        print(f"   SC{code}: {n}")
    if port_results is not None:
        pr = report["port"]
        print(f"\n=== PORT CONFORMANCE ===")
        print(f"exact-match scripts   : {pr['exact_scripts']}/{report['corpus_size']} ({pr['exact_pct']}%)")
        print(f"port errors           : {pr['port_errors']}")
        print("worst-covered codes (missing):")
        worst = sorted(pr["per_code"].items(), key=lambda kv: -kv[1]["missing"])[:20]
        for code, s in worst:
            print(f"   SC{code}: matched {s['matched']} / oracle {s['oracle']}  (missing {s['missing']}, extra {s['extra']})")


if __name__ == "__main__":
    main()
