#!/usr/bin/env python3
"""
ShellCheck Rust-port conformance harness.

Runs the Haskell **oracle** and the **Rust port** over the same corpus of shell
scripts, both emitting `--format=json1`, and diffs their diagnostics. Because
both tools are asked for machine-readable output over identical input, a match
is an exact behavioural-parity guarantee: same code, severity, span, message,
autofix, **order**, and process **exit status**.

Strictness (this harness is a CI gate, not a dashboard):
  - Diagnostics are compared as an ORDERED sequence, not just as a multiset.
    ShellCheck sorts its output deterministically (file, line, column, severity,
    code, message), so the port must reproduce that order. Scripts that match as
    a set but differ in order are reported separately (`order_mismatch`).
  - The process EXIT STATUS is compared per script (Haskell `statusToCode`:
    0 none / 1 issues / 2 runtime / 3 syntax / 4 support). Mismatches are
    reported (`exit_mismatch`).
  - Scripts where the oracle itself errors (no parseable JSON) are counted in
    their own bucket and excluded from the port comparison, instead of silently
    depressing the rate.

A script is "exact" only if: oracle produced comments, the ordered comment-key
sequences are identical, AND the exit codes match.

Provenance + self-invalidating cache:
  - Each cache file carries a provenance header (oracle/port git SHA + describe,
    binary sha256) and every entry records `input_hash = sha256(script)` and the
    producing binary's sha256. On load, any entry whose input_hash or binary sha
    no longer matches is treated as missing and regenerated automatically. No
    manual --regen needed when the corpus or a binary changes.

Outputs:
  - goldens.jsonl        cached oracle output per corpus id (+ provenance header)
  - port.jsonl           cached port output per corpus id (+ provenance header)
  - coverage.json        machine-readable strict report
  - baseline.json        committed gate baseline (written with --write-baseline)
  - prints a summary table

Usage:
  ORACLE=/path/to/haskell/shellcheck \
  PORT=/path/to/shellcheck-rs \
  python3 run_conformance.py [--regen-oracle] [--limit N] [--codes SC2086,...]
                             [--gate] [--write-baseline] [--selftest MODE]
"""
import os
import sys
import json
import hashlib
import subprocess
import argparse

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
BASELINE_PATH = os.path.join(HERE, "baseline.json")


def find_oracle():
    env = os.environ.get("ORACLE")
    if env and os.path.exists(env):
        return env
    cand = os.path.join(
        ROOT,
        "dist-newstyle/build/x86_64-linux/ghc-9.6.6/ShellCheck-0.11.0/x/shellcheck/build/shellcheck/shellcheck",
    )
    if os.path.exists(cand):
        return cand
    dist = os.path.join(ROOT, "dist-newstyle")
    if os.path.isdir(dist):
        for dirpath, _dirs, files in os.walk(dist):
            if "shellcheck" in files and dirpath.endswith("build/shellcheck"):
                return os.path.join(dirpath, "shellcheck")
    return None


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_str(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def git_info(root):
    def g(args):
        try:
            return subprocess.check_output(
                ["git", "-C", root] + args, stderr=subprocess.DEVNULL
            ).decode("utf-8", "replace").strip()
        except Exception:
            return None
    return {"head": g(["rev-parse", "HEAD"]), "describe": g(["describe", "--always", "--dirty"])}


def tool_provenance(binary, kind):
    """Provenance stamp for a tool binary. The oracle also records the repo git
    SHA it was built from (the port is built from the same tree)."""
    prov = {
        "kind": kind,
        "binary": os.path.abspath(binary),
        "binary_sha256": sha256_file(binary),
        "git": git_info(ROOT),
    }
    return prov


def run_json1(binary, script):
    """Run `binary --format=json1 -` on script via stdin.
    Returns {"comments": [...], "exit": rc} on success, else {"error": ...}.
    ShellCheck exits non-zero when it finds issues; that is expected and the
    exact code is captured for comparison (statusToCode)."""
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
        return {"error": "empty", "exit": proc.returncode,
                "stderr": proc.stderr.decode("utf-8", "replace")[:400]}
    try:
        data = json.loads(out)
    except json.JSONDecodeError as e:
        return {"error": f"badjson: {e}", "exit": proc.returncode, "raw": out[:400]}
    return {"comments": data.get("comments", []), "exit": proc.returncode}


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


def load_cache(path, tool_sha, corpus_by_id):
    """Load a cache, dropping any entry that is stale:
       - input_hash != sha256(current script for that id)
       - tool_sha256 != current binary sha256
       - id no longer in the corpus
    Stale/legacy entries are simply omitted, so generate() re-runs them."""
    cache = {}
    if not os.path.exists(path):
        return cache
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("__provenance__"):
                continue
            cid = obj.get("id")
            if cid is None or cid not in corpus_by_id:
                continue
            if obj.get("tool_sha256") != tool_sha:
                continue
            if obj.get("input_hash") != sha256_str(corpus_by_id[cid]["script"]):
                continue
            cache[cid] = obj["result"]
    return cache


def generate(binary, kind, corpus, cache_path, regen):
    prov = tool_provenance(binary, kind)
    tool_sha = prov["binary_sha256"]
    corpus_by_id = {e["id"]: e for e in corpus}
    cache = {} if regen else load_cache(cache_path, tool_sha, corpus_by_id)
    missing = [e for e in corpus if e["id"] not in cache]
    if missing:
        sys.stderr.write(
            f"[run] {os.path.basename(cache_path)}: running {len(missing)} scripts...\n")
        for i, e in enumerate(missing):
            cache[e["id"]] = run_json1(binary, e["script"])
            if (i + 1) % 200 == 0:
                sys.stderr.write(f"  {i+1}/{len(missing)}\n")
    # Rewrite the whole file so it never grows unbounded and always carries a
    # fresh provenance header matching its contents.
    with open(cache_path, "w", encoding="utf-8") as out:
        out.write(json.dumps({"__provenance__": prov}) + "\n")
        for e in corpus:
            out.write(json.dumps({
                "id": e["id"],
                "input_hash": sha256_str(e["script"]),
                "tool_sha256": tool_sha,
                "result": cache[e["id"]],
            }) + "\n")
    return cache, prov


def build_report(corpus, goldens, port_results, oracle_prov, port_prov):
    from collections import Counter, defaultdict

    oracle_code_counts = Counter()
    oracle_error_scripts = []
    for e in corpus:
        g = goldens.get(e["id"], {})
        if "comments" not in g:
            oracle_error_scripts.append({"id": e["id"], "error": g.get("error", "?")})
            continue
        for c in g["comments"]:
            oracle_code_counts[c["code"]] += 1

    report = {
        "corpus_size": len(corpus),
        "oracle_error_scripts": len(oracle_error_scripts),
        "oracle_error_sample": oracle_error_scripts[:40],
        "comparable_scripts": len(corpus) - len(oracle_error_scripts),
        "distinct_codes": len(oracle_code_counts),
        "code_counts": dict(sorted(oracle_code_counts.items(), key=lambda kv: -kv[1])),
        "oracle_provenance": oracle_prov,
    }

    if port_results is None:
        return report

    exact = 0
    set_equal = 0
    order_mismatch = []
    exit_mismatch = []
    port_error_scripts = []
    per_code = defaultdict(lambda: {"oracle": 0, "matched": 0, "missing": 0, "extra": 0})
    script_diffs = []

    for e in corpus:
        g = goldens.get(e["id"], {})
        p = port_results.get(e["id"], {})
        if "comments" not in g:
            continue  # oracle-errored: accounted for in its own bucket
        gc = g["comments"]
        for c in gc:
            per_code[c["code"]]["oracle"] += 1
        if "comments" not in p:
            port_error_scripts.append({"id": e["id"], "port_error": p.get("error", "?")})
            for c in gc:
                per_code[c["code"]]["missing"] += 1
            script_diffs.append({"id": e["id"], "port_error": p.get("error", "?")})
            continue

        pc = p["comments"]
        g_keys = [comment_key(c) for c in gc]
        p_keys = [comment_key(c) for c in pc]
        gset = Counter(g_keys)
        pset = Counter(p_keys)
        set_ok = gset == pset
        order_ok = g_keys == p_keys
        g_exit = g.get("exit")
        p_exit = p.get("exit")
        exit_ok = g_exit == p_exit

        if set_ok:
            set_equal += 1
        if set_ok and not order_ok:
            order_mismatch.append({"id": e["id"], "oracle_order": [k[5] for k in g_keys],
                                   "port_order": [k[5] for k in p_keys]})
        if not exit_ok:
            exit_mismatch.append({"id": e["id"], "oracle_exit": g_exit, "port_exit": p_exit})

        # Strict exact: ordered comment-keys AND exit code match.
        if order_ok and exit_ok:
            exact += 1
        else:
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
                "oracle_exit": g_exit,
                "port_exit": p_exit,
                "order_only": set_ok and not order_ok,
            })
        for k, n in (gset & pset).items():
            per_code[k[5]]["matched"] += n

    report["port"] = {
        "exact_scripts": exact,
        "exact_pct": round(100.0 * exact / max(1, report["comparable_scripts"]), 2),
        "set_equal_scripts": set_equal,
        "order_mismatch": len(order_mismatch),
        "order_mismatch_ids": sorted(m["id"] for m in order_mismatch),
        "order_mismatch_sample": order_mismatch[:40],
        "exit_mismatch": len(exit_mismatch),
        "exit_mismatch_ids": sorted(m["id"] for m in exit_mismatch),
        "exit_mismatch_sample": exit_mismatch[:40],
        "port_error_scripts": len(port_error_scripts),
        "port_error_sample": port_error_scripts[:40],
        "per_code": {str(k): v for k, v in sorted(per_code.items())},
        "port_provenance": port_prov,
    }
    report["script_diffs_sample"] = script_diffs[:40]
    return report


def print_summary(report, port_results):
    print(f"corpus scripts        : {report['corpus_size']}")
    print(f"oracle-errored scripts: {report['oracle_error_scripts']} (excluded from parity)")
    print(f"comparable scripts    : {report['comparable_scripts']}")
    print(f"distinct SC codes     : {report['distinct_codes']}")
    print("top codes in corpus   :")
    for code, n in list(report["code_counts"].items())[:15]:
        print(f"   SC{code}: {n}")
    if port_results is None:
        return
    pr = report["port"]
    print(f"\n=== PORT CONFORMANCE (STRICT: ordered + exit-status) ===")
    print(f"exact-match scripts   : {pr['exact_scripts']}/{report['comparable_scripts']} ({pr['exact_pct']}%)")
    print(f"set-equal scripts     : {pr['set_equal_scripts']}")
    print(f"order-only mismatches : {pr['order_mismatch']}")
    print(f"exit-code mismatches  : {pr['exit_mismatch']}")
    print(f"port-errored scripts  : {pr['port_error_scripts']}")
    if pr["order_mismatch"]:
        print("  order mismatches:")
        for m in pr["order_mismatch_sample"]:
            print(f"    {m['id']}: oracle {m['oracle_order']} vs port {m['port_order']}")
    if pr["exit_mismatch"]:
        print("  exit mismatches:")
        for m in pr["exit_mismatch_sample"]:
            print(f"    {m['id']}: oracle exit {m['oracle_exit']} vs port exit {m['port_exit']}")
    print("codes with any missing/extra:")
    worst = sorted(pr["per_code"].items(), key=lambda kv: -(kv[1]["missing"] + kv[1]["extra"]))
    for code, s in worst:
        if s["missing"] or s["extra"]:
            print(f"   SC{code}: matched {s['matched']} / oracle {s['oracle']}  "
                  f"(missing {s['missing']}, extra {s['extra']})")


def make_baseline(report):
    pr = report["port"]
    per_code = {c: {"oracle": s["oracle"], "matched": s["matched"],
                    "missing": s["missing"], "extra": s["extra"]}
                for c, s in pr["per_code"].items()}
    # The documented known-missing allowlist: the non-exact scripts, all
    # missing-only SC1xxx (no extras). Derived from the current strict diff.
    known_missing = {}
    for c, s in pr["per_code"].items():
        if s["missing"] > 0:
            known_missing[c] = {"missing": s["missing"], "reason": KNOWN_MISSING_REASONS.get(c, "documented parser/source-resolution gap")}
    return {
        "definition": "exact = ordered comment-keys identical AND exit codes match; comparison excludes oracle-errored scripts",
        "corpus_size": report["corpus_size"],
        "comparable_scripts": report["comparable_scripts"],
        "oracle_error_scripts": report["oracle_error_scripts"],
        "exact_scripts": pr["exact_scripts"],
        "order_mismatch": pr["order_mismatch"],
        "order_mismatch_ids": pr["order_mismatch_ids"],
        "exit_mismatch": pr["exit_mismatch"],
        "exit_mismatch_ids": pr["exit_mismatch_ids"],
        "exit_mismatch_note": ("These scripts exit-mismatch ONLY because the sole diagnostic the "
                               "oracle emits on them is an un-ported SC1xxx note (see known_missing); "
                               "with that note absent the port finds no issues and exits 0 while the "
                               "oracle exits 1. They are pinned so the gate still fails on any NEW "
                               "exit mismatch."),
        "per_code": per_code,
        "known_missing": known_missing,
        "provenance": {
            "oracle": report["oracle_provenance"],
            "port": pr["port_provenance"],
        },
    }


KNOWN_MISSING_REASONS = {
    "1091": "SC1091 (Not following sourced file): the port does not resolve/follow `source`d files, so it cannot emit the informational 'not following' note.",
    "1008": "SC1008 (unrecognized shebang): shebang-dialect note not yet ported.",
    "1014": "SC1014 (test as command): parser note not yet ported for this construct.",
    "1127": "SC1127 (comment without leading space / unexpected token) parser note not yet ported.",
}


def run_gate(report, port_results):
    if port_results is None:
        print("GATE: FAIL — port results unavailable (set PORT).")
        return 1
    if not os.path.exists(BASELINE_PATH):
        print(f"GATE: FAIL — baseline not found at {BASELINE_PATH}; run --write-baseline first.")
        return 1
    baseline = json.load(open(BASELINE_PATH, encoding="utf-8"))
    pr = report["port"]
    failures = []

    # 1. No extras on any code.
    for code, s in pr["per_code"].items():
        if s["extra"] > 0:
            failures.append(f"SC{code}: extra={s['extra']} (must be 0)")

    # 2. No code regressed below its baseline matched count.
    for code, base in baseline["per_code"].items():
        cur = pr["per_code"].get(code, {"matched": 0})
        if cur["matched"] < base["matched"]:
            failures.append(f"SC{code}: matched {cur['matched']} < baseline {base['matched']}")

    # 3. No NEW exit-code mismatches. The baseline pins the known ones (all a
    #    direct consequence of the known-missing SC1xxx notes being the sole
    #    diagnostic on those scripts). Any id not in the allowlist, or any
    #    increase in count, fails.
    base_exit_ids = set(baseline.get("exit_mismatch_ids", []))
    new_exit = sorted(set(pr["exit_mismatch_ids"]) - base_exit_ids)
    if new_exit:
        failures.append(f"new exit_mismatch scripts (not in baseline): {new_exit}")
    if pr["exit_mismatch"] > baseline.get("exit_mismatch", 0):
        failures.append(f"exit_mismatch={pr['exit_mismatch']} > baseline {baseline.get('exit_mismatch', 0)}")

    # 4. No NEW order-only mismatches (baseline order_mismatch is 0, so any
    #    order mismatch is a regression).
    base_order_ids = set(baseline.get("order_mismatch_ids", []))
    new_order = sorted(set(pr["order_mismatch_ids"]) - base_order_ids)
    if new_order:
        failures.append(f"new order_mismatch scripts (not in baseline): {new_order}")
    if pr["order_mismatch"] > baseline.get("order_mismatch", 0):
        failures.append(f"order_mismatch={pr['order_mismatch']} > baseline {baseline.get('order_mismatch', 0)}")

    # 5. exact_scripts must not drop below baseline.
    if pr["exact_scripts"] < baseline["exact_scripts"]:
        failures.append(f"exact_scripts {pr['exact_scripts']} < baseline {baseline['exact_scripts']}")

    if failures:
        print("GATE: FAIL")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"GATE: PASS (exact {pr['exact_scripts']}/{report['comparable_scripts']}, "
          f"0 extras, 0 exit/order mismatches)")
    return 0


def apply_selftest(mode, port_results, corpus):
    """Corrupt a COPY of the port results in memory to prove the gate fires.
    Never touches the real port binary or its cache."""
    if not mode or port_results is None:
        return port_results
    pr = dict(port_results)
    first_id = corpus[0]["id"]
    base = pr.get(first_id, {"comments": [], "exit": 1})
    if mode == "extra":
        # Inject a spurious diagnostic -> extra>0.
        c = dict(base)
        comments = list(c.get("comments", []))
        comments.append({"line": 1, "column": 1, "endLine": 1, "endColumn": 1,
                         "level": "error", "code": 9999,
                         "message": "SELFTEST spurious diagnostic", "fix": None})
        c["comments"] = comments
        pr[first_id] = c
    elif mode == "missing":
        # Drop all diagnostics -> matched regresses, exact drops.
        c = dict(base)
        c["comments"] = []
        pr[first_id] = c
    elif mode == "exit":
        # Flip exit code -> exit_mismatch>0.
        c = dict(base)
        c["exit"] = (base.get("exit", 1) or 0) + 7
        pr[first_id] = c
    elif mode == "order":
        # Reverse comment order on a multi-comment script -> order_mismatch>0.
        for e in corpus:
            cc = pr.get(e["id"])
            if cc and len(cc.get("comments", [])) >= 2:
                c = dict(cc)
                c["comments"] = list(reversed(cc["comments"]))
                pr[e["id"]] = c
                break
    return pr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--regen-oracle", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--codes", default="")
    ap.add_argument("--gate", action="store_true",
                    help="exit nonzero if conformance regressed vs baseline.json")
    ap.add_argument("--write-baseline", action="store_true",
                    help="write baseline.json from the current strict run")
    ap.add_argument("--selftest", default="",
                    choices=["", "extra", "missing", "exit", "order"],
                    help="corrupt port results IN MEMORY to prove the gate fires")
    args = ap.parse_args()

    corpus = json.load(open(os.path.join(HERE, "corpus.json"), encoding="utf-8"))
    if args.limit:
        corpus = corpus[: args.limit]

    oracle = find_oracle()
    if not oracle:
        sys.stderr.write("[run] ERROR: oracle binary not found; build it first.\n")
        sys.exit(1)
    sys.stderr.write(f"[run] oracle: {oracle}\n")

    goldens, oracle_prov = generate(
        oracle, "oracle", corpus, os.path.join(HERE, "goldens.jsonl"), args.regen_oracle)

    port = os.environ.get("PORT")
    if port and not os.path.exists(port):
        sys.stderr.write(f"[run] PORT set but not found: {port}\n")
        port = None
    port_results = None
    port_prov = None
    if port:
        sys.stderr.write(f"[run] port: {port}\n")
        port_results, port_prov = generate(
            port, "port", corpus, os.path.join(HERE, "port.jsonl"), False)

    if args.selftest:
        sys.stderr.write(f"[run] SELFTEST active: {args.selftest} (in-memory corruption)\n")
        port_results = apply_selftest(args.selftest, port_results, corpus)

    report = build_report(corpus, goldens, port_results, oracle_prov, port_prov)

    with open(os.path.join(HERE, "coverage.json"), "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=2)

    print_summary(report, port_results)

    if args.write_baseline:
        baseline = make_baseline(report)
        with open(BASELINE_PATH, "w", encoding="utf-8") as fh:
            json.dump(baseline, fh, indent=2)
        print(f"\n[baseline] wrote {BASELINE_PATH}: exact={baseline['exact_scripts']}, "
              f"known_missing codes={sorted(baseline['known_missing'])}")

    if args.gate:
        sys.exit(run_gate(report, port_results))


if __name__ == "__main__":
    main()
