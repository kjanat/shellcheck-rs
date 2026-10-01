#!/usr/bin/env bash
# A/B a compiled ShellCheck against a baseline binary and the GHC oracle.
#
#   scripts/perf-ab.sh <baseline-binary> <candidate-binary> <script>...
#
# For every script: the candidate's stdout, stderr and exit status must equal
# the oracle's in gcc and json1 format (a faster program that prints something
# else is not faster ShellCheck). Then hyperfine -N times both binaries on
# each script, and peak RSS is read from wait4 for one run each.
#
# The oracle is the GHC-built shellcheck the hs-shellcheck layer produced
# (H2R_ORACLE overrides). Runs: 10 timed per script after 2 warm-ups;
# H2R_RUNS / H2R_WARMUP override. Nothing else should run on the machine.
set -euo pipefail

[ $# -ge 3 ] || {
	sed -n '2,13p' "$0"
	exit 2
}
baseline=$(realpath "$1")
candidate=$(realpath "$2")
shift 2
runs=${H2R_RUNS:-10}
warmup=${H2R_WARMUP:-2}
target=${CARGO_TARGET_DIR:-target}
oracle=${H2R_ORACLE:-$(find "$target/h2r/hs-shellcheck/build" -type f -perm -u+x -path '*/x/shellcheck/build/shellcheck/shellcheck' 2>/dev/null | head -1)}
[ -x "${oracle:-}" ] || {
	echo "perf-ab: no GHC oracle found under $target/h2r/hs-shellcheck/build; set H2R_ORACLE" >&2
	exit 1
}
command -v hyperfine >/dev/null || {
	echo "perf-ab: hyperfine is required" >&2
	exit 1
}

echo "oracle:    $oracle"
echo "baseline:  $baseline"
echo "candidate: $candidate"
echo
echo "== parity (candidate vs oracle) =="
status=0
for script in "$@"; do
	for fmt in gcc json1; do
		a=$(
			"$oracle" -f "$fmt" "$script" 2>&1
			echo "exit $?"
		) || true
		b=$(
			"$candidate" -f "$fmt" "$script" 2>&1
			echo "exit $?"
		) || true
		if [ "$a" = "$b" ]; then verdict=same; else
			verdict=DIFFERENT
			status=1
		fi
		printf '  %-40s %-6s %s\n' "$script" "$fmt" "$verdict"
	done
done
[ $status -eq 0 ] || {
	echo "perf-ab: output differs from the oracle; timing a wrong program is pointless" >&2
	exit 1
}

echo
echo "== time (hyperfine -N, $runs runs, $warmup warm-up) =="
for script in "$@"; do
	hyperfine -N --warmup "$warmup" --runs "$runs" --ignore-failure --style basic \
		-n "baseline  $script" "$baseline -f gcc $script" \
		-n "candidate $script" "$candidate -f gcc $script" 2>&1 | grep -E 'Time \(|faster|slower' | grep -v Warning
done

echo
echo "== peak RSS (one run each, -f gcc) =="
for script in "$@"; do
	for bin in "$baseline" "$candidate"; do
		python3 - "$bin" "$script" <<'PY'
import os, subprocess, sys
p = subprocess.Popen([sys.argv[1], "-f", "gcc", sys.argv[2]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
_, _, ru = os.wait4(p.pid, 0)
print(f"  {sys.argv[2]:40s} {sys.argv[1]}: {ru.ru_maxrss / 1024:.0f} MiB")
PY
	done
done
