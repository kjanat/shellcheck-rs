#!/usr/bin/env bash
# Deterministic instruction counts for the h2r-rt hot paths (callgrind Ir).
#
#   scripts/rt-instrs.sh [scenario...]
#
# Builds crates/h2r-rt/examples/ops.rs in release mode, then for every
# scenario runs it under callgrind twice: with n = 0 (process start-up and
# setup) and with the scenario's n. Prints `scenario  n  Ir/op` with
# Ir/op = (Ir_n - Ir_0) / n, integer division. Instruction counts do not
# depend on machine load, so two runs agree to well under 0.1 %.
# No argument runs every scenario. CARGO_TARGET_DIR is respected.
set -euo pipefail

# scenario:n, n chosen so one callgrind run takes a few seconds
scenarios=(
	"thunk-chain:100000"
	"thunk-each:100000"
	"apply:100000"
	"apply-partial:100000"
	"cons:10000"
	"match:1000000"
	"deferred-data:1000000"
)

command -v valgrind >/dev/null || {
	echo "rt-instrs: valgrind is required" >&2
	exit 1
}

# Resolve a relative CARGO_TARGET_DIR against the caller's directory.
if [ -n "${CARGO_TARGET_DIR:-}" ]; then
	CARGO_TARGET_DIR=$(realpath -m "$CARGO_TARGET_DIR")
	export CARGO_TARGET_DIR
fi
cd "$(dirname "$0")/.."
target=${CARGO_TARGET_DIR:-$PWD/target}

cargo build --release -p h2r-rt --example ops >&2
bin=$target/release/examples/ops
[ -x "$bin" ] || {
	echo "rt-instrs: $bin was not built" >&2
	exit 1
}

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Total instructions (callgrind's "Collected" line) of `ops <scenario> <n>`.
instructions() {
	local log
	log=$(valgrind --tool=callgrind --callgrind-out-file="$work/callgrind.out" \
		"$bin" "$1" "$2" 2>&1 >/dev/null) || {
		printf '%s\n' "$log" >&2
		echo "rt-instrs: ops $1 $2 failed under callgrind" >&2
		return 1
	}
	local total
	total=$(printf '%s\n' "$log" | sed -n 's/^==[0-9]*== Collected *: *\([0-9]*\).*/\1/p')
	[ -n "$total" ] || {
		printf '%s\n' "$log" >&2
		echo "rt-instrs: no 'Collected' line in callgrind output" >&2
		return 1
	}
	echo "$total"
}

known() {
	local entry
	for entry in "${scenarios[@]}"; do
		if [ "${entry%%:*}" = "$1" ]; then return 0; fi
	done
	return 1
}

selected=("$@")
if [ ${#selected[@]} -eq 0 ]; then
	for entry in "${scenarios[@]}"; do selected+=("${entry%%:*}"); done
fi
for name in "${selected[@]}"; do
	known "$name" || {
		echo "rt-instrs: unknown scenario '$name'" >&2
		exit 2
	}
done

printf '%-14s %8s %8s\n' scenario n Ir/op
for name in "${selected[@]}"; do
	for entry in "${scenarios[@]}"; do
		if [ "${entry%%:*}" = "$name" ]; then n=${entry##*:}; fi
	done
	base=$(instructions "$name" 0)
	full=$(instructions "$name" "$n")
	printf '%-14s %8d %8d\n' "$name" "$n" $(((full - base) / n))
done
