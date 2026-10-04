#!/usr/bin/env bash
# Build the hand-written Rust port's CLI from the `rust-port` branch.
# Called by bench/build.sh with BENCH_SRC (checkout), BENCH_OUT, BENCH_TARGET.
set -euo pipefail

CARGO_TARGET_DIR="${BENCH_TARGET}"

export CARGO_TARGET_DIR

# Built from the bench checkout with the rust toolchain in mise.toml;
# the branch's own mise.toml also lists GHC and Python for its conformance suite,
# which the CLI does not need.
cargo build --release --locked --manifest-path "${BENCH_SRC}/Cargo.toml" -p shellcheck-cli --bin rshellcheck
install -m 755 "${BENCH_TARGET}/release/rshellcheck" "${BENCH_OUT}/shellcheck"
{
	rustc --version
	cargo --version
} >"${BENCH_OUT}/toolchain.txt"
