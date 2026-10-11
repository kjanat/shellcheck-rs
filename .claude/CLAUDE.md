# Rust port development

This repository ships Rust, with Go, Python and JavaScript WASM bindings.
Haskell reference source is fetched into an ignored cache; do not vendor it.

- Build: `cargo build --release --locked`.
- Unit tests: `cargo test --workspace --locked --lib --bins`.
- Behavior snapshots: `cargo conformance-snapshot` (offline, no oracle).
- Formatting: `dprint fmt`; lint: `cargo lint`.
- Oracle: `python tools/oracle.py` (requires GHC, Cabal and gh).
- Conformance: `cargo conformance-gate` and `cargo conformance-fuzz`.

See UPSTREAM.md for the exact upstream revision, frozen corpus provenance and
intentional SC2164 difference. Keep rust/snapshot.txt unchanged unless behavior
changes are intentional. Preserve Rust regression tests when updating upstream.
