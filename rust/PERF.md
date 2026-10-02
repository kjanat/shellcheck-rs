# Performance notes for the Rust port

Measured facts, the fast loops, and the work packages, in that order. Numbers are from this container (slower than CI by about 2.4×); compare ratios, not absolutes.

## Where the time goes (measured, `5d3fe06`)

Benchmark corpus `.bench/corpus` (seed 20260928), GHC ShellCheck 0.11.0 as the oracle.

| script | lines |  oracle |      port | port peak RSS | oracle peak RSS |
| ------ | ----: | ------: | --------: | ------------: | --------------: |
| small  |   170 | ~0.08 s |    0.07 s |        42 MiB |        ~120 MiB |
| medium | 1 632 |  1.31 s | 1.9–6.6 s |     1 374 MiB |         251 MiB |
| large  | 4 337 |  10.4 s | 12.7–50 s |     8 731 MiB |       1 203 MiB |

The spread in the port's wall time is page-fault time on the 1.4–8.7 GiB heap; the in-process number (`conformance bench`) is the lower figure. Per phase (`conformance bench --input`):

| phase        |              medium |                large | growth for 2.66× lines |
| ------------ | ------------------: | -------------------: | ---------------------: |
| parse        |               32 ms |                79 ms |                   2.5× |
| maps         |                3 ms |                 7 ms |                   2.6× |
| **cfg**      | **1 586 ms (85 %)** | **11 503 ms (90 %)** |   **7.3× (quadratic)** |
| params-other |              107 ms |               476 ms |                   4.4× |
| checks       |               70 ms |               355 ms |                   5.1× |
| resolve      |               64 ms |               310 ms |                   4.8× |

Callgrind on medium (9.67 G instructions): `analyze_control_flow` 87 %; inside it `BTreeMap::clone` ~45 %, `InternalState::clone` 23 %, drop glue 19 %, malloc+free 57 %, `internal_to_external` 13 %, `patch_state` 11 %. Massif peak 1.43 GB: 38 % is clones of `BTreeMap<String, VariableState>` whose values hold `BTreeSet<BTreeSet<CFVariableProp>>`.

**Root cause.** `cfg_analysis::VMap<V>` is a `BTreeMap<String, V>` cloned on every state copy, and `Ctx::process` copies the state about six times per CFG node (`states.get(c).map(|x| x.1.clone())` per predecessor, `input.clone()` twice, `output.clone()`, `states.get(&node).cloned()`, `result.clone()`), while `StateMap` keeps two full states per node and `internal_to_external` rebuilds a flat map per node at the end. The Haskell original does the same operations on `Data.Map`, which shares structure, so there it is O(nodes · log vars) in time and memory; here it is O(nodes · vars): quadratic in the script.

## Invariants

1. **Output parity.** `conformance gate --oracle <ghc shellcheck>` must report 0 divergences; `conformance fuzz --seed 0 --iterations 2000` likewise; `-f gcc` and `-f json1` output on the corpus scripts byte-identical to the oracle. `PARITY-NOTES.md` lists the upstream quirks reproduced on purpose; `DIVERGENCES.md` the open ones (none).
2. **The CFG analysis is a port of `CFGAnalysis.hs`**: keep its structure (versions, cache, invocation paths, merge/patch semantics, iteration order of maps where it is observable) so the fuzzer keeps agreeing; change representations, not the algorithm.
3. **Snapshot.** `cargo conformance-snapshot` (see `mise.toml`) must still pass or be regenerated with a reason.

## Fast loops

```sh
# 23 s: unit tests (1 517)
cargo test -p shellcheck-rs
# 4 min: release build of the CLI and the harness (thin LTO)
cargo build --release -p shellcheck-cli -p conformance
# 10 s: the oracle gate (0 divergences required)
target/release/conformance gate --oracle "$ORACLE" --quiet
# 1–3 min: the fuzzer (0 divergences required)
target/release/conformance fuzz --oracle "$ORACLE" --seed 0 --iterations 2000
# seconds: per-phase timing of the port against the oracle, per script
target/release/conformance bench --input .bench/corpus/medium.sh --oracle "$ORACLE"
# peak RSS of one run (ru_maxrss via wait4)
python3 - <<'PY'
import os, subprocess, sys
p = subprocess.Popen([sys.argv[1], "-f", "gcc", sys.argv[2]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
_, st, ru = os.wait4(p.pid, 0); print(ru.ru_maxrss // 1024, "MiB")
PY
```

`ORACLE` in this container: `.bench/target/h2r/h2r/hs-shellcheck/build/dist-newstyle/build/x86_64-linux/ghc-9.6.7/ShellCheck-0.11.0/x/shellcheck/build/shellcheck/shellcheck`. Clippy (`-D warnings`), `cargo fmt --check`, `dprint check` as elsewhere.

## Work packages

### WP-R1 Structural sharing in the CFG analysis state

Replace `VMap<V>`'s storage with a persistent map (`im-rc`'s `OrdMap<Rc<str>, V>`, or an in-crate persistent balanced tree if the crate cannot be used) so that cloning a state is O(1), inserting is O(log n) with path copying, and unchanged entries (including the `BTreeSet<BTreeSet<CFVariableProp>>` values) are shared between the states of different nodes. Keep `version` semantics, `vm_eq` (fast path by version, slow path by contents), ordered iteration, and the left-biased unions in `patch_state`/`merge_state`/`internal_to_external`. Make `internal_to_external` cheap: `ProgramState.variables_in_scope` should not be a freshly built `BTreeMap` per node for all nodes; either store the shared maps and resolve by scope precedence on lookup (prefix > local > global, literal value censored at access), or convert lazily in `get_incoming_state`/`get_outgoing_state` for the nodes the checks actually ask about (six call sites). Keep `Ctx::process` as it is except that the clones are now cheap; if a copy is still O(vars) after the change (`patch_state` building a new map by inserting every key, the `grouped`/`flattenByNode` loops), rewrite it as a map union with the same bias.

Acceptance: `cargo test -p shellcheck-rs` all pass; gate 0 divergences; fuzz seed 0 ×2000 and seed 1013 ×2000 0 divergences; snapshot passes; `conformance bench --input medium.sh`: cfg ≤ 250 ms (from 1 586); large: cfg ≤ 1.5 s (from 11 503); peak RSS medium ≤ 300 MiB (from 1 374), large ≤ 1.5 GiB (from 8 731); the `-f gcc`/`-f json1` outputs on all four corpus scripts byte-identical to the oracle. Report the before/after phase tables and the RSS.

### Candidates after WP-R1 (measure first)

- `params-other` (variable flow, 476 ms on large, growing 4.4× for 2.66× lines) and `checks`/`resolve` (5×): find the quadratic piece in each with `conformance bench` and callgrind once cfg no longer dominates.
- `startup` 4.2 ms vs the oracle's 3.0 ms on CI: what the CLI does before `check_script` (rc file search, clap, locale).
