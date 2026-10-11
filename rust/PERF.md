# Performance notes for the Rust port

Measured facts, the fast loops, and the work packages, in that order. Each measurement section names its baseline and method; compare within a section rather than across machines.

## 2026-10-11: bounded workers, shared snapshots and fewer parser allocations

Compared with our own release binary at [3ad86e18](https://github.com/kjanat/shellcheck-rs/commit/3ad86e183c3662a142cff5909a9d03b1498daaab). Five shuffled before/after runs per workload, one warm-up per binary, pinned to CPU 0; full analysis with `--norc`. Times are medians, with no confidence intervals or significance claim. Every measured output and exit status agrees with the baseline. Omarchy is pinned to [077ac1da939d](https://github.com/omacom/omarchy/commit/077ac1da939de00d061c1035e1a1d00587a119b8): **1,228 shell files, 119,468 lines**.

| Workload                      |    Before |     After | Before / after | Peak RSS before → after |
| ----------------------------- | --------: | --------: | -------------: | ----------------------: |
| **Ordinary scripts**          |           |           |                |                         |
| 2-line script                 |   2.28 ms |   2.32 ms |          0.98× |           6.2 → 6.1 MiB |
| 170-line script               |  10.41 ms |  10.02 ms |          1.04× |           9.1 → 9.2 MiB |
| 1,632-line script             | 115.34 ms | 102.50 ms |          1.13× |         42.9 → 41.4 MiB |
| 4,337-line script             | 277.60 ms | 281.35 ms |          0.99× |        100.8 → 97.9 MiB |
| 120 scripts / 9,107 lines     | 289.99 ms | 264.16 ms |          1.10× |           9.0 → 9.0 MiB |
| **Nested control flow**       |           |           |                |                         |
| 200 nested if statements      |  13.23 ms |  11.62 ms |          1.14× |         11.6 → 11.3 MiB |
| 400 nested if statements      |  26.67 ms |  22.86 ms |          1.17× |         17.0 → 17.5 MiB |
| 800 nested if statements      |  56.20 ms |  46.82 ms |          1.20× |         31.8 → 29.7 MiB |
| **Full Omarchy corpus**       |           |           |                |                         |
| All Omarchy, GCC diagnostics  |   4.292 s |   3.483 s |          1.23× |         54.0 → 51.9 MiB |
| All Omarchy, JSON diagnostics |   3.581 s |   3.385 s |          1.06× |         54.2 → 52.0 MiB |

RSS above is a separate GNU `time` run per binary/workload, not Python's launcher-contaminated `wait4` reading. The 4,337-line script and startup show no wall-time gain in this sample; fewer instructions do not guarantee a faster observed run.

### Worker throughput and memory

The same complete Omarchy sweep, five shuffled runs per binary/worker count and one warm-up. Each process has the same eight-CPU affinity set; `--jobs 1` can migrate among those CPUs, so compare within this table rather than against the CPU-0 table above. RSS is the median of the five isolated GNU `time` process peaks, including all worker threads. Both GCC and JSON output and exit status match the serial baseline for every sample.

| Format | Jobs |  Before |   After | Before RSS | After RSS |
| ------ | ---: | ------: | ------: | ---------: | --------: |
| GCC    |    1 | 3.539 s | 3.204 s |   54.6 MiB |  51.9 MiB |
| GCC    |    2 | 1.847 s | 1.681 s |   84.9 MiB |  76.6 MiB |
| GCC    |    4 | 0.980 s | 0.892 s |  128.7 MiB | 119.7 MiB |
| GCC    |    8 | 0.591 s | 0.540 s |  208.6 MiB | 203.7 MiB |
| JSON   |    1 | 3.694 s | 3.387 s |   54.5 MiB |  52.0 MiB |
| JSON   |    2 | 2.000 s | 1.740 s |   84.5 MiB |  70.8 MiB |
| JSON   |    4 | 1.017 s | 0.958 s |  127.0 MiB | 119.5 MiB |
| JSON   |    8 | 0.600 s | 0.558 s |  215.9 MiB | 215.9 MiB |

Implemented:

- Ordinary file reads bypass the stdin-cache mutex. Stdin remains protected and cached; native path identity and source-access checks are preserved.
- The producer resolves roots/configuration in input order while workers analyze earlier files. A bounded queue holds at most two pending specs per requested worker, plus active work and the producer's current spec. Completed diagnostics still accumulate for ordered formatting; this is not a constant-memory claim. Thread creation failure uses fewer workers or falls back to serial execution.
- Public CFG snapshots share immutable exit-code sets through `Rc`; checks borrow them instead of cloning. Copy-on-write mutation of a snapshot does not modify another snapshot.
- Token and parent maps use the existing integer-keyed `IdMap`. Current consumers use keyed lookups; no diagnostic ordering depends on map iteration.
- Remove the parser's write-only `reach_pos` field. Updating it copied the filename at every furthest cursor advance, even though diagnostics use the separate failure coordinates. Keep the `reach` index and all failure/recovery behavior.

`--jobs` remains opt-in and defaults to 1. Quiet mode and invocations with non-regular root inputs keep sequential behavior. Worker ASTs stay local to each worker; output order, source resolution, rc warnings and native filename handling remain covered by integration tests.

**Rust API compatibility:** `ProgramState::exit_codes` is now `Rc<BTreeSet<Id>>`; direct mutations use `Rc::make_mut`. The `exit_codes()` accessor still returns `&BTreeSet<Id>`, but is no longer `const`. `Parameters::{parent_map,id_map}` and `build_maps()` now expose `IdMap` rather than `BTreeMap`; their iteration order is unspecified. External constructors and callers requiring ordered map iteration must adapt. The CLI diagnostic contract is unchanged.

### Profile evidence

| Workload                     | Before instructions | After instructions | Reduction | Before malloc calls | After malloc calls |
| ---------------------------- | ------------------: | -----------------: | --------: | ------------------: | -----------------: |
| 4,337-line script            |       1,120,917,884 |      1,024,351,575 |      8.6% |           1,865,907 |          1,715,297 |
| 400 nested if statements     |         125,389,287 |        109,198,019 |     12.9% |             168,543 |            137,851 |
| 800 nested if statements     |         293,559,182 |        242,151,773 |     17.5% |             378,668 |            288,099 |
| All 1,228 Omarchy files, GCC |      22,898,695,974 |     20,825,126,279 |      9.1% |          39,924,750 |         34,094,238 |

Callgrind runs are separate from native timing and produce identical output. The intermediate `snapshots-profile/` excludes the final parser cleanup, allowing its allocation effect to be inspected separately. The initial Omarchy profile attributed 0.14% of instructions to `get_command_basename` and 0.70% to `is_command` (inclusive); those helpers were left unchanged. The parser's repeated filename allocation was the stronger measured string target.

Validation: **2,145 workspace tests**, strict Clippy with warnings denied, rustfmt and dprint; **2,086 oracle comparisons**, **2,000 seeded fuzz inputs**, all with zero divergences; **4,062 snapshot entries unchanged**. New regression tests hold the stdin lock during a regular-file read and send 40 inputs, including an 800-level nested first input, through the bounded queue while checking exact serial output order.

Local evidence (not published artifacts): `.cache/optimize-workers/{comparison,jobs,rss}.json`, their Python drivers, `*.callgrind`, `*.metrics.json`, `after-profile/` and validation logs. Drivers record hashes, arguments, affinity, shuffled run orders and individual samples. Baseline binary SHA-256: `a981b2ffec0c497770976bc4f4783fce58dad13a23189d42437e2aefa50cb979`; final binary SHA-256: `d62e2d074d7351f2ebde116261a38ab7fd5e959af891ff49b1ea5f7a5f63a461`.

## 2026-10-11: lazy CFG associations and allocation-free traversal

Compared with our own Rust release binary at [c0e72e70](https://github.com/kjanat/shellcheck-rs/commit/c0e72e70ce09d83193de087a3eed4e2edea3fba0). Five shuffled before/after process runs per workload, one warm-up per binary, pinned to CPU 0; full analysis, `--norc -s bash`. Times are medians. Every measured output is byte-identical, including complete GCC and JSON sweeps of pinned Omarchy [077ac1da939d](https://github.com/omacom/omarchy/commit/077ac1da939de00d061c1035e1a1d00587a119b8). These are local observations without confidence intervals; startup is effectively unchanged.

| Workload                                       |     Before |             After | Speedup | Peak RSS before → after |
| ---------------------------------------------- | ---------: | ----------------: | ------: | ----------------------: |
| **Ordinary scripts**                           |            |                   |         |                         |
| 2-line script                                  |    2.47 ms |       **2.45 ms** |   1.01× |           6.2 → 6.3 MiB |
| 170-line script                                |   12.65 ms |      **11.46 ms** |   1.10× |           8.9 → 9.2 MiB |
| 1,632-line script                              |  112.58 ms |     **103.60 ms** |   1.09× |         48.8 → 44.3 MiB |
| 4,337-line script                              |  369.20 ms |     **307.01 ms** |   1.20× |       109.8 → 103.5 MiB |
| 120 scripts / 9,107 lines                      |  395.85 ms |     **357.62 ms** |   1.11× |           9.6 → 9.1 MiB |
| **Nested control flow**                        |            |                   |         |                         |
| 200 nested if statements                       |   83.56 ms |      **15.70 ms** |   5.32× |         30.6 → 12.2 MiB |
| 400 nested if statements                       |  356.37 ms |      **33.83 ms** |  10.53× |         98.5 → 19.2 MiB |
| 800 nested if statements                       | 1560.40 ms | ***🏆 77.87 ms*** |  20.04× |        367.9 → 37.5 MiB |
| **Full Omarchy corpus**                        |            |                   |         |                         |
| All Omarchy: 1,228 files / 119,468 lines, GCC  | 4934.84 ms |    **4442.69 ms** |   1.11× |         56.3 → 56.0 MiB |
| All Omarchy: 1,228 files / 119,468 lines, JSON | 5041.36 ms |    **4583.16 ms** |   1.10× |         56.0 → 56.0 MiB |

Peak RSS is a separate isolated GNU `time` measurement per binary/workload. The raw Python `wait4` readings for small processes include a launcher-memory floor and are not used in this table. Binary size grew from 5,678,655 to 5,772,568 bytes (1.7%).

Implemented:

- Skip whole-subtree redirection searches when no relevant redirection exists. Pipeline producer/consumer predicates run only when a warning needs them, stop at the first match, and cache shared lookups.
- Replace eagerly expanded ancestor/node pairs with per-token ranges over original node numbers and a shared remapping vector. `NodeAssociations::get` materializes and caches a sorted, deduplicated set only when requested. Declaration checks skip lookups until there is an earlier assignment to reference. Construction storage is linear in tokens/build visits and graph nodes; demanding sets for every ancestor could still expand quadratically.
- Use one shared AST child-order definition for collecting, mutable, allocation-free and short-circuit visitors. Preorder, stack analysis and map-building walks no longer allocate temporary child vectors.

The public `CFGResult::cf_id_to_nodes` and `CFGAnalysis::token_to_nodes` fields now use `NodeAssociations` rather than a mutable `IdMap`. The current consumers retain the same `get(&Id) -> Option<&BTreeSet<Node>>` behavior; external code constructing or mutating those fields directly must adapt. No diagnostic or CLI contract changes.

Callgrind confirms the improvement is eliminated work: the 4,337-line workload drops from 1.633B to 1.308B instructions (19.9%); nesting depth 400 from 1.979B to 0.176B (91.1%); depth 800 from 7.895B to 0.455B (94.2%). Eager CFG association insertion is gone. Doubling depth now increases instructions 2.59x rather than 3.99x: the dominant quadratic paths are removed, but the complete analyzer is not claimed to be linear.

Across the entire Omarchy corpus, instructions fall from 33.777B to 27.364B (19.0%), allocation calls from 65,823,020 to 51,070,285 (22.4%), and collecting AST child-list calls from 20,090,714 to 821,737 (95.9%). The remaining walks use the allocation-free visitor. Native runtime improvements are smaller than instruction reductions; they are measured separately above.

Validation: 2,135 workspace tests; Clippy with warnings denied; rustfmt and dprint; 2,086 Haskell-oracle comparisons with zero divergences; 2,000 seeded fuzz inputs with zero divergences; all 4,062 behavior snapshot entries unchanged. Unit-test CFG builds compare every association against the original eager algorithm after graph collapse. Dedicated tests cover overlapping ranges, lazy caching, absent IDs, traversal order, mutable children and early stopping.

Local evidence (not published artifacts): `.cache/optimize-c0e72e70/comparison.json`, `rss.json`, `*.callgrind`, `*.metrics.json`, and verification logs. The comparison driver records exact arguments, input/output hashes, binary hashes, run order and all samples. The after binary SHA-256 is `1bc5368695c5a3a9990da52c80db69a6d1a34f4fd6ac8dfa85cbc9b2f736c767`.

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

Acceptance addition (startup): `valgrind --tool=callgrind` on `.bench/corpus/startup.sh` with `-f gcc` reports at most 8 M instructions (from 31.6 M, 63 % of it `insert_global` called from `create_environment_state`).

**As built.** `cfg_analysis::VMap<V>` stores an `im_rc::OrdMap<Rc<str>, Rc<V>>` (im-rc 15.1, a new dependency of `shellcheck-rs`, so the crate is no longer "std + regex only"). Cloning a state is O(1), an insert copies one root-to-leaf path, and the `VariableState` values with their nested property sets are shared between all states that hold them (values are `Rc` because a path copy clones up to 64 entries; with plain values that would deep-copy them). `version`, `vm_eq` (version, then root pointer, then `OrdMap`'s diff-based equality that skips shared subtrees), ordered iteration and `Ctx::process` are unchanged. What changed besides the storage:

- `ProgramState` no longer holds a flat `variables_in_scope` map. It holds the three scope maps of the `InternalState` (an O(1) clone each, so `internal_to_external` is O(1) per node) and resolves a name by precedence prefix > local > global at lookup, censoring the literal value when `variable_value()` reads it. `variables_in_scope()` still exists as an O(vars) flattening for tests and debugging; the two direct field users (`conditions.rs`, `flow.rs`) call `numerical_status`/`space_status`/`variable_properties` instead. `ProgramState` lost its derived `PartialEq` (nothing used it).
- `vm_patch` is a left-biased union (`union_left`, written in the crate): `OrdMap::union` in im-rc 15.1 keeps the *other* map's value when the other map is the larger, so it cannot be used for a biased union. It costs O(m log n) in the smaller map's size, which is the diff (or the dependency base) in `patch_state` and in the `grouped` loop.
- `merge_maps_var`/`merge_maps_func` walk `OrdMap::diff(a, b)` instead of the union of all keys. A key with an equal value on both sides merges to that value (`merge_variable_state(x, x) == x`, set union is idempotent), so skipping it changes nothing, and the reader fallback is called for exactly the keys that exist on one side only, as before. This is what keeps joins O(diff) instead of O(vars).
- `create_environment_state` builds the global map in one pass (later lists win, as the successive inserts did) with one shared `Rc` per kind of variable; empty maps share one thread-local allocation (`OrdMap::new` allocates a ~2 KB node, and there are four empty maps in most states: that alone was 68 % of the peak heap in the first version); the unreachable placeholder for nodes the analysis never reached is built once and cloned.

Before (`5d3fe06`, this container) and after, `conformance bench --input`, three repeats, the bench is noisy here so ranges are over several runs:

| phase        | medium before |   medium after |  large before |    large after |
| ------------ | ------------: | -------------: | ------------: | -------------: |
| parse        |         24 ms |       23–29 ms |         73 ms |     112–131 ms |
| maps         |          3 ms |         2–4 ms |          8 ms |       12–14 ms |
| **cfg**      |  **1 570 ms** | **142–220 ms** | **12 610 ms** | **650–840 ms** |
| params-other |        512 ms |       18–58 ms |      1 635 ms |    42–1 190 ms |
| checks       |        110 ms |       46–52 ms |        505 ms |     135–178 ms |
| resolve      |        145 ms |       57–80 ms |             — |         108 ms |
| total        |      2 364 ms |     278–430 ms |     13 799 ms | 1 060–1 580 ms |

(`params-other` and `resolve` in this tool are measured as differences of totals and jump around by that much between runs; the oracle takes 1.5–2.5 s on medium and 9.9–11.5 s on large in the same runs, so the port is now 4–7× faster in-process.) Peak RSS (`wait4`): small 41 -> 14 MiB, medium 1 375 -> 132 MiB, large 8 735 -> 530 MiB, startup 9 -> 9 MiB. CLI wall time: `startup.sh` median 6.2 -> 3.15 ms, 120 files in one invocation (`corpus/many`) 1 928 -> 777 ms; callgrind on `startup.sh` `-f gcc` 31.66 M -> 3.17 M instructions.

Verification: `cargo test -p shellcheck-rs` 1 517 pass; `conformance gate`: 2 048 agree, 0 diverge; `conformance fuzz` seed 0 and seed 1013, 2 000 inputs each, 0 divergences (seed 0 also reports the known upstream oracle crash in `checkCmd` on `coproc` inside `$(...)`); `cargo conformance-snapshot`: 4 026 entries, 0 changed (no regeneration needed); `-f gcc` and `-f json1` of small, medium, large and startup byte-identical to the oracle (sha256), and the port's json1 output on the 120 `many` scripts identical to both the pre-change port and the oracle.

What did not help or was a trap: the first version (persistent maps, no shared empty map) already brought cfg to 220 ms but left medium at 373 MiB, because every `new_internal_state()` and every placeholder state allocated four empty tree nodes; sharing the empty map took it to 132 MiB and cfg to ~150 ms. `OrdMap::union` is not left-biased when the left operand is smaller (see above), which is easy to miss because the doc says it is. Not done because the targets are met by a wide margin: `Rc<BTreeSet>` for `s_exit_codes` (it is still cloned per state copy), `Rc<VariableState>` all the way through `read_variable` (lookups still clone the value out), avoiding the `self.cache.get(&node).cloned()` clone in `get_cache`. The analysis result now holds `Rc`s, so `CFGAnalysis`/`ProgramState` are no longer `Send`; nothing in the workspace needs that, but a multi-threaded embedder would have to switch `im_rc` to `im` (Arc).

### Landed (end-to-end, this container, `hyperfine` 10 runs with warmup, GHC 0.11.0 oracle)

| scenario           | before `5d3fe06` | after `cdf4a1c` |  oracle | after vs oracle | after vs before |
| ------------------ | ---------------: | --------------: | ------: | --------------: | --------------: |
| startup (`-f gcc`) |           5.9 ms |          3.1 ms | 12.4 ms |            3.9× |            1.9× |
| small              |          72.8 ms |         23.4 ms |  104 ms |            4.4× |            3.1× |
| medium             |           2.87 s |          297 ms |  1.58 s |            5.3× |            9.7× |
| large              |           31.0 s |          1.30 s |  5.75 s |            4.4× |           23.8× |
| many (120 files)   |           1.92 s |          693 ms |  3.75 s |            5.4× |            2.8× |
| peak RSS medium    |        1 374 MiB |         131 MiB | 251 MiB |                 |                 |
| peak RSS large     |        8 731 MiB |         526 MiB | 1.2 GiB |                 |                 |

Both the oracle and the port were measured in the same session, so these ratios are what the bench on CI should show up to its 2.4× faster machine. Parity after WP-R1: `-f gcc` and `-f json1` byte-identical to the oracle on all four corpus scripts, gate 2 048 agree / 0 diverge, fuzz seed 0 ×2000 clean.

- **WP-R1** (`cdf4a1c`): the structural-sharing change above.
- **WP-R0** (`a8266e6`, correctness, found by CI's seed roulette: `conformance fuzz --seed "$GITHUB_RUN_NUMBER"`, seed 156): a `time` flag word that fails after consuming input commits the parse and fails, as Parsec's `many readFlag` does; `children()`/`children_mut()` of `T_CoProc` yield only the body, as `Inner_T_CoProc (Maybe Token) t` does not traverse the name. Verified: 1 617 tests, gate 2 048 / 0, fuzz seed 156 ×4000 and seed 0 ×2000 clean, clippy/fmt/dprint clean. Recorded in `DIVERGENCES.md` (seed 156 now in the clean list).

## Round 2: where the time goes after WP-R1 (measured, `02af506`)

`valgrind --tool=callgrind rshellcheck -f gcc .bench/corpus/large.sh`: **4.53 G instructions** (the port's wall time on large is 1.30 s here; the oracle's 5.75 s). Inclusive costs; the recursive frames (`'2`) are not usable in `callgrind_annotate --inclusive`, so the numbers below are from the non-recursive callers:

| where                                                                                   | Ir (large) | share |
| --------------------------------------------------------------------------------------- | ---------: | ----: |
| `cfg_analysis::analyze_control_flow`                                                    |     2.77 G |  61 % |
| ├ `patch_state` called from `analyze_control_flow` itself (the `addDeps` loop, 33 093×) |     1.58 G |  35 % |
| ├ `cfg::build_graph` (of which `remove_unnecessary_structural_nodes` 0.30 G)            |     0.67 G |  15 % |
| ├ the DFA (`dataflow`, `run_cached`, `merge_state`, …)                                  |    ~0.25 G |   5 % |
| └ `flattenByNode` merges, `node_to_data`, drop                                          |    ~0.27 G |   6 % |
| `parser::parse_script_spec`                                                             |     0.69 G |  15 % |
| `analytics::analyze_with` (node walk 0.48 G; `CommandCheck::run` 2 435 499× = 0.13 G)   |     0.66 G |  15 % |
| `drop_glue::<Parameters>`                                                               |     0.18 G |   4 % |
| `analyzer_lib::stack_analysis` (the `variableFlow`), `build_maps`, the rest             |    ~0.15 G |   3 % |

Self costs that cut across those: `memcmp` 9 % (`Rc<str>` key comparisons inside `OrdMap`), malloc+free 20 %, `OrdMap::insert` 10 %, SipHash on `usize`/`Id` keys (`hash_one::<&usize>` 5.6 % + `Sip13Rounds::write` 3.1 %: `HashMap<Node, _>` and `HashMap<Id, _>` with the default `RandomState` in `cfg.rs`, `cfg_analysis.rs`), `Vec<parser::Context>::clone` 3.9 %, `BTreeSet<Node>::insert` 2.3 % (498 479 inserts in `build_graph` for `id_to_nodes`, and `caai_get_associative_arrays`).

**The 35 %.** `analyze_control_flow` ends with Haskell's `addDeps`: for every invocation, `base = depsToState deps`, and for every node of that invocation `(patchState base pre, patchState base post)`. `patch_state(base, a)` is `union_left(a, base)`: an O(|base| · log n) walk of the dependency base per node (the root invocation's base holds every variable the script reads: hundreds of keys), done twice for each of ~16 500 nodes. Haskell pays the same O(|base| log n) per node with `Data.Map.union`; it is not quadratic, but it is the largest constant left.

### WP-R2 Patch the dependency base lazily

In `analyze_control_flow`, stop materialising `patch_state(&base, a)` for every node. A node that appears in exactly one invocation (almost all of them: every node outside a function body called more than once) needs no merge, so its `ProgramState` can be a two-layer view: the node's own `InternalState` over the invocation's `base`, resolved at lookup. Concretely: give `ProgramState` an optional second layer (`Option<Rc<InternalState>>` or the four maps of the base) and resolve a variable as `a.prefix ?? base.prefix ?? a.local ?? base.local ?? a.global ?? base.global`, which is exactly what `patch_state` then scope precedence computes (per-scope-map left-biased union, then prefix > local > global); `exit_codes` as `a.or(base)`, `state_is_reachable` likewise. Only nodes that appear in two or more invocations go through the existing `patch_state` + `merge_states_nonempty` path, so the result for those is bit-identical to today. `variables_in_scope()` (tests and debugging) flattens both layers. Keep `deps_to_state` and the grouping order; the invariant is the *answers* `ProgramState` gives (`variable_value`, `space_status`, `numerical_status`, `variable_properties`, `exit_codes`, `state_is_reachable`), not the shape.

Acceptance: `cargo test -p shellcheck-rs` all pass; gate 0 divergences; fuzz seed 0 ×2000 and seed 156 ×4000 0 divergences; snapshot unchanged; `-f gcc`/`-f json1` byte-identical to the oracle on the four corpus scripts; callgrind on `large.sh` down by ≥ 1.3 G instructions (from 4.53 G); the `conformance bench` cfg phase on large ≤ 350 ms (from 624 ms). Report callgrind totals before/after on medium and large.

**As built** (`32690b5`). `ProgramState`'s three scope maps are `ScopeValues { top: VMap, base: Option<VMap> }`: the node's own map over the invocation's dependency base, resolved at lookup (top, then base), then prefix > local > global as before. `analyze_control_flow` counts how many invocations each node occurs in; a node in exactly one gets `patched_to_external(&base, a)` in O(1), which takes the same cases as `patch_state`/`vm_patch` in the same order (diff version 0 → base; base version 0 or quick-equal → diff; per map an empty or version-equal side collapses to one layer; only the left-biased union stays two layers), so its answers are those of `internal_to_external(&patch_state(&base, a))` by construction. Nodes in two or more invocations take the old path (`patch_state`, then `merge_states_nonempty`, ascending node order), so their states and the merges the version counter sees are unchanged. `deps_to_state` is built once per invocation and shared by O(1) `OrdMap` clones; the invocation map is `mem::take`n out of the `Ctx`; `node_to_data` is filled directly with unreachable placeholders only for nodes nobody reached. A unit test compares every `ProgramState` accessor of the layered state against the materialised patch (overlapping keys in all scopes, exit codes, unreachability, empty sides) and fails if the layer order is flipped. Callgrind large 4.53 G → 2.67 G on its own (−41 %), `patch_state` 1.58 G → 70 M, `drop_glue::<Parameters>` 180 M → 61 M; peak RSS medium 132 → 53 MiB, large 530 → 122 MiB.

### WP-R3 A hasher for integer keys

Every `HashMap`/`HashSet` keyed by `Node` (`usize`) or `Id` (`i32`) in `cfg.rs` and `cfg_analysis.rs` uses SipHash with a random seed: 8.7 % of all instructions on large, mostly from `remap_graph`/`remove_unnecessary_structural_nodes`/`topsort` (a hash lookup per node per pass) and from `Ctx::process` (`pred_flow`, `succ_all`, `labels`, `cache` lookups per DFA step). Add an in-crate `BuildHasherDefault<IdHasher>` (a multiply-and-xor over the single integer write, no new dependency; `write_usize`/`write_i32` plus a `write` fallback that folds bytes) and `type IdMap<K, V> = HashMap<K, V, IdBuild>` / `IdSet`; use it for every integer-keyed map and set in the two files (24 + 11 `HashMap`, 5 `HashSet`). Iteration order over these maps must not become observable: check each `for` over a hash map in those files and keep any that feeds output or a merge in sorted order as today (several already sort or go through `BTreeMap`). Optionally, where the keys are the dense `0..n` renumbered nodes (`remap_graph`, `renumber_graph`, `topsort`'s `visited`), a `Vec` indexed by node beats any hash.

Acceptance: tests, gate, fuzz seed 0 ×2000, snapshot unchanged; callgrind on large down ≥ 300 M instructions; no `RandomState` map keyed by `Node` or `Id` left in `cfg.rs`/`cfg_analysis.rs`.

**As built** (`9e8fcb1`). `idhash.rs` holds `IdHasher`, a multiply-and-rotate hasher for small integer keys (the finish rotates by 26 bits because hashbrown takes the low bits for the bucket and the top 7 for the tag), `IdBuild = BuildHasherDefault<IdHasher>`, `IdMap<K, V>` and `IdSet<K>`. Every `HashMap`/`HashSet` keyed by `Node` or `Id` in `cfg.rs` and `cfg_analysis.rs` uses them (`cf_id_to_range`/`cf_id_to_nodes`, `MutGraph`'s maps, the remap/renumber helpers, degree and candidate sets in `remove_unnecessary_structural_nodes`, `topsort`'s and the dominator DFS's `visited`, `Ctx::cache`/`labels`/`pred_flow`/`succ_all`, `token_to_*`, `node_to_data`). Every iteration over those maps was checked: each is sorted, reduced with `max`, or feeds another set, so no order reached output. Left on `RandomState` on purpose: `Ctx::invocations`, keyed by `Vec<Node>` and iterated into the merge order (see WP-R5). Callgrind large −382 M (−8.4 %), medium −138 M (−10.8 %); no `hash_one`/`Sip13Rounds` left near the top, hashbrown is 0.7 % of instructions.

### WP-R4 Dispatch command checks by name once per command

`checks::commands::register` adds 73 `CommandCheck`s as separate node checks, so the node walk calls `CommandCheck::run` 73 times per AST node (2.4 M calls on large, 0.13 G), and for every `T_SimpleCommand` it recomputes `get_literal_string` of the command word and `dispatch`'s matching 73 times. Haskell's `Checks.Commands.getChecker` builds one `M.Map CommandName (Token -> Analysis)` with `buildCommandMap` and `checkCommand` looks the command up once. Do the same: `register` adds one node check that owns a `HashMap<CommandName, Vec<CommandBody>>` (plus the `Basename`/`Exactly`/`builtin` dispatch rules from `dispatch`) and runs the bodies for the one or two names a command maps to, in registration order within a name (Haskell's `insertWith composeAnalyzers` runs the *later* registered check first: `composeAnalyzers f g x = f x >> g x` with `f` the new one; find out whether the port already reproduces that order, by reading how two checks on one name emit today, and keep the current observable order, since the gate passes with it). The optional `deprecate-which` check must still join the map when enabled (`OPTIONAL_CHECKS` in `analytics/mod.rs`). `shell_support::register`'s `ForShell` has the same shape at 8 checks per node (15 M); do it too if it is the same mechanism.

Acceptance: tests, gate, fuzz seed 0 ×2000, snapshot unchanged, byte-identical output on the corpus; `CommandCheck::run`-equivalent cost on large ≤ 20 M instructions.

**As built** (`8f5525e`). `checks::commands::register` adds one node check, `CommandTable`, owning a `HashMap<&'static str, Vec<CommandCheck>>` keyed by the check's name string; `all_checks()` builds the list in the old registration order. Per node, `route(t)` returns `None` unless the node is a `T_SimpleCommand` with a literal first word, computes that literal once and applies `checkCommand`'s rules (`/path/cmd` → `Basename` only; `builtin x ..` → `Exactly x` on the rewritten command; otherwise `Exactly name` and `Basename name`), then runs that name's checks in registration order, skipping those whose key kind the route does not select. `dispatch` is replaced by `route` plus `CommandName::matches`, shared with the single-check path, so the optional `deprecate-which` check still registers as its own node check and its emission order is unchanged. Two tests: interleaving/route cases, and the table against the 73 checks run separately on 16 scripts. `ForShell` (8 checks per node, ~5.5 M) is a dialect gate, not a name table, and was left alone. Found, not changed: for two checks on one `CommandName` the port runs them in registration order (older first) with `Exactly`/`Basename` interleaved, whereas Haskell's `insertWith composeAnalyzers` runs the later-registered first and all `Exactly` before all `Basename`; it is unobservable because the comment list is sorted, and the gate/fuzz/snapshot agree. Callgrind large −125 M, medium −61 M.

### Round 2 landed (end-to-end, this container, `hyperfine` 10 runs, GHC 0.11.0 oracle)

Combined head `32690b5` = WP-R3 + WP-R4 + WP-R2, verified once as a whole: 1 524 tests pass; gate 2 048 agree / 0 diverge; fuzz seed 0 ×2000 and seed 156 ×4000 clean; snapshot 4 026 entries unchanged; `-f gcc` and `-f json1` byte-identical to the oracle on startup, small, medium, large and the 120 `many` scripts; clippy, fmt and dprint clean.

| scenario             | after WP-R1 (`02af506`) | after round 2 (`32690b5`) |  oracle | round 2 vs oracle |
| -------------------- | ----------------------: | ------------------------: | ------: | ----------------: |
| startup (`-f gcc`)   |                  3.0 ms |     3.6 ms (σ 1.0; noise) | 13.5 ms |              3.8× |
| small                |                 26.6 ms |                   17.7 ms |  115 ms |              6.5× |
| medium               |                  314 ms |                    166 ms |  1.40 s |              8.4× |
| large                |                  1.32 s |                    475 ms |  6.22 s |             13.1× |
| many (120 files)     |                  676 ms |                    575 ms |  3.84 s |              6.7× |
| peak RSS medium      |                 131 MiB |                    53 MiB | 251 MiB |                   |
| peak RSS large       |                 526 MiB |                   122 MiB | 1.2 GiB |                   |
| instructions startup |                  3.17 M |                    3.05 M |         |                   |
| instructions medium  |                 1.277 G |             739 M (−42 %) |         |                   |
| instructions large   |                 4.535 G |           2.155 G (−52 %) |         |                   |

Per phase after round 2 (`conformance bench --input`): medium total 131 ms = parse 25 / cfg 52 / checks 34; large total 438 ms = parse 100 / cfg 174 / checks 117. The CFG analysis is no longer the single dominant phase; the next round has to work on three fronts at once.

### WP-R5 Deterministic invocation order (correctness first, then measure)

`Ctx::invocations` is a `HashMap<Vec<Node>, (deps, StateMap)>` with `RandomState`, and `analyze_control_flow` iterates it to group the per-node states before `merge_states_nonempty`, so the merge order for nodes that occur in several invocations is per-run random. Haskell's `M.Map` iterates by key (the invocation path, a list of nodes, in lexicographic order). Both round-2 agents flagged it. Switch the map to `BTreeMap<Vec<Node>, _>` so the order is Haskell's; then gate, fuzz (several seeds), snapshot. If anything changes, that is a latent nondeterminism now fixed and the snapshot diff belongs in the commit.

### Later (measure first, after WP-R5)

- Parser (23 % of large now): `Vec<Context>::clone` 176 M (`try_parse`, `sub_parser`, `read_pending_heredocs`): restore the context stack by truncating to its saved length where the attempt is balanced; `pending_heredocs`/`heredoc_bodies` are cloned per `try_parse` too. `read_term_more`/`read_and_or` self costs next.
- CFG (40 %): `build_graph` 0.67 G, of which `remove_unnecessary_structural_nodes` 0.30 G and 498 479 `BTreeSet<Node>` inserts for `id_to_nodes` (a sorted `Vec<Node>` per id built once is cheaper); `memcmp` on `Rc<str>` keys inside `OrdMap` (9 %).
- Checks (27 %): `caai_get_associative_arrays` (104 M, walks the tree per call?), `check_pipe_to_nowhere` 46 M, `check_redirect_to_same` 32 M, `check_number_comparisons` 29 M; `ForShell` as one check resolving the shell once.
