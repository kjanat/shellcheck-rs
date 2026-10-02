<a name="idtop"></a>

# 3 Rust port performance

The full record is `rust/PERF.md` on `rust-port`. This page is the narrative and the numbers; PERF.md has the specs, acceptance lists and "as built" paragraphs.

## 3.1 Starting point

*2026-09-28 bench, port at `5d3fe06`.*

The port was faster than upstream on small inputs and *slower and far hungrier* on large ones:

| script | lines | upstream |      port |                                  port peak RSS | upstream RSS |
| ------ | ----: | -------: | --------: | ---------------------------------------------: | -----------: |
| small  |   170 |   0.08 s |    0.07 s |                                         42 MiB |      120 MiB |
| medium |  1632 |   1.31 s | 1.9–6.6 s |                                       1374 MiB |      251 MiB |
| large  |  4337 |   10.4 s | 12.7–50 s | 8731 MiB (excluded from the bench: over 4 GiB) |     1203 MiB |

Per phase (`conformance bench`), cfg was 85 % of medium and 90 % of large and grew 7.3× for 2.66× more lines: **quadratic**.

**[⬆ Top](#idtop)**

## 3.2 Round 1: the quadratic CFG state

*WP-R1, `cdf4a1c`.*

**Root cause.** `cfg_analysis::VMap<V>` was a `BTreeMap<String, V>` cloned on every state copy, and `Ctx::process` copied the state about six times per CFG node, while `internal_to_external` rebuilt a flat map per node at the end. Haskell does the same operations on `Data.Map`, which shares structure, so there it is O(nodes · log vars); in Rust it was O(nodes · vars). Callgrind on medium: 9.67 G instructions, 87 % in `analyze_control_flow`, `BTreeMap::clone` 45 %. Massif: 38 % of the 1.43 GB peak was map clones.

**Fix.** `VMap` stores an `im_rc::OrdMap<Rc<str>, Rc<V>>` (O(1) clone, path copying on insert, values shared); `ProgramState` holds the three scope maps and resolves prefix > local > global at lookup (censoring the literal value) instead of a flattened map; `vm_patch` is an in-crate left-biased `union_left` (im-rc's `OrdMap::union` is *not* left-biased when the left operand is smaller, despite its docs); merges walk `OrdMap::diff` so joins are O(diff); `create_environment_state` builds the global map in one pass; the empty map and the unreachable placeholder are shared (an empty `OrdMap` allocates a ~2 KB node, and four empty maps per state were 68 % of the heap in the first attempt). `CFGAnalysis`/`ProgramState` are no longer `Send` (switch `im_rc` → `im` for a multi-threaded embedder).

**Result** (this container, hyperfine 10 runs; before = `5d3fe06`, oracle = GHC 0.11.0):

| scenario           |          before |   after WP-R1 |         oracle | WP-R1 vs oracle |
| ------------------ | --------------: | ------------: | -------------: | --------------: |
| startup            |          5.9 ms |        3.1 ms |        12.4 ms |            3.9× |
| small              |         72.8 ms |       23.4 ms |         104 ms |            4.4× |
| medium             |          2.87 s |        297 ms |         1.58 s |            5.3× |
| large              |          31.0 s |        1.30 s |         5.75 s |            4.4× |
| 120 files          |          1.92 s |        693 ms |         3.75 s |            5.4× |
| RSS medium / large | 1374 / 8731 MiB | 131 / 526 MiB | 251 / 1200 MiB |                 |

Startup went from 31.6 M to 3.2 M instructions (63 % of it had been `insert_global` from `create_environment_state`).

**WP-R0** (`a8266e6`) rode along: two parity fixes found by CI's seed-156 fuzz (see [[Rust Port|02 Rust port]]).

**[⬆ Top](#idtop)**

## 3.3 Round 2: the remaining CFG constant, hashing, dispatch

*`9e8fcb1`, `8f5525e`, `32690b5`.*

Callgrind on large after WP-R1: 4.53 G instructions. `analyze_control_flow` 61 %, of which 35 % was Haskell's `addDeps` step (`patch_state(base, state)` for every node of every invocation: O(|dependency base| · log n) per node, twice); `build_graph` 15 %; parser 15 %; `analyze_with` 15 % (the 73 `CommandCheck`s ran on every AST node: 2.4 M calls); SipHash on integer-keyed maps 8.7 %; `memcmp` on `Rc<str>` keys 9 %; `drop_glue::<Parameters>` 4 %.

| package                    | commit    | what                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |       callgrind large |
| -------------------------- | --------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------: |
| WP-R3 integer hasher       | `9e8fcb1` | in-crate `IdHasher` (multiply-and-rotate; finish rotates by 26 bits because hashbrown takes the low bits for the bucket and the top 7 for the tag), `IdMap`/`IdSet` for every `Node`/`Id`-keyed map in `cfg.rs` and `cfg_analysis.rs`; every iteration order checked; `Ctx::invocations` left alone (iterated into a merge order)                                                                                                                                                |       −382 M (−8.4 %) |
| WP-R4 command dispatch map | `8f5525e` | one node check `CommandTable` with a `HashMap<&str, Vec<CommandCheck>>`; `route(t)` computes the literal command word once and applies `checkCommand`'s rules (`/path/cmd` → Basename only; `builtin x` → Exactly x on the rewritten token; else both); registration order kept; the optional `deprecate-which` still registers as its own node check                                                                                                                            |                −125 M |
| WP-R2 lazy dependency base | `32690b5` | `ProgramState` scope maps become `ScopeValues { top, base: Option<VMap> }` resolved at lookup; nodes in exactly one invocation (almost all) get an O(1) `patched_to_external(&base, a)` mirroring `patch_state`/`vm_patch`'s cases; nodes in several invocations keep the old patch + merge path so the version counter sees the same merges; `deps_to_state` built once per invocation; a unit test compares every accessor of the layered state against the materialised patch | −1.87 G (−41 %) alone |

**Combined result** (head `32690b5`, verified once as a whole: 1524 tests, gate 2048/0, fuzz seeds 0 and 156 clean, snapshot unchanged, byte parity on all corpus scripts and the 120 `many` scripts, clippy/fmt/dprint clean):

| scenario                    |       after WP-R1 |                                       after round 2 |         oracle | round 2 vs oracle |
| --------------------------- | ----------------: | --------------------------------------------------: | -------------: | ----------------: |
| startup                     |            3.0 ms | 3.6 ms (σ 1.0, noise; 3.17 M → 3.05 M instructions) |        13.5 ms |              3.8× |
| small                       |           26.6 ms |                                             17.7 ms |         115 ms |              6.5× |
| medium                      |            314 ms |                                              166 ms |         1.40 s |              8.4× |
| large                       |            1.32 s |                                              475 ms |         6.22 s |             13.1× |
| 120 files                   |            676 ms |                                              575 ms |         3.84 s |              6.7× |
| RSS medium / large          |     131 / 526 MiB |                                        53 / 122 MiB | 251 / 1200 MiB |                   |
| instructions medium / large | 1.277 G / 4.535 G |                     739 M (−42 %) / 2.155 G (−52 %) |                |                   |

Per phase after round 2: medium 131 ms = parse 25 / cfg 52 / checks 34; large 438 ms = parse 100 / cfg 174 / checks 117. The CFG analysis is no longer the single dominant phase.

Cumulative since `5d3fe06`: medium 2.87 s → 166 ms (17×), large 31 s → 475 ms (65×), large RSS 8.7 GiB → 122 MiB (72×).

**[⬆ Top](#idtop)**

## 3.4 What is next

*In `rust/PERF.md`.*

- **WP-R5** (correctness first): `Ctx::invocations` → `BTreeMap<Vec<Node>, _>` so the merge order for multi-invocation nodes is Haskell's; then gate, fuzz several seeds, snapshot. Any change is a latent nondeterminism fixed.
- Parser (23 % of large): `Vec<Context>::clone` 176 M in `try_parse`/`sub_parser`/`read_pending_heredocs`; restore the context stack by truncation where the attempt is balanced; `pending_heredocs`/`heredoc_bodies` cloned per `try_parse`.
- CFG build (`build_graph` 0.67 G): `remove_unnecessary_structural_nodes` 0.30 G; 498 479 `BTreeSet<Node>` inserts for `id_to_nodes` (sorted `Vec` per id instead); `memcmp` on `Rc<str>` keys in `OrdMap` (9 %).
- Checks (27 %): `caai_get_associative_arrays` 104 M (walks the tree per call?), `check_pipe_to_nowhere` 46 M, `check_redirect_to_same` 32 M, `check_number_comparisons` 29 M; `ForShell` as one check resolving the shell once (8 virtual calls per node today).
- Optional: an in-crate persistent tree to drop the `im-rc` dependency if its license or supply-chain score is a concern.

**[⬆ Top](#idtop)**

## 3.5 Methodology notes specific to this branch

- Instruction counts (callgrind, `-f gcc` on `.bench/corpus/{medium,large}.sh`) are the A/B currency: deterministic to the last digit, unaffected by parallel builds. Wall time (hyperfine, 10 runs, warm-up 2, `-N`, `-i` because the exit code is non-zero when there are findings) and peak RSS (Python `os.wait4` → `ru_maxrss`) are measured only when nothing else is building.
- Per-phase `conformance bench` numbers for `params-other` and `resolve` are differences of totals and jump around; `cfg`, `parse` and `checks` are directly timed.
- `callgrind_annotate --inclusive=yes` is unusable for recursive frames (`'2` suffixes show > 100 %); read the non-recursive callers (`--tree=caller`) instead. `stack_analysis` looked like 20 % and was really ~1 % for that reason.

**[⬆ Top](#idtop)**

<a name="idend"></a>
