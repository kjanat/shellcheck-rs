<a name="idtop"></a>

# 7 Performance

`rust/PERF.md` on `master` holds every measurement, its method and the work packages. Each section names its baseline and its machine; numbers compare within one section. This page keeps the tables a reader needs to place the port.

## 7.1 Starting point

Measured at port commit `5d3fe06` on the generated benchmark corpus (seed 20260928), against GHC ShellCheck 0.11.0:

| Script | Lines |  Oracle |      Port | Port peak RSS | Oracle peak RSS |
| ------ | ----: | ------: | --------: | ------------: | --------------: |
| small  |   170 | ~0.08 s |    0.07 s |        42 MiB |        ~120 MiB |
| medium | 1 632 |  1.31 s | 1.9–6.6 s |     1 374 MiB |         251 MiB |
| large  | 4 337 |  10.4 s | 12.7–50 s |     8 731 MiB |       1 203 MiB |

The cfg phase was 85 % of medium and 90 % of large and grew 7.3× for 2.66× more lines. The cause: `cfg_analysis::VMap<V>` was a `BTreeMap<String, V>` cloned on every state copy, about six times per CFG node, where Haskell's `Data.Map` shares structure.

**[⬆ Top](#idtop)**

## 7.2 Rounds 1 and 2

WP-R1 (`cdf4a1c`) stores the analysis state in `im_rc::OrdMap<Rc<str>, Rc<V>>`, resolves scope precedence at lookup, walks `OrdMap::diff` in merges, and shares the empty map. WP-R3 (`9e8fcb1`) adds the integer-key hasher `idhash.rs` for every node and id keyed map. WP-R4 (`8f5525e`) dispatches the 73 command checks through one `CommandTable` keyed by command name. WP-R2 (`32690b5`) layers a node's state over its invocation's dependency base and resolves at lookup, so nodes in exactly one invocation skip `patch_state`.

Combined head `32690b5`, hyperfine with 10 runs, same session as the oracle:

| Scenario            | After WP-R1 (`02af506`) | After round 2 (`32690b5`) |  Oracle | Round 2 vs oracle |
| ------------------- | ----------------------: | ------------------------: | ------: | ----------------: |
| startup (`-f gcc`)  |                  3.0 ms |                    3.6 ms | 13.5 ms |              3.8× |
| small               |                 26.6 ms |                   17.7 ms |  115 ms |              6.5× |
| medium              |                  314 ms |                    166 ms |  1.40 s |              8.4× |
| large               |                  1.32 s |                    475 ms |  6.22 s |             13.1× |
| many (120 files)    |                  676 ms |                    575 ms |  3.84 s |              6.7× |
| peak RSS medium     |                 131 MiB |                    53 MiB | 251 MiB |                   |
| peak RSS large      |                 526 MiB |                   122 MiB | 1.2 GiB |                   |
| instructions medium |                 1.277 G |                     739 M |         |                   |
| instructions large  |                 4.535 G |                   2.155 G |         |                   |

Verification of that head: 1 524 tests, gate 2 048 agree and 0 diverge, fuzz seeds 0 and 156 clean, snapshot 4 026 entries unchanged, `-f gcc` and `-f json1` byte-identical to the oracle on every corpus script.

**[⬆ Top](#idtop)**

## 7.3 2026-10-11: lazy CFG associations and allocation-free traversal

Compared with the release binary at `c0e72e70`. Five shuffled runs per workload, one warm-up, CPU 0, `--norc -s bash`, medians, no confidence intervals. Omarchy is pinned to `077ac1da939d`: 1,228 shell files, 119,468 lines.

| Workload                  |     Before |      After | Speedup | Peak RSS before → after |
| ------------------------- | ---------: | ---------: | ------: | ----------------------: |
| 2-line script             |    2.47 ms |    2.45 ms |   1.01× |           6.2 → 6.3 MiB |
| 170-line script           |   12.65 ms |   11.46 ms |   1.10× |           8.9 → 9.2 MiB |
| 1,632-line script         |  112.58 ms |  103.60 ms |   1.09× |         48.8 → 44.3 MiB |
| 4,337-line script         |  369.20 ms |  307.01 ms |   1.20× |       109.8 → 103.5 MiB |
| 120 scripts / 9,107 lines |  395.85 ms |  357.62 ms |   1.11× |           9.6 → 9.1 MiB |
| 200 nested if statements  |   83.56 ms |   15.70 ms |   5.32× |         30.6 → 12.2 MiB |
| 400 nested if statements  |  356.37 ms |   33.83 ms |  10.53× |         98.5 → 19.2 MiB |
| 800 nested if statements  | 1560.40 ms |   77.87 ms |  20.04× |        367.9 → 37.5 MiB |
| All Omarchy, GCC          | 4934.84 ms | 4442.69 ms |   1.11× |         56.3 → 56.0 MiB |
| All Omarchy, JSON         | 5041.36 ms | 4583.16 ms |   1.10× |         56.0 → 56.0 MiB |

What changed: whole-subtree redirection searches are skipped when no relevant redirection exists; eagerly expanded ancestor and node pairs became per-token ranges with a lazily materialised `NodeAssociations`; one shared child-order definition serves the collecting, mutable, allocation-free and short-circuit visitors. Callgrind: the 4,337-line workload fell from 1.633 G to 1.308 G instructions; nesting depth 800 from 7.895 G to 0.455 G. Across Omarchy, instructions fell 19.0 % and allocation calls 22.4 %. Doubling nesting depth costs 2.59× instructions; before the change it cost 3.99×.

**[⬆ Top](#idtop)**

## 7.4 2026-10-11: bounded workers, shared snapshots and fewer parser allocations

Compared with the release binary at `3ad86e18`, same method, `--norc`:

| Workload                      |    Before |     After | Before / after | Peak RSS before → after |
| ----------------------------- | --------: | --------: | -------------: | ----------------------: |
| 2-line script                 |   2.28 ms |   2.32 ms |          0.98× |           6.2 → 6.1 MiB |
| 170-line script               |  10.41 ms |  10.02 ms |          1.04× |           9.1 → 9.2 MiB |
| 1,632-line script             | 115.34 ms | 102.50 ms |          1.13× |         42.9 → 41.4 MiB |
| 4,337-line script             | 277.60 ms | 281.35 ms |          0.99× |        100.8 → 97.9 MiB |
| 120 scripts / 9,107 lines     | 289.99 ms | 264.16 ms |          1.10× |           9.0 → 9.0 MiB |
| 800 nested if statements      |  56.20 ms |  46.82 ms |          1.20× |         31.8 → 29.7 MiB |
| All Omarchy, GCC diagnostics  |   4.292 s |   3.483 s |          1.23× |         54.0 → 51.9 MiB |
| All Omarchy, JSON diagnostics |   3.581 s |   3.385 s |          1.06× |         54.2 → 52.0 MiB |

Worker throughput on the full Omarchy sweep, GCC output, eight-CPU affinity set:

| Jobs |  Before |   After | Before RSS | After RSS |
| ---: | ------: | ------: | ---------: | --------: |
|    1 | 3.539 s | 3.204 s |   54.6 MiB |  51.9 MiB |
|    2 | 1.847 s | 1.681 s |   84.9 MiB |  76.6 MiB |
|    4 | 0.980 s | 0.892 s |  128.7 MiB | 119.7 MiB |
|    8 | 0.591 s | 0.540 s |  208.6 MiB | 203.7 MiB |

What changed: ordinary file reads bypass the stdin-cache mutex; a bounded queue holds at most two pending specs per worker while the producer resolves inputs in order; CFG snapshots share exit-code sets through `Rc`; token and parent maps use `IdMap`; the parser's write-only `reach_pos` field is gone. Validation: 2,145 workspace tests, 2,086 oracle comparisons and 2,000 seeded fuzz inputs with zero divergences, 4,062 snapshot entries unchanged.

**[⬆ Top](#idtop)**

## 7.5 Method

- Instruction counts from callgrind (`valgrind --tool=callgrind`, `-f gcc` on a corpus script) are the before and after currency: deterministic and unaffected by load. Wall time and peak RSS are measured only when nothing else runs.
- Peak RSS comes from a separate GNU `time` run per binary and workload. Python's `wait4` reading includes a launcher floor and is not used.
- `callgrind_annotate --inclusive=yes` reports more than 100 % for recursive frames; read the non-recursive caller's row.
- `conformance bench` reports `params-other` and `resolve` as differences of totals; they jump between runs. `parse`, `cfg` and `checks` are timed directly.
- Invariants for any change: gate 0 divergences, fuzz 0 divergences, snapshot unchanged or regenerated with a reason, and the CFG analysis stays a port of `CFGAnalysis.hs` (versions, cache, invocation paths, merge and patch semantics, observable iteration order). Change representations and keep the algorithm.

**[⬆ Top](#idtop)**

## 7.6 Open work packages

- WP-R5: `Ctx::invocations` is a `HashMap<Vec<Node>, _>` with `RandomState`, iterated into the merge order for nodes that occur in several invocations. Haskell's `M.Map` iterates by key. Switch to `BTreeMap<Vec<Node>, _>`, then gate, fuzz several seeds and snapshot.
- Parser: `Vec<Context>::clone` in `try_parse`, `sub_parser` and `read_pending_heredocs`; `pending_heredocs` and `heredoc_bodies` cloned per `try_parse`.
- CFG build: `remove_unnecessary_structural_nodes`, the `BTreeSet<Node>` inserts for `id_to_nodes`, `memcmp` on `Rc<str>` keys inside `OrdMap`.
- Checks: `caai_get_associative_arrays`, `check_pipe_to_nowhere`, `check_redirect_to_same`, `check_number_comparisons`; `ForShell` as one check resolving the shell once.

**[⬆ Top](#idtop)**

<a name="idend"></a>
