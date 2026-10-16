<a name="idtop"></a>

# 9 H2R compiler

A finished experiment on branch `h2r-compiler`: a Haskell-to-Rust compiler that let GHC parse, type, desugar and optimise ShellCheck, then translated the resulting Core into Rust against a small lazy runtime. The branch's last commit is [`d64c96bd`](https://github.com/kjanat/shellcheck-rs/commit/d64c96bd3159a07c4af66acdc2fedf8b34ad953f) (2026-10-03, a merge of ShellCheck commit `6dce0df`). `compiler/README.md` on the branch documents each milestone; `todo.md` lists what was left open; `crates/h2r-rt/PERF.md` holds the runtime measurements. [Pull request #2](https://github.com/kjanat/shellcheck-rs/pull/2) carried the work.

## 9.1 Pipeline

GHC ran with the `compiler/h2r-plugin` plugin, which dumped optimised Core per module as `<Module>.core.json` (dump format 6, post-CoreTidy structure with pre-tidy demand facts joined on). The compiler normalised that Core in a closed world (dictionary erasure, monomorphisation, transformer collapsing, residual-laziness classification), lowered it to a proof-carrying strict IR called NIR, and emitted Rust crates that compiled to an `rshellcheck` binary. `containers`, `transformers`, `mtl` and `base` were rebuilt from source with the plugin under their installed unit ids.

**[⬆ Top](#idtop)**

## 9.2 Crates on the branch

| Crate                                       | Role                                                                                       |
| ------------------------------------------- | ------------------------------------------------------------------------------------------ |
| `h2r-cli`                                   | The `h2r` binary: `extract`, `lower`, surveys.                                             |
| `h2r-core-ir`                               | The Core dump model.                                                                       |
| `h2r-analysis`                              | The M1 to M2.4 censuses and proofs.                                                        |
| `h2r-lower`                                 | NIR, its verifier, the specialisation worklist and the Rust emitter.                       |
| `h2r-rt`                                    | The runtime: shared cells, thunks, closures, constructors, forcing, the stats census.      |
| `h2r-alloc`                                 | The binary's allocator (mimalloc) as a crate.                                              |
| `h2r-build`                                 | Drives extraction and lowering from `build.rs` scripts, cached layer by layer.             |
| `hs-libraries`, `hs-shellcheck`, `hs-entry` | The generated-code layer crates; `hs-shellcheck`'s build also produced the GHC oracle.     |
| `shellcheck-core`, `rshellcheck`            | The compiled program's library and CLI.                                                    |
| `h2r-canary`                                | The differential canary: a fixture table emitted, compiled and run against the GHC oracle. |
| `h2r-conformance`                           | Gate and fuzz for the compiled binary against the oracle.                                  |

**[⬆ Top](#idtop)**

## 9.3 Milestones

From the README's milestone table and `todo.md`:

- M1: the residual-laziness census, 2,242 potential thunk sites classified against GHC's own demand and cardinality.
- M2 and M2.1 to M2.4: who receives the 8,351 lazy arguments; Parsec's CPS roles proven structurally; 2,584 tuple constructions split into transport and value; constructor fields, list spines and text; the dump format bump; the class-op census of 565 dispatch sites; the dictionary and higher-order milestone with 606 positive claims re-derived independently with 0 disagreements on seven dumps.
- M3: the lowering. 9,795 live and 3,957 dead of 13,752 top-level bindings from a `Main.main` root; NIR with explicit `Delay` and `Force`, closures and instruction origins, no fallback instruction. M3d made the instance (binding plus closed types plus proven dictionaries) the unit of lowering.
- M4: characters, string literals, casts and the external boundary.
- M5: non-returning calls recognised from demand evidence; `errorWithoutStackTrace` executes with exact messages.
- M6: unboxed tuples. Canonical coverage ended at 9,124 lowered and 671 refused owners with `base` in the world. The canary ran 20,838 differential comparisons and 163 evidence checks.

The whole program emitted and compiled, and the compiled ShellCheck was byte-identical to the GHC-built reference on the conformance gate. The tags `h2r-m1` to `h2r-m2.4`, `h2r-dump-v5`, `h2r-dump-v6` and `h2r-a5-linkage-hole` mark the milestones.

**[⬆ Top](#idtop)**

## 9.4 Why it stopped

The runtime optimisation programme in `crates/h2r-rt/PERF.md` (work packages WP1 to WP18) took the compiled program from about 20× slower than GHC's ShellCheck to about 8× slower, and then found that each further package was worth about 2 % of the run. What remained was the representation itself: every constructor cell, closure and argument vector the Core demands, paid for with reference counting and a general-purpose allocator where GHC uses a bump allocator and a generational garbage collector. `todo.md` still lists the open compiler items: the IO story (`State# RealWorld`), method fields that are cast lambdas, compiling `ghc-prim`, `text`, `filepath`, `regex-tdfa`, `aeson`, `fgl`, `Diff` and `vector` from source, `FCallId` in the dump, non-tail recursion at about 560 bytes per level against GHC's 18, and a `Set.insert` loop at 10.9× GHC's time.

The hand-written `rshellcheck` on `master` is the shipped program. The `bench` branch keeps `h2r` as a candidate under a 600-second measurement budget (see [[Benchmark Harness|08 Benchmark harness]]).

**[⬆ Top](#idtop)**

<a name="idend"></a>
