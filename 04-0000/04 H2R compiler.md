<a name="idtop"></a>

# 4 H2R compiler

*The Haskell → Rust compiler. Branch `h2r-compiler`, [PR #2](https://github.com/kjanat/shellcheck-rs/pull/2).*

Goal: turn upstream ShellCheck into a native Rust program **without hand-porting it** and without a GHC runtime clone. GHC does what it is good at (parse, typecheck, desugar, simplify, demand analysis, worker/wrapper, specialisation); the compiler consumes **optimised Core** dumped by a GHC plugin, normalises it in a closed world, lowers it to a proof-carrying IR ("NIR") and emits Rust against a small lazy runtime (`h2r-rt`). The authoritative document is `compiler/README.md` on the branch (long, with per-milestone accounting); `todo.md` lists open items.

## 4.1 Pipeline

```
ShellCheck Haskell
   │ GHC: parse / typecheck / desugar / simplifier / demand analysis / worker-wrapper / specialisation
   ▼
 Core ──h2r-plugin──► <Module>.core.json      (compiler/h2r-plugin, dump format 6)
   │ closed-world normalisation: dictionary erasure, monomorphisation, transformer collapsing,
   │ residual-laziness classification
   ▼
 strict typed IR (NIR, in h2r-lower)
   │ ownership/escape inference, emission
   ▼
 Rust crates (generated into the layer crates) ──cargo──► rshellcheck
```

Libraries are compiled into the world from source: `containers`, `transformers`, `mtl`, `base` are rebuilt with the plugin under their installed unit ids (`mise run extract:libraries`), and `h2r extract interfaces` fails unless every rebuilt interface matches the installed one (all 359 do). `parsec` extracts but is not yet loaded by the `lower:*` tasks.

**[⬆ Top](#idtop)**

## 4.2 Crates

*`crates/`.*

| crate                                       | role                                                                                                                                                                            |
| ------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `h2r-cli`                                   | the `h2r` binary: `extract` (program, library, canary, matrix, interfaces), `lower`, surveys                                                                                    |
| `h2r-core-ir`                               | the Core dump model                                                                                                                                                             |
| `h2r-analysis`                              | the M1–M2.4 censuses and proofs (residual laziness, tuple transport, dictionary flow…)                                                                                          |
| `h2r-lower`                                 | NIR, its verifier, specialisation worklist, and the Rust **emitter** (`emit.rs`, `census.rs`)                                                                                   |
| `h2r-rt`                                    | the runtime: `Shared<T>` cells, thunks, closures, constructors, forcing, the stats census; `PERF.md` lives here                                                                 |
| `h2r-alloc`                                 | the binary's allocator (mimalloc, called with plain `mi_malloc` for alignment ≤ 16) as a crate, so the microbench pays the same cost                                            |
| `h2r-build`                                 | drives the extraction/lowering pipeline from `build.rs` scripts, cached layer by layer                                                                                          |
| `hs-libraries`, `hs-shellcheck`, `hs-entry` | the generated-code layer crates (libraries' Core, ShellCheck's Core, the entry point); `hs-shellcheck`'s build also produces the GHC oracle binary under `build/dist-newstyle/` |
| `shellcheck-core`, `rshellcheck`            | the compiled program's library and CLI; `cargo build --release -p rshellcheck` runs the whole pipeline                                                                          |
| `h2r-canary`                                | the differential canary: a declarative fixture table, emitted + compiled + run against the Haskell oracle in parallel (20 838 comparisons, 163 evidence checks)                 |
| `h2r-conformance`                           | gate/fuzz/corpus against the GHC oracle for the compiled ShellCheck binary (`--candidate`)                                                                                      |

**[⬆ Top](#idtop)**

## 4.3 Milestones

*State on the branch.*

- **M1–M2.4** done: residual-laziness census (2242 thunk sites), lazy-argument receivers (8351), Parsec CPS roles, tuple transport vs value (2584 constructions), representation of fields/spines/text, dump format bump, closed-world class-op census (565 dispatch sites, not one dictionary statically known), dictionary and higher-order milestone with independent re-derivation (606 positive claims, 0 disagreements on seven dumps).
- **M3** the lowering: `Main.main`-rooted live set, post-CoreTidy dumps (9795 live / 3957 dead of 13 752 bindings), NIR with explicit `Delay`/`Force`, closures, instruction origins, no `OpaqueCore` fallback. M3d (polymorphism and typeclass specialisation as *instances*) done. Canonical coverage grew from 2624 to 9124 lowered owners as blockers fell (constructors, thunk regions, recursion, closures, specialisation, characters/strings/casts, unboxed tuples, library list functions and predicates, `base` in the world).
- **M4** characters, string literals, casts and the external boundary: done.
- **M5** non-returning calls: recognised from demand evidence; `errorWithoutStackTrace` executes with exact messages; general exceptions and call stacks open.
- **M6** unboxed tuples: done (448 refusals → ~53 remaining of other kinds).
- Whole-program emission works: the compiled ShellCheck is **byte-identical to the GHC oracle on the conformance gate**, and the `rshellcheck` binary is what the bench measures.

Open compiler items (from `todo.md`): IO story (`State# RealWorld`, where IO is supplied), method fields that are cast lambdas, compiling `ghc-prim`/`text`/`filepath`/`regex-tdfa`/`aeson`/`fgl`/`Diff`/`vector` from source, `FCallId` in the dump, non-tail recursion stack cost (560 B/level vs GHC's 18), `Set.insert` loop 10.9× GHC's time, gate-8 attribution, milestone tags.

**[⬆ Top](#idtop)**

## 4.4 Build and verification costs

| step                                                                                    |          time | notes                                                                                                                                                                         |
| --------------------------------------------------------------------------------------- | ------------: | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `cargo test -p h2r-rt`                                                                  |       seconds | unit tests, allocation budgets (`tests/alloc.rs`), layout pins (`tests/layout.rs`)                                                                                            |
| Miri on `h2r-rt`                                                                        |        ~2 min | `MIRIFLAGS='-Zmiri-disable-isolation -Zmiri-ignore-leaks' cargo +nightly miri test -p h2r-rt -- --skip a_million_indirections`; the knot test leaks two allocations by design |
| `cargo test -p h2r-lower`                                                               |      ~1.5 min | emitter tests                                                                                                                                                                 |
| `CI=1 cargo build --release --locked -p rshellcheck`                                    | **25–35 min** | the whole extraction/lowering/emission pipeline plus rustc on ~46 k emitted functions; run alone                                                                              |
| `h2r-conformance gate --candidate target/release/rshellcheck --oracle <GHC shellcheck>` |        ~2 min | 0 differences required                                                                                                                                                        |
| `cargo test --workspace`                                                                |       ~10 min |                                                                                                                                                                               |
| `mise run perf:ab`                                                                      |       minutes | parity, then hyperfine and peak RSS, baseline vs candidate binary                                                                                                             |
| `mise run rt:instrs` (`scripts/rt-instrs.sh`)                                           |         ~10 s | deterministic callgrind Ir/op for the runtime hot paths; no rebuild                                                                                                           |

The binary is 138 MiB (vs 15.5 MiB upstream, 5.3 MiB rust-port). Startup is ~28 ms because of the size and the literal/site tables.

**[⬆ Top](#idtop)**

## 4.5 Key mise tasks

`mise run check` (format, lint, tests, plugin build), `mise run plugin`, `mise run extract` / `extract:libraries` / `matrix`, `mise run lower:leaf|program|coverage|specialize|sites`, `mise run canary` / `canary:extract` / `canary:explain`, `mise run conformance` / `conformance:fuzz` / `conformance:corpus`, `mise run baseline*` (historical dump reconstruction and reports), `mise run proofs`, `mise run perf:ab`, `mise run rt:instrs`, `mise run oracle` (cabal test upstream).

For the runtime optimisation work, see [[H2R Runtime Performance|05 H2R runtime performance]].

**[⬆ Top](#idtop)**

<a name="idend"></a>
