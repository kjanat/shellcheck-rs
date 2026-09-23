# Haskell → Rust compiler for ShellCheck

Goal: turn upstream ShellCheck (Haskell) into a native Rust program without hand-porting it, and without dragging a GHC runtime clone along.

The strategy is to let GHC do everything it is already good at — parsing, type checking, desugaring, simplification, demand analysis, worker/wrapper, specialisation — and to consume **optimised Core**, not surface Haskell. By that point GHC has already proved where laziness is irrelevant, so most of it can be erased before Rust codegen instead of being reproduced with `Thunk<T>` everywhere.

```text
ShellCheck Haskell
      │
      ▼  GHC: parse / typecheck / desugar
    Core
      │  simplifier · demand analysis · worker-wrapper · specialisation
      ▼
  h2r-plugin  ──►  <Module>.core.json
      │
      ▼  closed-world normalisation: dictionary erasure, monomorphisation,
      │  transformer collapsing, residual-laziness classification
  strict typed IR
      │
      ▼  ownership / escape inference, iterator recovery
    Rust
```

## Milestones

|                 |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | state                                                                                                                                                                                                                                                               |
| --------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **M1**          | the residual-laziness census: why does each local binding that survives GHC still exist? 2,242 potential thunk sites, classified and cross-checked against GHC's own demand and cardinality                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | done                                                                                                                                                                                                                                                                |
| **M2 baseline** | who receives the 8,351 lazy arguments — resolution, proven tier, abstraction family                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | done                                                                                                                                                                                                                                                                |
| **M2.1**        | proving Parsec's CPS roles structurally, and feeding the proof back into the census                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | done                                                                                                                                                                                                                                                                |
| **M2.2**        | which tuples are transport and which are values: 2,584 constructions, an independent verifier, a representation-boundary check, the scalar view                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | done                                                                                                                                                                                                                                                                |
| **M2.2.1**      | the generic aggregate def-use walk (`flow.rs`) lifted out of the tuple census, so every later population is a client of one walk                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         | done                                                                                                                                                                                                                                                                |
| **M2.3**        | the representation question for everything else — **b** constructor fields, **c** list spines, **d** text, **e** the independent re-derivation, **f** the views, the provenance, the accounting and the cross-milestone link, **g** the correction to the axiom layer                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    | done                                                                                                                                                                                                                                                                |
| **M2.4a**       | the dump-format bump underneath it: stable global identity, structured types, and `[Char]` moved from a rendered string to `TyCon` identity — with every M1–M2.3 number unchanged                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        | done                                                                                                                                                                                                                                                                |
| **M2.4b**       | the closed-world class-op census: 565 dispatch sites, the 294 mapped 1:1, every class identified — and not one dictionary statically known                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               | done                                                                                                                                                                                                                                                                |
| **M2.4**        | the closed-world dictionary and higher-order milestone, in three separate questions: **can the call target be enumerated** (7 of 565 sites, the dictionary bounded at 118), **can an abstraction boundary use one representation** (5,574 function-valued boundaries, 252 enumerated, 84 one representation, 66 rewritable as one, 68 clones planned per owner), and **can the object disappear** (102 of 191 dictionary values `Erasable`, 36 of 216 parameters `Erasable` and 4 more with a clone, 4 owner-level clones) — **c** whole-program dictionary flow with its own totality domain, **d** higher-order representation agreement, **e** the 41 Parsec edges (0 closed, and why), **f** the independent re-derivation of all 606 positive claims with 0 disagreements on all seven dumps, **g** the views, the provenance, the accounting and the four cross-milestone links, **c′/d′/h** the three corrections | done                                                                                                                                                                                                                                                                |
| **M3**          | The lowering — Core plus the M1–M2.4 proofs to an explicit, proof-carrying NIR and a compiled Rust canary. **a** the `Main.main`-rooted live set, and the finding that the dump's *pre-tidy* naming could not link 112 cross-module references, which made 8,131 dead verdicts conditional. **a′** the dumps regenerated post-`CoreTidy` with the pre-tidy proof facts joined back on: **9,795 live and 3,957 dead of 13,752** top-level bindings, `A5-IN-WORLD-MISSING` **0 on all seven dumps**, 116,029 claims re-derived with 0 disagreements, dump format 6                                                                                                                                                                                                                                                                                                                                                         | The format-6 baseline run and verifier checks are complete. Before/after accounting and site-level attribution remain open; see todo.md.                                                                                                                            |
| **M3d**         | polymorphism and typeclass specialization: the unit of lowering becomes an *instance* — a binding plus the closed types and proven-unique dictionaries its leading lambdas were bound to — interned under a canonical key so recursive cycles terminate, with growth bounded explicitly                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | done                                                                                                                                                                                                                                                                |
| **M4**          | characters, string literals, casts and the external boundary: exact literal values and coercion kinds in the dump, `Char#` as an unboxed scalar, `GHC.CString`'s unpackers, `GHC.Base.(++)`, Core's strict `let`, newtype representation and cast erasure. The `GHC.CString` boundary — 2,359 refused instances — is gone; canonical coverage rises from 5,402 to **8,067 of 9,795** live owners                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         | Characters, string literals and the boundary ranking are complete. Byte-oriented operations, recursive lazy value graphs and partial constructor/primitive application are not started; unboxed tuples are the dominant remaining blocker. See the ranked blockers. |

## Layout

| Path                       | What it is                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `h2r-plugin/`              | GHC plugin (pinned to GHC 9.6.*). Appends a Core pass after the whole optimisation pipeline, runs `CoreTidy` itself and serialises the **tidied** `CoreProgram` to JSON (dump format 6) — so a top-level binding carries, in its own module's dump, the name every downstream module refers to it by — while handing the pipeline back the *original* `ModGuts`. The `IdInfo` CoreTidy discards is joined back on, field by field and binder by binder: the per-binder `demand` on top-level, lambda, `case` and alternative binders, `oneShot` on top-level and `let` binders, and `exported`. Everything else is CoreTidy's finalised value. The dump carries every binder's demand signature, CPR signature, arity and occurrence info, every referenced **external** global Id keyed by stable name, and every type **structurally** in a hash-consed per-module table. Each module gets a `<Module>.tidy-align.txt` sidecar recording the alignment the join was proved against. See [dump format 6](#dump-format-6).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           |
| `matrix.sh`                | Runs `extract.sh` under a matrix of GHC optimisation profiles (into `compiler/matrix/<profile>/`), for `h2r compare`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `extract.sh`               | Driver: stages a copy of the ShellCheck sources, runs upstream's `striptests` (which removes QuickCheck and Template Haskell), builds it with the plugin enabled, and collects the dumps and their alignment sidecars. The tree at the repo root is never touched.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `rust/crates/h2r-core-ir`  | Rust-side model of that JSON. Flattened into an arena on load — iteratively, since Core `App` spines nest far deeper than a stack likes — with parent links and edge kinds, so every later pass is worklist-driven. Owns the canonical identities every analysis reads: which binder a `Var` occurrence refers to (`resolve`; GHC uniques are *not* unique in optimised Core), which imported Id an occurrence links to (its stable name), which `App` an application spine is rooted at (`spine_root`, cast- and tick-transparent), and what each type *is* (`Ty`, with `TyCon` identity and `alpha_eq`). Includes a depth-limited Core pretty-printer.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `rust/crates/h2r-analysis` | Analyses over the arena. Today: the generic aggregate def-use walk every saturated-constructor flow is built on (`flow.rs`), the residual-laziness census (`laziness.rs`), callee resolution and target tiers (`callee.rs`), the shape/position predicates (`shape.rs`), the single binding-site-first signature lookup they all read (`scope.rs`), the structural Parsec-CPS recogniser (`parsec.rs`), the tuple def-use census that separates transformer plumbing from real values (`tuples.rs`, a client of `flow.rs` plus the four tuple-specific rules), the independent re-derivation of every removable tuple verdict (`verify.rs`, which shares nothing with `tuples.rs` but the IR), the normalised scalar view and per-node tuple provenance (`scalar.rs`), the representation-boundary check that says whether all those views can be applied at once (`boundary.rs`), and the cross-milestone link from M1's thunk sites to M2.2's tuples (`link.rs`), and the constructor-field census that says what is evaluated when each field is read (`fields.rs`), and the list-flow census with its explicit library demand-semantics table (`lists.rs`, `lists/axioms.rs`), and the text census that selects the `[Char]` flows out of it and says what the program does with them (`text.rs`, with its own asserted text-head table), and the independent re-derivation of every M2.3 representation verdict whose being wrong would be a miscompile (`verify_rep.rs`, which shares nothing with `fields.rs`, `lists/` or `text.rs` but the IR and does **not** use `flow.rs`), and the per-site representation views with the `h2r show` provenance they share (`views.rs`), and M2.3's own accounting and its cross-milestone link to M1's thunk sites (`m23.rs`), and the closed-world class-op census with its asserted class table (`classops.rs`), and the whole-program dictionary flow with its separate erasure and totality domains (`dictflow.rs`), and the higher-order representation-agreement analysis (`higher.rs`), and the independent re-derivation of every *positive* M2.4 verdict (`verify_m24.rs`, which shares nothing with `classops.rs`, `dictflow.rs`, `higher.rs` or `flow.rs` but the IR, and reads the analyses' verdicts only as the plain data `m24_claims.rs` writes down), and M2.4's per-site and per-boundary views, the `h2r show` provenance they share, the milestone's own accounting and its four cross-milestone links (`m24.rs`). |
| `rust/crates/h2r-lower`    | The lowering. Where `h2r-analysis` *proves* things about the dumped Core, this crate *constructs* the program the proofs licence — it never mutates the arena and never re-derives a fact an analysis already carries. Today: the `Main.main`-rooted reachability graph over the closed world (`reachability.rs`), whose nodes are `(module, BinderId)` top-level binding pairs and whose edges come only from the resolver or from an external stable name, with a shortest witness path for every live binding and a named reason for every dead one; and the independent re-derivation of every one of its claims (`verify.rs`, which shares nothing with it but the IR and five named trusted inputs, and walks *up* the parent links where the census walks down).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `rust/crates/h2r-rt`       | Runtime for *residual* laziness only — `Lazy<T>`, `Shared<T>`. The design rule is that as little of this as possible should survive into generated code.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `rust/crates/h2r-cli`      | The `h2r` driver. Today: `stats`, `binders`, `show` (with both proof objects inline and per-node evidence), `laziness`, `compare`, `parsec` (including `--cfg`, the recovered parser graph), `tuples` (including `--verify`, `--scalar`, `--boundaries` and the milestone accounting), `fields` (the constructor-field census), `lists` (the list-flow census, including `--axioms`), `text` (the text census, including `--heads`), `verify-rep` (the independent re-derivation of the M2.3 verdicts, the milestone accounting and the M1 link), `classops` (the closed-world class-op census: population, the 294 mapping, dictionary sources, origin chains and the evaluation facts), `dictflow` (the whole-program dictionary flow, its erasure verdicts and its clone plan), `higher` (the function-valued boundaries and their representation verdicts), `verify-m24` (the independent re-derivation of every positive M2.4 verdict), `m24` (M2.4's accounting, its residual and its four cross-milestone links in one place), the `--view` / `--view-all` views `fields`, `lists`, `text`, `classops` and `higher` each carry, and `lower --reachability` (M3a's live set, its accounting, its rule table and the verifier's audit, with `--explain <name>` for one binding's witness path or dead reason, `--link <stable name>` for the whole-program linkage of one external name — its single defining binding, its referrers by module and rule, and its witness path — and `--m24-link` for how much of M2.4's residual sits in unreachable code). Later: the rest of the lowering passes.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |

## Usage

```sh
. ~/.ghcup/env                 # GHC 9.6.7 + cabal
./compiler/extract.sh          # → compiler/core-json/*.core.json

cd compiler/rust
cargo run --release --bin h2r -- stats ../core-json --per-module
cargo run --release --bin h2r -- binders ../core-json ShellCheck.Fixer
cargo run --release --bin h2r -- laziness ../core-json                      # the census
cargo run --release --bin h2r -- laziness ../core-json --module ShellCheck.Fixer --explain --thunks-only
cargo run --release --bin h2r -- show ../core-json ShellCheck.Fixer 1287    # Core at a node id
cargo run --release --bin h2r -- parsec ../core-json                        # prove Parsec's CPS roles
cargo run --release --bin h2r -- parsec ../core-json --module ShellCheck.Parser --explain
cargo run --release --bin h2r -- parsec ../core-json --cfg 8106       # one region's graph
cargo run --release --bin h2r -- parsec ../core-json --module ShellCheck.Parser --cfg-all --json
cargo run --release --bin h2r -- show ../core-json ShellCheck.Parser 141341   # + its proof
cargo run --release --bin h2r -- tuples ../core-json                        # tuple flows and fates
cargo run --release --bin h2r -- tuples ../core-json --module ShellCheck.Checks.Commands --explain
cargo run --release --bin h2r -- tuples ../core-json --verify    # the independent re-derivation
cargo run --release --bin h2r -- tuples ../core-json --module ShellCheck.Analytics --scalar 30892
cargo run --release --bin h2r -- tuples ../core-json --module ShellCheck.CFG --scalar-all --json
cargo run --release --bin h2r -- tuples ../core-json --boundaries  # can all the views be applied at once?
cargo run --release --bin h2r -- fields ../core-json                        # constructor fields: what is evaluated, and when
cargo run --release --bin h2r -- fields ../core-json --con OuterToken
cargo run --release --bin h2r -- lists ../core-json                         # list flows: when is a spine demanded, and how much
cargo run --release --bin h2r -- lists ../core-json --axioms                # the library demand-semantics table
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --explain
cargo run --release --bin h2r -- text ../core-json                          # which list flows are text, and what is done with them
cargo run --release --bin h2r -- text ../core-json --heads                  # the text-head table
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --explain
cargo run --release --bin h2r -- classops ../core-json                      # class-op dispatch: which instance, which method
cargo run --release --bin h2r -- classops ../core-json --class Show --explain
cargo run --release --bin h2r -- classops ../core-json --module ShellCheck.Fixer --json
cargo run --release --bin h2r -- verify-rep ../core-json          # re-derive every M2.3 verdict independently
cargo run --release --bin h2r -- dictflow ../core-json                      # whole-program dictionary flow and erasure
cargo run --release --bin h2r -- higher ../core-json                        # function-valued boundaries: can one representation serve each?
cargo run --release --bin h2r -- verify-m24 ../core-json   # re-derive every positive M2.4 verdict independently
cargo run --release --bin h2r -- verify-m24 ../core-json --explain # …listing every refusal one by one
cargo run --release --bin h2r -- verify-rep ../core-json --explain # …listing every refusal, plus the accounting and the M1 link
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.CFG --view 10329   # one construction, field by field
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.AST --view-all --json
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --view 1220  # one flow: cells, consumers, the facts
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --view 11
cargo run --release --bin h2r -- show ../core-json ShellCheck.AST 5293      # + its M2.3 footers
cargo run --release --bin h2r -- tuples ../core-json --module Main --boundaries --explain
cargo run --release --bin h2r -- show ../core-json ShellCheck.Checks.Commands 4714   # + its tuple proof
cargo run --release --bin h2r -- classops ../core-json --view 1154          # one dispatch site, laid out
cargo run --release --bin h2r -- classops ../core-json --view-all --module ShellCheck.Fixer --json
cargo run --release --bin h2r -- higher ../core-json --view 51239           # one boundary: producers, uses, the rule order
cargo run --release --bin h2r -- higher ../core-json --view-all --module ShellCheck.AST --json
cargo run --release --bin h2r -- m24 ../core-json             # M2.4's accounting, residual and cross-links
cargo run --release --bin h2r -- show ../core-json ShellCheck.Fixer 1154    # + its M2.4 footers
cargo run --release --bin h2r -- lower ../core-json --reachability          # M3a: what Main.main can reach
cargo run --release --bin h2r -- lower ../core-json --reachability --explain checkScript
cargo run --release --bin h2r -- lower ../core-json --reachability --json
cargo run --release --bin h2r -- lower ../core-json --reachability --m24-link
cargo run --release --bin h2r -- lower ../core-json --rules                 # the A0-A11 rule table
```

### Executable compiler canary

`mise run canary` runs a complete small pipeline: compile the real Haskell sources in `compiler/canary/` with GHC 9.6.7 and the format-6 plugin; lower the selected pure entries and every dependency; emit standalone Rust; compile with `rustc`; compare against the Haskell oracle. Both `-O1` and `-O0 -fmax-simplifier-iterations=0` drive 92 entries over 4,254 entry/input combinations each, in optimized and overflow-checked builds: **17,016 comparisons**. Signed 64-bit boundaries exercise overflowing arithmetic. Standard output, standard error and exit status are checked. Alongside scalar control flow and lazy bindings, the suite covers sums, products, nested constructor patterns, DEFAULT, case-binder reuse, strict/lazy fields, `Maybe Int`, finite `[Int]` values, recursion, higher-order calls, characters and string literals.

The driver is the `h2r-canary` crate, and its fixture table is `compiler/rust/crates/h2r-canary/src/fixtures.rs`: one row per entry giving the argument grid it runs over and the evidence it must exhibit. **113 evidence checks** run beside the comparisons — 46 in the optimized profile and 67 in the unoptimized one — and each is matched against the `Operation`, `Rule` and `Exit` values in the verified NIR rather than against printed diagnostics, so renaming a pretty-printer label cannot disable one and the compiler reports a check that no longer names anything. The same table records which profile a check belongs to and why: `-O1` folds `ord#`/`chr#` on a literal, folds two adjacent literals into one, moves every branch into tail position and inlines away the dictionary spines, so those checks can only be asked of the unoptimized dump, while a literal GHC floats out to its own top-level binding is looked for across the whole instance closure instead of in the binding that names the fixture. Three entries must be refused rather than answered, and the two recursive values assert the refusal message as well. Entries are emitted, compiled and run in parallel; failures are collected rather than raised, so one run reports everything that is wrong.

Disabling the simplifier in the second profile is deliberate: even ordinary `-O0` rewrites the non-tail cases into tail position. The fixture table requires `EvaluateBlock` in the four non-tail examples' verified NIR there, so a GHC transformation cannot silently remove the feature under test. They cover two branching operands, a branching scrutinee, capture of a previously computed value and branching arguments to a cross-module call. These examples also pass differentially at `-O1`, including the boxed constant CAFs introduced by GHC. The test-only second profile does not change the canonical ShellCheck extraction profile.

`compiler/canary/boxed_checks.rs` compiles against the actual generated Rust in both profiles. Its twenty semantic tests use deferred/instrumented inputs to check unused arguments and constructor fields, unselected/nested/default branches, delayed calls, shared inputs, strict constructor fields, CAF cell identity, nested/shared lazy bindings, recursive captures, reused closures and lazy function producers. The embedded runtime's ten tests also execute in each of the twenty generated modules (**220 test executions per profile**). The directly forced `lazyStrictUse` example is already desugared to a case, so its test checks forcing rather than requiring a surviving let.

Generated Rust, binaries and Core dumps live under `compiler/build/canary/`. The task is rerunnable and regenerates dumps even if Cabal considers its build up to date. No wrapper scripts or temporary worktrees are needed. `mise run canary:explain <entry>` prints one entry's verified NIR, the instances it needs and what its emission produced, for either profile. `h2r emit-rust <dump-dir> [--with <library-dir>]... --entry '<external-stable-name>' --output program.rs` exposes the emitter independently; a refused entry leaves an existing output file untouched.

This is a **pure backend**, not ShellCheck code generation: functions over `Int#`, boxed `Int`, supported algebraic values and function values are emitted only with source-verified NIR and a complete dependency closure. Direct self/mutual recursion, local functions/join points, escaping closures and partial application are supported. `LocalScope` records definitions and body regions; `CallLocal` passes explicit captures and arguments. `MakeClosure` retains code and lexical captures; `Apply` checks argument/result types independently against structured function types. Anonymous lambdas, returned functions and function-valued fields use the same shared lazy carrier. Partial application retains arguments without forcing them; overapplication enters the returned function. Source verification checks lexical visibility, signatures, definition identity, capture order and complete source accounting. Blocks with an unlifted result run in a dispatcher loop, and a lifted tail call returns an indirection that forcing follows in a loop. Non-tail calls and nested forcing use the native stack, which may grow to 80% of physical memory as GHC's does. See [Running against GHC](#running-against-ghc). A polymorphic function is emitted once per instance — the type arguments and dictionaries it is used at — and a class method resolves to its instance where that instance is proven unique; a dictionary that is not proven unique keeps its runtime dispatch, and an unbounded instance chain is refused with the chain that produced it. The target must be 64-bit. GADTs/existentials, newtype casts, unlifted datatypes, unsupported field carriers, recursive value/thunk graphs, ordinary unlifted lets, partial constructor/primitive workers and Haskell `IO` remain unsupported. Integer command-line parsing and printing are explicit test adapters, not translated Haskell `main`; algebraic and function values are internal, not CLI inputs/outputs. The CLI adapter also accepts function aliases and function-producing entries whose full signature takes and returns only Int#/Int. Unsupported entries fail without replacing already-generated code. M3 as a whole remains open.

Recursion fixtures cover self/mutual calls, non-tail tree recursion, list traversal, captured local loops, join points and lazy local arguments. Scalar tail loops run one million iterations in both Rust build modes. Both Core profiles require `LocalScope` and `CallLocal` in the local-loop NIR. Higher-order fixtures cover captured lambdas, top/local partial application, returned functions, function-valued branches/fields, escaping recursive closures, overapplication and eta-reduced entry aliases. After closure support, canonical NIR coverage is **5,395 / 9,795 live bindings**, with 4,400 refusals and 3,957 dead bindings skipped (+57 lowered); `mise run lower:coverage` reuses the unchanged constructor-bearing dumps. Specialization fixtures cover one function at several types, cross-module instantiation, a polymorphic higher-order argument, recursive specialization, a nested type argument, two instances of one class, a default method, a superclass field read, a cross-module class, a parameterized instance and a method used as a value. After specialization the same per-owner measure reads 5,402 / 4,393 / 3,957, and `mise run lower:specialize` reports the instance survey the milestone actually moves. Character and string fixtures cover the code-point round trip at the boundaries, all six `Char#` comparisons, a `Char#` switch, a character in a constructor field, empty, ASCII, non-ASCII and embedded-NUL literals, indexing inside and past the end, appended literals, a shared literal CAF and an undemanded traversal; after them the per-owner measure reads **7,936 / 1,859 / 3,957**.

General constructor lowering requires the optional format-6 `constructors` table: stable constructor/worker/family identities, complete family size, tag, structured worker signature, representation arity and representation-field strictness. The plugin includes complete families referenced by terms, patterns and binder types. Old dumps remain readable, but cannot justify this new lowering without fresh extraction. No pretty-type or constructor-name heuristic supplies missing evidence. Canonical ShellCheck and canary dumps now contain this metadata; the six optimization-matrix profiles have not been refreshed for this addition.

Canonical constructor-metadata refresh (2026-09-21): all 28 `-O1` module dumps were regenerated with GHC 9.6.7. Verified NIR coverage is **5,335 / 9,795 live bindings (54.5%)**, up from 2,860 (+2,475); 4,460 bindings are refused and 3,957 dead bindings are skipped. Reachability linkage and independent verification pass. The report contains 3,226 `Construct` and 250 `MatchData` instructions. This counts verified binding-level NIR, not dependency-closed executable coverage. Reproduce with `mise run lower:coverage`; the report, refusal diagnostic and input/output checksums live under `compiler/build/coverage/`. The task reuses unchanged extraction, whose build tree is `compiler/build/canonical/`, without removing canary artifacts.

`Construct` records the instantiated field types and ordered values. `MatchData` forces only the outer constructor and enters one region with explicit captures, the case binder and the selected fields. Missing/duplicate patterns, wrong families/field types and non-exhaustive cases without DEFAULT are refused. Independent source verification checks constructor identity, type arguments, field order, strictness, lexical captures, every branch and complete node accounting; mutation tests and consistent ID renumbering exercise these checks. `h2r-rt::Data` is a shared lazy node with typed field carriers. Lazy lifted fields retain shared handles; strict representation fields are forced when the constructor is evaluated. Recursive datatype shapes such as lists are supported for finite values; recursive function/thunk graphs are still a separate step.

The boxed carrier uses the existing `h2r-rt::Int`/`Lazy` implementation, embedded from its source into standalone output. Copies share an `Rc` cell; functions returning `Int` defer their body until demanded. Nullary boxed top-level bindings reuse a thread-local cell (the backend is single-threaded). `BoxInt` constructs `I#` from an evaluated `Int#`; `UnboxInt` forces the constructor and extracts its unlifted field, even when that field is unused. Construction requires the exact external `GHC.Types.I#` identity and matching constructor metadata. Cases require either the sole `I#` alternative with one typed field or a strict DEFAULT with no fields. Source verification independently checks fields, case-binder aliases, result types and forcing markers.

`DelayBlock` allocates a shared boxed-Int or algebraic thunk with explicit captures. Captures are retained without forcing; the region executes at most once when demanded. Computed lifted arguments and constructor fields use this operation rather than eager region evaluation. A non-recursive single-binding lifted `let` installs one shared value under a `LazyBinding` marker; variable aliases reuse the existing value without another thunk. Nested lets may capture earlier bindings, and strict positions may consume let expressions. The independent verifier checks lexical scope, sharing, delay versus evaluation, region return types and complete source accounting, including unused right-hand sides. The emitter clones captured handles before moving them into the closure, preserving later uses in the enclosing block. Recursive groups, join points and unsupported RHSs remain refusals; an unused unsupported computation is not silently discarded.

The primitive table recognizes exact external `GHC.Prim` identities for `+#`, `-#`, `*#`, `==#`, `/=#`, `<#`, `<=#`, `>#` and `>=#`, after lexical resolution, with matching `[PrimOp]` metadata and arity. Their fixed `Int# -> Int# -> Int#` signatures are checked against operands and result. NIR records `IntBinary` with ordered operands and source origin; the independent source verifier rejects changed operators, operands and origins. Rust uses wrapping arithmetic and converts comparison results to integer 0/1. Nested Int# computations are evaluated in argument order; supported lifted computations are delayed. No general external-call fallback is introduced.

Tail-position Int# cases lower to `IntSwitch` terminators and typed successor blocks, including nested cases and boxed Int results. Each successor receives explicit environment arguments and the evaluated case binder; no branch captures implicit values or evaluates before selection. The source verifier independently checks patterns, targets, argument order, binder scope, every arm's source subtree and complete node accounting. Rust emits a `match` calling only the selected block helper. One DEFAULT is mandatory; duplicate/out-of-range/non-numeric patterns and constructor alternatives in an Int# switch are refused. Boxed Int cases use the separate forcing rule above.

Non-tail cases in strict positions use `EvaluateBlock`: evaluate a region once, obtain its result and resume the caller's instruction sequence. The continuation is shared rather than copied into each arm; this is a returning region call, not a general SSA join implementation. Captures are explicit typed parameters, including strict local intermediates and shared boxed values. The verifier independently reconstructs lexical captures, checks return types per region, accounts for every block and rejects cyclic/shared source regions or forged call sites. Straight-line single-DEFAULT Int# scrutinees retain the verified move representation. Boxed Int support raises canonical ShellCheck NIR coverage from 2,651 to **2,860 of 9,795 live owners** (+209; 6,935 refused; 3,957 dead skipped), rechecked against the existing format-6 dumps. This measures accepted NIR owners, not complete executable dependency closures; the program task intentionally exits nonzero for remaining refusals.

### First NIR leaves

From the repository root, lower one reachable leaf from an existing dump:

```sh
mise run lower:leaf compiler/core-json --fn '$_in$usageHeader1'
```

To attempt every reachable binding, run `mise run lower:program compiler/core-json`. This prints source-verified NIR for supported owners and an addressed refusal for every unsupported owner, then exits nonzero if any were refused. Dead owners are skipped. Accepted references may still target refused owners: this is a partial lowering pass, not dependency-closed executable output, even with zero refusals. On the canonical format-6 dumps, the first pass lowers 2,618 of 9,795 live owners, refuses 7,177 and skips 3,957 dead owners. These are binding counts, not a percentage of compiler completion. With saturated parameter-only direct calls, this becomes 2,624 lowered and 7,171 refused, with the same live/dead totals.

The single-leaf task invokes `h2r lower --nir --fn '<stable-name>'`. It requires complete in-world linkage and a verified live set, selects one exact unambiguous name, and prints source-verified NIR plus node accounting. Currently supported: literals, parameter returns and references to top-level bindings in the loaded world, with leading type/value lambdas and ticks. A `top-ref` obtains the existing shared value without calling or forcing it; it identifies the target by module and lexical binder. Imports resolve by exact external stable name to one definition; missing or ambiguous definitions are refused. Cross-module types must be closed and structurally equal up to bound-variable renaming: free type variables, internal type-constructor names and opaque type text are refused. Type lambdas become explicit type parameters, not runtime arguments. Type-only application spines (`f @T @U`) on top-level bindings now produce `instantiate-top`, retaining the ordered type arguments without calling or forcing the shared value. This first slice requires closed structured head, argument and result types; parameter-headed type applications remain unsupported. The source verifier checks the target, argument order, substituted result and every application/type-argument node. Kind correctness is trusted from GHC, not re-proved here. Type-only support did not change canonical totals. Saturated direct value calls (`call-top`) now pass existing entry parameters unchanged, without extra forcing. The source checker verifies lexical argument order, closed argument/result types, exact target and GHC's declared arity. Leading closed type arguments followed by parameter arguments (`f @T x`) are supported too: substitution happens before checking value argument/result types, and arity counts only value arguments. Both argument lists and all source nodes are verified. Interleaved type/value spines, free type arguments, computed lifted arguments, partial/over-applications, unknown arity and higher-order calls remain unsupported. The scalar subset described above also supports nested Int# applications and tail-position Int# literal/default switches with nested branches, with executable Rust emission; general runtime calling conventions remain pending. Signature/body type variables are paired by binder position, permitting GHC's alpha-renaming; ambiguous repeated type-variable uniques are conservatively refused. All NIR value types remain in signature scope, while erased type-lambda origins retain the source binders and their kinds. Dead bindings and unsupported forms fail; there is no fallback or claim that the whole program was lowered. NIR output is diagnostic text, not emitted Rust; `--json` is not supported for this mode yet.

Literal value arguments are also supported, including alongside entry parameters. Each literal gets its expected type from the instantiated callee signature and retains its exact source payload and origin; the verifier checks every literal instruction before the call. This relies on GHC's literal typing and introduces no extra forcing. Canonical coverage remains 2,624 bindings.

Top-level references can now be passed as arguments too, including same-module recursive values and imports resolved in the loaded world. Their shared binding identity is preserved without forcing or copying the referenced value. Argument types must match the instantiated callee signature; source verification checks each reference target, origin and position. This raises canonical coverage to 2,651 lowered / 7,144 refused, with 3,957 dead bindings skipped.

## M1 — how much Haskell is left after GHC?

`h2r laziness` classifies every local binding that survives GHC's optimiser and explains *why* it still exists, from two cross-checked sources: GHC's own demand (strict / absent / used-once), occurrence and one-shot information, and a syntactic occurrence analysis of our own (which case alternatives and lambdas sit between the `let` and each use, and what each use *position* demands of the value).

The one principle: emit deferred evaluation only where the optimised Core still demonstrates conditional evaluation that Rust control flow cannot trivially preserve — and note that memoisation is never needed for *correctness* (only genuinely recursive values are); it preserves sharing. Sinking a binding into every use site is always semantically valid.

Headline numbers on the tree at the repo root (GHC 9.6.7, `-O1`). The "before" column is what the census reported until M2.1 stage 2 fixed two bugs in it — occurrences keyed by GHC unique, and spines split by casts; both are described under [M2.1](#m21--proving-parsecs-cps-roles):

|                                                                |              before |                 now | after tuple normalisation | after M2.3 |
| -------------------------------------------------------------- | ------------------: | ------------------: | ------------------------: | ---------: |
| Local bindings after optimisation                              |               6,156 |               6,156 |                         — |          — |
| … functions / join points / values already in WHNF             | 1,883 / 1,119 / 762 | 1,883 / 1,119 / 762 |                         — |          — |
| … strict (`let` the simplifier didn't turn into `case`)        |                 148 |                 148 |                         — |          — |
| … lazy, used at most once / possibly many times                |          39 / 2,134 |          39 / 2,134 |                         — |          — |
| **Potential thunk sites**                                      |           **2,242** |           **2,242** |                 **2,150** |  **2,139** |
| … sinkable into an evaluating position (thunk vanishes)        |                  12 |                  14 |                        14 |         11 |
| … sinkable, but into a lazy argument (thunk moves)             |                 243 |                 254 |                       251 |        248 |
| … … of all the sinkable ones, into mutually exclusive branches |                  56 |                  65 |                         — |          — |
| … … the rest being single-use                                  |                 199 |                 203 |                         — |          — |
| … memo needed to keep sharing                                  |               1,918 |               1,905 |                 **1,816** |  **1,811** |
| … … captured by a many-entry lambda                            |               1,387 |           **1,242** |                 **1,162** |  **1,160** |
| … … shared on one path                                         |                 531 |             **663** |                   **654** |    **651** |
| … genuinely recursive values (knot-tying)                      |                  69 |                  69 |                        69 |         69 |
| Top-level CAFs that are actually string literals               |      2,426 of 2,755 |      2,426 of 2,755 |                         — |          — |
| Genuine top-level thunks                                       |                 238 |                 238 |                         — |          — |

The third column is the [cross-milestone link](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples): 92 of these thunk sites are the lazy selectors of a tuple M2.2 proves removable, independently verifies *and* shows can be removed together with every other removal at the same representation boundary, so they disappear with it rather than needing anything of their own.

The fourth is [M2.3's own link](#the-cross-milestone-link): a further **11** whose right-hand side is a field expression already proven to be a value, a lazy selection over a field proven eager, or a cell of a spine one eager pass consumes — again only where the independent verifier confirms the verdict. The two columns are disjoint by construction, and `remaining + explained-by-tuples + explained-by-M2.3 = 2,242` is asserted. Both criteria are deliberately narrow; each section says what is *not* claimed and why the number is not larger.

GHC's cardinality and our syntactic occurrence analysis agree on 2,291 of the 2,321 thunk candidates they both have an opinion about (9 both-once, 2,282 both-many); GHC says once where the syntax says many 25 times, and the reverse 5 times.

The class split did not move at all: it is decided by GHC's own demand and cardinality, which are per-binder and were never wrong. What moved is *where each binding's uses are*, which is what decides whether a thunk has to be memoised — 145 bindings turn out not to be captured by a many-entry lambda after all, and 132 more turn out to be genuinely shared on a path.

By binder origin, the memo population is mostly compiler-introduced: `ds…` lazy pattern bindings from the desugarer (416, largely the lazy `StateT`/`Writer` tuple plumbing in the checkers), `lvl…` full-laziness float-outs (276 — GHC hoisting work out of lambdas; re-sinking is valid), `eta…` (164), `$d…` dictionaries (94, gone after specialisation). The user-named remainder (955) is dominated by derived `Functor`/`Foldable`/ `Traversable` instance internals in `ShellCheck.AST`, i.e. dictionary- polymorphic code that also dissolves under monomorphisation.

The `let` census cannot see allocations CorePrep would introduce for non-trivial arguments, so those are counted too: 21,670 non-trivial arguments, of which 12,269 are already values (closures, saturated constructors, partial applications), 1,049 sit in strict positions, one in a parameter the callee never uses, and 8,351 sit in lazy fields / lazy parameters / unknown-callee positions — the latter being where dictionary-passing and CPS (Parsec) code shows up.

Conclusions for the architecture: `Lazy<T>` is an escape hatch for a small, well-defined residue (recursive values, plus whichever float-outs are worth keeping shared), not the runtime model. The big levers are, in order, specialisation/dictionary erasure, transformer collapsing, and let-sinking.

## M2 baseline — who receives the lazy arguments?

M2 is *abstraction collapse*: the remaining problem is not laziness but GHC-generated abstraction structure (dictionaries, transformer plumbing, CPS, float-outs) that looks lazy. Before transforming anything, `h2r laziness` instruments every computation in a lazy or unknown argument position (8,351) on three axes:

- **resolution** — what kind of head receives the argument;
- **tier** — what is actually *proven* about the code that runs when the argument is consumed. This is the honest axis: recognising a Parsec continuation by name attributes the site to a pass, it does not resolve the target. Since M2.1 the tier is the better of two *independent* proofs — the syntactic resolution below, and whatever the Parsec CPS recogniser proves structurally — and neither may weaken the other;
- **family** — which abstraction the head belongs to, judged from its defining module and, for local heads, its binding site and name. This catches the *structural* signatures of inlined abstractions, which is how they appear in optimised Core: mtl's newtypes are gone and its binds show up as tuple constructors; Parsec's combinators are inlined and show up as its four continuations being applied.

Every arity and demand-signature question goes through one lookup (`scope::Scope::head_sig`): the binding-site binder for anything bound in the module, the imported-id table otherwise. GHC does not keep the `IdInfo` on occurrence `Var`s of locals current, so reading an occurrence for a local can return stale arity and strictness; the binder at the binding site is authoritative. (Since [M2.4a](#m24a--stable-global-identity-and-structured-types) the id table holds *only* globals, keyed by stable name, so there is nothing there to read for a local at all.) Argument *position*, partial-application *shape* and callee *resolution* all read the same source and cannot disagree. A second guard follows GHC's demand transformer: a signature's argument demands apply only to calls that supply at least the signature's arity. An undersaturated call is a partial application — a function value that holds the argument unevaluated — and claims no strictness (`Position::UnsaturatedArg`, 108 sites, 68 of them `$fApplicativeParsecT2` building parser values).

| Resolution (the syntactic head axis)                 |       |       |
| ---------------------------------------------------- | ----: | ----: |
| known data constructor                               | 3,317 | 39.7% |
| known global function, signature covers the argument | 1,848 | 22.1% |
| known local function, signature covers the argument  |   536 |  6.4% |
| class-op dispatch                                    |   294 |  3.5% |
| higher-order parameter                               | 2,216 | 26.5% |
| global applied past its signature                    |     5 |  0.1% |
| local lambda applied past its parameters             |    27 |  0.3% |
| closure from a known call, target not followed       |    86 |  1.0% |
| closure from a case/let computation                  |    22 |  0.3% |
| imported without signature / non-variable head       |     0 |    0% |

| Target tier                                | resolution only | with the Parsec proof |       |
| ------------------------------------------ | --------------: | --------------------: | ----: |
| exact target proven                        |           5,701 |             **7,800** | 93.4% |
| finite target set proven                   |               0 |                 **8** |  0.1% |
| producer known, returned target unresolved |             118 |                   118 |  1.4% |
| target unresolved                          |           2,532 |               **425** |  5.1% |

The first column is what the head alone proves; the second adds [M2.1](#m21--proving-parsecs-cps-roles)'s structural proof of Parsec's CPS roles, which resolves 2,107 sites the head could say nothing about. The resolution axis is unchanged by it: those 2,107 heads are still higher-order parameters, and still belong to the Parsec normalisation pass.

The 425 that remain unresolved are, exactly:

|     |                                                                                                                                                                                          |
| --: | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 294 | class-op dispatch — enumerated in [M2.4b](#m24b--the-closed-world-class-op-census): all 294 map onto the 565-site class-op population, and every one dispatches on a run-time dictionary |
|  99 | functional arguments of inlined folds and traversals (`f` 55, `f1` 14, `ww` 10, `ds1` 8, and 12 others), deliberately left alone as a control group                                      |
|  22 | closures computed by a `case` or `let` of function type                                                                                                                                  |
|  10 | heads the *name*-based family attribution called Parsec and the structural recogniser rejects: mtl plumbing (`RWST`, `StateT`) outside `ShellCheck.Parser`                               |

The 118 producer-known sites are known-origin closures awaiting target analysis, not proven dynamic: 86 are bound to the result of a call to a known function or constructor, 27 are local lambdas applied past their manifest parameters, 5 are globals applied past their signature. Following a producer's result to the closure it returns is a separate analysis.

| Attributable to                                                           |       |       |
| ------------------------------------------------------------------------- | ----: | ----: |
| Parsec / CPS normalisation                                                | 2,305 | 27.6% |
| constructor-field strategy (`:` 1,310, program constructors 396, other)   | 1,996 | 23.9% |
| transformer collapse (boxed tuples 849, unboxed tuples 472, mtl calls 13) | 1,334 | 16.0% |
| dictionary specialisation (class-op dispatch 294, dictionaries 57)        |   351 |  4.2% |
| ordinary calls with a visible signature                                   | 2,266 | 27.1% |
| unknown                                                                   |    99 |  1.2% |

A `$f…` name with a numeric suffix (`$fApplicativeParsecT2`) is not a dictionary but a floated-out instance-method body that GHC has already dispatched to; it is attributed by module, which moves 172 sites from the dictionary family to Parsec. The "ordinary calls" bucket is dominated by string building — `unpackAppendCString#` (573) and `++` (543) — i.e. diagnostic messages assembled from lazy string appends; a `String` representation decision, not a laziness one.

## M2.1 — proving Parsec's CPS roles

The census puts 2,532 of the 8,351 lazy/unknown argument sites in the "target unresolved" tier, and 2,117 of those have a head that *looks* like one of Parsec's four continuations (`cok`, `cerr`, `eok`, `eerr`) or an eta-expanded parameter (`eta`). That attribution is by name, so it is a diagnostic and nothing more: GHC names *every* eta-expanded parameter `eta` (in `readArray` a head named `eta` is a continuation, not a parser), renames unused ones `ds`, and a binder named `cok` is not evidence of anything. `h2r parsec` replaces the name with a proof.

### The representation, as it survives the optimiser

`ParsecT s u m a` is a function of a state and four continuations. After inlining, the newtype is gone and what is left is a lambda chain whose **parameter types** still say exactly what each parameter is — the plugin dumps GHC's pretty-printed type for every binder, and those types survive optimisation:

```text
\words                                                   -- the parser's own arguments
  eta :: State [Char] UserState                          -- state
  eta :: Token -> State [Char] UserState -> ParseError -> R   -- cok
  eta :: ParseError -> R                                 -- cerr
  eta :: Token -> State [Char] UserState -> ParseError -> R   -- eok
  eta :: ParseError -> R                                 -- eerr
  -> …
```

Discovered from the dump — and then **checked against the types at every region**, since what one dump exhibits is not a property of the representation (`R1-UNPARSER-SIG`, `R1-TRAILING-ERASURE`):

- the five parameters are always **contiguous and in Parsec's own order**, as a suffix of the lambda chain (836 chains are exactly `state·cok·cerr·eok·eerr`, 336 have one leading parser argument, and so on). Order is checked as an embedding into the `cok·cerr·eok·eerr` template and the shape of each continuation is checked position by position against `unParser`'s — `a -> State s u -> ParseError -> r` and `ParseError -> r`, with `a`, `s`, `u` and `r` agreeing across all five. A chain whose continuation types are present in any other order forms no region and is reported;
- `R` is `SCBase m b = ReaderT (Environment m) (StateT SystemState m) b`, which erases to **two trailing arguments** of type `Environment m` and `SystemState`. Eight regions are eta-expanded that far (e.g. `ShellCheck.Parser` node 8104, `\s1 eok eta::Environment m eta::SystemState`), and three continuation calls carry them (node 10115: `eok v s err env st`, five arguments); 28 parser calls carry them too. The permitted count and types are computed *per region* from that region's own `r`, so the 139 regions whose `r` is a bare `m b` may carry none at all;
- **worker/wrapper drops absent continuations**, so a run can be shorter than four and any subset of the slots may be missing (`state·cerr·eok·eerr`, `state·cok·eok·eerr`, …). The run is therefore matched as a *subsequence* of the four-slot template. 1,215 of 1,301 regions keep all four; 26 have more than one embedding, and 20 of those are resolved from the worker/wrapper pair (`R9-WRAPPER-MAP`), leaving 6 with a proven **finite role set** rather than a single slot;
- worker/wrapper also **unboxes `State` into its representation fields**, leaving parser calls with no `State`-typed argument at all (83 calls). A run of continuation-shaped arguments is not on its own evidence of a parser call — an ordinary higher-order function can take two of them — so the missing state has to be *explained*, and the rule says how.

### Rules

Every verdict records the rule that produced it, and every rule states which level of evidence it rests on. The hierarchy, strongest first:

1. **lexical binder identity** — which binder an occurrence resolves to;
2. **structural function / application shape** — lambda chains, spines, case alternatives;
3. **worker/wrapper dataflow** — a wrapper is an eta-expansion of its worker, so roles transfer across the call;
4. **GHC type compatibility** — the five type shapes the representation is made of (`State s u`, `ParseError`, the two continuation shapes);
5. **alpha-normalised textual type comparison** — candidate generation and corroboration only. It can equate two genuinely distinct type variables, so it is only ever used to *refuse* a region, never as the support for a verdict. The dump has carried *structured* types since [M2.4a](#m24a--stable-global-identity-and-structured-types), and `Ty::alpha_eq` is the structural replacement, but **the Parsec rules below are deliberately not migrated yet**: they still read the rendered types, and they stay at this level until a later milestone moves them with its own gate;
6. **binder names** — diagnostics only. Nothing reads one.

| Rule                             | Evidence                         | Meaning                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   |
| -------------------------------- | -------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `R1-LAYOUT`                      | 2 over 4                         | A lambda chain's parameter types carry `State s u` followed by a run of continuation types embedding into the `cok·cerr·eok·eerr` template.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `R1-UNPARSER-SIG`                | 4 over 2                         | Those parameter types *are* `unParser`'s argument list, checked position by position: every ok continuation is `a -> State s u -> ParseError -> r`, every error continuation is `ParseError -> r`, `State` is applied to exactly `s` and `u`, and the run is in `unParser`'s own order. A chain carrying continuation types in any other order forms no region and is reported.                                                                                                                                                                                                                                                                                                           |
| `R1-TYPE-AGREE`                  | 4, 5                             | `a`, `s`, `u` and `r` agree across all five, compared modulo type-variable renaming (GHC prints the same tyvar `b` on one binder and `b1` on the next). A filter on `R1-UNPARSER-SIG`, able only to refuse.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `R1-TRAILING-ERASURE`            | 4                                | A region's trailing parameters, and a call's trailing arguments, are a prefix — by count *and* by type — of what that region's own result type `r` erases to: `ReaderT r m a` is `r -> m a` and `StateT s m a` is `s -> m (a, s)`, so `SCBase m b` erases to `Environment m` then `SystemState`, and a bare `m b` erases to nothing at all. Derived per region from `r`; never a fixed "at most two". GHC's void token `(# #)` is zero-width and is not part of the erasure.                                                                                                                                                                                                              |
| `R2-PARSER-CALL`                 | 2 over 4                         | A call whose *arguments* are a `State s u` followed by a continuation run embedding into the template, plus whatever `R1-TRAILING-ERASURE` allows after it. A data constructor head is never a parser call.                                                                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `R2-UNBOXED-STATE/destructured`  | 1, 2, 4                          | The state argument is absent, and the three arguments standing in its place are the representation fields, in field order, of one `case … of State f0 f1 f2` — the state was destructured at this very call.                                                                                                                                                                                                                                                                                                                                                                                                                                                                              |
| `R2-UNBOXED-STATE/worker-layout` | 1, then the callee's `R1-LAYOUT` | …or the callee is itself a recognised region whose own parameters are (state fields, continuation run) in exactly this order, saturated by this call.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| `R2-UNBOXED-STATE/forwarded`     | 1, then the caller's `R1-LAYOUT` | …or the three arguments are the enclosing worker's own unboxed state, forwarded unchanged.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| `R3-CONT-CALL`                   | 1, 2, corroborated by 4          | A continuation applied to exactly its arity — (value, state, error) or (error). The head's type fixes what each slot means, and every argument whose own type is readable is checked against it.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          |
| `R3-CONT-CALL-TRAILING`          | as above                         | …plus trailing transformer arguments, as many and of exactly the types its own result type erases to (`R1-TRAILING-ERASURE`).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `R3-CONT-CALL-ETA`               | as above                         | …applied to fewer arguments, the shortfall supplied by eta-reduction: the enclosing continuation position owes exactly the missing ones (`\x -> cok v` is `\x s e -> cok v s e`).                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `R3-CONT-RETURNED`               | 1, 2                             | A continuation value returned into a continuation position that owes exactly what it still needs.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| `R4-PROP-CONT`                   | 1, 2                             | A continuation passed unchanged into a continuation slot of a recognised parser call. The ok/err kind must match and is checked on every propagation; the *slot* need not match its own role — the inlined `<?>` passes `cok` into the `eok` slot.                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| `R5-STATE-IN-CONT-CALL`          | 1, 2                             | The state in the state slot of a continuation call.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       |
| `R6-STATE-IN-PARSER-CALL`        | 1, 2                             | The state in the state slot of a parser call.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             |
| `R7-STATE-SCRUTINISED`           | 2                                | `case s of State …`.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| `R8-DERIVED-CONT`                | 1, 4                             | A let-bound value of continuation type inside a region **that dataflow connects to it** is a derived continuation and has to satisfy the same use rules (129 of them; GHC builds partial applications like `let lvl = cok ()`). Connected means its right-hand side mentions one of the region's continuation parameters, its state or its trailing parameters — transitively through other derived continuations, since GHC chains them. Its role is only ever the kind-restricted pair of slots, never a single slot. A let of continuation type that is *not* connected (100 of them) is no evidence of anything: it is excluded from the region's obligations and counted separately. |
| `R9-WRAPPER-MAP`                 | 3 over 1, 2                      | An ambiguous embedding resolved from the worker/wrapper pair: the wrapper's chain carries all four slots (so its own embedding is unambiguous) and its body is one saturated call forwarding its parameters into the worker, which fixes the worker's roles. Only accepted if the resulting mapping is one the worker's own layout already allowed.                                                                                                                                                                                                                                                                                                                                       |

Anything else — stored in a constructor field, returned from something that is not a continuation position, passed to an unknown callee, passed in a slot of the wrong kind, applied to an argument whose type contradicts the continuation's — rejects, and the rejection takes the whole region with it. Chains that carry continuation-typed parameters but do not form a region are recorded too (`skipped`), so nothing disappears silently.

#### Role identity is not role forwarding

Two different facts about a continuation are kept apart and never conflated. A continuation's **role** is what it *is*, fixed once by `R1-LAYOUT` / `R1-UNPARSER-SIG` (and possibly narrowed by `R9-WRAPPER-MAP`). A **forwarding** is a continuation being handed to a parser call in some slot: that chooses a target for one path, and says nothing about what the continuation is. Every edge carries both — `source_role` and `destination` — and no rule ever rewrites a role because of a forwarding. It matters in practice: of 7,242 forwardings on the `-O1` dump, **988 send a continuation into a slot other than its own role** (`<?>` and friends reusing `cok` as the labelled parser's `eok`).

A call's slots come from its argument types, which cannot always tell the consumed pair from the empty pair. Where the callee is a region in the same module whose parameters already have exact roles, the callee is the authority on what its own parameters are, and narrowing the call by it makes 38 further forwarding destinations exact.

### Scoping: uniques are not unique

GHC's simplifier duplicates terms without freshening their binders. `ShellCheck.Parser` has 41,874 binders over only 8,257 distinct uniques — `a1V6r` alone names 1,269 different `wild2` binders — and across the 28 modules, 116,340 binders share 42,572 uniques. Anything keyed by unique therefore merges inlined copies of the same term.

Variable identity is consequently settled once, in the IR: `Module::resolve` walks the module with an explicit environment stack and gives every local `Var` occurrence the `BinderId` that actually binds it; imports resolve to `Ref::Global`, which is linked to the imported-id table by its **stable name** (`$unit$Module$occ`), not by its unique — see [M2.4a](#m24a--stable-global-identity-and-structured-types). No analysis compares a unique at all. `Module::binder_in_scope` and `Module::scoping_violations` check the result against the definition of lexical scope independently, and report 0 violations over all 107,929 local occurrences of the `-O1` dump (and 328,110 of profile D).

This was a real bug, not a hypothetical one: **54,408 of the 107,929 local occurrences — 50.4% — resolved to a different binder afterwards.** The M1 `let` census had been computing use counts, exclusive-branch splits and lambda capture on merged occurrence sets; see the before/after column in [M1](#m1--how-much-haskell-is-left-after-ghc).

The second correction is smaller and purely mechanical: `Module::spine` has always looked through the casts the simplifier leaves inside an application spine, but the census' own "is this a spine root?" test did not, so a spine broken by a `Cast` was walked twice and its inner arguments counted twice — 167 duplicate argument sites out of 21,837. There is now one `spine_root` in the IR, defined as the exact converse of `spine`, and every analysis uses it.

### Results on the `-O1` dump

```text
candidate regions                               1301   (all in ShellCheck.Parser)
proven                                          1301
rejected                                           0
chains with continuation params but no region      0
… with a state parameter in the chain           1296
… with all four continuation slots present      1215
… with trailing transformer parameters             8
… with an ambiguous slot embedding                 6   (26 before R9-WRAPPER-MAP)
derived (let-bound) continuations promoted       129
… let-bound continuations excluded as unconnected 100
```

| Edges by kind                      |               | Edges by rule                   |       |
| ---------------------------------- | ------------: | ------------------------------- | ----: |
| `ConsumedOk` / `ConsumedErr`       | 2,430 / 2,710 | `R2-PARSER-CALL`                | 2,516 |
| `EmptyOk` / `EmptyErr`             | 2,249 / 1,953 | `R2-UNBOXED-STATE/destructured` |    77 |
| `{ConsumedOk\|EmptyOk}` (finite)   |            66 | `R2-UNBOXED-STATE/forwarded`    |     6 |
| `{ConsumedErr\|EmptyErr}` (finite) |            76 | `R3-CONT-CALL`                  | 2,192 |
| `CallParser`                       |         2,599 | `R3-CONT-CALL-ETA`              |    47 |
| role invocations / forwardings     | 2,242 / 7,242 | `R3-CONT-CALL-TRAILING`         |     3 |
|                                    |               | `R4-PROP-CONT`                  | 7,242 |

`R2-UNBOXED-STATE/worker-layout` proves nothing on this dump — every call with an unboxed state is already explained by the destructuring at the call site or by the enclosing worker's own fields — but it is the rule that covers a call to a visible worker from outside any region, so it stays. If none of the three explanations applied, the calls would not be parser calls and the continuations handed to them would reject their regions: dropping just the "forwarded" case costs 5 regions, 6 edges and 13 proven sites.

| The 2,117 Parsec-shaped unresolved sites    |       |       |
| ------------------------------------------- | ----: | ----: |
| exact role proven                           | 2,099 | 99.1% |
| finite role set proven                      |     8 |  0.4% |
| Parsec region recognised, target unresolved |     0 |    0% |
| rejected as non-Parsec / escape             |    10 |  0.5% |

The ten rejects are the whole non-`ShellCheck.Parser` remainder: heads named `eta` whose types are `RWST Parameters [TokenComment] Cache Identity ()`, `RWST r [TokenComment] s Identity b` and `StateT s Identity b` — mtl plumbing that the name-based family attribution called Parsec and the structural recogniser does not. A further **473** proven edges sit at sites *outside* that population (426 exact, 47 finite): heads the census resolves as ordinary local functions because they are let-bound (`lvl…`, and the derived continuations of `R8`). They are reported on their own line and never folded into the 2,117.

### What the type-derived layout checks found

`R1-LAYOUT` used to *assume* the layout this dump exhibits — the five parameters contiguous and in Parsec's order, and "at most two" trailing transformer arguments. Both are now derived from the types at every region and every call, and reported:

```text
R1-UNPARSER-SIG  chains checked against unParser's argument list   1301
  … refused: continuation types are not unParser's                   0
  … refused: a / s / u / r do not agree (R1-TYPE-AGREE)              0
  … refused: continuation order is not cok·cerr·eok·eerr             0
R1-TRAILING-ERASURE  regions with trailing parameters checked        8  (16 parameter(s))
  … refused: not a prefix of the result type's erasure               0
  parser calls carrying trailing transformer arguments              28
  … calls refused that a fixed "at most two" would have taken        0
  continuation calls with trailing arguments (R3-…-TRAILING)         3
  … refused by the erasure                                          0
R8-DERIVED-CONT  let-bound continuations connected to a region     129
  … unconnected: excluded from the region's obligations            100
```

On `-O1` the checks change nothing: all 1,301 regions survive them, the accounting is identical to the digit, and the assumption turns out to have been true. They are not vacuous, though — the erasure is computed per region and it differs between regions: 1,162 regions have result type `SCBase m b` (or its expansion) and may carry exactly `Environment m` then `SystemState`, while **139 regions have a bare `m b`** — the inlined `parsec` library code, where the base monad is still a variable — and may carry *nothing*. The old rule would have let two arbitrary arguments through there.

Across the flag matrix the checks do bite, which is the point of running them. Chains refused because what follows the continuation run is not that erasure: 0 (A), 4 (B), 12 (C), 32 (D, E, F) — typically a *second* representation starting again (`State [Char] UserState`, a value, another `ParseError -> …`), which is not one clean `unParser` argument list. Calls refused that a fixed "at most two" would have taken: 0, 0, 2, 58, 22, 37. Nothing on any profile is refused by `R1-UNPARSER-SIG` or `R1-TYPE-AGREE`: the continuation types themselves really are `unParser`'s everywhere, which is the assumption worth having checked. GHC's void token `(# #)` — which `-fno-full-laziness` and `-fexpose-all-unfoldings` leave on nullary workers — is zero-width and is excluded from the erasure; counting it as a trailing argument would have refused 5 further chains on C and 166 on D.

`R8`'s connectivity requirement is the one that moves the `-O1` numbers. 100 of the 229 let-bound continuation-typed binders inside regions have no dataflow connection to the region they sit in, and promoting them was loading regions with obligations they never owed. Excluding them costs 200 edges (6 invocations, 194 forwardings) and **changes no cell of the accounting**: the population stays 2,117 = 2,099 exact + 8 finite + 0 region-unresolved + 10 rejected, and the 473 proven edges outside the population stay 473 (426 exact, 47 finite). Their *types* are still read when a call to one is classified — that is what keeps the region's state explained where it is passed to one — they simply prove nothing and can reject nothing.

### Auditing one site

`h2r show` loads the proof object by default for a module that has regions (`--no-parsec` turns it off). It annotates region entries, role binders, their occurrences and the spine roots of proven edges inline, and prints the evidence for the node asked about:

```sh
$ h2r show compiler/core-json ShellCheck.Parser 141341 --depth 1
-- in top-level binding readVariableName, node 141341
eta[#141341]{Cok of region 5}

node 141341
  normalized as: Parsec::EmptyOk
  continuation: eta (binder #41249, region 5 entry node 61)
  intrinsic role: Cok; this use: Forward into slot Eok
  evidence:
    R1-LAYOUT: lambda parameter 2 of region entry 61, type [Char] -> State s u -> ParseError -> m b
    R1-UNPARSER-SIG: that region's unParser argument list: state State s u, value [Char], result m b
    R4-PROP-CONT: eta forwarded unchanged into slot Eok of the parser call at node 141301
```

That is the `<?>` case in full: the binder *is* the region's `cok`, and this use forwards it into the labelled parser's `eok` slot. The two facts are printed separately and neither is derived from the other.

### The recovered graph

`h2r parsec --cfg <region-entry-node>` (or `--cfg-all --module M`, and `--json` for either) prints the region's control-flow graph: its parameters with their roles, and every edge — each terminator with the values it hands back, and each parser call with the continuation filling every slot, each successor naming where that continuation comes from (own parameter, wrapped lambda, nested region, or derived continuation). Nothing is lowered: the graph is the deliverable.

```sh
$ h2r parsec compiler/core-json --module ShellCheck.Parser --cfg 11028
region 458 of ShellCheck.Parser — entry node 11028 (PROVEN)
  unParser: state State String UserState, value Token, result SCBase m b (erases to 2 trailing argument(s))
  parameters
    #13751  ds           argument       :: Token
    #13753  eta          state          :: State String UserState
    #13754  eta          Cok            :: Token -> State String UserState -> ParseError -> SCBase m b
    #13755  eta          Cerr           :: ParseError -> SCBase m b
    #13756  eta          Eok            :: Token -> State String UserState -> ParseError -> SCBase m b
    #13757  eta          Eerr           :: ParseError -> SCBase m b
  edges
    EmptyErr(err=#43485) at node 41700   [R3-CONT-CALL, eta role Eerr]
    CallParser(parser=$fApplicativeParsecT2#43480, state=eta#41713, cok←eta (own param #13754, role Cok), cerr←eta (own param #13755, role Cerr), eok←eta (own param #13756, role Eok), eerr←eta (own param #13757, role Eerr)) at node 41703   [R2-PARSER-CALL]
  2 node(s), 6 region edge(s) accounted for, 0 unplaced
```

Every parameter appears exactly once and every edge of the region appears in exactly one line — the four forwardings above are folded into the call whose slots they fill, and `unplaced` reports any edge that is not accounted for (it is empty for all 1,301 regions).

The 99 non-Parsec fold/traversal callbacks (`f`, `f1`, `ww`, `ds1`, …) are left alone as a control group: none of them is recognised.

### Feeding the proof back into the census

`Callee` carries a third, orthogonal field: what the recogniser proved about the call. `Resolution` and `Family` keep saying exactly what they said — the head is still a higher-order parameter, the site still belongs to the Parsec normalisation pass — and the **tier** becomes the better of the two independent proofs, so neither can weaken the other. (Before this rule was `min`, the recogniser's coarser "one of two slots" was downgrading 43 sites the census already resolved exactly.)

The accounting closes two independent ways:

- **by difference** — 2,532 sites were in the unresolved tier; 2,107 are now proven (2,099 exact + 8 finite, i.e. precisely the population's proven sites); 2,532 − 2,107 = **425** remain;
- **by enumeration** — 294 class-op dispatch + 99 fold/traversal callbacks + 22 computed closures + 10 Parsec rejects = **425**.

Both come to the same number, itemised in the [M2 residual table](#m2-baseline--who-receives-the-lazy-arguments).

### M2.1 acceptance

**The criterion is that every site the Parsec normalisation pass will transform is structurally proven — not that coverage is high.** A site the recogniser cannot prove has to end up in a named bucket with a machine- readable reason, and a "proven" verdict has to follow from a stated rule over the Core; binder names are diagnostics and nothing reads one. Coverage is a consequence, reported but secondary.

Against the `-O1` dump, all of the following hold.

**The population is partitioned.** Of the 2,117 census sites whose head is Parsec-shaped and whose target the head alone cannot resolve:

|                                             |           |       |
| ------------------------------------------- | --------: | ----: |
| exact role proven                           |     2,099 | 99.1% |
| finite role set proven                      |         8 |  0.4% |
| Parsec region recognised, target unresolved |         0 |    0% |
| rejected as non-Parsec / escape             |        10 |  0.5% |
| **population**                              | **2,117** |       |

The four buckets are disjoint and exhaustive by construction (one `Bucket` per site) and the sum is asserted, not eyeballed.

**The census tiers, after feeding the proof back:**

| Target tier                                | resolution only | with the Parsec proof |       |
| ------------------------------------------ | --------------: | --------------------: | ----: |
| exact target proven                        |           5,701 |             **7,800** | 93.4% |
| finite target set proven                   |               0 |                 **8** |  0.1% |
| producer known, returned target unresolved |             118 |                   118 |  1.4% |
| target unresolved                          |           2,532 |               **425** |  5.1% |

**The residual closes both ways.** By difference: 2,532 − 2,107 proven (2,099 exact + 8 finite) = **425**. By enumeration: 294 class-op dispatch + 99 fold/traversal callbacks + 22 computed closures + 10 Parsec rejects = **425**. The 2,107 are reported as a note beside the tier table, not as a sub-row of the 425 — they are what left that tier, not part of it.

**Every rule states its evidence level**, and no rule rests on a weaker level than it claims:

| Level | Evidence                                 | Rules                                                                                                             |
| ----- | ---------------------------------------- | ----------------------------------------------------------------------------------------------------------------- |
| 1     | lexical binder identity                  | `R3-CONT-CALL`, `R3-CONT-CALL-ETA`, `R3-CONT-RETURNED`, `R4-PROP-CONT`, `R5`, `R6`, `R8` (the connection)         |
| 2     | structural function / application shape  | `R1-LAYOUT`, `R2-PARSER-CALL`, `R2-UNBOXED-STATE/*`, `R7`                                                         |
| 3     | worker/wrapper dataflow                  | `R9-WRAPPER-MAP`, and the callee-narrowing of a call's slots                                                      |
| 4     | GHC type compatibility                   | `R1-UNPARSER-SIG`, `R1-TRAILING-ERASURE`, `R8` (the shape), and the argument-type corroboration of `R3-CONT-CALL` |
| 5     | alpha-normalised textual type comparison | `R1-TYPE-AGREE` only, and only to refuse                                                                          |
| 6     | binder names                             | nothing                                                                                                           |

**What the two new checks found** is above under [type-derived layout checks](#what-the-type-derived-layout-checks-found): on `-O1`, `R1-UNPARSER-SIG` and `R1-TRAILING-ERASURE` refuse nothing and confirm the assumption they replace (the erasure is nevertheless region-specific — 139 regions may carry no trailing argument at all); `R8`'s connectivity requirement excludes 100 of 229 let-bound continuations, costing 200 edges and moving no accounting cell.

**One rule fires on nothing here.** `R2-UNBOXED-STATE/worker-layout` proves nothing on `-O1` (it is exercised by a unit test, and does fire on profiles C and D). It covers a call to a visible worker from outside any region, so it stays — dropping the sibling "forwarded" case costs 5 regions, 6 edges and 13 proven sites, which is the scale of what an unexplained missing state costs.

**What remains, and what each thing is waiting for:**

|     |                                                      |                                                                                                                         |
| --: | ---------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------- |
| 294 | class-op dispatch                                    | closed-world instance enumeration ([M2.4b](#m24b--the-closed-world-class-op-census): enumerated, none statically known) |
|  99 | functional arguments of inlined folds and traversals | deliberately untouched control group; a *residual*, not a proof                                                         |
|  22 | closures computed by a `case` or `let`               | returned-closure analysis                                                                                               |
|  10 | mtl plumbing outside `ShellCheck.Parser`             | rejected by the recogniser; the name-based family attribution called them Parsec                                        |
| 118 | producer known, target unresolved                    | following a producer's result to the closure it returns                                                                 |

**How to audit a site.** `h2r show <dir> <module> <node>` prints the Core around the node with the proof object's marks inline and the node's own evidence — rule ids, source nodes, the binder, and intrinsic role and destination slot separately — as a footer; `h2r parsec <dir> --cfg <entry>` prints the whole region's graph, parameters and edges, with every successor named. Both are shown above. `h2r parsec --explain` lists every region's evidence, edges and rejects, and every population site that is not an exact edge.

## M2.2 — which tuples are transport, and which are values

The [M2 census](#m2-baseline--who-receives-the-lazy-arguments) attributes 1,321 lazy argument sites to boxed (849) and unboxed (472) tuples and files them under "transformer collapse". That is an attribution *by constructor*, and a constructor is not a proof: `(a, b)` is not intrinsically transformer noise — ShellCheck puts pairs in `Map`s, in constructor fields and in its own return types. `h2r tuples` replaces the constructor with **def-use**.

Argument sites are also only part of the population. A tuple is constructed just as often as a `let` right-hand side, as a case alternative's result, or as a function's return value — and the M2 census, which walks argument positions, sees none of those. Stage 1 therefore censuses **every saturated tuple construction**, boxed and unboxed separately, and maps the 1,321 onto it afterwards.

Stage 2 then tried to break it. The acceptance rule of this milestone is that **every tuple that will be removed has a complete def-use proof**; coverage is secondary, because a wrong "removable" is a miscompile and a wrong "Preserve" is only a missed optimisation. So stage 2 wrote a [second, independent verifier](#the-independent-verifier) of every removable verdict, went looking for [eight shapes](#the-adversarial-cases) a removable verdict could be wrong on, made the [tuple-in-tuple](#tuple-in-tuple) rule consistent, [read the Parsec proof object](#coupling-the-two-proof-objects) instead of giving up on its continuations, split the residual by what is holding the value, and removed a fate whose name claimed more than its rule proved.

Stage 3 turns the verdict into a **view** and closes the accounting. For every removal it prints [what replaces the tuple](#the-normalised-scalar-view), line by line, with the rule and the source nodes — and asserts that the view is complete, the way the recovered Parsec graph asserts that no edge is unplaced. It puts the same provenance [inline in `h2r show`](#auditing-one-construction), states the milestone's `before = normalised + preserved + unsupported` [accounting](#accounting) — where *normalised* means removable **and** independently verified, so a verdict with only one proof behind it counts as unsupported — and measures [how much of M1's residual laziness](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples) this milestone actually explains.

Stage 4 asks whether all those views can be applied **at the same time**. Each is complete for its own flow; a formal parameter and a function's result are shared slots, so a removable tuple that reaches one has to agree with everything *else* that reaches it. `boundary.rs` enumerates every [representation boundary](#composing-the-views-can-all-1453-be-applied-at-once) a removable flow crosses and every producer of it — from the IR's occurrences, not from the flow walk — and downgrades every flow that crosses one the producers do not agree on. Still no Rust and still no rewrite of the Core: the proof and the view are the deliverable.

### The population, and why the name is not the proof

A construction is selected by `T0-TUPLE-CON`: the head of an application spine is a data constructor from `ghc-prim` whose occurrence is `(,…)` in `GHC.Tuple*` or `(#,…#)` in `GHC.Prim`, whose `repArity` agrees with the name's comma count, whose fields are all lazy, and which is applied to exactly `repArity` value arguments. The name *selects* (evidence level 6); the saturation (2) and the `DataConInfo` (4) are what the rest of the analysis reads, and **no fate is ever decided by a name**. Tuple constructors that are *not* a saturated construction are recorded separately, so nothing disappears silently; on the `-O1` dump there are none at all — every tuple constructor in 28 modules is applied to exactly its fields.

### Following the value

Each construction gets a `TupleFlow`, built by a worklist over **value locations**. A location is a node *plus the number of value arguments still owed* before the tuple appears: 0 means the node's value is the tuple, `k` means it is a closure that returns the tuple after `k` more arguments. That debt is what lets the walk leave a function — ascending past a lambda raises it, a call site that pays it exactly is a location of the tuple again — and it is why the analysis is interprocedural from the first construction it looks at. The two shapes the dump is full of both need it:

- a lazy-RWS step returns its result triple, so its consumer is whoever calls the enclosing lambda, and that lambda is usually *inside* a case alternative rather than bound directly (`$wchecker = \cmd -> case … of Just x -> \eta2 eta3 -> (,,) …`), so the debt is paid three arguments up;
- a CPR worker returns `(# _, _ #)` and each call site scrutinises it.

The walk is a worklist with an explicit stack, like every other traversal here, keyed on (node, debt) so it terminates; a location budget (20,000) turns a pathological flow into an honest `Unresolved` rather than a hang. On `-O1` nothing comes near it — the largest flow visits 2,023 locations and the mean is 19 — but on the inlining-heavy profiles the transitive [tuple-in-tuple](#tuple-in-tuple) rule does reach it: 4 flows on B and 2 each on C–F end as `flow-exceeded-the-location-budget`. That is a coverage loss in the safe direction and the independent verifier refuses those flows too.

### Rules

| Rule                   | Evidence                             | Meaning                                                                                                                                                                                                                                                                                        |
| ---------------------- | ------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `T0-TUPLE-CON`         | 2 over 4, name selects only (6)      | The population: a saturated application of ghc-prim's boxed or unboxed tuple constructor, `repArity` agreeing with the name and all fields lazy.                                                                                                                                               |
| `T1-LET-BOUND`         | 1                                    | The value is a `let`/top-level right-hand side: its uses are that binder's resolved occurrences.                                                                                                                                                                                               |
| `T2-SCRUTINISED`       | 2                                    | `case t of (a, b) -> …`, with exactly *arity* field binders: taken apart, the box does not survive the match.                                                                                                                                                                                  |
| `T3-SELECTED`          | 1 over 2                             | …and the alternative returns exactly its *i*-th binder: a field selection, which is how the desugarer turns a lazy pattern `~(b, s, w)` into one selector thunk per field.                                                                                                                     |
| `T4-RETUPLE`           | 1 over 2                             | A construction every one of whose fields is the *matching* projection of one and the same binder: a field-wise copy, recorded as a consumer of the tuple it copies. All *n* scrutinees must resolve to the same binder — two textually equal expressions are not evidence.                     |
| `T5-PASSED-LOCAL`      | 1 over 2                             | Value argument *i* of a saturated call to a binder bound in this module to a manifest lambda chain, which is **not exported and never occurs as a value**: the flow continues at that parameter's occurrences.                                                                                 |
| `T6-RETURNED`          | 2 over 1                             | The value is reached from a binder through a debt of *k* arguments: the binder is a function returning the tuple, and its occurrences are call sites to follow.                                                                                                                                |
| `T7-CALL-RESULT`       | 3 over 1, 2                          | A call site paying exactly the debt: the spine root is a value location of the tuple again. Paying part of it leaves a partial application, which is followed too.                                                                                                                             |
| `T8-CASE-BINDER-ALIAS` | 1                                    | The case binder of a scrutiny aliases the whole tuple; its occurrences are followed, so a match that also keeps the box cannot be mistaken for one that consumes it.                                                                                                                           |
| `T9-STORED`            | 2 over 4                             | A value argument of a saturated data-constructor application: a real allocation holds it.                                                                                                                                                                                                      |
| `T10-OPAQUE-CALL`      | 1, 4                                 | An argument of a call this module cannot see into — an import, class-op dispatch, a partial application, an unknown higher-order callee.                                                                                                                                                       |
| `T11-ESCAPE`           | 2                                    | Any other use, with a machine-readable reason: applied as a function, bound to or returned from an exported binder, a closure handed to a callee or stored in a constructor, a case that is not one full tuple alternative.                                                                    |
| `T12-NESTED`           | 2 over 3                             | A field of *another* tuple whose own fate is proven removable: the box holding it will not exist, so the inner tuple's consumers are the uses of the outer's *i*-th field binder at every scrutiny of the outer — transitively. When the outer is not removable this is `T9-STORED` as before. |
| `T13-PARSEC-CONT`      | the Parsec proof's own level, then 3 | The value argument of a continuation call [M2.1](#m21--proving-parsecs-cps-roles) proves, where that proof also resolves the continuation to lambdas inside this module: the flow continues at their value parameters. The region graph is *read*; no role, slot or edge is re-derived here.   |
| `T14-FORCED`           | 2                                    | `case t of _ { DEFAULT -> … }`: the tuple is forced whole and no field is read. Forcing a constructor application is a no-op, so this neither keeps the box alive nor counts as a read.                                                                                                        |

Two of the rules are about whether the rewrite is *possible*, not about where the value goes, and both were added in stage 2 after the independent verifier refused what stage 1 accepted:

- removing a tuple that is **passed into** a local callee means splitting that callee's parameter, so every call site of the callee has to be visible and rewritable — `T5-PASSED-LOCAL` now requires the callee to be neither exported nor ever used as a value (`callee-parameter-cannot-be-split`);
- removing a tuple that a **closure returns**, where that closure is itself handed to a parameter, would change the parameter's type and therefore every other closure that reaches it — which this flow does not see. That is refused (`closure-returning-the-tuple-is-passed-into-a-parameter`), not guessed.

### Fates

Every construction lands in exactly one bucket, by this precedence:

| Fate            | Rule                | When                                                                                                                                                                                   |
| --------------- | ------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Preserve`      | `F4-PRESERVE`       | A proven real value: stored in a constructor field, held in a partial application, or handed to a function outside the module. An allocation that exists — this wins over everything.  |
| `Unresolved`    | `F5-UNRESOLVED`     | A use the rules cannot follow, with the reason. Never guessed either way.                                                                                                              |
| `WorkerReturn`  | `F2-WORKER-RETURN`  | The tuple crosses a return and **every** consumer reads its fields: a multi-value return.                                                                                              |
| `ScalarReplace` | `F1-SCALAR-REPLACE` | Every consumer reads fields and the box never outlives them, in the function that built it — including where it is passed to a known local callee, whose parameter becomes the fields. |

Passing a tuple *into* a known callee is deliberately not a "return": the box still never outlives its scrutinies, so it stays `ScalarReplace`.

**Stage 1's fifth fate, `StateThread`, is gone.** It separated a returned tuple whose consumers include a lazy selection or a field-wise re-tupling from one that is only ever scrutinised. That is a real difference — it says whether the fields are demanded together or one at a time — but it is not a different *fate*: both are removed the same way, as a multi-value return, and no structural rule distinguishes "a state being threaded" from "a worker's result". Naming a fate after a monad transformer it was not proven to be is exactly the mistake this milestone exists to avoid. So the split is kept as a **fact on the flow** (`TupleFlow::selected`, proved by `T3` and `T4`, reported beside the fate table) and the two fates are one. On `-O1` 279 of the 302 former `StateThread`s are `WorkerReturn` and 23 are now `Unresolved` for the closure-into-a-parameter reason above.

### The independent verifier

`h2r tuples <dir> --verify` re-derives every removable verdict a second time, from scratch, with code that shares nothing with `tuples.rs` beyond the IR (`h2r-analysis/src/verify.rs`: its own selection of the population, its own name test, its own walk). It is deliberately blunt — one verdict, removable or not — and it enumerates, for one construction, every alias the tuple can be reached under (the binder it is bound to, every case binder, the parameter of every local callee it is handed to, the call sites of every function that returns it) and requires that **every occurrence of every alias** is a scrutiny, a lazy selection or a further alias, and that the whole chain is closed within the module.

It found **94 disagreements** on the first run, all reported under one reason, which on inspection were two different things.

- **30 were the verifier being too blunt.** Its first cut refused any function that returns the tuple and does not occur *only* as the head of a saturated call — which also refuses a **partial application** (`let f = handleCommand a b c d` in `ShellCheck.CFG`, then `f` applied to the last two). A partial application is not an escape: the closure is local, the walk follows it, and every one of its own uses is checked. The rule was narrowed to the case that actually blocks the rewrite — a closure handed to a *parameter*, where the parameter's other producers are invisible — which is a weakening of the verifier and is why it is written down here. The 30 are removable and stayed removable.
- **64 were the census over-claiming**, and became the two new rules above: the tuple's own uses are all reads, but the rewrite needs a signature change the flow does not prove is possible. They are now `Unresolved` with a reason, costing coverage rather than soundness.

After that:

| dump                                       | removable verdicts | re-derived | disagreements | refused by [stage 4](#composing-the-views-can-all-1453-be-applied-at-once) |
| ------------------------------------------ | -----------------: | ---------: | ------------: | -------------------------------------------------------------------------: |
| `-O1` (`compiler/core-json`, and matrix A) |              1,206 |      1,206 |         **0** |                                                                        247 |
| B `-O2`                                    |              1,464 |      1,464 |         **0** |                                                                        277 |
| C                                          |              1,360 |      1,360 |         **0** |                                                                        334 |
| D                                          |              2,504 |      2,504 |         **0** |                                                                      1,497 |
| E                                          |              2,538 |      2,538 |         **0** |                                                                      1,497 |
| F                                          |              2,539 |      2,539 |         **0** |                                                                      1,501 |

The two sides also select the *same population* on every dump (0 constructions found by only one of them). The last column is the only thing the verifier accepts and the census refuses: the flows the representation boundary check downgraded after both walks agreed, which is a third rule neither walk has rather than a disagreement between them. Seven of `-O1`'s def-use verdicts (50 on D–F) used the one hop the verifier cannot derive on its own, the Parsec continuation target, supplied to it as an input from the other proof object rather than recomputed; on `-O1` all seven have since been downgraded.

### The adversarial cases

Each shape below has a hand-built regression test in `h2r-analysis/src/tests.rs` *and* a count in the real `-O1` dump, printed by `--verify`, so that a hand-built test is never the only evidence a rule was exercised.

| # | Shape                                                                  | In `-O1` | Example                       | Stage 1                       | Now                                          |
| - | ---------------------------------------------------------------------- | -------: | ----------------------------- | ----------------------------- | -------------------------------------------- |
| 1 | two names for one tuple (let + case binder, or two lets), one escaping |       59 | `ShellCheck.Analytics` 46     | Preserve 2, Unres 22, State 1 | Preserve 2, Unres 57 — never removable       |
| 1 | re-bound under a second `let` binder                                   |      167 | `ShellCheck.ASTLib` 651       | 143 removable, 24 not         | 108 removable, 59 not                        |
| 2 | two or more field reads                                                |    1,246 | `Main` 2737                   | 1,162 removable, 84 not       | 1,020 removable, 226 not                     |
| 2 | read and then stored                                                   |        6 | `ShellCheck.Analytics` 46     | Preserve 6                    | Preserve 6 — the store wins                  |
| 3 | returned from a *recursive* function                                   |      722 | `Main` 2594                   | 638 removable, 84 not         | 555 removable, 167 not; terminates           |
| 3 | threaded into a recursive callee (a `go` accumulator)                  |       19 | `ShellCheck.Analytics` 46     | 9 removable, 10 Preserve      | 3 need a clone, 7 Preserve, 9 Unres          |
| 4 | a field of another tuple, outer removable                              |      115 | `ShellCheck.Analytics` 1974   | **Preserve 115**              | 62 removable, 53 not                         |
| 4 | a field of another tuple, outer not removable                          |       64 | `Main` 422                    | Preserve 64                   | Preserve 64                                  |
| 5 | an unboxed worker return re-boxed by its caller                        |      284 | `Main` 5018                   | 236 removable, 48 not         | 185 removable, 99 not                        |
| 5 | a boxed tuple unboxed into a local callee's parameters                 |       15 | `ShellCheck.Analytics` 46     | 3 removable, 12 not           | 5 removable (3 of them need a clone), 10 not |
| 5 | returned from an exported wrapper of a local worker                    |       11 | `Paths_ShellCheck` 67         | Unresolved 11, unsplit        | Unresolved 11, reason names both binders     |
| 6 | returned from a closure whose call sites are all visible               |      303 | `Main` 3762                   | 450 removable, 3 Unres        | **303 removable**                            |
| 6 | returned from a closure that is stored or consed                       |      248 | `Main` 2220                   | Unresolved 248                | Unresolved 248, split by what holds it       |
| 7 | the callee is a computed (case-selected) closure                       |       12 | `ShellCheck.AnalyzerLib` 3861 | Unresolved 12                 | Unresolved 12 — never one alternative        |
| 7 | a parameter reached from two or more call sites                        |       32 | `ShellCheck.Analytics` 46     | 12 removable, 20 not          | 5 removable, 27 not                          |
| 8 | forced whole (`seq`), no field read                                    |        2 | `ShellCheck.Analytics` 47426  | Preserve 2 (a store wins)     | Preserve 2; the forcing reads no field       |
| 8 | stored in a *strict* constructor field                                 |        9 | `ShellCheck.Analytics` 47426  | Preserve 9                    | Preserve 9 — stored, not scrutinised         |
| 8 | a case that is not one full tuple alternative                          |        0 | —                             | —                             | would be Unresolved                          |

"Removable" is `ScalarReplace`, `WorkerReturn` or `RemovableWithClone` (stage 1's `StateThread` counts as removable in the left column). The "In `-O1`" counts of shapes 1 and 6 are themselves fate-dependent — they ask for a tuple that is *not* removable, or for a closure whose call sites are all visible — so they move when the fates do. Where the two columns differ it is one of the stage-2 changes (the 106 in case 4, the 7 Parsec resolutions, the 64 refusals) or a stage-4 boundary downgrade.

Case 7 is the may-analysis question, and it is answered in two places. A callee *computed* by a `case` is refused outright — picking either alternative would be a guess. Where a parameter is followed, its uses are the union over every call site that reaches it, which can only add consumers: the second test builds a parameter that is scrutinised on one path and stored on another and asserts that the store wins for *both* producers. Case 4 is the one that changed a verdict in the other direction, and case 3's `go`-accumulator test is the one that pins termination.

### Tuple in tuple

Stage 1 called a tuple stored in another tuple's field `Preserve` ("stored-in-a-tuple-field", 179 constructions), which is inconsistent: if the *outer* box will not exist, the inner tuple is not "stored" in anything. `T12-NESTED` makes the two agree. The fixpoint starts pessimistic — every nested tuple `Preserve` — and only ever adds resolved nestings, so a knot-tied cycle cannot bootstrap itself into being removable; on every dump it settles in two rounds.

Of the 179: **106 become removable** (84 `WorkerReturn`, 22 `ScalarReplace`), 73 stay `Preserve` — 71 because the outer is not removable, and 2 because the transitive walk found a *different* escape (one a constructor field, one an imported lazy parameter).

### Coupling the two proof objects

The 50 constructions stage 1 left as "the callee is an unknown higher-order value" are, 48 of them, Parsec continuations in `ShellCheck.Parser` — and M2.1 already proves what those are. `tuples::parsec_hops` reads that proof object (regions, their continuation parameters, the binder each region's chain is bound to) and resolves the *value* of a continuation only when the region graph closes over it: the region's parser is bound to a non-exported binder, every occurrence of that binder is a call saturating the chain exactly, and what fills the slot is a manifest lambda — directly, or through another continuation parameter, followed the same way. Only an `ok` continuation of the three-argument shape carries a value, and the proof object is what says which one this is.

Of the 50: **7 resolve** (4 `ScalarReplace`, 3 `WorkerReturn`), 41 get a reason that names the edge, and 2 are not Parsec at all (`ShellCheck.AnalyzerLib`, `ShellCheck.Formatter.TTY`). The 41 break down as

|    |                                                                                         |
| -: | --------------------------------------------------------------------------------------- |
| 20 | the region's chain is not bound to a binder (it is a lambda written out at a call site) |
| 19 | the region's parser occurs somewhere as a value, so not every call of it is visible     |
|  2 | a call of the region is not saturated exactly                                           |

each recorded as `parsec-continuation-target-not-in-the-region-graph` with the region and the continuation in the detail.

### Results on the `-O1` dump

2,584 saturated constructions — 1,765 boxed, 819 unboxed. Stage 1's numbers are in the "before" columns; every difference is one of the four stage-2 changes above (the two new refusals, `T12-NESTED`, `T13-PARSEC-CONT`, and folding `StateThread` away).

| arity | boxed | unboxed |   | fate          |      before b/u |         now b/u |
| ----: | ----: | ------: | - | ------------- | --------------: | --------------: |
|     2 |   887 |     568 |   | ScalarReplace |         402 / 5 |     **423 / 3** |
|     3 |   718 |     231 |   | StateThread   |        266 / 36 |               — |
|     4 |   156 |       9 |   | WorkerReturn  |        31 / 664 |   **338 / 689** |
|     5 |     0 |       9 |   | Preserve      |         657 / 0 |     **551 / 0** |
|     6 |     3 |       1 |   | Unresolved    |       409 / 114 |   **453 / 127** |
|     8 |     0 |       1 |   |               |                 |                 |
|    64 |     1 |       0 |   | **total**     | **1,765 / 819** | **1,765 / 819** |

1,453 constructions are proven removable by def-use (56%), up from 1,404; of those, 657 have at least one field read on its own and the rest are read whole. Stage 4 ([representation boundaries](#composing-the-views-can-all-1453-be-applied-at-once)) then takes 247 of those 1,453 back, because a def-use proof per tuple is not a proof that all of them can be applied at the same time; the accounting below is the post-boundary one. Unboxed tuples are 84% `WorkerReturn`/`ScalarReplace` and **never** `Preserve` — as they must be, since an unboxed tuple cannot be stored in a lazy field. 551 boxed ones, 31%, are proven real values.

| Consumers                                        | boxed | unboxed |
| ------------------------------------------------ | ----: | ------: |
| Scrutinised                                      |   899 |   2,089 |
| Selected (lazy selector)                         | 1,755 |      60 |
| Returned                                         | 1,825 |   1,271 |
| StoredIn                                         |   501 |       0 |
| NestedIn (a field of a removable tuple)          |   333 |       0 |
| Retupled                                         |   115 |       0 |
| PassedTo (known local, or a proven continuation) |   122 |       0 |
| PassedToUnknown                                  |    86 |       0 |
| Forced                                           |     2 |       0 |
| Escapes                                          |   540 |     168 |

The census' 1,321 tuple-attributed argument sites still map onto this population **one to one** (849 boxed + 472 unboxed, 0 unmapped, over 726 distinct constructions), and their fates are reported on their own:

| The 1,321          |    before b/u |   def-use b/u | after boundaries b/u |
| ------------------ | ------------: | ------------: | -------------------: |
| ScalarReplace      |       114 / 0 |       128 / 0 |          **111 / 0** |
| StateThread        |      225 / 29 |             — |                    — |
| WorkerReturn       |       5 / 435 |     375 / 463 |         **56 / 463** |
| RemovableWithClone |             — |             — |            **2 / 0** |
| Preserve           |       324 / 0 |       144 / 0 |          **144 / 0** |
| Unresolved         |       181 / 8 |       202 / 9 |          **536 / 9** |
| **population**     | **849 / 472** | **849 / 472** |        **849 / 472** |

### What the plumbing actually looks like

Two shapes account for nearly all of the transformer transport.

**The lazy-RWS re-tupling** (`ShellCheck.Checks.Commands` nodes 4714 and 4633, both printed in full by `--explain`): a step returns `(,,) b s w` from `eta1`; its caller binds the result to `ds1` and reads all three fields with lazy selector cases; those three selections are re-tupled into the next step's result (`T4-RETUPLE` at node 4633), which is returned again. The *inner* triple (4714) is a multi-value return — its four consumers are the three selections and the copy, and it crosses a return — while the *outer* copy (4633) is `Unresolved`, because the closure that returns it ends up in a `CommandCheck` constructor, which is the checks-in-a-top-level-list shape the residual is full of. The inner triple is `Unresolved` too *after stage 4*: `eta1`'s return points do not all agree on one representation, so its result cannot become three scalars however complete the triple's own def-use proof is — which is precisely the failure mode [stage 4](#composing-the-views-can-all-1453-be-applied-at-once) exists to find. 467 boxed removable constructions have a field read on its own, concentrated in `Checks.Commands`, `CFG`, `Checks.ShellSupport` and `Analytics`; only 129 constructions are *proven* field-wise copies, so re-tupling is the visible top of a much larger selector population (691 constructions have a `T3-SELECTED` consumer).

**The CPR worker return** (`ShellCheck.Analytics` node 30892): `$wgo` returns `(# () , … #)`, both of its call sites `case` it apart at once. 667 unboxed constructions are multi-value returns; counting boxed and unboxed together, the multi-value returns are concentrated in `Analytics` (291), `CFG` (168), `CFGAnalysis` (99) and `Checks.ShellSupport` (99). The 136 boxed ones are mostly the *other* half of that shape: a caller re-boxing the fields it just unpacked.

### What remains, and what each thing is waiting for

827 constructions are unsupported — 824 `Unresolved` and 3 `RemovableWithClone`. The residual is split by *where* the value went, so the next milestone can pick each class up without re-analysing (the constructor and callee names are diagnostics; the split is by what kind of thing holds it):

|     |                                                                                                                                                      |                                                                                                  |
| --: | ---------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------ |
| 244 | the flow's own proof stands, but a [representation boundary](#composing-the-views-can-all-1453-be-applied-at-once) it crosses is not a uniform split | a representation-agreement pass, or cloning                                                      |
| 187 | the closure that returns the tuple is passed to an **imported** call (`map` 107, `catch#` 25, `$wtext` 20, …)                                        | closure/whole-program analysis                                                                   |
| 134 | …**consed onto a list**                                                                                                                              | the checks-in-a-top-level-list shape; a closed-world list-of-closures pass                       |
| 114 | …**stored in a program constructor** (`CommandCheck` 51, `SystemInterface` 13, `ForShell` 11, …)                                                     | the same, per constructor                                                                        |
|  67 | …**handed to a local callee's parameter**                                                                                                            | the parameter's other producers: a higher-order representation agreement, not a def-use question |
|  41 | a proven Parsec continuation whose target the region graph does not close over                                                                       | above                                                                                            |
|  11 | returned from an **exported wrapper of a local worker**                                                                                              | the *worker's* callers, not the wrapper's — which is why the split exists                        |
|  10 | …passed to a local binder that is not a lambda chain                                                                                                 | returned-closure analysis                                                                        |
|   7 | …held in a partial application                                                                                                                       | the same                                                                                         |
|   3 | …passed to a class-op                                                                                                                                | closed-world instance enumeration                                                                |
|   2 | returned from an exported function with no worker                                                                                                    | callers outside the module                                                                       |
|   2 | an unknown higher-order callee outside `ShellCheck.Parser`                                                                                           | returned-closure analysis                                                                        |
|   1 | the argument lands past the callee's parameters                                                                                                      | the same                                                                                         |
|   3 | …and only a specialised **clone** of the callee could carry the split                                                                                | a cloning decision, which this milestone does not make                                           |
|   1 | the callee's parameter cannot be split (the callee escapes)                                                                                          | closure analysis                                                                                 |

> **Added by [M2.4d](#m24d--higher-order-representation-agreement)**, beside these rows and changing none of them: the 67 land on their callee's function-typed parameter (31 `CloneRequired`, 13 `UniformRepresentation`, 1 `ExactClosure`, 22 with no such parameter at all), so **14 could be reclassified by a later pass**; the 187 land outside the closed world; the 134 and 58 of the 114 land on the one shared `(:)` / `(,)` field slot, and 45 of the 114 on a `Preserve`d record of run-time closures.

The `Preserve` side is 551, dominated by exactly what one would hope: 369 tuples consed into a list, 71 stored in another tuple that is itself a real value, 52 handed to an imported function's lazy parameter (45 of them to `++`), 40 stored in a program or library constructor (`Just` 28, `Bin` 9, …), 19 passed through class-op dispatch.

### Accounting

Asserted in code, not eyeballed (`Accounting::check`): the boxed constructions sum to the boxed fate counts and likewise for unboxed, and every census tuple site either maps onto exactly one construction or carries a reason (`flow.is_some() ^ reason.is_some()`). The nesting fixpoint asserts its own convergence. The same assertions, and the independent verifier, run on all six matrix profiles.

Stage 3 adds the milestone's own equation, per representation:

```text
before = normalised + preserved + unsupported
```

*normalised* is a construction this milestone removes — removable **and** re-derived by the [independent verifier](#the-independent-verifier); *preserved* is `Preserve`; *unsupported* is `Unresolved` **plus any removable verdict the verifier does not confirm**. A construction that only one walk proves counts as unsupported, never as normalised: that is the direction the acceptance rule points. The verifier therefore runs inside `TupleCensus`, not behind `--verify` — it is part of the verdict, and `--verify` only reports it.

*normalised* is narrowed once more by stage 4: a flow that crosses a [representation boundary](#composing-the-views-can-all-1453-be-applied-at-once) that is not a uniform split is not normalised either, whether its own proof holds or not.

```text
M2.2 accounting — before = normalised + preserved + unsupported
                     before  normalised  preserved  unsupported
  boxed                1765         539        551          675
  unboxed               819         667          0          152
  total                2584        1206        551          827
  normalised = removable and re-derived by the independent verifier; 0 removable verdict(s) unverified

  the census' 1321 tuple-attributed argument sites, the same way
  boxed                 849         167        144          538
  unboxed               472         463          0            9
  total                1321         630        144          547
```

The unsupported residual is itemised by the *kind* of thing holding the value (the [table above](#what-remains-and-what-each-thing-is-waiting-for)), and the itemisation is asserted to sum to the unsupported total.

#### Two numbers, two questions — kept apart on purpose

There are two removability numbers in this milestone and they answer different questions. They are separate metrics in `metrics.rs` and separate rows of `h2r compare`, not one number with a caveat attached:

|                                                                   |                                                                                                                                                                                                 |     `-O1` |
| ----------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------: |
| **can this box disappear locally?**                               | the def-use walk proves the construction is transport, on its own terms and before anything is asked about how it composes                                                                      | **1,453** |
| **can it disappear without cloning?**                             | …and every [representation boundary](#composing-the-views-can-all-1453-be-applied-at-once) it crosses is a uniform split, so the removal composes with every other removal at the same boundary | **1,206** |
| …only a specialised **clone** of the callee could carry the split | recorded, and counted as *unsupported*                                                                                                                                                          |     **3** |

The 247 between them is the work a representation-agreement pass would have to do. The **3** `RemovableWithClone` parameter boundaries are the first concrete evidence in this compiler for a cloning pass: a callee whose parameter cannot be split because different callers want different representations, where specialising a copy of the callee would resolve it. **No cloning pass is implemented**, and they are counted as unsupported rather than as a removal waiting to happen.

```sh
$ h2r compare A=compiler/core-json
removable locally (def-use)           1453
removable without cloning             1206
  …only a clone could carry              3
```

### The normalised scalar view

Proving a tuple is transport is not the same as saying what replaces it. `h2r tuples --scalar <construction-node>` (and `--scalar-all`, `--json`) prints the program with that tuple gone, at the level of the IR — nothing is lowered and no Core is rewritten. The construction's fields become named scalars `f0…f{n-1}`; every consumer becomes bindings over them; every line names the nodes it reads and the rule that justifies it:

```sh
$ h2r tuples compiler/core-json --module ShellCheck.Analytics --scalar 30892
ShellCheck.Analytics node 30892 — unboxed (#,#) of arity 2, fate WorkerReturn [verified: yes]
  scalars
    f0     := ()                                       [node 31010]
    f1     := [] …                                     [node 31006]
  normalised
    hop   $wgo#10680 returns (f0, f1) as 2 scalar result(s) — returned from (after 3 more argument(s)) $wgo with 2 occurrence(s)
            [T6-RETURNED]
    bind  at node 30853: (ww#10682, ww#10683) := $wgo … … … at node 30854   [the call returns 2 scalar(s)]
            [T7-CALL-RESULT, T2-SCRUTINISED]
    bind  at node 30897: (ww#10722, ww#10723) := $wgo … … … at node 30974   [the call returns 2 scalar(s)]
            [T7-CALL-RESULT, T2-SCRUTINISED]
  3 consumer(s), 2 call site(s) accounted for, 0 unplaced
```

The shapes, and what each becomes:

| Consumer                                   | Rule                             | The view                                                                                                               |
| ------------------------------------------ | -------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `case t of (a, b) -> e`                    | `T2-SCRUTINISED`                 | `a := f0; b := f1`                                                                                                     |
| a lazy selector `case t of (_, s, _) -> s` | `T3-SELECTED`                    | `s := f1` — and the selector thunk goes with it                                                                        |
| a field-wise re-tupling                    | `T4-RETUPLE`                     | the copy's own fields *are* `f0…`, with that construction's own fate printed beside it                                 |
| passed into a local callee                 | `T5-PASSED-LOCAL`                | that parameter becomes *n* scalar parameters; the call passes `f0…`                                                    |
| returned                                   | `T6-RETURNED` / `T7-CALL-RESULT` | the function returns *n* scalar results, and each call site binds them — `case (f x) of (a, s) -> e` ⇒ `(a, s) := f x` |
| a field of a removable tuple               | `T12-NESTED`                     | the outer box is gone too, so `f0…` reach the outer's readers directly, through the field binder named on the line     |
| forced whole                               | `T14-FORCED`                     | the force disappears; forcing a constructor application is a no-op                                                     |

**The view is complete, and says so.** Every consumer on the flow is placed in exactly one line and every call site the flow proved is placed exactly once; the block ends the way [the recovered Parsec graph](#the-recovered-graph) ends, with `0 unplaced`, and the assertion is in code (`ScalarView::check`). A scrutiny whose scrutinee *is* the call folds the call into its own line, so the multiple-return shape reads as one binding rather than two. `--scalar-all` builds the view of every removable construction — the 1,206 normalised plus the 3 that keep their proof but need a clone: **1,209 on `-O1`, 0 unplaced**, and likewise on all six profiles (1,209 / 1,469 / 1,365 / 2,509 / 2,543 / 2,544).

### Composing the views: can all 1,453 be applied at once?

`scalar.rs` proves each view is complete *for its own flow*. It does not prove that all of them can be applied **simultaneously**, and that is a different question, because a formal parameter and a function's result are **representation boundaries**: one slot, one representation, shared by everything that reaches it.

Suppose parameter `p` of a local function `f` receives removable tuple A at one call, removable tuple B at another, and at a third call an expression that is not a removable tuple at all — a variable of tuple type from an opaque source, the result of an imported call, a parameter of the enclosing function. A and B each have a perfect def-use proof, and the two proofs do not contradict each other. `p` still cannot be *both* two scalars and one boxed tuple. The same holds for a return: a function that returns a removable tuple on one branch and something of unknown representation on another cannot have its result split.

Stages 1–3 do not catch this. `tuples.rs` guards the *callee* (`callee-parameter-cannot-be-split`, `closure-returning-the-tuple-is-passed-into-a-parameter`): the function must be local, not exported and never used as a value, so that every call site is visible and rewritable. That is strictly weaker than proving that every **producer** of the boundary agrees on one representation — and both `tuples.rs` and `verify.rs` follow *the selected tuple* into the parameter, so the assumption is shared by the two walks rather than challenged by the second one. `boundary.rs` is the third proof object that challenges it.

**How a boundary is enumerated — independently of the flow walk.**

- **A parameter** `(f, i)`. Every occurrence of `f`'s binder (`Module::occurrences`) is taken to its spine root (`Module::spine_root`). An occurrence that is not the head of a spine, or heads a spine supplying fewer value arguments than `f` has manifest parameters, is `f` used *as a value* — a PAP, an argument, something stored — and the parameter cannot be split at all. Every remaining occurrence is a call site, and the value argument at index `i` is a producer. `f` being exported is the same kind of disqualification.
- **A return** of `f`. Every syntactic return point of the body, enumerated iteratively through the `case`/`let` tree — GHC does not leave the lambdas at the head of a right-hand side, so `f = case c of A -> \s -> e1; B -> \s -> e2` has return points `e1` and `e2`. Each leaf carries the number of value arguments needed to reach it; the result lives at the deepest, and a leaf reached with fewer has, by the type of the position it sits in, to be a *function* of the remaining ones — a tuple is never a function — so it is a producer this walk cannot see into rather than a value of the boundary.

A producer expression is then classified by what it **is**, looking through casts, ticks, `let` bodies, `case` alternatives, local aliases (a variable bound to a right-hand side is that right-hand side) and the case binder that is another name for its scrutinee, and following a tail call to a local function into *its* return points at the matching arity. Everything else is named and asks for the tuple: a call to an import, a lambda-bound parameter, a field bound by a match, an imported value, a constructor application, a local call the walk will not follow.

**The verdict.** `UniformSplit(k)` only when every producer asks for `Scalars(k)` with the same `k` *and* the boundary has no other use. `CloneRequired` when the producers disagree at a **parameter** whose function is local, not exported and never used as a value: a clone of the callee can take the scalars while the call sites that have a real tuple keep calling the original. A **return** is never `CloneRequired` — every return point is inside one body and they all have to agree, so no clone splits some and not the others. `Preserve` when a proven real value reaches the boundary. `Unresolved` otherwise, with the reason.

Once a parameter boundary *is* a uniform split, a function that returns that parameter returns the same scalars, so the parameter's arity is propagated into the return boundaries that produce from it — a fixpoint that starts from nothing and only ever *adds* splittable parameters, so a cycle of functions passing each other's parameters around cannot bootstrap itself.

**The assertion this milestone is about.** Every removable flow whose view crosses a boundary — `PassedTo`, `Returned`, and their transitive hops, including through `T4-RETUPLE` and `T12-NESTED` — must have **every** crossed boundary `UniformSplit`. Otherwise the flow is **downgraded now**: `CloneRequired` moves it to the new fate `RemovableWithClone`, which keeps the flow's own proof but is counted as *unsupported* until a cloning decision exists; anything else moves it to `Unresolved` with the reason `boundary-not-uniform (<boundary>)`. Downgrading is itself a fixpoint — a flow that stops being removable stops asking for scalars at every other boundary it produces into — and it only ever shrinks the removable set, so it settles (2 rounds on `-O1`, 3 on B).

```sh
$ h2r tuples compiler/core-json --boundaries
  verdict          kind           boxed  unboxed   both    total
  CloneRequired    parameter          5        0      0        5
  Preserve         parameter          8        0      0        8
  Preserve         return            22        0      0       22
  UniformSplit     parameter          1        0      0        1
  UniformSplit     return            59      245     46      350
  Unresolved       parameter          3        0      0        3
  Unresolved       return           179       12      0      191
  total                                                      580

  of the 1453 flow(s) def-use proved removable, 1024 cross at least one boundary and 429 cross none
  247 of them were downgraded here: 3 to RemovableWithClone, 244 to Unresolved
  the downgrade fixpoint settled in 2 round(s)
```

580 boundaries, 351 of them uniform. **1,024 of the 1,453 def-use-removable flows cross at least one boundary**; 429 never leave the function they were built in and are untouched by any of this. **247 flows are downgraded**:

|         | new fate             | reason                                                          | representative                                                           |
| ------: | -------------------- | --------------------------------------------------------------- | ------------------------------------------------------------------------ |
|     181 | `Unresolved`         | producers request different representations                     | `Main` node 2737 — return of `p#1107`                                    |
|      23 | `Unresolved`         | the function is used as a value                                 | `ShellCheck.Analytics` node 49954 — return of `$s$fMonadWriterT2#1992`   |
|      21 | `Unresolved`         | a preserved tuple reaches the boundary                          | `ShellCheck.Analytics` node 3044 — return of `go1#2757`                  |
|      12 | `Unresolved`         | the function has no visible call site                           | `Main` node 8383 — return of `$s$w$c<*>#1`                               |
|       5 | `Unresolved`         | the binding is not a lambda chain, so it has no result to split | `ShellCheck.CFG` node 38683 — return of `m1#2556`                        |
|       3 | `RemovableWithClone` | producers disagree at a splittable parameter                    | `ShellCheck.Analytics` node 1974 — parameter 1 of `$wgo1#2086`           |
|       2 | `Unresolved`         | a call site is a partial application                            | `ShellCheck.Checks.Commands` node 13824 — return of `$s$fMonadRWST1#977` |
| **247** |                      |                                                                 | 222 boxed, 25 unboxed                                                    |

The single most common shape is the one the milestone was written for: `Main`'s `p#1107` returns a removable unboxed pair on one path and the result of an imported call on three others, so its result cannot become two scalars however good the pair's own proof is. Counted by what actually reaches a non-uniform boundary: 265 constructions that stay, 193 results of local calls the walk will not follow, 91 parameters of the enclosing function, 46 lambdas, 4 imported call results, 1 field bound by a match.

`--explain` lists each boundary's producers and consumers with node ids, and `--json` carries the boundaries and the downgrades:

```sh
$ h2r tuples compiler/core-json --module Main --boundaries --explain
Main return of p#1107 — Unresolved (producers-request-different-representations)
  crossed by unboxed tuple(s)
  producers
    node 2720     Tuple        result of an imported call                  at call …
    node 2738     Tuple        result of an imported call
    node 2737     Tuple        construction that stays
    node 2729     Tuple        result of an imported call
  consumers: 2532, 2625, 2568
```

**What this costs, and why it is the right price.** `normalised` falls from 1,453 to **1,206** and the unsupported residual rises from 580 to **827**. That is not a regression in what the compiler knows — every one of the 247 still has its def-use proof, and `--scalar-all` still prints a complete view for the 3 that only need a clone — it is the milestone refusing to count a removal it cannot actually perform. The verifier's report says so explicitly: it re-derives 1,206 of 1,206 with 0 disagreements, and the 247 constructions it would still accept are listed as *"verifier accepts, census does not … of which the boundary check downgraded: 247"*. Seven of them were the `-O1` verdicts that rested on a Parsec hop, which is why that line now reads 0.

### Auditing one construction

```sh
$ h2r tuples compiler/core-json --module ShellCheck.Analytics --explain
ShellCheck.Analytics node 30892 — unboxed tuple of arity 2, fate WorkerReturn
    T0-TUPLE-CON     node(s) 30892, 31017: unboxed tuple of arity 2 ($ghc-prim$GHC.Prim$(#,#)), 2 value argument(s)
    T6-RETURNED      node(s) 30852 [binder #10680 $wgo]: returned from (after 3 more argument(s)) $wgo with 2 occurrence(s)
    T7-CALL-RESULT   node(s) 30854: 3 argument(s) supplied: the call result is the tuple
    T2-SCRUTINISED   node(s) 30853, 30854: 2 field binder(s) bound
    T7-CALL-RESULT   node(s) 30974: 3 argument(s) supplied: the call result is the tuple
    T2-SCRUTINISED   node(s) 30897, 30974: 2 field binder(s) bound
    F2-WORKER-RETURN node(s) 30892: 3 consumer(s) over 10 value location(s), crossing a return
```

Every node id there is a `h2r show` argument. `--json` dumps the flows, their consumers and the accounting; `--verify` prints the independent re-derivation and the table of audited shapes above.

`h2r show` loads the tuple proof object by default for a module that has flows (`--no-tuples` turns it off, exactly like `--no-parsec`). It marks constructions, alias binders, consumers and their occurrences inline, and prints the flow's own evidence for the node asked about:

```sh
$ h2r show compiler/core-json ShellCheck.Checks.Commands 4714 --depth 2
-- in top-level binding lvl, node 4714
([#4714]{tuple flow #46 construction, arity 3, Unresolved}(,,)[#4725] ()[#4720] s1[#4718] w1[#4716])

node 4714
  tuple: (,,) boxed, arity 3, construction node 4714 (flow #46)
  fate: Unresolved  [boundary-not-uniform (return of eta1#2405)]
  this node: the construction itself
  consumers:
    returned from eta1#2405 (T6-RETURNED) → its call sites (T7-CALL-RESULT)
    copied field by field into the construction at node 4633 (T4-RETUPLE)
    field 2 selected on its own at node 4635 (T3-SELECTED)
    field 1 selected on its own at node 4640 (T3-SELECTED)
    field 0 selected on its own at node 4645 (T3-SELECTED)
  evidence:
    T0-TUPLE-CON: boxed tuple of arity 3 ($ghc-prim$GHC.Tuple.Prim$(,,)), 3 value argument(s) (node(s) 4714, 4725)
    T6-RETURNED: returned from (after 2 more argument(s)) eta1 with 1 occurrence(s) (node(s) 4626) [eta1#2405]
    T7-CALL-RESULT: 2 argument(s) supplied: the call result is the tuple (node(s) 4657)
    T4-RETUPLE: copied field by field into this construction (node(s) 4633) [ds1#2408]
    T1-LET-BOUND: bound to ds1 with 3 occurrence(s) (node(s) 4631) [ds1#2408]
    T3-SELECTED: field 2 selected (node(s) 4635, 4636) [w'#2412]
    T3-SELECTED: field 1 selected (node(s) 4640, 4641) [s''#2415]
    T3-SELECTED: field 0 selected (node(s) 4645, 4646) [b1#2418]
    F2-WORKER-RETURN: 5 consumer(s) over 24 value location(s), crossing a return, at least one field read on its own (node(s) 4714)
    B3-DOWNGRADE: return of eta1#2405 is Unresolved (producers-request-different-representations): the def-use proof stands, the rewrite does not (node(s) 4714) [eta1#2405]
```

A node that takes part in several flows gets one footer per flow — node 4635 above is a selector of three different constructions, and each says so separately. For `Preserve` and `Unresolved` the fate line carries the reason *with its holder* (`Preserve  [stored-in-constructor-field (:)]`), which is the same string the residual is itemised by. Both proof objects annotate the same rendering, and their marks are concatenated rather than merged, so it stays visible which object said what.

### The cross-milestone link: how many of M1's thunks are these tuples?

[M1](#m1--how-much-haskell-is-left-after-ghc) counts 2,242 potential thunk sites, 1,905 of which need memoisation to keep sharing, and attributes 422 of the sites to `ds…` desugar bindings. The desugarer turns a lazy tuple pattern `~(b, s, w)` into one selector thunk per field, so the obvious question is how much of M1's residue is *this milestone's* tuples.

`h2r tuples` answers it exactly, with a deliberately narrow rule: a thunk site is **explained by tuple transport** when the binding M1 reports is a potential thunk site, its right-hand side *is* a lazy selection (`T3-SELECTED`) or a field-wise re-tupling (`T4-RETUPLE`), and the tuple it reads is **normalised** — removable *and* verified. A `Preserve` or `Unresolved` tuple keeps its box, so its selectors stay; a removable verdict only one walk proves does not count either.

```text
Thunk sites explained by tuple transport (M1 × M2.2)
                                                 before explained    after
  sinkable, lands in an evaluating position          14         0       14
  sinkable, lands in a lazy position                254         3      251
  memoisation required                             1905        89     1816
  recursive value                                    69         0       69
  … captured by a many-entry lambda                1242        80     1162
  … shared on one path                              663         9      654
  potential thunk sites                            2242        92     2150
```

**92** thunk sites are explained: 89 of them memo (80 captured by a many-entry lambda, 9 shared on a path) and 3 sinkable into a lazy position. By binder origin they are 67 user-named, 23 `eta…`, 2 `ds…`, and none at all from `lvl…` or the dictionaries. (Before the [boundary check](#composing-the-views-can-all-1453-be-applied-at-once) narrowed `normalised`, this number was 111; the 19 difference is selectors over tuples whose boundary is not uniform, and their thunks stay.) The invariant `remaining + explained = 2,242` is asserted, as is "every explained site lands in exactly one fate row, one origin row and one rule".

Of the census' 1,321 tuple-attributed lazy argument sites, **630** stop being lazy positions because the tuple they are an argument *to* is normalised — the argument becomes a scalar binding at the construction (167 boxed, 463 unboxed). That is the same 630 as the `normalised` column of the site accounting above, seen from the other side.

**Why 92 and not 400.** The interesting finding is that the `ds…` population is *not* the selectors. GHC names the lazy pattern's scrutinee `ds…` and leaves the field selections under the pattern variables' own names, so `ds1` holds the *tuple* and `b1`/`s''`/`w'` are the selectors — which is exactly what the origin split shows. Counted separately, and **never folded into the table above**, 288 thunk sites *hold* a normalised tuple (`T1-LET-BOUND`): 210 `ds…`, 54 user-named, 23 `eta…`, 1 `lvl…`. Their box will not exist either, but what replaces each of them is one scalar binding per field, and whether *those* are thunks is a question for the let census to answer again after the rewrite — not one this link may answer now. Claiming them here would be the same mistake as naming a fate after a monad transformer.

The other reason the number is not larger is visible in the Core: of the 863 distinct lazy-selector cases over the whole population, only 142 are a `let` right-hand side at all. The rest are written inline — `case ($wgetCommandNameAndToken False x) of (# ww, ww1 #) -> ww` in `ShellCheck.ASTLib` — where there is no thunk to remove in the first place.

|                                          | A `-O1` |   B |   C |     D |     E |     F |
| ---------------------------------------- | ------: | --: | --: | ----: | ----: | ----: |
| thunk sites explained by tuple transport |      92 | 103 | 120 |   121 |   121 |   121 |
| thunk sites holding a normalised tuple   |     288 | 332 | 298 |   659 |   659 |   659 |
| lazy argument sites that become scalars  |     630 | 734 | 694 | 1,160 | 1,160 | 1,159 |

### M2.2 acceptance

**The criterion is that every tuple this milestone removes has a complete def-use proof, re-derived by an independent verifier, and a representation boundary that all the removals agree on — not that coverage is high.** A wrong "removable" is a miscompile; a wrong "Preserve" is a missed optimisation. Coverage is reported and secondary.

Against the `-O1` dump, all of the following hold.

**The population is partitioned, and the accounting closes.** 2,584 saturated constructions, 1,765 boxed and 819 unboxed, every one in exactly one fate bucket (asserted):

| fate               |     boxed | unboxed |
| ------------------ | --------: | ------: |
| ScalarReplace      |       403 |       0 |
| WorkerReturn       |       136 |     667 |
| RemovableWithClone |         3 |       0 |
| Preserve           |       551 |       0 |
| Unresolved         |       672 |     152 |
| **total**          | **1,765** | **819** |

and `before = normalised + preserved + unsupported` per representation: 1,765 = 539 + 551 + 675 boxed, 819 = 667 + 0 + 152 unboxed, 2,584 = 1,206 + 551 + 827 in all. The census' 1,321 tuple-attributed argument sites map one-to-one onto the population (849 boxed + 472 unboxed, 0 unmapped, over 726 distinct constructions) and close the same way: 1,321 = 630 + 144 + 547.

**Every removal is proven twice.** The [independent verifier](#the-independent-verifier) shares nothing with the census but the IR — its own population selection, its own name test, its own walk — and re-derives all 1,206 removable verdicts with **0 disagreements**; the two sides also select the same population (0 constructions found by only one). The 247 constructions the verifier would still accept and the census now refuses are exactly the ones the boundary check downgraded, and the report names them as such. The same holds on all six flag-matrix profiles (1,206 / 1,464 / 1,360 / 2,504 / 2,538 / 2,539, 0 disagreements each). **0 removable verdicts are unverified**, so nothing is counted as normalised on one proof.

**Every removal has a complete rewrite.** `--scalar-all` builds the normalised view of all 1,209 (and of all 2,544 on F): every consumer and every call site placed in exactly one line, `0 unplaced` everywhere.

**Every removal composes with the others.** Stage 4 enumerates all 580 [representation boundaries](#composing-the-views-can-all-1453-be-applied-at-once) the removable flows cross, *independently of the flow walk*, and requires every one of them to be a uniform split. 1,024 of the 1,453 def-use-removable flows cross at least one; 247 are downgraded because a boundary they cross is not uniform, 3 of them to `RemovableWithClone` (counted as unsupported) and 244 to `Unresolved`. The downgrade fixpoint asserts its own convergence, and the accounting, the 1,321-site table, the thunk link, the verifier and `--scalar-all` are all recomputed after it and all still close.

**No fate rests on a name.** The population is *selected* by ghc-prim's tuple constructor (evidence level 6) with `repArity` checked against the name and saturation checked structurally; every verdict after that is def-use over resolved occurrences. The constructor and callee names in the residual are diagnostics, and the residual is split by the *kind* of holder, not by the name.

**What remains, and what milestone each item belongs to:**

|     |                                                                                                                                                                                                                                                                           |                                                                                                  |
| --: | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------ |
| 244 | the def-use proof stands, but a **representation boundary** the flow crosses is not a uniform split (181 producers disagree, 23 the function is used as a value, 21 a preserved tuple reaches it, 12 no visible call site, 5 not a lambda chain, 2 a partial application) | a representation-agreement pass over the boundaries, or cloning                                  |
| 187 | the closure that returns the tuple is passed to an **imported** call                                                                                                                                                                                                      | M2.4 higher-order / whole-program closure analysis                                               |
| 134 | …**consed onto a list**                                                                                                                                                                                                                                                   | M2.4: the checks-in-a-top-level-list shape, a closed-world list-of-closures pass                 |
| 114 | …**stored in a program constructor**                                                                                                                                                                                                                                      | M2.4, per constructor                                                                            |
|  67 | …**handed to a local callee's parameter**                                                                                                                                                                                                                                 | a higher-order representation agreement (M2.4), not a def-use question                           |
|  41 | a proven Parsec continuation whose target the region graph does not close over                                                                                                                                                                                            | M2.1 follow-up: 20 chains not bound to a binder, 19 parsers used as a value, 2 unsaturated calls |
|  11 | returned from an **exported wrapper of a local worker**                                                                                                                                                                                                                   | whole-program linking — the *worker's* callers, not the wrapper's                                |
|  10 | …passed to a local binder that is not a lambda chain                                                                                                                                                                                                                      | M2.4 returned-closure analysis                                                                   |
|   7 | …held in a partial application                                                                                                                                                                                                                                            | M2.4                                                                                             |
|   3 | …passed to a class-op                                                                                                                                                                                                                                                     | closed-world instance enumeration (M2.3)                                                         |
|   2 | returned from an exported function with no worker                                                                                                                                                                                                                         | whole-program linking                                                                            |
|   2 | an unknown higher-order callee outside `ShellCheck.Parser`                                                                                                                                                                                                                | M2.4                                                                                             |
|   1 | the argument lands past the callee's parameters                                                                                                                                                                                                                           | M2.4                                                                                             |
|   3 | …and only a specialised **clone** of the callee could carry the split                                                                                                                                                                                                     | a cloning decision                                                                               |

> **Added by [M2.4d](#m24d--higher-order-representation-agreement)**, as a column beside these rows and changing none of them: 14 of the 67 now have a receiving parameter that is `UniformRepresentation` or `ExactClosure`, so a later pass **could** reclassify them; the 187 land on a parameter outside the closed world; the 134 and 58 of the 114 land on the single program-wide `(:)` / `(,)` field slot; 45 of the 114 land on a `Preserve`. | 1 | the callee's parameter cannot be split (the callee escapes) | M2.4 | | **827** | | |

**The cross-milestone table** is [above](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples): 92 of M1's 2,242 thunk sites are these tuples' lazy selectors, 2,150 remain, and the invariant is asserted.

**How to audit a site.** `h2r show <dir> <module> <node>` prints the Core around the node with both proof objects' marks inline and the flow's evidence as a footer; `h2r tuples <dir> --scalar <node>` prints what replaces the tuple, line by line, with `0 unplaced`; `--explain` lists every construction's evidence; `--verify` prints the independent re-derivation and the audited-shape table. All four are shown above.

**Known limits**, stated rather than hidden:

- the **location budget** (20,000) turns a pathological flow into an honest `Unresolved`. Nothing on `-O1` comes near it — the largest flow visits 2,023 locations, the mean is 19 — but the transitive `T12-NESTED` rule does reach it on the inlining-heavy profiles: 4 flows on B and 2 each on C–F end as `flow-exceeded-the-location-budget`. The verifier refuses those flows too, so it is a coverage loss in the safe direction;
- the **Parsec hop is an input to both sides** of the cross-check. Seven `-O1` verdicts rested on a continuation target the verifier cannot derive on its own and is handed from the other proof object; the boundary check has since downgraded all seven, so `-O1` now has none (D–F still do). Where they remain, they are proven twice *after* that hop and once before it; dropping the hop would move them to `Unresolved`, not to a different removal;
- `exported` is **trusted from GHC**. Every rule that needs "no caller outside this module" reads the binder's `exported` flag as dumped. A whole-program link step can replace that with the actual call graph, and would resolve the 11 exported-wrapper and 2 exported-return residuals;
- the link's `explained` count is the *narrow* one. The 288 bindings that hold a normalised tuple are reported beside it and not claimed;
- the boundary check's **producer classifier is partial by design**. A producer it will not follow — a local call at an arity it cannot match, a lambda-bound parameter whose own boundary is not uniform, a field bound by a match — asks for the tuple, which makes the boundary non-uniform and costs coverage in the safe direction. 331 of the 600 tuple-requesting producers at non-uniform boundaries are of that kind, so a sharper interprocedural representation analysis would recover some of the 247.

## M2.3b — what is evaluated when a constructor field is read

M2.2 asked which tuple *allocations* are plumbing. M2.3 asks the representation question for everything else, and it splits three ways: **M2.3b** (this section) is the constructor-**field** census, M2.3c is the list, M2.3d is text. This section decides exactly one thing and says so everywhere: for each field of each construction, what does the optimised Core prove about **when** the field's expression is evaluated? It answers nothing about ownership, about whether the box survives, or about a Rust type.

```sh
cargo run --release --bin h2r -- fields ../core-json
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.AST --explain
cargo run --release --bin h2r -- fields ../core-json --con OuterToken
cargo run --release --bin h2r -- lists ../core-json                         # list flows: when is a spine demanded, and how much
cargo run --release --bin h2r -- lists ../core-json --axioms                # the library demand-semantics table
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --explain
cargo run --release --bin h2r -- text ../core-json                          # which list flows are text, and what is done with them
cargo run --release --bin h2r -- text ../core-json --heads                  # the text-head table
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --explain
cargo run --release --bin h2r -- fields ../core-json --json
```

### The population

`D0-FIELD-CON`: every saturated application of a data constructor that is neither a tuple (M2.2's population) nor the list cons (M2.3c's), selected through the head's `DataConInfo` and never by name — 9,166 constructions on `-O1`, 2,703 of the program's own constructors and 6,463 of libraries', 19,830 fields in all. The constructor *name* only splits the report into program and library, exactly as the M2 census' family attribution does; no verdict reads it.

| constructions |                | constructions |                   |
| ------------: | -------------- | ------------: | ----------------- |
|         1,789 | `ParseError`   |           386 | `I#`              |
|           677 | `Solo#`        |           371 | `TyCon`           |
|           547 | `IS`           |           335 | `Comment`         |
|           500 | `OuterToken`   |           293 | `KindRepFun`      |
|           427 | `TrNameS`      |           291 | `Just`            |
|           408 | `TokenComment` |           282 | `KindRepTyConApp` |

### Sum types: which alternative is the scrutiny

The [generic aggregate walk](#m22--which-tuples-are-transport-and-which-are-values) was written for tuples, and it accepted a `case` only when it had exactly **one** data alternative of the construction's arity. For a product type that is exact; for a sum type one alternative per constructor is the normal shape, and the rule reported it as unresolved. M2.3b makes alternative selection **constructor-relative**, the way GHC decides it:

- the alternative whose data constructor is this one — matched on GHC's stable name with the tag corroborating — is the scrutiny (`T2-SCRUTINISED`);
- no such alternative, but a `DEFAULT`: that is what a value of this constructor selects, and it binds no field — an observation to WHNF (`T15-WHNF-ALT`), not an escape and not a read;
- neither: nothing this value could select, which is conservatively an escape (`R_ALTS`), never "the construction was not observed";
- every other alternative is **unreachable for this value** and contributes nothing to the field-demand theorem.

Reachability applies to the case **binder** too. It is in scope in all the alternatives but only one of them runs, so `case v of { C x -> k x; D y -> store v }` on a known `C` is *not* an escape: the store under `D` cannot be reached by this value. On `-O1` that skips 1,113 unreachable alternatives and 14 case-binder occurrences that would otherwise have forced a flow to `Unknown`.

Tuple behaviour is byte-identical under all of this — a tuple type has one constructor, so the constructor-relative rule only ever confirms what the single-alternative rule already said. `h2r tuples`, `--verify`, `--boundaries`, `--json`, `--scalar-all`, `h2r laziness`, `h2r parsec` and `h2r compare` produce identical output on `-O1` and on all six matrix profiles.

### Three facts first, then a verdict

Nothing is assigned a representation directly. Every (construction, field) records three **orthogonal** facts, and the rep is a function of them:

| Fact                    | Values                                         | Where it comes from                                   |
| ----------------------- | ---------------------------------------------- | ----------------------------------------------------- |
| field demand            | `Always` / `Conditional` / `Never` / `Unknown` | the walk's reachable observations                     |
| construction strictness | `StrictField` / `LazyField`                    | GHC's `DataConInfo.strictFields`                      |
| value recursion         | `RecursiveKnot` / `Acyclic`                    | **M1's** `Class::RecursiveValue`, read not re-derived |

The recursion fact is deliberately M1's and only M1's: a non-function member of a recursive group that refers to itself through the value. It does not mean "the field's type mentions the ADT" and it does not mean "produced by a recursive function".

| demand      | strictness  | recursion     |     fields |
| ----------- | ----------- | ------------- | ---------: |
| Always      | LazyField   | Acyclic       |        175 |
| Always      | StrictField | Acyclic       |         21 |
| Conditional | LazyField   | Acyclic       |        896 |
| Conditional | StrictField | Acyclic       |         19 |
| Never       | LazyField   | Acyclic       |          9 |
| Never       | StrictField | Acyclic       |         21 |
| Unknown     | LazyField   | Acyclic       |     15,418 |
| Unknown     | LazyField   | RecursiveKnot |          9 |
| Unknown     | StrictField | Acyclic       |      3,262 |
|             |             | **total**     | **19,830** |

The `Never` / `StrictField` row is the one that says why the facts are kept apart. `data X = X !Int Int` with field 0 never read is **not** `Dead`: the field carries a forcing obligation whenever `X` reaches WHNF, and nothing about "nobody reads it" removes that. 21 fields are in exactly that position. `Dead` requires all three: never demanded, lazy, and acyclic.

### Why `Direct` is narrow

`Direct` claims that evaluating the field where the constructor is built is equivalent to leaving it where GHC put it — **timing**, not eventual demand. Two things make "something forces it eventually" insufficient: `Foo (error "boom") ``seq`` 42` must stay `42`, and a construction that crosses a return can sit while other work happens before anything reads it, so moving the field's evaluation to the construction moves the divergence. Only three rules establish it:

| Rule                | Evidence       | What it proves                                                                                                                                                                                                                                                                    |
| ------------------- | -------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `R1-STRICT-FIELD`   | GHC (4)        | the field is already strict: forced at construction, nothing left to move                                                                                                                                                                                                         |
| `R2-FIELD-IS-VALUE` | structural (2) | the field expression is already a value — a literal, a lambda, a saturated construction, a partial application, a nullary constructor, a string literal, or a variable whose binding GHC marks `whnf` / `okForSpec` — so there is no evaluation to move                           |
| `R3-SAME-FRONTIER`  | 2 over 3       | every observation is a scrutiny that strictly demands the field and stands at the construction's own evaluation frontier: the walk crossed no return and no unknown call, and between the construction and each scrutiny there is no lambda, no conditional and no thunk boundary |

Everything demanded at all and not proven by one of those is `Deferred`. A false `Direct` is a miscompile; a false `Deferred` is lost coverage, so the rules are deliberately one-sided.

### Results on the `-O1` dump

|                     |  Dead |    Direct | Deferred | Recursive |    Unknown |
| ------------------- | ----: | --------: | -------: | --------: | ---------: |
| program, GHC-strict |     0 |         0 |        0 |         0 |          0 |
| program, lazy       |     4 |         1 |      206 |         1 |      6,524 |
| library, GHC-strict |     0 |     3,323 |        0 |         0 |          0 |
| library, lazy       |     5 |        84 |      780 |         8 |      8,894 |
| **total**           | **9** | **3,408** |  **986** |     **9** | **15,418** |

`Direct` by the rule that proved the timing: 3,323 `R1-STRICT-FIELD`, 85 `R2-FIELD-IS-VALUE`, **0** `R3-SAME-FRONTIER`. The last is not a bug and it is worth stating: the shape `R3` recognises is a construction scrutinised in the same frame it was built in, which is precisely what GHC's case-of-known-constructor already eliminates, so none survives `-O1`. The rule has a hand-built regression test rather than a count in the dump, and the negative case — the same demand behind a lambda — has one too.

Observations: 6,229 `FieldDemanded` (2,452 strict by GHC's demand on the alternative's binder, 12 strict by position, 3,765 lazy), 1,922 `FieldBoundUnused`, 471 `WhnfOnly` (468 `seq`-shaped forces, 3 `DEFAULT`-selected), 11,784 `Escape`. Constructions: 1,407 observed, 13 never observed, 7,746 escaped before any observation. The nesting fixpoint settles in 3 rounds.

| Top `Deferred` reason |                                                      |
| --------------------: | ---------------------------------------------------- |
|                   667 | demanded only lazily (passed on, stored, captured)   |
|                   203 | bound and unused on some observation                 |
|                    90 | demanded on every path, but not at the same frontier |
|                    26 | demanded on some observations only                   |

| Top `Unknown` reason |                                                                                         |
| -------------------: | --------------------------------------------------------------------------------------- |
|                2,264 | `stored-in-a-list-cell` — M2.3c's population                                            |
|                1,143 | an unknown higher-order callee (`eta`)                                                  |
|      998 / 573 / 348 | `the-program-construction-holding-it-escapes` (`TokenComment`, `OuterToken`, `Comment`) |
|      760 / 595 / 557 | `the-library-construction-holding-it-escapes` (`KindRepFun`, `TyCon`, `PushCallStack`)  |
|                  565 | an unknown higher-order callee (`eok`) — a Parsec continuation                          |
|                  311 | `stored-in-a-tuple-field` — M2.2's population                                           |

M2.3e split those reasons by **which population owns the holder**, because that is what decides who can close the residue: a list cell is M2.3c's, a tuple field is M2.2's, a program construction is one M2.3f can still follow inside this module, a library one is not. No verdict moved — 9,166 constructions, 19,830 fields and every cell of the three-fact matrix are byte-identical; only the reason strings changed.

The residual is dominated by three things that belong to other milestones rather than by a missing rule here: the list cell, the Parsec/higher-order callee, and the transitive escape of whatever holds the value. `D8-NESTED` does follow a construction stored in another construction **in this population** — through that field's binders at every scrutiny of the holder, inheriting the holder's own escapes — and fires 4,207 times; it stops at a list cell or a tuple because those are M2.3c's and M2.2's populations.

### The M2 census' 1,996 constructor-field sites

The [M2 baseline](#m2-baseline--who-receives-the-lazy-arguments) attributes 1,996 lazy argument sites to the constructor-field strategy. They map onto this population exactly, with nothing unexplained:

|       |                                                        |
| ----: | ------------------------------------------------------ |
| 1,310 | the list cons — **deferred to M2.3c**, not mapped here |
|   686 | mapped onto a (construction, field) pair               |
|     0 | unmapped                                               |

and their `FieldRep` is 77 `Deferred`, 609 `Unknown`, 0 of anything else — which is the honest shape of the thing: a lazy *computation* in a constructor field is, by construction, not a value, so `R2` cannot fire, and these are the sites whose holders reach a list or an import. (1,994 of the 1,996 are `Position::LazyField`; the other 2 are `Position::UnknownArg`, where the constructor's representation and source field counts differ. The population predicate is the census' own — a `Computation` in an escaping position with a `ProgramDataCon` / `LibraryDataCon` / `ListCons` family — so the 1,996 is the same 1,996.)

### Accounting

Asserted in code (`FieldAccounting::check`), on `-O1` and on all six matrix profiles:

- every field lands in exactly one rep, and the program/library × GHC-strict/lazy split and the three-fact matrix each cover all 19,830;
- `constructions = observed + unobserved + escaped-before-observation` (9,166 = 1,407 + 13 + 7,746) and `= program + library`;
- every census site is mapped, deferred to M2.3c, or carries a reason;
- every `Direct` verdict names the rule that proved its timing.

| profile   | constructions | fields | Dead | Direct | Deferred | Recursive | Unknown |
| --------- | ------------: | -----: | ---: | -----: | -------: | --------: | ------: |
| `-O1` / A |         9,166 | 19,830 |    9 |  3,408 |      986 |         9 |  15,418 |
| B         |        10,171 | 22,111 |   30 |  4,264 |    1,023 |         9 |  16,785 |
| C         |        11,092 | 23,381 |   26 |  4,621 |      782 |         9 |  17,943 |
| D         |        26,014 | 52,024 |  253 | 14,348 |      979 |         6 |  36,438 |
| E         |        23,632 | 47,292 |  223 | 12,748 |      925 |         6 |  33,390 |
| F         |        23,734 | 47,332 |  223 | 12,736 |      926 |         6 |  33,441 |

### Known limits, stated rather than hidden

- **`D8-NESTED` stops at the other milestones' populations.** A value stored in a list cell or a tuple field is `Unknown`, not followed. Following it needs M2.3c and M2.2's flows respectively; it is a coverage loss in the safe direction.
- **Any escape makes every field of that construction `Unknown`**, including an escape that is a *proven* real value (a store, an imported strict parameter). What the callee demands of the field is outside the module, so the analysis refuses rather than guessing — which is why 15,418 of 19,830 fields are `Unknown`.
- **`R2` counts a string literal as a value.** `unpackCString# "…"#` is not `exprIsHNF`, but it is total, terminating and cheap, so evaluating it eagerly can neither diverge nor error. That is the one place `R2` argues from `okForSpeculation`-style reasoning rather than from WHNF.
- **The recursion fact is M1's at `let` level and the group flag at top level.** M1 reports `Class::RecursiveValue` for `let`-bound bindings only; a top-level construction in a recursive group is taken at the group's own `rec` flag, under the same predicate.
- **This section decides evaluation only.** A field can be `Deferred` and `Acyclic` with no decision made about how it is represented.

## M2.3c — when, and how much, of a list's spine is demanded

M2.3b asked what is evaluated when a constructor *field* is read, and deferred 1,310 of the M2 census' 1,996 constructor-field sites — the list cons — to here. This section answers a different question about those and about every other list: **when, and how much, of a spine is demanded, by whom, how often, and does anything alias its tail?**

It deliberately does *not* start from `[]`/`(:)` and end at a Rust type. `foldl'` reaches every cell of a spine and is still a streaming consumer; "the whole spine is eventually consumed" does not mean the whole spine ever has to exist. So six **facts** are recorded per flow, each with its own rules and nodes, and an **advisory** recommendation is derived from them at the end and clearly labelled as advisory.

Text (`[Char]`) is M2.3d and nothing here decides it. Every flow records the list type and the element type as GHC rendered them on the binder — corroboration-level evidence that no verdict reads — so M2.3d can select the `[Char]` flows out of these facts.

```sh
cargo run --release --bin h2r -- lists ../core-json
cargo run --release --bin h2r -- lists ../core-json --axioms
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --explain
cargo run --release --bin h2r -- text ../core-json                          # which list flows are text, and what is done with them
cargo run --release --bin h2r -- text ../core-json --heads                  # the text-head table
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --explain
cargo run --release --bin h2r -- lists ../core-json --json
```

### The population: flows, not cells

| Producer      |                                                                                                                                           |      `-O1` |
| ------------- | ----------------------------------------------------------------------------------------------------------------------------------------- | ---------: |
| `L0-CONS`     | a saturated `(:)`, by `DataConInfo` and never by name, that is not itself the tail of another cons                                        |      3,920 |
| `L0-NIL`      | a `[]`, likewise, that is not the tail of a cons in the population                                                                        |      2,887 |
| `L0-IMPORTED` | a saturated call to an imported function whose [axiom](#the-library-demand-semantics-table) says the call's **own return type** is a list |      4,966 |
| `L0-LOCAL`    | a saturated call to a local function returning a list producer whose own flow could not reach this call site                              |         45 |
|               | **flows**                                                                                                                                 | **11,818** |

> Every number in this section is **after** M2.3e, which added eleven audited entries to the axiom table and fixed two propagation bugs, **and after M2.3g**, which corrected the axiom table itself: a call whose result merely *contains* a list (`span` returns a pair, `mapM` returns `m [b]`, `GHC.Magic.lazy` returns whatever it was given) is no longer a producer, which removed 99 structurally bogus flows. What moved, and why, is in [M2.3e](#m23e--re-deriving-the-representation-verdicts-independently) and in [Correction (M2.3g)](#correction-m23g--the-axiom-layer).

`L1-CHAIN`: a cons whose tail argument is another cons or a nil *construction* is a **cell of the same flow**, so `1 : 2 : 3 : []` is one flow of three cells, not four flows. 4,270 cons applications collapse into 3,920 chains.

`L0-LOCAL` is small on purpose. A call to a local list-producing function is normally *reached* — the producer's own flow leaves the function through `T6-RETURNED` and comes back at every call site through `T7-CALL-RESULT` — so it is a location of that flow rather than a new one, which is what keeps the population disjoint. The 45 are the cases where the return left the module and the call site is genuinely a new start.

### Following a spine

The [generic aggregate walk](#m22--which-tuples-are-transport-and-which-are-values) does the work, with the constructor-relative alternative selection M2.3b added: at `case xs of { [] -> …; (y:ys) -> … }` a cons flow selects the `(:)` alternative and a nil flow the `[]` one, and the other is unreachable for that flow (987 alternatives and 120 case-binder occurrences skipped). Three list-specific rules sit on top of it:

- **`L2-TAIL-ALIAS`** — the `(:)` alternative's *second* binder is not a field leaving the flow, it **is** the rest of this spine, and the walk continues at its occurrences. This is what lets a recursive consumer close a loop back onto the same `case` instead of stopping at the first cell. The *first* binder is an element, and is what `HeadDemand` is measured on (`L3-HEAD-BOUND`).
- **`L7-CONSED-AS-TAIL`** — the value is the **tail** argument of another cell: a `go`-loop accumulator, a cons built from a parameter. That is not storage; the spine continues into that cell's flow, and the successor's facts come back through a worklist fixpoint over the reverse edges (9,880 hops, 2,873 updates to settle).
- **`L18-STORED-FOLLOWED`** — the value is a field of a construction in M2.3b's population, and that holder is taken apart somewhere visible: the reads of the holder's field are reads of this spine. This is the exact mirror of M2.3b's `D8-NESTED`, which stops at a list cell precisely because this milestone owns it. It fires 3,191 times, and it is the reason `Storage` and `SpineDemand` are separate facts: a spine can be stored *and* have a fully visible demand.

### The library demand-semantics table

A call to `map`, `++` or `$wlenAcc` has no unfolding in the dump, so def-use can only say the list left the module. `lists/axioms.rs` restores the missing facts as an explicit, auditable table — 101 entries — each carrying a stable global name, a semantic rule id (`L-AX-…`), a note, and six fields whose axes M2.3g separated because conflating them was a bug in each case:

| field       | what it says                                                                                                                                                                                                                                | what it deliberately does **not** say                                                                                   |
| ----------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------- |
| `list_args` | `(end-index, ArgSpine)` for **each** list argument: `Whole`, `PrefixFromArg(i)`, `PrefixDataDependent`, `Incremental`, `NoDemand`                                                                                                           | how often the spine is walked — that is `replays`                                                                       |
| `replays`   | the end-indices of arguments the call **retains and traverses again from the front** (`cycle`, `isInfixOf`, `isSuffixOf`, `intercalate`'s separator)                                                                                        | nothing about how far each traversal gets                                                                               |
| `head`      | `HeadDemand`: what the call **provably forces** of the elements it reaches — a primop (`eqString` at `Char`), a `case` (`and`, `words`)                                                                                                     | that a callback forces anything: `any (const True)` does not                                                            |
| `exposure`  | `HeadExposure`: which callback the elements are handed to — `Predicate`, `Eq`, `Ord`, `Show`, `Other`                                                                                                                                       | that the element is evaluated                                                                                           |
| `alias`     | `NoAlias` · `ResultIsTailOfArg(i)` · `ResultSharesArg(i)` · `ResultContainsSuffixOfArg(i)` (the suffix is inside a pair or a `Maybe`) · `ResultSharesElementOf(i)` (the result is one of the *elements*, which puts nothing on this spine)  | whether the result is itself a list                                                                                     |
| `produces`  | the call's **outer return type**: `NotAList` · `DirectList(kind)` · `ProductContainsList{components}` · `EffectContainsList(kind)` · `OtherContainsList`, where `kind` is incremental / whole-before-first-cell / same-as-input / unbounded | which component of a product or effect the list is — that is tuple and effect normalisation's job, not this milestone's |

**Only `DirectList` starts a flow.** The two axes are independent in both directions: `span` returns a pair *and* its second component is a suffix of its argument, so it is no producer and still puts a shared tail on its input; `GHC.Magic.lazy` is the identity *and* `a` is not a list at every call site, so it is no producer either although its result is its argument.

It introduces a **new evidence level**, and where it sits is the point:

> 1 lexical binder identity · 2 structural shape · 3 def-use dataflow · 4 GHC type compatibility · **5 library axiom** · 6 textual type comparison · 7 names

Below dataflow because it is *asserted*, not derived — nothing in the dump proves that `reverse` traverses its whole argument. Above textual types because it is a statement about semantics rather than spelling. The table was written against **base-4.18.3.0 / ghc-prim-0.10.0 (GHC 9.6.7)**, the versions in `compiler/matrix/A/plan.json`.

**An axiom is only ever applied to an imported id.** The key is GHC's full stable name and the lookup happens only when `binding_of` says nothing in this module binds the head, so a program function called `map` is never looked up — there is a regression test for exactly that. List arguments are indexed **from the end** of the call's value arguments, which is what makes an entry survive a leading dictionary; an entry declares a minimum argument count and is not applied to a call supplying fewer.

The flows reached **116 distinct imported heads**; 36 of them have an entry, and those 36 cover 5,115 of the 6,660 imported consumer sites (77%). The rest are reported as `Unknown` with `no-axiom-for(<stable name>)` — never guessed. Eleven of the entries and three corrections came out of [M2.3e's audit](#the-axiom-audit), and a further **46 of the 101 entries were corrected** by [M2.3g's audit](#correction-m23g--the-axiom-layer), which read base's own definition for every entry claiming a result type, a forcing or an alias.

| calls | axiom | head                                         |   | calls | axiom  | head                             |
| ----: | ----- | -------------------------------------------- | - | ----: | ------ | -------------------------------- |
| 1,861 | yes   | `GHC.Base.++`                                |   |   394 | **no** | `ShellCheck.Interface.$wgo`      |
| 1,121 | yes   | `GHC.Base.eqString`                          |   |   168 | **no** | `GHC.Show.showLitString`         |
|   999 | yes   | `GHC.CString.unpackAppendCString#`           |   |    88 | **no** | `Text.Parsec.Char.string1`       |
|   236 | yes   | `GHC.List.elem`                              |   |    66 | **no** | `GHC.Show.showList__`            |
|   192 | yes   | `Data.OldList.isPrefixOf`                    |   |    61 | **no** | `GHC.IO.Handle.Text.hPutStr2`    |
|   144 | yes   | `GHC.Base.++_$s++`                           |   |    49 | **no** | `Text.Regex.TDFA.String.compile` |
|   138 | yes   | `GHC.List.reverse1`                          |   |    45 | **no** | `Data.Set.Internal.$fDataSet1`   |
|   129 | yes   | `GHC.List.takeWhile`                         |   |    40 | **no** | `Text.Parsec.Error.$wmergeError` |
|    81 | yes   | `GHC.Classes.$fEqList_$s$c==1` (M2.3e)       |   |    39 | **no** | `GHC.Base.pure`                  |
|    72 | yes   | `GHC.Classes.$fOrdList_$s$ccompare1` (M2.3e) |   |    43 | **no** | `Data.Set.Internal.$fDataSet1`   |

Entries are written only where the semantics are certain. M2.3e read base-4.18.3.0's source for every helper M2.3c had left out and added the ones it could confirm (`dropLength`, `dropLengthMaybe`, `prependToAll`, `splitAt_$s$wsplitAt'`, `init1`, `head1`, `flipSeq`, and the four `SPECIALISE`d list `==`/`compare` copies). `intercalate_$spoly_go1` keeps **no entry**: `poly_go` is a name GHC generated, base contains no such definition, and a shape read off a call site is a guess, not a contract. That residual is the honest measure of the table's coverage.

### Seven facts, and only then a recommendation

| `SpineDemand`         |       |   | `HeadDemand` (**proven forcing only**) |       |
| --------------------- | ----: | - | -------------------------------------- | ----: |
| Unknown               | 5,503 |   | Unknown                                | 5,503 |
| None                  | 4,359 |   | None                                   | 5,482 |
| Prefix(DataDependent) |   921 |   | Prefix                                 |   544 |
| Incremental           |   715 |   | All                                    |   270 |
| Prefix(Known)         |   179 |   | First                                  |    19 |
| Whole                 |   141 |   |                                        |       |

`HeadExposure` is fact 2b, added by M2.3g and recorded **beside** `HeadDemand`, never folded into it: an element that reaches a predicate or a class method has to exist as a value, but nothing proves it is evaluated.

| `HeadExposure`              |       |                                                        |
| --------------------------- | ----: | ------------------------------------------------------ |
| Unknown                     | 5,503 | a consumer is outside what this module proves          |
| NotExposed                  | 5,340 |                                                        |
| BoundAndUsed                |   460 | a `(:)` alternative binds the element and uses it      |
| PassedToCallback(Eq)        |   401 | `elem`, `nub`, `isPrefixOf`, the specialised list `==` |
| PassedToCallback(Other)     |    61 | `map`, `foldr`, `zipWith`, `mapM_`                     |
| PassedToCallback(Predicate) |    46 | `any`, `all`, `find`, `takeWhile`, `span`              |
| PassedToCallback(Ord)       |     7 | `sort`, `maximum`, the specialised list `compare`      |

| `Reuse`    |       |   | `Storage` |       |   | `Recursion`    |        |
| ---------- | ----: | - | --------- | ----: | - | -------------- | -----: |
| Escapes    | 5,238 |   | StoredIn  | 5,234 |   | FiniteProducer | 11,787 |
| SinglePass | 4,225 |   | NotStored | 4,310 |   | RecursiveKnot  |     31 |
| SharedTail | 1,860 |   | Returned  | 1,460 |   |                |        |
| MultiPass  |   495 |   | Captured  |   814 |   |                |        |
| Replayed   |     0 |   |           |       |   |                |        |

`ShortCircuit`: 1,181 flows have a consumer that may stop before the end, 10,637 do not. 6,239 flows have only streaming spine consumers.

`Reuse::Replayed` is M2.3g's fourth reuse shape — a consumer that retains the spine and walks it **again from the front**, which is neither a second independent entry (`MultiPass`) nor a surviving tail (`SharedTail`). Five axiom entries carry it (`cycle`, `isInfixOf` on both arguments, `isSuffixOf` on both, `intercalate`'s separator) and **none of them is called anywhere in these seven dumps**, so the fact has 0 firings. It is printed with its zero rather than left out: a rule that the program never exercises is a fact about the program.

The spine rules behind `SpineDemand`, beyond the axioms:

| Rule                   |                                                                                                                                                                                                                                                                     | `-O1` |
| ---------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----: |
| `L4-LOOP-WHOLE`        | the tail alias is an argument of a saturated call to a local callee whose parameter *this same `case`* scrutinises, and the call runs whenever the alternative does with only evaluating edges in between → **Whole**                                               |    27 |
| `L17-LOOP-INCREMENTAL` | the same loop with the recursive call in a lazy position — a constructor field, a lazy argument, a lambda — so a cell is reached only when the consumer's own consumer asks → **Incremental**. This is the `map`-shaped loop, and calling it `Whole` would be a lie |   115 |
| `L5-LOOP-SHORTCIRCUIT` | the same loop under a `case` inside the alternative → **Prefix(DataDependent)** and a short-circuit node                                                                                                                                                            |   195 |
| `L6-TAIL-DROPPED`      | the alternative binds the tail and never uses it → this cell only                                                                                                                                                                                                   |   137 |
| `L14-SHARED-TAIL`      | an axiom whose result — or a list inside its result — is a suffix of the argument, or a tail-derived value that is stored or handed out                                                                                                                             | 1,770 |
| `L15-MULTIPASS`        | more than one consumer enters the spine without reaching it through another's tail alias                                                                                                                                                                            |   330 |
| `L13-RECURSIVE-KNOT`   | **M1's** `Class::RecursiveValue`, read and not re-derived                                                                                                                                                                                                           |    31 |
| `L19-REPLAYED`         | an axiom says the consumer retains this argument and walks it again from the front (M2.3g)                                                                                                                                                                          |     0 |
| `L20-HEAD-EXPOSED`     | an element reaches a callback the analysis cannot see into — exposure, not forcing (M2.3g)                                                                                                                                                                          |   723 |

The rule counts are direct firings. The `Reuse` fact totals above are larger (1,860 `SharedTail`, 495 `MultiPass`) because M2.3e made `Reuse` travel the `L7-CONSED-AS-TAIL` edges with the other facts: a spine consed onto a longer one is a **suffix** of it, so a tail the longer spine shares, an extra entry into it and a head it escapes to all reach these cells too. Leaving `Reuse` out of that propagation was the one place the census could call a re-entered spine `SinglePass`, and it is what the independent re-derivation caught.

`Recursion` is M1's definition and only M1's: a non-function member of a recursive group that refers to itself through the value. A recursive *function* building a finite list is `FiniteProducer`, and there is a test that asserts M1 does not call such a binding a recursive value.

### The advisory recommendation

|            |                       |                                                                                                 |
| ---------: | --------------------- | ----------------------------------------------------------------------------------------------- |
|         32 | `VecCandidate`        | whole spine, entered more than once or outliving its consumers, no shared tail, finite producer |
|        727 | `IteratorCandidate`   | one pass, nothing retained, every spine consumer streaming, finite producer                     |
|      1,925 | `PersistentCandidate` | a tail survives in two places, the spine is replayed, or repeated entry with tails retained     |
|         30 | `LazyCandidate`       | a value knot, or a short-circuiting consumer in front of an unbounded producer                  |
|      9,104 | `Unknown`             | any fact is `Unknown`, or the facts match no recommendation — with the reason                   |
| **11,818** |                       |                                                                                                 |

**The ordering, corrected at M2.3g.** An advisory is a claim that a representation is sufficient *given everything we know*, so **every** `Unknown` fact — spine, head, exposure, or a `Reuse::Escapes` — makes the recommendation `Unknown`, before any positive fact is consulted. Until M2.3g a proven `SharedTail` and M1's `RecursiveKnot` were decided *first*, which let "one known property points this way" be published as "this is sufficient": 266 flows were advised on that basis with another fact unknown.

The positive facts are not lost. They are recorded as **constraints** on the flow — things any representation must support whatever the advisory says — and a constraint survives an `Unknown`:

| constraint                  |                                                           | `-O1` | of which the recommendation is `Unknown` |
| --------------------------- | --------------------------------------------------------- | ----: | ---------------------------------------: |
| `RequiresTailSharing`       | a tail of this spine survives in a second place (`L14`)   | 1,860 |                                      265 |
| `RequiresRecursiveLaziness` | M1 calls the producer's binding a recursive value (`L13`) |    31 |                                        1 |
| `RequiresReplay`            | a consumer retains the spine and walks it again (`L19`)   |     0 |                                        0 |

Only then do the positive facts decide, in this order: a **value knot** is a knot whatever else is true of it; then a **proven shared tail**, because two owners seeing the same cells settles the representation; then a **replayed** spine, because the cells must still be there for the second walk; then the short-circuit-over-unbounded case, and last the multi-pass / whole / single-pass arithmetic.

`foldl'` over a whole list is the case the split exists for: `Whole` spine, `SinglePass`, `NotStored`, streaming — an `IteratorCandidate`, **not** a `VecCandidate`. There is a test that asserts exactly that.

### The 1,310 list-cons census sites

M2.3b mapped 686 of the M2 census' 1,996 constructor-field sites onto a (construction, field) pair and deferred the 1,310 list-cons ones here. They map onto this population exactly:

|       |                                              |
| ----: | -------------------------------------------- |
| 1,310 | mapped onto the cell they are an argument of |
|     0 | unmapped                                     |

1,174 of them are the cell's **tail** and 136 its element — which is the shape of the thing: a lazy computation in a cons cell is usually the rest of the list.

| by recommendation |                     | by `SpineDemand` |                       |
| ----------------: | ------------------- | ---------------: | --------------------- |
|               977 | Unknown             |              682 | Unknown               |
|               289 | PersistentCandidate |              492 | None                  |
|                39 | IteratorCandidate   |               52 | Incremental           |
|                 5 | VecCandidate        |               40 | Prefix(DataDependent) |
|                   |                     |               29 | Whole                 |
|                   |                     |               15 | Prefix(Known)         |

### Accounting

Asserted in code (`ListAccounting::check`), on `-O1` and on all six matrix profiles: every flow lands in exactly one bucket of the producer-kind, recommendation, spine, head, **head-exposure**, reuse, storage and recursion tables; every flow either has a short-circuiting consumer or has not; every imported head seen either has an axiom or has not; and every one of the census' list-cons sites maps onto exactly one cell or carries a reason.

| profile   |  flows | ConsChain |   Nil | Imported | Local | Vec | Iterator | Persistent | Lazy | Unknown |
| --------- | -----: | --------: | ----: | -------: | ----: | --: | -------: | ---------: | ---: | ------: |
| `-O1` / A | 11,818 |     3,920 | 2,887 |    4,966 |    45 |  32 |      727 |      1,925 |   30 |   9,104 |
| B         | 12,146 |     3,989 | 3,024 |    5,083 |    50 |  37 |      701 |      2,079 |   30 |   9,299 |
| C         | 13,647 |     3,907 | 3,670 |    6,016 |    54 |  31 |    1,231 |      1,839 |   22 |  10,524 |
| D         | 23,886 |     6,291 | 8,516 |    9,025 |    54 |  32 |    1,886 |      2,480 |   82 |  19,406 |
| E         | 22,688 |     6,213 | 7,806 |    8,615 |    54 |  32 |    1,817 |      2,382 |   82 |  18,375 |
| F         | 22,807 |     6,262 | 7,839 |    8,652 |    54 |  32 |    1,795 |      2,362 |   82 |  18,536 |

`h2r tuples`, `--verify`, `--boundaries`, `h2r laziness`, `h2r parsec` and `h2r fields` are byte-identical on `-O1` before and after this milestone, and stayed byte-identical through M2.3e. M2.3f adds an accounting section to `h2r fields`, `lists`, `text` and `verify-rep` and changes no existing line of any of them.

### Known limits, stated rather than hidden

- **The axiom table is asserted.** Every `L-AX-…` entry is a claim about base that the dump does not prove. The entries most worth re-reading are the aliasing ones — `reverse1`'s accumulator becoming the result's tail, `unpackAppendCString#`'s second argument, `dropWhile`/`drop`/`span` returning a suffix of their input — because a wrong alias claim turns a `PersistentCandidate` into an `IteratorCandidate`, which is the unsafe direction. Nothing that could not be read off the function's contract with certainty got an entry.
- **2,848 flows are stored with no visible spine demand**, and M2.3e split the reason by what holds them: 620 (`…-in-a-holder-the-field-census-knows`) sit in a construction M2.3b has the field reads of, so M2.3f can pick that verdict up without re-analysing anything, and 2,228 (`…-in-a-holder-this-module-never-takes-apart`) sit in a holder that is never taken apart here or is not a construction at all. Whole-program (M2.4) work, not a missing rule here.
- **1,700 flows reach a holder that escapes.** `L18-STORED-FOLLOWED` inherits the holder's escapes, so a spine inside an escaping `TokenComment` is `Unknown` rather than guessed.
- **Traversal counting over-counts rather than under-counts.** A consumer is treated as a new entry into the spine unless it is reached through another consumer's tail alias, closed over known-local calls — and since M2.3e that closure requires **every** call site of a parameter to hand it a tail-derived argument, because a parameter that also receives the whole spine from somewhere else is an independent entry into it whatever the other call site does. Where that closure cannot follow — a higher-order hop — two views of one traversal are counted as two, which pushes a flow towards `MultiPass` and `PersistentCandidate`: the conservative direction for a representation decision.
- **`Captured` is narrow.** A flow that crossed a parameter or a return is never called captured, because a consumer inside the callee's lambdas is where the value was *sent*, not where it was captured. That costs coverage in the safe direction.
- **This section decides demand and sharing only.** No Rust type is chosen anywhere, and `[Char]` is not distinguished from any other element type.

## M2.3d — which of those flows are text, and what is done with them

`h2r text <dir> [--module M] [--json] [--explain] [--heads]`.

M2.3c's list census says how much of a spine is demanded. It deliberately did not ask whether the elements are characters. This milestone selects the **text** flows out of that population and refines them — it does not re-walk the Core, and every spine fact it needs (spine demand, head demand, shared tails, storage, escapes, recursion) is inherited with the `L…` rule id cited.

### How `Char` is established

*Amended by [M2.4a](#m24a--stable-global-identity-and-structured-types). This section originally read "the caveat this whole milestone rests on" and described a level-6, textual type comparison. Dump format 5 carries structured types, so the rules below now read `TyCon` identity and the caveat is gone — with, as M2.4a's gate required, not one number changed.*

`Char` is `TyConApp` with the `TyCon` GHC itself names `$ghc-prim$GHC.Types$Char`, and `[Char]` is that under `$ghc-prim$GHC.Types$List`: **level 4, structural `TyCon` identity — GHC type compatibility**. The plugin expands type synonyms before dumping, so `String` and `FilePath` arrive already in that form; they are not spellings anything has to recognise. GHC's rendering of each type still travels alongside and is what the reports print — a *label*, never a verdict.

What the milestone still refuses to conclude is unchanged. Where a flow's element type is a type **variable** — instantiated somewhere this module cannot see — or there is no type to read, the flow is `element-type-unknown` and is **never** assumed to be text. And a type is still only one of the ways in: a fact that reads no type at all agreeing with it is worth more than either alone, which is why every selection records how `Char` was established.

### The population, and the five ways in

A list flow is selected when **any** of these fires. Each stands alone.

| rule                   | what it reads                                                                                                                                                                 | level    |
| ---------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------- |
| `X0-ELEM-TYPE`         | the `(:)` alternative's head binder is `TyConApp Char []`                                                                                                                     | 4        |
| `X1-LIST-TYPE`         | the flow's own binder is `TyConApp List [TyConApp Char []]`                                                                                                                   | 4        |
| `X2-UNPACK-PRODUCER`   | the producer is an `unpackCString#`-family call                                                                                                                               | 2 over 5 |
| `X3-CHAR-LITERAL-HEAD` | a cell's element is a `Char` literal or a saturated `C#`                                                                                                                      | 2        |
| `X4-CHAR-SCRUTINY`     | a head binder is scrutinised by a `case` on `C#` or a `Char` literal                                                                                                          | 1 over 2 |
| `X5-AXIOM-FIXES-CHAR`  | a consumer's signature fixes the argument to `[Char]` (`eqString`, `unpackAppendCString#`, `lines`, `words`, `showLitString`, `hPutStr`, regex `compile`)                     | 5        |
| `X24-APPEND-SAME-ELEM` | an append does not change the element type, so a `[Char]` anywhere in a connected component of (append result ↔ its list operands) establishes it everywhere in the component | 5 over 2 |

`X24` is closed to a fixpoint with a union-find over the append relation. A component that also contains a flow whose rendered element type is concretely *not* `Char` is a contradiction and is **refused**, not propagated into (0 refusals on every profile).

On `-O1`, of M2.3c's 11,818 list flows:

|                                                 | flows |
| ----------------------------------------------- | ----: |
| text                                            | 4,431 |
| not text (element type reads as something else) | 1,788 |
| element-type-unknown — never assumed text       | 5,599 |

and of the 4,431 text flows, how `Char` was established:

|                                                                     | flows |
| ------------------------------------------------------------------- | ----: |
| type only (level 4: the element's `TyCon` is `Char`)                |    58 |
| structural only (the type did not agree, or there was none to read) | 1,772 |
| both — the type and a fact that reads no type agree                 | 2,601 |

90 of the structural selections came from `X24`. The type alone carries only 58 flows; it is the *corroboration* it provides on 2,601 that it is good for.

### The text-head table

`TEXT_HEADS` is a second deliberate name-keyed table, in the same spirit as M2.3c's axiom table and at the same evidence level (**5, library axiom**), under the same hard rule: consulted **only** for an imported head, which M2.3c has already established for every `L8-AXIOM`/`L9-NO-AXIOM` consumer. It is keyed on `(module, occ)` rather than the full stable name because a package's unit id carries a build hash (`regex-tdfa-1.3.2.6-4dff8751…`).

It does one thing the axiom table does not: it gives a demand class to heads the axiom table has **no entry for** — `hPutStr2`, `showLitString`, the specialised list `==` and `compare`, regex-tdfa's `compile`. A flow whose only unresolved consumer is such a head is `Unknown` in M2.3c and decided here. That is the one place this milestone is *more* decided than the last; it is asserted rather than derived, and every consumer it decides is marked `(asserted)` in `--explain` (1,528 of them on `-O1`).

One consequence is recorded explicitly in the code: M2.3c sets `Reuse::Escapes("no-axiom-for")` whenever *any* consumer is an imported head its table has no entry for. That is a restatement of those consumers, not a claim that the value left the walk, so it is not by itself an `Unknown` fact here — each such consumer is reported individually, resolved by the text table or not.

### Facts, then an advisory

Recorded independently, per flow:

- **`TextShape`** — `TextOnly` (every consumer is a `TEXT_HEADS` entry), `Mixed` (a generic list combinator or a structural `case` on the cells), `Unknown` (an imported head neither table knows, or the value left the walk), `Unobserved` (nothing observes it at all).
- **`Literal`** and **`AppendChain { length, all_literal, opaque }`** — counted in *operand segments* off the Core spine at the producer, following a let-bound operand by lexical identity, depth-capped at 64.
- **Per-consumer class** — `CompleteOutput` (the whole text is the subject: output, `eqString`, `==`, `length`, `reverse`, a regex compile), `Prefix` (`isPrefixOf`, `take`, `head`, `null`, `takeWhile`, a `case` on the first cell), `Incremental` (the left side of `++`, `map` over the characters, streaming output), `Retained` (nothing is demanded here), `Unknown`. Derived from the consumer's own M2.3c `SpineDemand` unless `TEXT_HEADS` asserts otherwise.
- **`char_semantics_required`** with its reasons — an element is exposed or the operation depends on characters rather than on encoded bytes. **This does not preclude `String`**: it says a future representation must preserve character semantics explicitly.
- **`SharedTails`, `PrefixConsumers`, `Storage`, `Escapes`** — inherited from `L14`, `L10`/`L16`, `L11`; cited, never recomputed.

On `-O1`:

| TextShape  | flows |   | consumer class | consumers |
| ---------- | ----: | - | -------------- | --------: |
| TextOnly   | 1,862 |   | CompleteOutput |     1,488 |
| Mixed      |    38 |   | Prefix         |       653 |
| Unobserved | 1,004 |   | Incremental    |       364 |
| Unknown    | 1,527 |   | Retained       |     6,641 |
|            |       |   | Unknown        |     2,891 |

| consumer side | consumers |   | text family | consumers |
| ------------- | --------: | - | ----------- | --------: |
| Text          |     3,690 |   | Append      |     1,917 |
| Neutral       |     5,072 |   | Compare     |     1,184 |
| Opaque        |     2,837 |   | Show        |       174 |
| Structural    |       232 |   | Affix       |       173 |
| Generic       |       206 |   | CharSearch  |       121 |
|               |           |   | Output      |        61 |
|               |           |   | Regex       |        55 |
|               |           |   | LinesWords  |         5 |

Construction: 2,414 flows are literal (`unpackCString#`-family producers), 1,349 are built by an append, 7 of those from literals only, and 1,268 are an operand of an append. The append-chain histogram, in operand segments:

| segments |     2 |   3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 | 15 |
| -------- | ----: | --: | -: | -: | -: | -: | -: | -: | -: | -: | -: | -: | -: | -: |
| flows    | 1,045 | 184 | 47 | 33 | 19 |  6 |  3 |  4 |  1 |  2 |  2 |  1 |  1 |  1 |

`char_semantics_required` holds for 882 of the 4,431, for these reasons (a flow may have several):

| reason                                                           | count |
| ---------------------------------------------------------------- | ----: |
| a consumer exposes individual characters                         |   738 |
| an element **is forced** (M2.3c's `HeadDemand`, proven)          |   383 |
| a `(:)` alternative binds and uses the head                      |   177 |
| an element **is exposed to a callback** (M2.3c's `HeadExposure`) |   161 |
| a consumer depends on character positions or count               |    69 |
| the head is compared against a `Char` literal                    |    59 |
| a `Char` literal is an element                                   |     1 |

M2.3g split the second row. Before it, `an-element-is-forced` covered 510 flows, and for most of them the only evidence was a predicate or an `Eq` method — which may ignore its argument. Character semantics are still required in both cases (the element has to exist as a `Char` either way, so the flag did not move except for the five flows the population lost), but the milestone may not say "forced" when all it knows is "handed to a callback".

### The advisory

Derived from the facts and clearly separated from them. **Nothing here decides that any flow is a Rust `String`.** Precedence: any `Unknown` fact first, then `NotText`, then the strong conjunction, then undecided.

| advisory                | flows | condition                                                                                                                                   |
| ----------------------- | ----: | ------------------------------------------------------------------------------------------------------------------------------------------- |
| `StrongStringCandidate` |   185 | `TextOnly` ∧ only complete-output or incremental consumers ∧ no character observed ∧ no shared tail ∧ no prefix consumer ∧ `FiniteProducer` |
| `TextValueUndecided`    | 2,561 | text, representation open                                                                                                                   |
| `NotText`               |     2 | selected by type, consumed only structurally, and no character observed anywhere                                                            |
| `Unknown`               | 1,683 | an opaque consumer, a real escape, or an unknown consumer class                                                                             |

2,345 flows have no text-shaped consumer at all, whatever else is unknown about them — the honest measure of how much of ShellCheck's text is handled by code this dump does not contain.

### The census' append argument sites

M2's census counts 573 lazy-argument sites at `unpackAppendCString#` and 545 at `GHC.Base.++` (the "ordinary calls" bucket), under its own population filter — a non-trivial *computation* in a lazy or unknown position — which `text::census_site` reproduces exactly, so the two milestones count the same 1,118 sites. Each is mapped onto the text flow its argument carries, or carries a reason:

|                                                                                                          | sites |
| -------------------------------------------------------------------------------------------------------- | ----: |
| map onto a text flow (all `TextValueUndecided`)                                                          |   226 |
| the argument is a `case`/`let` with no single producer                                                   |   281 |
| the argument is a local call result M2.3c follows as a *location* of another flow, not a flow of its own |   281 |
| the argument's flow is not text                                                                          |   234 |
| the argument is an imported call with no axiom                                                           |    96 |

Separately, as *evidence* rather than population: of M2.3c's append **consumer** sites, all 1,002 `unpackAppendCString#` sites and 905 of the 1,861 `GHC.Base.++` sites sit on a flow this milestone calls text (plus 12 of 144 `++_$s++` and the single `unpackAppendCStringUtf8#`).

### Accounting

Asserted in code (`TextAccounting::check`), on `-O1` and on all six matrix profiles: text + not-text + element-type-unknown = M2.3c's flow count; type-only + structural-only + both = the text flows; every text flow lands in exactly one bucket of the shape, advisory, storage and recursion tables; every append-produced flow appears exactly once in the histogram; the per-module totals sum to the population; and every one of the census' append argument sites maps onto exactly one text flow or carries a reason.

| profile   | list flows |  text | not text | elem unknown | type-only | struct-only |  both | Strong | Undecided | NotText | Unknown |
| --------- | ---------: | ----: | -------: | -----------: | --------: | ----------: | ----: | -----: | --------: | ------: | ------: |
| `-O1` / A |     11,818 | 4,431 |    1,788 |        5,599 |        58 |       1,772 | 2,601 |    185 |     2,561 |       2 |   1,683 |
| B         |     12,146 | 4,473 |    1,782 |        5,891 |        65 |       1,826 | 2,582 |    205 |     2,588 |       0 |   1,680 |
| C         |     13,647 | 5,344 |    1,648 |        6,655 |        52 |       3,673 | 1,619 |    186 |     3,045 |       0 |   2,113 |
| D         |     23,886 | 7,783 |    2,389 |       13,714 |       108 |       5,352 | 2,323 |    202 |     4,141 |       0 |   3,440 |
| E         |     22,688 | 7,481 |    2,389 |       12,818 |       108 |       5,038 | 2,335 |    202 |     3,947 |       0 |   3,332 |
| F         |     22,807 | 7,619 |    2,387 |       12,801 |       110 |       5,187 | 2,322 |    202 |     3,945 |       0 |   3,472 |

`h2r tuples`, `--verify`, `h2r laziness`, `h2r parsec`, `h2r fields` and `h2r lists` (with `--axioms`) are byte-identical on `-O1` before and after this milestone.

### Known limits, stated rather than hidden

- **Selection by type is level 4** since M2.4a — `TyCon` identity, not a rendered string. 58 flows rest on it alone. What it still cannot do is see through a type *variable*, and it does not try.
- **The text-head table is asserted.** The entries worth re-reading are the class overrides: calling `eqString` a *complete-output* consumer when its spine demand is a data-dependent prefix is a claim about what a representation decision turns on (the whole text is the subject of the comparison), not about how many cells are walked. `isPrefixOf` was deliberately **not** overridden, so it stays a prefix consumer.
- **`unpackCStringAscii#` has no axiom, and M2.3e established that it must not get one.** The 27 call sites in `ShellCheck.Formatter.JSON` and `.JSON1` are `$text-2.0.2$Data.Text.Show$$wunpackCStringAscii#`, and the `case` that consumes each one binds `(# ByteArray#, Int#, Int# #)`: it builds a `Data.Text.Text`, not a `[Char]`. It is invisible to M2.3c and to this milestone because it is not a list function at all, so the refusal is correct rather than a coverage loss. `unpackFoldrCString#` does not occur in this program.
- **5,599 flows are element-type-unknown.** Most are flows with no bound binder, no `(:)` alternative and no text-shaped consumer — nothing in the dump says what their elements are, and nothing here guesses.
- **1,527 flows have an `Unknown` shape.** 2,837 consumers are imported heads neither table knows or points at which the value left the walk; the largest single one is `ShellCheck.Interface.$wgo` (394 consumers). Whole-program work (M2.4), not a missing rule here.
- **Append chains are a lower bound.** An operand that is a parameter, a case, or an imported call counts as one segment and sets `all_literal = false`; the `opaque` field says how many such segments a chain has.
- **No Rust type is chosen.** `StrongStringCandidate` is the name of a conjunction of facts, not a decision. Even `char_semantics_required` does not rule `String` out — it rules out silently treating the value as bytes.

## M2.3e — re-deriving the representation verdicts independently

`h2r verify-rep <dir> [--module M] [--json] [--explain]`.

M2.2's [independent verifier](#the-independent-verifier) is the model: a second walk that shares nothing with the analysis but the IR, re-derives every verdict whose being wrong would be a miscompile, and forces every disagreement to be settled by fixing whichever side is wrong. `h2r-analysis/src/verify_rep.rs` does that for the three M2.3 censuses. It has its own population test, its own constructor test and its own climb-and-enumerate walk, and it **does not use `flow.rs`** — the generic aggregate walk *is* the censuses' walk, so re-deriving a verdict with it would only re-run the analysis being checked.

What it re-derives, and why those and not others:

| claim                   | `-O1` | a wrong one costs                                                      |
| ----------------------- | ----: | ---------------------------------------------------------------------- |
| `Direct` field          | 3,408 | a field's evaluation moves to the construction: a moved divergence     |
| `Dead` field            |     9 | a field that is read is dropped                                        |
| `Recursive` field       |     9 | M1's knot verdict misapplied                                           |
| list `RecursiveKnot`    |    31 | ditto                                                                  |
| `VecCandidate`          |    32 | a shared or infinite spine materialised                                |
| `IteratorCandidate`     |   727 | a spine that is re-entered or retained turned into a one-shot iterator |
| `StrongStringCandidate` |   185 | a value whose characters are observed treated as opaque text           |

A wrong `Deferred` / `Persistent` / `Undecided` / `Unknown` only costs coverage, so nothing re-derives those.

### The two semantic dependencies, stated

Two things are *asserted* rather than derived anywhere in this compiler, and re-deriving them would mean inventing a second unchecked assertion rather than checking the first. The verifier therefore consults **the same** tables:

- the [library demand-semantics table](#the-library-demand-semantics-table) and the [text-head table](#the-text-head-table). What the verifier re-derives itself is everything around them: that the head really is an import, its stable name, which value argument of the call the value lands in, how many value arguments the call supplies, and hence which row applies;
- **M1's** `Class::RecursiveValue`, which every milestone reads rather than re-derives.

Everything else — aliasing, reachability, scrutiny, storage, escape, traversal counting — is re-derived from the arena.

### What it found

| dump                 | claims | re-derived | **disagreements** | coverage refusals |
| -------------------- | -----: | ---------: | ----------------: | ----------------: |
| `-O1` (and matrix A) |  4,401 |      4,391 |             **0** |                10 |
| B                    |  5,277 |      5,266 |             **0** |                11 |
| C                    |  6,127 |      6,112 |             **0** |                15 |
| D                    | 16,810 |     16,795 |             **0** |                15 |
| E                    | 15,111 |     15,096 |             **0** |                15 |
| F                    | 15,077 |     15,062 |             **0** |                15 |

That is the state *after* the fixes below. The first run refused **483 of 4,431 claims on `-O1`**, and those refusals were five different things — three of them the verifier being blunt, two of them the census over-claiming, in the unsafe direction.

**Two census bugs, both in `L7-CONSED-AS-TAIL`'s successor fixpoint.** A flow consed onto another cell is a *suffix* of that longer spine, and the fixpoint propagated the longer spine's `SpineDemand`, `HeadDemand`, `Storage`, short-circuits and streaming back to it — but **not its `Reuse`**. So a spine whose longer form was walked twice, shared a tail, or escaped to a head with no axiom stayed `SinglePass`, and 21 flows on `-O1` were called `IteratorCandidate` on that basis. `Reuse` now travels those edges with the other facts, ranked `SinglePass < MultiPass < Escapes < SharedTail`, and a flow that is *both* consed onto a longer spine and has a spine consumer of its own is entered at least twice.

The second was `tail_derived`'s closure over known-local calls. It marked a callee's parameter tail-derived as soon as *one* call site handed it a tail-derived argument, so a parameter that also receives the whole spine from another call site had its scrutiny counted as a continuation of someone else's traversal rather than as a new entry. That under-counts traversals, which is the unsafe direction, and contradicted the milestone's own stated rule that a parameter's uses are the union over every call site. It now requires **every** call site to hand it a tail-derived argument.

Together those moved `VecCandidate` 49 → 32 and `IteratorCandidate` 740 → 713 (727 after the new axioms), and `PersistentCandidate` 1,951 → 2,197.

**Three blunt spots in the verifier, and in each of them the verifier was the wrong side.** Its first cut was not constructor-relative for a `[]` producer: a nil can only ever select a `[]` alternative, so every `(:)` alternative of a `case` on it — and every occurrence of the case binder inside one — is unreachable for it, which is exactly what M2.3b's [constructor-relative alternative selection](#sum-types-which-alternative-is-the-scrutiny) says. Following them found storage and shared tails that cannot happen, and that was most of the first run's refusals. (A *cons* flow is still followed with both alternatives live, because its tail alias need not be a cons; that is strictly more conservative than the census and can only make the verifier refuse more.) The second: it treated a value stored in a constructor as a non-text-shaped consumer, which is wrong — storage is a fact about lifetime, not about what is demanded, and it is what an `Iterator` claim turns on and what a `StrongString` claim does not. The third: it applied the `Iterator` storage rule to `Vec`, which *requires* storage or re-entry.

### The residue: what the verifier declines to re-derive

Ten refusals on `-O1`, none of them a claim about the census:

|  n | claim               | reason                                               |
| -: | ------------------- | ---------------------------------------------------- |
|  5 | `IteratorCandidate` | `entries-counted-across-a-consed-as-tail-hop`        |
|  5 | `VecCandidate`      | `the-Whole-spine-of-a-loop-is-not-re-derivable-here` |

The first: the verifier counts every consumer reached across an `L7` hop as an independent entry into the spine, because from the suffix's point of view the longer spine's cells *are* these cells. Where the longer spines are alternatives of one `case` — a `go` whose result is consed at five different branches of `ShellCheck.Analytics` — that is one entry at run time and five here. Refusing on it is a coverage loss.

The second: `Whole` for a `go`-loop is M2.3c's `L4-LOOP-WHOLE`, which turns on where the recursive call *stands* (an evaluating position, a constructor field, or under a `case` — `L4` vs `L17` vs `L5`). Re-deriving that would mean writing the loop-position analysis a second time rather than checking it. The verifier establishes every *other* fact those five `VecCandidate` verdicts rest on — no shared tail, no value knot, a spine that is demanded, storage or re-entry — and leaves the `Whole` fact to the census.

`R3-SAME-FRONTIER` is the third thing it declines, for the same reason: it is a statement about the census' own walk. What it does instead is count the `R3` verdicts, because the milestone's claim is that on `-O1` there are **none** — and there are none, on every profile.

### `Direct`, by what actually proved it

|                                                                | `-O1` |
| -------------------------------------------------------------- | ----: |
| `R1-STRICT-FIELD` (GHC made the field strict)                  | 3,323 |
| `R2-FIELD-IS-VALUE` (the expression is already a value)        |    85 |
| …of which the **only** evidence is that it is a string literal | **0** |
| `R3-SAME-FRONTIER`                                             |     0 |

The middle row is the one worth calling out. `R2` accepts a string literal — `unpackCString# "…"#` — and that is the one clause in the whole census that does **not** argue from WHNF: GHC's `exprIsHNF` rejects it, and it is accepted on `okForSpeculation` grounds instead (total, terminating, cheap, so evaluating it eagerly can neither diverge nor error). The verifier accepts it on the same grounds and counts the verdicts that rest on it alone. On `-O1` there are **none**: of the 85, 73 are saturated constructor applications and 12 are variables whose binding GHC itself marks `whnf` or `okForSpec`. The clause is exercised only by its regression test.

### The axiom audit

The unsafe direction for the [axiom table](#the-library-demand-semantics-table) is a wrong **alias** claim, because it turns a `PersistentCandidate` into an `IteratorCandidate`. Every aliasing entry was checked against base-4.18.3.0's own source *and* against a real call site in this dump.

`$base$GHC.List$reverse1` carries the most weight — its accumulator becoming the result's tail is asserted, and 138 consumer sites depend on it. The assertion is that the list is at `End(1)` and the accumulator at `End(0)`; `reverse l = rev l []` makes that the order, and **all 87** `reverse1` call spines in the dump pass a literal `[]` as the *second* value argument and none as the first, which makes the position observable rather than assumed.

| entry                                      | outcome                                                                                                                                                                                                       |
| ------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `reverse1`                                 | confirmed — 87/87 call sites, `[]` second                                                                                                                                                                     |
| `unpackAppendCString#` / `…Utf8#`          | confirmed — 1,086 + 1 call sites, the list is the second argument and becomes the result's tail                                                                                                               |
| `++`, `++_$s++`                            | confirmed — 927 + 68 call sites; the right operand *is* the result's tail                                                                                                                                     |
| `drop`, `span`, `break`, `splitAt`, `tail` | order and suffix-aliasing confirmed against base; **0 call sites in this dump**                                                                                                                               |
| `dropWhile`, `$wspan`, `$wbreak`           | confirmed — 29 / 16 / 6 call sites                                                                                                                                                                            |
| `GHC.Magic.lazy`                           | confirmed — the identity, 72 call sites                                                                                                                                                                       |
| `Data.Foldable.toList`                     | kept; it is a class-method key and the entry is only reached at the list instance, where it is the identity. 0 call sites                                                                                     |
| `GHC.List.concat`, `Data.Foldable.concat`  | **corrected to `NoAlias`.** `concat = foldr (++) []` copies every inner list (each is a *left* operand of `++`), and a `[[a]]` spine cell can never be an `[a]` result cell. 0 call sites, so no output moved |
| `Data.OldList.lines`                       | **corrected to `NoAlias`**, same reasoning: each line is `break`'s freshly built first component, and a `[String]` spine cell is not a `String` cell. 5 consumer sites                                        |

Eleven entries were added, each confirmed from base-4.18.3.0's source *and* from the dump's own types at a call site:

| added                                   | confirmed by                                                                                                                                                                                    | calls |
| --------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----: |
| `$fEqList_$s$c==1`, `$s$c==2`           | ghc-prim's `instance Eq a => Eq [a]`; the dump types both arguments `[Char]`/`[String]` and the result `Bool`                                                                                   | 81, 2 |
| `$fOrdList_$s$ccompare`, `$s$ccompare1` | the matching `Ord [a]` instance; result `Ordering`                                                                                                                                              | 3, 72 |
| `Data.OldList.dropLength`               | `dropLength :: [a] -> [b] -> [b]`, returns a **suffix of the second** argument; the dump's binders are literally `ns`/`hs`/`delta`, `isSuffixOf`'s own names                                    |    11 |
| `Data.OldList.dropLengthMaybe`          | the same, returning `Maybe [b]`                                                                                                                                                                 |    31 |
| `Data.OldList.prependToAll`             | `prependToAll sep (x:xs) = sep : x : …`; separator first, list second, confirmed by the dump's `[[Char]]` second argument                                                                       |     3 |
| `GHC.List.splitAt_$s$wsplitAt'`         | base's local `splitAt' :: Int -> [a] -> ([a],[a])`; the dump shows `Int#` then the list, and a literal `3#`/`1#` count                                                                          |    10 |
| `GHC.List.flipSeq`                      | base's `flipSeq x !_n = x`, "just flip seq": the result **is** the first argument and the second is forced and discarded                                                                        |    11 |
| `GHC.List.init1`                        | base's local `init' :: t -> [t] -> [t]`, floated out of `init`; the dump types the arguments `Token` and `[Token]`                                                                              |     0 |
| `GHC.List.head1`                        | base's `badHead :: HasCallStack => a`, the `head []` error: **no list argument at all**, which the dump confirms (the type argument is the *result* type and the value argument is a CallStack) |     0 |

The last two fire zero times in this dump and are kept as the written record of what they are: `head1` can never be a list consumer, and `init1`'s list argument is never reached by a tracked flow.

Two heads keep their refusal, and for different reasons:

- `$base$Data.OldList$intercalate_$spoly_go1` (3 call spines, **0** consumer sites) — `poly_go` is a name GHC generated; base contains no such definition, so an entry could only be read off the shape of a call site. That is a guess, and the table does not take guesses.
- `$text-2.0.2$Data.Text.Show$$wunpackCStringAscii#` (27 call sites) — it is **not a list function**. Every `case` that consumes it binds `(# ByteArray#, Int#, Int# #)`: it builds a `Data.Text.Text`. M2.3d recorded its absence as a coverage loss; it is not one, and an axiom would have been a soundness bug.

`$base$GHC.List$dropLength`/`dropLengthMaybe` were listed in M2.3c as `GHC.List` helpers; they are `Data.OldList`'s, which is why the dump reports them under that module.

### The text-head overrides, challenged

- **`eqString` is classed `CompleteOutput` although its spine demand is a data-dependent prefix.** *Kept.* The two facts answer different questions and both are recorded: M2.3c says how many cells are walked (a prefix — the comparison stops at the first difference), M2.3d says what the value is *for* (the whole text is the subject of the comparison). A representation decision turns on the second: you do not choose a prefix representation for something that is compared for equality against another whole string. The `Prefix` fact is still there, uncontradicted, and the advisory still refuses `StrongStringCandidate` whenever a `Prefix` *consumer class* is present — which is the safety-relevant use of it.
- **`isPrefixOf` is deliberately not overridden.** *Kept.* It is the case where the prefix really is the value's role: `"foo" isPrefixOf s` reads as much of `s` as it needs and no more, and a representation that can answer it from a prefix is a legitimate choice. Overriding it to `CompleteOutput` would have removed 173 `Affix` consumers' only reason to keep the flow undecided.

### The two derivation orderings, challenged

- **A value knot wins over everything.** *Kept.* `Recursion::RecursiveKnot` is M1's verdict that the binding refers to itself *through the value*; there is no representation that is not a knot for such a thing, whatever the demand facts say, so deciding it first is not a precedence choice but the only correct answer. The 31 flows it covers are all `LazyCandidate`.
- **A proven `SharedTail` outranks an `Unknown` spine.** *Kept at M2.3e — and **reversed at M2.3g**, which is the one M2.3e ruling that did not survive.* The reasoning below is sound about the fact and wrong about the advisory: two owners seeing the same cells is indeed a positive structural fact, but an advisory is a claim of *sufficiency*, and a flow with an unknown consumer supports no such claim. Since M2.3g the fact is kept as the constraint `RequiresTailSharing` and the recommendation is `Unknown` whenever any other fact is — 265 flows moved. The original argument: how much of a spine anyone walks does not change the fact that two owners see the same cells, and `SharedTail` is a *positive* structural fact where `Unknown` is the absence of one; after M2.3e's `Reuse` propagation the rule decided 1,867 flows rather than 1,762, all on `PersistentCandidate` — the safe side. What that missed is that "safe side" is a property of the *fact*, not a licence to publish it as an advisory. The verifier checks the converse directly and always did: no flow it accepts as `Vec` or `Iterator` has a shared tail.

### The adversarial cases

Each shape has a hand-built regression test in `h2r-analysis/src/tests.rs` *and* a count in the real `-O1` dump, printed by `verify-rep`, so that a hand-built test is never the only evidence a rule was exercised.

| #  | shape                                                | in `-O1` | example                              | verdict                                                                                |
| -- | ---------------------------------------------------- | -------: | ------------------------------------ | -------------------------------------------------------------------------------------- |
| 1  | `Foo (error …)` observed only at WHNF                |       53 | `ShellCheck.Checks.ShellSupport` 112 | never `Direct`                                                                         |
| 2a | an unused **lazy** field                             |        7 | `ShellCheck.CFG` 10329               | `Dead`                                                                                 |
| 2b | an unused **strict** field                           |       14 | `ShellCheck.ASTLib` 1626             | **not** `Dead` — forced at WHNF                                                        |
| 3  | forced on one branch, not another                    |      720 | `Main` 411                           | `Deferred`                                                                             |
| 4  | `take 1 (x : expensiveTail)`                         |      179 | `ShellCheck.ASTLib` 1220             | `Prefix(Known)`, never `Vec`                                                           |
| 5  | a `find`/`any` short-circuit                         |      921 | `Main` 140                           | `Prefix(DataDependent)` + short-circuit, never `Vec`                                   |
| 6  | two consumers sharing one tail                       |    1,860 | `Main` 7448                          | `SharedTail` → `Persistent` (or a constraint on an `Unknown`), never `Iterator`        |
| 7  | a finite recursive producer (a `go`)                 |      759 | `Main` 576                           | `FiniteProducer`, not a knot                                                           |
| 8  | an actual recursive list value                       |       30 | `ShellCheck.Analytics` 2042          | `RecursiveKnot` → `LazyCandidate` (one more is a knot whose spine demand is `Unknown`) |
| 9a | stored in another ADT, holder read structurally      |      181 | `Main` 140                           | `StoredIn`, spine facts propagate                                                      |
| 9b | stored in another ADT, holder escapes                |    4,357 | `Main` 74                            | `Unknown`                                                                              |
| 10 | through a higher-order parameter                     |    1,402 | `Main` 349                           | `Unknown` with a reason                                                                |
| 11 | `[Char]` used textually **and** structurally         |      151 | `Main` 135                           | `TextValueUndecided` + `char_semantics_required`, never `StrongString`                 |
| 12 | `foldl'` over a whole list                           |       38 | `Main` 5566                          | `Whole` spine, `IteratorCandidate` not `Vec`                                           |
| 13 | the right operand of `xs ++ ys`                      |    1,770 | `Main` 7448                          | `SharedTail` on `ys`                                                                   |
| 14 | a case-binder alias under an unreachable alternative |        4 | `ShellCheck.Analytics` 99            | no escape — confirmed from both sides                                                  |

Case 14 is the one both sides had to agree on separately: the verifier does its own constructor-relative alternative selection and skips the case binder's occurrences that stand inside an alternative this value cannot take, so `case v of { C x -> k x; D y -> store v }` on a known `C` is not an escape for it either.

### M2.3e acceptance

- `h2r verify-rep` re-derives every `Direct`, `Dead`, `Recursive`, `RecursiveKnot`, `VecCandidate`, `IteratorCandidate` and `StrongStringCandidate` verdict with **0 disagreements** on `-O1` and on all six matrix profiles; the ten remaining refusals are the two weakenings written down above, both coverage-only, both named in the output as `C` rather than `D`.
- `h2r tuples`, `--verify`, `--boundaries`, `h2r laziness` and `h2r parsec` are byte-identical on `-O1` before and after.
- `cargo test` (141), `cargo clippy --all-targets` (0 warnings) and `cargo fmt --check` are clean; `ListAccounting::check`, `FieldAccounting::check` and `TextAccounting::check` still close on all seven dumps.

### Still unsound, or still unchecked

- The axiom table and the text-head table remain **asserted**, and the verifier consults them rather than checking them. What M2.3e added is that every aliasing claim now cites base's own definition and a call site in this dump; the demand claims (`Whole`, `Incremental`, prefix) are still read off contracts and not proved.
- `Produces::SameAsInput` on a polymorphic identity (`GHC.Magic.lazy`) makes every call a list producer regardless of the result type. `flipSeq` was given `NotAList` for exactly that reason, but `lazy`'s 72 call spines were left as they were rather than changing published output on a point the verifier does not depend on.
- The five `VecCandidate` verdicts whose `Whole` fact comes from `L4-LOOP-WHOLE` rest on one walk, not two.

## M2.3f — the representation view, and what the milestone claims

M2.3b/c/d record the facts, M2.3e re-derives every verdict whose being wrong would be a miscompile. This section adds the three things a milestone needs before it can be closed: a **view** that lays one site's proof out so a person can audit it, **provenance** in `h2r show` so any Core node can be asked what the three censuses say about it, and the milestone's own **accounting**, asserted in code and printed by every command. It changes no verdict: `h2r tuples`, `--verify`, `h2r laziness` and `h2r parsec` are byte-identical on `-O1`, and `h2r fields`, `lists`, `text` and `verify-rep` gain sections without a single existing line changing.

```sh
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.CFG --view 10329
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.AST --view-all --json
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --view 1220
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --view 11
cargo run --release --bin h2r -- show ../core-json ShellCheck.AST 5293       # + its M2.3 footers
```

### Three views, each with its own completeness assertion

The **field view** puts every field of one construction on one line — the three facts, the derived rep, and the *route* that proved it — and under it the observations that justify the facts, each with its node ids, plus (for `Unknown`) the escape with its refined reason. `FieldView::check` asserts that every field of the construction appears exactly once and that no line names a field outside its arity:

```sh
$ h2r fields compiler/core-json --module ShellCheck.CFG --view 10329
ShellCheck.CFG node 10329 — Range (program), arity 2, observed
    f0  demand=Never  strict=LazyField  rec=Acyclic  ⇒ Dead  [R5-DEAD]
        D6-FIELD-UNUSED: field 0 bound and unused at node 10360 [start#3315]
        D6-FIELD-UNUSED: field 0 bound and unused at node 10520 [start#3359]
        D6-FIELD-UNUSED: field 0 bound and unused at node 10615 [start#3400]
        D6-FIELD-UNUSED: field 0 bound and unused at node 10664 [start#3406]
        verified: yes   field expression at node 10333
    f1  demand=Conditional  strict=LazyField  rec=Acyclic  ⇒ Deferred  [R4-DEFERRED: bound-and-unused-on-some-observation]
        D5-DEMAND-LAZY: field 1 bound and used at node 10360 [mid1#3316] — mid1
        D6-FIELD-UNUSED: field 1 bound and unused at node 10520 [mid1#3360]
        D5-DEMAND-LAZY: field 1 bound and used at node 10615 [mid1#3401] — mid1
        D6-FIELD-UNUSED: field 1 bound and unused at node 10664 [mid1#3407]
        verified: not a claim   field expression at node 10331
```

`verified:` is `verify_rep`'s answer and only its answer: `yes`, `coverage-refused (<reason>)`, `DISAGREED (<reason>)`, or `not a claim` for the reps nothing re-derives because a wrong one only costs coverage.

The **list view** prints the producer, every cell, every consumer with the rule that classified it *and the demand that one consumer contributes*, the the facts each with the rule that decided it, and the advisory with the fact conjunction it came from. `ListView::check` asserts every consumer appears exactly once. Where a fact is the *absence* of a rule firing — `SinglePass` is "no `L14` and no `L15`" — the view says that rather than naming a rule that did not fire:

```sh
$ h2r lists compiler/core-json --module ShellCheck.ASTLib --view 1220
ShellCheck.ASTLib node 1220 — Nil flow, 2 consumer(s), advisory IteratorCandidate
    producer  node 1220
    consumers (2), each with the demand it contributes
        node 1059    PassedLocal    [T5-PASSED-LOCAL]  spine None / head None, streaming
            handed to the local shortToOpts
        node 1293    Whnf           [T15-WHNF-ALT]  spine Prefix(Known) / head None, streaming
            observed at WHNF (alternative-binds-no-field)
    the facts
        SpineDemand   Prefix(Known)                [T15-WHNF-ALT]
        HeadDemand    None                         [no (:) alternative bound a head]
        HeadExposure  NotExposed                   [no consumer hands an element anywhere]
        Reuse         SinglePass                   [no L14/L15 fired]
        Storage       NotStored                    [no L10/L16 fired]
        Recursion     FiniteProducer               [M1 does not call it a recursive value]
        ShortCircuit  no                           [no short-circuiting consumer]
        traversals    1, every spine consumer streaming [one entry into the spine]
        constraints   none                         [what any representation must support, whatever the advisory says]
    advisory  IteratorCandidate [L-REC-ITERATOR] from Prefix(Known) ∧ None ∧ SinglePass ∧ NotStored ∧ FiniteProducer ∧ streaming
        verified: yes
```

The **text view** is the text facts *on top of* the list view — selection evidence with the rule that established `Char`, shape, per-consumer classes with `(asserted)` marked where `TEXT_HEADS` overrode M2.3c's spine demand, the char-semantics reasons, the append chain — and then prints the whole list view underneath, so the inherited facts are visible rather than cited:

```sh
$ h2r text compiler/core-json --module ShellCheck.Formatter.GCC --view 11
ShellCheck.Formatter.GCC node 11 — text flow, ImportedCall by both, shape TextOnly, advisory TextValueUndecided
    selection (how Char was established: both)
        X1-LIST-TYPE: the flow's binder is TyConApp List [Char] (level 4: structural TyCon identity), rendered "[Char]" (node(s) 11) [lvl#11]
        X2-UNPACK-PRODUCER: $ghc-prim$GHC.CString$unpackCString# produces [Char] by the primitive's type (node(s) 11)
        X5-AXIOM-FIXES-CHAR: GHC.Base.eqString: String -> String -> Bool: the whole text is the subject, though it stops at the first difference (node(s) 184)
    shape     TextOnly [X8-TEXT-ONLY], a string literal
    consumer classes
        CompleteOutput   1
        …
        node 184     Text           class CompleteOutput [X15-COMPLETE-OUTPUT] family Compare (asserted; M2.3c said L8-AXIOM)
    char_semantics_required: true
        L3-HEAD-BOUND: an-element-is-forced(Prefix) at node 11
    advisory  TextValueUndecided [X-ADV-TEXT-VALUE-UNDECIDED]  [character-semantics-are-required]
        verified: not a claim
```

`--view-all --module M` does every site in a module and `--json` dumps the views as structured data. Each has a hand-built regression test: the field view lists every field once, the list view lists every consumer once, and the text view shows the selection evidence (`X5-AXIOM-FIXES-CHAR` on a flow no type would have selected).

### Provenance in `h2r show`

The three proof objects are loaded by default whenever the module has any, exactly as the Parsec and tuple objects are, and `--no-fields`, `--no-lists`, `--no-text` opt out one at a time. They annotate constructions, field binders, producers, cells, tail aliases and consumers inline, and print one footer per site the node takes part in — as itself or as an *occurrence* of one of those binders:

```sh
$ h2r show compiler/core-json ShellCheck.AST 5293 --depth 1
-- in top-level binding $bT_WhileExpression, node 5293
([#5293]{Inner_T_WhileExpression construction, arity 2, Unknown 2}Inner_T_WhileExpression[#5298] c[#5297] l[#5295])

node 5293
  Inner_T_WhileExpression 2 field(s), construction node 5293 (program)
  this node: the construction itself
  f0 demand Unknown / LazyField / Acyclic ⇒ Unknown [verified: not a claim]  [R7-UNKNOWN: the-program-construction-holding-it-escapes (OuterToken)]
  f1 demand Unknown / LazyField / Acyclic ⇒ Unknown [verified: not a claim]  [R7-UNKNOWN: the-program-construction-holding-it-escapes (OuterToken)]
  consumers:
    D7-ESCAPE: the-program-construction-holding-it-escapes at node 5291
  evidence:
    D0-FIELD-CON: Inner_T_WhileExpression of repArity 2 (…), 0 strict field(s) (node(s) 5293, 5298)
    D8-NESTED: field 1 of OuterToken: 0 use(s) of that field follow (node(s) 5291)
    T11-ESCAPE: the-program-construction-holding-it-escapes (OuterToken) (node(s) 5291)
```

A list footer carries the facts and the advisory (`SpineDemand Prefix(DataDependent) [L8-AXIOM] … advisory PersistentCandidate [verified: not a claim]`), and a text footer the consumer classes, the append chain and the text advisory. All five proof objects' marks are concatenated rather than merged, so it stays visible which object said what. `show` verifies only the module it was asked about, so it stays a per-node query and not a whole-program analysis.

### The milestone accounting

Asserted in code (`m23::RepAccounting::check`) and printed by `h2r fields`, `lists`, `text` and `verify-rep` — always whole, so no command shows a fragment of it. The rule is M2.2's, pointing the same way: **any claim the verifier did not confirm, for coverage or otherwise, is unsupported and never proven.**

```text
M2.3 accounting — fields: total = proven-eager + proven-lazy + dead + unsupported
                          total proven-eager  proven-lazy   dead  unsupported
  program !                   0            0            0      0            0
  program                  6736            1          207      4         6524
  library !                3323         3323            0      0            0
  library                  9771           84          788      5         8894
  total                   19830         3408          995      9        15418

M2.3 accounting — lists and text: total = advised + unsupported
                          total      advised  unsupported   advised, by advisory
  list flows              11818         2704         9114   IteratorCandidate 722, LazyCandidate 30, PersistentCandidate 1925, VecCandidate 27
  text flows               4431         2748         1683   NotText 2, StrongStringCandidate 185, TextValueUndecided 2561

M2.3 accounting — the M2 census' argument sites
                                                               total   proven advised-lazy  deferred  unsupported
  the M2 census' 1,996 constructor-field sites                  1996        0           77      1310          609
  …of which the 1,310 list-cons sites, on M2.3c's population    1310       29          303         0          978
  the M2 census' 1,118 append argument sites                    1118        0          226         0          892
```

*proven-eager* is `Direct` **and** re-derived; *proven-lazy* is `Deferred` plus `Recursive` where it was re-derived. `Deferred` needs no second walk and gets none: a wrong `Deferred` loses an optimisation and cannot miscompile, which is exactly the criterion that decides what `verify-rep` checks. The ten coverage refusals show up here as the difference between M2.3c's published 32 `VecCandidate` / 727 `IteratorCandidate` and the 27 / 722 counted as *advised* — the five and five the verifier declined are unsupported, not advised.

The **route-set histogram** is printed unconditionally, zero rows included, because the overlap between the three `Direct` rules is the interesting part and an absent row hides a zero:

```text
Direct, by the route **set** that proves it (printed in full, zeros included)
     2648  R1
      675  R1+R2
        0  R1+R2+R3
        0  R1+R3
       85  R2
        0  R2+R3
        0  R3
```

M2.3b reports `Direct` by the rule that *fired first* (3,323 `R1`, 85 `R2`, 0 `R3`); this asks all three of every verdict. 675 of the 3,323 GHC-strict fields are **also** already values, so `R2` would have proved them independently — which is a real redundancy, not a coincidence, and it is why the histogram exists. `R3` still proves nothing on the dump, and the regression test that exercises it lands in `R1+R2+R3`, which is the only place all three are visible together.

### The cross-milestone link

Three rules, each narrow, each requiring the verifier's confirmation:

| rule                                 | what the thunk's right-hand side is                                                                                     | why it stops being a thunk                                                    |
| ------------------------------------ | ----------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------- |
| `M23-A-FIELD-ALREADY-A-VALUE`        | a binding whose occurrence is a constructor field proven `Direct` by **`R2`**                                           | the field expression is already a value, so there is no evaluation to defer   |
| `M23-B-SELECTOR-OVER-AN-EAGER-FIELD` | a lazy selection `case c of C .. x .. -> x` over a field proven `Direct`                                                | the field is forced at construction; no deferred selection remains            |
| `M23-C-CELL-OF-A-SINGLE-PASS-SPINE`  | the tail of a cell (or a text append operand) of a `Vec`/`Iterator` flow whose spine demand is `Whole` or `Incremental` | one eager pass consumes the spine, so the cell thunk becomes an iterator step |

```text
Thunk sites explained by M2.3 (M1 × M2.2 × M2.3)
                                                  before  by tuples   by M2.3   after
  sinkable, lands in an evaluating position           14          0         3      11
  sinkable, lands in a lazy position                 254          3         3     248
  memoisation required                              1905         89         5    1811
  recursive value                                     69          0         0      69
  … captured by a many-entry lambda                 1242         80         2    1160
  … shared on one path                               663          9         3     651
  potential thunk sites                             2242         92        11    2139
  by binder origin        FloatOut 5, User 6
  by the rule             M23-A 5, M23-B 1, M23-C 5
```

`remaining + explained-by-tuples + explained-by-M2.3 = 2,242` is asserted, as is "no site is counted twice": a site M2.2 already explains is M2.2's, and the M2.3 walk skips it before it can claim it. The tuple column is read from `link::ThunkLink` rather than recomputed, so the two milestones cannot disagree about who owns a site.

From the other side, **29** of the M2 census' 1,996 constructor-field argument sites stop being lazy positions — all 29 through the list cons, where the spine the argument is consed into is consumed by one eager pass — and **0** of the 1,118 append argument sites do.

**Eleven, and why it is not four hundred.** The number is small and the reasons are structural rather than a missing rule:

- the whole `Deferred` population (986 fields) is *by definition* the thunks that stay: `Deferred` says the evaluation remains where GHC put it;
- the whole `PersistentCandidate` population (1,925 flows) has a shared tail or a second entry, so its cells outlive any one pass;
- 239 flows are `Vec`/`Iterator` over a **prefix** spine, which is precisely a spine whose tail may never be reached — eager consumption of a prefix does not make the unreached tail eager;
- and `M23-A` can almost never fire *by construction*: `R2` accepts a bare variable only when GHC's own `whnf`/`okForSpec` flag is set on its binding, and a binding GHC marks `whnf` is one M1 does not call a thunk in the first place. The five that do fire are the shapes where the flag sits on a different binding from the one M1 reports.

That itemisation is printed by `verify-rep` beside the table, in the same spirit as M2.2's 288 holders: an adjacent population that would make the number larger and the claim weaker.

### M2.3 acceptance

**The criterion is that every claim this milestone makes about *eager* or *streaming* evaluation is re-derived by a second walk that shares nothing with the first but the IR — not that coverage is high.** A wrong `Direct` moves a divergence; a wrong `Vec`/`Iterator`/`StrongString` materialises or one-shots a value that is shared. A wrong `Deferred`, `Persistent` or `Unknown` costs an optimisation, so nothing re-derives those and nothing needs to. And the facts come before the reps everywhere: three orthogonal facts per field, seven per list flow, and the M2.3d facts on top — the rep is a *function* of them, and for lists and text it is explicitly **advisory**, a named conjunction of facts and not a decision about a Rust type.

Against the `-O1` dump, all of the following hold.

**The populations are partitioned and every equation closes.** 9,166 constructions / 19,830 fields, 11,818 list flows, 4,431 text flows; `FieldAccounting::check`, `ListAccounting::check`, `TextAccounting::check` and `RepAccounting::check` all close, on `-O1` and on all six matrix profiles. The three tables are [above](#the-milestone-accounting): 19,830 = 3,408 + 995 + 9 + 15,418 fields, 11,818 = 2,704 + 9,114 list flows, 4,431 = 2,748 + 1,683 text flows, and the 1,996 / 1,310 / 1,118 site tables close the same way.

**Every claim is proven twice.** `h2r verify-rep` re-derives all 4,401 claims — 3,408 `Direct`, 9 `Dead`, 9 `Recursive`, 31 `RecursiveKnot`, 32 `VecCandidate`, 727 `IteratorCandidate`, 185 `StrongStringCandidate` — with **0 disagreements** on `-O1` and on B–F. Ten refusals remain on `-O1`, all coverage-only and both named:

|  n | claim               | refusal                                              | why it is a coverage loss                                                                                                                                                                 |
| -: | ------------------- | ---------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
|  5 | `IteratorCandidate` | `entries-counted-across-a-consed-as-tail-hop`        | the verifier counts every consumer across an `L7` hop as an independent entry; where the longer spines are alternatives of one `case`, that is one entry at run time and five here        |
|  5 | `VecCandidate`      | `the-Whole-spine-of-a-loop-is-not-re-derivable-here` | `Whole` for a `go`-loop is `L4-LOOP-WHOLE`, a statement about where the recursive call *stands*; re-deriving it would be writing the loop-position analysis twice rather than checking it |

All ten are counted as **unsupported** in the accounting, never as advised. `R3-SAME-FRONTIER` is declined for the same reason and there are 0 of them to decline.

**The two census bugs M2.3e found were fixed, and both were in the unsafe direction.** `Reuse` was not propagated across `L7-CONSED-AS-TAIL`, so a spine whose longer form was walked twice, shared a tail or escaped stayed `SinglePass` — 21 flows were `IteratorCandidate` on that basis. And `tail_derived`'s closure marked a callee's parameter tail-derived as soon as *one* call site handed it a tail-derived argument, which under-counts traversals; it now requires **every** call site to. Together they moved `VecCandidate` 49 → 32 and `IteratorCandidate` 740 → 713 (727 after the new axioms), and `PersistentCandidate` 1,951 → 2,197 (1,925 after M2.3g's [ordering correction](#correction-m23g--the-axiom-layer)).

**One axiom would have been a soundness bug.** `$text-2.0.2$Data.Text.Show$$wunpackCStringAscii#` (27 call sites) is not a list function at all — every `case` consuming it binds `(# ByteArray#, Int#, Int# #)` and builds a `Data.Text.Text`. M2.3d had recorded its absence from the axiom table as a coverage loss; it is not one, and an entry would have given a `Text` a `[Char]`'s demand semantics.

**Every adversarial shape has a count in the real dump**, not only a hand-built test — [the table](#the-adversarial-cases) — 53 / 7 / 14 / 720 / 179 / 921 / 1,860 / 759 / 30 / 181 / 4,357 / 1,402 / 151 / 38 / 1,770 / 4, printed by `verify-rep` so a rule can never be exercised by its test alone.

**The two asserted tables are labelled as asserted.** The 101-entry library demand-semantics table and the text-head table sit at evidence level 5 — below def-use dataflow because nothing in the dump proves them, above textual type comparison because they are statements about semantics. Every *aliasing* claim is now confirmed against base-4.18.3.0's own source **and** against a call site in this dump (`reverse1` 87/87 with `[]` second, `unpackAppendCString#` 1,086+1, `++` 927+68, `dropWhile`/`$wspan`/`$wbreak` 29/16/6, `GHC.Magic.lazy` 72); two were **corrected to `NoAlias`** (`concat`, `lines`) and two heads keep their refusal. The *demand* claims (`Whole`, `Incremental`, prefix) are still read off contracts and are not proved.

**No verdict rests on a name.** Every population is selected through GHC's `DataConInfo` or through an import test, never by spelling; the program/library split, the constructor names in the residual and the family attributions are diagnostics. The one thing keyed on a name is the axiom lookup, which is applied **only** to an imported id, with a regression test that a program function called `map` is never looked up.

**The residual, itemised and owned:**

|        |                                                                              | whose problem it is                                                                                                                                                                                                                                                                                                                                                                                                              |
| -----: | ---------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 15,418 | fields `Unknown`                                                             | 2,264 stored in a list cell (M2.3c's population, followed as a spine but not as a field), 311 in a tuple field (M2.2's), 1,919 (998 + 573 + 348) a **program** construction that escapes — `TokenComment`, `OuterToken`, `Comment` — which is M2.4's whole-program work, 1,912 (760 + 595 + 557) a **library** construction that escapes, and 1,708 (1,143 `eta` + 565 `eok`) an unknown higher-order callee → M2.4 higher-order |
|  9,114 | list flows `Unknown`                                                         | 2,228 stored with no visible spine demand in a holder this module never takes apart, 620 in a holder the field census *does* know, 1,718 reaching a holder that escapes, 1,044 an unknown spine demand — and 266 of the 9,114, cutting across those reasons, carry a proven constraint (`RequiresTailSharing`, `RequiresRecursiveLaziness`) beside the unknown                                                                   |
|     80 | imported heads with **no axiom**, 1,545 of the 6,660 imported consumer sites | the largest are `ShellCheck.Interface.$wgo` (394), `GHC.Show.showLitString` (168), `Text.Parsec.Char.string1` (88), `GHC.Show.showList__` (66), `GHC.IO.Handle.Text.hPutStr2` (61), regex-tdfa's `compile` (49), `Data.Set.Internal.$fDataSet1` (45) — whole-program (the ShellCheck ones) or more axioms (the base ones)                                                                                                        |
|  1,683 | text flows `Unknown`                                                         | 2,837 consumers are imported heads neither table knows, or points at which the value left the walk                                                                                                                                                                                                                                                                                                                               |
|  2,345 | text flows with no text-shaped consumer at all                               | the honest measure of how much of ShellCheck's text is handled by code this dump does not contain                                                                                                                                                                                                                                                                                                                                |
|     10 | claims the verifier refuses                                                  | the two weakenings above, both coverage-only                                                                                                                                                                                                                                                                                                                                                                                     |

**How to audit a site.** `h2r show <dir> <module> <node>` for the footers, `h2r fields --view <node>` for the field-by-field proof, `h2r lists --view <node>` for the producer / cells / consumers / facts, `h2r text --view <node>` for the text facts on top of them; `--view-all --module M` for a whole module and `--json` for any of them. All four are shown above.

**Known limits, stated rather than hidden:**

- ~~**rendered types are level-6 evidence.**~~ **Fixed by [M2.4a](#m24a--stable-global-identity-and-structured-types):** dump format 5 carries structured types and selection of `[Char]` is `TyConApp` with a stable `TyCon` (level 4). 58 of the 4,431 text flows rest on the type alone; the population and every verdict are unchanged.
- **`R3-SAME-FRONTIER` is exercised only by its tests.** GHC's case-of-known-constructor has already eliminated every construction scrutinised in the frame that built it, so `R3` fires on nothing in any of the seven dumps. The rule stays, with a positive and a negative regression test, and the route-set histogram is where its absence is visible.
- **the five `VecCandidate` verdicts** whose `Whole` fact comes from `L4-LOOP-WHOLE` rest on one walk, not two — and are therefore counted as unsupported.

`cargo test` (159), `cargo clippy --all-targets` (0 warnings) and `cargo fmt --check` are clean; `h2r tuples`, `--verify`, `h2r laziness`, `h2r parsec` and `h2r compare` are byte-identical on `-O1` before and after M2.3f **and after M2.3g**. All four accounting checks close on all seven dumps.

### Correction (M2.3g) — the axiom layer

*2026-09-14. The acceptance above was written before this review; it is amended here rather than re-stamped.*

**The verifier's 0 disagreements never validated the axiom table.** `verify_rep.rs` re-derives which argument of which saturated call to which *import* a value lands in, and then **reads the table's row for it**. The table is the milestone's asserted semantic dependency: aliasing claims are confirmed against base-4.18.3.0's source *and* a call site in this dump, demand and forcing claims are read off base's definitions. Two independent walks that consult the same asserted table agree about the table by construction. A review of the table's *contents* found three classes of error, none of which the verifier could have caught.

**1. `Produces` conflated "returns a list" with "returns something containing a list" — a population bug.** Any entry whose `Produces` was not `NotAList` made its call an `L0-IMPORTED` producer, so calls whose result is a *pair* of lists, an *action* returning a list, or a polymorphic identity were flows whose producer node is not a list at all. The schema now states the outer return type honestly — `NotAList`, `DirectList(kind)`, `ProductContainsList{components}`, `EffectContainsList(kind)`, `OtherContainsList` — and **only `DirectList` starts a flow**. The other variants keep their argument-demand and aliasing facts for the consumer side; recovering the components is tuple and effect normalisation's work.

| entry                                                   | `Produces` before → after                                           | base                                                                                                                                                                                                |
| ------------------------------------------------------- | ------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `GHC.List.span`, `GHC.List.break`                       | `Incremental` → `ProductContainsList(2)`                            | `span p xs = (takeWhile p xs, dropWhile p xs)` — GHC/List.hs                                                                                                                                        |
| `GHC.List.$wspan`, `GHC.List.$wbreak`                   | `Incremental` → `ProductContainsList(2)`                            | the worker returns `(# [a], [a] #)`; the old note said so and the field still claimed a list                                                                                                        |
| `GHC.List.splitAt`                                      | `Incremental` → `ProductContainsList(2)`                            | `splitAt n xs = (take n xs, drop n xs)`                                                                                                                                                             |
| `GHC.List.splitAt_$s$wsplitAt'`                         | `Incremental` → `ProductContainsList(2)`                            | the specialised worker of `splitAt' :: Int -> [a] -> ([a],[a])`                                                                                                                                     |
| `GHC.List.unzip`                                        | `Incremental` → `ProductContainsList(2)`                            | `unzip :: [(a,b)] -> ([a],[b])`                                                                                                                                                                     |
| `Data.Traversable.mapM`, `forM`, `traverse`, `sequence` | `WholeBeforeFirstCell` → `EffectContainsList(WholeBeforeFirstCell)` | `mapM :: (a -> m b) -> [a] -> m [b]`                                                                                                                                                                |
| `Data.OldList.dropLengthMaybe`                          | `NotAList` → `OtherContainsList`                                    | returns `Maybe [b]`; the old value was honest but said nothing about the suffix inside                                                                                                              |
| `GHC.Magic.lazy`                                        | `SameAsInput` → `NotAList`                                          | `lazy :: a -> a`; `a` is not a list at every call site, which is exactly why `flipSeq` was already `NotAList`. The "known limit" M2.3f recorded about this entry is now fixed rather than tolerated |

**99 `L0-IMPORTED` flows disappeared** on `-O1`: `$wspan` 16, `$wbreak` 6, `splitAt_$s$wsplitAt'` 5, `GHC.Magic.lazy` 72. (`span`, `break`, `splitAt`, `unzip` and the `Traversable` four never occur saturated as producers in this dump — GHC's worker/wrapper had already replaced them — so their rows cost nothing here and are corrected anyway.) 92 of the 99 were `Unknown` and 7 were `PersistentCandidate`.

**2. `HeadDemand` claimed forcing where the axiom only proves exposure.** The enum is documented as "which elements are forced", and entries like `any`, `all`, `find`, `takeWhile`, `elem`, `nub`, `sort` marked heads `Prefix`/`All` — but `any (const True) xs` forces no element, and an `Eq` or `Ord` method may ignore its argument. The fact is split: `HeadDemand` is now **proven forcing only** and the new `HeadExposure` records which callback an element reaches (`Predicate`, `Eq`, `Ord`, `Show`, `Other`), with `BoundAndUsed` for a `(:)` alternative's head binder.

| kept as forcing (and why)                                         | moved to exposure                                                                                                                                                                                                                                                   |
| ----------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `eqString` — at `Char` the comparison is the `eqChar#` primop     | `elem`, `notElem`, `lookup`, `isPrefixOf`, `isSuffixOf`, `isInfixOf`, `nub`, `group`, the four specialised list `==`/`compare` copies → `Eq`/`Ord`                                                                                                                  |
| `and`, `or` — `foldr (&&)`, and `(&&)` case-analyses its argument | `takeWhile`, `dropWhile`, `span`, `break`, `any`, `all`, `find` (both copies) → `Predicate`                                                                                                                                                                         |
| `lines` — `break (== '\n')` on `Char`                             | `sort`, `sortOn`, `maximum`, `minimum` → `Ord`/`Other`; base's `sortOn` `seq`s the computed **key**, not the element                                                                                                                                                |
| `words` — `isSpace` case-analyses the `Char`                      | `sum` → `Other` (`(+)` comes from a dictionary)                                                                                                                                                                                                                     |
|                                                                   | `map`, `filter`, `foldr`, `foldl`, `foldl'`, `zipWith`, `concatMap`, `mapMaybe`, `nubBy`, `sortBy`, `groupBy`, `mapM_`/`forM_`/`traverse_`/`sequence_` and the `Traversable` four, which previously claimed `None` and now say **which** callback sees the elements |

**31 entries had a `head` claim weakened** from `Prefix`/`All` to `None`, and 53 of the 101 now carry a non-trivial `exposure`. On `-O1`, `HeadDemand::Prefix` fell **972 → 544** and `None` rose 5,054 → 5,482; nothing moved into `All`, which had come from `L4`-shaped loops and from `lines`/`words`, both of which are proven. The new fact reads: 5,340 `NotExposed`, 460 `BoundAndUsed`, 401 `Eq`, 61 `Other`, 46 `Predicate`, 7 `Ord` (515 callback exposures in all), 5,503 `Unknown`.

In the text census, `char_semantics_required` now cites which of the two it saw. The flag itself barely moved — an element handed to a callback still has to exist as a `Char` — but the evidence did:

| reason                                |       before |        after |
| ------------------------------------- | -----------: | -----------: |
| `an-element-is-forced`                |          510 |          383 |
| `an-element-is-exposed-to-a-callback` |            — |          161 |
| flows with `char_semantics_required`  | 887 of 4,436 | 882 of 4,431 |

(The five lost are flows the population correction removed; no flow lost the requirement.) The verifier splits the same way: its `StrongString` refusal is `an-individual-character-is-observed` for proven forcing and `an-individual-character-is-exposed-to-a-callback` for exposure. Neither fires on `-O1` — all 185 claims are re-derived — but the distinction is in the walk, not only in the census.

**3. `cycle` and `isInfixOf` encoded the wrong *kind* of demand.** `cycle xs = xs' where xs' = xs ++ xs'` consumes its argument incrementally and **replays** it forever; `Whole` said the call walks to the end before returning, which on an infinite argument never happens. `isInfixOf needle hay = any (isPrefixOf needle) (tails hay)` retries the needle at successive positions: neither spine is necessarily walked whole, and both are re-traversed. The new fact is `Axiom::replays` (end-indexed arguments) and `Reuse::Replayed`, distinct from `Whole`, `MultiPass` and `SharedTail`:

| entry                      | before → after                                                  | base                                                                                                                                                                     |
| -------------------------- | --------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `GHC.List.cycle`           | `Whole` → `Incremental` + replays `End(0)`                      | `cycle xs = xs' where xs' = xs ++ xs'` — GHC/List.hs                                                                                                                     |
| `Data.OldList.isInfixOf`   | needle `Whole` → `PrefixDataDependent`, both arguments replayed | `isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)` — OldList.hs                                                                                      |
| `Data.OldList.isSuffixOf`  | both spines replayed (the `Whole` demand is right here)         | `isSuffixOf ns hs = maybe False id $ do delta <- dropLengthMaybe ns hs; return $ ns == dropLength delta hs` — both spines are walked once to measure and once to compare |
| `Data.OldList.intercalate` | separator replayed, `streaming` true → **false**                | `intercalate xs xss = concat (intersperse xs xss)` — the separator is inserted at every gap and copied by `concat`                                                       |

The rest of the table was searched for the same shape: `dropLength` and `dropLengthMaybe` each make **one** pass — the replay in `isSuffixOf` is at the call site that uses both, and it is recorded there, not in the helpers; a `zip xs xs` style self-reuse is a property of the *call site*, not of the entry, and the walk already records it as two consumers of one flow (`MultiPass`). **None of the four entries carrying a replayed argument — six arguments in all — is called anywhere in these seven dumps, so `Reuse::Replayed` has 0 firings.** It is printed with its zero.

**4. Every `Alias` was type-checked.** `ResultSharesArg(i)` is only possible when the result spine and the argument spine can have the same element type. Two new variants were needed, and the audit is entry by entry:

| entry                                                                            | alias                                                     | base definition it rests on                                                                                                                                                                                                                                                                                                                                                                                                          |
| -------------------------------------------------------------------------------- | --------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `unpackAppendCString#`, `…Utf8#`                                                 | `ResultIsTailOfArg(0)` *kept*                             | `unpackAppendCString# :: Addr# -> [Char] -> [Char]` — the second argument is returned as the tail                                                                                                                                                                                                                                                                                                                                    |
| `GHC.Base.++`, `++_$s++`                                                         | `ResultIsTailOfArg(0)` *kept*                             | `(++) [] ys = ys` — GHC/Base.hs                                                                                                                                                                                                                                                                                                                                                                                                      |
| `GHC.List.tail`                                                                  | `ResultIsTailOfArg(0)` *kept*                             | `tail (_:xs) = xs`                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `GHC.List.reverse1`                                                              | `ResultIsTailOfArg(0)` *kept*                             | `rev [] a = a` — the accumulator is returned                                                                                                                                                                                                                                                                                                                                                                                         |
| `GHC.List.dropWhile`                                                             | `ResultSharesArg(0)` *kept*                               | `dropWhile p xs@(x:xs') = if p x then dropWhile p xs' else xs`                                                                                                                                                                                                                                                                                                                                                                       |
| `GHC.List.drop`                                                                  | `ResultSharesArg(0)` *kept*                               | `drop n xs` returns a suffix                                                                                                                                                                                                                                                                                                                                                                                                         |
| `Data.OldList.dropLength`                                                        | `ResultSharesArg(0)` *kept*                               | `dropLength :: [a] -> [b] -> [b]`; the result is a suffix of the `[b]`, and the types agree                                                                                                                                                                                                                                                                                                                                          |
| `GHC.List.flipSeq`                                                               | `ResultSharesArg(1)` *kept*                               | `flipSeq x !_n = x` — the result *is* the first argument; `Produces` stays `NotAList` because `a` need not be a list                                                                                                                                                                                                                                                                                                                 |
| `GHC.Magic.lazy`                                                                 | `ResultSharesArg(0)` *kept*                               | `lazy :: a -> a`; only `Produces` was wrong                                                                                                                                                                                                                                                                                                                                                                                          |
| `Data.Foldable.toList`                                                           | `ResultSharesArg(0)` *kept*                               | at the list instance, `toList = id`                                                                                                                                                                                                                                                                                                                                                                                                  |
| `GHC.List.span`, `break`, `$wspan`, `$wbreak`, `splitAt`, `splitAt_$s$wsplitAt'` | `ResultSharesArg(0)` → **`ResultContainsSuffixOfArg(0)`** | the suffix is the pair's *second component*; the outer result is a pair, and the two axes must not be spelled with one field                                                                                                                                                                                                                                                                                                         |
| `Data.OldList.dropLengthMaybe`                                                   | `ResultSharesArg(0)` → **`ResultContainsSuffixOfArg(0)`** | the suffix is inside the `Just`                                                                                                                                                                                                                                                                                                                                                                                                      |
| `GHC.List.head`, `last`, `!!`, `$w!!`                                            | `NoAlias` → **`ResultSharesElementOf(i)`**                | `head (x:_) = x`, `last`/`(!!)` likewise return an *element*: when the elements are lists the result shares cells with one of them, and that is **not** a shared tail on this spine                                                                                                                                                                                                                                                  |
| `concat`, `Data.Foldable.concat`, `intercalate`, `unwords`, `unlines`, `lines`   | `NoAlias` *kept*                                          | `concat = foldr (++) []` (GHC/List.hs) makes every inner list a **left** operand of `(++)`, so it is copied — even the final `xs ++ []`; `intercalate xs xss = concat (intersperse xs xss)` (OldList.hs) inherits that; `unlines (l:ls) = l ++ '\n' : unlines ls` and `unwords (w:ws) = w ++ go ws` copy every line and every word, the last one included (the Report-prelude `foldr1` `unwords` would share it; base-4.18 does not) |
| every remaining entry                                                            | `NoAlias` *kept*                                          | result cells are freshly allocated                                                                                                                                                                                                                                                                                                                                                                                                   |

`ResultContainsSuffixOfArg` still puts `RequiresTailSharing` on the **input** flow — `span`'s second component really does keep the argument's cells alive — while the call itself is no longer a producer. That is the point of separating the axes. `ResultSharesElementOf` is the one category M2.3e could not express; it is *not* assigned to `concat`, `intercalate`, `unwords` or `unlines`, where base copies, but to the four entries whose result **is** an element.

**5. The advisory ordering was wrong about what an advisory means.** A proven `SharedTail` and M1's `RecursiveKnot` used to be decided *before* the `Unknown` checks, so "one known property points this way" was published as `PersistentCandidate`/`LazyCandidate` — which reads as "this representation is sufficient". It is not sufficient when another consumer is unknown. Every `Unknown` fact now wins, the positive facts are recorded as constraints, and the accounting counts a constrained `Unknown` as unsupported like any other:

| moved | from → to                         | constraint it now carries   |
| ----: | --------------------------------- | --------------------------- |
|   265 | `PersistentCandidate` → `Unknown` | `RequiresTailSharing`       |
|     1 | `LazyCandidate` → `Unknown`       | `RequiresRecursiveLaziness` |

**The tables, before → after, on `-O1`:**

| `h2r lists`                   |      before |                                                                            after |
| ----------------------------- | ----------: | -------------------------------------------------------------------------------: |
| flows                         |      11,917 |                                                                       **11,818** |
| `L0-IMPORTED` producers       |       5,065 |                                                                        **4,966** |
| `SpineDemand::Unknown`        |       5,602 |                                                                        **5,503** |
| `HeadDemand::Prefix` / `None` | 972 / 5,054 |                                                                  **544 / 5,482** |
| `HeadExposure` (new)          |           — |                 5,340 NotExposed, 460 BoundAndUsed, 515 callbacks, 5,503 Unknown |
| `Reuse::SharedTail`           |       1,867 |                                                                        **1,860** |
| `VecCandidate`                |          32 |                                                                               32 |
| `IteratorCandidate`           |         727 |                                                                              727 |
| `PersistentCandidate`         |       2,197 |                                                                        **1,925** |
| `LazyCandidate`               |          31 |                                                                           **30** |
| `Unknown`                     |       8,930 |                                                                        **9,104** |
| constraints (new)             |           — | 1,860 tail sharing, 31 recursive laziness, 0 replay; 266 of them on an `Unknown` |

| `h2r text`                         | before |     after |
| ---------------------------------- | -----: | --------: |
| text flows                         |  4,436 | **4,431** |
| `char_semantics_required`          |    887 |   **882** |
| — of those, `an-element-is-forced` |    510 |   **383** |
| — of those, exposed to a callback  |      — |   **161** |
| `StrongStringCandidate`            |    185 |       185 |
| `Unknown`                          |  1,688 | **1,683** |

| `h2r verify-rep`                               |             before |                  after |
| ---------------------------------------------- | -----------------: | ---------------------: |
| claims checked / re-derived / refused          | 4,401 / 4,391 / 10 | **4,401 / 4,391 / 10** |
| disagreements                                  |                  0 |                  **0** |
| shape 6 (a tail in a second place)             |              1,867 |              **1,860** |
| shape 8 (a value knot)                         |                 31 |                 **30** |
| shape 9b (holder escapes)                      |              4,297 |              **4,357** |
| shape 10 (higher-order parameter)              |              1,355 |              **1,402** |
| shape 11 (`[Char]` textual **and** structural) |                156 |                **151** |
| shape 13 (right operand of `++`)               |              1,777 |              **1,770** |

| accounting                | before                            | after                      |
| ------------------------- | --------------------------------- | -------------------------- |
| list flows                | 11,917 = 2,977 + 8,940            | **11,818 = 2,704 + 9,114** |
| text flows                | 4,436 = 2,748 + 1,688             | **4,431 = 2,748 + 1,683**  |
| the 1,310 list-cons sites | 29 + 402 + 879                    | **29 + 303 + 978**         |
| the M1 link               | 2,242 = 2,139 + 92 + 11           | **unchanged**              |
| fields                    | 19,830 = 3,408 + 995 + 9 + 15,418 | **unchanged**              |

All four accounting `check()`s close on `-O1` and on all six matrix profiles, where the flow counts fall by 99 / 127 / 101 / 101 / 101 / 101 and the text counts by 5 each, with **0 disagreements** and the same 10 / 11 / 15 / 15 / 15 / 15 coverage refusals as before.

**What is still asserted rather than proven.** The same thing as before, now stated where it belongs: **the axiom table is this milestone's semantic dependency.** Its aliasing claims are checked against base's source and a call site; its demand, replay and forcing claims are read off base's definitions and are not derived from anything in the dump. The verifier consults it and cannot confirm it. What M2.3g adds is that each of those claims now has a field of its own, so a wrong one is a wrong *statement* rather than a conflation — and `h2r lists --axioms` prints all six per entry.

**Regression gate.** `h2r tuples`, `--verify`, `h2r laziness`, `h2r parsec` and `h2r compare` are byte-identical on `-O1` before and after M2.3g. `h2r fields`'s own census output is byte-identical too; the only lines of it that move are the two rows of the shared M2.3 accounting block that belong to lists and text. `cargo test` 144 lib tests (151 in all crates, 10 of them new and adversarial: a pair-returning head is not a producer, a product- or effect-returning head is not a producer, only `DirectList` may produce, `cycle` is incremental and replayed, `isInfixOf`'s needle is replayed, `concat` shares neither spine nor element, an element alias is not a shared tail, a predicate exposes without forcing, a primop does force, and a shared tail beside an unknown consumer is `Unknown` with a constraint).

## M2.4a — stable global identity and structured types

Two things the earlier milestones had to work around were properties of the *dump*, not of the program:

- the imported-id table was keyed by GHC **unique**, which [M2.1 showed is not an identity](#scoping-uniques-are-not-unique) — 116,340 binders share 42,572 uniques — so the one place a unique was still a linkage key was the last place a merge could hide;
- every type arrived only as GHC's **pretty-printed string**, so "the element is a `Char`" was a textual comparison (level 6) against the four spellings `Char`, `GHC.Types.Char`, `[Char]`, `String`, `FilePath` that GHC might print.

Dump format 5 removes both. The format bump is the whole of this milestone: **no analysis was allowed to change its mind about anything.**

> *The current format is **6**, which keeps every field below with the same name and shape and changes what a consumer may conclude from them: the program is the one after GHC's `CoreTidy`, not before it. The contract is set out field by field in [dump format 6](#dump-format-6), and both formats load.*

### The format

```jsonc
{ "format": 5,
  "module": "ShellCheck.Parser", "unit": "ShellCheck-0.11.0-inplace",

  // Every *global* Id referenced in the module, keyed by stable name.
  // Locals are not here at all.
  "ids": { "$base$GHC.Base$eqString": { "name": …, "arity": 2, "dmdSig": … } },

  // The module's types, hash-consed. Children are indices, and every child
  // index is smaller than its parent's, so the table rebuilds in one
  // forward pass with no recursion.
  "types": [
    { "kind": "TyConApp", "tycon": { "name": "$ghc-prim$GHC.Types$Char",
                                     "occ": "Char", "unique": "3g" },
      "args": [] },                                        // 16
    { "kind": "TyConApp", "tycon": { "name": "$ghc-prim$GHC.Types$List",
                                     "occ": "List", "unique": "3Q" },
      "args": [16] }                                       // 17  =  [Char]
  ],
  // … also TyVar{name,occ,unique}, AppTy{fun,arg}, FunTy{mult,arg,res},
  //     ForAllTy{binder,body}, LitTy{litKind,lit}, Opaque{pretty}
  //     (a CastTy or CoercionTy, which nothing downstream reads).

  "binds": [ … ]   // every binder, every `Type` node and every `case`
                   //   result type carries  "ty": <index>  next to the
                   //   "type": "<rendering>" it already carried
}
```

**Identity.** `nameStableString` is `$unit$Module$occ`. It is the key of the id table and of every `TyCon`. Uniques are still dumped — on `Var` nodes, binders, type variables and type constructors — and are now **diagnostics only**; the loader rejects format 4 with a message that says to re-extract. The check that this is sound is not an argument but a count: of the 44,992 occurrences the resolver classifies as `Ref::Global` on the `-O1` dump, **0** carry `isGlobal = false` and **0** have no entry in the table, and the 2,972 stable names in the new tables are in bijection with the 2,972 distinct global uniques the old ones held.

**Where the module's own top-level binders went.** Nowhere: they were never in the table. GHC globalises a module's top-level binders in CoreTidy, which runs *after* the simplifier, so at the point this plugin runs they are `LocalId`s and `isGlobalId` is false for them. That is the right answer anyway — they are bound in the module, so `Module::resolve` resolves their occurrences lexically to their binders, and a binder is the authoritative source for arity and demand where an occurrence's `IdInfo` may be stale. `Scope::head_sig` reads the id table only when nothing in the module binds the head.

**Types.** The plugin emits the `expandTypeSynonyms` form, so `String` and `FilePath` arrive as `TyConApp List [TyConApp Char []]` and no consumer has to know either name. The unexpanded rendering stays alongside in `"type"`, which is what `h2r`'s reports print — a label, never a verdict. The Rust side rebuilds the table into owned `Ty` values and adds `Ty::is_char`, `list_elem`, `is_list_of`, `fun_args`/`fun_result`, `tycon` and `Ty::alpha_eq` (structural alpha-equivalence, iterative, over a worklist).

**Size.** Interning matters: `ShellCheck.Parser` has 61,494 type occurrences over 1,041 distinct renderings, and its table has 9,516 entries (19,944 over all 28 modules). Emitting types inline would have multiplied the dump; emitting a table, and dropping the 32,789 local entries the id table no longer needs, made it **smaller** — 82,171,834 → 78,691,280 bytes on `-O1`, −4.2%.

### What moved up the evidence hierarchy

`X0-ELEM-TYPE` and `X1-LIST-TYPE` in [M2.3d](#m23d--which-of-those-flows-are-text-and-what-is-done-with-them), and the `X7`/`element-type-unknown` refusals with them, now read `TyCon` identity: **level 4, GHC type compatibility**, where they were level 6. Nothing else moved. In particular [M2.1's](#m21--proving-parsecs-cps-roles) `R1-LAYOUT`, `R1-UNPARSER-SIG`, `R1-TYPE-AGREE` and `R1-TRAILING-ERASURE` still read rendered types and still sit at levels 4/5 with `alpha_normalise`; migrating them is a later milestone's work and needs its own gate, so it was deliberately left alone here.

### The gate

The acceptance condition was that **not one semantic number changes**. All 113 reports — `stats`, `laziness`, `parsec`, `tuples` (plus `--verify` and `--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus `--heads` and `--explain`), `verify-rep` (plus `--explain`), the `--json` form of each, and `compare` — were captured on the old binary and the old dumps; the dumps were then re-extracted with the new plugin (`-O1` and all six matrix profiles) and every report re-captured and diffed.

**86 of the 113 are byte-identical**, `h2r compare` over all six profiles among them. The 27 that are not:

| what                              | diff                                                                                                                                                                                                                               |
| --------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `text`, `text --heads` (×7 dumps) | 17 lines each: the header paragraph, and three labels that said "level 6" / "type-string" / "a rendered type". Every count identical.                                                                                              |
| `text --explain`                  | 5,451 lines: 2,598 `X1-LIST-TYPE` and 61 `X0-ELEM-TYPE` evidence notes, 59 `type-string only` → `type only` labels, and the 17 above.                                                                                              |
| `text --json`                     | the same 2,659 notes, plus 58 `element_type_evidence` values renamed `TypeStringOnly` → `TypeOnly`.                                                                                                                                |
| `laziness --json`                 | 5,395 `unique` strings (below). Identical field-for-field once `unique` is removed.                                                                                                                                                |
| `parsec --json`                   | each region's edge *list order*, and `binder_unique` (below). Every region's edge multiset is identical modulo that field, and the accounting is identical.                                                                        |
| `parsec` on B, C, D               | one line each: the `e.g.` exemplar of a reject-reason histogram. **Pre-existing nondeterminism**, reproduced by running the *same* binary on the *same* dump twice; the counts never move. Not introduced here and not fixed here. |
| `matrix/<P>/provenance` (×6)      | `date`, `repo_head`, `repo_dirty_inputs`, `plugin_sha256`, `binary_sha256`. `stripped_source_sha256`, `flags`, `ghc`, `cabal`, `modules` and `binary_version` are unchanged, and the module lists are identical.                   |

**GHC renumbered the uniques, and nothing noticed.** Re-extracting with the new plugin shifted GHC's unique supply: **98,135 of the 116,340 binder uniques changed.** Compared field by field with uniques and the new type index excluded, the two dumps differ in **2,124 strings in total, all of them pretty-printed demand signatures that embed a unique** (`{a8Ia->M!P(L) …}` → `{a8Jr->M!P(L) …}`) — the Core is otherwise identical node for node, which is why every node id in every report is unchanged. That 98,135 uniques can move without a single census number moving is the strongest statement available that no analysis keys by one; it is what [M2.1](#scoping-uniques-are-not-unique) set out to make true and what this milestone finished.

**And the two element-type readings agree.** `rendered_element` is kept beside `structured_element`, and `elem_readings_disagree` compares them flow by flow. Over all **seven dumps — 11,818 / 11,818 / 12,146 / 13,647 / 23,886 / 22,688 / 22,807 list flows — it reports 0 disagreements**: the structured reading selects exactly the flows the string reading did. The linkage check runs beside it: of the `Ref::Global` occurrences (44,992 on `-O1`, 99,824 on D), **0** carry `isGlobal = false` and **0** are missing from the stable-name id table, on every dump.

`cargo test` (159 — eight new: the `Ty` helpers, `alpha_eq`, the type table's forward-reference refusal, the format-4 rejection, and three that make a fixture's rendering and its structure disagree on purpose to show which one a rule reads), `cargo clippy --all-targets` (0 warnings) and `cargo fmt --check` are clean.

## M2.4b — the closed-world class-op census

Two questions are easy to run together and must not be: *which instance and which method can run at this site?* and *can the dictionary disappear?* **A known method target is not a removable dictionary.** This milestone answers only the first. What bears on the second — is the dictionary forced, could it be bottom, is it also used as an ordinary value — is recorded as an *observation*, with no verdict attached; the verdict is M2.4c's.

`h2r classops` takes as its population **every application spine whose head is a class-op selector**, decided by GHC's own `isClassOpId` through the one signature lookup (`K0-CLASSOP-SITE`), never by a name. On `-O1` that is **565 sites**. Superclass selectors (`$p1Ord`) *are* class ops, so superclass selection is both a member of the population and a dictionary source, and one mechanism handles both.

The [residual-laziness census](#m2-baseline--who-receives-the-lazy-arguments) leaves **294** class-op *argument* sites in the unresolved tier. Each is an argument of exactly one population site, and the mapping is asserted: **294 of 294 map**, on all seven dumps. The other 271 population sites are class-op applications the census never counted, because none of their arguments is a non-trivial computation in a lazy position.

### The answer

|                                                           |   `-O1` |      |
| --------------------------------------------------------- | ------: | ---: |
| population — class-op application sites                   | **565** |      |
| … `Exact(target)`                                         |   **0** |   0% |
| … `FiniteSet(targets)`                                    |   **0** |   0% |
| … `Unresolved`                                            | **565** | 100% |
| … partially-applied selectors (the selector is the value) |       0 |      |

`population = Exact + FiniteSet + Unresolved` is asserted, and so is the 294 mapping.

**Not one residual class-op site in ShellCheck has a statically known dictionary.** That is the finding, and it is not a weakness of the walk: the walk resolves dfuns, dfuns applied to argument dictionaries, superclass chains, dictionary-constructor fields read back by a `case`, lexical aliases and the parameters of local functions (its nine unit tests exercise each, and produce `Exact` and `FiniteSet(2)` where a dictionary is statically known). The reason it finds none here is that GHC has **already taken every such site**: a selector applied to a visible dfun is exactly what the simplifier rewrites to the instance method. What survives optimisation is, by construction, only the dispatch whose dictionary is a *run-time* parameter. Of the 565 dictionary arguments, 499 are lambda parameters, 41 are superclass selections applied to one, 19 are bound by a `case` alternative and 6 are `let`-bound superclass selections — **none is a dfun**.

| by class                  | sites |   | by class    | sites |
| ------------------------- | ----: | - | ----------- | ----: |
| Applicative               |   191 |   | Monoid      |    55 |
| Show                      |    91 |   | Eq          |    54 |
| Monad                     |    69 |   | Functor     |    38 |
| Exception                 |    17 |   | Ord         |    11 |
| Ranged (ShellCheck's own) |    11 |   | MonadState  |     9 |
| MonadReader               |     7 |   | MonadWriter |     7 |
| Num                       |     2 |   | Semigroup   |     2 |
| Foldable                  |     1 |   |             |       |

Every site's class is identified, and 524 of the 565 from the *structured type* of the dictionary argument (`K2-DICT-TYPE`, level 4) rather than from any name; the remaining 41 are superclass selections, whose class the selector's own name gives (level 1) and whose table entry the dump's `repArity` checks.

### Why each site is unresolved

|     | reason                                                                                                                                                                                                                                                                                             | representative                  |
| --: | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------- |
| 252 | the dictionary is a parameter of an **exported** function — callers outside this module cannot be enumerated                                                                                                                                                                                       | `ShellCheck.AST` node 3465      |
| 280 | the dictionary is a parameter of an instance method (`$ctraverse` 220, `$cfoldMap` 53, `$cfoldMap'` 3, `$celem`/`$cmaximum`/`$cminimum`/`$csum`/`$cproduct` 1 each, `$fTraversableInnerToken` 2) — a function **reached only through dispatch**: its callers are the class-op sites that select it | `ShellCheck.AST` node 6559      |
|  17 | the dictionary is read back from a **constructor field** (`SomeException`'s existential `Exception` dictionary, 11 in `Main` + 6 in `Paths_ShellCheck`)                                                                                                                                            | `Main` node 659                 |
|   7 | the **instance method is not in the dump**: mtl's `$fMonadStatesReaderT` (5), `$fMonadStatesParsecT` (2) — the instance is known exactly, its body is in another package with no unfolding                                                                                                         | `ShellCheck.Parser` node 128333 |
|   6 | the dictionary expression reached is not a constructor application (the mtl chains above, at a second step)                                                                                                                                                                                        | `ShellCheck.Parser` node 138963 |

The second row is the one that says what a closed-world specialiser would have to do. An instance method's dictionary parameter is bound at *dispatch* time, by whichever dictionary the selector site used; enumerating it means propagating dictionaries **forward through dispatch**, and that is only sound if no dictionary of that class escapes into code the dump cannot see. It does — 166 of the 565 sites have a dictionary that is also used as an ordinary value — so the union is not claimed here. Nothing is guessed.

### Dictionary sources in the closed world

| kind                                                                                           | `-O1` |
| ---------------------------------------------------------------------------------------------- | ----: |
| dfun — a top-level binding whose type is a class constraint                                    |   259 |
| dfun applied at a use site, building an instance dictionary                                    |   609 |
| dictionary-constructor application (`C:Show f g h`)                                            |    10 |
| superclass selection (`$p…`)                                                                   |    72 |
| local (`let`) dictionary binding                                                               |   206 |
| dictionary parameter of a function                                                             |   216 |
| dictionary bound by a `case` alternative                                                       |    35 |
| … of all of these, admitted on their *name* because the class table does not carry their class |   838 |
| … whose binding is not in the dump at all                                                      |   681 |

The closed world is every module in the dump, indexed by stable name, so a dfun defined in `ShellCheck.AST` is followed from `ShellCheck.Analytics`; `--module` and `--class` restrict the *report*, never the resolution.

### The class table, and why there is one

One thing the dump cannot answer: **which field of a dictionary a selector reads**. Class-op selectors are globals, and format 5 carries no type and no unfolding for a global, so neither the selector's type (`C a => …`) nor its `case d of C:C … m … -> m` body is available. The field order is therefore asserted per class — 17 classes, in the style of the [list axioms](#correction-m23g--the-axiom-layer) — and **every use of an entry is cross-checked against that dictionary constructor's own `repArity` in the dump**. Over all seven dumps the check reports **0 disagreements**, and **0** sites fall outside the table.

### The rules

| rule                | level | what it says                                                             |
| ------------------- | ----: | ------------------------------------------------------------------------ |
| `K0-CLASSOP-SITE`   |     5 | the spine head is a class-op selector — GHC's `isClassOpId`              |
| `K1-DICT-ARG`       |     2 | the first value argument of a class-op application is the dictionary     |
| `K2-DICT-TYPE`      |     4 | the class is the head `TyCon` of the dictionary's structured type        |
| `K3-CLASS-TABLE`    |     5 | the method's field index, checked against `repArity`                     |
| `K4-SUPERCLASS-SEL` |     1 | `$pN<Class>` selects superclass field N-1                                |
| `K5-ALIAS`          |     3 | a `let`-/top-bound dictionary is followed to its right-hand side         |
| `K6-DFUN`           |     3 | a global dictionary is followed to its binding in the closed world       |
| `K7-DICT-CON`       |     2 | a saturated dictionary-constructor application is a dictionary           |
| `K8-PARAM-UNION`    |     3 | a local function's dictionary parameter is the union over its call sites |
| `K9-METHOD-FIELD`   |     2 | the method target is the dictionary's field at the method's index        |
| `K10-FORCED`        |     5 | a class-op application forces its dictionary (strict field selection)    |
| `K11-DICT-ESCAPES`  |     3 | the dictionary is also used as an ordinary value                         |
| `K12-PARTIAL`       |     2 | the selector is applied to no value argument: the selector is the value  |

### Dictionary-evaluation observations (no verdict)

|                                                                   | `-O1` |
| ----------------------------------------------------------------- | ----: |
| the selector application forces its dictionary (`K10`)            |   565 |
| the dictionary is a variable GHC records as strict at its binder  |   247 |
| … with no strictness recorded: nothing here says it is not bottom |   277 |
| the dictionary is also used as an ordinary value (`K11`)          |   166 |

The first row is every site, and it is the fact M2.4c has to answer to: a class op is a strict field selection, so a site that dispatches on a dictionary also *evaluates* it. Whether that matters — whether the dictionary can be erased anyway — is the next milestone's question.

### Across the flag matrix

|                             | A `-O1` | B `-O2` |       C |       D |       E |       F |
| --------------------------- | ------: | ------: | ------: | ------: | ------: | ------: |
| class-op sites (population) |     565 |     587 |     595 |     595 |     595 |     596 |
| … resolved to a target      |       0 |       0 |       0 |       0 |       0 |       0 |
| census sites mapped 1:1     | 294/294 | 305/305 | 314/314 | 314/314 | 314/314 | 314/314 |
| class-table disagreements   |       0 |       0 |       0 |       0 |       0 |       0 |
| classes outside the table   |       0 |       0 |       0 |       0 |       0 |       0 |
| dfun bindings               |     259 |     259 |     271 |     282 |     282 |     282 |
| dfun applications           |     609 |     646 |     639 |     558 |     558 |     564 |

### The gate

Every earlier report — `laziness`, `parsec`, `tuples`, `tuples --verify`, `fields`, `lists`, `text`, `verify-rep` — is **byte-identical** before and after this milestone: the census adds a population, it changes no existing one. `cargo test` (**172** — thirteen new: a selector on a known dfun, a dfun applied to an argument dictionary, a dfun parameter appearing in a field, a superclass selection followed to its superclass, a class cross-check that refuses, a two-call-site union, an exported function's parameter, a dictionary read from a constructor field, a partially applied selector, a dictionary also used as a value, the source enumeration, a dfun followed across modules, and an imported dfun that names its instance and refuses the method), `cargo clippy --all-targets` (0 warnings) and `cargo fmt --check` are clean.

Aggressive specialisation (D–F) does not resolve a single one, which is the same finding as the flag matrix's: GHC's specialiser has already taken everything it can take, and the residue is dispatch on a run-time dictionary. Closed-world specialisation is ours to do, and this census says exactly what it would have to prove: the dictionaries reaching 252 exported functions' parameters, and the dictionaries that reach 280 instance-method parameters through dispatch.

## M2.4c — whole-program dictionary flow, and whether the dictionary can go

[M2.4b](#m24b--the-closed-world-class-op-census) answered *which method can run here* one module at a time and found **0 of 565** sites resolved: every dictionary was a run-time parameter. It also said what a closed-world specialiser would have to do, and this milestone does it — and, separately, asks the question M2.4b refused to mix in.

### The closed-world assumption, stated

The 28 modules of the dump are **the entire program**, and `Main.main` is its only root. Nothing outside the dump calls into ShellCheck's library modules: there is no plugin interface, no `dlopen`, and the `prop_*` corpus — the only other importer — is what `striptests` removes from a production build. This is `W0-CLOSED-WORLD`, and it is an **assumption**: the dump cannot prove it. Everything in Part 1 rests on it, which is why it is written into `dictflow.rs`'s header, into `h2r dictflow`'s first paragraph, and here.

Under it, an exported function's dictionary parameter *does* have an enumerable producer set: the union over **all** call sites in **all** modules, found by stable name through the global occurrences of the function (`W1-GLOBAL-CALLERS`) — unless the function is also used as a value, which makes the set unenumerable exactly as [`boundary.rs`](#composing-the-views-can-all-1453-be-applied-at-once) found for tuples.

### Part 1 — the fixpoint

`crates/h2r-analysis/src/dictflow.rs` is a whole-program worklist over one abstract set per dictionary parameter. Dictionary **values** are dictionary-constructor applications, dfuns applied or not, and superclass selections of those (`W2-DICT-VALUE`); **parameters** accumulate the union of what reaches them across modules (`W3-PARAM-UNION`); **dispatch** (`W4-DISPATCH`) is what makes it more than a call graph: a class-op site with a known dictionary set selects, per dictionary, the method at the class's field index, and where that method is a separate binding in the dump — `$fTraversableInnerToken_$ctraverse` and its kin — the site's own remaining arguments *are* that binding's actual arguments, so the method's dictionary parameters are fed from the dispatch and propagation continues through it.

The analysis is **monovariant** (`W5-MONOVARIANT`): one abstract value per dictionary identity, one set per parameter, no calling context. It loses precision and never soundness. Anything it cannot account for taints (`W6-TAINT`): a `Top` set at a class-op site means *any* instance of that class could be selected there, including one outside the dump, so every method at that class's field index is tainted too — that is how the taint crosses dispatch in the other direction. Budgets are stated and exceeding one is `Unresolved`, never a guess (`W7-BUDGET`): 40 rounds, 32 dictionaries per set, 4,000 expression steps per evaluation, 8 nested field reads. **On all seven dumps the fixpoint settles in 7 rounds and no budget is hit.**

### What it found

|                             | per module (M2.4b) | whole program |
| --------------------------- | -----------------: | ------------: |
| class-op sites (population) |                565 |           565 |
| … `Exact(target)`           |              **0** |         **7** |
| … `FiniteSet(targets)`      |                  0 |             0 |
| … `Unresolved`              |                565 |           558 |

`population = Exact + FiniteSet + Unresolved` is asserted. Seven sites — all of `Ranged`, ShellCheck's own class, dispatching on `$fRangedPositionedComment` — now have a known method. That is the whole of the improvement in *method targets*, and stating only that would be misleading, because the fixpoint did far more than seven sites' worth of work:

> **the dictionary set is bounded at 118 of the 565 sites** (74 reach exactly one instance, 44 reach exactly two) **and at 106 of the 216 dictionary parameters.**

`ShellCheck.Parser`'s `parseScript`, `readArray`, `readNewlineList`, `tryWordToken` — 36 dictionary parameters in all — resolve their `$dMonad` to exactly `{$fMonadIdentity, $fMonadIO}` — the two monads ShellCheck really runs the parser in, proved by enumerating every caller in the program. The *method* stays `Unresolved` only because `$fMonadIdentity` and `$fMonadIO` are `base`'s, and their method bodies are not in the dump. Per the milestone's own rule, the target is the instance method's stable name only when GHC exported it as a separate binding referenced somewhere in the dump; otherwise `Unresolved(instance-method-not-in-the-dump)`, with the instance named. Nothing is guessed.

### Why the other 558 are unresolved

|           | reason                                                                                                                                                                         | representative                            |
| --------: | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------- |
|       413 | the function holding the dictionary parameter is **unreachable**: it has no occurrence anywhere in the closed world, so under `W0` nothing can name it and the site never runs | `ShellCheck.AST` node 3465 (`doAnalysis`) |
|        53 | `instance-method-not-in-the-dump($fMonoidDual)` — `$cfoldMap`'s `Monoid` is `Dual (Endo …)`, `base`'s                                                                          | `ShellCheck.AST` node 27756               |
|        48 | `instance-method-not-in-the-dump($fMonadIO)`                                                                                                                                   | `ShellCheck.Checker` node 49              |
|        17 | the dictionary is read from a **non-dictionary constructor field** (`SomeException`'s existential)                                                                             | `Main` node 659                           |
|         9 | the method sits in a dictionary field **no class-op site in the program ever selects**: it is never dispatched                                                                 | `ShellCheck.AST` node 6501                |
| 7 + 5 + 1 | mtl's `$fMonadStatesParsecT`, `$fMonadStatesReaderT`, `$fMonadReaderrParsecT` — instance known, body in another package                                                        | `ShellCheck.Parser` node 138695           |
|         4 | the dictionary is **returned by a call the dump cannot see**                                                                                                                   | `ShellCheck.AnalyzerLib` node 734         |
|         1 | dispatched from a site whose own dictionary is unknown                                                                                                                         | `ShellCheck.AST` node 27609               |

The first row is the milestone's most uncomfortable finding and it is not an artefact. **922 of the 2,235 top-level bindings in the dump are never referenced anywhere in it** — `doAnalysis` occurs exactly once in all 28 modules, as its own binder. They are ShellCheck's exported library API, whose only other consumers are the `prop_*` corpus and downstream packages, neither of which is in a production build. Under `W0` they are dead code, and 413 of the 565 class-op sites live in them. M2.4b called these "parameter of an exported function"; the closed world says something sharper and less flattering: most of that population is not reachable at all.

The taint over the 216 dictionary parameters, for comparison: 90 unreachable, 12 never dispatched, 4 from a call the dump cannot see, 3 a function used as a value, 1 dispatch-tainted — and 106 bounded.

### Part 2 — erasure agreement, a separate proof object

> **A KNOWN METHOD TARGET IS NOT A REMOVABLE DICTIONARY.**

This is the exact analogue of M2.2.1's *locally removable is not globally composable*. Part 1 says which method runs and says **nothing whatever** about whether the dictionary itself can disappear: a dictionary with one known instance may still be forced where erasure would move divergence, stored in a constructor, or handed to a callee the dump cannot see. The verdicts below come from facts recorded **separately** from Part 1, and the two are crossed rather than collapsed.

- **Evaluation** (`E1-TOTAL`). A class-op application is a strict field selection, so it forces its dictionary; replacing `classOp d x` by `method x` changes behaviour only if `d` could be ⊥. A dictionary-constructor or dfun application *is* a value, so a boundary all of whose producers are such values is total and erasure moves no divergence; a parameter GHC records as strict is forced at entry already.
- **Representation agreement** (`E2-AGREE`, `E3-CLONE`). Every producer at every boundary a dictionary crosses must request the same erased form — the same instance. One instance ⇒ `Erasable`. Several, at a function that is never used as a value (which is what kept the set finite), ⇒ `ErasableWithClone`, one clone per instance, **counted, never made**.
- **Escape** (`E4-ESCAPE`). Used as an ordinary value — stored, passed to an imported callee, handed to a non-dictionary parameter — ⇒ `Preserve`, with the holder named.

| verdict             | dictionary values | dictionary parameters |
| ------------------- | ----------------: | --------------------: |
| `Erasable`          |               102 |                    36 |
| `ErasableWithClone` |                 0 |                     4 |
| `Preserve`          |                89 |                    84 |
| `Unresolved`        |                 0 |                    92 |
| **total**           |           **191** |               **216** |

`values = Erasable + WithClone + Preserve + Unresolved` and the same for parameters are both asserted. The four `WithClone` parameters cost **8** clones between them (two instances each); no value needs one, a value being one instance by construction.

The dominant reasons: 133 `passed to a callee outside the dump` (a `base` dfun handed to a `base` function), 80 `function-is-unreachable-in-the-closed-world`, 40 `used as an ordinary value`, 7 `method-is-never-dispatched`, 4 `dictionary-returned-by-a-call-the-dump-cannot-see`, 1 dispatch-tainted.

### The two questions, crossed

The 3×4 matrix is asserted to sum to the population:

| target ⟍ dictionary | `Erasable` | `ErasableWithClone` | `Preserve` | `Unresolved` |
| ------------------- | ---------: | ------------------: | ---------: | -----------: |
| `Exact`             |          7 |                   0 |      **0** |            0 |
| `FiniteSet`         |          0 |                   0 |      **0** |            0 |
| `Unresolved`        |         10 |                   0 |        154 |          394 |

The bolded cells are the population this milestone exists to keep separate: a site whose method is known but whose dictionary must survive anyway — a dispatch on a preserved dictionary. On `-O1` it is **0**, which is a result, not an absence: the seven resolved sites all dispatch on a dictionary that nothing else holds. The other direction is populated and just as instructive: **10 sites whose dictionary is `Erasable` still have no known method target**, because the instance is `base`'s and its body is not here. Erasability and dispatch resolution are independent, and the matrix shows it in both directions.

### Across the flag matrix

|                                 | A `-O1` | B `-O2` |       C |       D |       E |       F |
| ------------------------------- | ------: | ------: | ------: | ------: | ------: | ------: |
| class-op sites                  |     565 |     587 |     595 |     595 |     595 |     596 |
| … `Exact`                       |       7 |       7 |       7 |       0 |       0 |       0 |
| sites with a bounded dictionary |     118 |     138 |     140 |      65 |      65 |      65 |
| parameters bounded / total      | 106/216 |  98/210 | 109/222 |  64/223 |  64/223 |  72/231 |
| values `Erasable` / total       | 102/191 | 102/191 | 101/191 | 139/238 | 139/238 | 139/238 |
| parameters `Erasable`           |      36 |      28 |      34 |      28 |      28 |      28 |
| clones a `WithClone` would cost |       8 |       6 |       8 |      12 |      12 |      12 |
| fixpoint rounds                 |       7 |       7 |       7 |       7 |       7 |       7 |

Aggressive specialisation (D–F) makes the whole-program answer *worse*, not better: it duplicates dictionaries into more inline constructor applications (238 values rather than 191) and loses the seven `Ranged` targets. Specialising harder does not help a closed-world analysis; it scatters the evidence.

### A hazard the milestone had to fix

A top-level binder GHC has not externalised carries an **internal** name — `$_in$$ctraverse`, `$_sys$$fTraversableInnerToken` — and those are **not unique**: `ShellCheck.AST` alone has three distinct top-level bindings whose name is `$_sys$$fTraversableInnerToken`. [M2.4a](#m24a--stable-global-identity-and-structured-types)'s bijection is over the *global Ids a module refers to*, which are external by construction; it says nothing about a module's own un-externalised binders. So `dictflow.rs` keys every dictionary identity by `Module#node` of its constructor application, keeps the name for the report only, and puts nothing with an internal name into the cross-module linkage table. The check that this is enough is a count: **0 global `Var` occurrences in the whole dump carry an internal name**, so nothing can refer to one from another module anyway. `classops.rs`'s `World` has the same latent collision and is not reachable through it for the same reason; it was left alone rather than changed under a byte-identity gate. (M2.4c′ closes it, and finds that the "external ⇒ unique" test was itself too weak — see [Correction (M2.4c′)](#correction-m24c--totality-is-not-the-same-fact-as-identity).)

### The CLI

`h2r classops` gains `--whole-program` (**on by default**), which appends the re-derivation and the erasure section to the M2.4b report, and `--per-module`, which reproduces M2.4b exactly. `h2r dictflow <dir> [--explain] [--json]` prints the closed-world assumption, the fixpoint, both tables and the 3×4 matrix (M2.4c′ adds a fifth verdict column, the totality table and the owner-level clone plan).

### The gate

Every earlier report — `laziness`, `parsec`, `tuples` (plus `--verify`), `fields`, `lists`, `text`, `verify-rep` — is **byte-identical** before and after, and so is `h2r classops --per-module` (plus `--explain` and `--json`) against M2.4b's `h2r classops`. `cargo test` (**181** — nine new: one caller in the closed world giving `Exact`, two callers in two modules giving `FiniteSet(2)`, a third module using the function as a value making it unenumerable, dispatch feeding an instance method's own dictionary parameter, a tainted producer unresolved downstream, the set budget exceeded, an `Exact` target on an escaping dictionary `Preserve`d, two instances costing one clone each, and two dictionaries sharing an internal name staying distinct), `cargo clippy --all-targets` (0 warnings) and `cargo fmt --check` are clean.

### What remains, stated rather than hidden

- The closed world is an **assumption**. If ShellCheck is built as a library for someone else, 413 of the 565 sites stop being dead and the answer changes.
- The analysis is monovariant: a dfun applied to two different argument dictionaries has one identity here. A call-string or per-instantiation analysis would split some of the 44 two-instance sites.
- `Unresolved` for a parameter is not a proof that it *cannot* be erased, only that this proof object declines to say so.
- A dictionary reaching an imported callee is `Preserve`d on the strength of the callee being outside the dump; a hand-written Rust replacement for that callee could take the erased form instead, and 133 of the 265 non-`Erasable` verdicts are that case. The lowering, not this analysis, decides those.

### Correction (M2.4c′) — totality is not the same fact as identity

The `Part 2` verdicts above were computed with a bug the project owner's review of `96e4733` found. `erasure()` decided `Erasable` from `!x.set.is_top()` and the instance count — but `eval_nested()` is a **MAY**-analysis of which dictionary values an expression can produce: for a `case` it walks the alternatives' right-hand sides and ignores the scrutinee entirely. "Bounded dictionary identity" had silently become "the producer is total". The counterexample:

```haskell
f d    = classOp d x
main   = f (case bottom of A -> knownDict; B -> knownDict)
```

The set is exactly `{knownDict}` — the old code says `Erasable` — but the selector forces `d` (`K10`), and deleting the dictionary computation deletes the divergence. `known_strict` was recorded on the parameter and copied to the report and **never consulted**; and consulting it would not have helped, because strictness at entry is not permission to drop the force: if the parameter disappears, its entry force still has to happen somewhere.

#### An independent totality domain

`Totality` is now its own lattice, propagated by its own transfer in its own fixpoint, sharing the settled dictionary sets **only** to resolve dispatch. The chain is `ProvenTotal < MustPreserveForce < Unknown`, bottom `ProvenTotal`, join `max`.

| rule                     | level | what it says                                                                                                                                                   |
| ------------------------ | ----: | -------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `E6-TOTALITY-VALUE`      |     2 | a saturated dictionary-constructor application, a dfun applied or not, and a superclass selection out of a `ProvenTotal` dictionary are values ⇒ `ProvenTotal` |
| `E6-TOTALITY-CASE`       |     5 | a `case` whose scrutinee is not *already evaluated* ⇒ `MustPreserveForce`, **even when every alternative yields the same dictionary**                          |
| `E6-TOTALITY-LET`        |     3 | a let- or top-bound dictionary inherits its right-hand side's totality                                                                                         |
| `E6-TOTALITY-PARAM`      |     3 | a parameter is the join over the totality of every producer that reaches it                                                                                    |
| `E6-TOTALITY-UNKNOWN`    |     3 | through a call the dump cannot see, a non-dictionary constructor field, a higher-order parameter, or a budget ⇒ `Unknown`                                      |
| `E6-TOTALITY-OBLIGATION` |     5 | `Erasable` requires `ProvenTotal`, **or** a named `ForceObligation`; strictness is evidence, never a verdict                                                   |
| `E7-OWNER-CLONES`        |     3 | a function's clones are its distinct call-site assignment tuples                                                                                               |

*Already evaluated* is deliberately narrow: a value (a literal, a lambda, a saturated constructor application, a dfun), a variable bound by an enclosing `case`, or a variable GHC marks strict **and** that an enclosing `case` on that same binder dominates. Strict-at-entry alone does not qualify — GHC's promise is that the force happens, not that it has happened *here*.

*Corrected by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found): "a variable bound by an enclosing `case`" was still too wide. It admitted every **alternative** binder, and matching an outer constructor forces the constructor, not its fields — the binder of a lazy field is an unevaluated thunk. Only the scrutinee binder and the binder of a field GHC marks strict qualify.*

The verdict is then: `ProvenTotal` ⇒ identity decides as before; `MustPreserveForce` ⇒ `ErasableWithObligation { at, what }`, naming the node whose evaluation erasure would delete and the scrutinee that must still be evaluated, or `Preserve(erasure-would-delete-a-force)` when no obligation can be expressed; `Unknown` ⇒ `Preserve(totality-unknown-erasure-could-move-divergence)`.

*Amended by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found): `ErasableWithObligation` carries the whole obligation **set**. The join kept one witness, so a dictionary standing behind two distinct forces was erased against one of them.*

#### Erasure tables, before → after

| verdict                  | values before | values after | parameters before | parameters after |
| ------------------------ | ------------: | -----------: | ----------------: | ---------------: |
| `Erasable`               |           102 |          102 |                36 |               36 |
| `ErasableWithObligation` |             — |            0 |                 — |                0 |
| `ErasableWithClone`      |             0 |            0 |                 4 |                4 |
| `Preserve`               |            89 |           89 |                84 |               84 |
| `Unresolved`             |             0 |            0 |                92 |               92 |
| **total**                |       **191** |      **191** |           **216** |          **216** |

**No verdict moved, and that is a result rather than a no-op.** The totality domain answers, over the 216 dictionary parameters: **118 `ProvenTotal`, 0 `MustPreserveForce`, 98 `Unknown`** (asserted to sum to 216). The 40 erasable parameters are all `ProvenTotal`; the 98 `Unknown` ones were already `Preserve` or `Unresolved` on escape or on a `Top` set. The reason `MustPreserveForce` is **0** is stronger than "nothing changed": an instrumented run shows the walk reaches **no `case` node at all** on any dictionary path in the dump — GHC's `-O1` floats every dictionary out of every scrutinee. The old code was unsound *in principle* and, on this program, accidentally right. It is now right on purpose, and the counterexample is a unit test.

Named force obligations carried: **0**.

The matrix gains a column and no cell moves:

| target ⟍ dictionary | `Erasable` | `ErasableWithObligation` | `ErasableWithClone` | `Preserve` | `Unresolved` |
| ------------------- | ---------: | -----------------------: | ------------------: | ---------: | -----------: |
| `Exact`             |          7 |                        0 |                   0 |      **0** |            0 |
| `FiniteSet`         |          0 |                        0 |                   0 |      **0** |            0 |
| `Unresolved`        |         10 |                        0 |                   0 |        154 |          394 |

#### Clone planning is per owner, not per parameter

`ErasableWithClone(n)` is a per-**parameter** cardinality and `Accounting` used to **sum** it: 4 parameters × 2 instances = **8 clones**. That is not a clone plan. A function needs one specialisation per *distinct assignment tuple actually seen at its call sites* — one tuple per call site, deduplicated — which is neither the sum nor the product of the per-parameter cardinalities. The cardinalities stay, as evidence.

On `-O1` all four `WithClone` parameters belong to four different single-parameter functions, and each has exactly **one** call site:

| module              | function            | dictionary parameters | cardinalities | tuples seen |    clones |
| ------------------- | ------------------- | --------------------: | ------------- | ----------: | --------: |
| `ShellCheck.Parser` | `allspacingOrFail`  |                     1 | `[2]`         |           1 |         1 |
| `ShellCheck.Parser` | `commentWarning`    |                     1 | `[2]`         |           1 |         1 |
| `ShellCheck.Parser` | `readNormalLiteral` |                     1 | `[2]`         |           1 |         1 |
| `ShellCheck.Parser` | `splitBy`           |                     1 | `[2]`         |           1 |         1 |
|                     |                     |                       |               |   **total** | **8 → 4** |

The "2 instances" never meant two call sites: it is one call site whose dictionary argument is itself a two-instance parameter, which the monovariant analysis (`W5-MONOVARIANT`) can only give as a *set*. Such a tuple is counted as the one call site it is, so **4 is a lower bound** — the true figure is between 4 and 8 and only a call-string analysis can close it. Every set-valued tuple is flagged in the report rather than smoothed over.

`-O2` and the specialising profiles make the same point more loudly: in D–F the four parameters collapse onto **two** two-parameter functions, `parseProblemAtWithEnd` and `shouldIgnoreCode`, each with cardinalities `[3, 3]` — a sum of 12 and a product of 9 — whose call sites use only 3 and 4 distinct tuples: **12 → 7**.

| clone plan                                                 |  A `-O1` |   B `-O2` |         C |        D |        E |        F |
| ---------------------------------------------------------- | -------: | --------: | --------: | -------: | -------: | -------: |
| per-parameter cardinality sum (the old number)             |        8 |         6 |         8 |       12 |       12 |       12 |
| owner-level clones (distinct tuples)                       |    **4** |     **3** |     **4** |    **7** |    **7** |    **7** |
| owning functions                                           |        4 |         3 |         4 |        2 |        2 |        2 |
| parameters `ProvenTotal` / `MustPreserveForce` / `Unknown` | 118/0/98 | 110/0/100 | 121/0/101 | 77/0/146 | 77/0/146 | 85/0/146 |

#### Identity cleanups

- `classops::World::new` keyed `tops` by `b.name` with `or_insert`, which admits internal, non-unique names exactly as the hazard above describes. It now admits only external stable names, as `dictflow::Program` does, and **asserts there is no collision**. Doing so found a second defect: `is_external_name` split `$_sys$poly_$j` into unit `_sys`, module `poly_`, occurrence `$j` and passed it as external. GHC's `nameStableString` renders a non-external name as `$_sys$<occ>` or `$_in$<occ>` with no unit and no module, and when that `<occ>` itself contains a `$` — GHC's worker/wrapper and join-point names are full of them — the three-way split is fooled. Two distinct top-level bindings of the dump claim `$_sys$poly_$j`. Rejecting the two pseudo-units makes *external ⇒ unique* true rather than nearly true, in `dictflow`, `higher` and now `classops` alike. **Collisions asserted: 0.** No target-enumeration number moved.
- The doc comments on `scope.rs` and on `Ref::Global` still said a GHC *unique* is the key into the imported-id table. It is not, and has not been since dump format 5: the key is the stable name. Corrected.
- `KVar`/`KAll` interning in the plugin and free-type-variable comparison in `Ty::alpha_eq` **still rest on GHC uniques**. `alpha_eq` alpha-maps *bound* type variables but compares *free* ones by unique, and free type variables are not scope-identified: format 5 carries no lexical identity for a type variable, and a unique is not unique in an optimised dump. So `alpha_eq` must not be used for any free-tyvar-sensitive proof until a later format carries lexical type-variable identity; every current caller compares closed or same-scope types. This is now stated on the function.
- The "**922 unreachable top-level bindings**" above are the **zero-reference subset** under `W0` — bindings with no occurrence anywhere in the dump. That is a valid *dead* subset (nothing can name them, so they cannot run), but it is **not** a `Main.main`-rooted transitive reachability set: a binding referenced only by another unreachable binding is not in it. M3 needs the rooted set, and will have to compute it.

#### The gate for this correction

Every report is byte-identical before and after except `dictflow` and the erasure section of `classops` — `stats`, `higher`, `tuples`, `fields`, `lists`, `text`, `verify-rep`, `laziness` and `compare`, with `--explain` and `--json`, on `core-json` and on all six matrix profiles. The target-enumeration half of `dictflow` (Part 1, in full) and of `classops` is byte-identical too; the `classops` diff is exactly its erasure block, six lines becoming ten. `cargo test` is **201** (six new: the `case`-on-⊥ counterexample, an unknown-call producer, a dfun application, a strict parameter with total producers, a strict parameter with one forced producer, and the owner-level clone plan), clippy is 0 and `cargo fmt --check` is clean.

One pre-existing defect surfaced and is **not** fixed here: `h2r parsec --explain` and `h2r parsec --json` are **nondeterministic run to run** — two consecutive runs of the same binary on the same input differ in the order of the per-role edge lines. The multiset of lines, and `h2r parsec` itself, are stable; the ordering comes from a `HashMap` iteration in the report. It predates this milestone and is unrelated to it, but it means those two outputs cannot carry a byte-identity gate until they are sorted.

## M2.4d — higher-order representation agreement

M2.2.1 refused 67 tuple flows because the **closure** that returns the tuple is handed to a local callee's parameter: rewriting the tuple away changes that parameter's type, and the flow does not see the other closures that arrive there. That refusal is not a tuple problem. A formal parameter is one slot and one representation, and a closure's representation is its *arity plus its captured environment*, so the question "can this slot be one representation" has to be asked of every function-valued slot in the program, independently of any flow. This milestone asks it. The 67 are read back out of the answer at the end, as feedback; **no existing verdict changes**.

### The population, by type and nothing else

Three kinds of function-valued boundary, each decided by the structured type (`H1-FUNCTION-TYPED`, GHC type identity — a `FunTy`, or a `ForAllTy` over one), never by a name and never by a rendering:

| kind          | what it is                                                                                | producers are                                                                  |
| ------------- | ----------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ |
| **parameter** | a value lambda binder of function type                                                    | the argument at that index of every call site of its function, in every module |
| **field**     | a constructor field at which some match in the closed world binds a function-typed binder | the argument at that index of every saturated application of that constructor  |
| **return**    | a function whose result, after its manifest value parameters, is still a function         | every syntactic return point of its body, at the deepest lambda depth          |

On the `-O1` dump that is **5,574 boundaries**: 5,464 parameters, 35 fields, 75 returns.

Producers are enumerated **from the IR's own occurrences**, whole-program by stable name under `H0-CLOSED-WORLD` (`H2-PRODUCERS`) — the same discipline [`boundary.rs`](#composing-the-views-can-all-1453-be-applied-at-once) and [M2.4c](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go) use, and for the same reason: a function used as a value, or one nothing in the closed world names, has no enumerable call-site set and the slot is refused rather than guessed. A producer that is itself a boundary — the parameter of a parameter, the result of a known saturated call — contributes *that* boundary's set, in a monovariant worklist fixpoint with the same budgets (`H3-PROPAGATE`). It settles in **10 rounds**; no budget is hit except one set cap, below.

### The shape class, stated conservatively

Two closures can share one representation only when

- they take the **same number of further arguments**, and
- they capture the **same ordered list of types**, compared up to alpha-equivalence of the *structured* type

(`H4-SHAPE-CLASS`). A lambda's captures are the local binders its body reads that it does not bind; a partial application's are the arguments it already holds; a bare known function's are none. A producer whose environment the closed world cannot see — a closure read back out of a constructor field, a closure returned by a call into a library — is **opaque**, and an opaque shape is equal to nothing, not even to another opaque shape.

Where a partial application's argument is not a variable there is no type to read, so it gets a key unique to its node and can never merge with anything: refusing to merge is the conservative direction.

On the `-O1` dump the producers fall into **261 distinct full class keys**. By the printable `(arity, captures)` summary, the commonest are arity 3 with 1, 3 or 5 captures (86 / 77 / 48 boundaries carry one) — Parsec's four-way CPS continuations, closed over the state they were built with.

### Two facts, and only then a verdict

**AN ENUMERATED PRODUCER SET IS NOT ONE REPRESENTATION.** This is the exact analogue of M2.4c's *known method target ≠ removable dictionary*, and it is kept apart the same way: `enumerated` and `classes` are recorded separately on every boundary (`H11-SEPARATE`) and crossed only afterwards.

|                    | one class | several / none |
| ------------------ | --------: | -------------: |
| **not enumerated** |         0 |          5,322 |
| **enumerated**     |   **103** |        **149** |

252 boundaries have a fully accounted producer set. Of those, 103 need exactly one representation and 149 do not — a boundary can have a perfect enumeration of nine producers and still need nine closure types.

### The verdicts

*(The tables in this section are as M2.4d computed them. Six of these numbers are wrong; see [Correction (M2.4d′)](#correction-m24d--sharing-is-decided-before-agreement-and-a-free-type-variable-identifies-nothing) below for what moved and why, and note that `UniformRepresentation` is now called `TypeShapeUniform`.)*

| kind      | ExactClosure | UniformRepresentation | CloneRequired | FiniteClosureSet | Preserve | Unresolved |     total |
| --------- | -----------: | --------------------: | ------------: | ---------------: | -------: | ---------: | --------: |
| parameter |           47 |                    20 |           138 |                0 |        6 |      5,253 |     5,464 |
| field     |            6 |                     0 |             0 |                0 |       10 |         19 |        35 |
| return    |           14 |                     0 |             0 |                1 |       10 |         50 |        75 |
| **all**   |       **67** |                **20** |       **138** |            **1** |   **26** |  **5,322** | **5,574** |

The population is asserted to be the six verdicts, and the per-kind rows to sum to it, in `Accounting::check`. **418 clones** are counted over the 138 `CloneRequired` parameters — one per shape class, counted and never made, exactly as M2.4c counts dictionary clones.

`Preserve` names its holder. The 22 largest are *a closure read back from a constructor field*, which is precisely what one would hope: `SystemInterface`'s three fields, `Checker`'s two, `Formatter`'s two — ShellCheck's records of run-time behaviour really are records of run-time closures, and nothing here pretends otherwise.

### Why the other 5,322 are unresolved

|       |                                                                                               |                                                       |
| ----: | --------------------------------------------------------------------------------------------- | ----------------------------------------------------- |
| 2,660 | the slot's function is used somewhere as a value, so its call sites are not an enumerable set | the same refusal `boundary.rs` and `dictflow.rs` make |
| 1,953 | the slot belongs to an **anonymous** lambda, which has no name to enumerate callers by        | a lambda-lifted naming, or a call-site-directed walk  |
|   413 | a call site of the function is a partial application, so the argument never lands             | the partial application's own consumers               |
|   227 | the function has no occurrence anywhere in the closed world: under `H0` it is dead            | a non-answer, but a different one                     |
|    44 | the body's lambda chain and the binder's type disagree about the return                       | refused rather than picked                            |
|    19 | a closure arrives from a higher-order parameter the analysis does not track                   | the propagation, once the anonymous lambdas are named |
|     5 | the constructor is never applied in the closed world                                          | dead, like the 227                                    |
|     1 | the producer set exceeded the 32-entry budget (`CommandCheck` field 1)                        | a larger budget, or a per-caller analysis             |

The 2,660 and the 1,953 are one shape between them: `ShellCheck.Parser` is CPS, its continuations are anonymous lambdas passed as values, and a higher-order analysis that wants them has to name them first. That is [M2.4e](#m24e--the-41-residual-parsec-continuation-edges)'s ground, and this milestone deliberately does not guess at it.

### Feeding the proof back — nothing is reclassified

Each section below is an **additional column** beside a residual M2.2.1 or M2.1 already recorded. Every fate and every tier stands exactly as it was; `could be reclassified` counts what a *later* pass could act on, and this one does not.

**(a) the 67 `closure-returning-the-tuple-is-passed-into-a-parameter` flows** land on the callee's function-typed parameters, chosen by the callee's own binder types (`H13-LANDING`):

|    |                         |                                                                                                                         |
| -: | ----------------------- | ----------------------------------------------------------------------------------------------------------------------- |
| 31 | `CloneRequired`         | the other closures at the slot disagree; a clone would carry it                                                         |
| 22 | no boundary             | the callee has no function-typed parameter at all — the closure lands on a slot whose type is instantiated out of sight |
| 13 | `UniformRepresentation` | one representation already serves the slot                                                                              |
|  1 | `ExactClosure`          | the flow's own closure is the only one there                                                                            |

**14 of the 67 could be reclassified by a later pass** (the 13 uniform plus the 1 exact): their receiving parameter is *already* one representation, so the reason M2.2.1 refused them — "the other closures reaching the parameter are not in this flow" — is answered. It is answered, not acted on.

**(b) the closure paths of the tuple residual:**

| population | where it lands                      |                                                                                                                                                                                                                                                                                                  |
| ---------: | ----------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
|        187 | passed to an **imported** call      | 187 × no boundary: the receiving parameter belongs to a function outside the dump. `H0` says the *program* is closed; it does not make a library's parameter a slot of it. **0** reclassifiable, and the honest answer is that the lowering of that callee decides, not this analysis.           |
|        134 | **consed onto a list**              | 134 × `Unresolved` on *field 0 of `(:)`* — every cons cell in the program shares one slot, and its producer set blows the budget. A closed-world list-of-closures pass has to split that slot per list, which this one deliberately does not.                                                    |
|        114 | **stored in a program constructor** | 45 `Preserve` (`SystemInterface` and kin: read back as run-time closures), 58 `Unresolved` (mostly the shared `(,)` and `(,,)` fields, the same one-slot-for-everything problem as `(:)`), 11 no boundary (no function-typed field of that constructor is ever read back). **0** reclassifiable. |

**(c) the census' unresolved higher-order sites.** The population is the census' own: computations in lazy or unknown argument positions, still in the unresolved tier once the Parsec proof has been fed back, and — for the first row — outside the Parsec-shaped population, so the 10 sites the recogniser rejected stay M2.1's residual and not this one's.

|                                                      population |                                                                                                                                                                    |                             |
| --------------------------------------------------------------: | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------- |
|     **99** fold/traversal callbacks (`f`, `go1`, `f1`, `ww`, …) | 66 `Unresolved`, 31 no boundary (the head's binder type is not a `FunTy` — a type variable instantiated out of sight), 1 `UniformRepresentation`, 1 `ExactClosure` | **2** could be reclassified |
| **22** computed closures (a `case`- or `let`-selected function) | 22 `Unresolved` — judged as expressions, since a computed closure is not a slot                                                                                    | **0**                       |

The 31 "not function-typed" is worth stating plainly: a third of the control group is not a higher-order *representation* question at all. The callback arrives at a slot whose type is a type variable, so there is no `FunTy` to agree about until the polymorphism is resolved.

**(d) the 41 Parsec continuation edges** are left to M2.4e, which asks this analysis directly rather than re-deriving it: `higher::Higher::verdict_for(module, binder)` returns the boundary a binder names, with its producers, its uses and its verdict.

### The rules

|                     |    level |                                                                                       |
| ------------------- | -------: | ------------------------------------------------------------------------------------- |
| `H0-CLOSED-WORLD`   |        5 | the dump is the whole program and `Main.main` its only root (assumption)              |
| `H1-FUNCTION-TYPED` |        4 | a boundary is function-valued when its structured type is a `FunTy`                   |
| `H2-PRODUCERS`      |        3 | producers are enumerated from the IR's occurrences over the whole closed world        |
| `H3-PROPAGATE`      |        3 | a producer that is a boundary contributes that boundary's set; a monovariant fixpoint |
| `H4-SHAPE-CLASS`    | 2 over 4 | same arity and the same ordered capture types, up to alpha-equivalence                |
| `H5-EXACT`          |        3 | exactly one known producer reaches the slot                                           |
| `H6-UNIFORM`        |        3 | every producer is known and they all fall in one shape class                          |
| `H7-CLONE`          |        3 | disagreeing producers at a local never-a-value parameter cost one clone per class     |
| `H8-PRESERVE`       |        3 | a run-time closure reaches the slot, or the slot is shared outside the rewrite        |
| `H9-TAINT`          |        3 | an unaccountable producer taints the set and the boundary is `Unresolved`             |
| `H10-BUDGET`        |        2 | a walk over budget is `Unresolved`, never a guess                                     |
| `H11-SEPARATE`      |        5 | an enumerated producer set is **not** one representation: separate facts              |
| `H12-USES`          |        3 | uses are read from the occurrences of the boundary's binders, through aliases         |
| `H13-LANDING`       |        4 | a residual closure flow lands on the callee's function-typed slots, by binder type    |

Nothing rests on a name. Binder names appear in the report and in nothing else, and the identity of a producer is `Module#node` (or the stable name of an imported function) for exactly the reason M2.4c gives: an internal top-level name is not unique.

### Uses, for completeness

A slot's uses are read from the occurrences of its binders, through local aliases (`H12-USES`): 10,038 passed on to another slot, 4,255 stored in a constructor, 2,882 called (3 over-applied, 6 under-applied, 236 saturated against a slot whose arity the producers agreed on, the rest at a slot with no agreed arity), 1,849 forced without being applied, 1,022 returned.

### Across the flag matrix

|                 | A (`-O1`) |     B |     C |      D |      E |      F |
| --------------- | --------: | ----: | ----: | -----: | -----: | -----: |
| boundaries      |     5,574 | 6,347 | 8,082 | 34,094 | 31,686 | 31,701 |
| rounds          |        10 |    10 |    11 |     11 |     11 |     11 |
| Exact + Uniform |        87 |   178 |   231 |    862 |    850 |    833 |
| CloneRequired   |       138 |   184 |   227 |  1,006 |    996 |  1,017 |
| Preserve        |        26 |    27 |    26 |     39 |     39 |     39 |

More inlining makes more anonymous lambdas and more boundaries, and the resolved share stays roughly flat: the limit is the anonymous-lambda and used-as-a-value populations, not the fixpoint. The accounting assertion holds on every profile.

### The CLI

```sh
h2r higher compiler/core-json                      # the whole report
h2r higher compiler/core-json --module ShellCheck.Analytics
h2r higher compiler/core-json --explain            # every boundary, producers and uses
h2r higher compiler/core-json --boundary 36827     # just the boundaries touching one node
h2r higher compiler/core-json --json
```

### The gate

Every existing report is byte-identical: `laziness`, `parsec`, `tuples`, `tuples --verify`, `tuples --boundaries`, `fields`, `lists`, `text`, `verify-rep`, `classops`, `dictflow`. `cargo test` is 194 (13 new), `cargo clippy --all-targets` 0 warnings, `cargo fmt --check` clean. No Core is mutated, no codegen is emitted, and no GHC flag changed.

### What remains, stated rather than hidden

- **The anonymous-lambda wall.** 4,613 of the 5,322 unresolved boundaries are one of two things: a slot on a function used as a value (2,660) or a slot on an anonymous lambda (1,953). Both are the same shape — CPS Parsec — and both need a naming pass before a producer set exists at all. The numbers above are therefore a floor, not a ceiling.
- **`(:)` and `(,)` are one slot for the whole program.** Treating a constructor field as a single boundary is sound and useless for the ubiquitous constructors: 134 + 58 of the residual land there. A per-list or per-site field boundary would split them; this one does not.
- **The shape class is conservative on purpose** and merges less than a real closure-conversion would. Two lambdas that capture the same types in a different order, or capture through a `newtype`, are two classes here. Every `CloneRequired` count is therefore an upper bound on the clones.
- **An `Unresolved` is not a proof that a slot cannot be uniform**, only that this proof object declines to say so — the same disclaimer M2.4c makes about erasure.

### Correction (M2.4d′) — sharing is decided before agreement, and a free type variable identifies nothing

The M2.4d tables above were computed with six defects the project owner's review of `3741ec5` found. Every one of them is a place where the proof object said something stronger than its evidence.

#### 1. `H8` was decided after `H5`/`H6`

`judge()` returned `ExactClosure` as soon as one producer reached a slot, and `TypeShapeUniform` as soon as they fell in one class, **before** it looked at `exported` or `valued`. But how well the producers the dump can see agree says nothing about the code outside the rewrite that names the same slot. Constructor fields are collected with `exported: true` on purpose — a constructor's fields are shared by every module that can build or match it — and the -O1 run still reported **6 field `ExactClosure`s**, which is exactly the contradiction. `H8-PRESERVE` is now decided first, and its documentation says so.

#### 2. Two different "one representation" theorems

`Accounting` counted `enumerated && classes == 1` (103) while the method `Verdict::one_representation()` accepted only `ExactClosure | TypeShapeUniform` (67 + 20 = 87). Worse, `Shape::class()` mapped every opaque producer with the same reason to the same string `opaque:<reason>`, although the rule says an opaque shape equals **nothing, not even another opaque one**. Two closures read back out of two different constructor fields were being counted as one representation.

- every opaque producer now carries its own identity (the producer key), so `opaque:` classes never merge;
- there is now **one** statement of the theorem, `Boundary::one_representation()` — enumerated, one class, and no opaque producer — and `Accounting::one_representation` is that method and nothing else;
- the strictly stronger question the *rewrite* asks is named separately, `Verdict::rewritable_as_one()`, and is reported beside it.

|                                                                 | before |   after |
| --------------------------------------------------------------- | -----: | ------: |
| `Accounting::one_representation` (`enumerated && classes == 1`) |    103 |       — |
| `Boundary::one_representation()` (the single theorem)           |      — |  **84** |
| `Verdict::one_representation()` / `rewritable_as_one()`         |     87 |  **66** |
| distinct shape classes                                          |    261 | **353** |

#### 3. The clone count was a sum of per-parameter numbers

`CloneRequired(classes)` is a count **per parameter** and `Accounting` added them up: 418. That is the same mistake M2.4c made and M2.4c′ fixed with `E7-OWNER-CLONES`. Clones are now planned per **owning function** (`H15-OWNER-CLONES`): the function-valued parameters of one function are grouped, the *actual* call-site shape-assignment tuples are enumerated and deduplicated, and the function's clones are its distinct tuples. The per-slot class counts stay as evidence and are never summed. A call site that cannot be enumerated refuses that owner's plan rather than guessing.

|                                            | before |                                                                                       after |
| ------------------------------------------ | -----: | ------------------------------------------------------------------------------------------: |
| per-parameter class cardinality (evidence) |    418 |                                                                                         509 |
| **clones planned**                         |    418 | **53** (→ **68** in [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)) |
| owning functions wanting a plan            |      — |                                                                                          87 |
| plans refused rather than guessed          |      — |                                                                                          66 |

The owners that need clones, largest first:

| module                         | function                 | params | call sites | tuples | clones | per-slot classes |
| ------------------------------ | ------------------------ | -----: | ---------: | -----: | -----: | ---------------- |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      4 |      4 | [1, 1, 4, 3]     |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      4 |      4 | [1, 1, 4, 4]     |
| ShellCheck.Analytics           | `$srunNodeAnalysis`      |      1 |          5 |      3 |      3 | [5]              |
| ShellCheck.Analytics           | `doVariableFlowAnalysis` |      2 |          3 |      3 |      3 | [3, 1]           |
| ShellCheck.CFGAnalysis         | `go15`                   |      1 |          3 |      3 |    3 † | [2]              |
| ShellCheck.CFGAnalysis         | `go15`                   |      1 |          3 |      3 |    3 † | [2]              |
| ShellCheck.CFGAnalysis         | `go4`                    |      1 |          3 |      3 |    3 † | [2]              |
| ShellCheck.Checks.ShellSupport | `go1`                    |      1 |          3 |      3 |    3 † | [2]              |
| ShellCheck.Parser              | `$wpoly_k`               |      1 |          4 |      3 |    3 † | [6]              |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      3 |      3 | [1, 1, 4, 3]     |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      3 |    3 † | [1, 1, 6, 5]     |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      3 |    3 † | [1, 1, 6, 5]     |
| ShellCheck.ASTLib              | `$sgetLiteralStringExt`  |      1 |          5 |      2 |      2 | [2]              |
| ShellCheck.Analytics           | `analyse`                |      1 |          3 |      2 |      2 | [2]              |
| ShellCheck.Parser              | `$wreadIoVariable`       |      3 |          2 |      2 |      2 | [2, 2, 2]        |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      2 |      2 | [1, 1, 4, 3]     |
| ShellCheck.Parser              | `k`                      |      4 |          4 |      2 |      2 | [1, 1, 4, 3]     |
| ShellCheck.Parser              | `k`                      |      4 |          2 |      2 |    2 † | [3, 1, 4, 2]     |
| ShellCheck.Fixer               | `$srealignColumn`        |      2 |          2 |      1 |      1 | [2, 2]           |
| ShellCheck.Parser              | `$wisFollowedBy`         |      1 |          4 |      1 |      1 | [4]              |

† a tuple has a **set-valued** component — one call site whose function-valued argument is itself a multi-class parameter, which the monovariant fixpoint can only give as a set. Those counts are **lower bounds**, closable only by a call-string analysis. `$srunNodeAnalysis` is the point of the correction in one row: five shape classes at one parameter, three clones.

#### 4. Free type variables could merge two unrelated closures

`ty_key()` wrote an unbound type variable as `f<unique>`. A GHC unique is neither module- nor scope-qualified, so two closures in two modules — or two closures under two different `forall`s in one module — whose captures are free variables could get the **same key** and be merged into one shape class. (The `ty_key == alpha_eq` test is not independent evidence: both sides use the same rule, and `Ty::alpha_eq` compares free variables by unique too, which M2.4c′ already recorded as a hazard.) A capture type containing a free type variable now gets a key private to its producer (`H14-FREE-TYVAR`) and merges with nothing.

Distinct shape classes **261 → 332** on -O1 — 71 classes that were being merged on the strength of a free variable's name — and with the opaque identity of defect 2, **353**.

#### 5. Existential/GADT fields were indexed by raw binder position

`alt_field` enumerated *all* the binders of an alternative and skipped the type binders with `continue`, keeping the raw position as the field index. Constructor applications, however, are indexed by **value** arguments. For `case e of C @a dict f -> ...` the runtime field `dict` is value index 0 and was recorded as 1, so a function-valued binder could be paired with the wrong constructor argument and read a producer set that is not its own. A separate value-field counter now does the indexing (`H2-PRODUCERS`), with a test that pins the pairing for a type binder before a function-typed field.

**No number moves on the -O1 dump**, but not for the reason first given here. *(Corrected at [M2.4f](#the-one-correction-this-produced): the original text said ShellCheck's Core has no alternative binding a function-typed field after an existential type binder. It has four — `ShellCheck.Formatter.JSON` nodes 4217 and 4219, `ShellCheck.Formatter.JSON1` nodes 4896 and 4898, all matches on `vector`'s existential `Data.Stream.Monadic.Stream`. Raw binder position would put its step function at field 1 where the value-field counter puts it at field 0; no number moves because that boundary is `Unresolved(constructor-is-never-applied-in-the-closed-world)` at either index.)* The pairing was wrong wherever such an alternative appears, and the flag matrix and any future dump are not the same program.

#### 6. `UniformRepresentation` → `TypeShapeUniform`

`H4` compares arity and the ordered list of captured **Haskell** types: `captures()` feeds `binder_ty` and nothing else to `ty_key`. Calling the result *one Rust representation* contradicts the earlier milestones on purpose-built grounds: M2.1 lets one Haskell type be a thunk or a value, M2.3 lets one be `Vec` or an iterator, owned or borrowed, `String` or `&str`. The verdict is therefore renamed **`TypeShapeUniform`**, and the reading *one Rust representation* is sound **only if** the M3 lowering promises a canonical closure-boundary carrier per Haskell type with conversions inserted at the boundary. **That invariant is open**, and the report says so on every run.

#### The verdicts, before → after (-O1)

| kind      |           | ExactClosure | TypeShapeUniform | CloneRequired | FiniteClosureSet | Preserve | Unresolved | total |
| --------- | --------- | -----------: | ---------------: | ------------: | ---------------: | -------: | ---------: | ----: |
| parameter | before    |           47 |               20 |           138 |                0 |        6 |      5,253 | 5,464 |
|           | **after** |           47 |           **16** |       **141** |                0 |    **7** |      5,253 | 5,464 |
| field     | before    |            6 |                0 |             0 |                0 |       10 |         19 |    35 |
|           | **after** |        **0** |                0 |             0 |                0 |   **16** |         19 |    35 |
| return    | before    |           14 |                0 |             0 |                1 |       10 |         50 |    75 |
|           | **after** |        **3** |                0 |             0 |                1 |   **21** |         50 |    75 |
| **all**   | before    |           67 |               20 |           138 |                1 |       26 |      5,322 | 5,574 |
|           | **after** |       **50** |           **16** |       **141** |                1 |   **44** |      5,322 | 5,574 |

Every number that moves, with its cause:

| number                       | before |  after | cause                                                                                                                                                                              |
| ---------------------------- | -----: | -----: | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| field `ExactClosure`         |      6 |      0 | defect 1 — an exported field slot is `Preserve`                                                                                                                                    |
| return `ExactClosure`        |     14 |      3 | defect 1 — exported / used-as-a-value returns                                                                                                                                      |
| parameter `TypeShapeUniform` |     20 |     16 | 3 by defect 4 (a free-tyvar class split makes them `CloneRequired`), 1 by defect 1                                                                                                 |
| `CloneRequired`              |    138 |    141 | defect 4 — three slots whose producers stop agreeing                                                                                                                               |
| `Preserve`                   |     26 |     44 | defect 1 — +6 field, +11 return, +1 parameter                                                                                                                                      |
| enumerated                   |    252 |    252 | unchanged: enumeration is a different fact (`H11`)                                                                                                                                 |
| one representation           |    103 |     84 | 3 by defect 4, 16 by defect 2 (opaque never shares)                                                                                                                                |
| rewritable as one            |     87 |     66 | 3 by defect 4, 18 by defect 1                                                                                                                                                      |
| distinct shape classes       |    261 |    353 | +71 defect 4, +21 defect 2                                                                                                                                                         |
| per-parameter class sum      |    418 |    509 | defect 4 — more classes, still only evidence                                                                                                                                       |
| **clones**                   |    418 | **53** | defect 3 — distinct call-site tuples, per owner (**68** since [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), which corrected how a tuple is deduplicated) |

#### M2.4e re-checked against the corrected `Higher`

`parsec::residual_edges` reads `Higher::verdict_for`, so it was re-run. The 41-row status table is **unchanged, row for row**:

| status                                                     | before | after |
| ---------------------------------------------------------- | -----: | ----: |
| closed by the closure graph (`P-HO-EXACT` / `P-HO-FINITE`) |      0 |     0 |
| `boundary-Unresolved(parameter-of-an-anonymous-lambda)`    |     20 |    20 |
| `boundary-Unresolved(function-used-as-a-value)`            |     19 |    19 |
| `boundary-Unresolved(call-site-is-a-partial-application)`  |      2 |     2 |

This is the expected result and not a coincidence: all 41 land on boundaries whose producer set is `Top`, and `H9-TAINT` is decided before anything the correction touched. None of the six defects can move an `Unresolved`.

#### Across the flag matrix, before → after

|                               |                     | A (`-O1`) |       B |       C |         D |         E |         F |
| ----------------------------- | ------------------- | --------: | ------: | ------: | --------: | --------: | --------: |
| boundaries                    |                     |     5,574 |   6,347 |   8,082 |    34,094 |    31,686 |    31,701 |
| Exact + TypeShapeUniform      | before              |        87 |     178 |     231 |       862 |       850 |       833 |
|                               | **after**           |    **66** | **125** | **172** |   **695** |   **683** |   **682** |
| `CloneRequired`               | before              |       138 |     184 |     227 |     1,006 |       996 |     1,017 |
|                               | **after**           |   **141** | **219** | **269** | **1,150** | **1,140** | **1,145** |
| `Preserve`                    | before              |        26 |      27 |      26 |        39 |        39 |        39 |
|                               | **after**           |    **44** |  **45** |  **43** |    **62** |    **62** |    **62** |
| clones                        | before (a sum)      |       418 |     621 |     770 |     3,118 |     3,132 |     3,210 |
|                               | **after (planned)** |    **53** |  **61** |  **65** |   **154** |   **154** |   **176** |
| per-slot class sum (evidence) | after               |       509 |     916 |   1,182 |     5,058 |     4,982 |     5,020 |

The shape of the correction is the same on every profile: more inlining makes more shape classes once free type variables stop merging, so `CloneRequired` rises and `Exact + TypeShapeUniform` falls, while the *planned* clone count is an order of magnitude below the old sum. The accounting assertion holds on all six.

#### The gate

Every report except `higher` and the **appended M2.4e sections** of `parsec` and `tuples --verify` is byte-identical, on `compiler/core-json` and on all six matrix profiles: `laziness`, `tuples`, `tuples --explain`, `tuples --boundaries`, `fields`, `lists`, `text`, `verify-rep`, `classops`, `dictflow`, and `parsec` itself on -O1 — including its 41-row M2.4e table. What does move, and why:

- `boundary-CloneRequired(5)` → `boundary-CloneRequired(8)` in the M2.4e section of `parsec` and `tuples --verify` on profiles C–F: defect 4, a free-tyvar class split at that one boundary. The M2.4e **status** of every row is unchanged.
- `parsec --json` and three `e.g.` exemplar lines of `parsec` on the matrix profiles differ — the known nondeterminism recorded at M2.4e. It was re-confirmed here by running the **unchanged** binary three times over the same dump: `arg-of-unrecognised-call`, `cont-in-non-cont-slot` and `cont-wrong-arity` pick a different witness each run with identical counts, and `--json` differs only in the order of each region's `edges` (972 of 1,301 regions, before against before).

`cargo test` is 208 (7 new), `cargo clippy --all-targets` 0 warnings, `cargo fmt --check` clean. No Core is mutated, no codegen is emitted, no GHC flag changed.

#### Still unsound, stated rather than hidden

- **The M3 carrier invariant** behind `TypeShapeUniform` (defect 6) is assumed, not proved, and nothing in M2 can prove it.
- **`Ty::alpha_eq` still compares free type variables by unique.** `H14` keeps the *shape class* from resting on that, but the IR predicate itself is unchanged and must not be given a free-tyvar-sensitive proof to carry.
- **66 of 87 clone plans are refused**, because some function-valued parameter of the owner has an unenumerable producer set. 53 is therefore the clone count of the 21 owners that can be planned, not of the program.
- **Set-valued tuples are lower bounds** (†): the fixpoint is monovariant.
- Everything M2.4d already listed under *What remains* still stands.

## M2.4e — the 41 residual Parsec continuation edges

[M2.2](#m22--which-tuples-are-transport-and-which-are-values) stage 2 resolved a continuation call's target by the **region graph** alone: every call of the region has to be a saturated call to a visible binder, and what fills the continuation slot at each has to be a manifest lambda. 41 tuple sites sit on a continuation call where that failed, and the tuple census counts them as `parsec-continuation-target-not-in-the-region-graph`. [M2.4d](#m24d--higher-order-representation-agreement) left them to this one, which asks a second, independent question per edge and asks it of the **closure graph**: the continuation parameter is a function-valued slot of the closed world, so the whole-program fixpoint already knows what reaches it.

The question, per edge:

1. `higher::Higher::verdict_for(module, binder)` — the boundary the continuation binder names. No boundary, no answer.
2. Is the verdict one of the three **enumerated** ones — `ExactClosure`, `UniformRepresentation`, `FiniteClosureSet`? `Preserve`, `Unresolved` and `CloneRequired` are recorded as the refusal they are.
3. Is **every** producer at that boundary a continuation of *known role* — a region continuation (a parameter, or a connected derived one) or a nested region? Read off `Analysis::cont_source`, the recogniser's own classifier; nothing here re-decides what a continuation is, and no name is read.

Only then does the edge gain a structural role target: one producer is an exact one (`P-HO-EXACT`), several a finite one (`P-HO-FINITE`), both level 3 over M2.4d's facts and citing the boundary node and every producer.

|               | level |                                                                                                                          |
| ------------- | ----: | ------------------------------------------------------------------------------------------------------------------------ |
| `P-HO-EXACT`  |     3 | the continuation slot's boundary is enumerated, every producer is a continuation of known role, and there is exactly one |
| `P-HO-FINITE` |     3 | the same, with more than one: a finite set of role targets                                                               |

### The answer: 0 of 41

**No edge closes.** The closure graph refuses every one of the 41, and — the result worth reporting — it refuses each of them for the *same reason the region graph did*, one for one:

|    | the region graph's refusal (M2.2 stage 2)     | the closure graph's answer (M2.4d)               |
| -: | --------------------------------------------- | ------------------------------------------------ |
| 20 | the region's chain is not bound to a binder   | `Unresolved(parameter-of-an-anonymous-lambda)`   |
| 19 | the region's parser is used as a value        | `Unresolved(function-used-as-a-value)`           |
|  2 | a call of the region is not saturated exactly | `Unresolved(call-site-is-a-partial-application)` |

The cross-tabulation is exact: the 20/19/2 split of the region graph's reasons maps onto the 20/19/2 split of the closure graph's, edge by edge. That is not a coincidence and it is not a second failure either — it is the same three facts about the Core seen from two sides. A region whose chain is not bound to a binder *is* an anonymous lambda, so M2.4d's `collect_params` has no owner to enumerate call sites of; a parser used as a value *is* a function used as a value, which is `H8-PRESERVE`'s and `H9-TAINT`'s reason to refuse a slot; a call that is not saturated exactly *is* a partial application, whose argument never lands. Two analyses that share nothing but the IR agree about which 41 edges they cannot see, and agree about why.

So M2.4e's honest contribution is a **negative result with provenance**, not a reclassification: nothing moves, no count in any report changes, and the 41 stay exactly where M2.2 put them — now each with the closure graph's own reason beside the region graph's. Closing them needs what both refusals point at and neither pass does: naming the anonymous CPS lambdas of `ShellCheck.Parser` (M2.4d says the same about its 2,660 + 1,953), and a per-call-site rather than monovariant view of a parser that is also a value.

### The 41, individually

`site` is the continuation call the tuple reached; `boundary` is the M2.4d slot that was asked about it.

*Recomputed by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), which changed the condition. The **new status** column now says what the enumeration question answered, with the representation verdict named inside it rather than standing in for it: all 41 boundaries are **unenumerated**, which is why none of them closes. Nothing else in the table moves, and the count is still 0 closed / 41 open.*

| module              |   node | edge                               | previous reason                                                 | new status                                                                                 | boundary                                        |
| ------------------- | -----: | ---------------------------------- | --------------------------------------------------------------- | ------------------------------------------------------------------------------------------ | ----------------------------------------------- |
| `ShellCheck.Parser` |   1946 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 119: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 1930            |
| `ShellCheck.Parser` |   1962 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 119: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 1930            |
| `ShellCheck.Parser` |   1996 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 119: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 1 (cok) of #? at node 1928            |
| `ShellCheck.Parser` |   2012 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 119: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 1 (cok) of #? at node 1928            |
| `ShellCheck.Parser` |  17769 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 546: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 17767           |
| `ShellCheck.Parser` |  40016 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 659: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 40014           |
| `ShellCheck.Parser` |  44120 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 687: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 3 (eta) of eta#14436 at node 44107    |
| `ShellCheck.Parser` |  44121 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 687: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 3 (eta) of eta#14436 at node 44107    |
| `ShellCheck.Parser` |  44170 | `eta Cok → Cok [R3-CONT-CALL]`     | eta of region 687: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (eta) of eta#14436 at node 44105    |
| `ShellCheck.Parser` |  44171 | `eta Cok → Cok [R3-CONT-CALL]`     | eta of region 687: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (eta) of eta#14436 at node 44105    |
| `ShellCheck.Parser` |  55495 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 769: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 55491           |
| `ShellCheck.Parser` |  57894 | `eta Eok → Eok [R3-CONT-CALL-ETA]` | eta of region 444: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 3 (eta) of lvl#4458 at node 57887     |
| `ShellCheck.Parser` |  57919 | `eta Cok → Cok [R3-CONT-CALL-ETA]` | eta of region 444: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (eta) of lvl#4458 at node 57885     |
| `ShellCheck.Parser` |  58867 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 439: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 2 (eok) of $wps#4447 at node 58854    |
| `ShellCheck.Parser` |  58868 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 439: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 2 (eok) of $wps#4447 at node 58854    |
| `ShellCheck.Parser` |  58921 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 439: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (cok) of $wps#4447 at node 58853    |
| `ShellCheck.Parser` |  58922 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 439: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (cok) of $wps#4447 at node 58853    |
| `ShellCheck.Parser` |  61995 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 802: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 61982           |
| `ShellCheck.Parser` |  61996 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 802: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 61982           |
| `ShellCheck.Parser` |  62045 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 802: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 1 (cok) of #? at node 61980           |
| `ShellCheck.Parser` |  62046 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 802: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 1 (cok) of #? at node 61980           |
| `ShellCheck.Parser` |  66715 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 407: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 4 (eta) of k#4393 at node 66700       |
| `ShellCheck.Parser` |  66716 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 407: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 4 (eta) of k#4393 at node 66700       |
| `ShellCheck.Parser` |  66765 | `eta Cok → Cok [R3-CONT-CALL]`     | eta of region 407: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 2 (eta) of k#4393 at node 66698       |
| `ShellCheck.Parser` |  66766 | `eta Cok → Cok [R3-CONT-CALL]`     | eta of region 407: the region's parser is used as a value       | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 2 (eta) of k#4393 at node 66698       |
| `ShellCheck.Parser` |  79705 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 866: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 79701           |
| `ShellCheck.Parser` |  87005 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 891: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eok) of #? at node 87003           |
| `ShellCheck.Parser` |  98148 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 976: the region's chain is not bound to a binder  | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eta) of #? at node 98146           |
| `ShellCheck.Parser` | 123694 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 5 (eta) of $wk#36309 at node 123689   |
| `ShellCheck.Parser` | 123725 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 5 (eta) of $wk#36309 at node 123689   |
| `ShellCheck.Parser` | 123767 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 5 (eta) of $wk#36309 at node 123689   |
| `ShellCheck.Parser` | 123824 | `eta Cok → Cok [R3-CONT-CALL]`     | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 3 (eta) of $wk#36309 at node 123687   |
| `ShellCheck.Parser` | 123881 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 1157: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 4 (eta) of k#36395 at node 123877     |
| `ShellCheck.Parser` | 124015 | `eta3 Eok → Eok [R3-CONT-CALL]`    | eta3 of region 1149: the region's parser is used as a value     | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 2 (eta3) of $wm1#36087 at node 123991 |
| `ShellCheck.Parser` | 124668 | `eta Eok → Eok [R3-CONT-CALL]`     | eta of region 1161: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)`   | parameter 4 (eta) of k#36617 at node 124648     |
| `ShellCheck.Parser` | 125675 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 54: a call of the region is not saturated exactly | `boundary-producer-set-is-not-enumerated (Unresolved: call-site-is-a-partial-application)` | parameter 3 (eok) of lvl#397 at node 125673     |
| `ShellCheck.Parser` | 125720 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 53: a call of the region is not saturated exactly | `boundary-producer-set-is-not-enumerated (Unresolved: call-site-is-a-partial-application)` | parameter 3 (eok) of lvl#382 at node 125718     |
| `ShellCheck.Parser` | 126651 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 1166: the region's parser is used as a value      | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 3 (eok) of lvl#36967 at node 126635   |
| `ShellCheck.Parser` | 126675 | `eok Eok → Eok [R3-CONT-CALL]`     | eok of region 1166: the region's parser is used as a value      | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 3 (eok) of lvl#36967 at node 126635   |
| `ShellCheck.Parser` | 126717 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 1166: the region's parser is used as a value      | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (cok) of lvl#36967 at node 126633   |
| `ShellCheck.Parser` | 126741 | `cok Cok → Cok [R3-CONT-CALL]`     | cok of region 1166: the region's parser is used as a value      | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)`           | parameter 1 (cok) of lvl#36967 at node 126633   |

### What this is checked by

`parsec::residual_edges(&[Analysis], &Higher)` builds the population the way the tuple census itself records it — the escape evidence of every flow whose fate is `parsec-continuation-target-not-in-the-region-graph`, one row per flow — so the 41 here are the same 41 `h2r tuples` counts, not a second population that happens to have the same size. The section prints in `h2r parsec` and, in summary, in `h2r tuples --verify`; both are additions, and every other line of every existing report is byte-identical.

*Corrected by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found). The condition this section states — "one of the three enumerated verdicts" — was the wrong condition, and the paragraph below called `residual_edge_closes_through_a_uniform_boundary_of_known_continuations` "the" regression test as though `parsec.rs` had no others. It carries **29** unit tests of its own (27 before M2.4h), in its own `mod tests`, and `cargo test` counts every one of them; this is one of three that cover `residual_edges`.*

That regression test covers the branch the real dump does not reach: two regions that each hand a tuple to their `cok` and are each called twice with a continuation the region graph refuses to follow. One closes — `P-HO-FINITE` over a `UniformRepresentation` boundary whose two producers are both nested regions — and one stays open with `producer-is-not-a-region-continuation`, because one of its two producers is a lambda that is no continuation at all: opaque to the role question however well its representation agrees. That the rule *can* fire is therefore evidence, and that it does not fire on ShellCheck is a fact about ShellCheck's Core.

## M2.4f — re-deriving the M2.4 verdicts independently

`h2r verify-m24 <dir> [--json] [--explain]`.

[M2.2 stage 2](#the-independent-verifier) and [M2.3e](#m23e--re-deriving-the-representation-verdicts-independently) are the model, and the discipline is theirs: a second implementation that **shares nothing with the analyses it checks beyond the IR** and a short, named list of trusted inputs, re-deriving every claim whose being wrong would be a miscompile, with every disagreement settled by fixing whichever side is wrong. `crates/h2r-analysis/src/verify_m24.rs` does that for M2.4b–d′. It does **not** use [`classops.rs`](#m24b--the-closed-world-class-op-census)'s walk, [`dictflow.rs`](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go), [`higher.rs`](#m24d--higher-order-representation-agreement) or `flow.rs`; it has its own closed-world index, its own dictionary test, its own call-site enumeration, its own dispatch, its own three fixpoints, its own totality domain with its own definition of *already evaluated*, its own escape walk, its own type key and its own shape classes.

The analyses' verdicts reach it as **plain data**, through `m24_claims.rs` — the same split `m23.rs` makes for `verify_rep.rs`, and for the same reason: the verifier must not be able to see a `Verdict` at all.

### What it re-derives, and why those

| claim                                                                                   |                                                                                                  `-O1` | a wrong one costs                                                   |
| --------------------------------------------------------------------------------------- | -----------------------------------------------------------------------------------------------------: | ------------------------------------------------------------------- |
| class-op site `Exact(target)`                                                           |                                                                                                      7 | a call redirected into the wrong instance's method                  |
| class-op site, bounded `DictSet`                                                        |                                                                                                    118 | an instance outside the set dispatched at run time                  |
| dictionary parameter, bounded `DictSet`                                                 |                                                                                                    106 | the same, one level up                                              |
| dictionary value `Erasable`                                                             |                                                                                                    102 | a dictionary that is still needed is deleted                        |
| dictionary parameter `Erasable` / `WithClone` / `WithObligation`                        |                                                                                             36 / 4 / 0 | a dictionary, or a force, that is still needed is deleted           |
| owner-level dictionary clone plan                                                       |                                                                                                      4 | fewer specialisations than the call sites that exist                |
| higher-order `ExactClosure` / `TypeShapeUniform` / `CloneRequired` / `FiniteClosureSet` |                                                                                      50 / 16 / 141 / 1 | one representation given to a slot two live closures disagree about |
| owner-level closure clone plan                                                          | 21 plans, 68 clones (53 before [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)) | ditto                                                               |
|                                                                                         |                                                                                         **606 claims** |                                                                     |

A wrong `Unresolved` or a wrong `Preserve` costs only coverage, so nothing re-derives those — the same asymmetry M2.3e states.

### Trusted inputs, named

These are **consulted, not verified**, and nothing in this milestone may be read as a check of them. They are printed at the top of every run.

1. **The 17-class method-field table** (`classops::CLASSES`). It is a [level-5 axiom](#the-class-table-and-why-there-is-one): format 5 carries neither a type nor an unfolding for a global, so a selector's `C a => …` type and its `case d of C:C … m … -> m` body are both absent and the field order is not derivable from the dump at all. Asserting it a second time here would be inventing a second unchecked assertion rather than checking the first — M2.3e's argument about the list axioms, exactly. The **data** is shared; every *use* of it is re-derived: which selector names which class, which field a method sits at, the `$pN<Class>` superclass reading, and the cross-check against the dictionary constructor's own `repArity`.
2. **`W0-CLOSED-WORLD` / `H0-CLOSED-WORLD`** — the 28 modules are the whole program. An assumption about the build, which no walk can prove.
3. **GHC's own flags**: `isClassOpId` (the id table's `isClassOp`), `isExportedId` (a binder's `exported`) and the demand signatures' strictness bits, read from the authoritative source — the binder at a binding site, the id table for an import.
4. **The structured `Ty`**, and `TyCon` stable-name identity.

**Addressing is not sharing.** A claim has to name what it is about, and the names are IR addresses: a module and a node id, a module and a `BinderId`, a constructor's stable name and a value-field index. A dictionary identity is addressed the way any dictionary built in the dump has to be — the module and node of its constructor application, or the stable name of an imported dfun — and *which node that is* is re-derived here. Agreeing on an address is not agreeing on a derivation; disagreeing about which node is the constructor application would be a disagreement, and is reported as one.

*[M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found) adds one shared **rendering** for the same reason: `dictflow::group_lines`, which lays a clone plan's partition of call sites out as text. It derives nothing — it sorts and joins addresses each walk computed for itself — and both sides need one spelling for the same set, exactly as they need one spelling for a method target. Nothing else crosses; in particular the two walks' shape classes, capture keys and type keys stay their own and are rendered differently on purpose, which is why a closure clone plan is checked by its partition and not by its tuple strings.*

The linkage table that addressing rests on is re-derived too, including [M2.4c′'s identity cleanup](#identity-cleanups): this walk writes its own *external name* test, rejects the two pseudo-units `_sys` and `_in` that a three-way split on `$` would otherwise read as a unit and a module, and **asserts that no two top-level bindings claim one external stable name**. That assertion holds on all seven dumps, and it is load-bearing: accepting the pseudo-units makes this walk's own assertion fail on `-O1` with exactly `external stable names are not unique: ["$_sys$poly_$j"]`.

### What it found

| dump                 | claims | re-derived | **disagreements** | coverage refusals |
| -------------------- | -----: | ---------: | ----------------: | ----------------: |
| `-O1` (and matrix A) |    606 |        606 |             **0** |                 0 |
| B                    |    749 |        749 |             **0** |                 0 |
| C                    |    867 |        867 |             **0** |                 0 |
| D                    |  2,209 |      2,209 |             **0** |                 0 |
| E                    |  2,187 |      2,187 |             **0** |                 0 |
| F                    |  2,209 |      2,209 |             **0** |                 0 |

Not one claim refused, on any dump, in either sense: this walk re-derived every positive verdict M2.4 publishes, and it never had to decline. The populations it built on the way are the same ones, which is a second agreement and a separate one — the claim list says nothing about how many class-op sites exist:

| this walk's own population               | A (`-O1`) |      B |      C |      D |      E |      F |
| ---------------------------------------- | --------: | -----: | -----: | -----: | -----: | -----: |
| class-op sites                           |       565 |    587 |    595 |    595 |    595 |    596 |
| dictionary parameters                    |       216 |    210 |    222 |    223 |    223 |    231 |
| dictionary identities                    |       191 |    191 |    191 |    238 |    238 |    238 |
| function-valued boundaries               |     5,574 |  6,347 |  8,082 | 34,094 | 31,686 | 31,701 |
| rounds (dictionary / totality / closure) |    7/4/10 | 7/4/10 | 7/4/11 | 7/7/11 | 7/7/11 | 7/7/11 |

### The whole population, not just the claimed part

A claim check is **one-sided**: only the positive verdicts are re-derived, so a walk that called everything `Erasable` would pass it. `verify-m24` therefore also prints what this walk says about *every* value, parameter and boundary, in the analyses' own column order, and every published table comes back cell for cell on `-O1`:

| this walk's own verdicts (`-O1`) | `Erasable` | `…WithObligation` | `…WithClone` | `Preserve` | `Unresolved` |
| -------------------------------- | ---------: | ----------------: | -----------: | ---------: | -----------: |
| dictionary values (191)          |        102 |                 0 |            0 |         89 |            0 |
| dictionary parameters (216)      |         36 |                 0 |            4 |         84 |           92 |

|                             | `ProvenTotal` | `MustPreserveForce` | `Unknown` |
| --------------------------- | ------------: | ------------------: | --------: |
| dictionary parameters (216) |           118 |                   0 |        98 |

|                    | `ExactClosure` | `TypeShapeUniform` | `CloneRequired` | `FiniteClosureSet` | `Preserve` | `Unresolved` |
| ------------------ | -------------: | -----------------: | --------------: | -----------------: | ---------: | -----------: |
| boundaries (5,574) |             50 |                 16 |             141 |                  1 |         44 |        5,322 |

It holds on every profile too. Every cell of [M2.4c′'s](#across-the-flag-matrix-1) and [M2.4d′'s](#across-the-flag-matrix-before--after) matrix tables comes back:

| this walk's own verdicts                                   | A (`-O1`) |         B |         C |        D |        E |        F |
| ---------------------------------------------------------- | --------: | --------: | --------: | -------: | -------: | -------: |
| values `Erasable`                                          |       102 |       102 |       101 |      139 |      139 |      139 |
| parameters `Erasable`                                      |        36 |        28 |        34 |       28 |       28 |       28 |
| parameters `ErasableWithClone`                             |         4 |         3 |         4 |        4 |        4 |        4 |
| parameters `ProvenTotal` / `MustPreserveForce` / `Unknown` |  118/0/98 | 110/0/100 | 121/0/101 | 77/0/146 | 77/0/146 | 85/0/146 |
| `ExactClosure` + `TypeShapeUniform`                        |        66 |       125 |       172 |      695 |      683 |      682 |
| `CloneRequired`                                            |       141 |       219 |       269 |    1,150 |    1,140 |    1,145 |
| boundary `Preserve`                                        |        44 |        45 |        43 |       62 |       62 |       62 |

These are not claim checks — a difference here would be a difference to look at, not a `D` — and there is no difference: the erasure table of [M2.4c′](#erasure-tables-before--after), its totality row (118/0/98) and the whole of [M2.4d′](#the-verdicts-before--after--o1)'s corrected verdict table are reproduced by a walk that has never seen them.

### Why silence here is evidence

A verifier that agrees with everything has said nothing unless it can be shown to bite. Two tests do that, and they are the reason the tables above are worth printing: `m24f_the_verifier_refuses_a_claim_that_names_the_wrong_target` rewrites one `Exact` claim's target to the *other* instance's method and the walk refuses it as `X_TARGET_DIFFERS` (a `D`, not a `C`), and `m24f_the_verifier_refuses_a_clone_plan_with_the_wrong_count` turns a two-tuple clone plan into a one-clone claim and gets `X_CLONES_DIFFER`. Both assert that the refusal is counted as a disagreement and not as a coverage loss.

### The adversarial shapes

Each shape is a hand-built fixture in `tests.rs` **and** a count in the real `-O1` dump, printed by `h2r verify-m24`, so that a fixture is never the only evidence a rule was exercised. Every count is this walk's own.

|   # | shape                                                                   | in `-O1` | example                                                             | must be                                                                             |
| --: | ----------------------------------------------------------------------- | -------: | ------------------------------------------------------------------- | ----------------------------------------------------------------------------------- |
|   1 | bounded dictionary identity whose producer is not total                 |    **0** | —                                                                   | never `Erasable`                                                                    |
|   2 | one dictionary parameter, two or more instances                         |       36 | `ShellCheck.Parser` 1645                                            | a finite set; `ErasableWithClone(n)` where it is erasable at all (4 of the 36 here) |
|   3 | a dictionary used as an ordinary value *and* as a selector's dictionary |       11 | `ShellCheck.AST` 23582                                              | `Preserve`; the target is unaffected                                                |
|   4 | a dictionary parameter of unknown totality                              |       98 | `ShellCheck.AST` 3461                                               | `Unresolved` / `Preserve(totality)`                                                 |
|   5 | a superclass selector site (`$pN<Class>`)                               |       72 | `Main` 659                                                          | follows to the superclass instance                                                  |
|   6 | a dictionary parameter fed through dispatch                             |       15 | `Main` 7766                                                         | terminates; the fixpoint is monotone                                                |
|   7 | a partially applied class-op selector                                   |    **0** | —                                                                   | recorded, no target claimed                                                         |
|   8 | an exported or valued function slot whose producers *do* agree          |       18 | `ShellCheck.AnalyzerLib` binder 2508                                | `Preserve`, decided before agreement                                                |
|   9 | a slot two opaque producers reach                                       |        4 | `ShellCheck.Interface` field 0 of `SystemInterface`                 | two classes: opaque unifies with nothing                                            |
|  10 | a capture type carrying a free type variable                            |      292 | `ShellCheck.AST` 3463                                               | a producer-private key: unifies with nothing                                        |
|  11 | a value field bound after an existential type binder                    |       25 | `Main` 623                                                          | value-field indexing, not raw binder position                                       |
| 11a | …and the field is function-typed                                        |        4 | `ShellCheck.Formatter.JSON` 4217                                    | pairs with the constructor's value argument                                         |
|  12 | an owner with two or more slots, planned jointly                        |       11 | `ShellCheck.Analytics` `doVariableFlowAnalysis` (2 slots, 3 tuples) | clones = distinct call-site tuples                                                  |
|  13 | several representations at one slot, at a local                         |      141 | `ShellCheck.ASTLib` binder 1422                                     | `CloneRequired`                                                                     |
| 13a | …the same, at an exported or valued slot                                |       10 | `ShellCheck.AnalyzerLib` field 0 of `Checker`                       | `Preserve`                                                                          |
|  14 | a finite closure set at a slot no clone can serve                       |        1 | `ShellCheck.Checks.ShellSupport` return binder 942                  | `FiniteClosureSet(n)`                                                               |
|  15 | a three-argument closure named like a Parsec continuation               |      124 | `ShellCheck.Parser` 3450                                            | arity and captures decide; no name is read                                          |
|  16 | a `case` on the alternative binder of a **lazy** field                  |    6,625 | `Main` 518                                                          | a force: the binder is an unevaluated thunk                                         |
|  17 | …the same, on a **GHC-strict** field's binder                           |      168 | `ShellCheck.ASTLib` 8186                                            | already evaluated: the `case` deletes nothing                                       |
|  18 | a `case`/`let` head carrying outer value arguments                      |    **0** | —                                                                   | refused, never peeled: the arguments would be dropped                               |

*Rows 16–18 were added by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), one per defect it found in the totality domain.*

Rows 1 and 7 are zero, and both are load-bearing zeroes rather than gaps: the fixtures exercise each rule, and the dump's zero is the finding. Row 1 is the `-O1` half of [M2.4c′](#correction-m24c--totality-is-not-the-same-fact-as-identity)'s counterexample; row 12 is [M2.4d′](#3-the-clone-count-was-a-sum-of-per-parameter-numbers)'s `(A,X)`, `(B,X)`, `(A,Y)` shape, whose fixture wants **three** clones where the per-slot sum and the product both say four.

Row 15 belongs half to [M2.4e](#m24e--the-41-residual-parsec-continuation-edges). On this side of the line the finding is that the 124 three-argument `cok`/`eok`/`cerr`/`eerr`-shaped closures buy nothing from their names: a shape class is an arity and an ordered list of captured types, and the fixture pins that an identically shaped `zzz` lands in the same class while a two-argument `cok2` does not. On the M2.4e side, role admission is decided by the layout check and never by a name — `h2r parsec` reports 1,301/1,301 regions proven with **0** refused on continuation *order* and 10 census sites rejected outright as `head-is-not-a-parsec-role-binder` (e.g. `ShellCheck.Checks.Commands` node 16805). A Parsec-looking head that is structurally not a continuation gets no role and no edge.

### M2.4c′'s instrumented claim, re-derived

M2.4c′ says `MustPreserveForce` is **0** for a reason stronger than "every force was discharged": an instrumented run showed the totality walk reaches *no `case` node at all* on any dictionary path, GHC's `-O1` having floated every dictionary out of every scrutinee. This walk counts the same thing in its own transfer and reports it on every run:

```text
  case nodes this walk's totality transfer reaches on a dictionary path: 0
```

That matters because this walk's definition of *already evaluated* is deliberately **narrower** than M2.4c′'s: a literal, a lambda, a saturated constructor application, a dfun, or a variable a `case` has already bound. M2.4c′ additionally admits a variable GHC marks strict at its binder that an enclosing `case` on that binder dominates — a sound clause, but one this module would be *re-running* rather than checking, so it is left out.

*Amended by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found): "a variable a `case` has already bound" was too generous on **both** sides. An alternative binder of a lazy field is an unevaluated thunk, and this walk had taken that clause from M2.4c′ rather than deciding it. Both now admit only the scrutinee binder and a GHC-strict field's binder.* Omitting it can only make this walk find more forces than the analysis, which is the conservative direction for a verifier; it finds none, because there is no `case` to find.

### The one correction this produced

There was no disagreement about a verdict. There was one about the **record**:

- [M2.4d′ defect 5](#5-existentialgadt-fields-were-indexed-by-raw-binder-position) says "No number moves on the -O1 dump — GHC's ShellCheck Core has no alternative binding a function-typed field after an existential type binder". The first half is right and the second half is **wrong**. There are four such alternatives: `ShellCheck.Formatter.JSON` nodes 4217 and 4219 and `ShellCheck.Formatter.JSON1` nodes 4896 and 4898, all of them matches on `vector`'s existential `Data.Stream.Monadic.Stream`, whose first runtime field is the step function. The value-field counter puts it at *field 0*, raw binder position would have put it at field 1, and the reason no number moves is not that the shape is absent but that the boundary is `Unresolved(constructor-is-never-applied-in-the-closed-world)` at either index. Resolution: the **analysis was right and the prose was wrong**; M2.4d′'s paragraph is corrected above, and the shape is now counted on every run (rows 11 and 11a).

### Where this walk declines, and why that is not a disagreement

Two weakenings are written down rather than hidden, and neither fired on any of the seven dumps:

- **A `Top` set of this walk's own is a coverage refusal (`C`), never a disagreement (`D`).** `Top` says only that *this* walk could not account for every producer, which is this walk being blunter. What would be a disagreement is naming a producer the analysis does not have, and that is `X_SET_DIFFERS`.
- __The narrower *already evaluated*__ above. A refusal it caused would be this walk over-refusing, and would be reported as a disagreement for a human to resolve — `X_NOT_TOTAL` — rather than silently absorbed.

### The gate

Every existing report is **byte-identical** before and after, on `compiler/core-json` and on all six matrix profiles: `stats`, `laziness`, `parsec`, `tuples` (plus `--explain`, `--verify`, `--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus `--heads`, `--explain`), `verify-rep`, `classops` (plus `--per-module`, `--explain`), `dictflow` and `higher`, with the `--json` form of each — 238 captured reports over the seven dumps, of which **224 are byte-identical** and the other 14 are the **pre-existing `parsec` nondeterminism** and nothing else (every run's standard error was captured too, and all 224 are empty):

- `parsec` on B, C and D and `parsec --explain` on B, C, E and F differ in exactly **one `e.g.` exemplar line each** — the same reject reason with a different witness, every count identical. That is the witness-picking M2.4a's gate recorded and M2.4d′ re-confirmed by running an unchanged binary three times; *which* of the profiles it lands on moves from run to run, which is the point.
- `parsec --json` differs on all seven dumps in each region's edge list order, and is **multiset-identical on all seven** when every list is canonicalised.

**No census number moved**, because nothing but new code was added: `verify_m24.rs` and `m24_claims.rs` are new, `h2r verify-m24` is new, and the only edit to an existing analysis is an `owner_binder` field on `dictflow::OwnerPlan` and `higher::OwnerPlan` — an address a claim needs, `#[serde(skip)]`, read by no report.

`cargo test` is **225** (17 new: one per adversarial shape, plus the two that make the verifier bite), `cargo clippy --all-targets` 0 warnings and `cargo fmt --check` clean. No Core is mutated, no codegen is emitted, no GHC flag changed.

### Still unsound, or still unchecked

- **The four trusted inputs are trusted.** In particular the class table is an axiom on both sides of this check, and a wrong field order would be wrong in the same way twice. What the two sides do check against each other is every *use* of it, including the `repArity` cross-check, which is what a wrong entry would have to survive.
- **The closed world is an assumption**, and this walk rests on it exactly as M2.4c and M2.4d do. Re-deriving a producer set does not re-derive the right to enumerate it.
- **`Unresolved` and `Preserve` are not re-derived *as claims*.** A milestone that refused too much would pass the claim check in silence; that is the deliberate asymmetry, because only the positive verdicts can miscompile. What narrows it is the whole-population table above, where this walk's own `Preserve` and `Unresolved` counts are printed and agree cell for cell — but a difference there is a difference to look at and not a `D`, and no *reason* attached to a refusal is compared at all.
- **The monovariant lower bounds stand.** Four dictionary plans and eight closure plans on `-O1` have a set-valued tuple component, and their clone counts are lower bounds on both sides — this walk re-derives the same tuples and flags the same lower bound, which is agreement about a bound and not a closing of it.
- **`TypeShapeUniform`'s M3 carrier invariant** is assumed here too. This walk re-derives the shape classes; it cannot promise a lowering.

## M2.4g — the views, the provenance, the accounting, and what the milestone claims

M2.4b–e record the facts and [M2.4f](#m24f--re-deriving-the-m24-verdicts-independently) re-derives every verdict whose being wrong would be a miscompile. This section adds the three things a milestone needs before it can be closed — exactly the three [M2.3f](#m23f--the-representation-view-and-what-the-milestone-claims) added for M2.3: **views** that lay one site's proof out so a person can audit it, **provenance** in `h2r show` so any Core node can be asked what M2.4 says about it, and the milestone's own **accounting**, asserted in code and printed whole. It changes no verdict.

```sh
cargo run --release --bin h2r -- classops ../core-json --view 1154
cargo run --release --bin h2r -- classops ../core-json --view-all --module ShellCheck.Fixer --json
cargo run --release --bin h2r -- higher ../core-json --view 51239
cargo run --release --bin h2r -- higher ../core-json --view-all --module ShellCheck.AST --json
cargo run --release --bin h2r -- show ../core-json ShellCheck.Fixer 1154      # + its M2.4 footers
cargo run --release --bin h2r -- m24 ../core-json                             # the whole milestone
```

### Two views, each with its own completeness assertion

The **class-op view** puts one dispatch site on the page: the class and the method with the field the selector reads, the dictionary argument, the per-module origin chain with each step's rule, the **whole-program producer set at every parameter hop** the dictionary passes through, the target outcome, the totality fact, the erasure verdict with its reason, and the owner's clone-plan row where the owner has one. Every fact carries the verifier's answer, and a claim `verify-m24` refused is never printed as proven. `ClassopViews::check` asserts that **every site of the module appears exactly once**, and `ClassopView::check` that no parameter hop is listed twice — the walk up the parameter chain terminates and never doubles back.

```sh
$ h2r classops compiler/core-json --view 1154
ShellCheck.Fixer node 1154 — Ranged.setRange, dispatch on node 1252 → Exact(ShellCheck.Fixer.$csetRange)
    class Ranged … method setRange (field 3) … selector $ShellCheck-0.11.0-inplace$ShellCheck.Fixer$setRange
    dictionary argument  node 1252  [K1-DICT-ARG]
    origin chain (per module)  none reached
    whole-program producer set, per parameter hop [W3-PARAM-UNION]
        ShellCheck.Fixer removeTabStops.$dRanged (binder 312), exported
            set {ShellCheck.Fixer#14}  [verified: yes]
            totality ProvenTotal … erasure Erasable [verified: yes]
    target   Exact(ShellCheck.Fixer.$csetRange)  [verified: yes]
    per module (M2.4b)  Unresolved(dictionary-parameter-of-an-exported-function)
    dictionary set  {ShellCheck.Fixer#14}  [verified: yes]
    totality ProvenTotal  [E6-TOTALITY-*]
    erasure  Erasable  [verified: yes]
    owner clone plan  none (this owner needs no clone)
    facts (no verdict attached)
        K10-FORCED: the selector application forces its dictionary: true
        K11-DICT-ESCAPES: the dictionary is also used as an ordinary value: false
        GHC records the dictionary binder strict: true (evidence only, never a verdict)
    rules  K0-CLASSOP-SITE K1-DICT-ARG K10-FORCED K2-DICT-TYPE K3-CLASS-TABLE
```

That one site is the milestone in miniature: M2.4b could only say `Unresolved(dictionary-parameter-of-an-exported-function)`, the closed-world fixpoint bounds the dictionary to one instance and the method to one binding, the totality domain says the producer is a value so erasing it moves no divergence, and the second walk re-derived all three.

The **boundary view** puts one function-valued slot on the page: the slot with its owner and whether it is exported or belongs to a function used as a value, every producer with its **full shape class and its capture types**, every use, and — the part the milestone's own corrections make necessary — the **rule order** that produced the verdict, with the answer at every step and an arrow on the one that fired. `H8-PRESERVE` is decided before `H5` and `H6` ([M2.4d′ defect 1](#1-h8-was-decided-after-h5h6)), and the view shows the earlier questions answered rather than skipped. `BoundaryViews::check` asserts **every boundary of the module appears exactly once**, and `BoundaryView::check` that every producer appears once and that *rewritable as one* never exceeds *one representation*.

```sh
$ h2r higher compiler/core-json --view 51239
ShellCheck.Analytics parameter 0 (readFunc) of doVariableFlowAnalysis#1867 — param of doVariableFlowAnalysis, producers 3 (classes 3) → CloneRequired
    slot     param parameter 0 (readFunc) of doVariableFlowAnalysis#1867 at node 51239 of doVariableFlowAnalysis
    facts    enumerated true … 3 shape class(es) … the producer set is accounted for  [H11-SEPARATE: …]
    producers (3)
        ShellCheck.Analytics#160                 known function as a value              arity 4
            captures []  class arity=4;captures=[]
        ShellCheck.Analytics#36841               lambda                                 arity 4
            captures [C(…Map,C(…Id),C(…Token)) | C(…Shell) | C(…Comment)]  class arity=4;captures=[…]
        ShellCheck.Analytics#41138               lambda                                 arity 4
            captures [C(…Map,C(…Id),C(…Token))]  class arity=4;captures=[…]
    uses (1)
        called, saturated                            node 51295  args 4
    the rule order that produced the verdict (H8 before H5/H6)
          H9-TAINT       is the producer set Top?                                         no, every producer is accounted for
          H2-PRODUCERS   does any producer reach the slot?                                3 producer(s)
          H8-PRESERVE    is a producer's environment invisible (opaque)?                  no
          H8-PRESERVE    is the slot exported, so its representation is shared?           no
          H8-PRESERVE    does the slot belong to a function used as a value?              no
          H5-EXACT       is there exactly one producer?                                   3 producer(s)
          H6-UNIFORM     do the producers fall in one shape class?                        3 shape class(es)
        → H7-CLONE       is the slot a parameter of a local function, so a clone can serve it? the slot is a param
          H4-SHAPE-CLASS otherwise: a finite set of closures no clone can serve           3 producer(s)
    verdict  CloneRequired — 3 shape class(es)  [verified: yes]
    one representation false … rewritable as one false (strictly stronger: the rewrite must own the slot)
    owner clone plan  ShellCheck.Analytics doVariableFlowAnalysis — 2 slot(s), 3 call site(s), 3 tuple(s) → 3  [verified: yes]
        tuple arity 4, 0 capture(s), arity 5, 0 capture(s)
        tuple arity 4, 1 capture(s), arity 5, 0 capture(s)
        tuple arity 4, 3 capture(s), arity 5, 0 capture(s)
```

`--view-all --module M` does every site or boundary of a module and `--json` dumps the views as structured data. Both assertions are exercised on the real dump rather than on a fixture: over the 28 modules they lay out **565 of 565** class-op sites and **5,548** boundaries, each exactly once — `ShellCheck.AST` 429 sites and 240 boundaries, `ShellCheck.Parser` 57 and 5,154. The 26 boundaries the 28 modules do not cover are constructor *fields* of constructors defined outside the dump — nine of `GHC.Prim`'s, nine of `GHC.Tuple.Prim`'s, three of `GHC.Base`'s and five more — and `--module GHC.Tuple.Prim` lays those out on the same terms. 5,548 + 26 = 5,574.

### Provenance in `h2r show`

The two proof objects are loaded by default whenever the module has any, exactly as the Parsec, tuple and three representation objects are, and `--no-classops` / `--no-higher` opt out one at a time. They annotate class-op sites, dictionary values, dictionary-parameter binders and their occurrences, function-valued slots and their binders, and every closure producer — inline, and with one footer per site the node takes part in:

```sh
$ h2r show compiler/core-json ShellCheck.Fixer 1154 --depth 1
([#1154]{class-op site Ranged.setRange ⇒ Exact}setRange[#1253]
   $dRanged[#1252]{occurrence of dictionary parameter 0 of removeTabStops} … )

node 1154
  classop: Ranged.setRange at node 1154 dictionary $dRanged at node 1252 (param 0 of removeTabStops#312) → whole-program {ShellCheck.Fixer#14} → target Exact(ShellCheck.Fixer.$csetRange)
  totality ProvenTotal … erasure Erasable [verified: yes]
  this node: the class-op application itself; per-module Unresolved(dictionary-parameter-of-an-exported-function) [verified target: yes]
```

```sh
$ h2r show compiler/core-json ShellCheck.Analytics 51239 --depth 0
\readFunc{function-valued param ⇒ CloneRequired} writeFunc¹{function-valued param ⇒ TypeShapeUniform} … ->

node 51239
  boundary: parameter 0 (readFunc) of doVariableFlowAnalysis#1867 producers 3 (classes 3) → CloneRequired(3) … owner plan 3 clones
  one representation false … rewritable as one false [verified: yes]
  this node: the param slot itself; not exported
  H11-SEPARATE: enumerated true — an enumerated producer set is not one representation
```

All seven proof objects' marks are concatenated rather than merged, so it stays visible which object said what. Unlike M2.3's, these two are *whole-program by construction* — a dictionary parameter's producer set and a slot's closure set are unions over every module — so the objects are built over the whole dump and only the asked-about module's sites, values, parameters, boundaries and producers are indexed. The whole M2.4 object, `verify-m24` included, costs about three seconds on the `-O1` dump: `h2r show` on a class-op site takes **2.7s** with both objects loaded against **1.8s** with `--no-classops --no-higher`, most of which is reading the dump either way. That is why `show` can load them by default and stay a per-node query.

### The milestone accounting — three questions, never collapsed

Asserted in code (`m24::Accounting::check`) and printed whole by `h2r classops`, `h2r higher` and `h2r m24`. The milestone has spent two corrections learning that these are three questions and not one: **a known method target is not a removable dictionary** (M2.4c) and **an enumerated producer set is not one representation** (M2.4d). They are never added together and never reported as one number.

```text
(1) can the call target be enumerated?   sites = Exact + FiniteSet + Unresolved
  class-op dispatch sites (population)              565
  Exact(target)                                       7
  FiniteSet(targets)                                  0
  Unresolved                                        558
  … sites whose dictionary is bounded               118   a SEPARATE fact, never added in
  re-derived by verify-m24 (Exact / bounded)          7 / 118
```

```text
(2) can this abstraction boundary use one representation?
    boundaries = ExactClosure + TypeShapeUniform + FiniteClosureSet + CloneRequired
               + Preserve + Unresolved
  function-valued boundaries (population)          5574
  ExactClosure                                       50
  TypeShapeUniform                                   16
  CloneRequired                                     141
  FiniteClosureSet                                    1
  Preserve                                           44
  Unresolved                                       5322
  one representation (the theorem)                   84   enumerated, one shape class, no opaque producer
  rewritable as one                                  66   strictly stronger: the rewrite must own the slot
  producer set enumerated                           252   a different fact again (H11-SEPARATE)
  re-derived by verify-m24 (of the claims)          208 / 208
```

```text
(3) can the dictionary or closure object actually disappear?
    values / parameters = Erasable + WithObligation + WithClone + Preserve
                        + Unresolved
  verdict                          values   parameters
  Erasable                            102           36
  ErasableWithObligation                0            0
  ErasableWithClone                     0            4
  Preserve                             89           84
  Unresolved                            0           92
  total                               191          216
  parameter totality: 118 ProvenTotal, 0 MustPreserveForce, 98 Unknown; named force obligations 0
  re-derived by verify-m24: 102 value claim(s), 40 parameter claim(s)

  the two clone plans — OWNER-LEVEL. A per-slot cardinality is evidence and must
  never be summed: a function is cloned once per DISTINCT call-site assignment
  tuple, which is neither the sum nor the product of the per-slot counts.
  plan                                  cardinality   clones   planned   refused  lower bounds
  dictionary clones (E7-OWNER-CLONES)             8        4         4         0             4
  closure clones (H15-OWNER-CLONES)             509       68        21        66             8
```

`rewritable as one` (66) ≤ `one representation` (84) ≤ `enumerated` (252) is asserted, and the direction is the point: 18 boundaries whose producers genuinely agree are still `Preserve`, because the rewrite does not own the slot. Twelve of the twenty-five `-O1` clone plans that carry a number are flagged where a tuple has a set-valued component — **4 of 4** dictionary plans and **8 of 21** closure plans are lower bounds, closable only by a call-string analysis.

**The 3×5 matrix** crosses questions 1 and 3 rather than collapsing them:

| target ⟍ dictionary | `Erasable` | `…WithObligation` | `…WithClone` | `Preserve` | `Unresolved` |
| ------------------- | ---------: | ----------------: | -----------: | ---------: | -----------: |
| `Exact`             |          7 |                 0 |            0 |      **0** |            0 |
| `FiniteSet`         |          0 |                 0 |            0 |      **0** |            0 |
| `Unresolved`        |         10 |                 0 |            0 |        154 |          394 |

The bolded cells — a site whose method is known but whose dictionary must survive anyway — are **0**, and the other direction is populated: 10 sites whose dictionary is `Erasable` still have no known method target.

**The residual, itemised and owned.** Every row is attributed; an unattributed row would be the milestone hiding what it did not do. The site rows sum to the 558 `Unresolved` and the boundary rows to the 44 `Preserve` plus 5,322 `Unresolved`, both asserted.

|                     | class-op sites                                                                                                                           | whose problem it is                                                                               |
| ------------------: | ---------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------- |
|                 413 | `function-is-unreachable-in-the-closed-world`                                                                                            | `W0`: dead in the closed world — if ShellCheck is built as a library they come back               |
| 53 + 48 + 7 + 5 + 1 | `instance-method-not-in-the-dump` (`$fMonoidDual`, `$fMonadIO`, `$fMonadStatesParsecT`, `$fMonadStatesReaderT`, `$fMonadReaderrParsecT`) | the instance is known and its body is in another package: a bigger dump, or a hand-written callee |
|                  17 | `dictionary-read-from-a-non-dictionary-constructor-field`                                                                                | `SomeException`'s existential dictionary field: M3, or a hand-written `Exception` lowering        |
|                   9 | `method-is-never-dispatched-in-the-closed-world`                                                                                         | no class-op site in the program selects that field: dead under `W0`                               |
|                   4 | `dictionary-returned-by-a-call-the-dump-cannot-see`                                                                                      | a bigger dump                                                                                     |
|                   1 | `dispatched-from-a-site-with-an-unknown-dictionary`                                                                                      | closable only when that site's dictionary is                                                      |

|                           | function-valued boundaries                                                               | whose problem it is                                                                                 |
| ------------------------: | ---------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------- |
| 2,660 + 1,953 = **4,613** | `function-used-as-a-value`, `parameter-of-an-anonymous-lambda`                           | the Parsec CPS wall: a naming pass for the anonymous lambdas, then a call-string view               |
|                       413 | `call-site-is-a-partial-application`                                                     | the partial application's own consumers                                                             |
|                       227 | `function-is-unreachable-in-the-closed-world`                                            | dead under `H0`                                                                                     |
|                        44 | `expression-is-not-a-closure`                                                            | the body's lambda chain and the binder's type disagree about the return: refused rather than picked |
|                    22 + 3 | `a-closure-read-back-from-a-constructor-field`, `a-closure-returned-by-an-imported-call` | a genuine run-time closure: the lowering decides, not this analysis                                 |
|                        19 | `closure-from-an-untracked-higher-order-parameter`                                       | the propagation, once the anonymous lambdas are named                                               |
|                    14 + 5 | `the-boundary-is-exported-…`, `…-belongs-to-a-function-used-as-a-value`                  | shared outside the rewrite: M3's ownership question                                                 |
|                         5 | `constructor-is-never-applied-in-the-closed-world`                                       | dead under `H0`                                                                                     |
|                         1 | `closure-set-exceeded-the-budget`                                                        | a larger budget, or a per-caller analysis                                                           |

### The cross-milestone links

Four, and **nothing is reclassified**: every fate M2.2 recorded, every tier M2.1 recorded and every rep M2.3 recorded stands exactly as it was. `h2r m24` recomputes each rather than quoting it, so the two sides cannot drift.

**Back to M2.2 — the 67 closure-into-a-parameter tuple flows.** Recomputed against the corrected `Higher`: 31 `CloneRequired`, 22 no boundary, 13 `TypeShapeUniform`, 1 `ExactClosure`, and **14 could be reclassified by a later pass** — the 13 uniform plus the 1 exact. That is the same 14 [M2.4d](#feeding-the-proof-back--nothing-is-reclassified) published and it is **unchanged after M2.4d′**. That is visible in the table rather than argued: not one of the 67 lands on a `Preserve` slot, so none of them is at an exported or valued boundary — which is where defect 1 moved verdicts — and the 13 uniform slots survived the free-tyvar class split of defect 4.

**Back to M2.3 — the closure residual, by holder.** M2.3b left **2,454** constructor fields `Unknown` because the callee that consumes them is an unknown higher-order value — the population whose two largest rows M2.3's residual table names as *1,143 `eta` + 565 `eok`*. Each is now asked of the closure graph, by the callee binder M2.3 itself named:

| holder   |     n | what the closure graph says                                              |
| -------- | ----: | ------------------------------------------------------------------------ |
| `eta`    | 1,143 | `Unresolved` 1,035, `CloneRequired` 84, `ExactClosure` 20, no boundary 4 |
| `eok`    |   565 | `Unresolved` 554, `CloneRequired` 11                                     |
| `cok`    |   282 | `Unresolved` 275, `CloneRequired` 7                                      |
| `eerr`   |   182 | `Unresolved` 178, `CloneRequired` 4                                      |
| `cerr`   |   146 | `Unresolved` 146                                                         |
| `reader` |    36 | `TypeShapeUniform` 36                                                    |
| `eta3`   |    29 | `Unresolved` 29                                                          |
| `z'`     |    21 | `CloneRequired` 21                                                       |
| 14 more  |    50 | no boundary 36, `Unresolved` 8, `ExactClosure` 3, `Preserve` 3           |

**59 could be reclassified** (36 `reader` + 20 `eta` + 3 `color`). The shape of the answer is M2.4d's own: five of the six largest holders are Parsec's CPS continuations, and they are `Unresolved` for the same reason 4,613 boundaries are.

**Back to M2.1 — the 41 residual Parsec continuation edges.** Re-run here against the same `Higher`: **0 of 41** closed, 20 `boundary-Unresolved(parameter-of-an-anonymous-lambda)`, 19 `boundary-Unresolved(function-used-as-a-value)`, 2 `boundary-Unresolved(call-site-is-a-partial-application)` — row for row what [M2.4e](#m24e--the-41-residual-parsec-continuation-edges) published.

**Back to M1 — the thunk sites.** The M1 table gains a fourth column, and the invariant it exists to state is asserted:

```text
Thunk sites explained by M2.4 (M1 × M2.2 × M2.3 × M2.4)
                                                      before  by tuples   by M2.3   by M2.4   after
  sinkable, lands in an evaluating position               14          0         3         0      11
  sinkable, lands in a lazy position                     254          3         3         0     248
  memoisation required                                  1905         89         5         0    1811
  recursive value                                         69          0         0         0      69
  potential thunk sites                                 2242         92        11         0    2139
```

`remaining + explained-by-tuples + explained-by-M2.3 + explained-by-M2.4 = 2,242` is asserted, as is *no site is counted twice*: a site an earlier milestone explains is that milestone's, and this walk skips it before it can claim it. The two earlier columns are read from `link::ThunkLink` and `m23::RepLink` rather than recomputed.

**M2.4's column is 0, and the reason is a fact about the dump rather than a missing rule.** The one rule (`M24-D-DICTIONARY-BINDING-ERASED`) is: a `$d…` binding whose right-hand side is a saturated application of a dfun the whole-program flow holds as a dictionary identity, and whose identity is `Erasable` with the verifier's confirmation. The population and every refusal are printed:

|     |                                                                    |                                                            |
| --: | ------------------------------------------------------------------ | ---------------------------------------------------------- |
| 152 | of the 2,242 thunk sites are `$d…` bindings (`Origin::Dictionary`) | the population this link draws on                          |
| 131 | name a dictionary the whole-program flow holds an identity for     | …and **all 131** are `Preserve(used as an ordinary value)` |
|  18 | have a head the flow holds no identity for                         | not a dictionary M2.4c gave a verdict to                   |
|   3 | are a superclass selection (`$pN<Class> d`)                        | a *field of* a dictionary, not an identity of its own      |
|   0 | are `Erasable` but unconfirmed                                     | an unconfirmed claim is unsupported and never proven       |

Every one of the 152 is `Memo` in M1's own table, and 131 of them build a dictionary that `E4-ESCAPE` says is handed on as an ordinary value. A dictionary that escapes keeps its box, so the binding that builds it keeps its thunk. The number is 0 and it is a result.

### Across the flag matrix

|                                                       |     A (`-O1`) |               B |               C |                 D |                 E |                 F |
| ----------------------------------------------------- | ------------: | --------------: | --------------: | ----------------: | ----------------: | ----------------: |
| class-op sites / `Exact`                              |       565 / 7 |         587 / 7 |         595 / 7 |           595 / 0 |           595 / 0 |           596 / 0 |
| … dictionary bounded                                  |           118 |             138 |             140 |                65 |                65 |                65 |
| boundaries                                            |         5,574 |           6,347 |           8,082 |            34,094 |            31,686 |            31,701 |
| … enumerated / one representation / rewritable as one | 252 / 84 / 66 | 391 / 143 / 125 | 486 / 189 / 172 | 1,909 / 718 / 695 | 1,887 / 706 / 683 | 1,891 / 705 / 682 |
| dictionary values / parameters                        |     191 / 216 |       191 / 210 |       191 / 222 |         238 / 223 |         238 / 223 |         238 / 231 |
| clone plans (dictionary / closure)                    |        4 / 68 |          3 / 83 |          4 / 87 |           7 / 207 |           7 / 207 |           7 / 227 |
| claims / disagreements                                |       606 / 0 |         749 / 0 |         867 / 0 |         2,209 / 0 |         2,187 / 0 |         2,209 / 0 |
| M1 thunk sites explained by M2.4                      |             0 |               0 |               0 |                 0 |                 0 |                 0 |

The accounting closes on all seven dumps, and `rewritable ≤ one representation ≤ enumerated` holds on all seven.

*The closure clone row is as [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found) recomputed it; M2.4g published 53 / 61 / 65 / 154 / 154 / 176, planning with `Shape::short()` instead of `Shape::class()`. It is the only row that moved, and it moved upward on every dump — the defect always under-counted.*

### The `h2r parsec` nondeterminism, fixed

[M2.4c′](#correction-m24c--totality-is-not-the-same-fact-as-identity) recorded that `h2r parsec --explain` and `h2r parsec --json` differ run to run, and [M2.4d′](#correction-m24d--sharing-is-decided-before-agreement-and-a-free-type-variable-identifies-nothing) and [M2.4f](#m24f--re-deriving-the-m24-verdicts-independently) had to keep them out of every byte-identity gate because of it. The cause is one line: `Analysis::prove` walked `self.role`, a `HashMap<BinderId, RoleInfo>`, and that walk order is the order every region's `edges`, `evidence` and `rejects` come out in — hence the per-role line order in `--explain`, the per-region `edges` order in `--json`, and the `e.g.` witness of a reject reason, which is whichever reject was pushed first.

Sorting that walk by the binder fixes all three. It is a **report-order change only**: nothing in the proof depends on the order, and every count is an aggregate over all of it.

- **the counts are unchanged.** Apart from the `e.g.` exemplar lines, `parsec --explain` is line-for-line **multiset identical** before and after on all seven dumps, and `parsec --json` is identical on all seven once each region's `edges`, `evidence` and `rejects` lists are canonicalised — the exact comparison M2.4f had to make. `h2r parsec` itself is **byte-identical on `-O1`, A and D**, and on B, C, E and F it differs in **exactly one `e.g.` exemplar line** — the same reject reason (`arg-of-unrecognised-call`, `cont-in-non-cont-slot`, `cont-wrong-arity`) with a different witness and the same count. `parsec --explain` differs in two such lines on C and one on E and on F, and in none on the other four. That is the wobble itself: the old binary picked a witness at random, so the *before* capture is one of several outputs it could have produced, and the new one always picks the lowest-numbered role binder's. The 41-row M2.4e table is byte-identical on every dump.
- **two runs are now identical.** Three consecutive runs of `h2r parsec`, `parsec --explain` and `parsec --json` on `-O1`, on B and on C give **one md5 each — nine hashes for twenty-seven runs**. Against the same three runs of the *unchanged* binary on B, `--json` and `--explain` give **three distinct hashes each**, which is the defect being measured rather than assumed.

Those two reports can now carry a byte-identity gate, and this milestone is the first to put them under one.

### Correction (M2.4h) — four defects the owner's review of M2.4 found

Four defects in `e2055bc`, found by the project owner's review of the published work and not by a failing test. Three of them are the analysis claiming more than its evidence; the fourth is a proof object answering the wrong question. Every one is in the same direction as the earlier corrections, and one of them the **verifier had copied rather than derived** — which is a defect in the verification and not only in the analysis.

|       | what was wrong                                                                                                                                                                                                                                                                  | what it moved                                                                                                                                                                                                                                                                                                                                                    |
| ----- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **1** | three defects in the totality domain, in `dictflow.rs` **and** reproduced in `verify_m24.rs`: every alternative binder counted as *already evaluated*; the totality join kept one obligation and lost the rest; an applied `case`/`let` head was peeled, dropping its arguments | no verdict on any of the seven dumps, and `dictflow`'s report is byte-identical on all seven — but the first shape occurs **6,625** times in `-O1` and misses every verdict only because none of them sits on a dictionary path, where the totality transfer reaches no `case` at all. Each defect now has a hand-built counterexample and a counted row (16–18) |
| **2** | `H15-OWNER-CLONES` deduplicated clone tuples with `Shape::short()` — arity and capture **count** — contradicting `Shape::class()`, which is what every other part of M2.4d calls a representation                                                                               | closure clones **53 → 68** on `-O1`, and up on every dump: 61 → **83** (B), 65 → **87** (C), 154 → **207** (D and E), 176 → **227** (F). The verifier's independent recount agrees on all seven                                                                                                                                                                  |
| **3** | a clone-plan claim carried only its cardinality and an `ErasableWithObligation` claim carried no obligation at all, so `check_plan` compared `tuples == n` and a different plan of the same size passed                                                                         | no number; the claim protocol and two refusal reasons are new, and `[verified: yes]` now requires a content-checked claim                                                                                                                                                                                                                                        |
| **4** | `parsec::residual_edges` gated target enumeration on the *representation* verdict, admitting three verdicts and refusing `CloneRequired`                                                                                                                                        | still **0 closed** on all seven dumps, and the 41-row `-O1` table keeps every other column — but on C, D, E and F four edges per profile that the old rule refused as `boundary-CloneRequired(8)` are now asked the role question and refused by it instead, and every status names the enumeration answer with the verdict beside it                            |

#### 1 — the totality domain, three defects, and a verifier that had copied them

**(a) an alternative binder is not already evaluated.** `is_already_evaluated` returned `true` for `BindSite::CaseBinder | BindSite::AltBinder`. The scrutinee binder is sound: it could not be named before the scrutinee was forced. The alternative binder is not. Matching `P d` forces `P`, not `d`, and if the field is lazy then `d` is an unevaluated thunk — so a `case` on `d` deletes an evaluation that erasure would have to put back. Both walks now admit only the scrutinee binder, the binder of a field GHC's own `strictFields` marks strict, and the values they already admitted; a constructor the dump does not carry, or one whose source-field strictness vector and representation arity disagree, contributes no strict field at all rather than a guess. `an_alt_binder_of_a_lazy_field_is_not_already_evaluated` and its strict twin pin both directions.

**(b) an obligation set is a set.** `Tot::join` kept the lexicographically smallest `ForceObligation` and dropped every other one, so a dictionary standing behind two distinct forces was erasable against one of them and the second force disappeared with it. An obligation is a proof debt, not a witness to be chosen. `Tot` now carries a `BTreeSet<ForceObligation>`, the join is a **union**, and `ErasableWithObligation` carries the whole set; `dictflow`'s accounting gained `named_forces` beside `obligations` because one verdict can now carry several. `every_force_obligation_survives_the_join` builds two call sites forcing different scrutinees and requires both.

**(c) an applied `case`/`let` head is not its alternatives.** `eval_nested` and `tot_nested` matched `Expr::Case`/`Expr::Let` in head position and walked into the alternatives — but `m.spine()` puts the *outer value arguments* in `args`, and `(case x of A -> f; B -> g) d` is not `case x of A -> f; B -> g`. Peeling it answered about an expression `d` had been dropped from. Pushing the arguments through would mean building Core, which this compiler never does, so both walks refuse: `case-or-let-head-with-outer-value-arguments`, a `Top` for the set and `Unknown` for the totality. `a_case_head_with_outer_arguments_is_refused_not_peeled` builds exactly that shape with `d` the dictionary, and pins that the old walk's answer — the two-element set `{$fShowT, $fShowU}` for an expression whose value is neither — is now a refusal.

**In the dump.** Each shape is now searched for over the whole closed world and counted by `h2r verify-m24` (rows **16**, **17** and **18**), so that the hand-built counterexamples are not the only evidence the corrected rules were exercised, and so that a zero is a fact about the dump rather than about where the walk looked:

| row | shape                                                  |   `-O1`/A |     B |     C |      D |      E |      F | example on `-O1`              |
| --: | ------------------------------------------------------ | --------: | ----: | ----: | -----: | -----: | -----: | ----------------------------- |
|  16 | a `case` on the alternative binder of a **lazy** field | **6,625** | 7,539 | 7,570 | 12,372 | 11,348 | 11,287 | `Main` node 518               |
|  17 | …the same, on a **GHC-strict** field's binder          |       168 |   204 |   222 |    459 |    339 |    339 | `ShellCheck.ASTLib` node 8186 |
|  18 | a `case`/`let` head carrying outer value arguments     |     **0** | **0** | **0** |  **0** |  **0** |  **0** | —                             |

Defect (a) was therefore **live in the program** — 6,625 of the 6,793 alternative-binder scrutinees in `-O1` bind a lazy field and were being read as already evaluated, against 168 that really are — and the only reason no verdict moves is that none of the 6,625 sits on a **dictionary** path: the totality transfer reaches **0** `case` nodes there at all, the instrumented fact M2.4c′ recorded and M2.4f re-derives on every run. "It did not matter here" is not "it was right": the rule was stated in the report, it was wrong as stated, and 6,625 is how much of this program it was wrong about.

Defects (b) and (c) have nothing to bite on for the same reason, and (c) additionally because shape 18 is itself zero: 0 verdicts carry more than one obligation, `MustPreserveForce` is still 0 of 216, and no expression in any of the seven dumps applies a `case` or `let` head to value arguments. `dictflow`'s report is **byte-identical** on all seven dumps.

**(d) the totality partition is asserted in its own right.** `m24::Accounting::check()` asserted it only inside `ErasureRow::closes()`, where a failure would have been reported as the whole erasure row not closing. It is now its own equation with its own message: `ProvenTotal + MustPreserveForce + Unknown = parameters` — 118 + 0 + 98 = 216 on `-O1`.

**And the verifier had copied all three.** `verify_m24.rs` claims to share nothing with `dictflow.rs` but the IR and four named inputs, and for these three points that was not true: its `already_evaluated`, its `TotFact::join` and its `tot_eval` reproduced the analysis's decisions, defect included, so the check agreed for the wrong reason. Each is now decided there on its own terms — its own `alt_strict` map built from GHC's `strictFields`, its own witness **set**, its own refusal of an applied head — and the module's documentation says that these three were previously copied, because a verifier that had copied a decision is a fact about the verification that belongs in the record.

#### 2 — a representation class is arity *and* the capture types

`H15-OWNER-CLONES` plans one clone per distinct call-site assignment tuple. Building the tuple, `component()` rendered each settled producer set with `Shape::short()` — *arity and the number of captures* — and deduplicated on that. `Shape::class()`, which is what `Boundary::classes`, `class_keys()`, `one_representation()` and `H14-FREE-TYVAR` all mean by a representation, is *arity and the ordered capture-type keys*. Two closures of the same arity capturing the same number of differently-typed values are one variant under `short()` and two under `class()`, and the plan used the wrong one — so it under-counted the specialisations the lowering has to emit, which is the one direction a clone plan must not err in.

The tuple component is `class()` now. `short()` survives as `tuples_short`, display only, and the correction is visible in it: `ShellCheck.Fixer` `$srealignColumn` has two call sites whose tuples both render as `arity 1, 1 capture(s), arity 1, 1 capture(s)` and whose classes are (type names abbreviated to their last component)

```text
arity=1;captures=[!ShellCheck.Fixer#1181!F(C(Many),faYH6,C(Position))], arity=1;captures=[!ShellCheck.Fixer#1170!C(Ranged,faYH6)]
arity=1;captures=[!ShellCheck.Fixer#1225!F(C(Many),faYH6,C(Position))], arity=1;captures=[!ShellCheck.Fixer#1214!C(Ranged,faYH6)]
```

— two `H14-FREE-TYVAR` producer-private keys, which is exactly the distinction `short()` erases. One clone before, two after. `clone_tuples_use_the_full_shape_class_not_the_short_rendering` pins the minimal version: two closures of arity 1 capturing one `T` and one `R`.

`verify_m24.rs`'s own planner had the same defect and is corrected independently.

**Closure clones, per owning function, before → after (`-O1`):**

| module                           | owning function              |  plans | clones before | clones after |
| -------------------------------- | ---------------------------- | -----: | ------------: | -----------: |
| `ShellCheck.ASTLib`              | `$sgetLiteralStringExt`      |      1 |             2 |            2 |
| `ShellCheck.Analytics`           | `$srunNodeAnalysis`          |      1 |             3 |        **5** |
| `ShellCheck.Analytics`           | `analyse`                    |      1 |             2 |            2 |
| `ShellCheck.Analytics`           | `doVariableFlowAnalysis`     |      1 |             3 |            3 |
| `ShellCheck.CFGAnalysis`         | `go15`                       |      2 |             6 |            6 |
| `ShellCheck.CFGAnalysis`         | `go4`                        |      1 |             3 |            3 |
| `ShellCheck.Checks.ShellSupport` | `go1`                        |      1 |             3 |            3 |
| `ShellCheck.Fixer`               | `$srealignColumn`            |      1 |             1 |        **2** |
| `ShellCheck.Parser`              | `$wisFollowedBy`             |      1 |             1 |        **4** |
| `ShellCheck.Parser`              | `$wpoly_k`                   |      1 |             3 |        **4** |
| `ShellCheck.Parser`              | `$wreadIoVariable`           |      1 |             2 |            2 |
| `ShellCheck.Parser`              | `k` (eight distinct binders) |      8 |            23 |       **30** |
| `ShellCheck.Parser`              | `readAmbiguous`              |      1 |             1 |        **2** |
| **total**                        |                              | **21** |        **53** |       **68** |

Six of the thirteen owning functions move and seven do not; the refusals do not move either (66 of 87 owners still refuse rather than guess), the per-parameter class cardinality is still 509 and is still evidence rather than a count, and the eight plans with a set-valued component are still lower bounds. `h2r verify-m24` re-derives all 21 plans from its own walk with **0 disagreements**, so 68 is two independent counts and not one.

#### 3 — a claim has to carry what the check needs

`m24_claims.rs` wrote a clone plan down as a cardinality — `n` — and `verify_m24::check_plan` compared `p.tuples == c.n`. A plan with completely different variants of the same size therefore re-derived as agreeing, which is a check of arithmetic and not of a plan. An `ErasableWithObligation` claim carried no obligation at all, so the check could compare only the verdict *label*: an obligation at the wrong node would have passed.

A claim now carries its content:

- **`Claim::groups`** — the plan as a **partition of the owner's call sites**, one entry per planned clone, each site by address (`Module#node`), rendered by one shared `group_lines`. This is the content of a clone plan that survives being derived twice: *which call shares a clone with which*. It is compared for every plan.
- **`Claim::tuples`** — the deduplicated tuple set itself. For a **dictionary** plan the components are dictionary identities — addresses — and the set is compared directly. For a **closure** plan they are shape classes, and the two walks derive their capture keys independently and render them differently on purpose (`arity=1;captures=[…]` against `1/[…]`); comparing those strings would compare two renderings and not two facts, so the tuples are the record and `groups` is the check. Addressing is not sharing; rendering a derived fact would be.
- **`Claim::obligations`** — every force the verdict leaves to be discharged, as `Module#at forces what`, an address both sides build from their own derivation.

`check_plan` compares the partition, then the tuple set where its components are addresses, then the cardinality **last** — agreeing about a number after disagreeing about the content is the defect this corrects. Two new refusals carry it: `X_GROUPS_DIFFER` and `X_TUPLES_DIFFER`, plus `X_OBLIGATIONS_DIFFER` for the obligation set. And `m24.rs` will not print `[verified: yes]` for a claim that carried no content to check: a clone-plan claim whose `tuples` or `groups` do not have one entry per planned clone, or an `ErasableWithObligation` claim with an empty obligation set, is refused with `X_NO_CONTENT` rather than silently counted as proven.

Four tests make it bite, and all four corrupt the **content** while leaving every count intact: `a_clone_plan_claim_with_swapped_tuples_is_refused` reassigns the call sites between two planned clones and gets `X_GROUPS_DIFFER`; `a_dictionary_clone_plan_claim_with_swapped_tuples_is_refused` replaces one tuple with a copy of the other and gets `X_TUPLES_DIFFER`; `an_obligation_claim_with_a_changed_address_is_refused` moves the obligation to a node that does not exist and gets `X_OBLIGATIONS_DIFFER`; and `a_contentless_clone_plan_claim_is_never_marked_verified` strips the content and keeps the count, and asserts the view no longer says `yes`. Each asserts the refusal is a `D` and not a `C`.

#### 4 — enumeration and representation are different questions

`parsec::residual_edges` asks, of each of the 41 residual Parsec continuation edges, whether the closure graph gives it a finite set of continuation targets. It admitted `ExactClosure | TypeShapeUniform | FiniteClosureSet` and refused `CloneRequired` — which is the exact conflation `H11-SEPARATE` exists to prevent. Whether the producers are **enumerated** and whether **one representation** can serve them are two facts M2.4d records separately. A `CloneRequired` boundary is enumerated — that is how its clones could be counted at all — and its continuation-target set is exactly as finite as an `ExactClosure` one; needing two representations says nothing about how many targets there are.

The condition is now `bd.enumerated && every producer has a known continuation role`, read from the recogniser's own `cont_source` as before. The representation verdict is recorded beside every edge as evidence (`representation verdict …`) and gates nothing, and an unenumerated boundary gets the new status `boundary-producer-set-is-not-enumerated`, naming the verdict inside the parentheses rather than in place of the answer.

**The 41-row table is recomputed and still closes 0.** Every one of the 41 boundaries is `Unresolved` and therefore unenumerated — 20 `parameter-of-an-anonymous-lambda`, 19 `function-used-as-a-value`, 2 `call-site-is-a-partial-application` — so none of them could have closed under either condition, and the rule never reached the role question. What changed is that the table now says *why* in the terms of the question it asked. The count is the same as M2.4e published, and it was the same for a different reason: the old rule refused these 41 by verdict, and on `-O1` the verdict happened to be the same `Unresolved` that also means unenumerated.

**On four of the six matrix profiles the two part.** On C, D, E and F — every profile built with `-fno-full-laziness` — **four** residual edges sit on a boundary the closure graph calls `CloneRequired(8)`: enumerated, eight shape classes. The old rule turned those four away on the representation verdict and never asked the role question. The corrected rule asks it, and all four fail it: `producer-is-not-a-region-continuation` goes from 1 to **5** on each of the four, and the `boundary-CloneRequired(8)` row disappears. The closed count is still 0 on all seven dumps, so no verdict moves — but four edges per profile are now refused for a reason about *continuations*, which is the question M2.4e set out to ask, instead of for a reason about *representations*, which is not. That is the defect showing itself in real dumps and not only in a fixture, and it is why "nothing moved on `-O1`" was not enough to leave the condition alone.

**And the rule now fires where it could not.** `residual_edge_closes_through_a_clone_required_boundary` builds the case the old condition refused by name: one region whose `cok` boundary has two producers, both nested regions of **known role**, whose representations disagree — `CloneRequired(2)`, and enumerated. The edge closes with `P-HO-FINITE`, and the test asserts that the representation verdict is present in the evidence as `representation verdict CloneRequired(2)` rather than as the answer. `residual_edge_at_an_unenumerated_boundary_says_so` pins the other direction. Both are new, and they are what makes this more than a rewording where the dumps are silent: on `-O1` and A no edge changes its answer, because the wall M2.4e found there is the anonymous-lambda wall and not a representation one, and the fixture is the only place the corrected rule can be seen firing.

*(`parsec.rs` carries **29** unit tests of its own — 27 before these two; M2.4e's text called one of them "the" regression test. That is corrected above.)*

#### The gate for this correction

**312 reports** were captured over the seven dumps before and after — `stats`, `laziness`, `tuples` (plus `--verify`, `--scalar-all`, `--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus `--heads`, `--explain`), `verify-rep` (plus `--explain`), `parsec` (plus `--explain`, `--cfg-all`), `classops` (plus `--per-module`, `--view-all`), `dictflow` (plus `--explain`), `higher` (plus `--view-all`), `verify-m24` (plus `--explain`), `m24`, `compare`, three `show` nodes and the `--json` form of each. **214 are byte-identical**, **98 moved**, and every one of the 98 is a report this correction was allowed to move; every run's standard error was captured too and is identical on both sides everywhere.

The 98 are fourteen reports × seven dumps, and nothing else:

| report                              | lines moved (`-O1` … F) | what moved                                                                                                                                                      |
| ----------------------------------- | ----------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `classops`                          | 2                       | the one closure-clone line of the accounting block it shares with `higher`                                                                                      |
| `classops --json`                   | —                       | the `named_forces` key, added; no existing value                                                                                                                |
| `dictflow --json`                   | —                       | `obligation` → `obligations` on values and parameters (empty on every dump), plus `groups` on each clone plan and `named_forces`; **no existing value changes** |
| `higher`                            | 52 … 70                 | the clone-plan table: 53 → 68 and the per-owner rows that produced it                                                                                           |
| `higher --json`                     | 1                       | `owner_clones`, and nothing else                                                                                                                                |
| `higher --view-all`                 | 20                      | the clone tuples in each boundary view, now the full shape class                                                                                                |
| `m24`                               | 8 … 9                   | the closure-clone row, and the three `parsec` residual status lines                                                                                             |
| `m24 --json`                        | —                       | the same two, in `accounting.erasure.plans` and `m21ResidualEdges`                                                                                              |
| `parsec`, `parsec --explain`        | 135 … 1,007             | every residual edge's status string, plus one `representation verdict …` evidence line each                                                                     |
| `tuples --verify`                   | 6 … 7                   | the same residual summary, which this report prints in brief                                                                                                    |
| `verify-m24`, `--explain`, `--json` | 3, and 5 on E and F     | the three appended shape rows (16–18); on E and F also row 12's exemplar, `Main $s$wgo1` 1 → 2 tuples, which is the H15 correction again                        |

Everything else is **byte-identical on all seven dumps**, including `dictflow` itself (the totality corrections move no verdict), `parsec --json` and `parsec --cfg-all` (the residual section is not in either), `classops --per-module` and `classops --view-all`, `tuples`, `fields`, `lists`, `text`, `verify-rep`, `compare`, and all three `show` nodes with their M2.4 footers.

No Core is mutated, no codegen is emitted, no GHC flag changed, no `rust-port` file is touched. `cargo test` is **243** (eleven new: one per defect in the totality domain and its strict twin, one for the shape class against the short rendering, three for a claim whose contents are corrupted while its counts are preserved, one for a claim with no content at all, and two for the corrected `parsec` condition), `cargo clippy --all-targets` 0 warnings and `cargo fmt --check` clean.

### M2.4 acceptance

*(Every count below is as M2.4g measured it, with [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)'s one moved number — 53 planned closure clones → **68** — folded in.)*

**The criterion is that the three questions are answered separately, that every positive answer is re-derived by a walk that shares nothing with the first but the IR and four named trusted inputs, and that every residual is itemised and owned.** Not that coverage is high: on this program it is low, and the milestone's contribution is knowing exactly why.

**Question 1 — can the call target be enumerated?** `sites = Exact + FiniteSet + Unresolved` closes on all seven dumps. [7 of 565](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go) on `-O1`, and **0 per module**: GHC's simplifier has already taken every site whose dictionary is visible, so what survives is dispatch on a run-time parameter. The closed-world fixpoint bounds the *dictionary* at 118 sites and at 106 of the 216 parameters, which is a different and larger result than the seven targets, and the accounting prints it as a separate fact. [The residual table above](#the-milestone-accounting--three-questions-never-collapsed) itemises all 558, and the largest row — 413 — is not a weakness of the walk but `W0` biting: those sites live in bindings nothing in the closed world references.

**Question 2 — can this abstraction boundary use one representation?** `boundaries = ExactClosure + TypeShapeUniform + CloneRequired + FiniteClosureSet + Preserve + Unresolved` closes on all seven dumps. There are **three** counts here and M2.4d′ had to separate them: 252 boundaries have an enumerated producer set, 84 satisfy the *one* statement of the theorem (`Boundary::one_representation` — enumerated, one shape class, no opaque producer), and 66 are `rewritable_as_one`, which additionally requires the rewrite to own the slot. The accounting prints all three side by side and asserts the inclusion. 4,613 of the 5,322 `Unresolved` are the Parsec CPS wall.

**Question 3 — can the object actually disappear?** `values = Erasable + WithObligation + WithClone + Preserve + Unresolved` and the same for parameters, both closing on all seven dumps, with the totality domain's 118/0/98 asserted to sum to 216 beside them. Erasure is computed from facts recorded **separately** from the targets and crossed with them in the 3×5 matrix rather than collapsed. Both clone plans are **owner-level** — distinct call-site assignment tuples, never the sum of per-slot cardinalities — and every plan with a set-valued tuple is flagged as the lower bound it is.

**The verifier.** `h2r verify-m24` re-derives **606** positive claims on `-O1` (749 / 867 / 2,209 / 2,187 / 2,209 on B–F) with **0 disagreements and 0 coverage refusals on all seven dumps**, and reproduces every published table cell for cell on a walk that has never seen them. Two tests make it bite. Every number in this section is the verifier's own or carries its answer beside it.

**The corrections history.** Three, all found by review of the published work rather than by a failing test, and all in the direction of the analysis having claimed more than its evidence:

|                                                                                                             | what was wrong                                                                                                                                                                                                                                                                                                                                                                                                                                                                       | what it moved                                                                                                                                                                                                                                         |
| ----------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [M2.4c′](#correction-m24c--totality-is-not-the-same-fact-as-identity)                                       | `Erasable` was decided from *bounded dictionary identity*, which a MAY-analysis over a `case` gives without the producer being total; and the per-parameter clone cardinalities were summed                                                                                                                                                                                                                                                                                          | no verdict moved (`MustPreserveForce` is 0 because `-O1` floats every dictionary out of every scrutinee — an instrumented fact, re-derived by M2.4f) and 8 clones → **4**                                                                             |
| [M2.4d′](#correction-m24d--sharing-is-decided-before-agreement-and-a-free-type-variable-identifies-nothing) | six defects: `H8` decided after `H5`/`H6`; two different one-representation theorems and opaque shapes merging; per-parameter clone counts summed; free type variables merging unrelated closures; existential fields indexed by raw binder position; `UniformRepresentation` named a Rust fact it is not                                                                                                                                                                            | `ExactClosure` 67 → **50**, `Preserve` 26 → **44**, one representation 103 → **84**, rewritable 87 → **66**, shape classes 261 → **353**, clones 418 → **53** (→ **68** in M2.4h)                                                                     |
| [M2.4f](#the-one-correction-this-produced)                                                                  | the *record*, not a verdict: M2.4d′ said ShellCheck's Core has no alternative binding a function-typed field after an existential type binder. It has four                                                                                                                                                                                                                                                                                                                           | no number moved; the prose was corrected and the shape is now counted on every run (rows 11 and 11a)                                                                                                                                                  |
| [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)                                      | four: three in the totality domain (every alternative binder read as already evaluated, the obligation join keeping one of a set, an applied `case`/`let` head peeled) which `verify_m24.rs` had **copied rather than derived**; clone tuples deduplicated by arity-and-capture-count instead of by representation class; a claim protocol that carried counts where the check needed contents; and `parsec::residual_edges` gating target enumeration on the representation verdict | closure clones 53 → **68**; nothing else moved as a number — the three totality shapes are absent from all seven dumps and the 41 Parsec edges still close **0** — but the claim protocol, two refusal reasons and the `parsec` status column are new |

**Trusted inputs and assumptions, named.** The first four are the trusted inputs: consulted and never verified, on both sides of the M2.4f check, and printed at the top of every `verify-m24` run. The last two are assumptions the *verdicts* rest on rather than inputs either walk reads.

1. **the 17-class method-field table** (`classops::CLASSES`), a level-5 axiom: format 5 carries neither a type nor an unfolding for a global, so a selector's `C a => …` type and its `case d of C:C … m … -> m` body are both absent and the field order is **not derivable from the dump at all**. Every *use* of the table is re-derived, including the cross-check against the dictionary constructor's own `repArity` — 0 disagreements and 0 classes outside the table on all seven dumps;
2. **`W0-CLOSED-WORLD` / `H0-CLOSED-WORLD`** — the 28 modules are the whole program and `Main.main` its only root. An assumption about the *build*, which no walk can prove, and the one 413 of the 558 unresolved sites rest on;
3. **GHC's own flags** — `isClassOpId`, `isExportedId` and the demand signatures' strictness bits, read from the authoritative source;
4. **the structured `Ty`** and `TyCon` stable-name identity (format 5);
5. **free type variables are compared by GHC unique** in `Ty::alpha_eq`, and a unique is not an identity in optimised Core. `H14-FREE-TYVAR` keeps the *shape class* off that — a capture type with a free type variable gets a producer-private key — but the IR predicate itself is unchanged and must not be handed a free-tyvar-sensitive proof;
6. **the M3 carrier invariant** behind `TypeShapeUniform`: the verdict is a fact about *Haskell* types (same arity, same ordered captured Haskell types). Reading it as *one Rust representation* is sound only if the lowering promises a canonical closure-boundary carrier per Haskell type with conversions inserted at the boundary. **That invariant is open**, and every `h2r higher` run says so.

**What remains, and who owns it.**

- **`Main.main`-rooted reachability — done, and conditional.** [M3a](#m3a--mainmain-rooted-reachability) computed the rooted set: 9,831 of the 13,828 top-level bindings are dead on `-O1`, 8,855 more than the zero-reference subset sees. What it also found is that the dump is serialised *before* `CoreTidy`, so 112 cross-module references name bindings under names their own module's dump does not carry; 8,131 of the dead verdicts are conditional on that, and every stable-name linkage in the compiler — `dictflow`'s, `classops`'s and `higher`'s — has the same gap. Fixing the plugin's naming is M3b's first task.
- **M3: the canonical closure carrier.** Until the lowering promises one, `TypeShapeUniform` is a Haskell-type fact and the 16 boundaries carrying it are not yet one Rust representation.
- **M3: a call-string analysis for the set-valued tuples.** 4 dictionary plans and 8 closure plans on `-O1` have a tuple with a set-valued component, because the fixpoint is monovariant (`W5`, `H3`). Their clone counts are lower bounds on both sides of the verifier — agreement about a bound, not a closing of it.
- **The anonymous-lambda naming pass.** 4,613 of the 5,322 unresolved boundaries, all 41 Parsec edges and five of the six largest M2.3 closure holders are one shape: `ShellCheck.Parser` is CPS, its continuations are anonymous lambdas passed as values, and a higher-order analysis that wants them has to name them first.
- **A future dump format: global types and unfoldings.** The class table is an axiom only because the dump carries neither for a global — still true of format 6, which widened the id table to every *external* global but did not add a type or an unfolding body to it. A format that did would make the table **derivable**, and the one level-5 assumption that both sides of the M2.4f check share would go.
- **`Unresolved` and `Preserve` are not re-derived as claims** — the deliberate asymmetry, narrowed but not closed by M2.4f's whole-population table.

`cargo test` (**232** — seven new: the class-op view over a module, the boundary view's rule order at a slot that is and is not exported, the boundary view over a module, the accounting's three questions, the `show` provenance with both opt-outs, the M1 link's invariant under a milestone that already claims every site, and a planted refusal that must never be reported as proven; **243** since [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), which added eleven), `cargo clippy --all-targets` (0 warnings) and `cargo fmt --check` are clean.

### The gate

**262 reports** were captured over the seven dumps before and after: **215 byte-identical**, 28 appended-only, 11 multiset-identical up to an `e.g.` exemplar, 7 canonical-JSON-identical and one `show` that gains its footer. Every existing report is **byte-identical** before and after, on `compiler/core-json` and on all six matrix profiles — `stats`, `laziness`, `tuples` (plus `--explain`, `--verify`, `--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus `--heads`, `--explain`), `verify-rep` (plus `--explain`), `dictflow` (plus `--explain`), `verify-m24` (plus `--explain`), `classops --per-module`, `compare` and the `--json` form of each — with three deliberate movements and nothing else:

- **`classops` and `higher` gain the accounting section**, 85 lines appended after everything they already print, so **not one existing line moves** — the *after* file starts with the *before* file byte for byte, on all seven dumps and with `--explain`. Their `--json` gains no key at all, because the views are their own `--view`/`--view-all` reports, and `classops --per-module` gains nothing at all: that mode exists to reproduce M2.4b exactly.
- **`parsec --explain` and `parsec --json`** change *order* only — multiset-identical and canonical-JSON-identical on all seven dumps — and `parsec` itself changes one `e.g.` exemplar line on B, C, E and F, which is the nondeterminism being fixed rather than a report changing. All three are now stable across runs.
- **`show`** gains M2.4 marks and footers on nodes that have them — `ShellCheck.Parser 141341` gains one inline mark and an eight-line boundary footer, `ShellCheck.AST 5293` is unchanged because it has neither — and `--no-classops --no-higher` reproduces the previous output **byte for byte**.

`h2r m24`, `h2r classops --view/--view-all` and `h2r higher --view/--view-all` are new commands. No Core is mutated, no codegen is emitted, no GHC flag changed.

## M3 — the lowering

M2.4 closed the last of the analysis milestones. M3 is the first one that **builds** something: it does not end with another census, it constructs a new program representation.

```text
GHC Core + M1–M2.4 proof objects → reachable program → explicit semantic NIR
  → closure conversion + specialisation → apply certified transformations
  → Rust-facing normal form → small generated-Rust canary
```

A new crate, `h2r-lower`, consumes `h2r-core-ir` and `h2r-analysis` and constructs the new IR. `h2r-core-ir` stays the flattened dumped Core, `h2r-analysis` stays the proof-producing layer, `h2r-rt` stays the runtime target. The sub-milestones:

|          |                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| -------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| **M3a**  | `Main.main`-rooted reachability — **done**, with a linkage hole it measured rather than hid                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| **M3a′** | dump post-CoreTidy Core and re-establish whole-program identity — **done.** The resolver decides locality lexically; the plugin runs `CoreTidy` itself, serialises the tidied program and joins back, field by field, the facts CoreTidy discards (`demand`, `oneShot`, `exported`), with the alignment proved per module at extraction time. All seven dumps regenerated, `A5-IN-WORLD-MISSING` **0** on every one, dump format 6. **The format-6 baseline run and verifier checks are complete. Before/after accounting and site-level attribution remain open; see todo.md.** See the [format-6 baseline](#format-6-baseline-2026-09-16). See [M3a′](#m3a--dump-post-coretidy-core-and-re-establish-whole-program-identity) |
| **M3b**  | the normalised IR — NIR, ANF/CFG-shaped, `FnId`/`ValueId`/`BlockId`, explicit `Delay`/`Force`/closure create/return, every instruction carrying `Origin { module, source_node/binder, rule }`, and **no `OpaqueCore` escape hatch**                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| **M3c**  | canonical carriers `Carrier(T)` plus closure conversion, so no anonymous `Lam` remains — this is what closes the open invariant `TypeShapeUniform` rests on                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    |
| **M3d**  | polyvariant specialisation keyed by `(FnId, DictAssignment, ClosureShapeAssignment)` from a live-rooted worklist, closing the set-valued clone lower bounds without a call-string length — **done** for the type-and-dictionary key: an instance is `(module, binder, type arguments, dictionaries)`, interned under a canonical alpha-equivalence key and driven from a live-rooted worklist. Closure-shape assignment is not part of the key. See [M3d](#m3d--polymorphism-and-typeclass-specialization)                                                                                                                                                                                                                     |
| **M3e**  | explicit evaluation: M1 consumed — `Delay`, `Lazy`, shared and recursive thunks — and every M2.4 force obligation becomes a `Force`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |
| **M3f**  | apply the certified representation rewrites. `Erasable` is *permission, not obligation*; every destructive rewrite gets a certificate naming the source address and the proof rule or claim it rests on                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| **M3g**  | lower the proven Parsec CPS regions into blocks and jumps using M2.1's regions and edges — no re-recognition, no names                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| **M3h**  | the lowering audit, and a thin canary emitter compiling at least one nontrivial reachable leaf SCC against `h2r-rt`                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |

**Acceptance for all of M3:** the complete `Main.main`-reachable ShellCheck program exists as an explicit, proof-carrying NIR with no implicit laziness and no anonymous closures, every optimisation traceable to an M1–M2.4 proof, and at least one reachable lowered SCC emitted as Rust and compiled.

Three forbidden temptations, stated so they can be refused by name: **no further dump-format project** unless the lowering hits a concrete blocker the current format cannot represent — M3a′ did bump the format to 6, and that was not a representational wish but the only honest way to mark a changed contract: the dump is now the post-`CoreTidy` program, and a format-5 consumer must not read it as the pre-tidy one; **no requirement to resolve every existing `Unresolved`** before lowering — the conservative NIR gives an unresolved case a correct fallback; and **no mutation of the source Core arena or its proof objects**.

## M3a — `Main.main`-rooted reachability

M2.4c's most uncomfortable finding was that a large part of the dump is never referenced by any of it, and that [413 of the 558 unresolved class-op sites](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go) live in that part. But the *zero-reference* set (`function-is-unreachable-in-the-closed-world`) is a valid dead **subset**, not a rooted dead **set**: it cannot see a binding referenced only by another dead binding, and it cannot see a recursive function whose only reference is its own. M3a computes the rooted set.

### The graph

The nodes are the **top-level binding pairs** of every module of the closed world — all 13,828 of them on `-O1`, not the exported ones and not the function-shaped ones — identified by `(module index, BinderId)` and never by a name. Three top-level bindings of `ShellCheck.AST` share the internal name `$_sys$$fTraversableInnerToken`; a name-keyed node table would silently make one of them stand for the others.

An edge is established two ways, and two ways only:

- **`A2-EDGE-LOCAL`** — `Module::resolve` gives `Ref::Local(b)` and `Module::binding(b).site` is `Top`. Lexical binder identity; the binding *site* decides, never the name. This is the only rule that can ever reach an internally-named top-level binding.
- **`A3-EDGE-GLOBAL`** — the resolver gives `Ref::Global` and the occurrence's stable name is the name of an *external* top-level binding of some in-world module. The same linkage `W1-GLOBAL-CALLERS` and `classops::World` already use; external names only, because an internal name is not unique.

An occurrence resolving to a lambda, `let`, `case` or alternative binder is not an edge: it names something *inside* a top-level binding. A global occurrence naming no in-world module is an **import reference** (`A4-IMPORT`), recorded with its count but not an edge, because the definition is outside the world.

### The rules

| Rule                     | Evidence | Meaning                                                                                                                                                                                                                                                                 |
| ------------------------ | -------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `A0-CLOSED-WORLD`        | 5        | The dump is the whole program and `Main.main` is its only root. This is `W0-CLOSED-WORLD` / `H0-CLOSED-WORLD` **cited, not re-asserted**: an assumption about the build that no walk can prove, and the one every `dead` verdict below rests on.                        |
| `A1-ROOT-MAIN`           | 4 over 1 | The root is the top-level binding of the dump's `Main` module whose stable name is `$<that module's unit>$Main$main`, found structurally through the world index. Not exactly one such binding is a named failure, never a guess.                                       |
| `A2-EDGE-LOCAL`          | 1        | An occurrence the resolver maps to a binder bound at top level is an edge to that binding.                                                                                                                                                                              |
| `A3-EDGE-GLOBAL`         | 3        | A global occurrence whose stable name is an external top-level binding of an in-world module is an edge to it.                                                                                                                                                          |
| `A4-IMPORT`              | 4        | A global occurrence whose stable name belongs to no in-world module is an import reference, counted per name, separately from live and from dead code. Not an edge.                                                                                                     |
| `A5-IN-WORLD-MISSING`    | 4 over 5 | A global occurrence whose stable name's unit *and* module are an in-world module's, that no top-level binding of that module defines, and that GHC's own flags do not mark as a data constructor or a class-op selector. Its own category. **It is not 0** — see below. |
| `A6-LIVE-CLOSURE`        | 3        | Live is the transitive closure of `A2`/`A3` edges from the `A1` roots, and nothing else.                                                                                                                                                                                |
| `A7-DEAD-NO-REFS`        | 3        | No occurrence anywhere in the closed world. This **calls** `dictflow`'s own `Program::is_unreachable_top`, the predicate behind `T_UNREACHABLE`, rather than restating it, so the two cannot drift.                                                                     |
| `A8-DEAD-ONLY-FROM-DEAD` | 3        | Referenced, but every top-level binding that references it is itself dead. The population the zero-reference subset could not see.                                                                                                                                      |
| `A9-WITNESS`             | 3        | Every live binding carries one **shortest** chain of edges from a root to it, so the verdict is checkable by hand from the report.                                                                                                                                      |
| `A10-ACCOUNTING`         | 5        | `top = live + dead` per module and in total; `dead = no-refs + only-from-dead`. Asserted, never assumed.                                                                                                                                                                |
| `A11-MISSING-IMPACT`     | 6        | A **name**-matched bound on what an `A5` hole could cost. Diagnostics only. No edge, no verdict and no accounting figure rests on it, and it exists only so the damage can be stated as a number.                                                                       |

Trusted inputs, named on every run and shared with the verifier: `W0`; the module list; the root name; the IR's resolver (`Module::resolve`, `Module::binding`, `Module::occurrences`); and GHC's own `isClassOp` flag and data-constructor record.

### The result on `-O1`

| module                            |       top |     live | dead, no references | dead, only dead referrers |
| --------------------------------- | --------: | -------: | ------------------: | ------------------------: |
| `Main`                            |       502 |      409 |                  18 |                        75 |
| `Paths_ShellCheck`                |        63 |        0 |                   9 |                        54 |
| `ShellCheck.AST`                  |      1083 |       35 |                 320 |                       728 |
| `ShellCheck.ASTLib`               |       346 |      150 |                  44 |                       152 |
| `ShellCheck.Analytics`            |      2676 |      489 |                  14 |                      2173 |
| `ShellCheck.Analyzer`             |         8 |        3 |                   1 |                         4 |
| `ShellCheck.AnalyzerLib`          |       650 |      309 |                  82 |                       259 |
| `ShellCheck.CFG`                  |      1003 |        0 |                 104 |                       899 |
| `ShellCheck.CFGAnalysis`          |       895 |        0 |                 128 |                       767 |
| `ShellCheck.Checker`              |        36 |       33 |                   1 |                         2 |
| `ShellCheck.Checks.Commands`      |      1254 |        0 |                  17 |                      1237 |
| `ShellCheck.Checks.ControlFlow`   |        16 |        0 |                   4 |                        12 |
| `ShellCheck.Checks.Custom`        |         9 |        0 |                   2 |                         7 |
| `ShellCheck.Checks.ShellSupport`  |       906 |        0 |                   7 |                       899 |
| `ShellCheck.Data`                 |      1340 |     1078 |                   1 |                       261 |
| `ShellCheck.Fixer`                |        92 |        0 |                   9 |                        83 |
| `ShellCheck.Formatter.CheckStyle` |        53 |        0 |                   2 |                        51 |
| `ShellCheck.Formatter.Diff`       |       156 |        0 |                   6 |                       150 |
| `ShellCheck.Formatter.Format`     |        62 |        0 |                  14 |                        48 |
| `ShellCheck.Formatter.GCC`        |        22 |        0 |                   2 |                        20 |
| `ShellCheck.Formatter.JSON`       |        69 |        0 |                   7 |                        62 |
| `ShellCheck.Formatter.JSON1`      |        91 |        0 |                   9 |                        82 |
| `ShellCheck.Formatter.Quiet`      |        11 |        0 |                   2 |                         9 |
| `ShellCheck.Formatter.TTY`        |        93 |        0 |                   2 |                        91 |
| `ShellCheck.Interface`            |       680 |        1 |                 137 |                       542 |
| `ShellCheck.Parser`               |      1645 |     1487 |                  24 |                       134 |
| `ShellCheck.Prelude`              |        42 |        0 |                   6 |                        36 |
| `ShellCheck.Regex`                |        25 |        3 |                   4 |                        18 |
| **total**                         | **13828** | **3997** |             **976** |                  **8855** |

17,695 edges over 21,636 occurrences — 17,197 intra-module, **498** inter-module, which is how thin the linkage between ShellCheck's modules actually is in optimised Core. 569 distinct external stable names are referenced, 11,924 times from live code and 27,347 times from dead; `Text.Parsec.Error.ParseError`, `$wmergeError`, `GHC.Types.[]`, `unpackCString#` and `GHC.Types.:` are the five most used.

**The zero-reference column of that table is not the old 922.** Over the whole 13,828-binding population `dictflow`'s own predicate gives **977** on `-O1` — the 922 in [M2.4c](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go) was measured over an unstated sub-population and is left standing there as the historical record; the number every later pass should quote is the one `Program::is_unreachable_top` produces over all top-level bindings, which is now the only place the predicate exists.

### The subset check

|                                                             |     `-O1` |
| ----------------------------------------------------------- | --------: |
| zero-reference (`dictflow`'s own `T_UNREACHABLE` predicate) |       977 |
| …of which are **roots**                                     |         1 |
| …of which are rooted-dead                                   |       976 |
| …neither dead nor a root — the gate asserts 0               |     **0** |
| rooted dead                                                 |     9,831 |
| **additional dead the rooted analysis finds**               | **8,855** |

The gate is `zero-reference \ roots ⊆ dead`, not `zero-reference ⊆ dead`, and the difference is not a fudge: a program's entry point is not called by the program, so `$…$Main$main` has no occurrence anywhere and is the one zero-reference binding that is live. It is named in the report every run.

### What the extra 8,855 are

Three shapes, all of them invisible to a zero-reference test:

- **Recursive functions whose only reference is their own.** 506 dead bindings occur inside their own right-hand side and nowhere else — `ShellCheck.ASTLib getCommandSequences` (6 referrers, all dead), `ShellCheck.AST $s$c==` (4), `Paths_ShellCheck lastChar` (2). A zero-reference test counts the self-occurrence and lets every one of them through.
- **Dead components that hang together.** `ShellCheck.AST $trModule` is referenced by **140** other bindings and every one of them is dead; the `Typeable` machinery of a module nothing reaches is a large, densely connected, entirely dead subgraph. `ShellCheck.CFG $trModule` (63), `ShellCheck.Interface $trModule` (51) and `ShellCheck.Checks.Commands lvl` (54) are the same shape.
- **Instance and dictionary chains.** `Main $fEqStatus` ← `$fOrdStatus`, `Main $fSemigroupStatus` ← `$cstimes`, `$fMonoidStatus`, `Main $c==` ← `$fEqStatus`: a dictionary is referenced by exactly the instance that builds it, and nothing reaches the instance.

`h2r lower --reachability <dir> --explain <name>` prints the witness path of a live binding hop by hop with the rule for each hop, or the dead reason and the full referrer list of a dead one.

### The finding: `A5-IN-WORLD-MISSING` is **not** 0

This is the milestone's real result, and it is a defect in the *dump*, not in the walk.

> *This section records M3a as it stood, on the pre-`CoreTidy` dumps. [M3a′](#m3a--dump-post-coretidy-core-and-re-establish-whole-program-identity) fixed the defect: the plugin now serialises the tidied program, the dumps have been regenerated on all seven profiles, and `A5-IN-WORLD-MISSING` is **0** on every one. The numbers below are the pre-tidy ones and are kept because they are what the finding was made of.*

`h2r-plugin` appends its pass after the optimisation pipeline and serialises the `CoreProgram` **before GHC's `CoreTidy` pass** — and `CoreTidy` is exactly what externalises a top-level binder GHC has kept internal, and what invents the names `foo1`, `$wfoo`, `foo_$sbar` that appear in the module's interface file. So the defining module's dump carries the *pre-tidy* name while every downstream module, which read the *tidied* interface, refers to the same binding by the *post-tidy* one:

| the reference, in the module that makes it                        | the binding, in its own dump                                                                                                                |
| ----------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------- |
| `ShellCheck.Analyzer` → `$…$ShellCheck.Checks.Commands$$wchecker` | `$_in$$wchecker`                                                                                                                            |
| `ShellCheck.Analytics` → `$…$ShellCheck.ASTLib$$wgetPath`         | `$_in$$wgetPath`                                                                                                                            |
| `Main` → `$…$ShellCheck.Formatter.TTY$format1`                    | *(nothing: no binding of that occurrence name exists in `ShellCheck.Formatter.TTY`'s dump at all — `format1` is a name `CoreTidy` invents)* |

The closed world cannot see that the two names are one binding, so the reference establishes no edge. On `-O1` that is **112 stable names over 1,232 occurrences**, **54 of them referenced from live code**. Every stable-name linkage in the compiler has this gap — `dictflow::Program::tops`, `classops::World::tops` and `higher`'s producer enumeration all build the same index — and M3a is simply the first pass whose answer *depends* on it.

What it costs, stated two ways and neither of them a repair:

- the **sound** bound, which uses no name: the 19 modules an unlinkable live-referenced name points into hold **8,131 of the 9,831** dead bindings, so those verdicts are conditional;
- the **constructive** bound (`A11-MISSING-IMPACT`, evidence level 6): **18** of the 112 names do have top-level bindings of the right module with the matching *occurrence* name — 23 of them, and every one a `$w…` worker, the one form `CoreTidy` leaves alone. They are `$wchecker` of `ShellCheck.Analytics`, of `Checks.Commands` and of `Checks.ShellSupport`, `$wbuildGraph` of `ShellCheck.CFG`, `$wanalyzeControlFlow` of `ShellCheck.CFGAnalysis`, `$wrunChecker` of `AnalyzerLib`, `$wapplyFix` of `Fixer` — the worker entry points of exactly the modules that show 0 live above. Re-running the closure with those 23 name-matched edges added makes **5,240** further bindings live: `ShellCheck.Analytics` 2,157, `Checks.Commands` 1,177, `Checks.ShellSupport` 870, `CFG` 354, `CFGAnalysis` 291, `Data` 257 and six modules more. The other 94 names have no candidate at all, so even 5,240 is a floor.

The report leads with this: `h2r lower --reachability` prints a `STATUS — THE DEAD SET IS CONDITIONAL` block immediately after the roots, on every dump, and the live set is labelled a **lower bound**. `ShellCheck.Checks.Commands` showing 0 live bindings in the table above is that defect and nothing else: the program obviously runs the command checks.

**This is the first thing M3 has to fix**, and it is squarely a [forbidden-temptation](#m3--the-lowering) case — a concrete blocker the current dump cannot represent. The fix is not a new format: it is moving the plugin's serialisation after `CoreTidy`, or recording each top-level binder's tidied name beside its pre-tidy one. Nothing here guesses in the meantime; a name match is level 6 and no verdict reads one.

[M3a′](#m3a--dump-post-coretidy-core-and-re-establish-whole-program-identity) took this on. Moving the serialisation after `CoreTidy` does close the hole completely — `A5` goes to 0 and the live set to 9,795 on a scratch dump — but it also takes GHC's per-binder demand off every lambda, `case` and alternative binder, which M2.3b, M2.3c, M2.4b and M2.4c read. The numbers in this section therefore still stand, and M3a′ stopped rather than regenerate.

### Where M2.4's residual sits

`h2r lower --reachability <dir> --m24-link` crosses the live set with M2.4's two unresolved populations. It costs one `dictflow` and one `higher` run, so it is off by default, and it inherits `A5` in full: a site inside a binding the linkage hole wrongly calls dead is counted dead here too.

|                                                                 |   `-O1` |
| --------------------------------------------------------------- | ------: |
| class-op dispatch sites                                         |     565 |
| …`Unresolved`                                                   |     558 |
| …inside a rooted-dead top-level binding                         | **484** |
| …`Unresolved` for `function-is-unreachable-in-the-closed-world` |     413 |
| …inside a rooted-dead top-level binding                         | **413** |
| function-valued boundaries                                      |   5,574 |
| …`Unresolved`                                                   |   5,322 |
| …inside a rooted-dead top-level binding                         | **331** |
| …a constructor field, which has no one binding to be inside     |      19 |

All 413 sites M2.4c attributed to the zero-reference subset are rooted-dead, as they must be, and the rooted analysis adds 71 more — 484 of the 558 unresolved class-op sites are in code `Main.main` cannot reach. The higher-order residual is the opposite shape: only 331 of 5,322 unresolved boundaries are in dead code, because 4,613 of them are `ShellCheck.Parser`'s CPS continuations and `ShellCheck.Parser` is 1,487 of 1,645 live. Killing dead code will not shrink the Parsec problem; M3g still has to lower it.

### The verifier

`h2r-lower/src/verify.rs` re-derives every claim from the IR alone. It shares nothing with `reachability.rs` but the arena and the five named trusted inputs, and it reads the `LiveSet` only as *data*: a population, a set of verdicts, a set of witnesses, a set of edges.

The two derivations are deliberately opposite. The census walks **down** — pre-order over each top-level right-hand side, collecting the occurrences it finds. The verifier works **up**: for every node of every arena it climbs `Module::parent` to the root and reads the `Edge::Top` it arrived by, giving an owner map, and phrases every check over that map and over `Module::occurrences`, the IR's own occurrence index.

|                        | what it re-derives                                                                                                                                      | claims on `-O1` |
| ---------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------: |
| `V1-ROOTS`             | the roots are exactly `Main`'s `$<unit>$Main$main`, and every binding carrying that name is a root                                                      |               2 |
| `V2-POPULATION`        | every top-level binding of every module appears exactly once in `live ∪ dead`, with the module and stable name it claims                                |          41,484 |
| `V3-LIVE-CLOSED`       | no live right-hand side names a dead top-level binding                                                                                                  |           6,111 |
| `V4-DEAD-UNREFERENCED` | every occurrence of a dead binder, intra-module through `occurrences` and inter-module through the stable-name scan, lies inside a dead right-hand side |          14,526 |
| `V5-WITNESS`           | every witness starts at a root, ends at its binding, and every hop is an edge re-derived here                                                           |           3,997 |
| `V6-EDGES`             | the recorded edges are exactly the IR's, rule and occurrence count included                                                                             |          35,390 |
| `V7-DEAD-REASON`       | every dead reason and referrer list is the one the IR gives                                                                                             |           9,831 |
| `V8-ACCOUNTING`        | the identities hold over the *contents*, not the counters                                                                                               |              30 |
| `V9-ZERO-REFERENCE`    | the zero-reference set is exactly the unreferenced bindings, every one dead or a root                                                                   |           1,954 |
|                        | **total**                                                                                                                                               |     **113,325** |

**0 disagreements on all seven dumps.** Six tests make it bite: a dead binding moved to live, a live one moved to dead (checked in both directions), a witness with its root removed, a dropped edge, an invented edge, and a binding carrying two verdicts. Each asserts that a *named* check fires, not merely that the audit fails.

### Across the flag matrix

|                                      | `core-json` |  A `-O1` |  B `-O2` |        C |        D |        E |        F |
| ------------------------------------ | ----------: | -------: | -------: | -------: | -------: | -------: | -------: |
| top-level bindings                   |      13,828 |   13,828 |   13,957 |    6,073 |    7,209 |    7,209 |    7,197 |
| live                                 |       3,997 |    3,997 |    3,525 |    1,260 |    1,484 |    1,484 |    1,482 |
| dead, no references                  |         976 |      976 |    1,000 |      930 |    1,057 |    1,057 |    1,055 |
| dead, only dead referrers            |       8,855 |    8,855 |    9,432 |    3,883 |    4,668 |    4,668 |    4,660 |
| zero-reference set                   |         977 |      977 |    1,001 |      931 |    1,058 |    1,058 |    1,056 |
| …not dead and not a root             |       **0** |    **0** |    **0** |    **0** |    **0** |    **0** |    **0** |
| `A5-IN-WORLD-MISSING` names          |         112 |      112 |      125 |       83 |      109 |      109 |      109 |
| …dead bindings they make conditional |       8,131 |    8,131 |    8,949 |    3,889 |    4,854 |    4,854 |    4,845 |
| verifier claims                      |     113,325 |  113,325 |  115,720 |   50,133 |   64,002 |   63,582 |   63,479 |
| verifier disagreements               |       **0** |    **0** |    **0** |    **0** |    **0** |    **0** |    **0** |
| accounting identities                |    all hold | all hold | all hold | all hold | all hold | all hold | all hold |

`compiler/core-json` and `matrix/A` produce byte-identical reports, as they should: A *is* the `-O1` profile. C's top-level population is less than half of A's because `-fno-full-laziness` is the profile that stops hoisting constants to top level — the same finding the census made about `lvl…` float-outs, now visible in the node count of the live graph itself. The share of the program that is dead rises from 71.1% on `-O1` to 79.4% on D–F, which is the linkage hole growing with the amount of cross-module inlining rather than the program shrinking.

### The gate

**44 reports** were captured on `compiler/core-json` before and after — `stats` (plus `--per-module`), `laziness`, `parsec`, `tuples` (plus `--verify`, `--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus `--heads`), `verify-rep`, `classops` (plus `--per-module`), `dictflow`, `higher`, `verify-m24`, `m24`, the `--explain` and `--json` form of each that has one, and two `show` nodes. **All 44 are byte-identical.** M3a adds a report; it moves none.

The one change outside `h2r-lower` and `h2r-cli` is in `h2r-analysis/src/dictflow.rs`, and it is deliberately not a change of behaviour: `Program::is_unreachable_top` names the predicate that was written inline at `T_UNREACHABLE`'s one call site, and `producers_of` now calls it, so M3a's `A7` and M2.4c's `T_UNREACHABLE` cannot drift apart. `all_occurrences` and `is_external_name` became `pub` for the same reason. No Core is mutated and no proof object is touched.

`h2r lower --reachability <dir>` produces byte-identical output on two consecutive runs, in both the text and the `--json` form, on every dump: the node order is the dump's own, every adjacency is a `BTreeMap`, and the breadth-first closure over it makes the witness a shortest path that does not depend on hash order.

`cargo test` is **259** (sixteen new), `cargo clippy --workspace --all-targets -- -D warnings` and `cargo fmt --check` are clean.

### M3a acceptance

What M3a establishes: the rooted live set exists, as a proof object, with a hand-checkable witness for every live binding and a named reason for every dead one; the accounting closes exactly on all seven dumps; the old zero-reference subset is contained in it up to the root, with the predicate now living in exactly one place; and an independent walk that shares only the IR confirms every claim with 0 disagreements.

What M3a does **not** establish: that the dead set is right. 8,131 of the 9,831 dead verdicts on `-O1` are conditional on a linkage the dump cannot supply, and inspection of the `A5` population shows the gap severs whole modules the program certainly uses. M3b cannot consume this live set until the plugin's naming is fixed; what it *can* consume unconditionally is the live set as a **lower bound** — every binding M3a calls live really is reachable, because every edge behind it is either lexical binder identity or a stable-name match, and neither can invent a reference. What it would cost to fix, and why the fix is not in the tree yet, is [M3a′](#m3a--dump-post-coretidy-core-and-re-establish-whole-program-identity).

## M3a′ — dump post-CoreTidy Core and re-establish whole-program identity

*2026-09-15. **Halted at its own gate**, deliberately and with the evidence below. The resolver half is done, proven and committed; the plugin half is written, measured, and **not** committed, because measuring it is what showed it would destroy proof inputs M1–M2.4 depend on.*

### The defect

[M3a's `A5` finding](#the-finding-a5-in-world-missing-is-not-0) named it: `h2r-plugin` appends its pass at the end of `installCoreToDos`, which puts it immediately *before* the driver's own `CoreTidy` — and `CoreTidy` is where GHC decides which top-level names become external and rewrites the bindings. So a defining module's dump carries the pre-tidy name (`$_in$$wchecker` in `ShellCheck.Checks.Commands`, `format` in `ShellCheck.Formatter.TTY`) while every downstream module, which read the *tidied* `.hi`, refers to `…Checks.Commands$$wchecker` and `…TTY$format1`. On `-O1` that is **112 stable names over 1,232 occurrences** that name an in-world module and no top-level binding of it, and it is under every stable-name linkage in the compiler: `dictflow::Program::tops`, `classops::World::tops`, `higher`'s producer enumeration and `h2r-lower`'s `A3-EDGE-GLOBAL` index all build it.

### The resolver: lexical binding decides locality, not `isGlobalId`

`Module::resolve_scopes` refused a lexical hit when the occurrence's `isGlobal` bit was set. That was valid only for pre-tidy Core, where a module's own top-level binders are `LocalId`s. `tidyTopBind` rebuilds every top-level binder as a `GlobalId` — including the ones whose `Name` stays internal — so on a post-tidy dump the bit no longer separates an import from a module-local top-level binding.

- An in-scope binder now wins whatever the flag says; only an occurrence with **no in-scope binder at all** is `Ref::Global`.
- `isGlobal` stays in the JSON and in `Expr::Var` as a GHC diagnostic fact. It is no longer the local-vs-import identity decision, and the doc comments that said module-level binders are `LocalId`s all the way through are corrected.
- The test being removed was also what kept an *import* from being captured by a same-unique local binder, so that guard is re-established explicitly: an occurrence that resolves lexically although its **own stable name** is an external name of another module is a **unique collision** (`Module::unique_collisions`). It is stated on the name the occurrence already carries, against the module's own identity — nothing is keyed by a unique — and `h2r stats` prints the count on every dump, with the offending modules when it is not 0.
- `split_stable_name` / `is_external_name` / `is_internal_unit` moved to `h2r-core-ir`, where dump format 5's names live; `h2r-analysis` delegates, so the IR's collision guard and `dictflow`'s linkage index cannot drift.

**The compatibility proof.** On the *unchanged* `-O1` dump and the six unchanged matrix dumps, with the resolver changed:

|                                                                            |        |
| -------------------------------------------------------------------------- | -----: |
| reports captured on `core-json`, stdout and stderr apart                   |     94 |
| …byte-identical before and after                                           | **94** |
| matrix files (`stats`, `stats --per-module`, `lower --reachability` × A–F) |     24 |
| …byte-identical before and after                                           | **24** |
| unique collisions, on all seven existing dumps                             |  **0** |

The 94 are `stats` (+`--per-module`), `laziness`, `parsec`, `tuples` (+`--verify`, `--boundaries`), `fields`, `lists` (+`--axioms`), `text` (+`--heads`), `verify-rep`, `classops` (+`--per-module`), `dictflow`, `higher`, `verify-m24`, `m24`, `lower --reachability` (+`--rules`, `--m24-link`) and every `--json` / `--explain` form. This is what lets the change stay **format 5**: the new resolver reads the old dumps to the byte, so old and new dumps can coexist. The one line `h2r stats` gains — the collision count — is committed separately and is the only difference between the pre- and post-resolver captures.

Four new IR tests: an `isGlobal` occurrence with an in-scope binder is `Local`, without one is `Global`, a module's own top-level binding referenced by its post-tidy external name resolves lexically, and the collision guard fires on a synthetic import-captured-by-a-local.

### The plugin: written, measured, **not committed**

The change is small: in `dumpPass`, run `tidyProgram` ourselves and serialise `cg_binds` instead of `mg_binds`, returning the **original** `ModGuts` so the pipeline still sees its own tidy; and admit into `idTable` only referenced `GlobalId`s whose `Name` is external, because an internal stable string is not unique (M2.4h).

It is **not side-effect free and must not be described as if it were.** `tidyProgram` allocates names through the process-global name cache (`takeUniqFromNameCache` / `allocateGlobalBinder`), consuming uniques the driver's own later tidy would otherwise have had. Whether the external names it picks are the ones the driver reuses, and whether anything perturbed is confined to internal uniques, is an experiment, recorded below.

It also does more than rename: it trims bindings kept alive only by rules it cannot use, and it *injects implicit bindings* into `cg_binds`.

The patch is kept at `plugin-post-tidy.patch` in the M3a′ scratchpad. It is not in the tree, because of the gate.

### The gate: the `IdInfo` census

`GHC.Core.Tidy.tidyIdBndr` / `tidyLetBndr` and `GHC.Iface.Tidy.tidyTopIdInfo` rebuild every `IdInfo` from `vanillaIdInfo` and put back only some fields. Read from GHC 9.6.7's own source:

| binder class                | tidied by       | kept                                                                                        | **zapped**                                                        |
| --------------------------- | --------------- | ------------------------------------------------------------------------------------------- | ----------------------------------------------------------------- |
| top level, external name    | `tidyTopIdInfo` | arity, `dmd_sig`, CPR, occ-info (`zapFragileOcc`), inline pragma, unfolding                 | per-binder demand, call arity, rules                              |
| top level, internal name    | `tidyTopIdInfo` | arity, `dmd_sig`, CPR, minimal unfolding                                                    | **occ-info**, per-binder demand, call arity, inline pragma, rules |
| `let` / `letrec`            | `tidyLetBndr`   | occ-info, arity, `dmd_sig` (DmdEnv zapped), **per-binder demand**, inline pragma, unfolding | CPR, call arity, one-shot                                         |
| **lambda**                  | `tidyIdBndr`    | occ-info, **one-shot**, trimmed unfolding                                                   | **arity, `dmd_sig`, per-binder demand, CPR, `IdDetails`**         |
| **case binder, alt binder** | `tidyIdBndr`    | occ-info, trimmed unfolding                                                                 | **arity, `dmd_sig`, per-binder demand, CPR, `IdDetails`**         |

Measured, not inferred: one `-O1` extraction of all 28 modules emitted twice through the *same* emitter, once from `mg_binds` and once from `cg_binds`. Binders carrying a non-trivial value, pre-tidy → post-tidy:

| field                      |              top |             let |           lam |          case |           alt |
| -------------------------- | ---------------: | --------------: | ------------: | ------------: | ------------: |
| binders in the class       |    13828 → 13752 |     6156 → 6125 | 24202 → 23950 | 25076 → 24923 | 47078 → 46819 |
| `arity != 0`               |      3067 → 2994 |     2755 → 2738 |         0 → 0 |         0 → 0 |         0 → 0 |
| `dmdSig` non-empty         |      3179 → 3106 |     3182 → 2738 |         0 → 0 |         0 → 0 |         0 → 0 |
| `dmdSig` has a strict arg  |      2426 → 2363 |     1617 → 1608 |         0 → 0 |         0 → 0 |         0 → 0 |
| `dmdSig` has an absent arg |        195 → 194 |       410 → 410 |         0 → 0 |         0 → 0 |         0 → 0 |
| `dmdSig` diverges          |        132 → 132 |         25 → 25 |         0 → 0 |         0 → 0 |         0 → 0 |
| `cprSig` non-empty         |        581 → 547 |      38 → **0** |         0 → 0 |         0 → 0 |         0 → 0 |
| **`demand` strict**        |            0 → 0 |     1059 → 1044 |  **6026 → 0** |   **532 → 0** | **22956 → 0** |
| **`demand` absent**        |            0 → 0 |           0 → 0 |  **1515 → 0** | **21065 → 0** | **14344 → 0** |
| **`demand` usedOnce**      |            0 → 0 |       460 → 454 |  **9518 → 0** | **21890 → 0** | **29245 → 0** |
| **`demand` pretty ≠ `L`**  |      820 → **0** |     4114 → 4089 | **11544 → 0** | **21911 → 0** | **35170 → 0** |
| `occInfo` dead             |            0 → 0 |           0 → 0 |   1513 → 1511 | 20675 → 20546 |         0 → 0 |
| `occInfo` loopBreaker      |    691 → **250** |       874 → 865 |         0 → 0 |         0 → 0 |         0 → 0 |
| `oneShot`                  |           25 → 0 |         187 → 0 |   6119 → 6098 |         0 → 0 |         0 → 0 |
| `hasUnfolding`             |    13828 → 11792 | 5828 → **3245** |         0 → 0 | 24687 → 24530 |   5388 → 5377 |
| `isJoinPoint`              |            0 → 0 |     1119 → 1102 |         0 → 0 |         0 → 0 |         0 → 0 |
| `details` non-empty        |        945 → 848 |     1423 → 1327 |         0 → 0 |         0 → 0 |         4 → 4 |
| **`exported`**             | **1200 → 13752** |           0 → 0 |         0 → 0 |         0 → 0 |         0 → 0 |

The id table grows, as it should: 2,972 → 8,056 entries, `hasUnfolding` 2,043 → 7,103, `isClassOp` 56 → 56, `dataCon` 1,071 → 1,064. Those extra entries are the module's own externalised binders, and they are redundant rather than harmful — such an occurrence resolves `Ref::Local` and the binder is what signatures are read from.

**Verdict: the gate fires.** Three of the four zapped fields are read by M1–M2.4 proofs in exactly the binder classes tidy zaps them in:

| reader                                                                        | binder class                      | field                                                                 |
| ----------------------------------------------------------------------------- | --------------------------------- | --------------------------------------------------------------------- |
| `h2r-analysis/src/fields.rs` `demand_of` (M2.3b)                              | **alt binder**                    | `demand.strict` → `DemandHow::StrictByGhc`                            |
| `h2r-analysis/src/lists/mod.rs` `head_forced` (M2.3c)                         | **alt binder**                    | `demand.strict && !absent`                                            |
| `h2r-analysis/src/dictflow.rs:2267` (M2.4c)                                   | **lambda**                        | `demand.strict` under `BindSite::Lam`                                 |
| `h2r-analysis/src/classops.rs:960` (M2.4b)                                    | **lambda** (dictionary parameter) | `demand.strict` → `dict_known_strict`                                 |
| `h2r-analysis/src/dictflow.rs:1623` (M2.4c)                                   | **lambda** (dictionary parameter) | `demand.strict` → `Param::known_strict`                               |
| `h2r-analysis/src/{dictflow,higher,boundary,verify,verify_rep,verify_m24}.rs` | top level                         | `exported`, which post-tidy is `isGlobalId` and so **uniformly true** |

Run on the two dumps, the damage is what the census predicts:

| report                                             |         pre-tidy |      post-tidy |
| -------------------------------------------------- | ---------------: | -------------: |
| `fields`: observed / unobserved / escaped          | 1407 / 13 / 7746 | 191 / 1 / 8931 |
| `fields`: `Always` verdicts                        |              196 |             34 |
| `fields`: `Conditional` verdicts                   |              915 |            275 |
| `lists`: `SpineDemand::Unknown`                    |             5503 |           8895 |
| `lists`: `Whole`                                   |              141 |             62 |
| `lists`: `Prefix(DataDependent)`                   |              921 |            145 |
| `classops`: dictionary known strict at its binder  |              247 |              0 |
| `classops`: sites with a bounded instance set (≥1) |               10 |              0 |
| `dictflow`: `Exact(target)` class-op sites         |         7 (1.2%) |       0 (0.0%) |
| `laziness`: potential thunk sites                  |             2242 |           2228 |

`laziness` (M1) survives — its binders are `let` binders, where tidy keeps the demand. M2.3b, M2.3c, M2.4b and M2.4c do not.

**So the dumps were not regenerated.** Per the milestone's own rule, this is where it stops and hands the decision back.

### What the fix would buy, measured on a scratch dump

The post-tidy `-O1` dump was extracted and run through `lower --reachability` anyway, to price the decision:

|                                             |           pre-tidy (committed) |            post-tidy (scratch) |
| ------------------------------------------- | -----------------------------: | -----------------------------: |
| top-level bindings                          |                         13,828 |                         13,752 |
| live                                        |                          3,997 |                      **9,795** |
| dead, no references                         |                            976 |                            905 |
| dead, only dead referrers                   |                          8,855 |                          3,052 |
| share dead                                  |                          71.1% |                      **28.8%** |
| inter-module edges (`A3`)                   |                            498 |                      **1,288** |
| `A5-IN-WORLD-MISSING` names                 | **112** over 1,232 occurrences |                          **0** |
| in-world names GHC's flags explain          |     277 data cons, 3 class ops | 277 data cons, **0** class ops |
| zero-reference set, not dead and not a root |                              0 |                              0 |
| verifier claims / disagreements             |                    113,325 / 0 |                116,029 / **0** |
| `stats` unique collisions                   |                              0 |                          **0** |

Every module gains a nonzero live count. `ShellCheck.Checks.Commands` goes from 0 live to 1,184; `Checks.ShellSupport` from 0 to 870; `Analytics` from 489 to 2,646; `Formatter.TTY` from 0 to 87. The `STATUS — THE DEAD SET IS CONDITIONAL` block disappears.

The two pinned links resolve structurally, through the external-name index and not by any name heuristic:

```text
ShellCheck.Checks.Commands $wchecker  — LIVE, 5 hops
  Main$main [A1] → Main$main1 [A2] → Main $_in$poly_$j1 [A2]
  → ShellCheck.Checker$checkScript [A3] → ShellCheck.Analyzer$analyzeScript [A3]
  → ShellCheck.Checks.Commands$$wchecker [A3]

ShellCheck.Formatter.TTY format1  — LIVE, 4 hops
  Main$main [A1] → Main$main1 [A2] → Main $_in$poly_$j1 [A2]
  → Main $_in$formats [A2] → ShellCheck.Formatter.TTY$format1 [A3]
```

The 277 data-constructor names that remain non-bindings are correct and not a hole: GHC 9.6.7's `getTyConImplicitBinds` injects constructor *wrappers* only — workers are generated from the `TyCon` by codegen and are never Core bindings — so `A5`'s "explained by GHC's own flags" branch is still the right classification for them. The 3 class-op selectors *do* become real top-level bindings (top-level `IdDetails` `[ClassOp]`: 0 → 4).

Top-level bindings per module, pre-tidy → post-tidy, with the count whose stable name is external:

| module                            | binds             | external names  |
| --------------------------------- | ----------------- | --------------- |
| `Main`                            | 502 → 501         | 29 → 80         |
| `Paths_ShellCheck`                | 63 → 63           | 10 → 63         |
| `ShellCheck.AST`                  | 1083 → 1083       | 381 → 840       |
| `ShellCheck.ASTLib`               | 346 → 345         | 85 → 190        |
| `ShellCheck.Analytics`            | 2676 → 2667       | 15 → 991        |
| `ShellCheck.Analyzer`             | 8 → 8             | 3 → 8           |
| `ShellCheck.AnalyzerLib`          | 650 → 649         | 117 → 334       |
| `ShellCheck.CFG`                  | 1003 → 993        | 124 → 557       |
| `ShellCheck.CFGAnalysis`          | 895 → 867         | 145 → 490       |
| `ShellCheck.Checker`              | 36 → 36           | 2 → 6           |
| `ShellCheck.Checks.Commands`      | 1254 → 1240       | 13 → 65         |
| `ShellCheck.Checks.ControlFlow`   | 16 → 14           | 3 → 14          |
| `ShellCheck.Checks.Custom`        | 9 → 9             | 2 → 9           |
| `ShellCheck.Checks.ShellSupport`  | 906 → 901         | 7 → 134         |
| `ShellCheck.Data`                 | 1340 → 1340       | 20 → 1340       |
| `ShellCheck.Fixer`                | 92 → 96           | 15 → 63         |
| `ShellCheck.Formatter.CheckStyle` | 53 → 53           | 2 → 38          |
| `ShellCheck.Formatter.Diff`       | 156 → 155         | 12 → 33         |
| `ShellCheck.Formatter.Format`     | 62 → 62           | 17 → 44         |
| `ShellCheck.Formatter.GCC`        | 22 → 22           | 2 → 11          |
| `ShellCheck.Formatter.JSON`       | 69 → 66           | 5 → 38          |
| `ShellCheck.Formatter.JSON1`      | 91 → 88           | 9 → 56          |
| `ShellCheck.Formatter.Quiet`      | 11 → 11           | 2 → 11          |
| `ShellCheck.Formatter.TTY`        | 93 → 93           | 2 → 8           |
| `ShellCheck.Interface`            | 680 → 678         | 175 → 549       |
| `ShellCheck.Parser`               | 1645 → 1645       | 76 → 105        |
| `ShellCheck.Prelude`              | 42 → 42           | 7 → 16          |
| `ShellCheck.Regex`                | 25 → 25           | 8 → 13          |
| **total**                         | **13828 → 13752** | **1288 → 6106** |

`ShellCheck.Fixer` is the only module that gains bindings net (92 → 96): implicit bindings injected. Everywhere else the trimming of rule-only-live bindings dominates. The net is **−76**. Injected and trimmed were not separated exactly — `getImplicitBinds` is not exported from `GHC.Iface.Tidy`, and a name-level before/after is meaningless because tidy is what invents the names (`$c==` → `$fEqStatus_$c==`).

### The transparency experiment

Three `-O1` builds of the stripped ShellCheck tree from the same sources: **(a)** no plugin at all, **(b)** the plugin as committed, **(c)** the post-tidy plugin.

|                                             | result                                                                                                                                                                                                                                                                                                                  |
| ------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| interface surface, (b) vs (c)               | **identical** except 27 `addDependentFile` lines naming the plugin's own `.so` (different path, different content) and the 27 `interface hash:` values that follow from them. **`ABI hash` and `export-list hash` are unchanged on every one of the 27 modules.**                                                       |
| interface surface, (a) vs (b)               | differs only in the same kind of bookkeeping: `plugin package dependencies`, the plugin `.so` `addDependentFile` lines, `trusted package dependencies`, and the hashes that follow.                                                                                                                                     |
| executable behaviour                        | **identical**, all three. 117 invocations — every `*.sh` in the repo (3 files) plus 12 inline cases exercising the parser, analytics and the fixer, each through `-f tty/json/json1/gcc/checkstyle/diff/quiet`, plus `--version` and `--help`; output **and** exit codes compared. 710 lines of output, byte-identical. |
| deterministic repeat extraction, plugin (c) | **byte-identical** across two independent build trees and two process runs, all 28 dumps; the two binaries also hash the same.                                                                                                                                                                                          |
| deterministic repeat extraction, plugin (b) | the re-extraction reproduced the committed `compiler/core-json` **to the byte**, and its binary hash equals the one in `compiler/matrix/A/provenance`.                                                                                                                                                                  |
| `shellcheck` binary sha256                  | (a) `1c2e2f59…`, (b) `38905705…`, (c) `192b82c8…` — **all three differ.**                                                                                                                                                                                                                                               |
| module `.o` sha256                          | 20 of the 27 differ between (a) and (b), and **the same 20** between (b) and (c).                                                                                                                                                                                                                                       |

The binaries and objects **do** move, and (a) vs (b) shows a plugin that touches nothing moves them too — so the move is not evidence about the extra tidy on its own. What can be said about where it lands, from `nm`: of the **8,793** defined symbols across the 27 objects, **every one is identical in all three builds**, byte for byte in name and section. The only differing symbols are the 294 `<unique>_str` string-literal symbols and the local `.Lr<unique>_bytes` labels — symbols whose *names are internal uniques*. That is consistent with, and only with, internal-unique perturbation.

What could not be determined: whether the `.o` bytes differ *only* in those symbol names and the relocations that follow them. `nm` shows the symbol tables agree; a byte-level attribution of the remaining object diff to those labels alone was not carried out, and a full `objdump` comparison of 27 objects is the work that would settle it.

### Where this leaves the milestone, and the options

Committed and proven: the resolver, the collision guard, `stats`'s report of it, and the byte-identity of all 118 captured report files on the seven existing dumps. The Rust side reads both the old dumps and post-tidy dumps, which is what Step 1 was for, and it is still **format 5**.

Not committed: the plugin. Regenerating the dumps under it would silently take `demand` off every lambda, case and alternative binder, and M2.3b, M2.3c, M2.4b and M2.4c read it there.

The options, for whoever picks this up:

1. **Join the pre-tidy `IdInfo` onto the tidied binder inside the pass.** `tidyIdBndr` and `tidyLetBndr` both rebuild the name as `mkInternalName (idUnique id) occ'` — **nested binders keep their unique** — so the join is exact for the three classes that lose anything. Top-level binders do **not**: `tidyTopName` takes a fresh unique from the name cache for every local name, external or internal. So the join has to be a lockstep structural walk of `mg_binds` and `cg_binds`, with the top-level pairs aligned first (the sequence of nested binder uniques inside a right-hand side is a fingerprint that survives tidying exactly, and implicit bindings have no pre-tidy counterpart while trimmed ones have no tidied one). Legitimate — it is all inside one compilation of one module — and it keeps every M1–M2.4 input while giving M3 the tidied names, the implicit bindings and the trimming. The most work; the only option that loses nothing.
2. **Emit the tidied program *structure* with pre-tidy `IdInfo` throughout**, i.e. the same lockstep walk but resolved the other way: serialise `mg_binds`, with each top-level binder's `name` replaced by the name `CoreTidy` gave it. Closes the linkage hole exactly and changes no `IdInfo` at all, so every M1–M2.4 report stays byte-identical by construction. Gives up the implicit bindings and the trimming, so the dump is not the program GHC hands to codegen.
3. **Emit both programs**, `<Module>.core.json` unchanged plus `<Module>.tidy.core.json`. Trivially safe, and trivially two programs; M3b would have to say which one it lowers.
4. **Accept the loss.** Not viable: the demand on an alternative binder is GHC's demand analysis, and nothing on the Rust side can recompute it.

Nothing in `h2r-analysis` changed; the resolver change forced no semantic change there, as expected. The M1–M2.4 numbers in this document are untouched and remain correct for the dumps in the tree.

*At this point, the M1–M2.4 baseline on the new dumps had to wait for a choice among these options and regeneration of the dumps. The following section records that choice.*

### 2026-09-15, continued — the decision: option 1, and what it became

Option 1 was chosen: **join the pre-tidy facts onto the tidied program.** The other three were refused for the reasons the table above gives — option 2 gives up the implicit bindings and the trimming, so the dump is not the program GHC hands to codegen; option 3 ships two programs and makes M3b pick; option 4 throws away GHC's demand analysis, which nothing on the Rust side can recompute.

It did not stay a whole-`IdInfo` transplant. `tidyTopIdInfo` does real finalisation — the arity codegen relies on, the final demand and CPR signatures, the robustified occurrence info, the unfolding that reaches the interface — and `tidyCbvInfoTop` / `tidyCbvInfoLocal` put the call-by-value marks onto the `IdDetails` codegen reads. Overwriting all of that with the pre-tidy `IdInfo` would undo genuine codegen-facing work and make the dump *less* the program GHC compiles. So the join is **field-level, with a stated owner per field**, and it supplies only what CoreTidy discards.

### The provenance contract

| field                                                                                                                | top     | let     | lam     | case    | alt     | why                                                                                                                                                                                                                                                                                                                                 |
| -------------------------------------------------------------------------------------------------------------------- | ------- | ------- | ------- | ------- | ------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `demand`                                                                                                             | **pre** | post    | **pre** | **pre** | **pre** | `tidyIdBndr` rebuilds lambda/case/alt binders from `vanillaIdInfo` (`Core/Tidy.hs:305-308`, which sets only occ-info, the unfolding and one-shot); `tidyTopIdInfo`'s setter list has no `setDemandInfo` (`Iface/Tidy.hs:1225-1241`). `tidyLetBndr` **does** keep it (`Core/Tidy.hs:356`), so a `let` binder's demand is CoreTidy's. |
| `oneShot`                                                                                                            | **pre** | **pre** | post    | post    | post    | Neither `tidyTopIdInfo` nor `tidyLetBndr` puts it back; `tidyIdBndr` sets it explicitly for lambda binders (`Core/Tidy.hs:308`, *Note [Preserve OneShotInfo]*), which is the only class a reader uses it on.                                                                                                                        |
| `exported`                                                                                                           | **pre** | post    | post    | post    | post    | Post-tidy every top-level binder is a `GlobalId`, so `isExportedId` is uniformly `True` and carries no information. Nested binders are `False` on both sides.                                                                                                                                                                       |
| `arity`, `callArity`, `dmdSig`, `cprSig`, `occInfo`, `details`, `hasUnfolding`, `isJoinPoint`, `isDataCon`, the type | post    | post    | post    | post    | post    | CoreTidy finalises these, and the finalised value is the one the compiled program has.                                                                                                                                                                                                                                              |

Which reader needs which joined field, named rather than asserted:

| field                      | binder class                   | reader                                                                                                      | milestone |
| -------------------------- | ------------------------------ | ----------------------------------------------------------------------------------------------------------- | --------- |
| `demand.strict`            | alternative binder             | `h2r-analysis/src/fields.rs:883` (`demand_of`)                                                              | M2.3b     |
| `demand.strict && !absent` | alternative binder             | `h2r-analysis/src/lists/mod.rs:1359` (`head_forced`)                                                        | M2.3c     |
| `demand.strict`            | lambda binder                  | `h2r-analysis/src/dictflow.rs:2267`                                                                         | M2.4c     |
| `demand.strict`            | lambda (dictionary parameter)  | `h2r-analysis/src/classops.rs:960` (`dict_known_strict`)                                                    | M2.4b     |
| `demand.strict`            | lambda (dictionary parameter)  | `h2r-analysis/src/dictflow.rs:1623` (`Param::known_strict`)                                                 | M2.4c     |
| `exported`                 | top level                      | `dictflow`, `higher`, `boundary`, `flow`, `m24`, `tuples`, `classops`, `verify`, `verify_rep`, `verify_m24` | M2.2–M2.4 |
| `one_shot`                 | **lambda** — taken *post*-tidy | `h2r-analysis/src/laziness.rs:421` (`transparent_lambda`)                                                   | M1        |

Two fields CoreTidy drops are deliberately **not** joined, because the search for readers found none: `cprSig` on a `let` binder (`tidyLetBndr` has no `setCprSigInfo`; 38 binders in the `-O1` world) and `callArity` (dropped everywhere, and 0 on every binder of every class in the `-O1` world). Their only consumer is a `h2r stats` census column, which is a report, not a proof. If a later milestone needs either, the join is one line per field.

### `exported`, and the fact the milestone brief expected that is not true

The brief proposed redefining `exported` as membership of the tidied `Name` in `availsToNameSet (mg_exports guts)`, expecting it to agree with the pre-tidy `isExportedId`. **It does not**, and the plugin measures the gap on every module. Over the `-O1` world:

|                                                                                       |      |
| ------------------------------------------------------------------------------------- | ---: |
| aligned top-level binders with pre-tidy `isExportedId` — the **emitted** `exported`   | 1200 |
| …in `availsToNameSet (mg_exports)` — emitted as `sourceExported`                      |  342 |
| …disagreements                                                                        |  858 |
| aligned top-level binders whose tidied `Name` is external — emitted as `externalName` | 6102 |

1200 − 342 = 858 exactly, so the source export list is a **strict subset** of the compiler's export flag. The desugarer marks as exported everything that must survive to the interface, not only what the module's export list names: dfuns (`$fClassyFoo`), `Typeable` bindings (`$trModule`, `$tcFoo`, `$tc'Foo`), class default methods (`$dmclassy`). All of those *are* referable from another module, so `isExportedId` is the fact the analyses want, and it is the fact the pre-tidy dumps carried. `exported` therefore keeps its meaning and its value, and the two narrower facts are emitted beside it as diagnostics that **nothing reads in this milestone**. An implicit binding has no pre-tidy binder to read `exported` from, and post-tidy `isExportedId` would say `True` for all of them, so those — the four in `ShellCheck.Fixer`, and only those — take `sourceExported`.

### The three GHC facts the join rests on, with their source lines

Read from GHC 9.6.7's own source, and cited in the plugin at the call site:

**(a) `tidyExpr` is structure-preserving.** `GHC/Core/Tidy.hs:207-233`: `Var`, `Lit`, `App`, `Lam`, `Let`, `Case`, `Cast`, `Tick`, `Type` and `Coercion` each map to the same constructor; `tidyAlt` (`:230-233`) rebuilds an `Alt` with the same `AltCon` and the same number of binders; and `map (tidyAlt env') alts` (`:223`) keeps the alternatives in order. A pre-tidy right-hand side and its tidied counterpart are the same tree, node for node.

**(b) Nested binders keep their `Unique`; top-level binders do not.** `tidyIdBndr` (`Core/Tidy.hs:300`) and `tidyLetBndr` (`Core/Tidy.hs:326`) both build `mkInternalName (idUnique id) occ' noSrcSpan` — the print name is freshened, the unique is the old one; `tidyVarBndr` does the same for type and coercion variables. At the top level `tidyTopName` (`Iface/Tidy.hs:1069-1093`) takes a **fresh** unique from the name cache for every name that was local: `takeUniqFromNameCache` (`:1084`) when it stays internal, `allocateGlobalBinder` (`:1092`) when it is externalised. Only names that were **already** global keep theirs (`:1073-1074`) — which is why an import occurrence is literally the same `Var` before and after. The plugin checks that on every aligned pair: **44,858 import occurrences agree in name and unique, 0 disagree.**

**(c) Order is preserved end to end; the implicit bindings are a prefix; a trimmed binding never has an exported binder.** ``tidyProgram`` (``Iface/Tidy.hs:381-387``) builds ``all_binds = implicit_binds ++ binds``, where ``implicit_binds = concatMap getImplicitBinds tcs`` (``:381``). ``getImplicitBinds`` (``:611-626``) yields exactly the class selectors (``getClassImplicitBinds``, ``ClassOpId``) and the data constructor **wrappers** (``getTyConImplicitBinds``, ``DataConWrapId``) — constructor *workers* are never Core bindings, which is why M3a's "277 data-constructor names explained by GHC's own flags" is still the right classification for them. ``findExternalRules`` (``:976-1050``) then filters that list with ``trim_binds``, which keeps a ``CoreBind`` group **whole** when ``any needed bndrs`` and discards it **whole** otherwise (``:1039-1045``), where ``needed bndr = isExportedId bndr || bndr \``elemVarSet\` needed_fvs`` (``:1046``). ``tidyTopBinds``is``mapAccumL tidyTopBind`` (``:1165``) — one tidied group per input group, in order — and ``tidyTopBind``keeps``NonRec``/``Rec``and the order of a``Rec`` group's pairs (``:1174-1190``). The only later insertion is ``sptCreateStaticBinds`` (``:390-392``), which runs only when ``StaticPointers`` is on (``Driver/Config/Tidy.hs:33-35``); the pass reads ``opt_static_ptr_opts` and records that it is **off on all 28 modules**, so the SPT column is 0 by construction and not by hope.

### The alignment theorem, asserted at extraction time

From (c) the alignment is a two-pointer merge over `mg_binds` and `cg_binds` in order. Order alone would leave "we took the first structural match" as the justification, so uniqueness is proved a **second time, independently of order**, with a fingerprint CoreTidy preserves exactly: the expression-constructor tree, every nested binder's `Unique`, every literal, every `AltCon`, and the stable name of every occurrence of an import or of one of the implicit ids. An occurrence of one of the module's *own* top-level bindings is the one thing that cannot be fingerprinted directly — tidy reallocates its unique and may rename it — so it is a **hole**, closed by partition refinement: every binding starts with one colour, each round re-fingerprints with the previous round's colours in the holes, and the rounds stop when the partition stops splitting. Both programs are coloured **together**, in one shared numbering, so a colour means the same thing on both sides of the tidy. Colours are 64-bit FNV-1a hashes; a collision can only *merge* two colours, which surfaces as a tie and is then resolved below — it can never make two different structures look aligned, because the lockstep zip is what admits a pair.

What the pass asserts, per module, and aborts the extraction on:

1. every aligned tidied binding has **exactly one** pre-tidy binding of the same refined fingerprint — **13,499 of 13,660** — or, where several pre-tidy bindings are structurally indistinguishable, **all of them carry the same joined facts**, so which one the merge picked cannot change a byte — **161 of 161 ties are vacuous in that sense.** A tie that is not vacuous aborts.
2. every aligned pair passes a **strict lockstep zip** of the two trees before any field is merged: node for node, alternative for alternative, `AltCon` for `AltCon`, binder for binder with equal uniques. A mismatch aborts, naming the module and the binding.
3. every unmatched pre-tidy group is a `trim_binds` trim and **has no exported binder** (`Iface/Tidy.hs:1046`). A counter-example aborts. There were none.
4. every unmatched tidied group is a `getImplicitBinds` injection, identified by `IdDetails` (`ClassOpId` / `DataConWrapId`), never by a name. Anything else aborts, and the log records that SPT insertion was impossible.
5. the implicit bindings are a prefix of the tidied program, as (c) says.

Nothing is keyed by a unique across the module: uniques are not unique in optimised Core, and two copies of one binder can carry different demands. The zip is positional inside one aligned pair, and the fingerprint is compared whole.

Each module's counts go to `compiler/core-json/<Module>.tidy-align.txt` beside its dump (136 KB for all 28), and a one-line summary to stderr during the build. The Rust loader reads `*.core.json` only (`h2r_core_ir::load_dir`), so the sidecar is inert.

### The alignment, per module

Groups are `CoreBind`s — a recursive group is one — and `bOut`/`bTrim` are top-level *binders*, which is what the dump's top-level pair count is.

| module                            |   aligned | implicit | trimmed |   spt | unique FP |    tied | vacuous |      bOut |  bTrim | `exported` | `sourceExported` | `externalName` |
| --------------------------------- | --------: | -------: | ------: | ----: | --------: | ------: | ------: | --------: | -----: | ---------: | ---------------: | -------------: |
| `Main`                            |       500 |        0 |       1 |     0 |       487 |      13 |      13 |       501 |      1 |         24 |                1 |             80 |
| `Paths_ShellCheck`                |        63 |        0 |       0 |     0 |        63 |       0 |       0 |        63 |      0 |          9 |                8 |             63 |
| `ShellCheck.AST`                  |      1067 |        0 |       0 |     0 |      1063 |       4 |       4 |      1083 |      0 |        381 |                6 |            840 |
| `ShellCheck.ASTLib`               |       328 |        0 |       1 |     0 |       319 |       9 |       9 |       345 |      1 |         85 |               78 |            190 |
| `ShellCheck.Analytics`            |      2659 |        0 |       9 |     0 |      2632 |      27 |      27 |      2667 |      9 |          8 |                2 |            991 |
| `ShellCheck.Analyzer`             |         8 |        0 |       0 |     0 |         8 |       0 |       0 |         8 |      0 |          3 |                2 |              8 |
| `ShellCheck.AnalyzerLib`          |       648 |        0 |       1 |     0 |       645 |       3 |       3 |       649 |      1 |        117 |               81 |            334 |
| `ShellCheck.CFG`                  |       973 |        0 |      10 |     0 |       930 |      43 |      43 |       993 |     10 |        121 |                7 |            557 |
| `ShellCheck.CFGAnalysis`          |       866 |        0 |      28 |     0 |       853 |      13 |      13 |       867 |     28 |        124 |               19 |            490 |
| `ShellCheck.Checker`              |        36 |        0 |       0 |     0 |        36 |       0 |       0 |        36 |      0 |          2 |                1 |              6 |
| `ShellCheck.Checks.Commands`      |      1238 |        0 |      14 |     0 |      1232 |       6 |       6 |      1240 |     14 |         10 |                2 |             65 |
| `ShellCheck.Checks.ControlFlow`   |        14 |        0 |       2 |     0 |        14 |       0 |       0 |        14 |      2 |          3 |                2 |             14 |
| `ShellCheck.Checks.Custom`        |         9 |        0 |       0 |     0 |         7 |       2 |       2 |         9 |      0 |          2 |                1 |              9 |
| `ShellCheck.Checks.ShellSupport`  |       901 |        0 |       5 |     0 |       895 |       6 |       6 |       901 |      5 |          4 |                1 |            134 |
| `ShellCheck.Data`                 |      1340 |        0 |       0 |     0 |      1340 |       0 |       0 |      1340 |      0 |         20 |               19 |           1340 |
| `ShellCheck.Fixer`                |        91 |    **4** |       0 |     0 |        91 |       0 |       0 |        96 |      0 |         15 |                3 |             59 |
| `ShellCheck.Formatter.CheckStyle` |        53 |        0 |       0 |     0 |        53 |       0 |       0 |        53 |      0 |          2 |                1 |             38 |
| `ShellCheck.Formatter.Diff`       |       154 |        0 |       1 |     0 |       154 |       0 |       0 |       155 |      1 |          9 |                1 |             33 |
| `ShellCheck.Formatter.Format`     |        62 |        0 |       0 |     0 |        62 |       0 |       0 |        62 |      0 |         17 |               14 |             44 |
| `ShellCheck.Formatter.GCC`        |        22 |        0 |       0 |     0 |        22 |       0 |       0 |        22 |      0 |          2 |                1 |             11 |
| `ShellCheck.Formatter.JSON`       |        66 |        0 |       3 |     0 |        63 |       3 |       3 |        66 |      3 |          5 |                1 |             38 |
| `ShellCheck.Formatter.JSON1`      |        88 |        0 |       3 |     0 |        84 |       4 |       4 |        88 |      3 |          9 |                1 |             56 |
| `ShellCheck.Formatter.Quiet`      |        11 |        0 |       0 |     0 |        11 |       0 |       0 |        11 |      0 |          2 |                1 |             11 |
| `ShellCheck.Formatter.TTY`        |        93 |        0 |       0 |     0 |        93 |       0 |       0 |        93 |      0 |          2 |                1 |              8 |
| `ShellCheck.Interface`            |       678 |        0 |       2 |     0 |       674 |       4 |       4 |       678 |      2 |        175 |               74 |            549 |
| `ShellCheck.Parser`               |      1625 |        0 |       0 |     0 |      1601 |      24 |      24 |      1645 |      0 |         34 |                1 |            105 |
| `ShellCheck.Prelude`              |        42 |        0 |       0 |     0 |        42 |       0 |       0 |        42 |      0 |          7 |                6 |             16 |
| `ShellCheck.Regex`                |        25 |        0 |       0 |     0 |        25 |       0 |       0 |        25 |      0 |          8 |                7 |             13 |
| **TOTAL**                         | **13660** |    **4** |  **80** | **0** | **13499** | **161** | **161** | **13752** | **80** |   **1200** |          **342** |       **6102** |

**The net −76 explained rather than observed.** 13,828 pre-tidy top-level binders = 13,748 aligned + 80 trimmed; 13,752 emitted = 13,748 aligned + 4 implicit. Every one of the 80 is named in its module's sidecar, and they are overwhelmingly auto-specialisations that nothing but an auto-generated rule kept alive, which is exactly *Note [Trimming auto-rules]*: `$sinsert`, `$ssplit`, `$sinsertR`, `$sfromListWithKey`, `$ssplitS`, `$s$wsplit`, `$s$fMonadRWST1`, `$ssequence__c`, `$s$cshow`, `$s$cshowsPrec`, `$s$fMonadStateT1`, `$s$w$c<*>`, `$snew`, `$sunstream`, `$snewSystemInterface`, plus a handful of `lvl_`, `go4_`, `poly_go15_` and `$wgo1_` bindings that were only reachable from them. The 4 implicit bindings are `ShellCheck.Fixer`'s `Range` class selectors — `start`, `end`, `overlap`, `setRange` — all `[ClassOp]`, all in that module's export list.

### The three-column census, with the owning side named

`pre` is the pre-tidy program, `post-raw` the tidied program with no join, `joined` what the dump now carries. All three were emitted **from one compilation process through one emitter**, so there is no internal-unique confound between the columns.

The invariant is checked per binder, not by these totals: over all 28 modules, **115,537 aligned binders, every field equal to its owning side's value, 0 violations.** (The dump has 115,569 binders; the other 32 belong to the four implicit bindings, which have no pre-tidy counterpart and read everything from themselves.) The totals below then differ from the owning column only by population, and the population differs only by the 80 trimmed binders (−) and the 4 implicit ones (+).

| binder class |   pre | post-raw | joined |
| ------------ | ----: | -------: | -----: |
| top          | 13828 |    13752 |  13752 |
| let          |  6156 |     6125 |   6125 |
| lam          | 24202 |    23950 |  23950 |
| case         | 25076 |    24923 |  24923 |
| alt          | 47078 |    46819 |  46819 |

Only the rows where `joined` is not literally equal to the owning column are listed; every other row is equal to the byte, and the full table is in the scratchpad. Each difference here is a *population* difference, attributed:

| field                | class |   pre | post-raw | joined | owner | difference                                      |
| -------------------- | ----- | ----: | -------: | -----: | ----- | ----------------------------------------------- |
| `demand absent`      | lam   |  1515 |        0 |   1513 | pre   | −2 trimmed                                      |
| `demand absent`      | case  | 21065 |        0 |  20936 | pre   | −129 trimmed                                    |
| `demand absent`      | alt   | 14344 |        0 |  14282 | pre   | −62 trimmed                                     |
| `demand pretty != L` | top   |   820 |        0 |    818 | pre   | −2 trimmed                                      |
| `demand pretty != L` | lam   | 11544 |        0 |  11386 | pre   | −158 trimmed                                    |
| `demand pretty != L` | case  | 21911 |        0 |  21776 | pre   | −135 trimmed                                    |
| `demand pretty != L` | alt   | 35170 |        0 |  35015 | pre   | −155 trimmed                                    |
| `demand strict`      | lam   |  6026 |        0 |   5900 | pre   | −126 trimmed                                    |
| `demand strict`      | alt   | 22956 |        0 |  22872 | pre   | −84 trimmed                                     |
| `demand usedOnce`    | lam   |  9518 |        0 |   9382 | pre   | −136 trimmed                                    |
| `demand usedOnce`    | case  | 21890 |        0 |  21755 | pre   | −135 trimmed                                    |
| `demand usedOnce`    | alt   | 29245 |        0 |  29107 | pre   | −138 trimmed                                    |
| `exported`           | top   |  1200 |      346 |   1204 | pre   | +4 implicit (all four in `Fixer`'s export list) |

`demand strict` on a **case** binder is 532 in all three of pre, post-raw's would-be value and joined, because none of the trimmed bindings held one; `oneShot` on **top** (25) and **let** (187) is likewise unchanged by the trimming. The rows the join does **not** own are equal to `post-raw` to the digit, including the ones where CoreTidy's value differs sharply from the pre-tidy one and that is deliberate: `hasUnfolding` on a `let` binder (5828 → 3245 — CoreTidy decided what the interface exposes), `occInfo loopBreaker` at top level (691 → 250 — `zapFragileOcc`), `details` (945 → 848 at top, 1423 → 1327 in lets — the CBV marks), `dmdSig pretty non-empty` in lets (3182 → 2738 — `zapDmdEnvSig` drops the demand environment while keeping every argument demand: `dmdSig with >=1 arg demand` is 2755 → 2738, which is the trimming alone), and `cprSig` in lets (38 → 0, not joined because no analysis reads it).

The **pair-level shape facts** (`whnf`, `trivial`, `cheap`, `okForSpec`) and the whole **id table** are computed from the tidied program by design, and are equal to `post-raw` exactly: pairs 13752/6125, `whnf` 10997/3399, `cheap` 11109/3758, `okForSpec` 11035/3631, `trivial` 54/0; id table 2972 → **8056** entries, `hasUnfolding` 2043 → 7103, `dataCon` 1071 → 1064, `isClassOp` 56 → 56.

### Dump format 6

The dump's *semantic contract* changed, not only its content, so the number changed with it. Format 5 was the program **before** `CoreTidy`; format 6 is the program **after** it — the one GHC hands to codegen. Field names and shapes are format 5's; what a consumer may conclude from them is not.

|                                                                                                                   | format 5                                                  | format 6                                                                                                           |
| ----------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| top-level names                                                                                                   | pre-tidy: a binding can carry a name no other module uses | CoreTidy's: a stable name links across modules                                                                     |
| top-level binder `isGlobalId`                                                                                     | `False` (module-local binders are `LocalId`s)             | `True` for all of them — which is why the resolver decides locality lexically (see above)                          |
| population                                                                                                        | `mg_binds`                                                | `cg_binds`: the implicit class-op selectors and constructor wrappers injected, the rule-only-live bindings trimmed |
| `ids` (id table)                                                                                                  | every referenced `GlobalId`                               | only those with an **external** `Name` — an internal stable string is not unique (M2.4h)                           |
| `demand`                                                                                                          | GHC's, everywhere                                         | GHC's, everywhere — joined back on top/lam/case/alt, CoreTidy's on lets                                            |
| `oneShot`                                                                                                         | GHC's, everywhere                                         | joined back on top/let, CoreTidy's on lambdas                                                                      |
| `exported`                                                                                                        | `isExportedId`                                            | `isExportedId`, unchanged in meaning and value (implicit bindings: the source export list)                         |
| `arity`, `callArity`, `dmdSig`, `cprSig`, `occInfo`, `details`, `hasUnfolding`, `isJoinPoint`, `isDataCon`, types | pre-tidy                                                  | **CoreTidy's finalised values**                                                                                    |
| `whnf` / `trivial` / `cheap` / `okForSpec`                                                                        | on the pre-tidy RHS                                       | on the tidied RHS                                                                                                  |
| `externalName`, `sourceExported`                                                                                  | —                                                         | **new**, top-level binders only, **diagnostics**; nothing reads them                                               |
| structured types, hash-consed `types` table, stable-name keys                                                     | yes                                                       | yes, unchanged                                                                                                     |

`h2r-core-ir` loads **both**: `raw::FORMATS_ACCEPTED = [5, 6]`, the number is recorded on `Module::format`, `h2r stats` prints it, and **no analysis branches on it**. That is what keeps the old format-5 dumps in the scratchpad readable, which is what makes the compatibility check below possible. Any other number is refused, as before.

The plugin's `ghc` bound is now `>= 9.6 && < 9.7`: the join rests on documented GHC 9.6.7 internals, cited by line and asserted per module at extraction time. A different series has to be re-read and re-proved, not assumed. There are no version-specific branches in the plugin.

### The seven dumps, regenerated

`-O1` was extracted **twice more, in independent build trees and separate process runs**, and all 28 dumps — and all 28 alignment sidecars — are **byte-identical** across them. (Three runs in all, counting the first: 0 differing files in every pairing.) `compiler/matrix/A` is a fourth, independent `-O1` extraction and its reachability report is identical to `compiler/core-json`'s line for line.

| profile     | top           | live            | dead (0-ref) | dead (only-dead) | % dead          | inter-module edges | `A5` names  | `A5` occurrences | verifier claims / disagreements |
| ----------- | ------------- | --------------- | ------------ | ---------------- | --------------- | ------------------ | ----------- | ---------------- | ------------------------------- |
| **A** `-O1` | 13828 → 13752 | 3997 → **9795** | 976 → 905    | 8855 → 3052      | 71.1 → **28.8** | 498 → **1288**     | 112 → **0** | 1232 → **0**     | 113325/0 → 116029/0             |
| **B** `-O2` | 13957 → 13867 | 3525 → **9894** | 1000 → 921   | 9432 → 3052      | 74.7 → **28.7** | 490 → **1317**     | 125 → **0** | 1376 → **0**     | 115720/0 → 118510/0             |
| **C**       | 6073 → 6035   | 1260 → **2759** | 930 → 893    | 3883 → 2383      | 79.3 → **54.3** | 487 → **816**      | 83 → **0**  | 659 → **0**      | 50133/0 → 51433/0               |
| **D**       | 7209 → 6889   | 1484 → **3082** | 1057 → 921   | 4668 → 2886      | 79.4 → **55.3** | 635 → **1084**     | 109 → **0** | 1793 → **0**     | 64002/0 → 63668/0               |
| **E**       | 7209 → 6889   | 1484 → **3082** | 1057 → 921   | 4668 → 2886      | 79.4 → **55.3** | 635 → **1084**     | 109 → **0** | 1451 → **0**     | 63582/0 → 63077/0               |
| **F**       | 7197 → 6879   | 1482 → **3078** | 1055 → 921   | 4660 → 2880      | 79.4 → **55.3** | 642 → **1085**     | 109 → **0** | 1433 → **0**     | 63479/0 → 62977/0               |

`A5-IN-WORLD-MISSING` is **0 on all seven dumps**, which was the gate. `STATUS — THE DEAD SET IS CONDITIONAL` therefore does not print on any of them; the check is still there and the report now says, in one line, `A5-IN-WORLD-MISSING 0: the dead set is unconditional`. `A11-MISSING-IMPACT` is untouched and prints nothing when there is no hole. On `-O1` the remaining in-world non-bindings are **277 data-constructor names over 3827 occurrences and 0 class-op selectors** — the class-op selectors are now real top-level bindings, and constructor *workers* never were Core bindings at all (fact (c)).

Every module now has a nonzero live count. The ones that had none:

| module                                                                            | live, old → new                |
| --------------------------------------------------------------------------------- | ------------------------------ |
| `ShellCheck.Checks.Commands`                                                      | 0 → 1184                       |
| `ShellCheck.Checks.ShellSupport`                                                  | 0 → 870                        |
| `ShellCheck.CFG`                                                                  | 0 → 355                        |
| `ShellCheck.CFGAnalysis`                                                          | 0 → 292                        |
| `ShellCheck.Formatter.Diff`                                                       | 0 → 106                        |
| `ShellCheck.Formatter.TTY`                                                        | 0 → 87                         |
| `ShellCheck.Formatter.JSON1` / `JSON` / `CheckStyle` / `GCC` / `Format` / `Quiet` | 0 → 48 / 44 / 47 / 16 / 19 / 4 |
| `ShellCheck.Fixer`                                                                | 0 → 30                         |
| `ShellCheck.Prelude`                                                              | 0 → 29                         |
| `ShellCheck.Analytics`                                                            | 489 → 2646                     |
| `ShellCheck.Interface`                                                            | 1 → 30                         |

### The two pinned links, and `lower --link`

`LiveSet::link` answers, for one **external** stable name: the single top-level binding that defines it, found through the external-name index and never by a name heuristic; every binding that refers to it, grouped by module and by the rule that made the edge; and its shortest witness chain from `Main.main`. The fact lives in the proof object so it can be tested; `h2r lower --reachability --link <stable name>` prints it. An internal name is **refused with the reason**, not answered — internal stable strings are not unique, so there is no single binding to point at.

```sh
$ h2r lower --reachability compiler/core-json \
      --link '$ShellCheck-0.11.0-inplace$ShellCheck.Checks.Commands$$wchecker'

  defined by exactly one top-level binding [A12-EXTERNAL-UNIQUE]
    module ShellCheck.Checks.Commands   binder #1238   occ $wchecker
    the name is external, so another module can name it [A3-EDGE-GLOBAL]

  referenced by 2 top-level binding(s) over 2 occurrence(s), in 2 module(s)
         1 occ over    1 binding(s)  ShellCheck.Analyzer         [A3-EDGE-GLOBAL]
         1 occ over    1 binding(s)  ShellCheck.Checks.Commands  [A2-EDGE-LOCAL]

  LIVE — witness [A9-WITNESS], 5 hop(s) from the root
      0. Main                        $…-shellcheck$Main$main            [A1-ROOT-MAIN]
      1. Main                        $…-shellcheck$Main$main1           [A2-EDGE-LOCAL]
      2. Main                        $_in$poly_$j1#485                  [A2-EDGE-LOCAL]
      3. ShellCheck.Checker          $…$ShellCheck.Checker$checkScript  [A3-EDGE-GLOBAL]
      4. ShellCheck.Analyzer         $…$ShellCheck.Analyzer$analyzeScript [A3-EDGE-GLOBAL]
      5. ShellCheck.Checks.Commands  $…$ShellCheck.Checks.Commands$$wchecker [A3-EDGE-GLOBAL]
```

```sh
$ h2r lower --reachability compiler/core-json \
      --link '$ShellCheck-0.11.0-inplace$ShellCheck.Formatter.TTY$format1'

  defined by exactly one top-level binding [A12-EXTERNAL-UNIQUE]
    module ShellCheck.Formatter.TTY   binder #91   occ format1
  referenced by 2 top-level binding(s) over 2 occurrence(s), in 2 module(s)
         1 occ over    1 binding(s)  Main                      [A3-EDGE-GLOBAL]
         1 occ over    1 binding(s)  ShellCheck.Formatter.TTY  [A2-EDGE-LOCAL]

  LIVE — witness [A9-WITNESS], 4 hop(s) from the root
      0. Main  $…-shellcheck$Main$main   [A1-ROOT-MAIN]
      1. Main  $…-shellcheck$Main$main1  [A2-EDGE-LOCAL]
      2. Main  $_in$poly_$j1#485         [A2-EDGE-LOCAL]
      3. Main  $_in$formats#140          [A2-EDGE-LOCAL]
      4. ShellCheck.Formatter.TTY  $…$ShellCheck.Formatter.TTY$format1 [A3-EDGE-GLOBAL]
```

Both are exactly the two names M3a could not link. Each resolves to **one** defining top-level binding, through the external-name index; each is live; and the witness paths are the ones the scratch measurement predicted.

Seven tests on the synthetic two-module world cover the view itself: the link names the one defining binding and its referrers, crosses a module through a local hop, refuses an internal name and refuses an occurrence name, reports a dead binding with no witness, and the identity-rule counts hold — with a world that violates `A13` failing loudly.

### Two new rules, reported with their counts

| rule                  | level | meaning                                                                         |                                   `-O1` |
| --------------------- | ----- | ------------------------------------------------------------------------------- | --------------------------------------: |
| `A12-EXTERNAL-UNIQUE` | 5     | every external in-world stable name is defined by exactly one top-level binding |    6106 names defined, **0** collisions |
| `A13-GLOBAL-EXTERNAL` | 4     | no `Ref::Global` occurrence carries an internal stable name                     | **0** occurrences, **0** distinct names |

`A12` is what makes `A3-EDGE-GLOBAL` an identity rather than a guess. `RootError::NameCollisions` already *refused* a world where it fails; now the size of the index and the collision count are printed, and `Accounting::check` asserts the latter is 0. The IR resolver's own unique-collision guard is summed over the world and printed beside them: **0**, on all seven dumps, as `h2r stats` also reports. All three counts hold on all seven.

### The compatibility re-check, on the old format-5 dumps

The old `-O1` dump in the scratchpad still loads, and with the final binary produces, for every report:

|                                                 |                                                |
| ----------------------------------------------- | ---------------------------------------------: |
| report files captured (stdout and stderr apart) |                                             94 |
| …byte-identical to the previous capture         |                                         **88** |
| …differing                                      | **6**, and every difference is an *added line* |

- `stats`, `stats --per-module`: one added line each, `dump format 5 (pre-CoreTidy)`. Nothing else.
- `lower --reachability`, `… --m24-link`: one added eight-line block, the identity-rule counts. The `STATUS — THE DEAD SET IS CONDITIONAL` block is **unchanged and still printed**, because `A5` is 112 on that dump — the new one-line verdict only appears when `A5` is 0, so the wording change is invisible here.
- `lower --rules`: the two added rule rows.
- `lower --json`: five added `accounting` keys (`external_names_defined` 1288, `external_name_collisions` 0, `global_internal_names` 0, `global_internal_occurrences` 0, `unique_collisions` 0) and the two added rules. Compared structurally with those removed, the rest of the document is **identical**.

### The transparency re-run, on the final plugin

Three builds of the stripped ShellCheck tree from the same sources: **(a)** no plugin, **(b)** the plugin as it was before this milestone (pre-tidy dump, no extra tidy), **(d)** the final plugin.

|                                                                                  | result                                                                                                                                                                                                                                                                                                                                                                                                                                                      |
| -------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| executable behaviour, (a) vs (b) vs (d)                                          | **identical** — 117 invocations (every `*.sh` in the repo through 7 formatters, 12 inline cases through 7 formatters plus the fixer, `--version`, `--help`), output *and* exit codes, 710 lines, byte-identical in all three                                                                                                                                                                                                                                |
| interface surface, **(b) vs (d)** — the measurement that isolates the extra tidy | **`ABI hash` and `export-list hash` unchanged on all 27 modules.** The only differences are the 27 `addDependentFile` lines naming the plugin's own `.so` (different path, different content) and the 27 `interface hash:` values that follow: 108 diff lines, 54 of each, and nothing else                                                                                                                                                                 |
| interface surface, (a) vs (d)                                                    | differs only in plugin-presence bookkeeping: `plugin package dependencies`, `trusted package dependencies`, the `.so` and package `addDependentFile` lines, and — on the two modules Safe Haskell had inferred safe, `Paths_ShellCheck` and `ShellCheck.Prelude` — `trusted: safe-inferred` → `trusted: none`, which does move those two `ABI hash`es. That is *loading a plugin at all*, not the extra tidy: (b) vs (d) shows the extra tidy moves neither |
| object symbols, (b) vs (d)                                                       | 20 of the 27 `.o` files differ byte-wise; **9,504 defined symbols in each, and of the 1,418 symbol names that differ, 0 are anything but a `<unique>_str` string-literal symbol or a `.Lr<unique>_bytes` local label** — symbols whose *names are internal uniques*. Consistent with, and only with, internal-unique perturbation                                                                                                                           |
| `shellcheck` binary sha256                                                       | (a) `1c2e2f59…`, (d) `2468445e…` — they differ, as (a) vs (b) already did for a plugin that touched nothing                                                                                                                                                                                                                                                                                                                                                 |
| deterministic repeat extraction                                                  | byte-identical across three independent build trees and three process runs, all 28 dumps and all 28 sidecars                                                                                                                                                                                                                                                                                                                                                |

What still could not be determined, unchanged from the earlier record: whether the `.o` bytes differ *only* in those symbol names and the relocations that follow them. `nm` shows the symbol tables agree; a byte-level attribution would need a full `objdump` comparison of 27 objects.

### A sanity pass over the M2 readers — and the one number that moved structurally

Run on the new `-O1` dump. "raw" is the tidied program with **no** join, which is what the join had to avoid. **These were preliminary checks**; the earlier M1–M2.4 sections retain their historical counts for the old dumps. The [format-6 baseline](#format-6-baseline-2026-09-16) below records the full run.

| report                                            |   old (pre-tidy) |  raw post-tidy |    **new (joined)** |
| ------------------------------------------------- | ---------------: | -------------: | ------------------: |
| `fields`: observed / unobserved / escaped         | 1407 / 13 / 7746 | 191 / 1 / 8931 | **1395 / 1 / 7727** |
| `fields`: `Always` verdicts                       |              196 |             34 |             **196** |
| `fields`: `Conditional` verdicts                  |              915 |            275 |             **895** |
| `lists`: `SpineDemand::Unknown`                   |             5503 |           8895 |            **5503** |
| `lists`: `Whole`                                  |              141 |             62 |             **141** |
| `lists`: `Prefix(DataDependent)`                  |              921 |            145 |             **921** |
| `classops`: dictionary known strict at its binder |              247 |              0 |             **236** |
| `classops`: class-op dispatch sites               |              565 |            554 |             **554** |
| `dictflow`: `Exact(target)` sites                 |         7 (1.2%) |              0 |        **0 (0.0%)** |
| `laziness`: potential thunk sites                 |             2242 |           2228 |            **2228** |

Every reader lands at or beside its old value, not at the raw one — except `dictflow`'s `Exact`, which is 0 on both. That one was chased down rather than waved through, and it is **not the join failing**:

- all 7 `Exact` sites were `setRange`, `end` and `start` — the `Range` class of `ShellCheck.Fixer`;
- those are exactly the four class-op selectors `getImplicitBinds` now injects as **real top-level bindings** of `ShellCheck.Fixer`;
- so an occurrence of one is no longer a `Ref::Global` naming a class-op selector the dump does not contain. It resolves `Ref::Local` to a top-level binding of its own module, and `dictflow` no longer classifies it as a class-op dispatch site at all. The site population falls 565 → 554, and the 11 sites that leave take the 7 `Exact` verdicts with them.

That is the dump getting *better*, in precisely the way `A5`'s "0 class-op selectors remain" line reports: the dispatch M2.4c had to model as a bounded class-op site is now a plain call to a selector binding the world contains. Whether `dictflow` should still count such a call as a dispatch site was left open here; the [format-6 baseline](#format-6-baseline-2026-09-16) below records the population decision. The join itself is proved directly, not by these numbers: **115,537 aligned binders, every field equal to its owning side, 0 violations** — and `classops`' 236 (raw: 0) and `fields`' 1395 (raw: 191) are what a working join looks like.

Every independent verifier on the new `-O1` dump:

| verifier                 |                            claims | disagreements |
| ------------------------ | --------------------------------: | ------------: |
| `tuples --verify`        |           1227 removable verdicts |         **0** |
| `verify-rep`             | every M2.3 representation verdict |         **0** |
| `verify-m24`             |         every positive M2.4 claim |         **0** |
| `lower --reachability`'s |                            116029 |         **0** |

`cargo fmt --all --check` clean, `cargo clippy --workspace --all-targets -- -D warnings` clean, `cargo test --workspace` **270 passing** (263 before, plus the seven new ones). The synthetic-module tests in `h2r-analysis` and `h2r-lower` pass unchanged.

### Where this leaves the milestone

The dumps are regenerated under the join, on all seven profiles. `A5-IN-WORLD-MISSING` is 0 everywhere, every stable name in the closed world links, the two names M3a could not resolve resolve structurally, and the identity rules are asserted with their counts. The dump is format 6 and says so.

**The format-6 baseline run and verifier checks are complete. Before/after accounting and site-level attribution remain open; see todo.md.** The M1–M2.4 sections above retain the historical pre-tidy counts; the current counts and remaining proof limitations follow below. M3b is next.

### Format-6 baseline (2026-09-16)

Historical snapshot before the local-selector census correction below. The 2026-09-17 correction supersedes its class-op and M2.4 counts.

The canonical input remains `-O1`, with GHC 9.6.7 and Cabal 3.18.1.0. Source and analysis revision: `49005a34b2334edcb45d0a1f45dbef4935e36681`. The canonical dump and profile A are byte-identical, as are their analysis reports. Earlier M1–M2.4 tables describe the pre-tidy input; the counts below describe the post-tidy input with the proof facts joined back on.

| Canonical result                                           |          Format 6 |
| ---------------------------------------------------------- | ----------------: |
| Modules / top-level bindings                               |       28 / 13,752 |
| M1 potential thunk sites / recursive values                |        2,228 / 69 |
| M2.1 proven Parsec regions / unresolved residual edges     |        1,301 / 41 |
| M2.2 jointly removable tuples                              |             1,227 |
| M2.3 direct fields / dead fields                           |         3,346 / 2 |
| M2.3 independently confirmed claims / coverage refusals    |        4,322 / 10 |
| M2.4 class-op sites / exact targets                        |           554 / 0 |
| M2.4 one-representation boundaries / rewritable boundaries |           92 / 70 |
| M2.4 independently confirmed claims / coverage refusals    |           601 / 0 |
| M1 residual after verified M2 removals                     |             2,127 |
| Reachability live / dead / missing in-world names          | 9,795 / 3,957 / 0 |
| Reachability independently confirmed claims                |           116,029 |

Every independent verifier reports zero semantic disagreements. The ten M2.3 coverage refusals are five consed-as-tail traversals and five loop-spine claims that the independent walker cannot re-derive. They are excluded from positive accounting. M2 removes 92 tuple-related and 9 field/list-related thunk sites; M2.4 removes no additional thunk sites: `2228 - 92 - 9 = 2127`. The 41 residual Parsec continuation edges remain open.

CoreTidy trims bindings and introduces implicit selector bindings, so the population changes; the proof predicates have not been relaxed. In particular, the four `Range` selectors now have bodies in the dumped world. Their eleven local call sites, including the seven former exact targets, leave the imported class-op census. This initial baseline kept that census definition: local selector calls are ordinary calls to available bindings. Zero exact targets among the remaining 554 sites does not mean the seven known calls became unknown.

The same gates pass on all six optimization profiles. Every profile contains the same 28 modules, all alignment sidecars report no errors, every independent verifier reports zero semantic disagreements, M2.4 has zero coverage refusals, and reachability has zero missing in-world names.

| Profile               | Thunk sites | Removable tuples | M2.3 confirmed / refused | M2.4 confirmed |   Live / dead |
| --------------------- | ----------: | ---------------: | -----------------------: | -------------: | ------------: |
| canonical / A (`-O1`) |       2,228 |            1,227 |               4,322 / 10 |            601 | 9,795 / 3,957 |
| B                     |       2,375 |            1,485 |               5,137 / 11 |            739 | 9,894 / 3,973 |
| C                     |       2,833 |            1,360 |               6,054 / 15 |            867 | 2,759 / 3,276 |
| D                     |       7,234 |            2,494 |              16,589 / 15 |          2,215 | 3,082 / 3,807 |
| E                     |       7,054 |            2,528 |              14,890 / 15 |          2,193 | 3,082 / 3,807 |
| F                     |       7,032 |            2,529 |              14,856 / 15 |          2,219 | 3,078 / 3,801 |

Profile flags are defined in `compiler/matrix.sh`. These are distinct Core populations, so more removable tuples alone does not make a better input: the aggressive profiles also replicate substantially more thunk sites.

Run `mise run baseline` for extraction and reports, or `mise run baseline:reports` for reports from existing dumps. Both reuse completed results whose input and output checksums still match. Interrupted extraction resumes its Cabal build when the input fingerprint matches. `H2R_JOBS` limits extraction concurrency. Outputs stay in `compiler/core-json` and `compiler/matrix/<profile>`; canonical reports live in `compiler/matrix/canonical/reports`. Each report directory contains text, JSON, input fingerprints and output checksums. Build trees are retained for incremental extraction.

### Evidence: the four local `Ranged` selectors and the census exclusion (2026-09-16)

This records the pre-correction exclusion. The 2026-09-17 correction below uses this evidence to restore the local sites to the census.

Site-level evidence for the population-definition sentence above, "local selector calls are ordinary calls to available bindings", read from the canonical `-O1` dump and reports, no extraction run.

**The four bindings.** `ShellCheck.Fixer.tidy-align.txt` (`getImplicitBinds`, lines 54-58) names `start_rYqD`, `end_rYqE`, `overlap_rYqF`, `setRange_rYqG`. `ShellCheck.Fixer.core.json` has each as a top-level pair, arity 1, RHS node `Lam`, binder `details` field `"[ClassOp]"`:

| occ        | stable name                                            | unique | RHS `ExprId` | binder JSON path            |
| ---------- | ------------------------------------------------------ | ------ | -----------: | --------------------------- |
| `start`    | `$ShellCheck-0.11.0-inplace$ShellCheck.Fixer$start`    | rYqD   |            0 | `.binds[0].pairs[0].binder` |
| `end`      | `$ShellCheck-0.11.0-inplace$ShellCheck.Fixer$end`      | rYqE   |            1 | `.binds[1].pairs[0].binder` |
| `overlap`  | `$ShellCheck-0.11.0-inplace$ShellCheck.Fixer$overlap`  | rYqF   |            2 | `.binds[2].pairs[0].binder` |
| `setRange` | `$ShellCheck-0.11.0-inplace$ShellCheck.Fixer$setRange` | rYqG   |            3 | `.binds[3].pairs[0].binder` |

The RHS `ExprId` is `h2r show`'s own node address: `h2r show compiler/core-json ShellCheck.Fixer <N>` on each of `0`-`3` prints `-- in top-level binding <occ>, node <N>` followed by the `Lam` from that occ's definition, confirming the id names that exact node. `BinderId` is a separate arena index the loader assigns when it flattens the raw dump into a `Module` (`h2r-core-ir/src/lib.rs:25`); `h2r show` never prints one (no binder in its output, lambda parameter, case binder or alt binder, carries a bracketed id, only `Var`/`Case`/`App`/`Lam`-root nodes do), so the JSON path above is given instead. That path is a raw-JSON array index into `RawModule.binds`, not a `BinderId` and not an `ExprId`: confirmed directly against `ShellCheck.Fixer.core.json` (`.binds[0..3]`, each a non-recursive one-pair group, `occ` `start`/`end`/`overlap`/`setRange` in that order, `details == "[ClassOp]"`).

**Applications inside `ShellCheck.Fixer`.** Every `Var` occurrence of the four names, spine head traced to its `App` root, one row per full application. `head ExprId` and `spine-root ExprId` are read directly off `h2r show compiler/core-json ShellCheck.Fixer --depth 40 --no-parsec --no-tuples --no-fields --no-lists --no-text --no-classops --no-higher`, which prints `[spine-root]head[head-id] arg1[id1] arg2[id2] …` for a spine and never prints `@Type`/coercion arguments, so the printed argument count is already the value-argument count:

| owner            | selector   | head `ExprId` | spine-root `ExprId` | value args |
| ---------------- | ---------- | ------------: | ------------------: | ---------: |
| `$dmoverlap`     | `start`    |          1922 |                1855 |          2 |
| `$dmoverlap`     | `end`      |          1916 |                1857 |          2 |
| `$dmoverlap`     | `start`    |          1910 |                1884 |          2 |
| `$dmoverlap`     | `end`      |          1904 |                1886 |          2 |
| `removeTabStops` | `setRange` |          1257 |                1158 |          3 |
| `removeTabStops` | `start`    |          1249 |                1209 |          2 |
| `removeTabStops` | `start`    |          1239 |                1213 |          1 |
| `removeTabStops` | `start`    |          1226 |                1220 |          2 |
| `removeTabStops` | `end`      |          1205 |                1165 |          2 |
| `removeTabStops` | `end`      |          1195 |                1169 |          1 |
| `removeTabStops` | `end`      |          1182 |                1176 |          2 |

Eleven rows, matching "eleven local call sites" above: `$dmoverlap` has 2× `start` and 2× `end`, each 2 value args (the dictionary and one `PositionedComment`/`Replacement`); `removeTabStops` has 3× `start` and 3× `end`, each selector once at 1 value arg and twice at 2. The 1-arg row is the point-free `g = start $dRanged`: `start`'s binder arity is 1 (its single parameter is the dictionary itself, per the four-bindings table above), so this application is saturated, not partial, and returns the extracted method value, itself a function; `scope.rs`'s binding-site branch excludes it on `is_class_op: false`, not on argument count. Plus 1× `setRange` at 3 (dictionary, the constructed `(start.., end..)` pair, `range`). `overlap` has zero rows: it is never applied in the module and never appears in `ShellCheck.Fixer.core.json`'s `ids` table. The `setRange` application sits in the body of `removeTabStops` (`binds[32].pairs[0].binder.occ == "removeTabStops"`), the function the historical Exact-verdict example above names.

**The exclusion, traced for the `removeTabStops`/`setRange` application.** `removeTabStops` and `setRange` are both top-level bindings of `ShellCheck.Fixer`, so the occurrence resolves lexically within the module. `Scope::head_sig` (`h2r-analysis/src/scope.rs:108`) takes the binding-site branch at line 112 (`self.binding_of(head)` is `Some`) and returns at lines 114-122 with `is_class_op: false` fixed at line 121, under the comment "Locals are never constructors or class methods" at line 119. The id-table branch at lines 124-134, which reads `IdInfo::is_class_op`, is never reached for this occurrence. `Census::add_module` (`h2r-analysis/src/classops.rs:731-741`) calls `s.head_sig(head)` at line 736 and drops the site at line 739 (`if !sig.is_class_op { continue; }`). No `Site` is built for this application.

**What ClassOp information survives, and where.** `raw::Binder` (`h2r-core-ir/src/raw.rs:213-263`), the type `head_sig`'s binding-site branch reads at `scope.rs:113`, carries no `is_class_op` field: not stored on that type at all. It does carry `details: Option<String>` (`raw.rs:243`), and the dump has `details == "[ClassOp]"` on all four binders; `head_sig` never reads `b.details`. `raw::IdInfo` (`raw.rs:134-154`) does carry `is_class_op: bool` (`raw.rs:144`), and the module's own `ids` table has redundant entries for `start`, `end` and `setRange` (not `overlap`, never referenced) with `isClassOp: true`, per the redundancy `raw.rs:62-68` documents for a module's own externalised top-level binders. That table is never consulted for these three: the binding-site branch returns at `scope.rs:122`, before line 126 (`self.m.ids.get(name)`) runs.

**Proven.** The eleven applications above are excluded from the classop population by `scope.rs:112-122` and `classops.rs:736-739`, for the reason traced above, on this dump. `dictflow.json`'s `.parameters` entry for `removeTabStops`'s `$dRanged` (`owner: "removeTabStops", occ: "$dRanged"`) still resolves to `{Set: ["ShellCheck.Fixer#18"]}`, i.e. `$fRangedPositionedComment`, the instance the historical Exact-verdict example above names, independently of the classop-site exclusion: `dictflow`'s own parameter union does not read `Census`'s site population.

**The seven method targets, traced on format 6 (2026-09-17).** All seven applications in `removeTabStops` pass its own dictionary parameter. In the raw RHS, their first value argument has unique `aYPX`, and the enclosing parameter at `.binds[32].pairs[0].rhs.body.binder` is the sole binding of that unique within the function. This is a lexical binding check within this dump, not a cross-build unique match. The parameter's producer set in `dictflow.json` is the singleton `{ShellCheck.Fixer#18}`.

The selector bodies themselves case on `C:Ranged` and return alternative fields 0 (`start`), 1 (`end`), 2 (`overlap`) and 3 (`setRange`). This field mapping follows the bound variables in the case alternatives, not their diagnostic names. Dictionary construction node 18 supplies `pcStartPos`, `pcEndPos`, `$fRangedPositionedComment_$coverlap` and `$fRangedPositionedComment_$csetRange` in that order. Combining that constructor with each selector body gives all seven targets:

| spine root | dictionary argument | selector   | field | selected method                                         |
| ---------: | ------------------: | ---------- | ----: | ------------------------------------------------------- |
|       1158 |                1256 | `setRange` |     3 | `ShellCheck.Fixer.$fRangedPositionedComment_$csetRange` |
|       1209 |                1248 | `start`    |     0 | `ShellCheck.Interface.pcStartPos`                       |
|       1213 |                1238 | `start`    |     0 | `ShellCheck.Interface.pcStartPos`                       |
|       1220 |                1225 | `start`    |     0 | `ShellCheck.Interface.pcStartPos`                       |
|       1165 |                1204 | `end`      |     1 | `ShellCheck.Interface.pcEndPos`                         |
|       1169 |                1194 | `end`      |     1 | `ShellCheck.Interface.pcEndPos`                         |
|       1176 |                1181 | `end`      |     1 | `ShellCheck.Interface.pcEndPos`                         |

These are manually re-derived targets from existing proof facts and Core, not seven `Exact` entries emitted by the pre-correction class-op census: it excluded all seven before target analysis. The same dictionary-field selection and singleton-target rule is implemented by `field_expr` and `outcome_of` in `h2r-analysis/src/dictflow.rs`. The two dictionary-only applications select known method values even without applying those methods to a `PositionedComment`.

The other four applications are in `$dmoverlap`; its dictionary parameter has `Top(function-is-unreachable-in-the-closed-world)` in `dictflow.json`. They therefore supply no additional known targets under the existing producer-set rules. The eleven excluded applications split into seven with a determined target and four without one.

This reconstructs the seven-target result on the current program and agrees with the historical seven-target aggregate and the recorded `setRange` example. It is not an old-node-to-new-node identity proof: the six other historical site records were not found in the available captures. The census decision and implementation follow below.

### Local class-op selectors remain in the census (2026-09-17)

A class-op call remains a class-op call when its definition is available locally. `Scope::head_sig` first resolves lexical identity. For a top-level binding, it reads GHC's structured `isClassOp` flag from the redundant id-table entry keyed by that definition's stable name. Arity, demand and divergence still come from the binding site. Nested binders cannot inherit the flag from a shadowed global name. No pretty `IdDetails` string is parsed, no unique is used for linkage, and no new dump or format is required.

The independent M2.4 verifier implements the same input contract through its own lookup; it does not call the analysis helper. Target resolution, dictionary boundedness and dictionary erasure remain separate questions. An exact target does not by itself grant permission to erase a dictionary.

On canonical `-O1`, all eleven local `Ranged` applications re-enter the population: seven resolve to the method targets in the evidence table and four remain unresolved because their owner, `$dmoverlap`, is unreachable. Thus `554 = 0 + 554` becomes `565 = 7 + 558`; bounded dictionary sets rise from 111 to 118. Dead-attributed class-op sites rise from 409 to 413, exactly the four `$dmoverlap` applications. The independent verifier confirms 615 claims (previously 601), with zero disagreements and zero coverage refusals. The added claims are seven exact targets and seven bounded dictionary sets.

All seven existing dumps were checked with `mise run baseline:reports`:

| profile   | sites | Exact | unresolved | bounded dictionaries | verified claims |
| --------- | ----: | ----: | ---------: | -------------------: | --------------: |
| canonical |   565 |     7 |        558 |                  118 |             615 |
| A         |   565 |     7 |        558 |                  118 |             615 |
| B         |   587 |     7 |        580 |                  138 |             753 |
| C         |   595 |     7 |        588 |                  140 |             881 |
| D         |   595 |     0 |        595 |                   65 |           2,215 |
| E         |   595 |     0 |        595 |                   65 |           2,193 |
| F         |   596 |     0 |        596 |                   65 |           2,219 |

Sources: `compiler/matrix/<profile>/reports/m24.json` → `.accounting.targets`, `.accounting.claims`, and `verify-m24.txt`. Finite target sets remain zero. Every profile gains eleven census sites; unreachable owners still prevent target claims. All seven independent M2.4 checks report zero disagreements and zero coverage refusals. The complete erasure and representation accounting, and M1 thunk-site totals, are unchanged from the pre-correction reports for every profile.

Three regression tests cover local classification with stale occurrence signatures, rejection of pretty-string inference, and lexical shadowing. Workspace tests and Clippy (`--all-targets -- -D warnings`) pass.

### Gate-8 attribution: reason provenance versus rooted death (2026-09-21)

The corrected census restores 413 sites whose unresolved reason is `function-is-unreachable-in-the-closed-world`. **Only 193 of those sites are inside rooted-dead top-level bindings.** The other 220 are inside rooted-live bindings. Across all 558 unresolved dispatch sites, 262 have rooted-dead owners. These are the current canonical `reachability.txt` cross-reference counts; the earlier 413/413 result in [M3a's residual section](#where-m24s-residual-sits) used conditional, pre-tidy reachability and must not be carried forward as an invariant.

The reason is provenance of an unknown dictionary set, not a reachability verdict on the consuming site. `dictflow::producers_of` seeds it at a zero-reference function; parameter propagation and `DictSet::join` carry `Top(reason)` onward. Joining two unknown sets keeps the lexicographically smaller reason. A live consumer can therefore display a reason originating in dead code. Its target remains `Unresolved`; this grants no erasure or dead-code-removal permission.

Concrete counterexample, from the current binary's explanations:

```text
ShellCheck.AST node 6559  Applicative.liftA2
  -> Unresolved function-is-unreachable-in-the-closed-world
ShellCheck.AST $fTraversableInnerToken_$ctraverse.$dApplicative#0
  Top(function-is-unreachable-in-the-closed-world)
```

The enclosing top-level binding is binder 361, `$ShellCheck-0.11.0-inplace$ShellCheck.AST$$fTraversableInnerToken_$ctraverse`. `lower --reachability --explain` confirms it is live via the six-edge path `Main.main → main1 → poly_$j1 → checkScript → analyzeScript → $wrunChecker → $fTraversableInnerToken_$ctraverse`. The last four edges use authoritative cross-module linkage. This disproves interpreting the site's reason as its owner's dead verdict, without changing either analysis's semantics.

`mise run baseline:explain` captures canonical `dictflow`, `higher` and `parsec --explain`, plus that reachability witness, under `compiler/matrix/canonical/explain/`. Profile arguments select other existing dumps. The task uses the existing release binary, fingerprints it and the dumps, and reuses checksum-verified captures; it does not build or extract.

The captures also preserve the other current gate-8 evidence:

- Dictionary clone planning: four owners, each with one set-valued tuple containing the Identity and IO Monad dictionaries; four clones are a lower bound, not eight independent specializations.
- Closure clone planning: 71 clones across 22 planned owners, with eight set-valued lower-bound plans. For example, `$wpoly_k2` has six classes in its parameter set but four distinct assignment tuples, one set-valued.
- Residual Parsec edges: all 41 remain unresolved, split into 2 partial-call, 19 function-as-value and 20 anonymous-lambda refusals. For example, `ShellCheck.Parser#1946` reaches anonymous `eok` parameter 3 at node 1930; the closure graph cannot enumerate its producer set.
- Local selectors: the eleven-site correction and seven exact targets are accounted for in the preceding section, independently of rooted death.

#### The three extra closure clones, localized

`higher --explain --json` now includes every `clonePlans` entry with its `ownerBinder`, full shape tuples and call-site partition. The text explanation also includes every owner; the ordinary summary still shows the first 20. The existing JSON fields are unchanged. `baseline:explain` saves this evidence as `higher-plans.json` alongside the text captures.

Comparing the historical M2.4h owner table with the current plans gives:

| module                         | historical owners / clones | current owners / clones |
| ------------------------------ | -------------------------: | ----------------------: |
| ShellCheck.AST                 |                      0 / 0 |                   1 / 3 |
| ShellCheck.ASTLib              |                      1 / 2 |                   1 / 2 |
| ShellCheck.Analytics           |                     3 / 10 |                  3 / 10 |
| ShellCheck.CFGAnalysis         |                      3 / 9 |                   3 / 9 |
| ShellCheck.Checks.ShellSupport |                      1 / 3 |                   1 / 3 |
| ShellCheck.Fixer               |                      1 / 2 |                   1 / 2 |
| ShellCheck.Parser              |                    12 / 42 |                 12 / 42 |
| **Total**                      |                **21 / 68** |             **22 / 71** |

The extra current owner is `ShellCheck.AST` binder 322, `$fTraversableInnerToken_$s$ctraverse`, parameter `eta#0` (binder 2933, lambda node 10424). Its three clone groups are singleton call sites: `ShellCheck.AST#1105`, `ShellCheck.Analytics#51637`, and `ShellCheck.Parser#106026`. The corresponding producers are `ShellCheck.AST#1085`, `ShellCheck.Analytics#1769`, and `ShellCheck.Parser#104248`. All have arity 1. Their capture vectors differ: two function types; no captures; and a Map type plus a function type. Thus these really are three shape classes, including two that the short rendering would both call "arity 1, 2 captures". This plan has no set-valued component: all three clones are fully enumerated.

This locates the net delta at module level and identifies the entire current AST plan. Equal totals elsewhere do not prove that each historical binder or producer set survived unchanged. The AST sidecar records zero trimmed and zero implicit bindings, excluding creation of this owner by selector injection or local trimming. The reconstruction below now supplies the historical producer set and identifies repaired linkage as the cause of this transition.

#### What each proposed cause actually establishes

- **Linkage — a paired named example survives.** The historical A5 section records Analytics referring to external `ShellCheck.ASTLib.$wgetPath` while its definition was `$_in$$wgetPath`. The current `path-link.txt` capture resolves that same external reference to ASTLib binder 142: 52 occurrences across four modules, 43 referring top-level bindings, and a six-edge live witness. Of those occurrences, 51 cross module boundaries. The original missing definition and the current resolved definition are documented; no occurrence-name guess is used to construct the current edge.
- **Trimming — population is proved, verdict deltas are not.** The sidecars identify all 80 removed binders. For example, Main loses `$s$w$c<*>_sdG7`, kept alive only by an auto-rule. Its body is absent from the current dump, so a current `--explain` cannot recover its old thunk, boundary or producer contribution. The population identity is `13,828 − 80 + 4 = 13,752`; it is not a per-analysis attribution.
- **Implicit selectors — closed.** The preceding selector evidence supplies the four definitions, eleven sites, seven exact targets and four unreachable-owner sites. This has its own checked correction.
- **OccInfo — exclude the irrelevant field change.** The recorded top-level loop-breaker count falls from 691 to 250, but no analysis consumes that variant. The only `occ_info` read in the analysis crate is M1's `OccInfo::Dead` check (`laziness.rs`). In particular, the loop-breaker delta cannot explain an H15 clone-plan change. **Arity is separate:** `higher` does read binder signatures for known functions and partial applications. The current AST plan's three producers all have arity 1; their historical signatures are not preserved in the owner table.

Gate 8 remains open for historical per-site trimming and arity/Dead-OccInfo attribution. The canonical reconstruction below removes the missing-input blocker and closes the AST clone-plan transition.

#### Reconstructed canonical format-5 input (2026-09-21)

`mise run baseline:historical` reconstructs commit `aa5b7f3763ea6c95dc0412ac2bbae6fddee6c487` with its original plugin and ShellCheck sources, GHC 9.6.7 and package-local `-O1`. It archives the requested files into `compiler/matrix/format5/build`; it does not switch branches or create a worktree. Dependency versions are constrained by `compiler/matrix/A/plan.json`. All dependency unit IDs match that plan, and the stripped source hash matches profile A exactly: `e588f5a2854d9356e5b43cdcb268e8265f6d603c4efb13dc03c11fe3444fcf7f`.

The 28 dumps (76 MiB) are in `compiler/matrix/format5/core-json`; the binary, build plan and provenance remain beside them. These are reconstructed historical inputs, not recovered original captures. The current analyzer's `baseline:historical-reports` task reproduces 13,828 top-level bindings, 2,242 thunk sites, 565 dispatch sites / 7 Exact targets, and 68 closure clones across 21 owners. The independent M2.4 verifier confirms 606 claims with zero disagreements and zero coverage refusals. Both tasks reuse checksum-verified outputs on a second invocation.

The old AST definition is binder 322, `$_in$$s$ctraverse`, arity 2; the new one is binder 322, `$ShellCheck-0.11.0-inplace$ShellCheck.AST$$fTraversableInnerToken_$s$ctraverse`, also arity 2 with the same function type. A paired walk confirms the same 1,026-node expression topology and 348 variable-reference links, mapping binders by position rather than assuming unique equality.

The old `higher.json` records parameter `eta#0` at node 10424 as `ExactClosure`, with only producer `ShellCheck.AST#1085`. Analytics and Parser already carry the final external name in their format-5 id tables (arity 2), but the old internal definition cannot link to it. In format 6 those callers reach the definition and contribute `ShellCheck.Analytics#1769` and `ShellCheck.Parser#104248`. The parameter becomes `CloneRequired(3)` and enters the owner plan with the three groups listed above. The original local producer's full shape is unchanged. This is the concrete linkage-driven transition behind the extra owner and three clones; it is not an arity change or a newly injected definition.

### Format-6 baseline — before/after accounting tables (2026-09-16)

These tables retain the pre-correction snapshot. Report paths name the captures used at that time; rerunning `baseline:reports` updates those files to the current compiler. See the dated local-selector correction above for the changed M2.4 results.

Partial fill of the before/after accounting brief 1 asked for, per milestone, across all seven profiles. Site-level attribution (why a number differs between two profiles) is not attempted here; that is separate, still-open work. Sources are named under each table by report file and JSON path. Where the historical (pre-tidy) README section documents the exact same metric for canonical/`-O1`, it is given alongside; where it does not, the cell says "niet vastgelegd" rather than 0.

#### 1. M1 — thunk-site breakdown

Source: `m24.json` → `.m1Link` (`rows`, `by_m23`, `by_tuples`, `thunk_sites`). `residual = thunk_sites − by_m23 − by_tuples − by_m24` (`by_m24` is 0 on every profile).

| profile   | thunk sites (before) | removed by tuples (M2.2) | removed by M2.3 | removed by M2.4 | residual |
| --------- | -------------------: | -----------------------: | --------------: | --------------: | -------: |
| canonical |                2,228 |                       92 |               9 |               0 |    2,127 |
| A         |                2,228 |                       92 |               9 |               0 |    2,127 |
| B         |                2,375 |                      103 |               8 |               0 |    2,264 |
| C         |                2,833 |                      120 |               4 |               0 |    2,709 |
| D         |                7,234 |                      121 |              10 |               0 |    7,103 |
| E         |                7,054 |                      121 |              10 |               0 |    6,923 |
| F         |                7,032 |                      121 |              10 |               0 |    6,901 |

`.m1Link.rows` itself, the four thunk-site classes summed into each `by_m23`/`by_tuples` column above (`by_m24` is 0 in every row on every profile, so it is dropped here):

| profile   | eager-position (before / by_m23 / by_tuples) | lazy-position (before / by_m23 / by_tuples) | memoisation-required (before / by_m23 / by_tuples) | recursive value (before) |
| --------- | -------------------------------------------: | ------------------------------------------: | -------------------------------------------------: | -----------------------: |
| canonical |                                   14 / 3 / 0 |                                 254 / 3 / 3 |                                     1,891 / 3 / 89 |                       69 |
| A         |                                   14 / 3 / 0 |                                 254 / 3 / 3 |                                     1,891 / 3 / 89 |                       69 |
| B         |                                   14 / 3 / 0 |                                 259 / 4 / 3 |                                    2,037 / 1 / 100 |                       65 |
| C         |                                   10 / 0 / 0 |                                 541 / 2 / 2 |                                    2,237 / 2 / 118 |                       45 |
| D         |                                   16 / 6 / 0 |                                 750 / 2 / 2 |                                    6,349 / 2 / 119 |                      119 |
| E         |                                   16 / 6 / 0 |                                 756 / 2 / 2 |                                    6,163 / 2 / 119 |                      119 |
| F         |                                   16 / 6 / 0 |                                 756 / 2 / 2 |                                    6,141 / 2 / 119 |                      119 |

Recursive values contribute 0 to `by_m23` and `by_tuples` on every profile; row `before` values sum to `thunk_sites` (e.g. canonical: `14 + 254 + 1891 + 69 = 2228`), and each row's `by_m23`/`by_tuples` sum to the table above's "removed by" totals (e.g. canonical `by_tuples`: `0 + 3 + 89 = 92`).

Historical comparison, canonical/`-O1` only (source: [M1](#m1--how-much-haskell-is-left-after-ghc), the "Potential thunk sites" row):

| metric                     | old (pre-tidy) | new (format 6) |
| -------------------------- | -------------: | -------------: |
| thunk sites (before)       |          2,242 |          2,228 |
| removed by tuples (M2.2)   |             92 |             92 |
| removed by M2.3            |             11 |              9 |
| residual after M2 removals |          2,139 |          2,127 |

#### 2. M2.1 — Parsec population and residual edges

Source: `parsec.json` → `.accounting` (`population`, `exact`, `finite`, `region_unresolved`, `rejected`); `m24.json` → `.m21ResidualEdges` (array length).

| profile   | population | exact | finite | region_unresolved | rejected | residual edges |
| --------- | ---------: | ----: | -----: | ----------------: | -------: | -------------: |
| canonical |      1,872 | 1,858 |      8 |                 0 |        6 |             41 |
| A         |      1,872 | 1,858 |      8 |                 0 |        6 |             41 |
| B         |      2,195 | 2,081 |      8 |                99 |        7 |             50 |
| C         |      2,241 | 2,061 |     25 |               144 |       11 |             71 |
| D         |      9,127 | 8,407 |     84 |               583 |       53 |            249 |
| E         |      8,047 | 7,471 |     84 |               439 |       53 |            249 |
| F         |      7,523 | 6,903 |     82 |               485 |       53 |            330 |

Historical comparison, canonical/`-O1` only (source: [M2.1 — Results on the `-O1` dump](#results-on-the--o1-dump), "The 2,117 Parsec-shaped unresolved sites"; candidate/proven regions of 1,301 are already unchanged in the Format-6 baseline table above):

| metric            | old (pre-tidy) | new (format 6) |
| ----------------- | -------------: | -------------: |
| population        |          2,117 |          1,872 |
| exact             |          2,099 |          1,858 |
| finite            |              8 |              8 |
| region_unresolved |              0 |              0 |
| rejected          |             10 |              6 |

#### 3. M2.2 — tuples, boxed and unboxed separately

Source: `tuples.json` → `.accounting.milestone` (`before`, `normalised`, `preserved`, `unsupported`, per `boxed` flag).

| profile   | boxed before | boxed normalised | boxed preserved | boxed unsupported | unboxed before | unboxed normalised | unboxed preserved | unboxed unsupported |
| --------- | -----------: | ---------------: | --------------: | ----------------: | -------------: | -----------------: | ----------------: | ------------------: |
| canonical |        1,754 |              539 |             550 |               665 |            812 |                688 |                 0 |                 124 |
| A         |        1,754 |              539 |             550 |               665 |            812 |                688 |                 0 |                 124 |
| B         |        1,978 |              625 |             682 |               671 |          1,013 |                860 |                 0 |                 153 |
| C         |        2,239 |              562 |             673 |             1,004 |            936 |                798 |                 0 |                 138 |
| D         |        4,252 |              930 |             903 |             2,419 |          1,724 |              1,564 |                 0 |                 160 |
| E         |        4,263 |              964 |             880 |             2,419 |          1,724 |              1,564 |                 0 |                 160 |
| F         |        4,348 |              964 |             880 |             2,504 |          1,725 |              1,565 |                 0 |                 160 |

Historical comparison, canonical/`-O1` only (source: [M2.2 — Accounting](#accounting), the `M2.2 accounting` block):

| metric                                            | old (pre-tidy) | new (format 6) |
| ------------------------------------------------- | -------------: | -------------: |
| boxed before                                      |          1,765 |          1,754 |
| boxed normalised                                  |            539 |            539 |
| boxed preserved                                   |            551 |            550 |
| boxed unsupported                                 |            675 |            665 |
| unboxed before                                    |            819 |            812 |
| unboxed normalised                                |            667 |            688 |
| unboxed preserved                                 |              0 |              0 |
| unboxed unsupported                               |            152 |            124 |
| removable without cloning (total normalised)      |          1,206 |          1,227 |
| removable only via a clone (`RemovableWithClone`) |              3 |              3 |
| removable locally (def-use), before composition   |          1,453 |          1,439 |

`removable without cloning` old is [M2.2's own line](#two-numbers-two-questions--kept-apart-on-purpose); new is `tuples.json` → `.accounting.removable_with_clone` (clone count, unchanged at 3) and the boxed+unboxed `normalised` sum above (1,227, already in the Format-6 baseline table as "M2.2 jointly removable tuples"). "removable locally (def-use), before composition" old is [the 1,453 figure](#two-numbers-two-questions--kept-apart-on-purpose); new is `of the N flow(s) def-use proved removable` in `boundaries.txt` (canonical/A: 1,439), per profile below.

| profile   | removable locally (def-use) | of which cross ≥1 boundary | of which cross none |
| --------- | --------------------------: | -------------------------: | ------------------: |
| canonical |                       1,439 |                      1,010 |                 429 |
| A         |                       1,439 |                      1,010 |                 429 |
| B         |                       1,727 |                      1,249 |                 478 |
| C         |                       1,680 |                      1,259 |                 421 |
| D         |                       3,970 |                      3,096 |                 874 |
| E         |                       4,004 |                      3,130 |                 874 |
| F         |                       4,009 |                      3,135 |                 874 |

Source: `boundaries.txt` per profile, the "of the N flow(s) def-use proved removable, X cross at least one boundary and Y cross none" line.

#### 4. M2.3 — fields, lists, text

Source: `verify-rep.json` → `.m23Accounting.fields[4]` (the `"total"` row: `before`, `dead`, `proven_eager`, `proven_lazy`, `unsupported`); `.m23Accounting.lists` (`before`, `advised`, `unsupported`); `.m23Accounting.text` (`before`, `advised`, `unsupported`); `.crossCheck` (`checked`, `agreed`). `checked − agreed` below is labelled "coverage refusals", matching [M2.3's own table](#what-it-found): every dump's independent walker reports **0** actual disagreements, on this baseline as on the pre-tidy one.

| profile   | fields before | fields dead | fields direct (proven_eager) | fields proven_lazy | fields unsupported | lists before | lists advised | lists unsupported | text before | text advised | text unsupported | crossCheck checked | crossCheck agreed | crossCheck coverage refusals |
| --------- | ------------: | ----------: | ---------------------------: | -----------------: | -----------------: | -----------: | ------------: | ----------------: | ----------: | -----------: | ---------------: | -----------------: | ----------------: | ---------------------------: |
| canonical |        19,746 |           2 |                        3,346 |                987 |             15,411 |       11,813 |         2,704 |             9,109 |       4,431 |        2,748 |            1,683 |              4,332 |             4,322 |                           10 |
| A         |        19,746 |           2 |                        3,346 |                987 |             15,411 |       11,813 |         2,704 |             9,109 |       4,431 |        2,748 |            1,683 |              4,332 |             4,322 |                           10 |
| B         |        21,954 |          23 |                        4,142 |              1,026 |             16,763 |       12,136 |         2,832 |             9,304 |       4,473 |        2,793 |            1,680 |              5,148 |             5,137 |                           11 |
| C         |        23,319 |          18 |                        4,571 |                791 |             17,939 |       13,641 |         3,108 |            10,533 |       5,343 |        3,231 |            2,112 |              6,069 |             6,054 |                           15 |
| D         |        51,741 |         109 |                       14,286 |                985 |             36,361 |       23,798 |         4,468 |            19,330 |       7,780 |        4,345 |            3,435 |             16,604 |            16,589 |                           15 |
| E         |        47,009 |          79 |                       12,686 |                931 |             33,313 |       22,600 |         4,301 |            18,299 |       7,478 |        4,151 |            3,327 |             14,905 |            14,890 |                           15 |
| F         |        47,049 |          79 |                       12,674 |                932 |             33,364 |       22,719 |         4,259 |            18,460 |       7,616 |        4,149 |            3,467 |             14,871 |            14,856 |                           15 |

`crossCheck agreed` / `coverage refusals` are already the Format-6 baseline table's "M2.3 confirmed / refused" column; repeated here beside the `m23Accounting` fields/lists/text split, which is not otherwise tabulated. Unconfirmed claims (per `.m23Accounting.unconfirmed`) are kept apart from this table, per the instruction to not conflate them with confirmed counts: canonical has 5 unconfirmed `list IteratorCandidate` and 5 unconfirmed `list VecCandidate` claims, not counted above as either confirmed or as population.

Historical comparison, canonical/`-O1` only:

| metric                                            |        old (pre-tidy) |        new (format 6) | old source                                                       |
| ------------------------------------------------- | --------------------: | --------------------: | ---------------------------------------------------------------- |
| fields: `Direct`                                  |                 3,408 |                 3,346 | [M2.3b — Accounting](#accounting-1), profile row `-O1`/A         |
| fields: `Dead`                                    |                     9 |                     2 | same                                                             |
| lists: flows (before)                             |                11,818 |                11,813 | [M2.3c — Accounting](#accounting-2), profile row `-O1`/A         |
| lists: `Iterator` / `Persistent` / `Vec` / `Lazy` | 727 / 1,925 / 32 / 30 | 722 / 1,925 / 27 / 30 | same                                                             |
| lists: `Unknown`                                  |                 9,104 |                 9,109 | same                                                             |
| text: flows (before)                              |                 4,431 |                 4,431 | [M2.3d — Accounting](#accounting-3), profile row `-O1`/A         |
| text: `Strong` / `Undecided` / `NotText`          |       185 / 2,561 / 2 |       185 / 2,561 / 2 | same                                                             |
| text: `Unknown`                                   |                 1,683 |                 1,683 | same                                                             |
| crossCheck checked / agreed / coverage refusals   |    4,401 / 4,391 / 10 |    4,332 / 4,322 / 10 | [M2.3 — What it found](#what-it-found), `-O1` (and matrix A) row |

#### 5. M2.4 — class-op targets, representation, erasure, totality, clone plans

Source: `m24.json` → `.accounting.targets` (`sites`, `exact`, `finite`, `unresolved`, `dict_bounded`); `.accounting.representation` (`boundaries`, `enumerated`, `one_representation`, `rewritable_as_one`, `claims`/`verified`); `.accounting.erasure` (`values`, `verified_values`, `params`, `verified_params`, `param_totality`); `.accounting.erasure.plans` (labelled "dictionary clones (E7-OWNER-CLONES)" and "closure clones (H15-OWNER-CLONES)").

**Targets and representation**

| profile   | class-op sites | exact | finite | unresolved | dict-bounded | boundaries | enumerated | one-representation | rewritable-as-one |
| --------- | -------------: | ----: | -----: | ---------: | -----------: | ---------: | ---------: | -----------------: | ----------------: |
| canonical |            554 |     0 |      0 |        554 |          111 |      5,572 |        265 |                 92 |                70 |
| A         |            554 |     0 |      0 |        554 |          111 |      5,572 |        265 |                 92 |                70 |
| B         |            576 |     0 |      0 |        576 |          131 |      6,337 |        399 |                146 |               124 |
| C         |            584 |     0 |      0 |        584 |          133 |      8,080 |        503 |                201 |               180 |
| D         |            584 |     0 |      0 |        584 |           65 |     33,967 |      1,929 |                730 |               709 |
| E         |            584 |     0 |      0 |        584 |           65 |     31,559 |      1,907 |                718 |               697 |
| F         |            585 |     0 |      0 |        585 |           65 |     31,582 |      1,913 |                717 |               696 |

**Erasure and totality** (values / params totals, and the `param_totality` triple `[ProvenTotal, MustPreserveForce, Unknown]`)

| profile   | values | verified values | params | verified params | totality: ProvenTotal | totality: MustPreserveForce | totality: Unknown |
| --------- | -----: | --------------: | -----: | --------------: | --------------------: | --------------------------: | ----------------: |
| canonical |    190 |             103 |    218 |              41 |                   119 |                           0 |                99 |
| A         |    190 |             103 |    218 |              41 |                   119 |                           0 |                99 |
| B         |    190 |             103 |    212 |              32 |                   111 |                           0 |               101 |
| C         |    190 |             103 |    224 |              39 |                   122 |                           0 |               102 |
| D         |    195 |             121 |    224 |              32 |                    76 |                           0 |               148 |
| E         |    195 |             121 |    224 |              32 |                    76 |                           0 |               148 |
| F         |    195 |             121 |    232 |              32 |                    84 |                           0 |               148 |

`values`/`params` above are totals; the `Erasable`/`WithObligation`/ `WithClone`/`Preserve`/`Unresolved` verdict split behind them (`.accounting.erasure.value_verdicts` / `.param_verdicts`, same order) is not otherwise tabulated per profile:

| profile   | value verdicts: Erasable | WithObligation | WithClone | Preserve | Unresolved | param verdicts: Erasable | WithObligation | WithClone | Preserve | Unresolved |
| --------- | -----------------------: | -------------: | --------: | -------: | ---------: | -----------------------: | -------------: | --------: | -------: | ---------: |
| canonical |                      103 |              0 |         0 |       87 |          0 |                       37 |              0 |         4 |       84 |         93 |
| A         |                      103 |              0 |         0 |       87 |          0 |                       37 |              0 |         4 |       84 |         93 |
| B         |                      103 |              0 |         0 |       87 |          0 |                       29 |              0 |         3 |       85 |         95 |
| C         |                      103 |              0 |         0 |       87 |          0 |                       35 |              0 |         4 |       89 |         96 |
| D         |                      121 |              0 |         0 |       74 |          0 |                       28 |              0 |         4 |       89 |        103 |
| E         |                      121 |              0 |         0 |       74 |          0 |                       28 |              0 |         4 |       89 |        103 |
| F         |                      121 |              0 |         0 |       74 |          0 |                       28 |              0 |         4 |       97 |        103 |

Value verdicts sum to `values` on every profile; param verdicts sum to `params` (e.g. canonical params: `37 + 0 + 4 + 84 + 93 = 218`).

**Clone plans** — dictionary clones (E7-OWNER-CLONES) and closure clones (H15-OWNER-CLONES), each as cardinality-sum / clones-planned / owners-planned / owners-refused / verified

| profile   | dict: cardinality sum | dict: clones | dict: owners planned | dict: owners refused | dict: verified | closure: cardinality sum | closure: clones | closure: owners planned | closure: owners refused | closure: verified |
| --------- | --------------------: | -----------: | -------------------: | -------------------: | -------------: | -----------------------: | --------------: | ----------------------: | ----------------------: | ----------------: |
| canonical |                     8 |            4 |                    4 |                    0 |              4 |                      512 |              71 |                      22 |                      66 |                22 |
| A         |                     8 |            4 |                    4 |                    0 |              4 |                      512 |              71 |                      22 |                      66 |                22 |
| B         |                     6 |            3 |                    3 |                    0 |              3 |                      919 |              86 |                      25 |                     119 |                25 |
| C         |                     8 |            4 |                    4 |                    0 |              4 |                    1,185 |              90 |                      26 |                     156 |                26 |
| D         |                    12 |            7 |                    2 |                    0 |              2 |                    5,124 |             202 |                      60 |                     756 |                60 |
| E         |                    12 |            7 |                    2 |                    0 |              2 |                    5,048 |             202 |                      60 |                     744 |                60 |
| F         |                    12 |            7 |                    2 |                    0 |              2 |                    5,088 |             226 |                      72 |                     738 |                72 |

Note on terminology, per the instruction not to confuse these: `enumerated` (a boundary's producer set is fully known) is not `one_representation` (that set needs exactly one representation), which is not `rewritable_as_one` (the stronger, per-rewrite question); all three are separate columns above, taken as-is from `.accounting.representation`.

Historical comparison, canonical/`-O1` only:

| metric                                                                          |            old (pre-tidy) |           new (format 6) | old source                                                                                                                                            |
| ------------------------------------------------------------------------------- | ------------------------: | -----------------------: | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| class-op sites, per-module census population                                    |                       565 |                      554 | [M2.4b — The answer](#the-answer)                                                                                                                     |
| class-op sites, whole-program `Exact`                                           |                         7 |                        0 | [M2.4c — What it found](#what-it-found) (see also this baseline's `Range`-selector note above)                                                        |
| class-op sites, whole-program `Unresolved`                                      |                       558 |                      554 | same                                                                                                                                                  |
| representation boundaries                                                       |                     5,574 |                    5,572 | [M2.4d′ — verdicts, before → after](#the-verdicts-before--after--o1)                                                                                  |
| representation: enumerated                                                      |                       252 |                      265 | same                                                                                                                                                  |
| representation: one_representation                                              |                        84 |                       92 | same                                                                                                                                                  |
| representation: rewritable_as_one                                               |                        66 |                       70 | same                                                                                                                                                  |
| erasure values: `Erasable`/`WithObligation`/`WithClone`/`Preserve`/`Unresolved` |  102/0/0/89/0 (total 191) | 103/0/0/87/0 (total 190) | [Erasure tables, before → after](#erasure-tables-before--after)                                                                                       |
| erasure params: `Erasable`/`WithObligation`/`WithClone`/`Preserve`/`Unresolved` |  36/0/4/84/92 (total 216) | 37/0/4/84/93 (total 218) | same                                                                                                                                                  |
| totality params: ProvenTotal/MustPreserveForce/Unknown                          |      118/0/98 (total 216) |     119/0/99 (total 218) | same                                                                                                                                                  |
| dictionary clone plan: cardinality sum / clones / owning functions              |                 8 / 4 / 4 |                8 / 4 / 4 | [Clone planning is per owner](#clone-planning-is-per-owner-not-per-parameter)                                                                         |
| closure clone plan: clones / owners planned / owners refused                    | 68 / 21 / 66 (post-M2.4h) |             71 / 22 / 66 | [M2.4h correction](#correction-m24h--four-defects-the-owners-review-of-m24-found) via [M2.4d′](#3-the-clone-count-was-a-sum-of-per-parameter-numbers) |

The dictionary clone plan (E7) is unchanged across the re-baseline: same cardinality sum, same clone count, same four owning functions. The closure clone plan (H15) moves by 3 clones (68 → 71) and 1 owning function (21 → 22); no cause is attributed here, per the instruction to leave site-level attribution open.

#### 6. Reachability — the 28-module canonical table

Source: `reachability.json` → `.reachability.accounting.modules`, canonical profile only, all 28 modules (A is byte-identical to canonical). Totals: 13,752 top, 9,795 live, 3,957 dead (`dead_no_refs + dead_only_from_dead`).

| module                          |        top |      live | dead_no_refs | dead_only_from_dead |
| ------------------------------- | ---------: | --------: | -----------: | ------------------: |
| Main                            |        501 |       409 |           17 |                  75 |
| Paths_ShellCheck                |         63 |         5 |            9 |                  49 |
| ShellCheck.AST                  |      1,083 |        98 |          320 |                 665 |
| ShellCheck.ASTLib               |        345 |       264 |           43 |                  38 |
| ShellCheck.Analytics            |      2,667 |     2,646 |            6 |                  15 |
| ShellCheck.Analyzer             |          8 |         3 |            1 |                   4 |
| ShellCheck.AnalyzerLib          |        649 |       327 |           81 |                 241 |
| ShellCheck.CFG                  |        993 |       355 |           94 |                 544 |
| ShellCheck.CFGAnalysis          |        867 |       292 |          100 |                 475 |
| ShellCheck.Checker              |         36 |        33 |            1 |                   2 |
| ShellCheck.Checks.Commands      |      1,240 |     1,184 |            6 |                  50 |
| ShellCheck.Checks.ControlFlow   |         14 |         6 |            3 |                   5 |
| ShellCheck.Checks.Custom        |          9 |         2 |            2 |                   5 |
| ShellCheck.Checks.ShellSupport  |        901 |       870 |            2 |                  29 |
| ShellCheck.Data                 |      1,340 |     1,335 |            1 |                   4 |
| ShellCheck.Fixer                |         96 |        30 |           10 |                  56 |
| ShellCheck.Formatter.CheckStyle |         53 |        47 |            2 |                   4 |
| ShellCheck.Formatter.Diff       |        155 |       106 |            5 |                  44 |
| ShellCheck.Formatter.Format     |         62 |        19 |           14 |                  29 |
| ShellCheck.Formatter.GCC        |         22 |        16 |            2 |                   4 |
| ShellCheck.Formatter.JSON       |         66 |        44 |            5 |                  17 |
| ShellCheck.Formatter.JSON1      |         88 |        48 |            7 |                  33 |
| ShellCheck.Formatter.Quiet      |         11 |         4 |            2 |                   5 |
| ShellCheck.Formatter.TTY        |         93 |        87 |            2 |                   4 |
| ShellCheck.Interface            |        678 |        30 |          136 |                 512 |
| ShellCheck.Parser               |      1,645 |     1,487 |           24 |                 134 |
| ShellCheck.Prelude              |         42 |        29 |            6 |                   7 |
| ShellCheck.Regex                |         25 |        19 |            4 |                   2 |
| **Total (28 modules)**          | **13,752** | **9,795** |      **905** |           **3,052** |

`905 + 3,052 = 3,957`. This is the "authoritative per-module live table" still requested by todo.md; the pointers from the historical milestone sections to it are not added here.

## M3d — polymorphism and typeclass specialization

A polymorphic binding has no single Rust function. `poly :: forall a. a -> a` is one Core binding and as many Rust functions as the program uses it at, so the unit the lowering owns stops being a binding and becomes an **instance**: a top-level binding together with the closed types and the proven-unique dictionaries its leading lambdas were bound to.

### What a dictionary turns out to be

Reading the Core rather than assuming: a class dictionary is an ordinary single-constructor data value, and a class method selector is an ordinary case on it.

```text
area   = \@a (v :: Shape a) -> case v of C:Shape v2 v3 v4 -> v2
$fShapeSq = C:Shape @Sq $fShapeSq_$carea $fShapeSq_$cname $fShapeSq_$cperimeter
```

So dispatch needed no new NIR operation — `Construct`, `MatchData` and `Apply` already express it. What it needed was evidence: the selector's field index is read out of the selector's own body, and an instance dictionary's fields out of the constructor application its binding is. GHC's `IdDetails` (`[ClassOp]`, `[DFunId]`) corroborates each shape. An occurrence name is never the proof.

At `-O0` this is not an optimisation but the only way the program can be emitted at all. GHC's unoptimised desugaring produces a knot:

```text
$fShapeSq = C:Shape @Sq $carea1 $cname1 $cperimeter1
$cname1   = $dmname @Sq $fShapeSq
```

a recursive CAF the emitter refuses. Resolving `name @Sq $fShapeSq` to `$cname1` statically, and `$cname1` to the instance `$dmname` at `([Sq], [$fShapeSq])`, breaks the knot because the dictionary is never built.

### The rules

| Rule              | Source shape                                                                  | What the instance key absorbs                               |
| ----------------- | ----------------------------------------------------------------------------- | ----------------------------------------------------------- |
| `InstantiateTop`  | `f @T…` with no value arguments                                               | the type arguments                                          |
| `ResolveInstance` | `f @T… d…` whose every value argument is a proven-unique dictionary           | the type and dictionary arguments; the spine is a reference |
| `ResolveMethod`   | `sel @T… d args…` where `sel` is a class-op selector and `d` is proven unique | the selector and the dictionary; the call names the method  |
| `CallTop`         | anything else that saturates a known target                                   | the leading dictionary arguments, if any                    |

A dictionary resolves when it is a top-level binding whose right-hand side is a saturated class-constructor application, a dictionary the instance already bound, a superclass field of one of those, or a top-level name whose right-hand side is one of those read in its own arguments' scope. **Anything else keeps its runtime dispatch**: the dictionary stays an ordinary value, the selector stays a constructor match and the call stays an indirect application. Nothing is guessed, and nothing silently falls back to a different meaning.

### Substitution, and what makes an instance the same instance

Substitution is capture-safe: a quantifier whose variable occurs free in a replacement is renamed before the replacement is inserted, so `forall b. a -> b` at `a := b` cannot become `forall b. b -> b`. Nothing rewrites Core; an instance reads every type through one substituted view of the module's immutable type table.

Instance identity is a canonical key built from the *structured* type — stable type-constructor names and de Bruijn levels, with every string length-framed — so two keys are equal exactly when the types are alpha-equivalent. Equal keys intern to one instance, which is what makes a recursive cycle terminate: a self-call finds the instance it is already inside.

Growth is bounded explicitly. An instance chain whose type arguments keep growing (`f @a` calling `f @(L a)`) is refused with the chain that produced it, against a nesting budget and a per-owner budget, rather than being allowed to run. Detection does not depend on noticing the pattern; it depends on the budget, so no chain can outrun it.

### Constructor evidence is a whole-world fact

A function from one module specialized at a type declared in another needs that other module's constructor evidence, so every layout query now searches the loaded world. Where several modules describe the same constructor, they must agree; a disagreement is an error rather than a first-wins pick.

The dump gained four additive facts per constructor, because GHC's `isVanillaDataCon` is false for a class dictionary with a superclass — the superclass is a *constraint* field — and that is not distinguishable from an existential or a GADT equality without asking. `newtype`, `unlifted`, `unboxed`, `existential`, `equalities` and `class` are each a separate GHC fact; older dumps carry none of them and keep the conservative answer.

Extending the format means re-extracting every dump, so the M1–M2.4 reports were recaptured against the new ones (`mise run baseline:reports`, all seven profiles, verification passing on each). All eight text reports — `stats`, `laziness`, `parsec`, `higher`, `classops`, `dictflow`, `m24`, `verify-m24` — are byte-identical to the ones taken before. Three JSON forms differ. Every number in them is unchanged and so is the count of scalar paths (`higher` 206,177, `laziness` 379,789, `parsec` 259,854); the textual differences are GHC uniques, in `laziness.json`'s `"unique"` fields and in the free type-variable names embedded in `higher.json` and `parsec.json`'s shape keys. A unique is a per-compilation serial number that nothing keys by.

### Verification

The verifier re-derives the substitution and the dictionary scope **from the source and the caller's stated instance**, never from the candidate's own evidence, then checks every type, target and origin against them. Corruption tests cover a wrong type argument, a wrong parameter or result type, wrong instantiation provenance, a wrong type argument on a call site, a missing or swapped dictionary, wrong dictionary provenance, and a method target swapped for the other method of the same dictionary. Each is rejected.

### Results

The canary compares generated Rust against the GHC oracle in both profiles over **13,096 differential cases**, in optimised and overflow-checked builds. Eleven new entries cover one function at several types, cross-module instantiation, a polymorphic higher-order argument, recursive specialization, a nested type argument, two instances of one class, a default method, a superclass field read, a cross-module class, a parameterized instance and a method used as a value.

Canonical NIR coverage, per owner at its own signature (`mise run lower:coverage`): **5,402 lowered / 4,393 refused / 3,957 dead**, against 5,395 / 4,400 before. That measure barely moves, and should not: a polymorphic owner still cannot be lowered at its own open signature, and what specialization changes is which *instances* exist.

The measure this milestone moves is the instance survey (`mise run lower:specialize`), every live binding as a root:

```text
Instances: 9811 = 5407 lowered + 4404 refused, over 9795 owners
Specialized: 16 at type or dictionary arguments, of which 0 carry a dictionary
```

### The blockers, ranked

```text
   2891  imported binding is outside the loaded world
    498  unsupported constructor field carrier
    389  algebraic case result mismatch
    338  switch requires Int# scrutinee, Int#/Int result and no alternative binders
     97  type application requires closed structured types
     55  lazy let requires a supported non-recursive lifted value, not a join point
     24  type arguments must precede value arguments
     23  unsupported constructor family or representation
     21  casts need source and target type evidence
     14  instance reference needs closed structured type arguments
     14  local functions require supported closed signatures
      8  call arguments require supported Int#/Int computations or shared references
      8  unsupported local function parameter
      7  direct call must match known target arity
      4  local functions require monomorphic value lambdas
      4  non-exhaustive algebraic case
      4  unsupported case scrutinee carrier
      2  constructor type arguments or saturation mismatch
      1  boxed case result type mismatch
      1  lazy let requires one non-recursive binding
      1  unsupported strict case type or alternative
```

Read against the milestone's own question, this ranks the blockers the survey reached, and nothing beyond them. The dominant one is the external library boundary — 2,891 references into `base`, `containers`, `bytestring` and the rest, which are outside the 28-module dump — followed by carrier coverage for constructor fields, algebraic case results and non-`Int#` switches. The specialization-shaped residue among them is small: 97 open type applications, 24 interleaved spines, 14 open instance arguments and 7 arity mismatches.

What that establishes is the subset now implemented, not the size of what is left. The survey discovers an instance only through a call site it has already lowered, so each of the 4,404 refusals hides its own requirements, and the specialization those hidden instances would demand is unmeasured. The ranking above becomes an answer about substantial pure programs only once the carrier and boundary blockers are cleared and a survey reaches past them.

Two further facts worth stating rather than leaving implied. `Main.main` cannot be a survey root at all: its Core opens with a cast through the `IO` newtype, so a single-root survey stops on the first instruction. And only 16 specialized instances appear on the canonical `-O1` dump, none of them carrying a dictionary, because `-O1` has already specialised the dictionaries away before the dump is taken. The dictionary machinery is therefore exercised by the canary's unoptimised profile and the unit fixtures, and by no canonical instance.

## M4 — characters, string literals, casts and the external boundary

M3d's ranking named the external library boundary as the dominant blocker, 2,891 of 4,404 refused instances. It did not name *which* bindings, so the first thing this milestone added was that question's answer. `lower --nir --specialize` now prints two further sections: the external bindings the survey asked for and could not find, ranked by refusals, and — for every other refusal whose site knew one — the type it is about. A reason says which rule stopped an instance; the subject says which type would have to be carried for that rule to pass.

The answer was concentrated far more than expected:

```text
    2317  $ghc-prim$GHC.CString$unpackCString#
      70  $base$GHC.Base$++
      60  $base$GHC.List$elem
      49  …Text.Regex.TDFA.String$compile
      34  $ghc-prim$GHC.Classes$$fOrdList_$s$ccompare1
      32  $ghc-prim$GHC.Prim$dataToTag#
      31  $base$GHC.Base$eqString
```

80% of the external boundary was one binding. A Haskell string literal is not a value in Core: it is an `Addr#` literal handed to one of `GHC.CString`'s unpackers, which walks the bytes into a lazy `[Char]`. Every module that mentions a string was stopped by it.

### The dump had to carry the literal, not its rendering

`ppr` escapes. A `LitString`'s bytes reach the dump through `pprHsBytes` and a `LitChar` through `pprPrimChar`, so anything outside printable ASCII arrives as an escape sequence in GHC's own spelling, and a number's width is not in its text at all. Reconstructing values from that would be re-implementing GHC's escaping backwards.

The plugin now emits the value beside the rendering: `codepoint` for a character, lower-case hex `bytes` for a string, and a decimal `value` with its `numType` for a number. Every decoder reads those; `pretty` is a diagnostic and is parsed nowhere. The fields are additive, and a dump taken before they existed carries none of them, so a consumer that needs an exact value refuses rather than guessing — which is what re-extracting every dump is for.

The corruption tests moved with them. Forging `pretty` no longer changes the emitted code, and a test asserts that; what the tests corrupt now is the value, the `LitNumType` and the code point, because that is what a decoder reads.

### `Char#`, and what GHC actually does with it

`Char` needed no carrier of its own. `C#` is an ordinary single-constructor record in the dump's constructor table, and once `Char#` joined `Int#` as a supported unboxed scalar, `Char` became an ordinary algebraic value and `[Char]` an ordinary list. What needed adding was the operations: the six comparisons, `ord#` and `chr#`, each with its exact GHC signature asserted and the site checked against it.

The canary caught the thing reading the primop table would not have told us. GHC orders `Char#` as an **unsigned machine word**, and `chr#` narrows nothing, so `chr# -1#` is the largest `Char#` rather than the smallest, and `ord#` after it returns the original word. Signed comparison agreed with GHC on every code point and disagreed on 24 of the 960 differential cases the new fixtures run. The orderings are emitted as unsigned; equality is unaffected either way.

`Int#` and `Char#` share the `i64` carrier, but not the runtime field tag: `Field::Char` is separate from `Field::Int64`, so a mixed-up field is a panic rather than a silently wrong character.

### The unpackers

Only the saturated spine is recognised, so an `Addr#` never becomes a value: this backend has no pointer carrier and refuses one anywhere else. Full laziness floats a literal out to its own top-level `Addr#` binding, so the address argument is resolved through the loaded world as well as read in place.

The decoders reproduce `GHC.CString`'s own arithmetic rather than Rust's UTF-8 handling, because GHC's does not validate and accepts what Rust's rejects: GHC encodes a NUL inside a literal as the overlong `C0 80`. A `LitString`'s bytes carry no terminator — the code generator adds it — so the end of the array ends the string, and an embedded NUL still ends it early.

The list is built one cell at a time behind a thunk, so `head` of a long literal decodes one character and a literal that is never demanded decodes none. The constructor names the cells carry come from the world's own layout evidence, handed to the runtime; the runtime assumes no shape.

### Two more things the fixtures forced

`GHC.Base.(++)` is implemented rather than linked. At `-O1` GHC rewrites `"a" ++ "b"` into `unpackAppendCString#`, but at `-O0` it does not, and `++` was the second-ranked external anyway. It is lazy in both arguments and in the spine: forcing the result to WHNF forces only the left list to WHNF, and the right list is reached rather than copied.

A `let` at an unboxed type is Core's strict binding, not a thunk — GHC admits one only when its right-hand side is ok for speculation, and it is evaluated where it stands. It carries `StrictBinding` rather than `LazyBinding`, and the verifier decides which rule to expect from the source type rather than reading it back off the candidate.

### What is not used as evidence

An imported Id with no unfolding carries whatever arity *this compilation* inferred: `unpackCString#` is arity 0 under `-O0` and arity 1 under `-O1`, for the same function. That field is a fact about the dump. Corroboration for these entries is the site instead — a spine saturated at the entry's own argument count, an address argument that is a literal, arguments lowered *at* the asserted argument types and a result compared with the asserted result type, which in well-typed Core pins the signature. A primop's arity is intrinsic and survives `-O0`, so that check stays where it was.

### Casts, and the newtypes underneath them

A coercion has no runtime content — `Cast e co` evaluates exactly as `e` does — which is why GHC's dump threw them away entirely and why 22 instances stopped at "casts need source and target type evidence" with nothing to decide on. The plugin now emits `coercionKind`: the two types the coercion relates, interned in the module's own type table, and its role.

That alone answered almost nothing. Naming the types showed that 20 of the 22 were crossings into a **newtype** — 16 of them `ShellCheck.AST.Id` — and a newtype had no carrier here at all, because `boxed_record` excludes one and every carrier question went through it.

So the answer was not a cast rule but a representation. A newtype has no runtime existence: `newtype N = MkN T` *is* `T` once the program runs, which is exactly why GHC turns every wrap and unwrap into a cast rather than a constructor. Every carrier question is now asked of the representation, peeled from the declaring module's own evidence — `newtype`, a representation arity of one, a family of one — with the field read out of the worker's signature and the peeling bounded, so a dump claiming a cycle refuses rather than loops.

A cast is then erased to a `Move` when both sides carry the same way, and refused with both type heads named when they do not. Carrier agreement, not the coercion's role, is what the check rests on: the role is provenance, and the property that matters is that this backend's typed NIR reads the value the same way on both sides. Every emitted instruction is checked against both definitions of carrier — the backend's structural one and the world's evidence-based one — so a type that reaches emission without a carrier is an error rather than an `HData` nothing can build.

Three smaller things fell out, each a real shape rather than a special case: a cast in argument position, a cast as a function's whole body, and an application whose *head* is a cast, which is an indirect call whose callee type the cast itself names.

Casts fell from 22 refusals to 4 — two whose source has no carrier, two that change it. Constructor-field carriers fell from 367 to 183, because a newtype field is now carried as what it wraps.

Two refusals are gated rather than merely expected. A recursive value is refused for its type when it is the entry and for its dependency cycle when an `Int#` entry reaches it, with the previous output left untouched in both cases; the canary asserts each message. Extending the dump means re-extracting it, so all seven profiles were recaptured and re-verified (`mise run baseline:reports`): 0 disagreements on every one, `A5-IN-WORLD-MISSING` still 0, 28 modules, dump format 6.

### Results

The canary compares generated Rust against the GHC oracle in both profiles over **17,016 differential cases**, up from 13,096, in optimised and overflow-checked builds. Twenty new entries cover the code-point round trip at the boundaries, all six character comparisons, a `Char#` switch with literal alternatives, a character in a constructor field, an empty literal, ASCII and non-ASCII literals, indexing inside and past the end, an embedded NUL, the top of Latin-1, two literals appended, one literal read twice, a string traversal that is built and never demanded, a newtype wrapped and unwrapped, a newtype wrapping a newtype, and a newtype over a function.

Canonical NIR coverage, per owner at its own signature (`mise run lower:coverage`): **8,067 lowered / 1,728 refused / 3,957 dead**, against 5,402 / 4,393 before. The instance survey (`mise run lower:specialize`) moves with it: **9,812 = 8,072 lowered + 1,740 refused**, against 5,407 / 4,404. Seventeen instances are specialized at type or dictionary arguments, up from sixteen, and none of them carries a dictionary.

### The blockers, ranked again

```text
     546  imported binding is outside the loaded world
     369  algebraic case result mismatch
     351  switch requires an unboxed scalar scrutinee, a supported result …
     183  unsupported constructor field carrier
      98  type application requires closed structured types
      38  a let requires a supported non-recursive value, not a join point
      26  unsupported constructor family or representation
      24  type arguments must precede value arguments
      24  unsupported local function parameter
       7  partial application needs a carried function type
```

Every one of those is a *type* that has no carrier, standing behind a rule that reads like a property of the call. That is why the second ranking exists.

and, by the type each is about:

```text
     109  [] /1                          (unsupported constructor field carrier)
      95  (#,#) /4                       (algebraic case result mismatch)
      92  [] /1                          (switch … unboxed scalar scrutinee)
      83  (#,#) /4                       (switch … unboxed scalar scrutinee)
      76  Solo# /2                       (algebraic case result mismatch)
      76  RWST /5                        (algebraic case result mismatch)
      68  Solo# /2                       (switch … unboxed scalar scrutinee)
      48  Checks.Commands.CommandCheck   (unsupported constructor field carrier)
      41  WriterT /3                     (algebraic case result mismatch)
      39  (#,,#) /6                      (switch … unboxed scalar scrutinee)
```

The external boundary fell from 2,891 refusals to **546**, over 95 distinct bindings in 35 modules — it *rose* from 482 once casts and newtypes let the survey reach further, which is what a lower bound does when the floor moves. What replaced it at the top is not a boundary at all: **unboxed tuples** — `(#,#)`, `Solo#`, `(#,,#)`, `(##)` and the wider ones — account for **448** refusals, spread over the case-result, switch and constructor-family rules. Those are GHC's worker/wrapper returns and state tokens, and they are a representation this backend does not carry at all, not a library it cannot find. The monad transformer stacks (`RWST`, `WriterT`, `StateT`, `ReaderT`) are the next cluster, then `containers`' `Map` and `Set`.

### The dependency list as M4 left it

These are the bindings the survey reached and refused, by package, as the ranking stood when M4's boundary work finished — 482 refusals over 82 bindings, then 546 over 95 once casts and newtypes pushed the survey deeper. It is kept as M4's record; the current list is in [Remaining runtime and external dependencies](#remaining-runtime-and-external-dependencies), which now stands at 231 over 46. Every count is a lower bound: a refused instance never revealed its own requirements.

| Package                  | Refusals | The bindings                                                                                                                                                           |
| ------------------------ | -------: | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `base` `GHC.List`        |      115 | `elem`, `lastError`, `head1`, `errorEmptyList`, `lvl`, `dropWhile`, `takeWhile`, `$wlenAcc`, `reverse`, `reverse1`, `filter`, `zip`, `badHead`                         |
| `base` `GHC.Base`        |       56 | `eqString`, `map`, `id`, `maxInt`, `++_$s++`, `++`, `$fApplicativeList_$cpure`, `$fMonoid(,,,)`                                                                        |
| `ghc-prim` `GHC.Prim`    |       52 | `dataToTag#`, `reallyUnsafePtrEquality#`, `leWord#`, `andI#`, `orI#`, `tagToEnum#`                                                                                     |
| `regex-tdfa`             |       49 | `Text.Regex.TDFA.String.compile`                                                                                                                                       |
| `ghc-prim` `GHC.Classes` |       45 | `$fOrdList_$s$ccompare1`, `$fOrdList_$ccompare`, `compareInt#`, `$fEqList`, `$fEqList_$c==`, `$fEq(,)`, `$fEq(,,)`, `neChar`                                           |
| `base` `Data.OldList`    |       30 | `isPrefixOf`, `lines`, `unlines`, `sortBy`, `words`                                                                                                                    |
| `base` `GHC.Err`         |       28 | `error`, `errorWithoutStackTrace`, `undefined`                                                                                                                         |
| `base` exceptions        |       27 | `Control.Exception.Base.patError`                                                                                                                                      |
| `containers`             |       20 | `Data.Set.Internal` `insertMax`, `$fEqSet`, `$fOrdSet`; `Data.Map.Internal` `$fEqMap_$c==`, `balanceR`, `keys1`, `keysSet`                                             |
| `transformers` / `mtl`   |       14 | the `Applicative`/`Functor`/`Monad` dictionaries of `StateT`, `WriterT`, `RWST`, and `MonadReader`/`MonadWriter` for them                                              |
| `base` `GHC.Show`        |        9 | `$w$cshowsPrec15`, `$fShow(,)_itos'`                                                                                                                                   |
| `base` IO and env        |        9 | `GHC.IO.Handle.Text.hPutStr2`, `System.Environment.getEnv1`, `System.Exit.exitFailure1`, `System.Console.GetOpt.usageInfo`                                             |
| `ghc-bignum`             |        5 | `integerAdd`, `integerEq`, `integerGe`, `integerLe`, `integerToInt#`                                                                                                   |
| `base` `GHC.Ix`          |        5 | `$w$sindexError`                                                                                                                                                       |
| `ghc-prim` `GHC.Magic`   |        4 | `runRW#`                                                                                                                                                               |
| `filepath`               |        3 | `joinDrive`, `dropTrailingPathSeparator`                                                                                                                               |
| `aeson`                  |        2 | `$fMonoidSeries_$c<>`                                                                                                                                                  |
| `base` other             |        9 | `Data.Maybe.fromJust1`, `GHC.Maybe.$fEqMaybe1`, `GHC.Unicode.$wisAlpha`, `Text.ParserCombinators.ReadP.run`, `Data.List.NonEmpty.cycle7`, `Data.Version.$wshowVersion` |
| `parsec`                 |        2 | `Text.Parsec.Prim.$fApplicativeParsecT2`                                                                                                                               |

Three groups stand apart from the rest. `error`, `errorWithoutStackTrace`, `patError`, `undefined`, `lastError`, `head1`, `errorEmptyList` and `$w$sindexError` are the **error behaviour** the milestone brief names: they diverge, and nothing yet expresses a diverging call. `hPutStr2`, `getEnv1`, `exitFailure1` and `runRW#` are **IO**, which is the next milestone's subject. `compile` from `regex-tdfa` is the one genuinely foreign dependency in the list.

What is *not* here, because it is now implemented, is the whole `GHC.CString` family: 2,359 refusals in M3d, none now.

### What this milestone did not do

Named here rather than left to be inferred from the ranking. **Byte-oriented operations** have no entry, and the reason is worth stating exactly rather than as "not needed". `bytestring` *is* referenced — `Data.ByteString.Builder` and `Data.ByteString.Lazy` from both JSON formatters, `Data.ByteString.Short.Internal.packCStringLen1` from `Main` — but the survey never reaches any of it, because every path leading there is refused earlier. So it is not absent from the program; it is behind the blockers, and every count here is a lower bound for exactly that reason. Building a `ByteString` carrier now would be guessing at a requirement the survey has not yet stated. **Recursive lazy value graphs** are still refused — the emitter rejects a dependency cycle through a value, and `h2r-rt`'s `Lazy::force` panics on re-entry rather than tying a knot; the canary now holds that refusal in place rather than leaving it to chance. **Partial application of a constructor or a primop** turned out not to be a blocker at all. That refusal used to say "direct call must match known target arity", which is four different things wearing one sentence; split apart, all 7 are an *uncarried component type* — five a function whose own argument has no carrier, two a `WriterT` — and the two reasons that would mean a partially applied primop or constructor fire zero times in the whole live set. A call at an arity the metadata disagrees with is no longer refused either: it is an indirect application, which is what it means, and the verifier rejects the old leaf rather than the new one. The four casts that remain are the two whose source has no carrier and the two that change it, which is the answer rather than a gap: a cast this backend cannot read the value through is exactly what must be refused.

The first thing the next slice should take is on none of those lists. It is **unboxed tuples**, which the ranking puts at 448 refusals and which nothing here touched. They are GHC's worker/wrapper returns and its state tokens, and they are a representation this backend does not carry at all rather than a library it cannot find.

## M5 — calls that do not return

**Safety correction:** dead-end recognition is analysis-only. Rust emission refuses any dependency closure containing `Exit::Diverge`, including one inside an unused thunk. Non-return does not establish whether a call loops, throws, evaluates its arguments or performs effects; replacing it with `exit(1)` was not semantics-preserving. The three optimized error fixtures now check NIR evidence and emission refusal. The M5 counts below record the earlier run, not proof of error-behavior support.

After this correction, the full canary passes **20,544 differential cases**. The 294 formerly executable unused-error cases are replaced by emission-refusal checks. NIR coverage remains an analysis measure, not a count of executable bindings.

Each oracle and generated-binary invocation now has a default ten-second deadline, configurable with `mise run canary --timeout-seconds 10`. Both output pipes are drained concurrently. A timed-out child is killed and reaped, and the case fails even if both implementations would time out. This covers direct executables, not descendant process trees, compilation or the boxed-test harness. Fixtures declare `expected_exit` (zero by default): an expected failure must match the exact code and both output streams, not merely agree with another failing process. Signals and unexpected oracle exits still fail.

### Executable stack-free errors

`errorWithoutStackTrace` now has an explicit `RaiseError` operation, separate from demand-only `Diverge`. Its saturated library signature requires `BoxedRep Lifted`, a lifted result and a lazy `[Char]` message. The independent verifier checks the source spine, arguments, result and rule. The runtime evaluates the message before printing `<executable>: <message>\n` and exiting 1 at the generated CLI's uncaught-error boundary. Unused failing arguments, shared thunks and constructor fields stay unevaluated. Empty cases over proven non-returning lexical top-level scrutinees preserve and force the actual computation instead of replacing it with a generic exit.

The canary checks plain, empty, Unicode, NUL, multiline, computed and nested-failing messages, unboxed results, and both outcomes of an error-bearing branch, in both Core profiles and both Rust compilation modes. A NUL truncates the printed diagnostic but does not skip evaluation of the remaining message. Diagnostic encoding drops surrogate code points and preserves GHC's unchecked byte encoding for out-of-range `chr#` values. Executable names are checked against each binary's actual basename; no other stderr content is normalized. Four forged error instructions per profile must be rejected by source verification. `error`, `patError`, call stacks and exception catching remain unsupported; arbitrary `Diverge` still refuses emission.

Validation after this correction: **21,132 regular differential comparisons plus 72 error/branch comparisons**, zero differences. Reusing the unchanged canonical dumps, `mise run --skip-deps lower:coverage` reports **8,265 lowered / 1,530 refused / 3,957 dead** (12 more lowered owners than the prior 8,253/1,542 baseline). These are source-verified NIR counts, not executable-program coverage; the historical milestone and instance-survey tables below retain their original measurements.

`error`, `patError`, `errorEmptyList`, `undefined` and the rest of that family were the largest single group behind the external boundary. They are ordinary imported bindings whose bodies this world does not contain, so the resolver could not lower them and 96 instances were refused for the one reason that covers every unlinkable import.

But a call to one of them has no result to lower. GHC's demand analysis has already proved the call is a dead end, and a dead end needs a terminator rather than a value.

### The evidence is GHC's, not a list of names

The plugin already records `DmdSig`'s divergence through GHC's own `isDeadEndDiv`, which is the predicate for "this does not return normally" and covers both `Diverges` and `ExnOrDiv`. It is a property GHC computed and wrote into the interface file, so it is read off the binding rather than guessed from what a name looks like. No allowlist was added, and adding `error` to one would have been the wrong shape: what matters is the proof, and a ShellCheck-local binding that GHC proves is a dead end gets the same treatment.

The arity comes from the same signature. `<S><S>b` says the bottom holds *after two arguments*; applied to one, `error` is a partial application and an ordinary value. So the demand signature states both facts the rule needs, and `IdInfo.arity` — which for an imported Id records what this compilation inferred rather than what the function is — states neither. A test holds both halves: without the divergence, and below the signature's own arity, the same spine stays an ordinary call.

The rule fires only for a binding this world cannot link. When the body *is* in the world it is lowered like any other, because a dead end is not one behaviour: `let x = x in x` loops, `error` stops, and only the body says which.

### What it lowers to, and what it does not reproduce

`Exit::Diverge { name, ty }` is a terminator, so the block has no successor and produces no value. It is the one exit that carries a type: a dead end inhabits every type, so unlike a return there is no value to read it off, and the block's context is the only thing that knows it. The verifier re-derives the spine from Core, checks the name against the source's own resolution and compares that type against the one the block was required to produce; three corruption tests cover a forged name, a forged rule and a forged source address.

The analysis accounts for the arguments without lowering them. This is insufficient evidence for execution: a message computation may itself diverge, and exception behavior is observable. Emission is refused until the actual call and argument semantics are implemented; there is no generic exit-code substitute.

### The evidence exists only at `-O1`

The earlier ten `errorWithoutStackTrace` oracle/refusal probes are superseded by the executable checks above. These are reported separately from the regular differential grid. Unicode diagnostic comparisons require a UTF-8 environment. Stack-free error execution does not depend on demand signatures and works at both `-O0` and `-O1`.

GHC turns the unboxed-result entry into an empty `case` over a top-level failing CAF. The analysis follows nested empty cases only when each result type matches its context and either the final external call or a lexical top-level binding's own demand signature proves saturated non-return. The source verifier repeats those checks and accounts for the full source subtree. This produces analysis-only `Diverge` NIR, not an executable shortcut; an empty case without that proof remains unsupported.

Measured, not assumed: in the `-O0` canary dump `$base$GHC.Err$error` carries `diverges=false`, an empty demand signature and arity 0, because GHC does not slurp the signature from the interface when optimisation is off — the same reason `IdInfo.arity` is unreliable there. So the rule cannot fire in the unoptimised profile at all, and the three new canary entries are compiled and run in the optimised profile only. That is now a property of a fixture row rather than something the runner assumes, and the unoptimised profile skips them instead of failing on them.

### Results

The canary compares generated Rust against the GHC oracle over **17,310 differential cases**, up from 17,016, with **117 evidence checks** beside them. Three new entries cover a failing argument passed to a function that ignores it, a failing computation bound by `let` and never demanded, and one failing thunk read twice and ignored twice. None is ever forced: if the backend evaluated a lazy binding eagerly, every one of them would abort instead of answering, at every one of the 49 boundary inputs.

Canonical NIR coverage, per owner at its own signature: **8,163 lowered / 1,632 refused / 3,957 dead**, against 8,067 / 1,728. The instance survey moves with it: **9,812 = 8,168 lowered + 1,644 refused**, against 8,072 / 1,740.

The external boundary falls from **546 refusals over 95 bindings in 35 modules** to **450 over 83 in 31**. `base:GHC.Err` leaves the ranking entirely (28 refusals), `base:Control.Exception.Base` drops from 27 to 6, and `base:GHC.List` from 124 to 86 as `lastError`, `errorEmptyList` and `badHead` stop being unlinkable imports and start being what they are.

Unboxed tuples remain the dominant blocker at 448, untouched by any of this.

## M6 — unboxed tuples

The ranking put them at 448 refusals, the largest single blocker and more than the entire external boundary. They are GHC's multi-value return: `(# a, b #)`, `Solo#`, `(##)` and the wider ones, produced by every worker/wrapper split and by the `State#` threading that `IO` and `ST` are built from.

### They are not a data type, and the dump already said so

An unboxed tuple has no heap object, no tag and no laziness. It *is* its components, side by side. GHC's own type system guarantees one is never bound lazily, stored in a lifted field or passed where a value is expected, so there is nothing to allocate and nothing to force.

The evidence was already in the dump. The plugin records `isUnboxedTupleTyCon || isUnboxedSumTyCon` as `unboxed` and `not (isLiftedTypeKind (tyConResKind ...))` as `unlifted`, alongside the family size and representation arity. A sum has one constructor per alternative and needs a discriminant to say which is present; a tuple has exactly one. So `unboxed && familySize == 1` is exactly the unboxed tuples, and it is GHC's count rather than a reading of the name `(#,#)`. No plugin change and no re-extraction were needed.

`Carrier::Tuple` joins the four others, and it is the one that holds no representation of its own: what its components are is read back from the type, and the emitted Rust type is built from theirs and nests as they do. `(# Int#, Int# #)` is `(i64, i64)`; `(# Int, Int #)` is `(HInt, HInt)`; `(# (# Int#, Int# #), Int# #)` is `((i64, i64), i64)`. `Solo#` needs Rust's trailing comma to be a one-tuple rather than a parenthesised type.

### A case on one is not control flow

The family has one constructor, so there is nothing to branch on. `Operation::UnboxedTupleField` names a component by position, and a `case` becomes one naming per binder followed by the body in the same block. That is what the `case` *is*, and calling it a `MatchData` with a single arm would have been describing it as something it is not.

GHC emits two forms and the rule has to take both. The constructor pattern names the components; a `DEFAULT` with no binders names only the case binder. At `-O0` an unboxed tuple case is usually the first wrapping the second — `case splitInt x y of ds { _ -> case ds of { (#,#) a b -> ... } }` — and rejecting the outer one refused every fixture until it was allowed.

The case binder is bound even when the source never reads it. That is what marks where the scrutinee's instructions end, and without it a nullary `(##)` — no components to project — would leave the boundary unstated. The verifier finds that naming by its source address, so a nested tuple case inside the scrutinee cannot be mistaken for it; an earlier version searched for the first projection instruction and mis-split on exactly that, which cost 22 instances their lowering until the anchor replaced the search.

A corruption test covers what a wrong answer here would look like: a projection reading component 1 where the source named component 0, a forged rule and a forged source address are each rejected.

### One emission rule was wrong before and only tuples revealed it

The function wrapper deferred any result that was not `i64`, on the assumption that everything else is lifted. An unboxed tuple is neither, and `(i64, i64)::defer(...)` does not compile. The condition is now `data::lifted`, which is the question that was always meant: a lifted result is returned as a thunk the caller forces, an unlifted one is returned as it is.

### Results

The canary compares generated Rust against the GHC oracle over **18,878 differential cases** at this point, up from 17,310, with **143 evidence checks**; the text-processing programs below take it to 20,838 and 163. Eight new entries cover a tuple built and taken apart, a tuple whose components feed another, `Solo#`, a three-tuple, lifted `Int` components, a tuple nested inside a tuple, a thunk in a component that is never demanded, and a component the body never names.

Canonical NIR coverage, per owner at its own signature: **8,253 lowered / 1,542 refused / 3,957 dead**, against 8,163 / 1,632. The instance survey: **9,821 = 8,261 lowered + 1,560 refused**, against 9,812 = 8,168 + 1,644.

Unboxed tuple *types* now account for about 53 refusals, down from 448. What is left is not the representation: 111 are `unboxed tuple case result mismatch`, where the case's own result is something else this backend cannot carry, and 14 are a component with no carrier.

### The lower bound moved, as it does

The external boundary *rose* from 450 refusals over 83 bindings to **592 over 103**, and `text-2.0.2:Data.Text.Show` appears in the ranking for the first time with 27. Nothing regressed. Every count in this document is a lower bound because a refused instance hides its own requirements, and clearing the blocker that stood in front of `text` is what made the survey reach it. A ranking that only ever fell would be measuring the wrong thing.

## Generated text-processing programs

The string fixtures up to this point were single operations: unpack a literal, walk it, index it. These are whole algorithms, and each is ordinary Haskell over `[Char]` translated from its own Core rather than a Rust implementation of the same idea wearing a Haskell name.

| entry              | what it does                                                         |
| ------------------ | -------------------------------------------------------------------- |
| `textWords`        | splits on a space and counts the fields                              |
| `textLines`        | splits on a newline                                                  |
| `textUnicodeWords` | the same split over non-ASCII text, including a four-byte code point |
| `textFind`         | naive substring search, returning the index or −1                    |
| `textReverse`      | reverses onto an accumulator, then indexes the result                |
| `textFilter`       | keeps the code points below a bound                                  |
| `textMap`          | shifts every code point through `ord#`/`chr#`                        |
| `textSlice`        | drops the first argument's worth and takes the second's              |
| `textZip`          | walks two literals together, summing the products                    |
| `textCompare`      | lexicographic comparison, returning −1, 0 or 1                       |

They build new cells one at a time rather than only reading a literal's, so a defect in the list machinery is a wrong answer at a boundary input rather than a refusal. `textSlice` is the one that reads both arguments, so each of the 49 boundary pairs slices differently instead of repeating one answer.

Three of them first reached `patError`. Matching two lists at once is not visibly exhaustive to GHC, which inserts the incomplete-pattern call, and at `-O0` there is no demand signature to prove it is a dead end — so they lowered at `-O1` and were refused at `-O0`. They are written exhaustively now, which puts the algorithm under test rather than GHC's incomplete-pattern machinery, and all ten run in both profiles.

**20,838 differential cases** in total, with **163 evidence checks**.

## Library list predicates

`eqString`, `elem` and `isPrefixOf` were the three largest external bindings: 84, 74 and 32 refusals. The dump records `hasUnfolding: false` for all three, so their bodies are implemented in the runtime against base 4.18.3.0's own equations:

```haskell
eqString []       []       = True
eqString (c1:cs1) (c2:cs2) = c1 == c2 && cs1 `eqString` cs2
eqString _        _        = False

elem _ []     = False
elem x (y:ys) = x == y || elem x ys

isPrefixOf [] _          = True
isPrefixOf _  []         = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys
```

`elem` and `isPrefixOf` take an `Eq` dictionary, and the `==` they call is the one that dictionary supplies. `Operation::ListPredicate` carries an `Equality` resolved from the dictionary argument in the source spine, and the source verifier resolves it again independently:

| dictionary                                   | at type  | equality                                                        |
| -------------------------------------------- | -------- | --------------------------------------------------------------- |
| `$ghc-prim$GHC.Classes$$fEqChar`             | `Char`   | ``eqChar (C# x) (C# y) = isTrue# (x `eqChar#` y)``              |
| `$ghc-prim$GHC.Classes$$fEqList_$s$fEqList1` | `[Char]` | `Eq [a]`'s `==` over `eqChar`, whose equations are `eqString`'s |

GHC specialises `Eq [a]` at both `[Char]` and `[[Char]]`, so the dictionary's name alone does not say which one it is. The call's type argument decides, and GHC's typing guarantees the dictionary is `Eq` of that type. Any other dictionary is refused as `an Eq dictionary this backend does not implement`, with the dictionary named. In ShellCheck that is `$fEqShell`, at 2 sites.

Every predicate returns a lazy `Bool`, and it forces only what its definition forces, in the same order: both spines in step with the left one first, the needle only once there is an element to compare it with, and the list only while the prefix still has elements.

### Fixtures

Eight entries cover empty inputs, non-ASCII text including a four-byte code point, and all 49 boundary input pairs. `stringEqualLazy`, `elemLazy` and `prefixLazy` put a failing computation where the definition must not look: the tail after the first mismatch, the list after the first match, and the list behind an empty prefix. `elemString` goes through the `Eq [Char]` dictionary and runs only in the optimized profile. At `-O0` the dictionary is a different expression, and the canary asserts that refusal. `stringEqualRule` uses `==`, which GHC's `eqString` RULE rewrites when optimising.

Ten forced-error probes pin the order of evaluation, because the error that appears shows which argument was forced first: the left spine before the right, the left element before the right, the list spine before the needle, the needle before the element, and the prefix before the list. For each of `stringEqual`, `elemChar` and `prefixOf`, five forgeries of the verified instruction must be rejected: a flipped equality, a different predicate, swapped operands, swapped `True` and `False`, and a wrong rule.

### `compare` at `[Char]`

`$fOrdList_$s$ccompare1` was the next binding, at 39 refusals. It is GHC's specialisation of `Ord [a]`'s `compare`, and every site applies it to two `String`s, so well-typed Core pins its type to `[Char] -> [Char] -> Ordering`. `Ord [a]` defines it as:

```haskell
compare []     []     = EQ
compare []     (_:_)  = LT
compare (_:_)  []     = GT
compare (x:xs) (y:ys) = case compare x y of
                          EQ    -> compare xs ys
                          other -> other
```

`Ord Char` does not define `compare`, so the element comparison is the class default, `if x == y then EQ else if x <= y then LT else GT`, which forces the left character first. GHC orders `Char#` as an unsigned word, so a negative `chr#` sorts after every code point. `Operation::CompareStrings` carries the `LT`, `EQ` and `GT` layouts from the world.

At `-O0`, `compare` at `String` is a class-method call on a dictionary built at runtime, so the three fixtures (`compareStrings`, `compareLazy`, `compareUnsigned`) and the three order probes run in the optimized profile only. `compareUnsigned` compares `chr#` of all 49 boundary input pairs, negative ones included. Three forgeries must be rejected: swapped operands, swapped `LT` and `GT`, and a wrong rule.

### Results

Canonical NIR coverage per owner: **8,434 lowered / 1,361 refused / 3,957 dead**, against 8,265 / 1,530 before these four externals. The instance survey: **9,830 = 8,449 lowered + 1,381 refused**, against 9,821 = 8,273 + 1,548. Of the 229 sites, 227 lower; the other 2 are the `$fEqShell` refusals. The canary passes **22,798 differential cases**, with 31 forced-error and branch probes in the optimized profile and 28 in the unoptimized one.

## Constructor tags and pointer equality

Three primops take type arguments, so they sit in the external table beside the library functions rather than in the monomorphic primop table. They resolve only as unbound globals whose `IdInfo` says `[PrimOp]` at the asserted arity.

| primop                                       | ShellCheck refusals | what it does                                                                        |
| -------------------------------------------- | ------------------: | ----------------------------------------------------------------------------------- |
| `dataToTag# :: a -> Int#`                    |                  39 | forces its argument and returns its constructor's position in the family, from zero |
| `reallyUnsafePtrEquality# :: a -> b -> Int#` |                  28 | returns 1 when both arguments are one heap object, forcing neither                  |
| `tagToEnum# :: Int# -> a`                    |                   3 | the nullary constructor at that position of an enumeration type                     |

`dataToTag#` is how GHC derives `Eq` and `Ord` for enumerations, and `tagToEnum# @Bool` turns the `Int#` comparison back into a `Bool`. The constructor family comes from the world's layouts, never from the name. The argument must be carried as data, and `tagToEnum#` also requires every constructor to be nullary. The emitted code matches on constructor names and panics on one outside the family.

`reallyUnsafePtrEquality#` is `Rc` identity. GHC allows false negatives, and `containers` uses the answer only to keep sharing, never to change a value. The canary fixture therefore chooses between two structurally equal values, and its output is the same whatever the answer is.

An unlifted argument to one of these calls, such as the `a# ==# b#` inside `tagToEnum#`, is now evaluated where it stands instead of being delayed. The verifier requires a delay only when the argument's type is lifted.

Fixtures: `tagColour` and `tagMaybe` call `dataToTag#` directly in both profiles. `colourEqual` and `colourCompare` go through the derived `Eq` and `Ord` instances. At `-O0` those instances are reached through `ghc-prim`'s class selectors, whose dictionary layout is not in the world, so they run in the optimized profile and the canary asserts the `-O0` refusal. A forced-error probe shows `dataToTag#` forcing its argument. Two forgeries of `tagColour`'s instruction, a reordered family and a wrong rule, must be rejected. The canary passes **23,582 differential cases**.

Canonical NIR coverage per owner: **8,457 lowered / 1,338 refused / 3,957 dead**, against 8,434 / 1,361. The instance survey: **9,830 = 8,472 lowered + 1,358 refused**. The three primops are gone from the external list. Coverage moved less than the 70 sites suggest, because the `Set` and `Map` code behind pointer equality now reaches its balancing functions: `containers` rose from 33 refusals to 67.

## ShellCheck's own bindings, run against GHC

The canary's fixtures are small Haskell programs written for each rule, and their Core is not ShellCheck's. GHC fuses, specialises and resolves dictionaries differently in a small module, so a fixture can pass while testing a different shape from the one the program uses. The library suite closes that gap for the bindings it can reach. It emits ShellCheck's own exported bindings from the canonical dump, and compares each with the same function called from a GHC-built driver (`compiler/canary/shellcheck/Main.hs`) that links the staged ShellCheck tree `mise run extract` prepares. `mise run canary:library` builds that driver, and `mise run canary` runs the suite after both profiles.

The entry point now reads `String` arguments and prints results exactly as `show` does: `Int` with its precedence rule, `Char` and `String` through `showLitChar` (decimal escapes, `\&` before a digit, `\SO\&H`, the `asciiTab` names), lists, tuples, and derived `Show` over positional constructors. A type outside that set is refused by name. The driver prints with `print`, so a data type inside a result must derive `Show`; `Shell` does.

Sixteen bindings run: `isDereferencingBinaryOp`, which is `elem` over a literal list, and `shellForExecutable`, a `case` over string patterns that becomes `eqString`, with operator and executable names including empty, non-ASCII and near-miss spellings, plus fourteen `ShellCheck.Data` constants. All 88 cases match.

Running the constants exposed a limit in rustc. Each top-level value is a thread-local initialiser and a deferred closure, and rustc counts nested instantiations of the one `FnOnce::call_once` shim against `recursion_limit`, which is 128 by default. A chain of 280 constants exceeded it. An emitted program now declares a limit equal to its own number of shim sites, two per function plus one per instruction, when that number is above 128.

Two tools answer the questions this work kept asking:

- `mise run lower:sites <subject>` groups every survey refusal about one stable name or type head by the shape of the call at its site: the head, each argument (type arguments rendered, globals by name, locals with their types), where the call sits, and the refused instances with their type arguments.
- `mise run lower:entries` lists every live exported binding with its type and whether a standalone entry emits for it, with the refusal reason otherwise. Of 105, 16 emit, and those are the suite above.

`h2r lower --nir --specialize --fn` and `canary:explain` now print what each refusal is about.

## Library list functions

`map`, `reverse1`, `++_$s++`, `dropWhile`, `$wlenAcc`, `takeWhile`, `filter` and `reverse` had 75 refusals between them, 29 of them `map`'s. The dump records `hasUnfolding: false` for all eight, so each is implemented in `h2r-rt` against base 4.18.3.0's equations and resolved through the external table at its exact signature:

```haskell
map _ []     = []
map f (x:xs) = f x : map f xs

filter _pred []    = []
filter pred (x:xs)
  | pred x         = x : filter pred xs
  | otherwise      = filter pred xs

takeWhile _ []          =  []
takeWhile p (x:xs)
            | p x       =  x : takeWhile p xs
            | otherwise =  []

dropWhile _ []          =  []
dropWhile p xs@(x:xs')
            | p x       =  dropWhile p xs'
            | otherwise =  xs

reverse l =  rev l []
  where
    rev []     a = a
    rev (x:xs) a = rev xs (x:a)

lenAcc []     n = n
lenAcc (_:ys) n = lenAcc ys (n+1)
```

Three of the names are GHC's. `reverse1` is `reverse`'s local `rev`, and `reverse`'s unfolding is `reverse1 l []`. `$wlenAcc :: [a] -> Int# -> Int#` is `lenAcc`'s worker, and its addition wraps. Its `IdInfo` says `[StrictWorker([!])]`, and the table requires exactly that. `++_$s++ :: a -> [a] -> [a] -> [a]` is SpecConstr's specialisation of `(++)`, and base's own rule defines it:

```
"SC:++0" forall sc sc1. ++ (sc : sc1) = ++_$s++ sc sc1
```

So `++_$s++ x xs ys` is one cell holding `x`, whose tail is `xs ++ ys`.

`Operation::ListFunction` carries the function, its value arguments, the input list's cells, `map`'s result cells, and `False` and `True` for the three functions that take a predicate. All the layouts come from the world. The source verifier derives each of them again from the spine. The structural verifier instantiates the function's signature at the cells' element types and checks every operand and the result against it.

Each function forces what its equations force. `map` builds a cell when one is demanded and applies the function once, when that element is forced. The element is a thunk in its own carrier: `Int`, data or a function. `filter` skips failing elements inside one cell's evaluation. `takeWhile` stops at the first failure and never touches the rest. `dropWhile` returns the first failing cell itself. `reverse1` forces the spine and nothing else, and its accumulator only when the list ends.

### Fixtures

Seventeen entries run over the 49 boundary input pairs. `map` runs at data, `Int` and function elements (`mapChars`, `mapInts`, `mapFunctions`). `mapLazy`, `mapUnapplied`, `filterLazy`, `takeWhileLazy`, `dropWhileLazy`, `reverseLazy`, `lengthLazy` and `consAppendLazy` put a failing computation where the definition must not look. At `-O1`, `reverse` becomes `reverse1` and `(x : xs) ++ ys` becomes `++_$s++`. At `-O0` the same fixtures call `reverse` and `(++)`, and the evidence checks ask for each call in its own profile. `lengthChars` and `lengthLazy` run in the optimized profile only: `-O0` calls `GHC.List.length`, which ShellCheck never reaches, and the canary asserts that refusal.

Nine forced-error probes pin what each function forces: `map`'s spine and its function, `filter`'s predicate, `takeWhile`'s element, `dropWhile`'s spine, the tail `reverse` and `length` walk to, and the right list `++_$s++` reaches once the left runs out. For `mapChars`, `filterChars`, `takeWhileChars` and `dropWhileChars`, five forgeries of the verified instruction must be rejected: a different function, reversed operands, a predicate's `Bool` added or removed, `map`'s result cells added or removed, and a wrong rule.

### Results

Canonical NIR coverage per owner: **8,498 lowered / 1,297 refused / 3,957 dead**, against 8,457 / 1,338. The instance survey: **9,833 = 8,516 lowered + 1,317 refused**, 958 of them at a closed signature, against 999. All eight functions are gone from the external list. The canary passes **26,806 differential cases**, with 41 forced-error and branch probes in the optimized profile and 37 in the unoptimized one.

## Type constructors applied by substitution

`WriterT`, `RWST` and `StateT` were the largest remaining blockers: about 290 refusals at a closed signature, plus the 110 cons cells of the checker lists, whose element is `Parameters -> Token -> WriterT [TokenComment] Identity ()`. Their newtype evidence was in the dump and correct. The failure was in substitution.

`WriterT`'s worker has the type `m (a, w) -> WriterT w m a`, where `m (a, w)` is an application of a type variable. Substituting `m := Identity` left `App (Con Identity []) (a, w)`. GHC's `mkAppTy` never builds that form: it appends the argument to the constructor's own, giving `TyConApp Identity [(a, w)]`. So `newtype_field` could not see `Identity` as a newtype to peel, no carrier was found, and a type that GHC wrote as `Identity (a, w)` did not compare equal to the instantiated one.

Substitution now folds each `App (Con tc args) arg` into `Con tc (args ++ [arg])`, as `mkAppTy` does. The dumps contain no `FUN` constructor application, so the other normalisation `mkTyConApp` performs, a saturated `FUN` becoming a `FunTy`, cannot arise from them.

`newtypeMonad` exercises it: `runLogged :: Logged m a -> m (a, Int)` specialised at `m := Maybe`, in both profiles. With the fold disabled, the canary refuses it in both.

### Results

Canonical NIR coverage per owner: **8,901 lowered / 894 refused / 3,957 dead**, against 8,498 / 1,297. The instance survey: **9,865 = 8,935 lowered + 930 refused**, 571 of them at a closed signature, against 958. Every transformer type is gone from the blocker ranking. The survey now reaches further, so the external boundary rose from 330 refusals to 369, `containers` from 67 to 79. A new blocker appeared: 31 empty cases whose scrutinee has no supported non-return evidence. The canary passes **27,002 differential cases**.

## Libraries compiled from source

A library binding without an unfolding in the dump had to be implemented in `h2r-rt` by hand, as `map` and `eqString` were. That does not scale to `Set.balanceR` or `Map.link`, and rewriting library algorithms is what this compiler must not do. The library's own Core scales. `containers`, `transformers`, `mtl` and `base` are now rebuilt from their Hackage source with the plugin, and their dumps load into the same world as ShellCheck's.

`mise run extract:libraries` runs `compiler/extract-library.sh <package>` for each of them, which writes `compiler/library-json/<package>/`. `h2r lower --with <dir>` loads a library directory beside the program's, the `lower:*` tasks and the canary load all four that way, and the M1 to M3a reports keep measuring the program alone.

The dumps have to name every binding exactly as ShellCheck's Core refers to it, `$containers-0.6.7$Data.Set.Internal$balanceR`, so each library is compiled as the unit the program linked:

- **The module list** is the installed package's own, from `ghc-pkg field <package> exposed-modules,hidden-modules`. These are the modules the program was linked against: 37 for `containers`, 24 each for `transformers` and `mtl`, and 274 for `base`. `ghc-pkg` lists `base`'s re-exports from `ghc-bignum` among them, as `Module from unit:Module`, and those are not compiled.
- **The unit id** is the installed one, such as `-this-unit-id containers-0.6.7`. `base` is a wired-in unit, so GHC calls it `base` while `ghc-pkg` lists `base-4.18.3.0`, and the script names it explicitly. `h2r-plugin`'s dependency closure contains all four packages. Loaded with `-fplugin`, it deadlocked the `containers` compilation before its first module, at 0% CPU. Loaded from its shared object with `-fplugin-library`, it lets all four compile under their installed ids.
- **Safe Haskell.** GHC marks every module a plugin touched as unsafe, which breaks the `Safe` modules that import them. `-fplugin-trustworthy` is GHC's flag for exactly that.
- **The source path.** GHC writes the path a module was compiled from into the `SrcLoc` of every `HasCallStack` call site, and those appear in `error`'s output. The installed libraries were built by hadrian, and `libHScontainers-0.6.7.a` embeds `libraries/containers/containers/src/...`, so the script compiles from a root in which the source sits at hadrian's relative path.
- **Flags.** `-O2 -XHaskell2010` for all four.
- **Generated sources.** 19 of `base`'s modules are `.hsc` sources. `hsc2hs` runs on each from the same root, so its `LINE` pragmas carry hadrian's relative path, with the installed package's include directory for the headers `configure` generated. A module whose source is generated keeps its `.hs-boot` beside the generated `.hs`, where GHC looks for it.
- **Interfaces.** `compiler/compare-interfaces.sh` compares every rebuilt interface with the installed one, after removing hashes, dependent-file paths, the plugin dependency and the haddock section, and the extraction fails on any difference. That covers every exported unfolding, the `SrcLoc` paths inside them, and the Typeable fingerprints GHC derives from the unit id. All 359 interfaces are identical, `base`'s 274 included.

With `containers` loaded, `A5-IN-WORLD-MISSING` is 0, so every reference ShellCheck's Core makes into `containers` resolves. 152 `containers` bindings are live, and the independent reachability verifier reports 0 disagreements over 161,911 claims.

### Rooting

A library binding is needed only at the instantiations the program asks for, so only the program's own live bindings are survey roots and lowering owners. Rooting `containers`' polymorphic functions at their own signatures would count them against open types no caller uses. The per-owner report counts the program's owners and reports the live library bindings beside them.

### What `containers`' code needed

- **`GHC.Magic.lazy :: a -> a`**, the identity once CorePrep has run. It is a `Move` of its argument.
- **`uncheckedIShiftL#` and `uncheckedIShiftRA#`**, `Int#` shifts. GHC leaves a count outside `0..63` undefined. The emitted code masks it to the word, as x86-64's `shl` and `sar` do.
- **`Word#`**, a third scalar. It is the same machine word as `Int#`, compared unsigned. `int2Word#` moves the word, and `leWord#` is an unsigned comparison.
- **Pointer equality on a boxed `Int`.** `containers`' `insert` compares the new element with the old one by pointer to keep sharing. `reallyUnsafePtrEquality#` now accepts two values of one shared carrier, a boxed `Int` or algebraic data, and is `Rc` identity for both.
- **`error`**, below.
- **`(##)` passed as an argument.** A join point that takes `(# #)` is called with the nullary constructor as a bare variable. A call argument that named a constructor was resolved through the boxed-constructor layout, which refuses an unboxed tuple, so the unboxed-tuple worker is now tried first, in the lowering and in the verifier. This refused 41 ShellCheck owners with or without `containers`.

### `error`

`GHC.Err.error :: forall r (a :: TYPE r). (?callStack :: CallStack) => [Char] -> a` takes its call stack as an `IP "callStack" CallStack` argument, a newtype over `CallStack`. At `-O1` every call site's stack is constant data in Core, `PushCallStack "error" (SrcLoc pkg module file line col endLine endCol) EmptyCallStack`, so the whole message is computed from the program.

`Operation::RaiseCallStackError` carries the message, the stack, and the `CallStack` and `SrcLoc` layouts from the world. The runtime prints the message, then, when the stack has a frame, `CallStack (from HasCallStack):` and one `  f, called at file:line:col in package:module` line per `PushCallStack`, through any `FreezeCallStack`. That is base 4.18's output for an uncaught `ErrorCallWithLocation`. The stack is forced to its first frame before the message, because `showsPrec`'s match on an empty location forces it. At `-O0` the stack is built by calling `base`'s `pushCallStack`, which is lowered from `base`'s own Core.

`undefined` is in the world too. Its body raises through `raise#`, a primop with no implementation, and emission refuses it.

### Fixtures

- `shifts`, `wordOrder`, `magicLazy` and `voidJoin` run in both profiles.
- `setSize`, `setMember`, `setOrder` and `mapStrings` run `containers` code compiled from source against GHC's `containers`, over the 49 boundary input pairs, in the optimized profile. At `-O0` they reach `ghc-prim`'s `Ord Int` dictionary, which the world does not contain yet. `mapLookup` and `mapUnion` run in the optimized profile with `base`'s `(+)` and `(-)` at `Int`, and their `-O0` refusal is asserted.
- Four located probes compare `error`'s whole output with the oracle's. `errorCall` and `errorCallComputed` raise with a stack that points into `Canary.hs`. `setFindMin` raises `containers`' own `Set.findMin: empty set has no minimal element`, and its stack points into `libraries/containers/containers/src/Data/Set/Internal.hs:776:17 in containers-0.6.7:Data.Set.Internal`. A located probe reads the location from the oracle's output, requires the message and the `CallStack` header before it, and compares both Rust builds with it.
- `errorUnusedArgument`, `errorUnusedLet` and `errorUnusedShared` bind an `error` and never demand it. They were refusal fixtures while `error` had no implementation, and now run as differential fixtures in both profiles. `undefinedUnused` keeps its refusal.
- Three forgeries of `error`'s verified instruction must be rejected: a swapped message and stack, swapped `PushCallStack` and `EmptyCallStack` layouts, and a wrong rule.
- `stateCollect`, `stateNumber`, `writerCollect`, `stateClass` and `rwsRecord` pass a `StateT`, `WriterT` or `RWST` dictionary over `Identity` to an `OPAQUE` function, as ShellCheck's own code passes them, and use `transformers`' `Monad` and `Applicative` and `mtl`'s `MonadState`, `MonadReader` and `MonadWriter`. Their refusals are asserted in both profiles; see [`base` in the world](#base-in-the-world) for what they reach now.

### Results

Canonical NIR coverage per owner: **9,000 lowered / 795 refused** over the same 9,795 live program owners, against 8,901 / 894; the 152 live `containers` bindings are lowered as the instances the program requests. The instance survey: **10,186 = 9,353 lowered + 833 refused**, 474 of them at a closed signature, against 571. 363 instances are specialized at type or dictionary arguments. The 15 that carry a dictionary are `containers`' `Eq (Set a)` and `Ord (Set a)` instances and methods, at `CFVariableProp`, `Set CFVariableProp` and `FunctionDefinition`. `containers` is gone from the external boundary, which falls from 369 refusals over 108 bindings to 305 over 92. `ghc-prim:GHC.Classes` rises from 29 refusals to 44. `Set`'s `Eq` and `Ord` compare two sets' element lists, and 17 of the 44 are those comparisons, all 14 at list `compare` and 3 at list `==`. The canary passes **28,472 differential cases**.

## `base` in the world

With `base` compiled into the world, the external boundary no longer counts anything in `base`. What remains outside is `ghc-prim`'s `GHC.Classes`, `regex-tdfa`, `text`, `ghc-bignum`'s `Integer`, primops, and a few bindings of `aeson`, `fgl`, `filepath` and `parsec`; see [Remaining runtime and external dependencies](#remaining-runtime-and-external-dependencies).

The runtime implementations of `map`, `filter`, `eqString`, `++`, `error` and the rest stay in use. The lowering matches an external by stable name and `IdInfo` before it looks for a definition in the world.

### Dead ends in the world

A divergent call to a binding outside the world is an analysis-only dead end. A direct call to a binding the world defines is lowered as a call, so its body can run. Two cases stay dead ends:

- **More type arguments than the definition binds.** GHC calls its wired-in `patError` at `forall (r :: RuntimeRep) (a :: TYPE r)`, and `base` defines it at `forall a`. `diverge::defined_quantifiers` counts the definition's own quantifiers, and a call that supplies more cannot link to it.
- **An empty case over a divergent global**, whatever module defines the global.

The survey now refuses no empty case and no `patError` site. Before `base` was loaded it refused 31 empty cases.

### Type arguments after a dictionary

A class method's own quantifiers follow the class's dictionary, as in `(>>) @m $dMonad @a @b m k`, and so do an instance method's, as in `$fRegexContextab(,,)_$cmatchM @a @b $dRegexLike @m $dMonadFail re input`. A spine may now interleave type arguments with dictionaries that resolve at compile time. The instance key keeps its type arguments and its dictionaries as two lists, and the target's lambdas, walked in order, say which comes first: `bind_type_arguments` keeps a dictionary arrow and instantiates the quantifiers after it inside its result, and `dict::reference_type` does the same for the signature. A type argument after a runtime value is still refused: its dictionary is a runtime value, and a polymorphic method read from it has no carrier.

### Methods through a cast

GHC writes an eta-reduced method whose result is a newtype as its implementation cast to the method's type. `$fMonadStateT`'s `>>` field is `($fMonadStateT1 @s @m $dMonad) |> co`, and `Identity`'s `Functor` and `Applicative` methods are casts too. `dict::method` resolves such a field to its implementation's instance and types the call at the cast's target type, instantiated at the method's own type arguments. The call always goes through `Apply`. The closure keeps the implementation's own arity, and `HClosure::apply` feeds arguments one at a time, so the cast's type may split the arrows differently. As for any cast, both sides must have the same carrier.

A method field that is a cast lambda, as `$fMonadStateT`'s `return` is, has no top-level binding to instantiate, and the call falls back to its selector, which binds fewer type arguments than the method supplies.

### Fixtures

- `identityWalk` runs `stepsA`, an `OPAQUE` `Applicative` traversal, over `Identity`. The instance of `stepsA` is specialized on `Identity`'s `Applicative` dictionary, and its methods resolve through their casts to `$fApplicativeIdentity2`, `$fApplicativeIdentity3` and `$fFunctorIdentity2`. It runs differentially in the optimized profile. At `-O0`, `<$>` reaches an application of a value, which is not lowered yet, and that refusal is asserted.
- `patternFail` falls through a non-exhaustive match into `patError`. Its evidence is the dead-end rule in both profiles, and its emission is refused.
- `mapLookup` and `mapUnion` run in the optimized profile, and `errorCall`, `errorCallComputed`, `errorUnusedArgument`, `errorUnusedLet`, `errorUnusedShared`, `lengthChars`, `lengthLazy` and `lengthTail` run in both.
- `stateCollect`, `stateNumber` and `stateClass` in both profiles, and `writerCollect` at `-O0`, stop at a selector reached with a method's own type arguments. At `-O1`, `stateCollect`'s is `return`, whose field in `$fMonadStateT` is a cast lambda. `writerCollect` at `-O1` is refused with `reference is neither a parameter nor a top-level binding`. `rwsRecord` stops at `>>=` and `return` selected from a dictionary that stays a runtime value.

### Results

Canonical NIR coverage per owner: **9,124 lowered / 671 refused** over the 9,795 live program owners, against 9,000 / 795 with `containers` alone, and 2,143 library bindings are live. The instance survey: **11,107 = 10,166 lowered + 941 refused**, 577 at a closed signature and 364 at an open one. 1,022 instances are specialized at type or dictionary arguments, 243 of them on a dictionary, against 363 and 15. The survey reaches further than it did, and its refusals rose with its lowered instances: 115 are instance chains past the per-owner budget, and 98 are selectors reached with a method's own type arguments. The external boundary falls from 305 refusals over 92 bindings in 36 modules to 231 over 46 in 15. The canary passes **29,256 differential cases**.

## Risk assessment

Four questions decide whether this pipeline ends in a working `shellcheck` binary. Can rustc build the whole program? How does the emitted code run against GHC's? What does `IO` need? Do the libraries still outside the world lower? Each was measured on the canonical `-O1` dump with `containers`, `transformers`, `mtl` and `base` in the world, on 2026-09-23. Artifacts go to `compiler/build/risk/` and `compiler/build/canary/bench/`.

| question          | measured                                                                                                                                                                                         |
| ----------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| whole program     | 79.8% of the live bindings that carry code emit with their whole closure, as 15.3 MiB of Rust. rustc builds it at opt-level 0 in 43 s and 5.3 GiB, and needs more than 6 GiB at opt-level 2.     |
| against GHC       | Every bench entry runs to the largest size tried with no stack limit raised. Tail loops run in constant memory. At n = 10⁷, non-tail recursion takes 31.9× GHC's time and 31.2× its peak memory. |
| `IO`              | The program names about 25 of `base`'s IO bindings. 664 live `base` bindings, 79 foreign calls and the IO primops sit beneath them.                                                              |
| outside the world | `parsec` builds from source with identical interfaces and moves no survey total. Six packages from the cabal store stay outside.                                                                 |

### Linkage with `base` loaded

With `base` in the world, 199 names over 658 `Ref::Global` occurrences carry an internal stable name, and the reachability report fails `A13-GLOBAL-EXTERNAL`. All 199 are foreign calls, such as `$_in${__ffi_static_ccall_unsafe base:close :: Int32# -> State# RealWorld -> (# State# RealWorld, Int32# #)}`. GHC gives an `FCallId` an internal name, and the dump's id table has no entry for one, so its `IdDetails` are not recorded. Every in-world reference links. `h2r lower --reachability --boundary` lists the foreign calls with the rest of the boundary.

### Building the whole program

`mise run lower:emit-program` (`h2r lower --nir --emit-program <file>`) surveys the live program and keeps the largest set of instances that is closed under its dependencies and whose own code emits. It writes that set as one Rust program, in modules of 64 instances, whose `main` takes the address of every function so rustc compiles each one. The task then builds it at opt-level 0 and 2 under a 6 GiB memory cap.

|                                               |                                      |
| --------------------------------------------- | -----------------------------------: |
| live program bindings, each a survey root     |                                9,795 |
| … whose instance emits with its whole closure |                                5,735 |
| instances the survey reaches                  |                               11,107 |
| … lowered                                     |                               10,166 |
| … whose own code emits                        |                                7,434 |
| … emitted, with every dependency              |                                6,660 |
| generated Rust                                | 15.3 MiB, 195,936 lines, 105 modules |
| `h2r` itself                                  |                       381 s, 2.0 GiB |

The 4,060 roots that do not emit, by cause:

| cause                                                  | roots |
| ------------------------------------------------------ | ----: |
| the root is a floated string literal, typed `Addr#`    | 2,604 |
| a dependency does not emit                             |   717 |
| the root itself does not lower                         |   671 |
| a non-returning call to `patError`                     |    33 |
| a non-returning call to `ShellCheck.ASTLib.arguments1` |    24 |
| `[]` without a carrier                                 |     6 |
| a non-returning call to `$fEqMaybe1`                   |     3 |
| a polymorphic instance                                 |     2 |

The first row costs no emitted code. `strings::address_literal` reads a floated literal's bytes at compile time where an unpacker consumes it, so no emitted function depends on the `Addr#` binding, which is a survey root only because every live binding is one. Of the other 7,191 roots, 5,735 emit with their whole closure (79.8%). By module, counting the literals: `ShellCheck.Parser` 851 of 1,487, `ShellCheck.Analytics` 1,522 of 2,646, `ShellCheck.Checks.Commands` 658 of 1,184, `Main` 230 of 409, and the JSON formatters 7 of 92.

rustc builds it at opt-level 0. At opt-level 2 it needs more than the 6 GiB cap, with one module, with 105, and with codegen limited to two jobserver slots.

| build                                 | wall | peak memory | result            |
| ------------------------------------- | ---: | ----------: | ----------------- |
| type checking only, `--emit=metadata` | 27 s |     2.5 GiB | 98% of one core   |
| opt-level 0, one module               | 61 s |     4.9 GiB | a 99.2 MiB binary |
| opt-level 0, 105 modules              | 43 s |     5.3 GiB | a 101 MiB binary  |
| opt-level 2, one module               | 51 s |     > 6 GiB | killed at the cap |
| opt-level 2, 105 modules              | 58 s |     > 6 GiB | killed at the cap |
| opt-level 2, 105 modules, `make -j2`  | 58 s |     > 6 GiB | killed at the cap |

The opt-level 0 builds report no errors. rustc warns about 2,893 block helpers the dispatcher leaves unused and 96 unreachable expressions.

### Running against GHC

`mise run canary:bench` compiles the entries of `compiler/canary/Bench.hs` from the canary's `-O1 -fno-worker-wrapper` dump, and times each against the GHC-built oracle at growing sizes, with peak resident memory from GNU time. All outputs agree with GHC's.

| entry        | what it does                                  |
| ------------ | --------------------------------------------- |
| `benchSet`   | `Set.insert` of n pseudo-random `Int`s        |
| `benchText`  | build, `map` and scan an n-character `String` |
| `benchDeep`  | non-tail recursion n deep over a list         |
| `benchCps`   | n tail calls through a continuation argument  |
| `benchChain` | forcing a chain of n thunks                   |
| `benchLoop`  | a tail loop n long returning a boxed `Int`    |

Every entry runs to n = 10⁷, and `benchSet` to 10⁶, the largest sizes tried, with no stack limit raised. The table gives time and peak memory as multiples of GHC's. `canary:bench` stops at n = 10⁶, and the n = 10⁷ column comes from the same binaries run by hand under the 6 GiB cap. GHC's times below 0.05 s are mostly process start-up.

| entry        |      n = 10⁵ |       n = 10⁶ |       n = 10⁷ |
| ------------ | -----------: | ------------: | ------------: |
| `benchSet`   | 16.5× / 6.6× |  10.9× / 9.5× |               |
| `benchText`  |  3.0× / 0.3× |  16.0× / 0.2× |  29.0× / 0.3× |
| `benchDeep`  |  7.5× / 4.6× | 24.5× / 20.9× | 31.9× / 31.2× |
| `benchCps`   |  1.0× / 0.4× |   7.2× / 0.4× |  45.5× / 0.4× |
| `benchChain` |  2.9× / 1.3× |   3.6× / 2.8× |   3.2× / 2.9× |
| `benchLoop`  |  0.7× / 0.3× |   4.7× / 0.2× |  20.0× / 0.3× |

`benchText`, `benchCps` and `benchLoop` peak at 2.7 MiB or less at every size. At n = 10⁷ `benchDeep` peaks at 5.2 GiB and GHC at 171 MiB, and `benchChain` at 1.8 GiB and GHC at 632 MiB.

The emitted code bounds its stack in three ways:

- **Unlifted results.** A block whose result is `Int#` or an unboxed tuple runs in a dispatcher loop, one loop per result carrier. A direct tail call, an `Int#` switch and a tail `case` on data return the next block as a loop state. A saturated tail call through a closure whose code is an `Int#` block enters the loop as well. `benchText`'s scan and `benchCps`'s continuation run this way.
- **Lifted results.** A top-level function, a CAF and a delayed block return a thunk. So do a tail call through a closure and a tail transfer to a block that can reach its caller again. When the thunk's code ends in another call, it returns that call's thunk as an indirection. `force` follows a chain of indirections in a loop and writes the value into every link that is still shared. `benchLoop` runs this way.
- **Nested evaluation.** A non-tail call, and forcing a thunk inside another thunk's code, use the native stack, as they use GHC's. `benchDeep`, `benchChain` and `benchSet`'s accumulated `Set.insert`, a delayed argument in the canary's `-fno-worker-wrapper` Core, nest this way. The program runs on a thread whose stack may grow to 80% of physical memory, GHC's default maximum stack size.

`Data::force` also clones the node's field vector each time a value is inspected, and constructors are matched by comparing their stable-name strings.

### `IO`

`h2r lower --reachability --boundary` lists every name live code references that the world does not define. With `base` loaded, `Main.main` reaches:

- **133 primops** over 5,120 occurrences. Beside the arithmetic ones they include mutable variables (`newMutVar#`, `readMutVar#`, `writeMutVar#`), `MVar#`s, exceptions and masking (`catch#`, `raiseIO#`, `maskAsyncExceptions#`), threads (`yield#`, `myThreadId#`, `killThread#`), raw memory (`plusAddr#`, `readWord8OffAddr#`, `writeWideCharOffAddr#`), arrays and byte arrays, weak and stable pointers, `touch#` and `keepAlive#`.
- **79 foreign calls** over 138 occurrences: `open`, `read`, `write`, `close`, `lseek`, `fstat`, `ftruncate`, `fcntl`, `dup`, terminal settings, signal masks, `iconv`, the locale, `getenv`, the program's arguments, file locks, `malloc` and `memcpy`, and the MD5 behind `Typeable`'s fingerprints.
- **664 live bindings in `base`'s IO modules.** The handle layer has 258, text encodings 183, IO exceptions 70 and the event manager 44, and `Foreign`, `System.Posix.Internals`, `System.Environment` and `System.Exit` the other 109. Behind exceptions sit 208 live bindings of `Data.Typeable.Internal` and `GHC.Fingerprint`, and 82 of `GHC.Exception`, `GHC.Exception.Type` and `Control.Exception.Base`.

The program itself names few of them. The same report lists the library bindings live program code calls directly, and the IO ones are `stdin`, `stdout`, `stderr`, `hPutStr`, `hGetContents`, `hPutBuf`, `openFile`, `openBinaryFile`, `hSetBinaryMode`, `hIsSeekable`, `hGetEcho`, `wantReadableHandle`, `getForeignEncoding`, `withCString`, `allocaBytesAligned`, `getArgs`, `getEnv`, `exitWith`, `exitFailure` and `modifyIOError`, with `IOException`'s `Exception` instance and `sameTypeRep` for `catch`. Beyond `base` it calls 7 bindings of `directory` and 5 of `bytestring`. `IO` can be supplied either at that surface, as typed runtime adapters, or at the bottom, by translating `base`'s handle layer and implementing the primops and foreign calls beneath it.

### Libraries still outside the world

`compiler/extract-library.sh parsec` builds `parsec` 3.1.16.1 from source under its installed unit id, and all 25 interfaces match the installed ones. Loaded as a fifth library, it leaves the survey at 11,107 = 10,166 lowered + 941 refused. Its 12 external refusals were all at open signatures, and they become in-world refusals of ShellCheck's parser code: 10 more `type arguments must precede value arguments` and 7 more `instance reference needs closed structured type arguments`, while 5 `a let binds a value whose type has no carrier` go. The closed-signature blockers do not change. ShellCheck's parser is generic in its base monad, `type SCParser m v = ParsecT String UserState (SCBase m) v`, so the survey roots its bindings at signatures over `m`, where the `Monad m` dictionary is a parameter.

`regex-tdfa`, `regex-base`, `aeson`, `fgl`, `Diff` and `vector` come from the cabal store under hashed unit ids, and the script builds only packages `ghc-pkg` finds in the global database.

## Remaining runtime and external dependencies

`mise run lower:specialize` against the canonical `-O1` dump reports **231 refusals over 46 bindings in 15 modules**, with `containers`, `transformers`, `mtl` and `base` compiled into the world. The groups below are by the work each needs, not by package.

| What it needs                                                                            | Refusals | Where                                                                                                                                                                                                                                                                                                       |
| ---------------------------------------------------------------------------------------- | -------: | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **Foreign libraries.** Haskell packages not yet compiled into the world.                 |      102 | `regex-tdfa` 63 (`Text.Regex.TDFA.String.compile` 49, `Text.Regex.TDFA.NewDFA.Tester.matchTest_multi5` 14), `regex-base` 16 (`$fRegexContextab(,,,)_$cmatchM` 14, `$fRegexContextab(,,)_$cmatchM` 2), `parsec` 12 (`$fApplicativeParsecT2` 7, `$woptional` 3, `upper1` 2), `aeson` 4, `fgl` 4, `filepath` 3 |
| **`Eq`/`Ord` for lists, tuples and `Int`.** `ghc-prim`'s class methods and dictionaries. |       59 | `ghc-prim:GHC.Classes` (`$fEqList_$s$c==1` 16, `$fOrdList_$ccompare` 14, `$fEqList_$c==` 6, `$fEqList_$s$fEqList1` 6, `eqInt` 4, `$fEqList_$s$c==2` 2, `compareInt` 2, `compareInt#` 2, seven more at 1)                                                                                                    |
| **`text`.**                                                                              |       27 | `Data.Text.Show.$wunpackCStringAscii#`                                                                                                                                                                                                                                                                      |
| **`Integer`.** This backend has no carrier for arbitrary precision.                      |       23 | `ghc-bignum:GHC.Num.Integer` (`integerEq` 9, `integerCompare` 5, `integerToInt#` 3, `integerAdd` 2, `integerGe` 2, two more at 1)                                                                                                                                                                           |
| **Primops with no implementation yet.**                                                  |       20 | `ghc-prim:GHC.Prim` 14 (`andI#` 3, `negateInt#` 2, `quotRemInt#` 2, `raise#` 2, `unsafeFreezeArray#` 2, `minusWord#`, `orI#`, `word8ToWord#`), `ghc-prim:GHC.Magic.runRW#` 6                                                                                                                                |

Every count is a lower bound. A refused instance never revealed its own requirements, which is why clearing a blocker can raise other counts. After the list predicates, `map` rose from 24 to 29 and `System.Info.os` appeared. After `compare`, the `Map` code behind string-keyed lookups became reachable. After pointer equality, the `Set` and `Map` balancing code behind it did. After the list functions, the functions passed to them did: `fst`, `snd`, `isSpace` and `toSimpleLowerCase`. After substitution learned to apply a type constructor, the transformer code did, and `containers` rose again. Once `containers` was compiled into the world, `Set`'s `Eq` and `Ord` instances became reachable, and they compare element lists with `ghc-prim`'s list `Eq` and `Ord`. Once `base` was, and a spine could interleave type arguments with dictionaries, calls reached `regex-base`'s `matchM`, more of `parsec`, and primops such as `raise#` and `negateInt#`.

### Open signatures

The survey roots every live binding at its own signature. For a binding quantified over a type, that asks for code over a free type variable, and a free type variable has no carrier. The report now counts these separately from the blockers:

```
Refused: 941 = 577 at a closed signature + 364 at an open signature
Open signatures: 364 refused instances of 364 bindings quantified over types they were not given; 111 of those bindings were also requested at closed types
```

For 253 of the 364, the survey never requested a closed instantiation. Some are artifacts of the rooting, but not all of them. `ShellCheck.CFGAnalysis`'s `ST` code is quantified over the state thread `s`, which `runST`'s rank-2 type never instantiates to a closed type, so no specialization can close it. Those are real blockers.

Before the split, 152 of these refusals read `switch requires an unboxed scalar scrutinee, a supported result and no alternative binders`. A tail `case` went to the scalar switch whenever its scrutinee was not lifted, and a type with no carrier counted as not lifted. So a `case` over `[(String, a)]` was reported as a failed switch. The tail now switches only on a scalar carrier, and everything else reaches the case rules, which report `unsupported case scrutinee carrier`. The unboxed-tuple test also discarded its error: `(# State# s, InternalState #)` with a free `s` fails to instantiate, and that failure was read as "not a tuple" and routed to the switch as well. It now reports its own reason. No switch refusal remains.

`bytestring` is still absent from this table and still referenced by the program: `Data.ByteString.Builder` and `Data.ByteString.Lazy` from both JSON formatters, `Data.ByteString.Short.Internal.packCStringLen1` from `Main`. The survey has not reached any of it. **Byte-oriented operations therefore remain unmeasured rather than unnecessary**, and building a `ByteString` carrier now would be guessing at a requirement that has not been stated — exactly what `text` did until this milestone made it reachable.

## Recursive lazy value graphs: none reached by the current survey

The current refusal frontier contains no recursive-value binding refusal. This does not prove that none occur behind earlier refusals or missing dependency bodies.

The refusal that looked like it covered them said "a let requires a supported non-recursive value, not a join point" — three different things wearing one sentence, which is the same defect the partial-application refusal had. Split apart, over the whole live set:

| cause                                         | refusals |
| --------------------------------------------- | -------: |
| a let binds a value whose type has no carrier |        7 |
| a let group binds several values at once      |        4 |
| **a recursive value binding**                 |    **0** |
| **a join point bound as a value**             |    **0** |

Of the 7, 1 is at a closed signature (`aeson`'s `Encoding'`) and 6 at an open one (a `forall` 5, `MonadState` 1). None of them is about recursion. A conflated message cannot be ranked, and until it was split the ranking could not say which of the three the program actually contains.

So the knot-tying runtime this would have needed is not built. `h2r-rt`'s `Lazy::force` still panics on re-entry rather than tying a knot, the emitter still refuses a dependency cycle through a value, and the canary holds both refusals in place with their messages asserted, so a wrong answer cannot appear quietly. Building the cyclic `Rc` for zero refusals would be guessing at a requirement the survey has not stated — the same reason there is still no `ByteString` carrier.

## What ShellCheck actually needs

Surveyed against the tree at the repo root:

- **Template Haskell** appears in 13 modules and is *only* `$quickCheckAll`; `striptests` removes it, so a production build needs neither TH nor QuickCheck.
- **No `unsafePerformIO`** anywhere.
- `Control.Monad.ST` / `Data.STRef` are used in exactly one place, `ShellCheck.CFGAnalysis`, and can lower to scoped Rust mutability.
- Extensions in use: `FlexibleContexts`, `DeriveGeneric`, `DeriveAnyClass`, `DeriveTraversable`, `PatternSynonyms`, `PatternGuards`, `ViewPatterns`, `RankNTypes`, `MultiWayIf`, `OverloadedStrings`, `NondecreasingIndentation`, `NoMonomorphismRestriction` — all handled by GHC before we see Core.
- Library surface to replace on the Rust side: `base`, `containers`, `array`, `bytestring`, `directory`, `filepath`, `mtl`/`transformers` (collapsed into explicit parameters), `parsec` (the substantial one), `regex-tdfa`, `aeson`, `Diff`, `fgl`.

## Conformance

The [binary conformance harness](rust/crates/h2r-conformance/README.md) reuses the `rust-port` corpus extractor and fuzz generator. Run `mise run conformance --candidate <binary>` or `mise run conformance:fuzz --candidate <binary>`; the candidate is explicit and need not link to any Rust-port library.

The `prop_*` corpus that `striptests` removes is the oracle: build ShellCheck once with GHC and once through this pipeline, run the same inputs through both, and require identical diagnostics, positions, fixes, exit status and output formats. Differential fuzzing over generated shell scripts extends it.

## GHC flag matrix — can GHC be tuned into producing more Rust-shaped Core?

`compiler/matrix.sh` extracts Core under six profiles and `h2r compare` puts the census side by side. The hypothesis was that `-fno-full-laziness` plus aggressive specialisation would remove float-outs, dictionaries and much of the memo population before any pass of ours runs.

What the matrix tests, exactly: the flags apply to the **ShellCheck package only**. Dependencies (parsec, mtl, containers, regex-tdfa, ...) are built with their Hackage defaults, so a profile answers "which flags give the best ShellCheck Core against the dependency interfaces as shipped". Rebuilding the dependencies with exposed unfoldings is a different experiment — aggressive specialisation can only use an imported unfolding that is actually there.

Per profile, `compiler/matrix/<P>/` keeps the dumps, the built `shellcheck` binary, cabal's `plan.json` and a `provenance` record (source and plugin hashes, toolchain versions, module list), so behavioural comparison and timing never need a rebuild. All six profiles were extracted from the same source and plugin revision, produce the same 28 modules, and their binaries give byte-identical output on a sample script in the tty, JSON and gcc formats. Re-extracting profile A reproduces the census to the last count: the dumps are deterministic.

|                                                       |   A `-O1` | B `-O2` | C = B `-fno-full-laziness` | D = C `-fspecialise-aggressively -fexpose-all-unfoldings` | E = D `-fstatic-argument-transformation` | F = E `-fstrictness-before=2` |
| ----------------------------------------------------- | --------: | ------: | -------------------------: | --------------------------------------------------------: | ---------------------------------------: | ----------------------------: |
| Core nodes                                            |   409,622 | 469,070 |                    498,825 |                                                 1,197,283 |                                1,116,489 |                     1,119,151 |
| extraction time                                       |     101 s |   114 s |                      111 s |                                                     252 s |                                    237 s |                         241 s |
| thunk sites                                           |     2,242 |   2,389 |                      2,849 |                                                     7,311 |                                    7,131 |                         7,109 |
| memo, under many-entry lambda                         |     1,242 |   1,328 |                      1,509 |                                                     3,904 |                                    3,778 |                         3,757 |
| `lvl…` float-outs                                     |       307 |     340 |                     **89** |                                                       275 |                                      275 |                           271 |
| genuine CAFs                                          |       238 |     230 |                     **53** |                                                        34 |                                       34 |                            34 |
| recursive values                                      |        69 |      65 |                         45 |                                                       119 |                                      119 |                           119 |
| class-op dispatch sites                               |       294 |     305 |                        314 |                                                       314 |                                      314 |                           314 |
| unsaturated call positions                            |       108 |     120 |                        197 |                                                       473 |                                      473 |                           472 |
| lazy/unknown computations                             |     8,351 |   9,268 |                     10,039 |                                                    25,771 |                                   24,186 |                        24,188 |
| … exact target tier                                   |   **93%** |     92% |                        91% |                                                       91% |                                      91% |                           91% |
| … finite target set                                   |         8 |       8 |                         25 |                                                        84 |                                       84 |                           106 |
| … producer known, target unresolved                   |       118 |     124 |                        125 |                                                       318 |                                      318 |                           318 |
| … unresolved tier                                     |    **5%** |      5% |                         7% |                                                        6% |                                       6% |                            6% |
| … exact *by the head alone*, before the Parsec proof  |   **68%** |     66% |                        64% |                                                       47% |                                      49% |                           49% |
| … Parsec CPS                                          |   **27%** |     29% |                        32% |                                                       41% |                                      40% |                           38% |
| thunk sites per 1k nodes                              |         5 |       5 |                          5 |                                                         6 |                                        6 |                             6 |
| saturated tuple constructions, boxed                  |     1,765 |   1,989 |                      2,250 |                                                     4,369 |                                    4,380 |                         4,465 |
| … removable after the boundary check                  |       542 |     630 |                        567 |                                                       935 |                                      969 |                           969 |
| … proven a real value                                 |       551 |     683 |                        674 |                                                       923 |                                      900 |                           900 |
| saturated tuple constructions, unboxed                |       819 |   1,020 |                        943 |                                                     1,751 |                                    1,751 |                         1,752 |
| … removable after the boundary check                  |       667 |     839 |                        798 |                                                     1,574 |                                    1,574 |                         1,575 |
| **tuples proven removable by def-use**                |   **56%** |     57% |                        53% |                                                       65% |                                      65% |                           64% |
| representation boundaries crossed                     |       580 |     691 |                        851 |                                                     1,972 |                                    2,006 |                         2,003 |
| … a uniform split                                     |       351 |     452 |                        486 |                                                       697 |                                      731 |                           728 |
| … flows downgraded because one is not                 |       247 |     277 |                        334 |                                                     1,497 |                                    1,497 |                         1,501 |
| **normalised** (removable, verified *and* composable) | **1,206** |   1,464 |                      1,360 |                                                     2,504 |                                    2,538 |                         2,539 |
| … verifier disagreements                              |         0 |       0 |                          0 |                                                         0 |                                        0 |                             0 |
| … scalar views built, all with 0 unplaced             |     1,209 |   1,469 |                      1,365 |                                                     2,509 |                                    2,543 |                         2,544 |
| M1 thunk sites explained by tuple transport           |        92 |     103 |                        120 |                                                       121 |                                      121 |                           121 |

Findings:

- **The flags change the program's size, not its shape.** Per-node ratios are flat across A–C; D–F are worse. `-O1` is the most Rust-shaped profile on every resolvability metric.
- **Inlining replicates Parsec's CPS, it does not dissolve it.** Exposing all unfoldings triples the Core and takes Parsec-attributed sites from 2,305 to 10,816. The Parsec normalisation pass is unavoidable; it should run on the smallest Core that still exhibits the pattern. The structural recogniser does keep up with the replication — the exact-target tier only falls from 93% to 91% across A→D — which is the point of proving the roles rather than counting names. The layout checks are what keep it there: they are derived per region from that region's own types, so replicated code with a different result type is measured against its own erasure, not against `-O1`'s.
- **GHC's specialiser does not finish the dictionary job.** Class-op dispatch sites *rise* (294 → 314) under `-fspecialise-aggressively`; the remaining dispatch is in code GHC cannot specialise (dictionaries stored in data, polymorphic recursion, unexposed instances). Closed-world specialisation is ours to do. [M2.4b](#m24b--the-closed-world-class-op-census) measured what is left: on every profile, **none** of the 565–596 class-op sites has a statically known dictionary, because a selector applied to a visible dfun is exactly what GHC has already rewritten.
- **Full laziness is doing useful work for us.** Turning it off removes the `lvl…` float-outs and most CAFs as predicted, but the constant expressions it had hoisted to top level — string literals, partial applications, ~7,700 top-level bindings in all — are *static data* in Rust; inside functions they become lets captured by inner lambdas, and the memo population grows by 18% (the captured-by-a-lambda part by 21%). Better to keep the hoisting and lower top-level constants to statics.
- **The tuple proof holds up under replication.** Inlining more (D–F) triples the constructions and the *share* proven removable goes up, not down (56% → 65%), because the extra copies are worker/wrapper returns whose call sites are all local. `-fno-full-laziness` (C) is the only profile that loses ground (53%): floating a tuple-returning closure back inside a lambda turns some returns into closures handed to parameters, which is the one shape the def-use proof refuses. The independent verifier agrees with the census on all six, with no disagreement anywhere.
- Static-argument transformation trims ~7% of nodes; an extra strictness pass changes nothing.

Decision: stay on `-O1` for the survey dump. Revisit per pass (e.g. SAT before ownership inference) rather than globally.
