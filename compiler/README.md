# Haskell → Rust compiler for ShellCheck

Goal: turn upstream ShellCheck (Haskell) into a native Rust program without
hand-porting it, and without dragging a GHC runtime clone along.

The strategy is to let GHC do everything it is already good at — parsing, type
checking, desugaring, simplification, demand analysis, worker/wrapper,
specialisation — and to consume **optimised Core**, not surface Haskell. By
that point GHC has already proved where laziness is irrelevant, so most of it
can be erased before Rust codegen instead of being reproduced with `Thunk<T>`
everywhere.

```
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

## Layout

| Path | What it is |
|---|---|
| `h2r-plugin/` | GHC plugin. Appends a Core pass after the whole optimisation pipeline and serialises each module's `CoreProgram` to JSON, including every binder's demand signature, CPR signature, arity and occurrence info. |
| `extract.sh` | Driver: stages a copy of the ShellCheck sources, runs upstream's `striptests` (which removes QuickCheck and Template Haskell), builds it with the plugin enabled, and collects the dumps. The tree at the repo root is never touched. |
| `rust/crates/h2r-core-ir` | Rust-side model of that JSON. Flattened into an arena on load — iteratively, since Core `App` spines nest far deeper than a stack likes — with parent links and edge kinds, so every later pass is worklist-driven. Includes a depth-limited Core pretty-printer. |
| `rust/crates/h2r-analysis` | Analyses over the arena. Today: the residual-laziness census (`laziness.rs`) and the shape/position predicates it rests on (`shape.rs`). |
| `rust/crates/h2r-rt` | Runtime for *residual* laziness only — `Lazy<T>`, `Shared<T>`. The design rule is that as little of this as possible should survive into generated code. |
| `rust/crates/h2r-cli` | The `h2r` driver. Today: `stats`, `binders`, `show`, `laziness`. Later: the lowering passes. |

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
```

## M1 — how much Haskell is left after GHC?

`h2r laziness` classifies every local binding that survives GHC's optimiser
and explains *why* it still exists, from two cross-checked sources: GHC's own
demand (strict / absent / used-once), occurrence and one-shot information,
and a syntactic occurrence analysis of our own (which case alternatives and
lambdas sit between the `let` and each use, and what each use *position*
demands of the value).

The one principle: emit deferred evaluation only where the optimised Core
still demonstrates conditional evaluation that Rust control flow cannot
trivially preserve — and note that memoisation is never needed for
*correctness* (only genuinely recursive values are); it preserves sharing.
Sinking a binding into every use site is always semantically valid.

Headline numbers on the tree at the repo root (GHC 9.6.7, `-O1`):

| | |
|---|---|
| Local bindings after optimisation | 6,156 |
| … functions / join points / values already in WHNF | 1,883 / 1,119 / 762 |
| … strict (`let` the simplifier didn't turn into `case`) | 148 |
| **Potential thunk sites** | **2,242** |
| … sinkable into an evaluating position (thunk vanishes) | 30 |
| … sinkable, but into a lazy argument (thunk moves) | 225 |
| … memo needed to keep sharing, captured by a many-entry lambda | 1,387 |
| … memo needed to keep sharing, shared on one path | 531 |
| … genuinely recursive values (knot-tying) | 69 |
| Top-level CAFs that are actually string literals | 2,426 of 2,755 |
| Genuine top-level thunks | 238 |

By binder origin, the memo population is mostly compiler-introduced:
`ds…` lazy pattern bindings from the desugarer (418, largely the lazy
`StateT`/`Writer` tuple plumbing in the checkers), `lvl…` full-laziness
float-outs (276 — GHC hoisting work out of lambdas; re-sinking is valid),
`eta…` (171), `$d…` dictionaries (94, gone after specialisation). The
user-named remainder (959) is dominated by derived `Functor`/`Foldable`/
`Traversable` instance internals in `ShellCheck.AST`, i.e. dictionary-
polymorphic code that also dissolves under monomorphisation.

The `let` census cannot see allocations CorePrep would introduce for
non-trivial arguments, so those are counted too: 21,837 non-trivial
arguments, of which 12,401 are already values (closures, saturated
constructors, partial applications), 935 sit in strict positions, and 8,235
sit in lazy fields / lazy parameters / unknown-callee positions — the latter
being where dictionary-passing and CPS (Parsec) code shows up.

Conclusions for the architecture: `Lazy<T>` is an escape hatch for a small,
well-defined residue (recursive values, plus whichever float-outs are worth
keeping shared), not the runtime model. The big levers are, in order,
specialisation/dictionary erasure, transformer collapsing, and let-sinking.

## M2 baseline — who receives the lazy arguments?

M2 is *abstraction collapse*: the remaining problem is not laziness but
GHC-generated abstraction structure (dictionaries, transformer plumbing, CPS,
float-outs) that looks lazy. Before transforming anything, `h2r laziness`
instruments every computation in a lazy or unknown argument position (8,384)
on two orthogonal axes: **resolution** (can the compiler see the callee?) and
**family** (which abstraction is the callee part of?). Family is judged from
the callee's defining module and, for local heads, its binding site and name
— so it catches the *structural* signatures of inlined abstractions, which is
how they actually appear in optimised Core: mtl's newtypes are gone and its
binds show up as tuple constructors; Parsec's combinators are inlined and show
up as its four continuations being applied.

| Resolution | | |
|---|---:|---:|
| known data constructor | 3,305 | 39.4% |
| known global function, signature covers the argument | 1,822 | 21.7% |
| known local function, signature covers the argument | 543 | 6.5% |
| class-op dispatch (resolved by specialisation) | 294 | 3.5% |
| higher-order parameter | 2,264 | 27.0% |
| past the callee's arity (applied to a call result) | 156 | 1.9% |
| imported without signature / non-variable head | 0 | 0% |

Of the 2,264 higher-order parameters, 2,108 are Parsec's `cok`/`cerr`/`eok`/
`eerr` continuations or `eta`-expanded parser functions being applied — 960
of the 969 `eta` sites are in `ShellCheck.Parser`. Genuinely unknown heads:
156 (1.9%).

| Attributable to | | |
|---|---:|---:|
| Parsec / CPS normalisation | 2,124 | 25.3% |
| constructor-field strategy (`:` 1,298, program constructors 396, other) | 1,984 | 23.7% |
| transformer collapse (boxed tuples 849, unboxed tuples 472) | 1,321 | 15.8% |
| dictionary specialisation (class-op dispatch 294, dfuns 216) | 510 | 6.1% |
| ordinary calls with a visible signature | 2,289 | 27.3% |
| unknown | 156 | 1.9% |

The "ordinary calls" bucket is dominated by string building —
`unpackAppendCString#` (573) and `++` (544) — i.e. diagnostic messages
assembled from lazy string appends; a `String` representation decision, not
a laziness one.

## What ShellCheck actually needs

Surveyed against the tree at the repo root:

* **Template Haskell** appears in 13 modules and is *only* `$quickCheckAll`;
  `striptests` removes it, so a production build needs neither TH nor
  QuickCheck.
* **No `unsafePerformIO`** anywhere.
* `Control.Monad.ST` / `Data.STRef` are used in exactly one place,
  `ShellCheck.CFGAnalysis`, and can lower to scoped Rust mutability.
* Extensions in use: `FlexibleContexts`, `DeriveGeneric`, `DeriveAnyClass`,
  `DeriveTraversable`, `PatternSynonyms`, `PatternGuards`, `ViewPatterns`,
  `RankNTypes`, `MultiWayIf`, `OverloadedStrings`, `NondecreasingIndentation`,
  `NoMonomorphismRestriction` — all handled by GHC before we see Core.
* Library surface to replace on the Rust side: `base`, `containers`, `array`,
  `bytestring`, `directory`, `filepath`, `mtl`/`transformers` (collapsed into
  explicit parameters), `parsec` (the substantial one), `regex-tdfa`, `aeson`,
  `Diff`, `fgl`.

## Conformance

The `prop_*` corpus that `striptests` removes is the oracle: build ShellCheck
once with GHC and once through this pipeline, run the same inputs through both,
and require identical diagnostics, positions, fixes, exit status and output
formats. Differential fuzzing over generated shell scripts extends it.
