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
