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
| `matrix.sh` | Runs `extract.sh` under a matrix of GHC optimisation profiles (into `compiler/matrix/<profile>/`), for `h2r compare`. |
| `extract.sh` | Driver: stages a copy of the ShellCheck sources, runs upstream's `striptests` (which removes QuickCheck and Template Haskell), builds it with the plugin enabled, and collects the dumps. The tree at the repo root is never touched. |
| `rust/crates/h2r-core-ir` | Rust-side model of that JSON. Flattened into an arena on load — iteratively, since Core `App` spines nest far deeper than a stack likes — with parent links and edge kinds, so every later pass is worklist-driven. Includes a depth-limited Core pretty-printer. |
| `rust/crates/h2r-analysis` | Analyses over the arena. Today: the residual-laziness census (`laziness.rs`), callee resolution and target tiers (`callee.rs`), the shape/position predicates (`shape.rs`), the single binding-site-first signature lookup they all read (`scope.rs`), and the structural Parsec-CPS recogniser (`parsec.rs`). |
| `rust/crates/h2r-rt` | Runtime for *residual* laziness only — `Lazy<T>`, `Shared<T>`. The design rule is that as little of this as possible should survive into generated code. |
| `rust/crates/h2r-cli` | The `h2r` driver. Today: `stats`, `binders`, `show`, `laziness`, `compare`, `parsec`. Later: the lowering passes. |

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
instruments every computation in a lazy or unknown argument position (8,447)
on three axes:

* **resolution** — what kind of head receives the argument;
* **tier** — what is actually *proven* about the code that runs when the
  argument is consumed. This is the honest axis: recognising a Parsec
  continuation by name attributes the site to a pass, it does not resolve
  the target;
* **family** — which abstraction the head belongs to, judged from its
  defining module and, for local heads, its binding site and name. This
  catches the *structural* signatures of inlined abstractions, which is how
  they appear in optimised Core: mtl's newtypes are gone and its binds show
  up as tuple constructors; Parsec's combinators are inlined and show up as
  its four continuations being applied.

Every arity and demand-signature question goes through one lookup
(`scope::Scope::head_sig`): the binding-site binder for anything bound in
the module, the imported-id table otherwise. GHC does not keep the `IdInfo`
on occurrence `Var`s of locals current, and the id table is populated from
occurrences, so reading it for a local can return stale arity and
strictness. Argument *position*, partial-application *shape* and callee
*resolution* all read the same source and cannot disagree. A second guard
follows GHC's demand transformer: a signature's argument demands apply only
to calls that supply at least the signature's arity. An undersaturated call
is a partial application — a function value that holds the argument
unevaluated — and claims no strictness (`Position::UnsaturatedArg`, 109
sites, 68 of them `$fApplicativeParsecT2` building parser values).

| Resolution | | |
|---|---:|---:|
| known data constructor | 3,317 | 39.3% |
| known global function, signature covers the argument | 1,851 | 21.9% |
| known local function, signature covers the argument | 543 | 6.4% |
| class-op dispatch | 294 | 3.5% |
| higher-order parameter | 2,303 | 27.3% |
| global applied past its signature | 5 | 0.1% |
| local lambda applied past its parameters | 33 | 0.4% |
| closure from a known call, target not followed | 81 | 1.0% |
| closure from a case/let computation | 20 | 0.2% |
| imported without signature / non-variable head | 0 | 0% |

| Target tier | | |
|---|---:|---:|
| exact target proven | 5,711 | 67.6% |
| finite target set proven | 0 | 0% |
| producer known, returned target unresolved | 119 | 1.4% |
| target unresolved | 2,617 | 31.0% |

"Finite target set" is empty by construction: class-op dispatch (294) moves
there once the closed-world instance enumeration exists, and Parsec's
continuations (1,141 `cok`/`cerr`/`eok`/`eerr` sites plus 978 `eta` sites,
960 of the latter in `ShellCheck.Parser`) once the CPS normalisation
replaces them with control flow. Until then they are *unresolved*: 2,119 of
the 2,303 higher-order parameters are Parsec-shaped, 184 are not (`f`, `go1`,
`f1`, `ww`: functional arguments of inlined folds and traversals).

The 119 producer-known sites are known-origin closures awaiting target
analysis, not proven dynamic: 81 are bound to the result of a call to a
known function or constructor, 33 are local lambdas applied past their
manifest parameters, 5 are globals applied past their signature. Following
a producer's result to the closure it returns is a separate analysis.

| Attributable to | | |
|---|---:|---:|
| Parsec / CPS normalisation | 2,311 | 27.4% |
| constructor-field strategy (`:` 1,310, program constructors 396, other) | 1,996 | 23.6% |
| transformer collapse (boxed tuples 849, unboxed tuples 472, mtl calls 13) | 1,334 | 15.8% |
| dictionary specialisation (class-op dispatch 294, dictionaries 57) | 351 | 4.2% |
| ordinary calls with a visible signature | 2,271 | 26.9% |
| unknown | 184 | 2.2% |

A `$f…` name with a numeric suffix (`$fApplicativeParsecT2`) is not a
dictionary but a floated-out instance-method body that GHC has already
dispatched to; it is attributed by module, which moves 172 sites from the
dictionary family to Parsec. The "ordinary calls" bucket is dominated by
string building — `unpackAppendCString#` (573) and `++` (543) — i.e.
diagnostic messages assembled from lazy string appends; a `String`
representation decision, not a laziness one.

## M2.1 — proving Parsec's CPS roles

The census puts 2,617 of the 8,447 lazy/unknown argument sites in the
"target unresolved" tier, and 2,119 of those have a head that *looks* like
one of Parsec's four continuations (`cok`, `cerr`, `eok`, `eerr`) or an
eta-expanded parameter (`eta`). That attribution is by name, so it is a
diagnostic and nothing more: GHC names *every* eta-expanded parameter
`eta` (in `readArray` a head named `eta` is a continuation, not a parser),
renames unused ones `ds`, and a binder named `cok` is not evidence of
anything. `h2r parsec` replaces the name with a proof.

### The representation, as it survives the optimiser

`ParsecT s u m a` is a function of a state and four continuations. After
inlining, the newtype is gone and what is left is a lambda chain whose
**parameter types** still say exactly what each parameter is — the plugin
dumps GHC's pretty-printed type for every binder, and those types survive
optimisation:

```
\words                                                   -- the parser's own arguments
  eta :: State [Char] UserState                          -- state
  eta :: Token -> State [Char] UserState -> ParseError -> R   -- cok
  eta :: ParseError -> R                                 -- cerr
  eta :: Token -> State [Char] UserState -> ParseError -> R   -- eok
  eta :: ParseError -> R                                 -- eerr
  -> …
```

Discovered from the dump, not assumed:

* the five parameters are always **contiguous and in Parsec's own order**,
  as a suffix of the lambda chain (836 chains are exactly
  `state·cok·cerr·eok·eerr`, 332 have one leading parser argument, and so on);
* `R` is `SCBase m b = ReaderT (Environment m) (StateT SystemState m) b`,
  which erases to **two trailing arguments** of type `Environment m` and
  `SystemState`. Eight regions are eta-expanded that far (e.g.
  `ShellCheck.Parser` node 8104, `\s1 eok eta::Environment m eta::SystemState`),
  and three continuation calls carry them (node 10115: `eok v s err env st`,
  five arguments);
* **worker/wrapper drops absent continuations**, so a run can be shorter
  than four and any subset of the slots may be missing (`state·cerr·eok·eerr`,
  `state·cok·eok·eerr`, …). The run is therefore matched as a *subsequence*
  of the four-slot template. 1,215 of 1,301 regions keep all four; 26 have
  more than one embedding and so get a proven **finite role set** rather
  than a single slot;
* worker/wrapper also **unboxes `State` into its fields**, leaving parser
  calls with no `State`-typed argument at all (83 calls).

### Rules

Every verdict records the rule that produced it.

| Rule | Meaning |
|---|---|
| `R1-LAYOUT` | A lambda chain's parameter types carry `State s u` followed by a run of continuation types embedding into the `cok·cerr·eok·eerr` template. |
| `R1-TYPE-AGREE` | All of a region's continuations agree on the state type and on the result type, compared modulo type-variable renaming (GHC prints the same tyvar `b` on one binder and `b1` on the next). |
| `R2-PARSER-CALL` | A call whose *arguments* are a `State s u` followed by a continuation run embedding into the template, plus ≤2 trailing transformer arguments. A data constructor head is never a parser call. |
| `R2-UNBOXED-STATE` | The same, with the state argument absent because worker/wrapper unboxed it. |
| `R3-CONT-CALL` | A continuation applied to exactly its arity — (value, state, error) or (error). The argument *types* follow from the head's type, so arity is the whole check. |
| `R3-CONT-CALL-TRAILING` | …plus the two trailing transformer arguments. |
| `R3-CONT-CALL-ETA` | …applied to fewer arguments, the shortfall supplied by eta-reduction: the enclosing continuation position owes exactly the missing ones (`\x -> cok v` is `\x s e -> cok v s e`). |
| `R3-CONT-RETURNED` | A continuation value returned into a continuation position that owes exactly what it still needs. |
| `R4-PROP-CONT` | A continuation passed unchanged into a continuation slot of a recognised parser call. The slot need not match its own role: the inlined `<?>` passes `cok` into the `eok` slot. |
| `R5-STATE-IN-CONT-CALL` | The state in the state slot of a continuation call. |
| `R6-STATE-IN-PARSER-CALL` | The state in the state slot of a parser call. |
| `R7-STATE-SCRUTINISED` | `case s of State …`. |
| `R8-DERIVED-CONT` | A let-bound value of continuation type inside a region is a derived continuation and has to satisfy the same use rules (229 of them; GHC builds partial applications like `let lvl = cok ()`). |

Anything else — stored in a constructor field, returned from something that
is not a continuation position, passed to an unknown callee, passed in a
slot of the wrong kind — rejects, and the rejection takes the whole region
with it. Chains that carry continuation-typed parameters but do not form a
region are recorded too (`skipped`), so nothing disappears silently.

### Scoping: uniques are not unique

GHC's simplifier duplicates terms without freshening their binders.
`ShellCheck.Parser` has 41,874 binders over only 8,257 distinct uniques —
`a1V6r` alone names 1,269 different `wild2` binders. Every occurrence is
therefore resolved to its innermost enclosing binder by an explicit-stack
scope walk. Keying occurrences by unique, as the M1 `let` census still
does, conflates copies.

### Results on the `-O1` dump

```
candidate regions                               1301   (all in ShellCheck.Parser)
proven                                          1301
rejected                                           0
chains with continuation params but no region      0
… with a state parameter in the chain           1296
… with all four continuation slots present      1215
… with an ambiguous slot embedding                26
derived (let-bound) continuations promoted       229
```

| Edges | |
|---|---:|
| `ConsumedOk` / `ConsumedErr` | 2,568 / 2,710 |
| `EmptyOk` / `EmptyErr` | 2,246 / 1,932 |
| finite-set edges (`{ConsumedOk\|EmptyOk}`, `{ConsumedErr\|EmptyErr}`) | 131 / 97 |
| `CallParser` | 2,599 |

| The 2,119 Parsec-shaped unresolved sites | | |
|---|---:|---:|
| exact role proven | 2,090 | 98.6% |
| finite role set proven | 20 | 0.9% |
| Parsec region recognised, target unresolved | 0 | 0% |
| rejected as non-Parsec / escape | 9 | 0.4% |

The nine rejects are the whole non-`ShellCheck.Parser` remainder: heads
named `eta` whose types are `RWST Parameters [TokenComment] Cache Identity ()`,
`RWST r [TokenComment] s Identity b` and `StateT s Identity b` — mtl
plumbing that the name-based family attribution called Parsec and the
structural recogniser does not. A further **478** proven edges sit at sites
*outside* that population (430 exact, 48 finite): heads the census resolves
as ordinary local functions because they are let-bound (`lvl…`, and the
derived continuations of `R8`). They are reported on their own line and
never folded into the 2,119.

The 184 non-Parsec fold/traversal callbacks (`f`, `go1`, `ww`) are left
alone as a control group: none of them is recognised.

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


## GHC flag matrix — can GHC be tuned into producing more Rust-shaped Core?

`compiler/matrix.sh` extracts Core under six profiles and `h2r compare`
puts the census side by side. The hypothesis was that `-fno-full-laziness`
plus aggressive specialisation would remove float-outs, dictionaries and
much of the memo population before any pass of ours runs.

What the matrix tests, exactly: the flags apply to the **ShellCheck package
only**. Dependencies (parsec, mtl, containers, regex-tdfa, ...) are built
with their Hackage defaults, so a profile answers "which flags give the best
ShellCheck Core against the dependency interfaces as shipped". Rebuilding the
dependencies with exposed unfoldings is a different experiment — aggressive
specialisation can only use an imported unfolding that is actually there.

Per profile, `compiler/matrix/<P>/` keeps the dumps, the built `shellcheck`
binary, cabal's `plan.json` and a `provenance` record (source and plugin
hashes, toolchain versions, module list), so behavioural comparison and
timing never need a rebuild. All six profiles were extracted from the same
source and plugin revision, produce the same 28 modules, and their binaries
give byte-identical output on a sample script in the tty, JSON and gcc
formats. Re-extracting profile A reproduces the census to the last count:
the dumps are deterministic.

| | A `-O1` | B `-O2` | C = B `-fno-full-laziness` | D = C `-fspecialise-aggressively -fexpose-all-unfoldings` | E = D `-fstatic-argument-transformation` | F = E `-fstrictness-before=2` |
|---|---:|---:|---:|---:|---:|---:|
| Core nodes | 409,622 | 469,070 | 498,825 | 1,197,283 | 1,116,489 | 1,119,151 |
| extraction time | 101 s | 114 s | 111 s | 252 s | 237 s | 241 s |
| thunk sites | 2,242 | 2,389 | 2,849 | 7,311 | 7,131 | 7,109 |
| memo, under many-entry lambda | 1,387 | 1,614 | 1,953 | 6,107 | 5,915 | 5,891 |
| `lvl…` float-outs | 307 | 340 | **89** | 275 | 275 | 271 |
| genuine CAFs | 238 | 230 | **53** | 34 | 34 | 34 |
| recursive values | 69 | 65 | 45 | 119 | 119 | 119 |
| class-op dispatch sites | 294 | 305 | 314 | 314 | 314 | 314 |
| unsaturated call positions | 109 | 121 | 255 | 531 | 531 | 528 |
| lazy/unknown computations | 8,447 | 9,390 | 10,280 | 26,160 | 24,552 | 24,561 |
| … exact target tier | **67%** | 65% | 63% | 47% | 49% | 49% |
| … producer known, target unresolved | 119 | 123 | 229 | 232 | 233 | 216 |
| … unresolved tier | **30%** | 32% | 34% | 51% | 49% | 49% |
| … Parsec CPS | **27%** | 29% | 31% | 42% | 40% | 39% |
| thunk sites per 1k nodes | 5 | 5 | 5 | 6 | 6 | 6 |

Findings:

* **The flags change the program's size, not its shape.** Per-node ratios
  are flat across A–C; D–F are worse. `-O1` is the most Rust-shaped profile
  on every resolvability metric.
* **Inlining replicates Parsec's CPS, it does not dissolve it.** Exposing
  all unfoldings triples the Core and takes Parsec-attributed sites from
  2,311 to 11,140. The Parsec normalisation pass is unavoidable; it should
  run on the smallest Core that still exhibits the pattern.
* **GHC's specialiser does not finish the dictionary job.** Class-op
  dispatch sites *rise* (294 → 314) under `-fspecialise-aggressively`; the
  remaining dispatch is in code GHC cannot specialise (dictionaries stored
  in data, polymorphic recursion, unexposed instances). Closed-world
  specialisation is ours to do.
* **Full laziness is doing useful work for us.** Turning it off removes the
  `lvl…` float-outs and most CAFs as predicted, but the constant
  expressions it had hoisted to top level — string literals, partial
  applications, ~7,700 top-level bindings in all — are *static data* in
  Rust; inside functions they become lets captured by inner lambdas, and
  the memo population grows by 40%. Better to keep the hoisting and lower
  top-level constants to statics.
* Static-argument transformation trims ~7% of nodes; an extra strictness
  pass changes nothing.

Decision: stay on `-O1` for the survey dump. Revisit per pass (e.g. SAT
before ownership inference) rather than globally.
