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
| `rust/crates/h2r-core-ir` | Rust-side model of that JSON. Flattened into an arena on load — iteratively, since Core `App` spines nest far deeper than a stack likes — with parent links and edge kinds, so every later pass is worklist-driven. Owns the two canonical identities every analysis reads: which binder a `Var` occurrence refers to (`resolve`; GHC uniques are *not* unique in optimised Core), and which `App` an application spine is rooted at (`spine_root`, cast- and tick-transparent). Includes a depth-limited Core pretty-printer. |
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

Headline numbers on the tree at the repo root (GHC 9.6.7, `-O1`). The
"before" column is what the census reported until M2.1 stage 2 fixed two
bugs in it — occurrences keyed by GHC unique, and spines split by casts;
both are described under [M2.1](#m21--proving-parsecs-cps-roles):

| | before | now |
|---|---:|---:|
| Local bindings after optimisation | 6,156 | 6,156 |
| … functions / join points / values already in WHNF | 1,883 / 1,119 / 762 | 1,883 / 1,119 / 762 |
| … strict (`let` the simplifier didn't turn into `case`) | 148 | 148 |
| … lazy, used at most once / possibly many times | 39 / 2,134 | 39 / 2,134 |
| **Potential thunk sites** | **2,242** | **2,242** |
| … sinkable into an evaluating position (thunk vanishes) | 12 | 14 |
| … sinkable, but into a lazy argument (thunk moves) | 243 | 254 |
| … … of all the sinkable ones, into mutually exclusive branches | 56 | 65 |
| … … the rest being single-use | 199 | 203 |
| … memo needed to keep sharing | 1,918 | 1,905 |
| … … captured by a many-entry lambda | 1,387 | **1,242** |
| … … shared on one path | 531 | **663** |
| … genuinely recursive values (knot-tying) | 69 | 69 |
| Top-level CAFs that are actually string literals | 2,426 of 2,755 | 2,426 of 2,755 |
| Genuine top-level thunks | 238 | 238 |

GHC's cardinality and our syntactic occurrence analysis agree on 2,291 of
the 2,321 thunk candidates they both have an opinion about (9 both-once,
2,282 both-many); GHC says once where the syntax says many 25 times, and
the reverse 5 times.

The class split did not move at all: it is decided by GHC's own demand and
cardinality, which are per-binder and were never wrong. What moved is
*where each binding's uses are*, which is what decides whether a thunk has
to be memoised — 145 bindings turn out not to be captured by a many-entry
lambda after all, and 132 more turn out to be genuinely shared on a path.

By binder origin, the memo population is mostly compiler-introduced:
`ds…` lazy pattern bindings from the desugarer (416, largely the lazy
`StateT`/`Writer` tuple plumbing in the checkers), `lvl…` full-laziness
float-outs (276 — GHC hoisting work out of lambdas; re-sinking is valid),
`eta…` (164), `$d…` dictionaries (94, gone after specialisation). The
user-named remainder (955) is dominated by derived `Functor`/`Foldable`/
`Traversable` instance internals in `ShellCheck.AST`, i.e. dictionary-
polymorphic code that also dissolves under monomorphisation.

The `let` census cannot see allocations CorePrep would introduce for
non-trivial arguments, so those are counted too: 21,670 non-trivial
arguments, of which 12,269 are already values (closures, saturated
constructors, partial applications), 1,049 sit in strict positions, one in a
parameter the callee never uses, and 8,351 sit in lazy fields / lazy
parameters / unknown-callee positions — the latter being where
dictionary-passing and CPS (Parsec) code shows up.

Conclusions for the architecture: `Lazy<T>` is an escape hatch for a small,
well-defined residue (recursive values, plus whichever float-outs are worth
keeping shared), not the runtime model. The big levers are, in order,
specialisation/dictionary erasure, transformer collapsing, and let-sinking.

## M2 baseline — who receives the lazy arguments?

M2 is *abstraction collapse*: the remaining problem is not laziness but
GHC-generated abstraction structure (dictionaries, transformer plumbing, CPS,
float-outs) that looks lazy. Before transforming anything, `h2r laziness`
instruments every computation in a lazy or unknown argument position (8,351)
on three axes:

* **resolution** — what kind of head receives the argument;
* **tier** — what is actually *proven* about the code that runs when the
  argument is consumed. This is the honest axis: recognising a Parsec
  continuation by name attributes the site to a pass, it does not resolve
  the target. Since M2.1 the tier is the better of two *independent*
  proofs — the syntactic resolution below, and whatever the Parsec CPS
  recogniser proves structurally — and neither may weaken the other;
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
unevaluated — and claims no strictness (`Position::UnsaturatedArg`, 108
sites, 68 of them `$fApplicativeParsecT2` building parser values).

| Resolution (the syntactic head axis) | | |
|---|---:|---:|
| known data constructor | 3,317 | 39.7% |
| known global function, signature covers the argument | 1,848 | 22.1% |
| known local function, signature covers the argument | 536 | 6.4% |
| class-op dispatch | 294 | 3.5% |
| higher-order parameter | 2,216 | 26.5% |
| global applied past its signature | 5 | 0.1% |
| local lambda applied past its parameters | 27 | 0.3% |
| closure from a known call, target not followed | 86 | 1.0% |
| closure from a case/let computation | 22 | 0.3% |
| imported without signature / non-variable head | 0 | 0% |

| Target tier | resolution only | with the Parsec proof | |
|---|---:|---:|---:|
| exact target proven | 5,701 | **7,800** | 93.4% |
| finite target set proven | 0 | **8** | 0.1% |
| producer known, returned target unresolved | 118 | 118 | 1.4% |
| target unresolved | 2,532 | **425** | 5.1% |

The first column is what the head alone proves; the second adds
[M2.1](#m21--proving-parsecs-cps-roles)'s structural proof of Parsec's CPS
roles, which resolves 2,107 sites the head could say nothing about. The
resolution axis is unchanged by it: those 2,107 heads are still
higher-order parameters, and still belong to the Parsec normalisation pass.

The 425 that remain unresolved are, exactly:

| | |
|---:|---|
| 294 | class-op dispatch — waiting on closed-world instance enumeration |
| 99 | functional arguments of inlined folds and traversals (`f` 55, `f1` 14, `ww` 10, `ds1` 8, and 12 others), deliberately left alone as a control group |
| 22 | closures computed by a `case` or `let` of function type |
| 10 | heads the *name*-based family attribution called Parsec and the structural recogniser rejects: mtl plumbing (`RWST`, `StateT`) outside `ShellCheck.Parser` |

The 118 producer-known sites are known-origin closures awaiting target
analysis, not proven dynamic: 86 are bound to the result of a call to a
known function or constructor, 27 are local lambdas applied past their
manifest parameters, 5 are globals applied past their signature. Following
a producer's result to the closure it returns is a separate analysis.

| Attributable to | | |
|---|---:|---:|
| Parsec / CPS normalisation | 2,305 | 27.6% |
| constructor-field strategy (`:` 1,310, program constructors 396, other) | 1,996 | 23.9% |
| transformer collapse (boxed tuples 849, unboxed tuples 472, mtl calls 13) | 1,334 | 16.0% |
| dictionary specialisation (class-op dispatch 294, dictionaries 57) | 351 | 4.2% |
| ordinary calls with a visible signature | 2,266 | 27.1% |
| unknown | 99 | 1.2% |

A `$f…` name with a numeric suffix (`$fApplicativeParsecT2`) is not a
dictionary but a floated-out instance-method body that GHC has already
dispatched to; it is attributed by module, which moves 172 sites from the
dictionary family to Parsec. The "ordinary calls" bucket is dominated by
string building — `unpackAppendCString#` (573) and `++` (543) — i.e.
diagnostic messages assembled from lazy string appends; a `String`
representation decision, not a laziness one.

## M2.1 — proving Parsec's CPS roles

The census puts 2,532 of the 8,351 lazy/unknown argument sites in the
"target unresolved" tier, and 2,117 of those have a head that *looks* like
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
  `state·cok·cerr·eok·eerr`, 336 have one leading parser argument, and so on);
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
  more than one embedding, and 20 of those are resolved from the
  worker/wrapper pair (`R9-WRAPPER-MAP`), leaving 6 with a proven **finite
  role set** rather than a single slot;
* worker/wrapper also **unboxes `State` into its representation fields**,
  leaving parser calls with no `State`-typed argument at all (83 calls).
  A run of continuation-shaped arguments is not on its own evidence of a
  parser call — an ordinary higher-order function can take two of them — so
  the missing state has to be *explained*, and the rule says how.

### Rules

Every verdict records the rule that produced it, and every rule states which
level of evidence it rests on. The hierarchy, strongest first:

1. **lexical binder identity** — which binder an occurrence resolves to;
2. **structural function / application shape** — lambda chains, spines,
   case alternatives;
3. **worker/wrapper dataflow** — a wrapper is an eta-expansion of its
   worker, so roles transfer across the call;
4. **GHC type compatibility** — the five type shapes the representation is
   made of (`State s u`, `ParseError`, the two continuation shapes);
5. **alpha-normalised textual type comparison** — candidate generation and
   corroboration only. It can equate two genuinely distinct type variables,
   so it is only ever used to *refuse* a region, never as the support for a
   verdict;
6. **binder names** — diagnostics only. Nothing reads one.

| Rule | Evidence | Meaning |
|---|---|---|
| `R1-LAYOUT` | 2 over 4 | A lambda chain's parameter types carry `State s u` followed by a run of continuation types embedding into the `cok·cerr·eok·eerr` template. |
| `R1-TYPE-AGREE` | 4, 5 | All of a region's continuations agree on the state type and on the result type, compared modulo type-variable renaming (GHC prints the same tyvar `b` on one binder and `b1` on the next). A filter on `R1-LAYOUT`, able only to refuse. |
| `R2-PARSER-CALL` | 2 over 4 | A call whose *arguments* are a `State s u` followed by a continuation run embedding into the template, plus ≤2 trailing transformer arguments. A data constructor head is never a parser call. |
| `R2-UNBOXED-STATE/destructured` | 1, 2, 4 | The state argument is absent, and the three arguments standing in its place are the representation fields, in field order, of one `case … of State f0 f1 f2` — the state was destructured at this very call. |
| `R2-UNBOXED-STATE/worker-layout` | 1, then the callee's `R1-LAYOUT` | …or the callee is itself a recognised region whose own parameters are (state fields, continuation run) in exactly this order, saturated by this call. |
| `R2-UNBOXED-STATE/forwarded` | 1, then the caller's `R1-LAYOUT` | …or the three arguments are the enclosing worker's own unboxed state, forwarded unchanged. |
| `R3-CONT-CALL` | 1, 2, corroborated by 4 | A continuation applied to exactly its arity — (value, state, error) or (error). The head's type fixes what each slot means, and every argument whose own type is readable is checked against it. |
| `R3-CONT-CALL-TRAILING` | as above | …plus the two trailing transformer arguments. |
| `R3-CONT-CALL-ETA` | as above | …applied to fewer arguments, the shortfall supplied by eta-reduction: the enclosing continuation position owes exactly the missing ones (`\x -> cok v` is `\x s e -> cok v s e`). |
| `R3-CONT-RETURNED` | 1, 2 | A continuation value returned into a continuation position that owes exactly what it still needs. |
| `R4-PROP-CONT` | 1, 2 | A continuation passed unchanged into a continuation slot of a recognised parser call. The ok/err kind must match and is checked on every propagation; the *slot* need not match its own role — the inlined `<?>` passes `cok` into the `eok` slot. |
| `R5-STATE-IN-CONT-CALL` | 1, 2 | The state in the state slot of a continuation call. |
| `R6-STATE-IN-PARSER-CALL` | 1, 2 | The state in the state slot of a parser call. |
| `R7-STATE-SCRUTINISED` | 2 | `case s of State …`. |
| `R8-DERIVED-CONT` | 1, 4 | A let-bound value of continuation type inside a region is a derived continuation and has to satisfy the same use rules (229 of them; GHC builds partial applications like `let lvl = cok ()`). Its role is only ever the kind-restricted pair of slots, never a single slot. |
| `R9-WRAPPER-MAP` | 3 over 1, 2 | An ambiguous embedding resolved from the worker/wrapper pair: the wrapper's chain carries all four slots (so its own embedding is unambiguous) and its body is one saturated call forwarding its parameters into the worker, which fixes the worker's roles. Only accepted if the resulting mapping is one the worker's own layout already allowed. |

Anything else — stored in a constructor field, returned from something that
is not a continuation position, passed to an unknown callee, passed in a
slot of the wrong kind, applied to an argument whose type contradicts the
continuation's — rejects, and the rejection takes the whole region with it.
Chains that carry continuation-typed parameters but do not form a region are
recorded too (`skipped`), so nothing disappears silently.

#### Role identity is not role forwarding

Two different facts about a continuation are kept apart and never conflated.
A continuation's **role** is what it *is*, fixed once by `R1-LAYOUT` (and
possibly narrowed by `R9-WRAPPER-MAP`). A **forwarding** is a continuation
being handed to a parser call in some slot: that chooses a target for one
path, and says nothing about what the continuation is. Every edge carries
both — `source_role` and `destination` — and no rule ever rewrites a role
because of a forwarding. It matters in practice: of 7,436 forwardings on
the `-O1` dump, **1,168 send a continuation into a slot other than its own
role** (`<?>` and friends reusing `cok` as the labelled parser's `eok`).

A call's slots come from its argument types, which cannot always tell the
consumed pair from the empty pair. Where the callee is a region in the same
module whose parameters already have exact roles, the callee is the
authority on what its own parameters are, and narrowing the call by it makes
38 further forwarding destinations exact.

### Scoping: uniques are not unique

GHC's simplifier duplicates terms without freshening their binders.
`ShellCheck.Parser` has 41,874 binders over only 8,257 distinct uniques —
`a1V6r` alone names 1,269 different `wild2` binders — and across the 28
modules, 116,340 binders share 42,572 uniques. Anything keyed by unique
therefore merges inlined copies of the same term.

Variable identity is consequently settled once, in the IR: `Module::resolve`
walks the module with an explicit environment stack and gives every local
`Var` occurrence the `BinderId` that actually binds it; imports resolve to
`Ref::Global`, whose unique is a linkage key into the imported-id table and
nothing more. No analysis compares a local unique. `Module::binder_in_scope`
and `Module::scoping_violations` check the result against the definition of
lexical scope independently, and report 0 violations over all 107,929 local
occurrences of the `-O1` dump (and 328,110 of profile D).

This was a real bug, not a hypothetical one: **54,408 of the 107,929 local
occurrences — 50.4% — resolved to a different binder afterwards.** The M1
`let` census had been computing use counts, exclusive-branch splits and
lambda capture on merged occurrence sets; see the before/after column in
[M1](#m1--how-much-haskell-is-left-after-ghc).

The second correction is smaller and purely mechanical: `Module::spine` has
always looked through the casts the simplifier leaves inside an application
spine, but the census' own "is this a spine root?" test did not, so a spine
broken by a `Cast` was walked twice and its inner arguments counted twice —
167 duplicate argument sites out of 21,837. There is now one `spine_root` in
the IR, defined as the exact converse of `spine`, and every analysis uses it.

### Results on the `-O1` dump

```
candidate regions                               1301   (all in ShellCheck.Parser)
proven                                          1301
rejected                                           0
chains with continuation params but no region      0
… with a state parameter in the chain           1296
… with all four continuation slots present      1215
… with trailing transformer parameters             8
… with an ambiguous slot embedding                 6   (26 before R9-WRAPPER-MAP)
derived (let-bound) continuations promoted       229
```

| Edges by kind | | Edges by rule | |
|---|---:|---|---:|
| `ConsumedOk` / `ConsumedErr` | 2,568 / 2,710 | `R2-PARSER-CALL` | 2,516 |
| `EmptyOk` / `EmptyErr` | 2,291 / 1,953 | `R2-UNBOXED-STATE/destructured` | 77 |
| `{ConsumedOk\|EmptyOk}` (finite) | 86 | `R2-UNBOXED-STATE/forwarded` | 6 |
| `{ConsumedErr\|EmptyErr}` (finite) | 76 | `R3-CONT-CALL` | 2,198 |
| `CallParser` | 2,599 | `R3-CONT-CALL-ETA` | 47 |
| role invocations / forwardings | 2,248 / 7,436 | `R3-CONT-CALL-TRAILING` | 3 |
| | | `R4-PROP-CONT` | 7,436 |

`R2-UNBOXED-STATE/worker-layout` proves nothing on this dump — every call
with an unboxed state is already explained by the destructuring at the call
site or by the enclosing worker's own fields — but it is the rule that
covers a call to a visible worker from outside any region, so it stays. If
none of the three explanations applied, the calls would not be parser calls
and the continuations handed to them would reject their regions: dropping
just the "forwarded" case costs 5 regions, 6 edges and 13 proven sites.

| The 2,117 Parsec-shaped unresolved sites | | |
|---|---:|---:|
| exact role proven | 2,099 | 99.1% |
| finite role set proven | 8 | 0.4% |
| Parsec region recognised, target unresolved | 0 | 0% |
| rejected as non-Parsec / escape | 10 | 0.5% |

The ten rejects are the whole non-`ShellCheck.Parser` remainder: heads
named `eta` whose types are `RWST Parameters [TokenComment] Cache Identity ()`,
`RWST r [TokenComment] s Identity b` and `StateT s Identity b` — mtl
plumbing that the name-based family attribution called Parsec and the
structural recogniser does not. A further **473** proven edges sit at sites
*outside* that population (426 exact, 47 finite): heads the census resolves
as ordinary local functions because they are let-bound (`lvl…`, and the
derived continuations of `R8`). They are reported on their own line and
never folded into the 2,117.

The 99 non-Parsec fold/traversal callbacks (`f`, `f1`, `ww`, `ds1`, …) are
left alone as a control group: none of them is recognised.

### Feeding the proof back into the census

`Callee` carries a third, orthogonal field: what the recogniser proved about
the call. `Resolution` and `Family` keep saying exactly what they said — the
head is still a higher-order parameter, the site still belongs to the Parsec
normalisation pass — and the **tier** becomes the better of the two
independent proofs, so neither can weaken the other. (Before this rule was
`min`, the recogniser's coarser "one of two slots" was downgrading 43 sites
the census already resolved exactly.)

The accounting closes two independent ways:

* **by difference** — 2,532 sites were in the unresolved tier; 2,107 are now
  proven (2,099 exact + 8 finite, i.e. precisely the population's proven
  sites); 2,532 − 2,107 = **425** remain;
* **by enumeration** — 294 class-op dispatch + 99 fold/traversal callbacks +
  22 computed closures + 10 Parsec rejects = **425**.

Both come to the same number, itemised in the
[M2 residual table](#m2-baseline--who-receives-the-lazy-arguments).

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
| memo, under many-entry lambda | 1,242 | 1,328 | 1,509 | 3,904 | 3,778 | 3,757 |
| `lvl…` float-outs | 307 | 340 | **89** | 275 | 275 | 271 |
| genuine CAFs | 238 | 230 | **53** | 34 | 34 | 34 |
| recursive values | 69 | 65 | 45 | 119 | 119 | 119 |
| class-op dispatch sites | 294 | 305 | 314 | 314 | 314 | 314 |
| unsaturated call positions | 108 | 120 | 197 | 473 | 473 | 472 |
| lazy/unknown computations | 8,351 | 9,268 | 10,039 | 25,771 | 24,186 | 24,188 |
| … exact target tier | **93%** | 92% | 91% | 90% | 90% | 90% |
| … finite target set | 8 | 8 | 25 | 80 | 80 | 102 |
| … producer known, target unresolved | 118 | 124 | 125 | 318 | 318 | 318 |
| … unresolved tier | **5%** | 5% | 6% | 8% | 7% | 7% |
| … exact *by the head alone*, before the Parsec proof | **68%** | 66% | 64% | 47% | 49% | 49% |
| … Parsec CPS | **27%** | 29% | 32% | 41% | 40% | 38% |
| thunk sites per 1k nodes | 5 | 5 | 5 | 6 | 6 | 6 |

Findings:

* **The flags change the program's size, not its shape.** Per-node ratios
  are flat across A–C; D–F are worse. `-O1` is the most Rust-shaped profile
  on every resolvability metric.
* **Inlining replicates Parsec's CPS, it does not dissolve it.** Exposing
  all unfoldings triples the Core and takes Parsec-attributed sites from
  2,305 to 10,816. The Parsec normalisation pass is unavoidable; it should
  run on the smallest Core that still exhibits the pattern. The structural
  recogniser does keep up with the replication — the exact-target tier only
  falls from 93% to 90% across A→D — which is the point of proving the
  roles rather than counting names.
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
  the memo population grows by 18% (the captured-by-a-lambda part by 21%).
  Better to keep the hoisting and lower top-level constants to statics.
* Static-argument transformation trims ~7% of nodes; an extra strictness
  pass changes nothing.

Decision: stay on `-O1` for the survey dump. Revisit per pass (e.g. SAT
before ownership inference) rather than globally.
