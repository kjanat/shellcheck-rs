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
| `rust/crates/h2r-analysis` | Analyses over the arena. Today: the generic aggregate def-use walk every saturated-constructor flow is built on (`flow.rs`), the residual-laziness census (`laziness.rs`), callee resolution and target tiers (`callee.rs`), the shape/position predicates (`shape.rs`), the single binding-site-first signature lookup they all read (`scope.rs`), the structural Parsec-CPS recogniser (`parsec.rs`), the tuple def-use census that separates transformer plumbing from real values (`tuples.rs`, a client of `flow.rs` plus the four tuple-specific rules), the independent re-derivation of every removable tuple verdict (`verify.rs`, which shares nothing with `tuples.rs` but the IR), the normalised scalar view and per-node tuple provenance (`scalar.rs`), the representation-boundary check that says whether all those views can be applied at once (`boundary.rs`), and the cross-milestone link from M1's thunk sites to M2.2's tuples (`link.rs`), and the constructor-field census that says what is evaluated when each field is read (`fields.rs`), and the list-flow census with its explicit library demand-semantics table (`lists.rs`, `lists/axioms.rs`). |
| `rust/crates/h2r-rt` | Runtime for *residual* laziness only — `Lazy<T>`, `Shared<T>`. The design rule is that as little of this as possible should survive into generated code. |
| `rust/crates/h2r-cli` | The `h2r` driver. Today: `stats`, `binders`, `show` (with both proof objects inline and per-node evidence), `laziness`, `compare`, `parsec` (including `--cfg`, the recovered parser graph), `tuples` (including `--verify`, `--scalar`, `--boundaries` and the milestone accounting), `fields` (the constructor-field census), `lists` (the list-flow census, including `--axioms`). Later: the lowering passes. |

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
cargo run --release --bin h2r -- tuples ../core-json --module Main --boundaries --explain
cargo run --release --bin h2r -- show ../core-json ShellCheck.Checks.Commands 4714   # + its tuple proof
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

| | before | now | after tuple normalisation |
|---|---:|---:|---:|
| Local bindings after optimisation | 6,156 | 6,156 | — |
| … functions / join points / values already in WHNF | 1,883 / 1,119 / 762 | 1,883 / 1,119 / 762 | — |
| … strict (`let` the simplifier didn't turn into `case`) | 148 | 148 | — |
| … lazy, used at most once / possibly many times | 39 / 2,134 | 39 / 2,134 | — |
| **Potential thunk sites** | **2,242** | **2,242** | **2,150** |
| … sinkable into an evaluating position (thunk vanishes) | 12 | 14 | 14 |
| … sinkable, but into a lazy argument (thunk moves) | 243 | 254 | 251 |
| … … of all the sinkable ones, into mutually exclusive branches | 56 | 65 | — |
| … … the rest being single-use | 199 | 203 | — |
| … memo needed to keep sharing | 1,918 | 1,905 | **1,816** |
| … … captured by a many-entry lambda | 1,387 | **1,242** | **1,162** |
| … … shared on one path | 531 | **663** | **654** |
| … genuinely recursive values (knot-tying) | 69 | 69 | 69 |
| Top-level CAFs that are actually string literals | 2,426 of 2,755 | 2,426 of 2,755 | — |
| Genuine top-level thunks | 238 | 238 | — |

The third column is the [cross-milestone
link](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples):
92 of these thunk sites are the lazy selectors of a tuple M2.2 proves
removable, independently verifies *and* shows can be removed together with
every other removal at the same representation boundary, so they disappear
with it rather than needing anything of their own. `remaining + explained = 2,242` is
asserted, and the criterion is deliberately narrow — see that section for
what is *not* claimed.

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

Discovered from the dump — and then **checked against the types at every
region**, since what one dump exhibits is not a property of the
representation (`R1-UNPARSER-SIG`, `R1-TRAILING-ERASURE`):

* the five parameters are always **contiguous and in Parsec's own order**,
  as a suffix of the lambda chain (836 chains are exactly
  `state·cok·cerr·eok·eerr`, 336 have one leading parser argument, and so
  on). Order is checked as an embedding into the `cok·cerr·eok·eerr`
  template and the shape of each continuation is checked position by
  position against `unParser`'s — `a -> State s u -> ParseError -> r` and
  `ParseError -> r`, with `a`, `s`, `u` and `r` agreeing across all five. A
  chain whose continuation types are present in any other order forms no
  region and is reported;
* `R` is `SCBase m b = ReaderT (Environment m) (StateT SystemState m) b`,
  which erases to **two trailing arguments** of type `Environment m` and
  `SystemState`. Eight regions are eta-expanded that far (e.g.
  `ShellCheck.Parser` node 8104, `\s1 eok eta::Environment m eta::SystemState`),
  and three continuation calls carry them (node 10115: `eok v s err env st`,
  five arguments); 28 parser calls carry them too. The permitted count and
  types are computed *per region* from that region's own `r`, so the 139
  regions whose `r` is a bare `m b` may carry none at all;
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
| `R1-UNPARSER-SIG` | 4 over 2 | Those parameter types *are* `unParser`'s argument list, checked position by position: every ok continuation is `a -> State s u -> ParseError -> r`, every error continuation is `ParseError -> r`, `State` is applied to exactly `s` and `u`, and the run is in `unParser`'s own order. A chain carrying continuation types in any other order forms no region and is reported. |
| `R1-TYPE-AGREE` | 4, 5 | `a`, `s`, `u` and `r` agree across all five, compared modulo type-variable renaming (GHC prints the same tyvar `b` on one binder and `b1` on the next). A filter on `R1-UNPARSER-SIG`, able only to refuse. |
| `R1-TRAILING-ERASURE` | 4 | A region's trailing parameters, and a call's trailing arguments, are a prefix — by count *and* by type — of what that region's own result type `r` erases to: `ReaderT r m a` is `r -> m a` and `StateT s m a` is `s -> m (a, s)`, so `SCBase m b` erases to `Environment m` then `SystemState`, and a bare `m b` erases to nothing at all. Derived per region from `r`; never a fixed "at most two". GHC's void token `(# #)` is zero-width and is not part of the erasure. |
| `R2-PARSER-CALL` | 2 over 4 | A call whose *arguments* are a `State s u` followed by a continuation run embedding into the template, plus whatever `R1-TRAILING-ERASURE` allows after it. A data constructor head is never a parser call. |
| `R2-UNBOXED-STATE/destructured` | 1, 2, 4 | The state argument is absent, and the three arguments standing in its place are the representation fields, in field order, of one `case … of State f0 f1 f2` — the state was destructured at this very call. |
| `R2-UNBOXED-STATE/worker-layout` | 1, then the callee's `R1-LAYOUT` | …or the callee is itself a recognised region whose own parameters are (state fields, continuation run) in exactly this order, saturated by this call. |
| `R2-UNBOXED-STATE/forwarded` | 1, then the caller's `R1-LAYOUT` | …or the three arguments are the enclosing worker's own unboxed state, forwarded unchanged. |
| `R3-CONT-CALL` | 1, 2, corroborated by 4 | A continuation applied to exactly its arity — (value, state, error) or (error). The head's type fixes what each slot means, and every argument whose own type is readable is checked against it. |
| `R3-CONT-CALL-TRAILING` | as above | …plus trailing transformer arguments, as many and of exactly the types its own result type erases to (`R1-TRAILING-ERASURE`). |
| `R3-CONT-CALL-ETA` | as above | …applied to fewer arguments, the shortfall supplied by eta-reduction: the enclosing continuation position owes exactly the missing ones (`\x -> cok v` is `\x s e -> cok v s e`). |
| `R3-CONT-RETURNED` | 1, 2 | A continuation value returned into a continuation position that owes exactly what it still needs. |
| `R4-PROP-CONT` | 1, 2 | A continuation passed unchanged into a continuation slot of a recognised parser call. The ok/err kind must match and is checked on every propagation; the *slot* need not match its own role — the inlined `<?>` passes `cok` into the `eok` slot. |
| `R5-STATE-IN-CONT-CALL` | 1, 2 | The state in the state slot of a continuation call. |
| `R6-STATE-IN-PARSER-CALL` | 1, 2 | The state in the state slot of a parser call. |
| `R7-STATE-SCRUTINISED` | 2 | `case s of State …`. |
| `R8-DERIVED-CONT` | 1, 4 | A let-bound value of continuation type inside a region **that dataflow connects to it** is a derived continuation and has to satisfy the same use rules (129 of them; GHC builds partial applications like `let lvl = cok ()`). Connected means its right-hand side mentions one of the region's continuation parameters, its state or its trailing parameters — transitively through other derived continuations, since GHC chains them. Its role is only ever the kind-restricted pair of slots, never a single slot. A let of continuation type that is *not* connected (100 of them) is no evidence of anything: it is excluded from the region's obligations and counted separately. |
| `R9-WRAPPER-MAP` | 3 over 1, 2 | An ambiguous embedding resolved from the worker/wrapper pair: the wrapper's chain carries all four slots (so its own embedding is unambiguous) and its body is one saturated call forwarding its parameters into the worker, which fixes the worker's roles. Only accepted if the resulting mapping is one the worker's own layout already allowed. |

Anything else — stored in a constructor field, returned from something that
is not a continuation position, passed to an unknown callee, passed in a
slot of the wrong kind, applied to an argument whose type contradicts the
continuation's — rejects, and the rejection takes the whole region with it.
Chains that carry continuation-typed parameters but do not form a region are
recorded too (`skipped`), so nothing disappears silently.

#### Role identity is not role forwarding

Two different facts about a continuation are kept apart and never conflated.
A continuation's **role** is what it *is*, fixed once by `R1-LAYOUT` /
`R1-UNPARSER-SIG` (and
possibly narrowed by `R9-WRAPPER-MAP`). A **forwarding** is a continuation
being handed to a parser call in some slot: that chooses a target for one
path, and says nothing about what the continuation is. Every edge carries
both — `source_role` and `destination` — and no rule ever rewrites a role
because of a forwarding. It matters in practice: of 7,242 forwardings on
the `-O1` dump, **988 send a continuation into a slot other than its own
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
derived (let-bound) continuations promoted       129
… let-bound continuations excluded as unconnected 100
```

| Edges by kind | | Edges by rule | |
|---|---:|---|---:|
| `ConsumedOk` / `ConsumedErr` | 2,430 / 2,710 | `R2-PARSER-CALL` | 2,516 |
| `EmptyOk` / `EmptyErr` | 2,249 / 1,953 | `R2-UNBOXED-STATE/destructured` | 77 |
| `{ConsumedOk\|EmptyOk}` (finite) | 66 | `R2-UNBOXED-STATE/forwarded` | 6 |
| `{ConsumedErr\|EmptyErr}` (finite) | 76 | `R3-CONT-CALL` | 2,192 |
| `CallParser` | 2,599 | `R3-CONT-CALL-ETA` | 47 |
| role invocations / forwardings | 2,242 / 7,242 | `R3-CONT-CALL-TRAILING` | 3 |
| | | `R4-PROP-CONT` | 7,242 |

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

### What the type-derived layout checks found

`R1-LAYOUT` used to *assume* the layout this dump exhibits — the five
parameters contiguous and in Parsec's order, and "at most two" trailing
transformer arguments. Both are now derived from the types at every region
and every call, and reported:

```
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

On `-O1` the checks change nothing: all 1,301 regions survive them, the
accounting is identical to the digit, and the assumption turns out to have
been true. They are not vacuous, though — the erasure is computed per
region and it differs between regions: 1,162 regions have result type
`SCBase m b` (or its expansion) and may carry exactly `Environment m` then
`SystemState`, while **139 regions have a bare `m b`** — the inlined
`parsec` library code, where the base monad is still a variable — and may
carry *nothing*. The old rule would have let two arbitrary arguments
through there.

Across the flag matrix the checks do bite, which is the point of running
them. Chains refused because what follows the continuation run is not that
erasure: 0 (A), 4 (B), 12 (C), 32 (D, E, F) — typically a *second*
representation starting again (`State [Char] UserState`, a value, another
`ParseError -> …`), which is not one clean `unParser` argument list.
Calls refused that a fixed "at most two" would have taken: 0, 0, 2, 58, 22,
37. Nothing on any profile is refused by `R1-UNPARSER-SIG` or
`R1-TYPE-AGREE`: the continuation types themselves really are `unParser`'s
everywhere, which is the assumption worth having checked. GHC's void token
`(# #)` — which `-fno-full-laziness` and `-fexpose-all-unfoldings` leave on
nullary workers — is zero-width and is excluded from the erasure; counting
it as a trailing argument would have refused 5 further chains on C and 166
on D.

`R8`'s connectivity requirement is the one that moves the `-O1` numbers.
100 of the 229 let-bound continuation-typed binders inside regions have no
dataflow connection to the region they sit in, and promoting them was
loading regions with obligations they never owed. Excluding them costs 200
edges (6 invocations, 194 forwardings) and **changes no cell of the
accounting**: the population stays 2,117 = 2,099 exact + 8 finite + 0
region-unresolved + 10 rejected, and the 473 proven edges outside the
population stay 473 (426 exact, 47 finite). Their *types* are still read
when a call to one is classified — that is what keeps the region's state
explained where it is passed to one — they simply prove nothing and can
reject nothing.

### Auditing one site

`h2r show` loads the proof object by default for a module that has regions
(`--no-parsec` turns it off). It annotates region entries, role binders,
their occurrences and the spine roots of proven edges inline, and prints
the evidence for the node asked about:

```
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

That is the `<?>` case in full: the binder *is* the region's `cok`, and
this use forwards it into the labelled parser's `eok` slot. The two facts
are printed separately and neither is derived from the other.

### The recovered graph

`h2r parsec --cfg <region-entry-node>` (or `--cfg-all --module M`, and
`--json` for either) prints the region's control-flow graph: its parameters
with their roles, and every edge — each terminator with the values it hands
back, and each parser call with the continuation filling every slot, each
successor naming where that continuation comes from (own parameter, wrapped
lambda, nested region, or derived continuation). Nothing is lowered: the
graph is the deliverable.

```
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

Every parameter appears exactly once and every edge of the region appears
in exactly one line — the four forwardings above are folded into the call
whose slots they fill, and `unplaced` reports any edge that is not
accounted for (it is empty for all 1,301 regions).

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

### M2.1 acceptance

**The criterion is that every site the Parsec normalisation pass will
transform is structurally proven — not that coverage is high.** A site the
recogniser cannot prove has to end up in a named bucket with a machine-
readable reason, and a "proven" verdict has to follow from a stated rule
over the Core; binder names are diagnostics and nothing reads one. Coverage
is a consequence, reported but secondary.

Against the `-O1` dump, all of the following hold.

**The population is partitioned.** Of the 2,117 census sites whose head is
Parsec-shaped and whose target the head alone cannot resolve:

| | | |
|---|---:|---:|
| exact role proven | 2,099 | 99.1% |
| finite role set proven | 8 | 0.4% |
| Parsec region recognised, target unresolved | 0 | 0% |
| rejected as non-Parsec / escape | 10 | 0.5% |
| **population** | **2,117** | |

The four buckets are disjoint and exhaustive by construction (one
`Bucket` per site) and the sum is asserted, not eyeballed.

**The census tiers, after feeding the proof back:**

| Target tier | resolution only | with the Parsec proof | |
|---|---:|---:|---:|
| exact target proven | 5,701 | **7,800** | 93.4% |
| finite target set proven | 0 | **8** | 0.1% |
| producer known, returned target unresolved | 118 | 118 | 1.4% |
| target unresolved | 2,532 | **425** | 5.1% |

**The residual closes both ways.** By difference: 2,532 − 2,107 proven
(2,099 exact + 8 finite) = **425**. By enumeration: 294 class-op dispatch +
99 fold/traversal callbacks + 22 computed closures + 10 Parsec rejects =
**425**. The 2,107 are reported as a note beside the tier table, not as a
sub-row of the 425 — they are what left that tier, not part of it.

**Every rule states its evidence level**, and no rule rests on a weaker
level than it claims:

| Level | Evidence | Rules |
|---|---|---|
| 1 | lexical binder identity | `R3-CONT-CALL`, `R3-CONT-CALL-ETA`, `R3-CONT-RETURNED`, `R4-PROP-CONT`, `R5`, `R6`, `R8` (the connection) |
| 2 | structural function / application shape | `R1-LAYOUT`, `R2-PARSER-CALL`, `R2-UNBOXED-STATE/*`, `R7` |
| 3 | worker/wrapper dataflow | `R9-WRAPPER-MAP`, and the callee-narrowing of a call's slots |
| 4 | GHC type compatibility | `R1-UNPARSER-SIG`, `R1-TRAILING-ERASURE`, `R8` (the shape), and the argument-type corroboration of `R3-CONT-CALL` |
| 5 | alpha-normalised textual type comparison | `R1-TYPE-AGREE` only, and only to refuse |
| 6 | binder names | nothing |

**What the two new checks found** is above under
[type-derived layout checks](#what-the-type-derived-layout-checks-found):
on `-O1`, `R1-UNPARSER-SIG` and `R1-TRAILING-ERASURE` refuse nothing and
confirm the assumption they replace (the erasure is nevertheless
region-specific — 139 regions may carry no trailing argument at all);
`R8`'s connectivity requirement excludes 100 of 229 let-bound
continuations, costing 200 edges and moving no accounting cell.

**One rule fires on nothing here.** `R2-UNBOXED-STATE/worker-layout` proves
nothing on `-O1` (it is exercised by a unit test, and does fire on profiles
C and D). It covers a call to a visible worker from outside any region, so
it stays — dropping the sibling "forwarded" case costs 5 regions, 6 edges
and 13 proven sites, which is the scale of what an unexplained missing
state costs.

**What remains, and what each thing is waiting for:**

| | | |
|---:|---|---|
| 294 | class-op dispatch | closed-world instance enumeration |
| 99 | functional arguments of inlined folds and traversals | deliberately untouched control group; a *residual*, not a proof |
| 22 | closures computed by a `case` or `let` | returned-closure analysis |
| 10 | mtl plumbing outside `ShellCheck.Parser` | rejected by the recogniser; the name-based family attribution called them Parsec |
| 118 | producer known, target unresolved | following a producer's result to the closure it returns |

**How to audit a site.** `h2r show <dir> <module> <node>` prints the Core
around the node with the proof object's marks inline and the node's own
evidence — rule ids, source nodes, the binder, and intrinsic role and
destination slot separately — as a footer; `h2r parsec <dir> --cfg <entry>`
prints the whole region's graph, parameters and edges, with every
successor named. Both are shown above. `h2r parsec --explain` lists every
region's evidence, edges and rejects, and every population site that is not
an exact edge.

## M2.2 — which tuples are transport, and which are values

The [M2 census](#m2-baseline--who-receives-the-lazy-arguments) attributes
1,321 lazy argument sites to boxed (849) and unboxed (472) tuples and files
them under "transformer collapse". That is an attribution *by constructor*,
and a constructor is not a proof: `(a, b)` is not intrinsically transformer
noise — ShellCheck puts pairs in `Map`s, in constructor fields and in its
own return types. `h2r tuples` replaces the constructor with **def-use**.

Argument sites are also only part of the population. A tuple is constructed
just as often as a `let` right-hand side, as a case alternative's result, or
as a function's return value — and the M2 census, which walks argument
positions, sees none of those. Stage 1 therefore censuses **every saturated
tuple construction**, boxed and unboxed separately, and maps the 1,321 onto
it afterwards.

Stage 2 then tried to break it. The acceptance rule of this milestone is
that **every tuple that will be removed has a complete def-use proof**;
coverage is secondary, because a wrong "removable" is a miscompile and a
wrong "Preserve" is only a missed optimisation. So stage 2 wrote a
[second, independent verifier](#the-independent-verifier) of every removable
verdict, went looking for [eight shapes](#the-adversarial-cases) a removable
verdict could be wrong on, made the [tuple-in-tuple](#tuple-in-tuple) rule
consistent, [read the Parsec proof object](#coupling-the-two-proof-objects)
instead of giving up on its continuations, split the residual by what is
holding the value, and removed a fate whose name claimed more than its rule
proved.

Stage 3 turns the verdict into a **view** and closes the accounting. For
every removal it prints [what replaces the tuple](#the-normalised-scalar-view),
line by line, with the rule and the source nodes — and asserts that the
view is complete, the way the recovered Parsec graph asserts that no edge
is unplaced. It puts the same provenance [inline in `h2r
show`](#auditing-one-construction), states the milestone's
`before = normalised + preserved + unsupported`
[accounting](#accounting) — where *normalised* means removable **and**
independently verified, so a verdict with only one proof behind it counts
as unsupported — and measures [how much of M1's residual
laziness](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples)
this milestone actually explains.

Stage 4 asks whether all those views can be applied **at the same time**.
Each is complete for its own flow; a formal parameter and a function's
result are shared slots, so a removable tuple that reaches one has to agree
with everything *else* that reaches it. `boundary.rs` enumerates every
[representation boundary](#composing-the-views-can-all-1453-be-applied-at-once)
a removable flow crosses and every producer of it — from the IR's
occurrences, not from the flow walk — and downgrades every flow that crosses
one the producers do not agree on. Still no Rust and still no rewrite of the
Core: the proof and the view are the deliverable.

### The population, and why the name is not the proof

A construction is selected by `T0-TUPLE-CON`: the head of an application
spine is a data constructor from `ghc-prim` whose occurrence is `(,…)` in
`GHC.Tuple*` or `(#,…#)` in `GHC.Prim`, whose `repArity` agrees with the
name's comma count, whose fields are all lazy, and which is applied to
exactly `repArity` value arguments. The name *selects* (evidence level 6);
the saturation (2) and the `DataConInfo` (4) are what the rest of the
analysis reads, and **no fate is ever decided by a name**. Tuple
constructors that are *not* a saturated construction are recorded
separately, so nothing disappears silently; on the `-O1` dump there are
none at all — every tuple constructor in 28 modules is applied to exactly
its fields.

### Following the value

Each construction gets a `TupleFlow`, built by a worklist over **value
locations**. A location is a node *plus the number of value arguments still
owed* before the tuple appears: 0 means the node's value is the tuple, `k`
means it is a closure that returns the tuple after `k` more arguments.
That debt is what lets the walk leave a function — ascending past a lambda
raises it, a call site that pays it exactly is a location of the tuple
again — and it is why the analysis is interprocedural from the first
construction it looks at. The two shapes the dump is full of both need it:

* a lazy-RWS step returns its result triple, so its consumer is whoever
  calls the enclosing lambda, and that lambda is usually *inside* a case
  alternative rather than bound directly (`$wchecker = \cmd -> case … of
  Just x -> \eta2 eta3 -> (,,) …`), so the debt is paid three arguments up;
* a CPR worker returns `(# _, _ #)` and each call site scrutinises it.

The walk is a worklist with an explicit stack, like every other traversal
here, keyed on (node, debt) so it terminates; a location budget (20,000)
turns a pathological flow into an honest `Unresolved` rather than a hang.
On `-O1` nothing comes near it — the largest flow visits 2,023 locations
and the mean is 19 — but on the inlining-heavy profiles the transitive
[tuple-in-tuple](#tuple-in-tuple) rule does reach it: 4 flows on B and 2
each on C–F end as `flow-exceeded-the-location-budget`. That is a coverage
loss in the safe direction and the independent verifier refuses those
flows too.

### Rules

| Rule | Evidence | Meaning |
|---|---|---|
| `T0-TUPLE-CON` | 2 over 4, name selects only (6) | The population: a saturated application of ghc-prim's boxed or unboxed tuple constructor, `repArity` agreeing with the name and all fields lazy. |
| `T1-LET-BOUND` | 1 | The value is a `let`/top-level right-hand side: its uses are that binder's resolved occurrences. |
| `T2-SCRUTINISED` | 2 | `case t of (a, b) -> …`, with exactly *arity* field binders: taken apart, the box does not survive the match. |
| `T3-SELECTED` | 1 over 2 | …and the alternative returns exactly its *i*-th binder: a field selection, which is how the desugarer turns a lazy pattern `~(b, s, w)` into one selector thunk per field. |
| `T4-RETUPLE` | 1 over 2 | A construction every one of whose fields is the *matching* projection of one and the same binder: a field-wise copy, recorded as a consumer of the tuple it copies. All *n* scrutinees must resolve to the same binder — two textually equal expressions are not evidence. |
| `T5-PASSED-LOCAL` | 1 over 2 | Value argument *i* of a saturated call to a binder bound in this module to a manifest lambda chain, which is **not exported and never occurs as a value**: the flow continues at that parameter's occurrences. |
| `T6-RETURNED` | 2 over 1 | The value is reached from a binder through a debt of *k* arguments: the binder is a function returning the tuple, and its occurrences are call sites to follow. |
| `T7-CALL-RESULT` | 3 over 1, 2 | A call site paying exactly the debt: the spine root is a value location of the tuple again. Paying part of it leaves a partial application, which is followed too. |
| `T8-CASE-BINDER-ALIAS` | 1 | The case binder of a scrutiny aliases the whole tuple; its occurrences are followed, so a match that also keeps the box cannot be mistaken for one that consumes it. |
| `T9-STORED` | 2 over 4 | A value argument of a saturated data-constructor application: a real allocation holds it. |
| `T10-OPAQUE-CALL` | 1, 4 | An argument of a call this module cannot see into — an import, class-op dispatch, a partial application, an unknown higher-order callee. |
| `T11-ESCAPE` | 2 | Any other use, with a machine-readable reason: applied as a function, bound to or returned from an exported binder, a closure handed to a callee or stored in a constructor, a case that is not one full tuple alternative. |
| `T12-NESTED` | 2 over 3 | A field of *another* tuple whose own fate is proven removable: the box holding it will not exist, so the inner tuple's consumers are the uses of the outer's *i*-th field binder at every scrutiny of the outer — transitively. When the outer is not removable this is `T9-STORED` as before. |
| `T13-PARSEC-CONT` | the Parsec proof's own level, then 3 | The value argument of a continuation call [M2.1](#m21--proving-parsecs-cps-roles) proves, where that proof also resolves the continuation to lambdas inside this module: the flow continues at their value parameters. The region graph is *read*; no role, slot or edge is re-derived here. |
| `T14-FORCED` | 2 | `case t of _ { DEFAULT -> … }`: the tuple is forced whole and no field is read. Forcing a constructor application is a no-op, so this neither keeps the box alive nor counts as a read. |

Two of the rules are about whether the rewrite is *possible*, not about
where the value goes, and both were added in stage 2 after the independent
verifier refused what stage 1 accepted:

* removing a tuple that is **passed into** a local callee means splitting
  that callee's parameter, so every call site of the callee has to be
  visible and rewritable — `T5-PASSED-LOCAL` now requires the callee to be
  neither exported nor ever used as a value (`callee-parameter-cannot-be-split`);
* removing a tuple that a **closure returns**, where that closure is itself
  handed to a parameter, would change the parameter's type and therefore
  every other closure that reaches it — which this flow does not see. That
  is refused (`closure-returning-the-tuple-is-passed-into-a-parameter`),
  not guessed.

### Fates

Every construction lands in exactly one bucket, by this precedence:

| Fate | Rule | When |
|---|---|---|
| `Preserve` | `F4-PRESERVE` | A proven real value: stored in a constructor field, held in a partial application, or handed to a function outside the module. An allocation that exists — this wins over everything. |
| `Unresolved` | `F5-UNRESOLVED` | A use the rules cannot follow, with the reason. Never guessed either way. |
| `WorkerReturn` | `F2-WORKER-RETURN` | The tuple crosses a return and **every** consumer reads its fields: a multi-value return. |
| `ScalarReplace` | `F1-SCALAR-REPLACE` | Every consumer reads fields and the box never outlives them, in the function that built it — including where it is passed to a known local callee, whose parameter becomes the fields. |

Passing a tuple *into* a known callee is deliberately not a "return": the
box still never outlives its scrutinies, so it stays `ScalarReplace`.

**Stage 1's fifth fate, `StateThread`, is gone.** It separated a returned
tuple whose consumers include a lazy selection or a field-wise re-tupling
from one that is only ever scrutinised. That is a real difference — it says
whether the fields are demanded together or one at a time — but it is not a
different *fate*: both are removed the same way, as a multi-value return,
and no structural rule distinguishes "a state being threaded" from "a
worker's result". Naming a fate after a monad transformer it was not proven
to be is exactly the mistake this milestone exists to avoid. So the split is
kept as a **fact on the flow** (`TupleFlow::selected`, proved by `T3` and
`T4`, reported beside the fate table) and the two fates are one. On `-O1`
279 of the 302 former `StateThread`s are `WorkerReturn` and 23 are now
`Unresolved` for the closure-into-a-parameter reason above.

### The independent verifier

`h2r tuples <dir> --verify` re-derives every removable verdict a second
time, from scratch, with code that shares nothing with `tuples.rs` beyond
the IR (`h2r-analysis/src/verify.rs`: its own selection of the population,
its own name test, its own walk). It is deliberately blunt — one verdict,
removable or not — and it enumerates, for one construction, every alias the
tuple can be reached under (the binder it is bound to, every case binder,
the parameter of every local callee it is handed to, the call sites of every
function that returns it) and requires that **every occurrence of every
alias** is a scrutiny, a lazy selection or a further alias, and that the
whole chain is closed within the module.

It found **94 disagreements** on the first run, all reported under one
reason, which on inspection were two different things.

* **30 were the verifier being too blunt.** Its first cut refused any
  function that returns the tuple and does not occur *only* as the head of a
  saturated call — which also refuses a **partial application** (`let f =
  handleCommand a b c d` in `ShellCheck.CFG`, then `f` applied to the last
  two). A partial application is not an escape: the closure is local, the
  walk follows it, and every one of its own uses is checked. The rule was
  narrowed to the case that actually blocks the rewrite — a closure handed
  to a *parameter*, where the parameter's other producers are invisible —
  which is a weakening of the verifier and is why it is written down here.
  The 30 are removable and stayed removable.
* **64 were the census over-claiming**, and became the two new rules above:
  the tuple's own uses are all reads, but the rewrite needs a signature
  change the flow does not prove is possible. They are now `Unresolved`
  with a reason, costing coverage rather than soundness.

After that:

| dump | removable verdicts | re-derived | disagreements | refused by [stage 4](#composing-the-views-can-all-1453-be-applied-at-once) |
|---|---:|---:|---:|---:|
| `-O1` (`compiler/core-json`, and matrix A) | 1,206 | 1,206 | **0** | 247 |
| B `-O2` | 1,464 | 1,464 | **0** | 277 |
| C | 1,360 | 1,360 | **0** | 334 |
| D | 2,504 | 2,504 | **0** | 1,497 |
| E | 2,538 | 2,538 | **0** | 1,497 |
| F | 2,539 | 2,539 | **0** | 1,501 |

The two sides also select the *same population* on every dump (0
constructions found by only one of them). The last column is the only thing
the verifier accepts and the census refuses: the flows the representation
boundary check downgraded after both walks agreed, which is a third rule
neither walk has rather than a disagreement between them. Seven of `-O1`'s
def-use verdicts (50 on D–F) used the one hop the verifier cannot derive on
its own, the Parsec continuation target, supplied to it as an input from the
other proof object rather than recomputed; on `-O1` all seven have since
been downgraded.

### The adversarial cases

Each shape below has a hand-built regression test in
`h2r-analysis/src/tests.rs` *and* a count in the real `-O1` dump, printed by
`--verify`, so that a hand-built test is never the only evidence a rule was
exercised.

| # | Shape | In `-O1` | Example | Stage 1 | Now |
|---|---|---:|---|---|---|
| 1 | two names for one tuple (let + case binder, or two lets), one escaping | 59 | `ShellCheck.Analytics` 46 | Preserve 2, Unres 22, State 1 | Preserve 2, Unres 57 — never removable |
| 1 | re-bound under a second `let` binder | 167 | `ShellCheck.ASTLib` 651 | 143 removable, 24 not | 108 removable, 59 not |
| 2 | two or more field reads | 1,246 | `Main` 2737 | 1,162 removable, 84 not | 1,020 removable, 226 not |
| 2 | read and then stored | 6 | `ShellCheck.Analytics` 46 | Preserve 6 | Preserve 6 — the store wins |
| 3 | returned from a *recursive* function | 722 | `Main` 2594 | 638 removable, 84 not | 555 removable, 167 not; terminates |
| 3 | threaded into a recursive callee (a `go` accumulator) | 19 | `ShellCheck.Analytics` 46 | 9 removable, 10 Preserve | 3 need a clone, 7 Preserve, 9 Unres |
| 4 | a field of another tuple, outer removable | 115 | `ShellCheck.Analytics` 1974 | **Preserve 115** | 62 removable, 53 not |
| 4 | a field of another tuple, outer not removable | 64 | `Main` 422 | Preserve 64 | Preserve 64 |
| 5 | an unboxed worker return re-boxed by its caller | 284 | `Main` 5018 | 236 removable, 48 not | 185 removable, 99 not |
| 5 | a boxed tuple unboxed into a local callee's parameters | 15 | `ShellCheck.Analytics` 46 | 3 removable, 12 not | 5 removable (3 of them need a clone), 10 not |
| 5 | returned from an exported wrapper of a local worker | 11 | `Paths_ShellCheck` 67 | Unresolved 11, unsplit | Unresolved 11, reason names both binders |
| 6 | returned from a closure whose call sites are all visible | 303 | `Main` 3762 | 450 removable, 3 Unres | **303 removable** |
| 6 | returned from a closure that is stored or consed | 248 | `Main` 2220 | Unresolved 248 | Unresolved 248, split by what holds it |
| 7 | the callee is a computed (case-selected) closure | 12 | `ShellCheck.AnalyzerLib` 3861 | Unresolved 12 | Unresolved 12 — never one alternative |
| 7 | a parameter reached from two or more call sites | 32 | `ShellCheck.Analytics` 46 | 12 removable, 20 not | 5 removable, 27 not |
| 8 | forced whole (`seq`), no field read | 2 | `ShellCheck.Analytics` 47426 | Preserve 2 (a store wins) | Preserve 2; the forcing reads no field |
| 8 | stored in a *strict* constructor field | 9 | `ShellCheck.Analytics` 47426 | Preserve 9 | Preserve 9 — stored, not scrutinised |
| 8 | a case that is not one full tuple alternative | 0 | — | — | would be Unresolved |

"Removable" is `ScalarReplace`, `WorkerReturn` or `RemovableWithClone`
(stage 1's `StateThread` counts as removable in the left column). The "In
`-O1`" counts of shapes 1 and 6 are themselves fate-dependent — they ask for
a tuple that is *not* removable, or for a closure whose call sites are all
visible — so they move when the fates do. Where the two columns differ it is
one of the stage-2 changes (the 106 in case 4, the 7 Parsec resolutions, the
64 refusals) or a stage-4 boundary downgrade.

Case 7 is the may-analysis question, and it is answered in two places. A
callee *computed* by a `case` is refused outright — picking either
alternative would be a guess. Where a parameter is followed, its uses are
the union over every call site that reaches it, which can only add
consumers: the second test builds a parameter that is scrutinised on one
path and stored on another and asserts that the store wins for *both*
producers. Case 4 is the one that changed a verdict in the other direction,
and case 3's `go`-accumulator test is the one that pins termination.

### Tuple in tuple

Stage 1 called a tuple stored in another tuple's field `Preserve`
("stored-in-a-tuple-field", 179 constructions), which is inconsistent: if
the *outer* box will not exist, the inner tuple is not "stored" in anything.
`T12-NESTED` makes the two agree. The fixpoint starts pessimistic — every
nested tuple `Preserve` — and only ever adds resolved nestings, so a
knot-tied cycle cannot bootstrap itself into being removable; on every dump
it settles in two rounds.

Of the 179: **106 become removable** (84 `WorkerReturn`, 22
`ScalarReplace`), 73 stay `Preserve` — 71 because the outer is not
removable, and 2 because the transitive walk found a *different* escape
(one a constructor field, one an imported lazy parameter).

### Coupling the two proof objects

The 50 constructions stage 1 left as "the callee is an unknown higher-order
value" are, 48 of them, Parsec continuations in `ShellCheck.Parser` — and
M2.1 already proves what those are. `tuples::parsec_hops` reads that proof
object (regions, their continuation parameters, the binder each region's
chain is bound to) and resolves the *value* of a continuation only when the
region graph closes over it: the region's parser is bound to a non-exported
binder, every occurrence of that binder is a call saturating the chain
exactly, and what fills the slot is a manifest lambda — directly, or through
another continuation parameter, followed the same way. Only an `ok`
continuation of the three-argument shape carries a value, and the proof
object is what says which one this is.

Of the 50: **7 resolve** (4 `ScalarReplace`, 3 `WorkerReturn`), 41 get a
reason that names the edge, and 2 are not Parsec at all
(`ShellCheck.AnalyzerLib`, `ShellCheck.Formatter.TTY`). The 41 break down as

| | |
|---:|---|
| 20 | the region's chain is not bound to a binder (it is a lambda written out at a call site) |
| 19 | the region's parser occurs somewhere as a value, so not every call of it is visible |
| 2 | a call of the region is not saturated exactly |

each recorded as `parsec-continuation-target-not-in-the-region-graph` with
the region and the continuation in the detail.

### Results on the `-O1` dump

2,584 saturated constructions — 1,765 boxed, 819 unboxed. Stage 1's numbers
are in the "before" columns; every difference is one of the four stage-2
changes above (the two new refusals, `T12-NESTED`, `T13-PARSEC-CONT`, and
folding `StateThread` away).

| arity | boxed | unboxed | | fate | before b/u | now b/u |
|---:|---:|---:|---|---|---:|---:|
| 2 | 887 | 568 | | ScalarReplace | 402 / 5 | **423 / 3** |
| 3 | 718 | 231 | | StateThread | 266 / 36 | — |
| 4 | 156 | 9 | | WorkerReturn | 31 / 664 | **338 / 689** |
| 5 | 0 | 9 | | Preserve | 657 / 0 | **551 / 0** |
| 6 | 3 | 1 | | Unresolved | 409 / 114 | **453 / 127** |
| 8 | 0 | 1 | | | | |
| 64 | 1 | 0 | | **total** | **1,765 / 819** | **1,765 / 819** |

1,453 constructions are proven removable by def-use (56%), up from 1,404; of
those, 657 have at least one field read on its own and the rest are read
whole. Stage 4 ([representation boundaries](#composing-the-views-can-all-1453-be-applied-at-once))
then takes 247 of those 1,453 back, because a def-use proof per tuple is not
a proof that all of them can be applied at the same time; the accounting
below is the post-boundary one.
Unboxed tuples are 84% `WorkerReturn`/`ScalarReplace` and **never**
`Preserve` — as they must be, since an unboxed tuple cannot be stored in a
lazy field. 551 boxed ones, 31%, are proven real values.

| Consumers | boxed | unboxed |
|---|---:|---:|
| Scrutinised | 899 | 2,089 |
| Selected (lazy selector) | 1,755 | 60 |
| Returned | 1,825 | 1,271 |
| StoredIn | 501 | 0 |
| NestedIn (a field of a removable tuple) | 333 | 0 |
| Retupled | 115 | 0 |
| PassedTo (known local, or a proven continuation) | 122 | 0 |
| PassedToUnknown | 86 | 0 |
| Forced | 2 | 0 |
| Escapes | 540 | 168 |

The census' 1,321 tuple-attributed argument sites still map onto this
population **one to one** (849 boxed + 472 unboxed, 0 unmapped, over 726
distinct constructions), and their fates are reported on their own:

| The 1,321 | before b/u | def-use b/u | after boundaries b/u |
|---|---:|---:|---:|
| ScalarReplace | 114 / 0 | 128 / 0 | **111 / 0** |
| StateThread | 225 / 29 | — | — |
| WorkerReturn | 5 / 435 | 375 / 463 | **56 / 463** |
| RemovableWithClone | — | — | **2 / 0** |
| Preserve | 324 / 0 | 144 / 0 | **144 / 0** |
| Unresolved | 181 / 8 | 202 / 9 | **536 / 9** |
| **population** | **849 / 472** | **849 / 472** | **849 / 472** |

### What the plumbing actually looks like

Two shapes account for nearly all of the transformer transport.

**The lazy-RWS re-tupling** (`ShellCheck.Checks.Commands` nodes 4714 and
4633, both printed in full by `--explain`): a step returns `(,,) b s w`
from `eta1`; its caller binds the result to `ds1` and reads all three
fields with lazy selector cases; those three selections are re-tupled into
the next step's result (`T4-RETUPLE` at node 4633), which is returned
again. The *inner* triple (4714) is a multi-value return — its four
consumers are the three selections and the copy, and it crosses a return —
while the *outer* copy (4633) is `Unresolved`, because the closure that
returns it ends up in a `CommandCheck` constructor, which is the
checks-in-a-top-level-list shape the residual is full of. The inner triple
is `Unresolved` too *after stage 4*: `eta1`'s return points do not all agree
on one representation, so its result cannot become three scalars however
complete the triple's own def-use proof is — which is precisely the failure
mode [stage 4](#composing-the-views-can-all-1453-be-applied-at-once) exists
to find. 467 boxed removable constructions have a field read on its own,
concentrated in `Checks.Commands`, `CFG`, `Checks.ShellSupport` and
`Analytics`; only 129 constructions are *proven* field-wise copies, so
re-tupling is the visible top of a much larger selector population (691
constructions have a `T3-SELECTED` consumer).

**The CPR worker return** (`ShellCheck.Analytics` node 30892): `$wgo`
returns `(# () , … #)`, both of its call sites `case` it apart at once. 667
unboxed constructions are multi-value returns; counting boxed and unboxed
together, the multi-value returns are concentrated in `Analytics` (291),
`CFG` (168), `CFGAnalysis` (99) and `Checks.ShellSupport` (99). The 136
boxed ones are mostly the *other* half of that shape: a caller re-boxing the
fields it just unpacked.

### What remains, and what each thing is waiting for

827 constructions are unsupported — 824 `Unresolved` and 3
`RemovableWithClone`. The residual is split by *where* the value went, so
the next milestone can pick each class up without re-analysing (the
constructor and callee names are diagnostics; the split is by what kind of
thing holds it):

| | | |
|---:|---|---|
| 244 | the flow's own proof stands, but a [representation boundary](#composing-the-views-can-all-1453-be-applied-at-once) it crosses is not a uniform split | a representation-agreement pass, or cloning |
| 187 | the closure that returns the tuple is passed to an **imported** call (`map` 107, `catch#` 25, `$wtext` 20, …) | closure/whole-program analysis |
| 134 | …**consed onto a list** | the checks-in-a-top-level-list shape; a closed-world list-of-closures pass |
| 114 | …**stored in a program constructor** (`CommandCheck` 51, `SystemInterface` 13, `ForShell` 11, …) | the same, per constructor |
| 67 | …**handed to a local callee's parameter** | the parameter's other producers: a higher-order representation agreement, not a def-use question |
| 41 | a proven Parsec continuation whose target the region graph does not close over | above |
| 11 | returned from an **exported wrapper of a local worker** | the *worker's* callers, not the wrapper's — which is why the split exists |
| 10 | …passed to a local binder that is not a lambda chain | returned-closure analysis |
| 7 | …held in a partial application | the same |
| 3 | …passed to a class-op | closed-world instance enumeration |
| 2 | returned from an exported function with no worker | callers outside the module |
| 2 | an unknown higher-order callee outside `ShellCheck.Parser` | returned-closure analysis |
| 1 | the argument lands past the callee's parameters | the same |
| 3 | …and only a specialised **clone** of the callee could carry the split | a cloning decision, which this milestone does not make |
| 1 | the callee's parameter cannot be split (the callee escapes) | closure analysis |

The `Preserve` side is 551, dominated by exactly what one would hope: 369
tuples consed into a list, 71 stored in another tuple that is itself a real
value, 52 handed to an imported function's lazy parameter (45 of them to
`++`), 40 stored in a program or library constructor (`Just` 28, `Bin` 9,
…), 19 passed through class-op dispatch.

### Accounting

Asserted in code, not eyeballed (`Accounting::check`): the boxed
constructions sum to the boxed fate counts and likewise for unboxed, and
every census tuple site either maps onto exactly one construction or
carries a reason (`flow.is_some() ^ reason.is_some()`). The nesting fixpoint
asserts its own convergence. The same assertions, and the independent
verifier, run on all six matrix profiles.

Stage 3 adds the milestone's own equation, per representation:

```
before = normalised + preserved + unsupported
```

*normalised* is a construction this milestone removes — removable **and**
re-derived by the [independent verifier](#the-independent-verifier);
*preserved* is `Preserve`; *unsupported* is `Unresolved` **plus any
removable verdict the verifier does not confirm**. A construction that only
one walk proves counts as unsupported, never as normalised: that is the
direction the acceptance rule points. The verifier therefore runs inside
`TupleCensus`, not behind `--verify` — it is part of the verdict, and
`--verify` only reports it.

*normalised* is narrowed once more by stage 4: a flow that crosses a
[representation boundary](#composing-the-views-can-all-1453-be-applied-at-once)
that is not a uniform split is not normalised either, whether its own proof
holds or not.

```
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

The unsupported residual is itemised by the *kind* of thing holding the
value (the [table above](#what-remains-and-what-each-thing-is-waiting-for)),
and the itemisation is asserted to sum to the unsupported total.

### The normalised scalar view

Proving a tuple is transport is not the same as saying what replaces it.
`h2r tuples --scalar <construction-node>` (and `--scalar-all`, `--json`)
prints the program with that tuple gone, at the level of the IR — nothing
is lowered and no Core is rewritten. The construction's fields become named
scalars `f0…f{n-1}`; every consumer becomes bindings over them; every line
names the nodes it reads and the rule that justifies it:

```
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

| Consumer | Rule | The view |
|---|---|---|
| `case t of (a, b) -> e` | `T2-SCRUTINISED` | `a := f0; b := f1` |
| a lazy selector `case t of (_, s, _) -> s` | `T3-SELECTED` | `s := f1` — and the selector thunk goes with it |
| a field-wise re-tupling | `T4-RETUPLE` | the copy's own fields *are* `f0…`, with that construction's own fate printed beside it |
| passed into a local callee | `T5-PASSED-LOCAL` | that parameter becomes *n* scalar parameters; the call passes `f0…` |
| returned | `T6-RETURNED` / `T7-CALL-RESULT` | the function returns *n* scalar results, and each call site binds them — `case (f x) of (a, s) -> e` ⇒ `(a, s) := f x` |
| a field of a removable tuple | `T12-NESTED` | the outer box is gone too, so `f0…` reach the outer's readers directly, through the field binder named on the line |
| forced whole | `T14-FORCED` | the force disappears; forcing a constructor application is a no-op |

**The view is complete, and says so.** Every consumer on the flow is placed
in exactly one line and every call site the flow proved is placed exactly
once; the block ends the way [the recovered Parsec graph](#the-recovered-graph)
ends, with `0 unplaced`, and the assertion is in code
(`ScalarView::check`). A scrutiny whose scrutinee *is* the call folds the
call into its own line, so the multiple-return shape reads as one binding
rather than two. `--scalar-all` builds the view of every removable
construction — the 1,206 normalised plus the 3 that keep their proof but
need a clone: **1,209 on `-O1`, 0 unplaced**, and likewise on all six
profiles (1,209 / 1,469 / 1,365 / 2,509 / 2,543 / 2,544).

### Composing the views: can all 1,453 be applied at once?

`scalar.rs` proves each view is complete *for its own flow*. It does not
prove that all of them can be applied **simultaneously**, and that is a
different question, because a formal parameter and a function's result are
**representation boundaries**: one slot, one representation, shared by
everything that reaches it.

Suppose parameter `p` of a local function `f` receives removable tuple A at
one call, removable tuple B at another, and at a third call an expression
that is not a removable tuple at all — a variable of tuple type from an
opaque source, the result of an imported call, a parameter of the enclosing
function. A and B each have a perfect def-use proof, and the two proofs do
not contradict each other. `p` still cannot be *both* two scalars and one
boxed tuple. The same holds for a return: a function that returns a
removable tuple on one branch and something of unknown representation on
another cannot have its result split.

Stages 1–3 do not catch this. `tuples.rs` guards the *callee*
(`callee-parameter-cannot-be-split`,
`closure-returning-the-tuple-is-passed-into-a-parameter`): the function must
be local, not exported and never used as a value, so that every call site is
visible and rewritable. That is strictly weaker than proving that every
**producer** of the boundary agrees on one representation — and both
`tuples.rs` and `verify.rs` follow *the selected tuple* into the parameter,
so the assumption is shared by the two walks rather than challenged by the
second one. `boundary.rs` is the third proof object that challenges it.

**How a boundary is enumerated — independently of the flow walk.**

* **A parameter** `(f, i)`. Every occurrence of `f`'s binder
  (`Module::occurrences`) is taken to its spine root (`Module::spine_root`).
  An occurrence that is not the head of a spine, or heads a spine supplying
  fewer value arguments than `f` has manifest parameters, is `f` used *as a
  value* — a PAP, an argument, something stored — and the parameter cannot
  be split at all. Every remaining occurrence is a call site, and the value
  argument at index `i` is a producer. `f` being exported is the same kind
  of disqualification.
* **A return** of `f`. Every syntactic return point of the body, enumerated
  iteratively through the `case`/`let` tree — GHC does not leave the lambdas
  at the head of a right-hand side, so `f = case c of A -> \s -> e1; B -> \s
  -> e2` has return points `e1` and `e2`. Each leaf carries the number of
  value arguments needed to reach it; the result lives at the deepest, and a
  leaf reached with fewer has, by the type of the position it sits in, to be
  a *function* of the remaining ones — a tuple is never a function — so it
  is a producer this walk cannot see into rather than a value of the
  boundary.

A producer expression is then classified by what it **is**, looking through
casts, ticks, `let` bodies, `case` alternatives, local aliases (a variable
bound to a right-hand side is that right-hand side) and the case binder that
is another name for its scrutinee, and following a tail call to a local
function into *its* return points at the matching arity. Everything else is
named and asks for the tuple: a call to an import, a lambda-bound parameter,
a field bound by a match, an imported value, a constructor application, a
local call the walk will not follow.

**The verdict.** `UniformSplit(k)` only when every producer asks for
`Scalars(k)` with the same `k` *and* the boundary has no other use.
`CloneRequired` when the producers disagree at a **parameter** whose
function is local, not exported and never used as a value: a clone of the
callee can take the scalars while the call sites that have a real tuple keep
calling the original. A **return** is never `CloneRequired` — every return
point is inside one body and they all have to agree, so no clone splits some
and not the others. `Preserve` when a proven real value reaches the
boundary. `Unresolved` otherwise, with the reason.

Once a parameter boundary *is* a uniform split, a function that returns that
parameter returns the same scalars, so the parameter's arity is propagated
into the return boundaries that produce from it — a fixpoint that starts
from nothing and only ever *adds* splittable parameters, so a cycle of
functions passing each other's parameters around cannot bootstrap itself.

**The assertion this milestone is about.** Every removable flow whose view
crosses a boundary — `PassedTo`, `Returned`, and their transitive hops,
including through `T4-RETUPLE` and `T12-NESTED` — must have **every** crossed
boundary `UniformSplit`. Otherwise the flow is **downgraded now**:
`CloneRequired` moves it to the new fate `RemovableWithClone`, which keeps
the flow's own proof but is counted as *unsupported* until a cloning
decision exists; anything else moves it to `Unresolved` with the reason
`boundary-not-uniform (<boundary>)`. Downgrading is itself a fixpoint — a
flow that stops being removable stops asking for scalars at every other
boundary it produces into — and it only ever shrinks the removable set, so
it settles (2 rounds on `-O1`, 3 on B).

```
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

580 boundaries, 351 of them uniform. **1,024 of the 1,453 def-use-removable
flows cross at least one boundary**; 429 never leave the function they were
built in and are untouched by any of this. **247 flows are downgraded**:

| | new fate | reason | representative |
|---:|---|---|---|
| 181 | `Unresolved` | producers request different representations | `Main` node 2737 — return of `p#1107` |
| 23 | `Unresolved` | the function is used as a value | `ShellCheck.Analytics` node 49954 — return of `$s$fMonadWriterT2#1992` |
| 21 | `Unresolved` | a preserved tuple reaches the boundary | `ShellCheck.Analytics` node 3044 — return of `go1#2757` |
| 12 | `Unresolved` | the function has no visible call site | `Main` node 8383 — return of `$s$w$c<*>#1` |
| 5 | `Unresolved` | the binding is not a lambda chain, so it has no result to split | `ShellCheck.CFG` node 38683 — return of `m1#2556` |
| 3 | `RemovableWithClone` | producers disagree at a splittable parameter | `ShellCheck.Analytics` node 1974 — parameter 1 of `$wgo1#2086` |
| 2 | `Unresolved` | a call site is a partial application | `ShellCheck.Checks.Commands` node 13824 — return of `$s$fMonadRWST1#977` |
| **247** | | | 222 boxed, 25 unboxed |

The single most common shape is the one the milestone was written for:
`Main`'s `p#1107` returns a removable unboxed pair on one path and the
result of an imported call on three others, so its result cannot become two
scalars however good the pair's own proof is. Counted by what actually
reaches a non-uniform boundary: 265 constructions that stay, 193 results of
local calls the walk will not follow, 91 parameters of the enclosing
function, 46 lambdas, 4 imported call results, 1 field bound by a match.

`--explain` lists each boundary's producers and consumers with node ids, and
`--json` carries the boundaries and the downgrades:

```
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

**What this costs, and why it is the right price.** `normalised` falls from
1,453 to **1,206** and the unsupported residual rises from 580 to **827**.
That is not a regression in what the compiler knows — every one of the 247
still has its def-use proof, and `--scalar-all` still prints a complete view
for the 3 that only need a clone — it is the milestone refusing to count a
removal it cannot actually perform. The verifier's report says so
explicitly: it re-derives 1,206 of 1,206 with 0 disagreements, and the 247
constructions it would still accept are listed as *"verifier accepts, census
does not … of which the boundary check downgraded: 247"*. Seven of them were
the `-O1` verdicts that rested on a Parsec hop, which is why that line now
reads 0.

### Auditing one construction

```
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

Every node id there is a `h2r show` argument. `--json` dumps the flows,
their consumers and the accounting; `--verify` prints the independent
re-derivation and the table of audited shapes above.

`h2r show` loads the tuple proof object by default for a module that has
flows (`--no-tuples` turns it off, exactly like `--no-parsec`). It marks
constructions, alias binders, consumers and their occurrences inline, and
prints the flow's own evidence for the node asked about:

```
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

A node that takes part in several flows gets one footer per flow — node
4635 above is a selector of three different constructions, and each says so
separately. For `Preserve` and `Unresolved` the fate line carries the
reason *with its holder* (`Preserve  [stored-in-constructor-field (:)]`),
which is the same string the residual is itemised by. Both proof objects
annotate the same rendering, and their marks are concatenated rather than
merged, so it stays visible which object said what.

### The cross-milestone link: how many of M1's thunks are these tuples?

[M1](#m1--how-much-haskell-is-left-after-ghc) counts 2,242 potential thunk
sites, 1,905 of which need memoisation to keep sharing, and attributes 422
of the sites to `ds…` desugar bindings. The desugarer turns a lazy tuple
pattern `~(b, s, w)` into one selector thunk per field, so the obvious
question is how much of M1's residue is *this milestone's* tuples.

`h2r tuples` answers it exactly, with a deliberately narrow rule: a thunk
site is **explained by tuple transport** when the binding M1 reports is a
potential thunk site, its right-hand side *is* a lazy selection
(`T3-SELECTED`) or a field-wise re-tupling (`T4-RETUPLE`), and the tuple it
reads is **normalised** — removable *and* verified. A `Preserve` or
`Unresolved` tuple keeps its box, so its selectors stay; a removable
verdict only one walk proves does not count either.

```
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

**92** thunk sites are explained: 89 of them memo (80 captured by a
many-entry lambda, 9 shared on a path) and 3 sinkable into a lazy position.
By binder origin they are 67 user-named, 23 `eta…`, 2 `ds…`, and none at
all from `lvl…` or the dictionaries. (Before the [boundary
check](#composing-the-views-can-all-1453-be-applied-at-once) narrowed
`normalised`, this number was 111; the 19 difference is selectors over
tuples whose boundary is not uniform, and their thunks stay.) The invariant
`remaining + explained = 2,242` is asserted, as is "every explained site
lands in exactly one fate row, one origin row and one rule".

Of the census' 1,321 tuple-attributed lazy argument sites, **630** stop
being lazy positions because the tuple they are an argument *to* is
normalised — the argument becomes a scalar binding at the construction
(167 boxed, 463 unboxed). That is the same 630 as the `normalised` column
of the site accounting above, seen from the other side.

**Why 92 and not 400.** The interesting finding is that the `ds…`
population is *not* the selectors. GHC names the lazy pattern's scrutinee
`ds…` and leaves the field selections under the pattern variables' own
names, so `ds1` holds the *tuple* and `b1`/`s''`/`w'` are the selectors —
which is exactly what the origin split shows. Counted separately, and
**never folded into the table above**, 288 thunk sites *hold* a normalised
tuple (`T1-LET-BOUND`): 210 `ds…`, 54 user-named, 23 `eta…`, 1 `lvl…`.
Their box will not exist either, but what replaces each of them is one
scalar binding per field, and whether *those* are thunks is a question for
the let census to answer again after the rewrite — not one this link may
answer now. Claiming them here would be the same mistake as naming a fate
after a monad transformer.

The other reason the number is not larger is visible in the Core: of the
863 distinct lazy-selector cases over the whole population, only 142 are a
`let` right-hand side at all. The rest are written inline —
`case ($wgetCommandNameAndToken False x) of (# ww, ww1 #) -> ww` in
`ShellCheck.ASTLib` — where there is no thunk to remove in the first place.

| | A `-O1` | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| thunk sites explained by tuple transport | 92 | 103 | 120 | 121 | 121 | 121 |
| thunk sites holding a normalised tuple | 288 | 332 | 298 | 659 | 659 | 659 |
| lazy argument sites that become scalars | 630 | 734 | 694 | 1,160 | 1,160 | 1,159 |

### M2.2 acceptance

**The criterion is that every tuple this milestone removes has a complete
def-use proof, re-derived by an independent verifier, and a representation
boundary that all the removals agree on — not that coverage is high.** A
wrong "removable" is a miscompile; a wrong "Preserve" is a missed
optimisation. Coverage is reported and secondary.

Against the `-O1` dump, all of the following hold.

**The population is partitioned, and the accounting closes.** 2,584
saturated constructions, 1,765 boxed and 819 unboxed, every one in exactly
one fate bucket (asserted):

| fate | boxed | unboxed |
|---|---:|---:|
| ScalarReplace | 403 | 0 |
| WorkerReturn | 136 | 667 |
| RemovableWithClone | 3 | 0 |
| Preserve | 551 | 0 |
| Unresolved | 672 | 152 |
| **total** | **1,765** | **819** |

and `before = normalised + preserved + unsupported` per representation:
1,765 = 539 + 551 + 675 boxed, 819 = 667 + 0 + 152 unboxed, 2,584 = 1,206 +
551 + 827 in all. The census' 1,321 tuple-attributed argument sites map
one-to-one onto the population (849 boxed + 472 unboxed, 0 unmapped, over
726 distinct constructions) and close the same way: 1,321 = 630 + 144 +
547.

**Every removal is proven twice.** The [independent
verifier](#the-independent-verifier) shares nothing with the census but the
IR — its own population selection, its own name test, its own walk — and
re-derives all 1,206 removable verdicts with **0 disagreements**; the two
sides also select the same population (0 constructions found by only one).
The 247 constructions the verifier would still accept and the census now
refuses are exactly the ones the boundary check downgraded, and the report
names them as such. The same holds on all six flag-matrix profiles (1,206 /
1,464 / 1,360 / 2,504 / 2,538 / 2,539, 0 disagreements each). **0 removable
verdicts are unverified**, so nothing is counted as normalised on one
proof.

**Every removal has a complete rewrite.** `--scalar-all` builds the
normalised view of all 1,209 (and of all 2,544 on F): every consumer and
every call site placed in exactly one line, `0 unplaced` everywhere.

**Every removal composes with the others.** Stage 4 enumerates all 580
[representation boundaries](#composing-the-views-can-all-1453-be-applied-at-once)
the removable flows cross, *independently of the flow walk*, and requires
every one of them to be a uniform split. 1,024 of the 1,453 def-use-removable
flows cross at least one; 247 are downgraded because a boundary they cross is
not uniform, 3 of them to `RemovableWithClone` (counted as unsupported) and
244 to `Unresolved`. The downgrade fixpoint asserts its own convergence, and
the accounting, the 1,321-site table, the thunk link, the verifier and
`--scalar-all` are all recomputed after it and all still close.

**No fate rests on a name.** The population is *selected* by ghc-prim's
tuple constructor (evidence level 6) with `repArity` checked against the
name and saturation checked structurally; every verdict after that is
def-use over resolved occurrences. The constructor and callee names in the
residual are diagnostics, and the residual is split by the *kind* of holder,
not by the name.

**What remains, and what milestone each item belongs to:**

| | | |
|---:|---|---|
| 244 | the def-use proof stands, but a **representation boundary** the flow crosses is not a uniform split (181 producers disagree, 23 the function is used as a value, 21 a preserved tuple reaches it, 12 no visible call site, 5 not a lambda chain, 2 a partial application) | a representation-agreement pass over the boundaries, or cloning |
| 187 | the closure that returns the tuple is passed to an **imported** call | M2.4 higher-order / whole-program closure analysis |
| 134 | …**consed onto a list** | M2.4: the checks-in-a-top-level-list shape, a closed-world list-of-closures pass |
| 114 | …**stored in a program constructor** | M2.4, per constructor |
| 67 | …**handed to a local callee's parameter** | a higher-order representation agreement (M2.4), not a def-use question |
| 41 | a proven Parsec continuation whose target the region graph does not close over | M2.1 follow-up: 20 chains not bound to a binder, 19 parsers used as a value, 2 unsaturated calls |
| 11 | returned from an **exported wrapper of a local worker** | whole-program linking — the *worker's* callers, not the wrapper's |
| 10 | …passed to a local binder that is not a lambda chain | M2.4 returned-closure analysis |
| 7 | …held in a partial application | M2.4 |
| 3 | …passed to a class-op | closed-world instance enumeration (M2.3) |
| 2 | returned from an exported function with no worker | whole-program linking |
| 2 | an unknown higher-order callee outside `ShellCheck.Parser` | M2.4 |
| 1 | the argument lands past the callee's parameters | M2.4 |
| 3 | …and only a specialised **clone** of the callee could carry the split | a cloning decision |
| 1 | the callee's parameter cannot be split (the callee escapes) | M2.4 |
| **827** | | |

**The cross-milestone table** is
[above](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples):
92 of M1's 2,242 thunk sites are these tuples' lazy selectors, 2,150
remain, and the invariant is asserted.

**How to audit a site.** `h2r show <dir> <module> <node>` prints the Core
around the node with both proof objects' marks inline and the flow's
evidence as a footer; `h2r tuples <dir> --scalar <node>` prints what
replaces the tuple, line by line, with `0 unplaced`; `--explain` lists
every construction's evidence; `--verify` prints the independent
re-derivation and the audited-shape table. All four are shown above.

**Known limits**, stated rather than hidden:

* the **location budget** (20,000) turns a pathological flow into an honest
  `Unresolved`. Nothing on `-O1` comes near it — the largest flow visits
  2,023 locations, the mean is 19 — but the transitive `T12-NESTED` rule
  does reach it on the inlining-heavy profiles: 4 flows on B and 2 each on
  C–F end as `flow-exceeded-the-location-budget`. The verifier refuses
  those flows too, so it is a coverage loss in the safe direction;
* the **Parsec hop is an input to both sides** of the cross-check. Seven
  `-O1` verdicts rested on a continuation target the verifier cannot derive
  on its own and is handed from the other proof object; the boundary check
  has since downgraded all seven, so `-O1` now has none (D–F still do).
  Where they remain, they are proven twice *after* that hop and once before
  it; dropping the hop would move them to `Unresolved`, not to a different
  removal;
* `exported` is **trusted from GHC**. Every rule that needs "no caller
  outside this module" reads the binder's `exported` flag as dumped. A
  whole-program link step can replace that with the actual call graph, and
  would resolve the 11 exported-wrapper and 2 exported-return residuals;
* the link's `explained` count is the *narrow* one. The 288 bindings that
  hold a normalised tuple are reported beside it and not claimed;
* the boundary check's **producer classifier is partial by design**. A
  producer it will not follow — a local call at an arity it cannot match, a
  lambda-bound parameter whose own boundary is not uniform, a field bound by
  a match — asks for the tuple, which makes the boundary non-uniform and
  costs coverage in the safe direction. 331 of the 600 tuple-requesting
  producers at non-uniform boundaries are of that kind, so a sharper
  interprocedural representation analysis would recover some of the 247.

## M2.3b — what is evaluated when a constructor field is read

M2.2 asked which tuple *allocations* are plumbing. M2.3 asks the
representation question for everything else, and it splits three ways:
**M2.3b** (this section) is the constructor-**field** census, M2.3c is the
list, M2.3d is text. This section decides exactly one thing and says so
everywhere: for each field of each construction, what does the optimised
Core prove about **when** the field's expression is evaluated? It answers
nothing about ownership, about whether the box survives, or about a Rust
type.

```sh
cargo run --release --bin h2r -- fields ../core-json
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.AST --explain
cargo run --release --bin h2r -- fields ../core-json --con OuterToken
cargo run --release --bin h2r -- lists ../core-json                         # list flows: when is a spine demanded, and how much
cargo run --release --bin h2r -- lists ../core-json --axioms                # the library demand-semantics table
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --explain
cargo run --release --bin h2r -- fields ../core-json --json
```

### The population

`D0-FIELD-CON`: every saturated application of a data constructor that is
neither a tuple (M2.2's population) nor the list cons (M2.3c's), selected
through the head's `DataConInfo` and never by name — 9,166 constructions on
`-O1`, 2,703 of the program's own constructors and 6,463 of libraries',
19,830 fields in all. The constructor *name* only splits the report into
program and library, exactly as the M2 census' family attribution does; no
verdict reads it.

| constructions | | constructions | |
|---:|---|---:|---|
| 1,789 | `ParseError` | 386 | `I#` |
| 677 | `Solo#` | 371 | `TyCon` |
| 547 | `IS` | 335 | `Comment` |
| 500 | `OuterToken` | 293 | `KindRepFun` |
| 427 | `TrNameS` | 291 | `Just` |
| 408 | `TokenComment` | 282 | `KindRepTyConApp` |

### Sum types: which alternative is the scrutiny

The [generic aggregate walk](#m22--which-tuples-are-transport-and-which-are-values)
was written for tuples, and it accepted a `case` only when it had exactly
**one** data alternative of the construction's arity. For a product type
that is exact; for a sum type one alternative per constructor is the normal
shape, and the rule reported it as unresolved. M2.3b makes alternative
selection **constructor-relative**, the way GHC decides it:

* the alternative whose data constructor is this one — matched on GHC's
  stable name with the tag corroborating — is the scrutiny (`T2-SCRUTINISED`);
* no such alternative, but a `DEFAULT`: that is what a value of this
  constructor selects, and it binds no field — an observation to WHNF
  (`T15-WHNF-ALT`), not an escape and not a read;
* neither: nothing this value could select, which is conservatively an
  escape (`R_ALTS`), never "the construction was not observed";
* every other alternative is **unreachable for this value** and contributes
  nothing to the field-demand theorem.

Reachability applies to the case **binder** too. It is in scope in all the
alternatives but only one of them runs, so `case v of { C x -> k x; D y ->
store v }` on a known `C` is *not* an escape: the store under `D` cannot be
reached by this value. On `-O1` that skips 1,113 unreachable alternatives
and 14 case-binder occurrences that would otherwise have forced a flow to
`Unknown`.

Tuple behaviour is byte-identical under all of this — a tuple type has one
constructor, so the constructor-relative rule only ever confirms what the
single-alternative rule already said. `h2r tuples`, `--verify`,
`--boundaries`, `--json`, `--scalar-all`, `h2r laziness`, `h2r parsec` and
`h2r compare` produce identical output on `-O1` and on all six matrix
profiles.

### Three facts first, then a verdict

Nothing is assigned a representation directly. Every (construction, field)
records three **orthogonal** facts, and the rep is a function of them:

| Fact | Values | Where it comes from |
|---|---|---|
| field demand | `Always` / `Conditional` / `Never` / `Unknown` | the walk's reachable observations |
| construction strictness | `StrictField` / `LazyField` | GHC's `DataConInfo.strictFields` |
| value recursion | `RecursiveKnot` / `Acyclic` | **M1's** `Class::RecursiveValue`, read not re-derived |

The recursion fact is deliberately M1's and only M1's: a non-function member
of a recursive group that refers to itself through the value. It does not
mean "the field's type mentions the ADT" and it does not mean "produced by a
recursive function".

| demand | strictness | recursion | fields |
|---|---|---|---:|
| Always | LazyField | Acyclic | 175 |
| Always | StrictField | Acyclic | 21 |
| Conditional | LazyField | Acyclic | 896 |
| Conditional | StrictField | Acyclic | 19 |
| Never | LazyField | Acyclic | 9 |
| Never | StrictField | Acyclic | 21 |
| Unknown | LazyField | Acyclic | 15,418 |
| Unknown | LazyField | RecursiveKnot | 9 |
| Unknown | StrictField | Acyclic | 3,262 |
| | | **total** | **19,830** |

The `Never` / `StrictField` row is the one that says why the facts are kept
apart. `data X = X !Int Int` with field 0 never read is **not** `Dead`: the
field carries a forcing obligation whenever `X` reaches WHNF, and nothing
about "nobody reads it" removes that. 21 fields are in exactly that
position. `Dead` requires all three: never demanded, lazy, and acyclic.

### Why `Direct` is narrow

`Direct` claims that evaluating the field where the constructor is built is
equivalent to leaving it where GHC put it — **timing**, not eventual
demand. Two things make "something forces it eventually" insufficient:
`Foo (error "boom") ``seq`` 42` must stay `42`, and a construction that
crosses a return can sit while other work happens before anything reads it,
so moving the field's evaluation to the construction moves the divergence.
Only three rules establish it:

| Rule | Evidence | What it proves |
|---|---|---|
| `R1-STRICT-FIELD` | GHC (4) | the field is already strict: forced at construction, nothing left to move |
| `R2-FIELD-IS-VALUE` | structural (2) | the field expression is already a value — a literal, a lambda, a saturated construction, a partial application, a nullary constructor, a string literal, or a variable whose binding GHC marks `whnf` / `okForSpec` — so there is no evaluation to move |
| `R3-SAME-FRONTIER` | 2 over 3 | every observation is a scrutiny that strictly demands the field and stands at the construction's own evaluation frontier: the walk crossed no return and no unknown call, and between the construction and each scrutiny there is no lambda, no conditional and no thunk boundary |

Everything demanded at all and not proven by one of those is `Deferred`. A
false `Direct` is a miscompile; a false `Deferred` is lost coverage, so the
rules are deliberately one-sided.

### Results on the `-O1` dump

| | Dead | Direct | Deferred | Recursive | Unknown |
|---|---:|---:|---:|---:|---:|
| program, GHC-strict | 0 | 0 | 0 | 0 | 0 |
| program, lazy | 4 | 1 | 206 | 1 | 6,524 |
| library, GHC-strict | 0 | 3,323 | 0 | 0 | 0 |
| library, lazy | 5 | 84 | 780 | 8 | 8,894 |
| **total** | **9** | **3,408** | **986** | **9** | **15,418** |

`Direct` by the rule that proved the timing: 3,323 `R1-STRICT-FIELD`, 85
`R2-FIELD-IS-VALUE`, **0** `R3-SAME-FRONTIER`. The last is not a bug and it
is worth stating: the shape `R3` recognises is a construction scrutinised in
the same frame it was built in, which is precisely what GHC's
case-of-known-constructor already eliminates, so none survives `-O1`. The
rule has a hand-built regression test rather than a count in the dump, and
the negative case — the same demand behind a lambda — has one too.

Observations: 6,229 `FieldDemanded` (2,452 strict by GHC's demand on the
alternative's binder, 12 strict by position, 3,765 lazy), 1,922
`FieldBoundUnused`, 471 `WhnfOnly` (468 `seq`-shaped forces, 3
`DEFAULT`-selected), 11,784 `Escape`. Constructions: 1,407 observed, 13
never observed, 7,746 escaped before any observation. The nesting fixpoint
settles in 3 rounds.

| Top `Deferred` reason | |
|---:|---|
| 667 | demanded only lazily (passed on, stored, captured) |
| 203 | bound and unused on some observation |
| 90 | demanded on every path, but not at the same frontier |
| 26 | demanded on some observations only |

| Top `Unknown` reason | |
|---:|---|
| 2,264 | stored in a **list cell** — M2.3c's population |
| 1,143 | an unknown higher-order callee (`eta`) |
| 998 / 760 / 595 / 573 / 557 / 348 | the construction **holding** it escapes (`TokenComment`, `KindRepFun`, `TyCon`, `OuterToken`, `PushCallStack`, `Comment`) |
| 565 | an unknown higher-order callee (`eok`) — a Parsec continuation |
| 311 | stored in a **tuple** field — M2.2's population |

The residual is dominated by three things that belong to other milestones
rather than by a missing rule here: the list cell, the Parsec/higher-order
callee, and the transitive escape of whatever holds the value. `D8-NESTED`
does follow a construction stored in another construction **in this
population** — through that field's binders at every scrutiny of the holder,
inheriting the holder's own escapes — and fires 4,207 times; it stops at a
list cell or a tuple because those are M2.3c's and M2.2's populations.

### The M2 census' 1,996 constructor-field sites

The [M2 baseline](#m2-baseline--who-receives-the-lazy-arguments) attributes
1,996 lazy argument sites to the constructor-field strategy. They map onto
this population exactly, with nothing unexplained:

| | |
|---:|---|
| 1,310 | the list cons — **deferred to M2.3c**, not mapped here |
| 686 | mapped onto a (construction, field) pair |
| 0 | unmapped |

and their `FieldRep` is 77 `Deferred`, 609 `Unknown`, 0 of anything else —
which is the honest shape of the thing: a lazy *computation* in a
constructor field is, by construction, not a value, so `R2` cannot fire, and
these are the sites whose holders reach a list or an import. (1,994 of the
1,996 are `Position::LazyField`; the other 2 are `Position::UnknownArg`,
where the constructor's representation and source field counts differ. The
population predicate is the census' own — a `Computation` in an escaping
position with a `ProgramDataCon` / `LibraryDataCon` / `ListCons` family — so
the 1,996 is the same 1,996.)

### Accounting

Asserted in code (`FieldAccounting::check`), on `-O1` and on all six matrix
profiles:

* every field lands in exactly one rep, and the program/library ×
  GHC-strict/lazy split and the three-fact matrix each cover all 19,830;
* `constructions = observed + unobserved + escaped-before-observation`
  (9,166 = 1,407 + 13 + 7,746) and `= program + library`;
* every census site is mapped, deferred to M2.3c, or carries a reason;
* every `Direct` verdict names the rule that proved its timing.

| profile | constructions | fields | Dead | Direct | Deferred | Recursive | Unknown |
|---|---:|---:|---:|---:|---:|---:|---:|
| `-O1` / A | 9,166 | 19,830 | 9 | 3,408 | 986 | 9 | 15,418 |
| B | 10,171 | 22,111 | 30 | 4,264 | 1,023 | 9 | 16,785 |
| C | 11,092 | 23,381 | 26 | 4,621 | 782 | 9 | 17,943 |
| D | 26,014 | 52,024 | 253 | 14,348 | 979 | 6 | 36,438 |
| E | 23,632 | 47,292 | 223 | 12,748 | 925 | 6 | 33,390 |
| F | 23,734 | 47,332 | 223 | 12,736 | 926 | 6 | 33,441 |

### Known limits, stated rather than hidden

* **`D8-NESTED` stops at the other milestones' populations.** A value stored
  in a list cell or a tuple field is `Unknown`, not followed. Following it
  needs M2.3c and M2.2's flows respectively; it is a coverage loss in the
  safe direction.
* **Any escape makes every field of that construction `Unknown`**, including
  an escape that is a *proven* real value (a store, an imported strict
  parameter). What the callee demands of the field is outside the module, so
  the analysis refuses rather than guessing — which is why 15,418 of 19,830
  fields are `Unknown`.
* **`R2` counts a string literal as a value.** `unpackCString# "…"#` is not
  `exprIsHNF`, but it is total, terminating and cheap, so evaluating it
  eagerly can neither diverge nor error. That is the one place `R2` argues
  from `okForSpeculation`-style reasoning rather than from WHNF.
* **The recursion fact is M1's at `let` level and the group flag at top
  level.** M1 reports `Class::RecursiveValue` for `let`-bound bindings only;
  a top-level construction in a recursive group is taken at the group's own
  `rec` flag, under the same predicate.
* **This section decides evaluation only.** A field can be `Deferred` and
  `Acyclic` with no decision made about how it is represented.

## M2.3c — when, and how much, of a list's spine is demanded

M2.3b asked what is evaluated when a constructor *field* is read, and
deferred 1,310 of the M2 census' 1,996 constructor-field sites — the list
cons — to here. This section answers a different question about those and
about every other list: **when, and how much, of a spine is demanded, by
whom, how often, and does anything alias its tail?**

It deliberately does *not* start from `[]`/`(:)` and end at a Rust type.
`foldl'` reaches every cell of a spine and is still a streaming consumer;
"the whole spine is eventually consumed" does not mean the whole spine ever
has to exist. So six **facts** are recorded per flow, each with its own
rules and nodes, and an **advisory** recommendation is derived from them at
the end and clearly labelled as advisory.

Text (`[Char]`) is M2.3d and nothing here decides it. Every flow records
the list type and the element type as GHC rendered them on the binder —
corroboration-level evidence that no verdict reads — so M2.3d can select
the `[Char]` flows out of these facts.

```sh
cargo run --release --bin h2r -- lists ../core-json
cargo run --release --bin h2r -- lists ../core-json --axioms
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --explain
cargo run --release --bin h2r -- lists ../core-json --json
```

### The population: flows, not cells

| Producer | | `-O1` |
|---|---|---:|
| `L0-CONS` | a saturated `(:)`, by `DataConInfo` and never by name, that is not itself the tail of another cons | 3,920 |
| `L0-NIL` | a `[]`, likewise, that is not the tail of a cons in the population | 2,887 |
| `L0-IMPORTED` | a saturated call to an imported function the [axiom table](#the-library-demand-semantics-table) says returns a list | 5,031 |
| `L0-LOCAL` | a saturated call to a local function returning a list producer whose own flow could not reach this call site | 45 |
| | **flows** | **11,883** |

`L1-CHAIN`: a cons whose tail argument is another cons or a nil
*construction* is a **cell of the same flow**, so `1 : 2 : 3 : []` is one
flow of three cells, not four flows. 4,270 cons applications collapse into
3,920 chains.

`L0-LOCAL` is small on purpose. A call to a local list-producing function
is normally *reached* — the producer's own flow leaves the function through
`T6-RETURNED` and comes back at every call site through `T7-CALL-RESULT` —
so it is a location of that flow rather than a new one, which is what keeps
the population disjoint. The 45 are the cases where the return left the
module and the call site is genuinely a new start.

### Following a spine

The [generic aggregate walk](#m22--which-tuples-are-transport-and-which-are-values)
does the work, with the constructor-relative alternative selection M2.3b
added: at `case xs of { [] -> …; (y:ys) -> … }` a cons flow selects the
`(:)` alternative and a nil flow the `[]` one, and the other is unreachable
for that flow (987 alternatives and 120 case-binder occurrences skipped).
Three list-specific rules sit on top of it:

* **`L2-TAIL-ALIAS`** — the `(:)` alternative's *second* binder is not a
  field leaving the flow, it **is** the rest of this spine, and the walk
  continues at its occurrences. This is what lets a recursive consumer
  close a loop back onto the same `case` instead of stopping at the first
  cell. The *first* binder is an element, and is what `HeadDemand` is
  measured on (`L3-HEAD-BOUND`).
* **`L7-CONSED-AS-TAIL`** — the value is the **tail** argument of another
  cell: a `go`-loop accumulator, a cons built from a parameter. That is not
  storage; the spine continues into that cell's flow, and the successor's
  facts come back through a worklist fixpoint over the reverse edges
  (9,880 hops, 2,873 updates to settle).
* **`L18-STORED-FOLLOWED`** — the value is a field of a construction in
  M2.3b's population, and that holder is taken apart somewhere visible: the
  reads of the holder's field are reads of this spine. This is the exact
  mirror of M2.3b's `D8-NESTED`, which stops at a list cell precisely
  because this milestone owns it. It fires 3,191 times, and it is the
  reason `Storage` and `SpineDemand` are separate facts: a spine can be
  stored *and* have a fully visible demand.

### The library demand-semantics table

A call to `map`, `++` or `$wlenAcc` has no unfolding in the dump, so
def-use can only say the list left the module. `lists/axioms.rs` restores
the missing facts as an explicit, auditable table — 90 entries — each
carrying a stable global name, a semantic rule id (`L-AX-…`), the spine
demand on **each** list argument, the head demand, whether the result
aliases the input or a tail, whether evaluation short-circuits, how the
result list is produced (incremental / whole-before-first-cell /
same-as-input / unbounded), and a note.

It introduces a **new evidence level**, and where it sits is the point:

> 1 lexical binder identity · 2 structural shape · 3 def-use dataflow ·
> 4 GHC type compatibility · **5 library axiom** · 6 textual type
> comparison · 7 names

Below dataflow because it is *asserted*, not derived — nothing in the dump
proves that `reverse` traverses its whole argument. Above textual types
because it is a statement about semantics rather than spelling. The table
was written against **base-4.18.3.0 / ghc-prim-0.10.0 (GHC 9.6.7)**, the
versions in `compiler/matrix/A/plan.json`.

**An axiom is only ever applied to an imported id.** The key is GHC's full
stable name and the lookup happens only when `binding_of` says nothing in
this module binds the head, so a program function called `map` is never
looked up — there is a regression test for exactly that. List arguments are
indexed **from the end** of the call's value arguments, which is what makes
an entry survive a leading dictionary; an entry declares a minimum argument
count and is not applied to a call supplying fewer.

The flows reached **119 distinct imported heads**; 27 of them have an
entry, and those 27 cover 4,973 of the 6,806 imported consumer sites
(73%). The rest are reported as `Unknown` with
`no-axiom-for(<stable name>)` — never guessed.

| calls | axiom | head | | calls | axiom | head |
|---:|---|---|---|---:|---|---|
| 1,861 | yes | `GHC.Base.++` | | 394 | **no** | `ShellCheck.Interface.$wgo` |
| 1,123 | yes | `GHC.Base.eqString` | | 168 | **no** | `GHC.Show.showLitString` |
| 1,002 | yes | `GHC.CString.unpackAppendCString#` | | 88 | **no** | `Text.Parsec.Char.string1` |
| 236 | yes | `GHC.List.elem` | | 72 | **no** | `GHC.Classes.$fOrdList_$s$ccompare1` |
| 192 | yes | `Data.OldList.isPrefixOf` | | 66 | **no** | `GHC.Show.showList__` |
| 144 | yes | `GHC.Base.++_$s++` | | 61 | **no** | `GHC.IO.Handle.Text.hPutStr2` |
| 138 | yes | `GHC.List.reverse1` | | 61 | **no** | `GHC.Classes.$fEqList_$s$c==1` |
| 129 | yes | `GHC.List.takeWhile` | | 49 | **no** | `Text.Regex.TDFA.String.compile` |

Entries are written only where the semantics are certain. Several
GHC-internal helpers occur whose argument order or sharing behaviour cannot
be read off their names — `splitAt_$s$wsplitAt'`,
`intercalate_$spoly_go1`, `dropLength`, `dropLengthMaybe`,
`prependToAll`, `head1`, `init1`, `lvl` — and they get **no entry**. That
residual is the honest measure of the table's coverage.

### Six facts, and only then a recommendation

| `SpineDemand` | | | `HeadDemand` | |
|---|---:|---|---|---:|
| Unknown | 5,649 | | Unknown | 5,649 |
| None | 4,358 | | None | 5,048 |
| Prefix(DataDependent) | 856 | | Prefix | 897 |
| Incremental | 710 | | All | 270 |
| Prefix(Known) | 178 | | First | 19 |
| Whole | 132 | | | |

| `Reuse` | | | `Storage` | | | `Recursion` | |
|---|---:|---|---|---:|---|---|---:|
| SinglePass | 5,489 | | StoredIn | 5,277 | | FiniteProducer | 11,852 |
| Escapes | 4,347 | | NotStored | 4,332 | | RecursiveKnot | 31 |
| SharedTail | 1,762 | | Returned | 1,460 | | | |
| MultiPass | 285 | | Captured | 814 | | | |

`ShortCircuit`: 1,096 flows have a consumer that may stop before the end,
10,787 do not. 6,166 flows have only streaming spine consumers.

The spine rules behind `SpineDemand`, beyond the axioms:

| Rule | | `-O1` |
|---|---|---:|
| `L4-LOOP-WHOLE` | the tail alias is an argument of a saturated call to a local callee whose parameter *this same `case`* scrutinises, and the call runs whenever the alternative does with only evaluating edges in between → **Whole** | 27 |
| `L17-LOOP-INCREMENTAL` | the same loop with the recursive call in a lazy position — a constructor field, a lazy argument, a lambda — so a cell is reached only when the consumer's own consumer asks → **Incremental**. This is the `map`-shaped loop, and calling it `Whole` would be a lie | 115 |
| `L5-LOOP-SHORTCIRCUIT` | the same loop under a `case` inside the alternative → **Prefix(DataDependent)** and a short-circuit node | 195 |
| `L6-TAIL-DROPPED` | the alternative binds the tail and never uses it → this cell only | 137 |
| `L14-SHARED-TAIL` | an axiom whose result aliases the argument, or a tail-derived value that is stored or handed out | 1,762 |
| `L15-MULTIPASS` | more than one consumer enters the spine without reaching it through another's tail alias | 285 |
| `L13-RECURSIVE-KNOT` | **M1's** `Class::RecursiveValue`, read and not re-derived | 31 |

`Recursion` is M1's definition and only M1's: a non-function member of a
recursive group that refers to itself through the value. A recursive
*function* building a finite list is `FiniteProducer`, and there is a test
that asserts M1 does not call such a binding a recursive value.

### The advisory recommendation

| | | |
|---:|---|---|
| 49 | `VecCandidate` | whole spine, entered more than once or outliving its consumers, no shared tail, finite producer |
| 740 | `IteratorCandidate` | one pass, nothing retained, every spine consumer streaming, finite producer |
| 1,951 | `PersistentCandidate` | a tail survives in two places, or repeated entry with tails retained |
| 31 | `LazyCandidate` | a value knot, or a short-circuiting consumer in front of an unbounded producer |
| 9,112 | `Unknown` | any fact is `Unknown`, or the facts match no recommendation — with the reason |
| **11,883** | | |

Two orderings in the derivation are deliberate and stated rather than
hidden. A **value knot** is a knot whatever else is true of it, so it is
decided first. A **proven shared tail** decides the representation on its
own even when the spine demand is `Unknown`: how much of the spine anyone
walks does not change the fact that two owners see the same cells. That is
the one place a positive structural fact outranks an `Unknown` one.

`foldl'` over a whole list is the case the split exists for: `Whole` spine,
`SinglePass`, `NotStored`, streaming — an `IteratorCandidate`, **not** a
`VecCandidate`. There is a test that asserts exactly that.

### The 1,310 list-cons census sites

M2.3b mapped 686 of the M2 census' 1,996 constructor-field sites onto a
(construction, field) pair and deferred the 1,310 list-cons ones here. They
map onto this population exactly:

| | |
|---:|---|
| 1,310 | mapped onto the cell they are an argument of |
| 0 | unmapped |

1,174 of them are the cell's **tail** and 136 its element — which is the
shape of the thing: a lazy computation in a cons cell is usually the rest
of the list.

| by recommendation | | by `SpineDemand` | |
|---:|---|---:|---|
| 900 | Unknown | 684 | Unknown |
| 351 | PersistentCandidate | 492 | None |
| 40 | IteratorCandidate | 52 | Incremental |
| 19 | VecCandidate | 40 | Prefix(DataDependent) |
| | | 27 | Whole |
| | | 15 | Prefix(Known) |

### Accounting

Asserted in code (`ListAccounting::check`), on `-O1` and on all six matrix
profiles: every flow lands in exactly one bucket of the producer-kind,
recommendation, spine, head, reuse, storage and recursion tables; every
flow either has a short-circuiting consumer or has not; every imported head
seen either has an axiom or has not; and every one of the census' list-cons
sites maps onto exactly one cell or carries a reason.

| profile | flows | ConsChain | Nil | Imported | Local | Vec | Iterator | Persistent | Lazy | Unknown |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `-O1` / A | 11,883 | 3,920 | 2,887 | 5,031 | 45 | 49 | 740 | 1,951 | 31 | 9,112 |
| B | 12,235 | 3,989 | 3,024 | 5,172 | 50 | 81 | 705 | 1,931 | 31 | 9,487 |
| C | 13,709 | 3,907 | 3,670 | 6,078 | 54 | 65 | 1,205 | 1,951 | 23 | 10,465 |
| D | 23,871 | 6,291 | 8,516 | 9,010 | 54 | 69 | 1,789 | 2,600 | 83 | 19,330 |
| E | 22,673 | 6,213 | 7,806 | 8,600 | 54 | 69 | 1,708 | 2,492 | 83 | 18,321 |
| F | 22,792 | 6,262 | 7,839 | 8,637 | 54 | 69 | 1,690 | 2,462 | 83 | 18,488 |

`h2r tuples`, `--verify`, `--boundaries`, `h2r laziness`, `h2r parsec` and
`h2r fields` are byte-identical on `-O1` before and after this milestone.

### Known limits, stated rather than hidden

* **The axiom table is asserted.** Every `L-AX-…` entry is a claim about
  base that the dump does not prove. The entries most worth re-reading are
  the aliasing ones — `reverse1`'s accumulator becoming the result's tail,
  `unpackAppendCString#`'s second argument, `dropWhile`/`drop`/`span`
  returning a suffix of their input — because a wrong alias claim turns a
  `PersistentCandidate` into an `IteratorCandidate`, which is the unsafe
  direction. Nothing that could not be read off the function's contract
  with certainty got an entry.
* **2,849 flows are stored with no visible spine demand.** The holder is in
  M2.3b's population but never taken apart in this module, or it is not a
  construction at all. Whole-program (M2.4) work, not a missing rule here.
* **1,700 flows reach a holder that escapes.** `L18-STORED-FOLLOWED`
  inherits the holder's escapes, so a spine inside an escaping
  `TokenComment` is `Unknown` rather than guessed.
* **Traversal counting over-counts rather than under-counts.** A consumer
  is treated as a new entry into the spine unless it is reached through
  another consumer's tail alias, closed over known-local calls. Where that
  closure cannot follow — a higher-order hop — two views of one traversal
  are counted as two, which pushes a flow towards `MultiPass` and
  `PersistentCandidate`: the conservative direction for a representation
  decision.
* **`Captured` is narrow.** A flow that crossed a parameter or a return is
  never called captured, because a consumer inside the callee's lambdas is
  where the value was *sent*, not where it was captured. That costs
  coverage in the safe direction.
* **This section decides demand and sharing only.** No Rust type is chosen
  anywhere, and `[Char]` is not distinguished from any other element type.

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
| … exact target tier | **93%** | 92% | 91% | 91% | 91% | 91% |
| … finite target set | 8 | 8 | 25 | 84 | 84 | 106 |
| … producer known, target unresolved | 118 | 124 | 125 | 318 | 318 | 318 |
| … unresolved tier | **5%** | 5% | 7% | 6% | 6% | 6% |
| … exact *by the head alone*, before the Parsec proof | **68%** | 66% | 64% | 47% | 49% | 49% |
| … Parsec CPS | **27%** | 29% | 32% | 41% | 40% | 38% |
| thunk sites per 1k nodes | 5 | 5 | 5 | 6 | 6 | 6 |
| saturated tuple constructions, boxed | 1,765 | 1,989 | 2,250 | 4,369 | 4,380 | 4,465 |
| … removable after the boundary check | 542 | 630 | 567 | 935 | 969 | 969 |
| … proven a real value | 551 | 683 | 674 | 923 | 900 | 900 |
| saturated tuple constructions, unboxed | 819 | 1,020 | 943 | 1,751 | 1,751 | 1,752 |
| … removable after the boundary check | 667 | 839 | 798 | 1,574 | 1,574 | 1,575 |
| **tuples proven removable by def-use** | **56%** | 57% | 53% | 65% | 65% | 64% |
| representation boundaries crossed | 580 | 691 | 851 | 1,972 | 2,006 | 2,003 |
| … a uniform split | 351 | 452 | 486 | 697 | 731 | 728 |
| … flows downgraded because one is not | 247 | 277 | 334 | 1,497 | 1,497 | 1,501 |
| **normalised** (removable, verified *and* composable) | **1,206** | 1,464 | 1,360 | 2,504 | 2,538 | 2,539 |
| … verifier disagreements | 0 | 0 | 0 | 0 | 0 | 0 |
| … scalar views built, all with 0 unplaced | 1,209 | 1,469 | 1,365 | 2,509 | 2,543 | 2,544 |
| M1 thunk sites explained by tuple transport | 92 | 103 | 120 | 121 | 121 | 121 |

Findings:

* **The flags change the program's size, not its shape.** Per-node ratios
  are flat across A–C; D–F are worse. `-O1` is the most Rust-shaped profile
  on every resolvability metric.
* **Inlining replicates Parsec's CPS, it does not dissolve it.** Exposing
  all unfoldings triples the Core and takes Parsec-attributed sites from
  2,305 to 10,816. The Parsec normalisation pass is unavoidable; it should
  run on the smallest Core that still exhibits the pattern. The structural
  recogniser does keep up with the replication — the exact-target tier only
  falls from 93% to 91% across A→D — which is the point of proving the
  roles rather than counting names. The layout checks are what keep it
  there: they are derived per region from that region's own types, so
  replicated code with a different result type is measured against its own
  erasure, not against `-O1`'s.
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
* **The tuple proof holds up under replication.** Inlining more (D–F)
  triples the constructions and the *share* proven removable goes up, not
  down (56% → 65%), because the extra copies are worker/wrapper returns
  whose call sites are all local. `-fno-full-laziness` (C) is the only
  profile that loses ground (53%): floating a tuple-returning closure back
  inside a lambda turns some returns into closures handed to parameters,
  which is the one shape the def-use proof refuses. The independent
  verifier agrees with the census on all six, with no disagreement
  anywhere.
* Static-argument transformation trims ~7% of nodes; an extra strictness
  pass changes nothing.

Decision: stay on `-O1` for the survey dump. Revisit per pass (e.g. SAT
before ownership inference) rather than globally.
