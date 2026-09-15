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

## Milestones

| | | state |
|---|---|---|
| **M1** | the residual-laziness census: why does each local binding that survives GHC still exist? 2,242 potential thunk sites, classified and cross-checked against GHC's own demand and cardinality | done |
| **M2 baseline** | who receives the 8,351 lazy arguments — resolution, proven tier, abstraction family | done |
| **M2.1** | proving Parsec's CPS roles structurally, and feeding the proof back into the census | done |
| **M2.2** | which tuples are transport and which are values: 2,584 constructions, an independent verifier, a representation-boundary check, the scalar view | done |
| **M2.2.1** | the generic aggregate def-use walk (`flow.rs`) lifted out of the tuple census, so every later population is a client of one walk | done |
| **M2.3** | the representation question for everything else — **b** constructor fields, **c** list spines, **d** text, **e** the independent re-derivation, **f** the views, the provenance, the accounting and the cross-milestone link, **g** the correction to the axiom layer | done |
| **M2.4a** | the dump-format bump underneath it: stable global identity, structured types, and `[Char]` moved from a rendered string to `TyCon` identity — with every M1–M2.3 number unchanged | done |
| **M2.4b** | the closed-world class-op census: 565 dispatch sites, the 294 mapped 1:1, every class identified — and not one dictionary statically known | done |
| **M2.4** | the closed-world dictionary and higher-order milestone, in three separate questions: **can the call target be enumerated** (7 of 565 sites, the dictionary bounded at 118), **can an abstraction boundary use one representation** (5,574 function-valued boundaries, 252 enumerated, 84 one representation, 66 rewritable as one, 68 clones planned per owner), and **can the object disappear** (102 of 191 dictionary values `Erasable`, 36 of 216 parameters `Erasable` and 4 more with a clone, 4 owner-level clones) — **c** whole-program dictionary flow with its own totality domain, **d** higher-order representation agreement, **e** the 41 Parsec edges (0 closed, and why), **f** the independent re-derivation of all 606 positive claims with 0 disagreements on all seven dumps, **g** the views, the provenance, the accounting and the four cross-milestone links, **c′/d′** the two corrections | done |
| **M3** | **next.** The lowering: `Main.main`-rooted reachability (the 922 zero-reference bindings are not a rooted dead set), a canonical closure-boundary carrier per Haskell type — the open invariant `TypeShapeUniform` rests on — a call-string analysis to close the twelve set-valued clone plans, and a naming pass for the 4,613 anonymous-lambda / used-as-a-value boundaries that are `ShellCheck.Parser`'s CPS | next |

## Layout

| Path | What it is |
|---|---|
| `h2r-plugin/` | GHC plugin. Appends a Core pass after the whole optimisation pipeline and serialises each module's `CoreProgram` to JSON (dump format 5), including every binder's demand signature, CPR signature, arity and occurrence info, every referenced **global** Id keyed by stable name, and every type **structurally** in a hash-consed per-module table. |
| `matrix.sh` | Runs `extract.sh` under a matrix of GHC optimisation profiles (into `compiler/matrix/<profile>/`), for `h2r compare`. |
| `extract.sh` | Driver: stages a copy of the ShellCheck sources, runs upstream's `striptests` (which removes QuickCheck and Template Haskell), builds it with the plugin enabled, and collects the dumps. The tree at the repo root is never touched. |
| `rust/crates/h2r-core-ir` | Rust-side model of that JSON. Flattened into an arena on load — iteratively, since Core `App` spines nest far deeper than a stack likes — with parent links and edge kinds, so every later pass is worklist-driven. Owns the canonical identities every analysis reads: which binder a `Var` occurrence refers to (`resolve`; GHC uniques are *not* unique in optimised Core), which imported Id an occurrence links to (its stable name), which `App` an application spine is rooted at (`spine_root`, cast- and tick-transparent), and what each type *is* (`Ty`, with `TyCon` identity and `alpha_eq`). Includes a depth-limited Core pretty-printer. |
| `rust/crates/h2r-analysis` | Analyses over the arena. Today: the generic aggregate def-use walk every saturated-constructor flow is built on (`flow.rs`), the residual-laziness census (`laziness.rs`), callee resolution and target tiers (`callee.rs`), the shape/position predicates (`shape.rs`), the single binding-site-first signature lookup they all read (`scope.rs`), the structural Parsec-CPS recogniser (`parsec.rs`), the tuple def-use census that separates transformer plumbing from real values (`tuples.rs`, a client of `flow.rs` plus the four tuple-specific rules), the independent re-derivation of every removable tuple verdict (`verify.rs`, which shares nothing with `tuples.rs` but the IR), the normalised scalar view and per-node tuple provenance (`scalar.rs`), the representation-boundary check that says whether all those views can be applied at once (`boundary.rs`), and the cross-milestone link from M1's thunk sites to M2.2's tuples (`link.rs`), and the constructor-field census that says what is evaluated when each field is read (`fields.rs`), and the list-flow census with its explicit library demand-semantics table (`lists.rs`, `lists/axioms.rs`), and the text census that selects the `[Char]` flows out of it and says what the program does with them (`text.rs`, with its own asserted text-head table), and the independent re-derivation of every M2.3 representation verdict whose being wrong would be a miscompile (`verify_rep.rs`, which shares nothing with `fields.rs`, `lists/` or `text.rs` but the IR and does **not** use `flow.rs`), and the per-site representation views with the `h2r show` provenance they share (`views.rs`), and M2.3's own accounting and its cross-milestone link to M1's thunk sites (`m23.rs`), and the closed-world class-op census with its asserted class table (`classops.rs`), and the whole-program dictionary flow with its separate erasure and totality domains (`dictflow.rs`), and the higher-order representation-agreement analysis (`higher.rs`), and the independent re-derivation of every *positive* M2.4 verdict (`verify_m24.rs`, which shares nothing with `classops.rs`, `dictflow.rs`, `higher.rs` or `flow.rs` but the IR, and reads the analyses' verdicts only as the plain data `m24_claims.rs` writes down), and M2.4's per-site and per-boundary views, the `h2r show` provenance they share, the milestone's own accounting and its four cross-milestone links (`m24.rs`). |
| `rust/crates/h2r-rt` | Runtime for *residual* laziness only — `Lazy<T>`, `Shared<T>`. The design rule is that as little of this as possible should survive into generated code. |
| `rust/crates/h2r-cli` | The `h2r` driver. Today: `stats`, `binders`, `show` (with both proof objects inline and per-node evidence), `laziness`, `compare`, `parsec` (including `--cfg`, the recovered parser graph), `tuples` (including `--verify`, `--scalar`, `--boundaries` and the milestone accounting), `fields` (the constructor-field census), `lists` (the list-flow census, including `--axioms`), `text` (the text census, including `--heads`), `verify-rep` (the independent re-derivation of the M2.3 verdicts, the milestone accounting and the M1 link), `classops` (the closed-world class-op census: population, the 294 mapping, dictionary sources, origin chains and the evaluation facts), `dictflow` (the whole-program dictionary flow, its erasure verdicts and its clone plan), `higher` (the function-valued boundaries and their representation verdicts), `verify-m24` (the independent re-derivation of every positive M2.4 verdict), `m24` (M2.4's accounting, its residual and its four cross-milestone links in one place), and the `--view` / `--view-all` views `fields`, `lists`, `text`, `classops` and `higher` each carry. Later: the lowering passes. |

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

| | before | now | after tuple normalisation | after M2.3 |
|---|---:|---:|---:|---:|
| Local bindings after optimisation | 6,156 | 6,156 | — | — |
| … functions / join points / values already in WHNF | 1,883 / 1,119 / 762 | 1,883 / 1,119 / 762 | — | — |
| … strict (`let` the simplifier didn't turn into `case`) | 148 | 148 | — | — |
| … lazy, used at most once / possibly many times | 39 / 2,134 | 39 / 2,134 | — | — |
| **Potential thunk sites** | **2,242** | **2,242** | **2,150** | **2,139** |
| … sinkable into an evaluating position (thunk vanishes) | 12 | 14 | 14 | 11 |
| … sinkable, but into a lazy argument (thunk moves) | 243 | 254 | 251 | 248 |
| … … of all the sinkable ones, into mutually exclusive branches | 56 | 65 | — | — |
| … … the rest being single-use | 199 | 203 | — | — |
| … memo needed to keep sharing | 1,918 | 1,905 | **1,816** | **1,811** |
| … … captured by a many-entry lambda | 1,387 | **1,242** | **1,162** | **1,160** |
| … … shared on one path | 531 | **663** | **654** | **651** |
| … genuinely recursive values (knot-tying) | 69 | 69 | 69 | 69 |
| Top-level CAFs that are actually string literals | 2,426 of 2,755 | 2,426 of 2,755 | — | — |
| Genuine top-level thunks | 238 | 238 | — | — |

The third column is the [cross-milestone
link](#the-cross-milestone-link-how-many-of-m1s-thunks-are-these-tuples):
92 of these thunk sites are the lazy selectors of a tuple M2.2 proves
removable, independently verifies *and* shows can be removed together with
every other removal at the same representation boundary, so they disappear
with it rather than needing anything of their own.

The fourth is [M2.3's own link](#the-cross-milestone-link): a further
**11** whose right-hand side is a field expression already proven to be a
value, a lazy selection over a field proven eager, or a cell of a spine one
eager pass consumes — again only where the independent verifier confirms
the verdict. The two columns are disjoint by construction, and
`remaining + explained-by-tuples + explained-by-M2.3 = 2,242` is asserted.
Both criteria are deliberately narrow; each section says what is *not*
claimed and why the number is not larger.

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
on occurrence `Var`s of locals current, so reading an occurrence for a local
can return stale arity and strictness; the binder at the binding site is
authoritative. (Since [M2.4a](#m24a--stable-global-identity-and-structured-types)
the id table holds *only* globals, keyed by stable name, so there is nothing
there to read for a local at all.) Argument *position*,
partial-application *shape* and callee
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
| 294 | class-op dispatch — enumerated in [M2.4b](#m24b--the-closed-world-class-op-census): all 294 map onto the 565-site class-op population, and every one dispatches on a run-time dictionary |
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
   verdict. The dump has carried *structured* types since
   [M2.4a](#m24a--stable-global-identity-and-structured-types), and
   `Ty::alpha_eq` is the structural replacement, but **the Parsec rules
   below are deliberately not migrated yet**: they still read the rendered
   types, and they stay at this level until a later milestone moves them
   with its own gate;
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
`Ref::Global`, which is linked to the imported-id table by its **stable
name** (`$unit$Module$occ`), not by its unique — see
[M2.4a](#m24a--stable-global-identity-and-structured-types). No analysis
compares a unique at all. `Module::binder_in_scope`
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
| 294 | class-op dispatch | closed-world instance enumeration ([M2.4b](#m24b--the-closed-world-class-op-census): enumerated, none statically known) |
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

> **Added by [M2.4d](#m24d--higher-order-representation-agreement)**, beside
> these rows and changing none of them: the 67 land on their callee's
> function-typed parameter (31 `CloneRequired`, 13 `UniformRepresentation`,
> 1 `ExactClosure`, 22 with no such parameter at all), so **14 could be
> reclassified by a later pass**; the 187 land outside the closed world; the
> 134 and 58 of the 114 land on the one shared `(:)` / `(,)` field slot, and
> 45 of the 114 on a `Preserve`d record of run-time closures.

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

#### Two numbers, two questions — kept apart on purpose

There are two removability numbers in this milestone and they answer
different questions. They are separate metrics in `metrics.rs` and separate
rows of `h2r compare`, not one number with a caveat attached:

| | | `-O1` |
|---|---|---:|
| **can this box disappear locally?** | the def-use walk proves the construction is transport, on its own terms and before anything is asked about how it composes | **1,453** |
| **can it disappear without cloning?** | …and every [representation boundary](#composing-the-views-can-all-1453-be-applied-at-once) it crosses is a uniform split, so the removal composes with every other removal at the same boundary | **1,206** |
| …only a specialised **clone** of the callee could carry the split | recorded, and counted as *unsupported* | **3** |

The 247 between them is the work a representation-agreement pass would have
to do. The **3** `RemovableWithClone` parameter boundaries are the first
concrete evidence in this compiler for a cloning pass: a callee whose
parameter cannot be split because different callers want different
representations, where specialising a copy of the callee would resolve it.
**No cloning pass is implemented**, and they are counted as unsupported
rather than as a removal waiting to happen.

```
$ h2r compare A=compiler/core-json
removable locally (def-use)           1453
removable without cloning             1206
  …only a clone could carry              3
```

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

> **Added by [M2.4d](#m24d--higher-order-representation-agreement)**, as a
> column beside these rows and changing none of them: 14 of the 67 now have
> a receiving parameter that is `UniformRepresentation` or `ExactClosure`,
> so a later pass **could** reclassify them; the 187 land on a parameter
> outside the closed world; the 134 and 58 of the 114 land on the single
> program-wide `(:)` / `(,)` field slot; 45 of the 114 land on a `Preserve`.
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
cargo run --release --bin h2r -- text ../core-json                          # which list flows are text, and what is done with them
cargo run --release --bin h2r -- text ../core-json --heads                  # the text-head table
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --explain
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
| 2,264 | `stored-in-a-list-cell` — M2.3c's population |
| 1,143 | an unknown higher-order callee (`eta`) |
| 998 / 573 / 348 | `the-program-construction-holding-it-escapes` (`TokenComment`, `OuterToken`, `Comment`) |
| 760 / 595 / 557 | `the-library-construction-holding-it-escapes` (`KindRepFun`, `TyCon`, `PushCallStack`) |
| 565 | an unknown higher-order callee (`eok`) — a Parsec continuation |
| 311 | `stored-in-a-tuple-field` — M2.2's population |

M2.3e split those reasons by **which population owns the holder**, because
that is what decides who can close the residue: a list cell is M2.3c's, a
tuple field is M2.2's, a program construction is one M2.3f can still follow
inside this module, a library one is not. No verdict moved — 9,166
constructions, 19,830 fields and every cell of the three-fact matrix are
byte-identical; only the reason strings changed.

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
cargo run --release --bin h2r -- text ../core-json                          # which list flows are text, and what is done with them
cargo run --release --bin h2r -- text ../core-json --heads                  # the text-head table
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --explain
cargo run --release --bin h2r -- lists ../core-json --json
```

### The population: flows, not cells

| Producer | | `-O1` |
|---|---|---:|
| `L0-CONS` | a saturated `(:)`, by `DataConInfo` and never by name, that is not itself the tail of another cons | 3,920 |
| `L0-NIL` | a `[]`, likewise, that is not the tail of a cons in the population | 2,887 |
| `L0-IMPORTED` | a saturated call to an imported function whose [axiom](#the-library-demand-semantics-table) says the call's **own return type** is a list | 4,966 |
| `L0-LOCAL` | a saturated call to a local function returning a list producer whose own flow could not reach this call site | 45 |
| | **flows** | **11,818** |

> Every number in this section is **after** M2.3e, which added eleven audited
> entries to the axiom table and fixed two propagation bugs, **and after
> M2.3g**, which corrected the axiom table itself: a call whose result merely
> *contains* a list (`span` returns a pair, `mapM` returns `m [b]`,
> `GHC.Magic.lazy` returns whatever it was given) is no longer a producer,
> which removed 99 structurally bogus flows. What moved, and why, is in
> [M2.3e](#m23e--re-deriving-the-representation-verdicts-independently) and
> in [Correction (M2.3g)](#correction-m23g--the-axiom-layer).

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
the missing facts as an explicit, auditable table — 101 entries — each
carrying a stable global name, a semantic rule id (`L-AX-…`), a note, and
six fields whose axes M2.3g separated because conflating them was a bug in
each case:

| field | what it says | what it deliberately does **not** say |
|---|---|---|
| `list_args` | `(end-index, ArgSpine)` for **each** list argument: `Whole`, `PrefixFromArg(i)`, `PrefixDataDependent`, `Incremental`, `NoDemand` | how often the spine is walked — that is `replays` |
| `replays` | the end-indices of arguments the call **retains and traverses again from the front** (`cycle`, `isInfixOf`, `isSuffixOf`, `intercalate`'s separator) | nothing about how far each traversal gets |
| `head` | `HeadDemand`: what the call **provably forces** of the elements it reaches — a primop (`eqString` at `Char`), a `case` (`and`, `words`) | that a callback forces anything: `any (const True)` does not |
| `exposure` | `HeadExposure`: which callback the elements are handed to — `Predicate`, `Eq`, `Ord`, `Show`, `Other` | that the element is evaluated |
| `alias` | `NoAlias` · `ResultIsTailOfArg(i)` · `ResultSharesArg(i)` · `ResultContainsSuffixOfArg(i)` (the suffix is inside a pair or a `Maybe`) · `ResultSharesElementOf(i)` (the result is one of the *elements*, which puts nothing on this spine) | whether the result is itself a list |
| `produces` | the call's **outer return type**: `NotAList` · `DirectList(kind)` · `ProductContainsList{components}` · `EffectContainsList(kind)` · `OtherContainsList`, where `kind` is incremental / whole-before-first-cell / same-as-input / unbounded | which component of a product or effect the list is — that is tuple and effect normalisation's job, not this milestone's |

**Only `DirectList` starts a flow.** The two axes are independent in both
directions: `span` returns a pair *and* its second component is a suffix of
its argument, so it is no producer and still puts a shared tail on its
input; `GHC.Magic.lazy` is the identity *and* `a` is not a list at every
call site, so it is no producer either although its result is its argument.

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

The flows reached **116 distinct imported heads**; 36 of them have an
entry, and those 36 cover 5,115 of the 6,660 imported consumer sites
(77%). The rest are reported as `Unknown` with
`no-axiom-for(<stable name>)` — never guessed. Eleven of the entries and
three corrections came out of [M2.3e's audit](#the-axiom-audit), and a
further **46 of the 101 entries were corrected** by
[M2.3g's audit](#correction-m23g--the-axiom-layer), which read base's own
definition for every entry claiming a result type, a forcing or an alias.

| calls | axiom | head | | calls | axiom | head |
|---:|---|---|---|---:|---|---|
| 1,861 | yes | `GHC.Base.++` | | 394 | **no** | `ShellCheck.Interface.$wgo` |
| 1,121 | yes | `GHC.Base.eqString` | | 168 | **no** | `GHC.Show.showLitString` |
| 999 | yes | `GHC.CString.unpackAppendCString#` | | 88 | **no** | `Text.Parsec.Char.string1` |
| 236 | yes | `GHC.List.elem` | | 66 | **no** | `GHC.Show.showList__` |
| 192 | yes | `Data.OldList.isPrefixOf` | | 61 | **no** | `GHC.IO.Handle.Text.hPutStr2` |
| 144 | yes | `GHC.Base.++_$s++` | | 49 | **no** | `Text.Regex.TDFA.String.compile` |
| 138 | yes | `GHC.List.reverse1` | | 45 | **no** | `Data.Set.Internal.$fDataSet1` |
| 129 | yes | `GHC.List.takeWhile` | | 40 | **no** | `Text.Parsec.Error.$wmergeError` |
| 81 | yes | `GHC.Classes.$fEqList_$s$c==1` (M2.3e) | | 39 | **no** | `GHC.Base.pure` |
| 72 | yes | `GHC.Classes.$fOrdList_$s$ccompare1` (M2.3e) | | 43 | **no** | `Data.Set.Internal.$fDataSet1` |

Entries are written only where the semantics are certain. M2.3e read
base-4.18.3.0's source for every helper M2.3c had left out and added the
ones it could confirm (`dropLength`, `dropLengthMaybe`, `prependToAll`,
`splitAt_$s$wsplitAt'`, `init1`, `head1`, `flipSeq`, and the four
`SPECIALISE`d list `==`/`compare` copies). `intercalate_$spoly_go1` keeps
**no entry**: `poly_go` is a name GHC generated, base contains no such
definition, and a shape read off a call site is a guess, not a contract.
That residual is the honest measure of the table's coverage.

### Seven facts, and only then a recommendation

| `SpineDemand` | | | `HeadDemand` (**proven forcing only**) | |
|---|---:|---|---|---:|
| Unknown | 5,503 | | Unknown | 5,503 |
| None | 4,359 | | None | 5,482 |
| Prefix(DataDependent) | 921 | | Prefix | 544 |
| Incremental | 715 | | All | 270 |
| Prefix(Known) | 179 | | First | 19 |
| Whole | 141 | | | |

`HeadExposure` is fact 2b, added by M2.3g and recorded **beside**
`HeadDemand`, never folded into it: an element that reaches a predicate or
a class method has to exist as a value, but nothing proves it is evaluated.

| `HeadExposure` | | |
|---|---:|---|
| Unknown | 5,503 | a consumer is outside what this module proves |
| NotExposed | 5,340 | |
| BoundAndUsed | 460 | a `(:)` alternative binds the element and uses it |
| PassedToCallback(Eq) | 401 | `elem`, `nub`, `isPrefixOf`, the specialised list `==` |
| PassedToCallback(Other) | 61 | `map`, `foldr`, `zipWith`, `mapM_` |
| PassedToCallback(Predicate) | 46 | `any`, `all`, `find`, `takeWhile`, `span` |
| PassedToCallback(Ord) | 7 | `sort`, `maximum`, the specialised list `compare` |

| `Reuse` | | | `Storage` | | | `Recursion` | |
|---|---:|---|---|---:|---|---|---:|
| Escapes | 5,238 | | StoredIn | 5,234 | | FiniteProducer | 11,787 |
| SinglePass | 4,225 | | NotStored | 4,310 | | RecursiveKnot | 31 |
| SharedTail | 1,860 | | Returned | 1,460 | | | |
| MultiPass | 495 | | Captured | 814 | | | |
| Replayed | 0 | | | | | | |

`ShortCircuit`: 1,181 flows have a consumer that may stop before the end,
10,637 do not. 6,239 flows have only streaming spine consumers.

`Reuse::Replayed` is M2.3g's fourth reuse shape — a consumer that retains
the spine and walks it **again from the front**, which is neither a second
independent entry (`MultiPass`) nor a surviving tail (`SharedTail`). Five
axiom entries carry it (`cycle`, `isInfixOf` on both arguments,
`isSuffixOf` on both, `intercalate`'s separator) and **none of them is
called anywhere in these seven dumps**, so the fact has 0 firings. It is
printed with its zero rather than left out: a rule that the program never
exercises is a fact about the program.

The spine rules behind `SpineDemand`, beyond the axioms:

| Rule | | `-O1` |
|---|---|---:|
| `L4-LOOP-WHOLE` | the tail alias is an argument of a saturated call to a local callee whose parameter *this same `case`* scrutinises, and the call runs whenever the alternative does with only evaluating edges in between → **Whole** | 27 |
| `L17-LOOP-INCREMENTAL` | the same loop with the recursive call in a lazy position — a constructor field, a lazy argument, a lambda — so a cell is reached only when the consumer's own consumer asks → **Incremental**. This is the `map`-shaped loop, and calling it `Whole` would be a lie | 115 |
| `L5-LOOP-SHORTCIRCUIT` | the same loop under a `case` inside the alternative → **Prefix(DataDependent)** and a short-circuit node | 195 |
| `L6-TAIL-DROPPED` | the alternative binds the tail and never uses it → this cell only | 137 |
| `L14-SHARED-TAIL` | an axiom whose result — or a list inside its result — is a suffix of the argument, or a tail-derived value that is stored or handed out | 1,770 |
| `L15-MULTIPASS` | more than one consumer enters the spine without reaching it through another's tail alias | 330 |
| `L13-RECURSIVE-KNOT` | **M1's** `Class::RecursiveValue`, read and not re-derived | 31 |
| `L19-REPLAYED` | an axiom says the consumer retains this argument and walks it again from the front (M2.3g) | 0 |
| `L20-HEAD-EXPOSED` | an element reaches a callback the analysis cannot see into — exposure, not forcing (M2.3g) | 723 |

The rule counts are direct firings. The `Reuse` fact totals above are
larger (1,860 `SharedTail`, 495 `MultiPass`) because M2.3e made `Reuse`
travel the `L7-CONSED-AS-TAIL` edges with the other facts: a spine consed
onto a longer one is a **suffix** of it, so a tail the longer spine shares,
an extra entry into it and a head it escapes to all reach these cells too.
Leaving `Reuse` out of that propagation was the one place the census could
call a re-entered spine `SinglePass`, and it is what the independent
re-derivation caught.

`Recursion` is M1's definition and only M1's: a non-function member of a
recursive group that refers to itself through the value. A recursive
*function* building a finite list is `FiniteProducer`, and there is a test
that asserts M1 does not call such a binding a recursive value.

### The advisory recommendation

| | | |
|---:|---|---|
| 32 | `VecCandidate` | whole spine, entered more than once or outliving its consumers, no shared tail, finite producer |
| 727 | `IteratorCandidate` | one pass, nothing retained, every spine consumer streaming, finite producer |
| 1,925 | `PersistentCandidate` | a tail survives in two places, the spine is replayed, or repeated entry with tails retained |
| 30 | `LazyCandidate` | a value knot, or a short-circuiting consumer in front of an unbounded producer |
| 9,104 | `Unknown` | any fact is `Unknown`, or the facts match no recommendation — with the reason |
| **11,818** | | |

**The ordering, corrected at M2.3g.** An advisory is a claim that a
representation is sufficient *given everything we know*, so **every**
`Unknown` fact — spine, head, exposure, or a `Reuse::Escapes` — makes the
recommendation `Unknown`, before any positive fact is consulted. Until
M2.3g a proven `SharedTail` and M1's `RecursiveKnot` were decided *first*,
which let "one known property points this way" be published as "this is
sufficient": 266 flows were advised on that basis with another fact
unknown.

The positive facts are not lost. They are recorded as **constraints** on
the flow — things any representation must support whatever the advisory
says — and a constraint survives an `Unknown`:

| constraint | | `-O1` | of which the recommendation is `Unknown` |
|---|---|---:|---:|
| `RequiresTailSharing` | a tail of this spine survives in a second place (`L14`) | 1,860 | 265 |
| `RequiresRecursiveLaziness` | M1 calls the producer's binding a recursive value (`L13`) | 31 | 1 |
| `RequiresReplay` | a consumer retains the spine and walks it again (`L19`) | 0 | 0 |

Only then do the positive facts decide, in this order: a **value knot** is
a knot whatever else is true of it; then a **proven shared tail**, because
two owners seeing the same cells settles the representation; then a
**replayed** spine, because the cells must still be there for the second
walk; then the short-circuit-over-unbounded case, and last the
multi-pass / whole / single-pass arithmetic.

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
| 977 | Unknown | 682 | Unknown |
| 289 | PersistentCandidate | 492 | None |
| 39 | IteratorCandidate | 52 | Incremental |
| 5 | VecCandidate | 40 | Prefix(DataDependent) |
| | | 29 | Whole |
| | | 15 | Prefix(Known) |

### Accounting

Asserted in code (`ListAccounting::check`), on `-O1` and on all six matrix
profiles: every flow lands in exactly one bucket of the producer-kind,
recommendation, spine, head, **head-exposure**, reuse, storage and
recursion tables; every
flow either has a short-circuiting consumer or has not; every imported head
seen either has an axiom or has not; and every one of the census' list-cons
sites maps onto exactly one cell or carries a reason.

| profile | flows | ConsChain | Nil | Imported | Local | Vec | Iterator | Persistent | Lazy | Unknown |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `-O1` / A | 11,818 | 3,920 | 2,887 | 4,966 | 45 | 32 | 727 | 1,925 | 30 | 9,104 |
| B | 12,146 | 3,989 | 3,024 | 5,083 | 50 | 37 | 701 | 2,079 | 30 | 9,299 |
| C | 13,647 | 3,907 | 3,670 | 6,016 | 54 | 31 | 1,231 | 1,839 | 22 | 10,524 |
| D | 23,886 | 6,291 | 8,516 | 9,025 | 54 | 32 | 1,886 | 2,480 | 82 | 19,406 |
| E | 22,688 | 6,213 | 7,806 | 8,615 | 54 | 32 | 1,817 | 2,382 | 82 | 18,375 |
| F | 22,807 | 6,262 | 7,839 | 8,652 | 54 | 32 | 1,795 | 2,362 | 82 | 18,536 |

`h2r tuples`, `--verify`, `--boundaries`, `h2r laziness`, `h2r parsec` and
`h2r fields` are byte-identical on `-O1` before and after this milestone,
and stayed byte-identical through M2.3e. M2.3f adds an accounting section to
`h2r fields`, `lists`, `text` and `verify-rep` and changes no existing line
of any of them.

### Known limits, stated rather than hidden

* **The axiom table is asserted.** Every `L-AX-…` entry is a claim about
  base that the dump does not prove. The entries most worth re-reading are
  the aliasing ones — `reverse1`'s accumulator becoming the result's tail,
  `unpackAppendCString#`'s second argument, `dropWhile`/`drop`/`span`
  returning a suffix of their input — because a wrong alias claim turns a
  `PersistentCandidate` into an `IteratorCandidate`, which is the unsafe
  direction. Nothing that could not be read off the function's contract
  with certainty got an entry.
* **2,848 flows are stored with no visible spine demand**, and M2.3e split
  the reason by what holds them: 620
  (`…-in-a-holder-the-field-census-knows`) sit in a construction M2.3b has
  the field reads of, so M2.3f can pick that verdict up without re-analysing
  anything, and 2,228 (`…-in-a-holder-this-module-never-takes-apart`) sit in
  a holder that is never taken apart here or is not a construction at all.
  Whole-program (M2.4) work, not a missing rule here.
* **1,700 flows reach a holder that escapes.** `L18-STORED-FOLLOWED`
  inherits the holder's escapes, so a spine inside an escaping
  `TokenComment` is `Unknown` rather than guessed.
* **Traversal counting over-counts rather than under-counts.** A consumer
  is treated as a new entry into the spine unless it is reached through
  another consumer's tail alias, closed over known-local calls — and since
  M2.3e that closure requires **every** call site of a parameter to hand it
  a tail-derived argument, because a parameter that also receives the whole
  spine from somewhere else is an independent entry into it whatever the
  other call site does. Where that
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

## M2.3d — which of those flows are text, and what is done with them

`h2r text <dir> [--module M] [--json] [--explain] [--heads]`.

M2.3c's list census says how much of a spine is demanded. It deliberately
did not ask whether the elements are characters. This milestone selects the
**text** flows out of that population and refines them — it does not re-walk
the Core, and every spine fact it needs (spine demand, head demand, shared
tails, storage, escapes, recursion) is inherited with the `L…` rule id
cited.

### How `Char` is established

*Amended by [M2.4a](#m24a--stable-global-identity-and-structured-types).
This section originally read "the caveat this whole milestone rests on" and
described a level-6, textual type comparison. Dump format 5 carries
structured types, so the rules below now read `TyCon` identity and the
caveat is gone — with, as M2.4a's gate required, not one number changed.*

`Char` is `TyConApp` with the `TyCon` GHC itself names
`$ghc-prim$GHC.Types$Char`, and `[Char]` is that under
`$ghc-prim$GHC.Types$List`: **level 4, structural `TyCon` identity — GHC
type compatibility**. The plugin expands type synonyms before dumping, so
`String` and `FilePath` arrive already in that form; they are not spellings
anything has to recognise. GHC's rendering of each type still travels
alongside and is what the reports print — a *label*, never a verdict.

What the milestone still refuses to conclude is unchanged. Where a flow's
element type is a type **variable** — instantiated somewhere this module
cannot see — or there is no type to read, the flow is
`element-type-unknown` and is **never** assumed to be text. And a type is
still only one of the ways in: a fact that reads no type at all agreeing
with it is worth more than either alone, which is why every selection
records how `Char` was established.

### The population, and the five ways in

A list flow is selected when **any** of these fires. Each stands alone.

| rule | what it reads | level |
|---|---|---|
| `X0-ELEM-TYPE` | the `(:)` alternative's head binder is `TyConApp Char []` | 4 |
| `X1-LIST-TYPE` | the flow's own binder is `TyConApp List [TyConApp Char []]` | 4 |
| `X2-UNPACK-PRODUCER` | the producer is an `unpackCString#`-family call | 2 over 5 |
| `X3-CHAR-LITERAL-HEAD` | a cell's element is a `Char` literal or a saturated `C#` | 2 |
| `X4-CHAR-SCRUTINY` | a head binder is scrutinised by a `case` on `C#` or a `Char` literal | 1 over 2 |
| `X5-AXIOM-FIXES-CHAR` | a consumer's signature fixes the argument to `[Char]` (`eqString`, `unpackAppendCString#`, `lines`, `words`, `showLitString`, `hPutStr`, regex `compile`) | 5 |
| `X24-APPEND-SAME-ELEM` | an append does not change the element type, so a `[Char]` anywhere in a connected component of (append result ↔ its list operands) establishes it everywhere in the component | 5 over 2 |

`X24` is closed to a fixpoint with a union-find over the append relation. A
component that also contains a flow whose rendered element type is
concretely *not* `Char` is a contradiction and is **refused**, not
propagated into (0 refusals on every profile).

On `-O1`, of M2.3c's 11,818 list flows:

| | flows |
|---|---:|
| text | 4,431 |
| not text (element type reads as something else) | 1,788 |
| element-type-unknown — never assumed text | 5,599 |

and of the 4,431 text flows, how `Char` was established:

| | flows |
|---|---:|
| type only (level 4: the element's `TyCon` is `Char`) | 58 |
| structural only (the type did not agree, or there was none to read) | 1,772 |
| both — the type and a fact that reads no type agree | 2,601 |

90 of the structural selections came from `X24`. The type alone carries
only 58 flows; it is the *corroboration* it provides on 2,601 that it is
good for.

### The text-head table

`TEXT_HEADS` is a second deliberate name-keyed table, in the same spirit as
M2.3c's axiom table and at the same evidence level (**5, library axiom**),
under the same hard rule: consulted **only** for an imported head, which
M2.3c has already established for every `L8-AXIOM`/`L9-NO-AXIOM` consumer.
It is keyed on `(module, occ)` rather than the full stable name because a
package's unit id carries a build hash (`regex-tdfa-1.3.2.6-4dff8751…`).

It does one thing the axiom table does not: it gives a demand class to
heads the axiom table has **no entry for** — `hPutStr2`, `showLitString`,
the specialised list `==` and `compare`, regex-tdfa's `compile`. A flow
whose only unresolved consumer is such a head is `Unknown` in M2.3c and
decided here. That is the one place this milestone is *more* decided than
the last; it is asserted rather than derived, and every consumer it decides
is marked `(asserted)` in `--explain` (1,528 of them on `-O1`).

One consequence is recorded explicitly in the code: M2.3c sets
`Reuse::Escapes("no-axiom-for")` whenever *any* consumer is an imported head
its table has no entry for. That is a restatement of those consumers, not a
claim that the value left the walk, so it is not by itself an `Unknown` fact
here — each such consumer is reported individually, resolved by the text
table or not.

### Facts, then an advisory

Recorded independently, per flow:

* **`TextShape`** — `TextOnly` (every consumer is a `TEXT_HEADS` entry),
  `Mixed` (a generic list combinator or a structural `case` on the cells),
  `Unknown` (an imported head neither table knows, or the value left the
  walk), `Unobserved` (nothing observes it at all).
* **`Literal`** and **`AppendChain { length, all_literal, opaque }`** —
  counted in *operand segments* off the Core spine at the producer,
  following a let-bound operand by lexical identity, depth-capped at 64.
* **Per-consumer class** — `CompleteOutput` (the whole text is the subject:
  output, `eqString`, `==`, `length`, `reverse`, a regex compile),
  `Prefix` (`isPrefixOf`, `take`, `head`, `null`, `takeWhile`, a `case` on
  the first cell), `Incremental` (the left side of `++`, `map` over the
  characters, streaming output), `Retained` (nothing is demanded here),
  `Unknown`. Derived from the consumer's own M2.3c `SpineDemand` unless
  `TEXT_HEADS` asserts otherwise.
* **`char_semantics_required`** with its reasons — an element is exposed or
  the operation depends on characters rather than on encoded bytes. **This
  does not preclude `String`**: it says a future representation must
  preserve character semantics explicitly.
* **`SharedTails`, `PrefixConsumers`, `Storage`, `Escapes`** — inherited
  from `L14`, `L10`/`L16`, `L11`; cited, never recomputed.

On `-O1`:

| TextShape | flows | | consumer class | consumers |
|---|---:|---|---|---:|
| TextOnly | 1,862 | | CompleteOutput | 1,488 |
| Mixed | 38 | | Prefix | 653 |
| Unobserved | 1,004 | | Incremental | 364 |
| Unknown | 1,527 | | Retained | 6,641 |
| | | | Unknown | 2,891 |

| consumer side | consumers | | text family | consumers |
|---|---:|---|---|---:|
| Text | 3,690 | | Append | 1,917 |
| Neutral | 5,072 | | Compare | 1,184 |
| Opaque | 2,837 | | Show | 174 |
| Structural | 232 | | Affix | 173 |
| Generic | 206 | | CharSearch | 121 |
| | | | Output | 61 |
| | | | Regex | 55 |
| | | | LinesWords | 5 |

Construction: 2,414 flows are literal (`unpackCString#`-family producers),
1,349 are built by an append, 7 of those from literals only, and 1,268 are
an operand of an append. The append-chain histogram, in operand segments:

| segments | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| flows | 1,045 | 184 | 47 | 33 | 19 | 6 | 3 | 4 | 1 | 2 | 2 | 1 | 1 | 1 |

`char_semantics_required` holds for 882 of the 4,431, for these reasons
(a flow may have several):

| reason | count |
|---|---:|
| a consumer exposes individual characters | 738 |
| an element **is forced** (M2.3c's `HeadDemand`, proven) | 383 |
| a `(:)` alternative binds and uses the head | 177 |
| an element **is exposed to a callback** (M2.3c's `HeadExposure`) | 161 |
| a consumer depends on character positions or count | 69 |
| the head is compared against a `Char` literal | 59 |
| a `Char` literal is an element | 1 |

M2.3g split the second row. Before it, `an-element-is-forced` covered 510
flows, and for most of them the only evidence was a predicate or an `Eq`
method — which may ignore its argument. Character semantics are still
required in both cases (the element has to exist as a `Char` either way, so
the flag did not move except for the five flows the population lost), but
the milestone may not say "forced" when all it knows is "handed to a
callback".

### The advisory

Derived from the facts and clearly separated from them. **Nothing here
decides that any flow is a Rust `String`.** Precedence: any `Unknown` fact
first, then `NotText`, then the strong conjunction, then undecided.

| advisory | flows | condition |
|---|---:|---|
| `StrongStringCandidate` | 185 | `TextOnly` ∧ only complete-output or incremental consumers ∧ no character observed ∧ no shared tail ∧ no prefix consumer ∧ `FiniteProducer` |
| `TextValueUndecided` | 2,561 | text, representation open |
| `NotText` | 2 | selected by type, consumed only structurally, and no character observed anywhere |
| `Unknown` | 1,683 | an opaque consumer, a real escape, or an unknown consumer class |

2,345 flows have no text-shaped consumer at all, whatever else is unknown
about them — the honest measure of how much of ShellCheck's text is handled
by code this dump does not contain.

### The census' append argument sites

M2's census counts 573 lazy-argument sites at `unpackAppendCString#` and
545 at `GHC.Base.++` (the "ordinary calls" bucket), under its own
population filter — a non-trivial *computation* in a lazy or unknown
position — which `text::census_site` reproduces exactly, so the two
milestones count the same 1,118 sites. Each is mapped onto the text flow
its argument carries, or carries a reason:

| | sites |
|---|---:|
| map onto a text flow (all `TextValueUndecided`) | 226 |
| the argument is a `case`/`let` with no single producer | 281 |
| the argument is a local call result M2.3c follows as a *location* of another flow, not a flow of its own | 281 |
| the argument's flow is not text | 234 |
| the argument is an imported call with no axiom | 96 |

Separately, as *evidence* rather than population: of M2.3c's append
**consumer** sites, all 1,002 `unpackAppendCString#` sites and 905 of the
1,861 `GHC.Base.++` sites sit on a flow this milestone calls text (plus 12
of 144 `++_$s++` and the single `unpackAppendCStringUtf8#`).

### Accounting

Asserted in code (`TextAccounting::check`), on `-O1` and on all six matrix
profiles: text + not-text + element-type-unknown = M2.3c's flow count;
type-only + structural-only + both = the text flows; every text flow lands
in exactly one bucket of the shape, advisory, storage and recursion tables;
every append-produced flow appears exactly once in the histogram; the
per-module totals sum to the population; and every one of the census'
append argument sites maps onto exactly one text flow or carries a reason.

| profile | list flows | text | not text | elem unknown | type-only | struct-only | both | Strong | Undecided | NotText | Unknown |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `-O1` / A | 11,818 | 4,431 | 1,788 | 5,599 | 58 | 1,772 | 2,601 | 185 | 2,561 | 2 | 1,683 |
| B | 12,146 | 4,473 | 1,782 | 5,891 | 65 | 1,826 | 2,582 | 205 | 2,588 | 0 | 1,680 |
| C | 13,647 | 5,344 | 1,648 | 6,655 | 52 | 3,673 | 1,619 | 186 | 3,045 | 0 | 2,113 |
| D | 23,886 | 7,783 | 2,389 | 13,714 | 108 | 5,352 | 2,323 | 202 | 4,141 | 0 | 3,440 |
| E | 22,688 | 7,481 | 2,389 | 12,818 | 108 | 5,038 | 2,335 | 202 | 3,947 | 0 | 3,332 |
| F | 22,807 | 7,619 | 2,387 | 12,801 | 110 | 5,187 | 2,322 | 202 | 3,945 | 0 | 3,472 |

`h2r tuples`, `--verify`, `h2r laziness`, `h2r parsec`, `h2r fields` and
`h2r lists` (with `--axioms`) are byte-identical on `-O1` before and after
this milestone.

### Known limits, stated rather than hidden

* **Selection by type is level 4** since M2.4a — `TyCon` identity, not a
  rendered string. 58 flows rest on it alone. What it still cannot do is
  see through a type *variable*, and it does not try.
* **The text-head table is asserted.** The entries worth re-reading are the
  class overrides: calling `eqString` a *complete-output* consumer when its
  spine demand is a data-dependent prefix is a claim about what a
  representation decision turns on (the whole text is the subject of the
  comparison), not about how many cells are walked. `isPrefixOf` was
  deliberately **not** overridden, so it stays a prefix consumer.
* **`unpackCStringAscii#` has no axiom, and M2.3e established that it must
  not get one.** The 27 call sites in `ShellCheck.Formatter.JSON` and
  `.JSON1` are `$text-2.0.2$Data.Text.Show$$wunpackCStringAscii#`, and the
  `case` that consumes each one binds `(# ByteArray#, Int#, Int# #)`: it
  builds a `Data.Text.Text`, not a `[Char]`. It is invisible to M2.3c and to
  this milestone because it is not a list function at all, so the refusal is
  correct rather than a coverage loss. `unpackFoldrCString#` does not occur
  in this program.
* **5,599 flows are element-type-unknown.** Most are flows with no bound
  binder, no `(:)` alternative and no text-shaped consumer — nothing in the
  dump says what their elements are, and nothing here guesses.
* **1,527 flows have an `Unknown` shape.** 2,837 consumers are imported
  heads neither table knows or points at which the value left the walk;
  the largest single one is `ShellCheck.Interface.$wgo` (394 consumers).
  Whole-program work (M2.4), not a missing rule here.
* **Append chains are a lower bound.** An operand that is a parameter, a
  case, or an imported call counts as one segment and sets
  `all_literal = false`; the `opaque` field says how many such segments a
  chain has.
* **No Rust type is chosen.** `StrongStringCandidate` is the name of a
  conjunction of facts, not a decision. Even `char_semantics_required` does
  not rule `String` out — it rules out silently treating the value as
  bytes.

## M2.3e — re-deriving the representation verdicts independently

`h2r verify-rep <dir> [--module M] [--json] [--explain]`.

M2.2's [independent verifier](#the-independent-verifier) is the model: a
second walk that shares nothing with the analysis but the IR, re-derives
every verdict whose being wrong would be a miscompile, and forces every
disagreement to be settled by fixing whichever side is wrong.
`h2r-analysis/src/verify_rep.rs` does that for the three M2.3 censuses. It
has its own population test, its own constructor test and its own
climb-and-enumerate walk, and it **does not use `flow.rs`** — the generic
aggregate walk *is* the censuses' walk, so re-deriving a verdict with it
would only re-run the analysis being checked.

What it re-derives, and why those and not others:

| claim | `-O1` | a wrong one costs |
|---|---:|---|
| `Direct` field | 3,408 | a field's evaluation moves to the construction: a moved divergence |
| `Dead` field | 9 | a field that is read is dropped |
| `Recursive` field | 9 | M1's knot verdict misapplied |
| list `RecursiveKnot` | 31 | ditto |
| `VecCandidate` | 32 | a shared or infinite spine materialised |
| `IteratorCandidate` | 727 | a spine that is re-entered or retained turned into a one-shot iterator |
| `StrongStringCandidate` | 185 | a value whose characters are observed treated as opaque text |

A wrong `Deferred` / `Persistent` / `Undecided` / `Unknown` only costs
coverage, so nothing re-derives those.

### The two semantic dependencies, stated

Two things are *asserted* rather than derived anywhere in this compiler, and
re-deriving them would mean inventing a second unchecked assertion rather
than checking the first. The verifier therefore consults **the same** tables:

* the [library demand-semantics table](#the-library-demand-semantics-table)
  and the [text-head table](#the-text-head-table). What the verifier
  re-derives itself is everything around them: that the head really is an
  import, its stable name, which value argument of the call the value lands
  in, how many value arguments the call supplies, and hence which row
  applies;
* **M1's** `Class::RecursiveValue`, which every milestone reads rather than
  re-derives.

Everything else — aliasing, reachability, scrutiny, storage, escape,
traversal counting — is re-derived from the arena.

### What it found

| dump | claims | re-derived | **disagreements** | coverage refusals |
|---|---:|---:|---:|---:|
| `-O1` (and matrix A) | 4,401 | 4,391 | **0** | 10 |
| B | 5,277 | 5,266 | **0** | 11 |
| C | 6,127 | 6,112 | **0** | 15 |
| D | 16,810 | 16,795 | **0** | 15 |
| E | 15,111 | 15,096 | **0** | 15 |
| F | 15,077 | 15,062 | **0** | 15 |

That is the state *after* the fixes below. The first run refused **483 of
4,431 claims on `-O1`**, and those refusals were five different things —
three of them the verifier being blunt, two of them the census
over-claiming, in the unsafe direction.

**Two census bugs, both in `L7-CONSED-AS-TAIL`'s successor fixpoint.**
A flow consed onto another cell is a *suffix* of that longer spine, and the
fixpoint propagated the longer spine's `SpineDemand`, `HeadDemand`,
`Storage`, short-circuits and streaming back to it — but **not its
`Reuse`**. So a spine whose longer form was walked twice, shared a tail, or
escaped to a head with no axiom stayed `SinglePass`, and 21 flows on `-O1`
were called `IteratorCandidate` on that basis. `Reuse` now travels those
edges with the other facts, ranked `SinglePass < MultiPass < Escapes <
SharedTail`, and a flow that is *both* consed onto a longer spine and has a
spine consumer of its own is entered at least twice.

The second was `tail_derived`'s closure over known-local calls. It marked a
callee's parameter tail-derived as soon as *one* call site handed it a
tail-derived argument, so a parameter that also receives the whole spine
from another call site had its scrutiny counted as a continuation of someone
else's traversal rather than as a new entry. That under-counts traversals,
which is the unsafe direction, and contradicted the milestone's own stated
rule that a parameter's uses are the union over every call site. It now
requires **every** call site to hand it a tail-derived argument.

Together those moved `VecCandidate` 49 → 32 and `IteratorCandidate` 740 →
713 (727 after the new axioms), and `PersistentCandidate` 1,951 → 2,197.

**Three blunt spots in the verifier, and in each of them the verifier was
the wrong side.** Its first cut was not constructor-relative for a `[]`
producer: a nil can only ever select a `[]` alternative, so every `(:)`
alternative of a `case` on it — and every occurrence of the case binder
inside one — is unreachable for it, which is exactly what M2.3b's
[constructor-relative alternative selection](#sum-types-which-alternative-is-the-scrutiny)
says.
Following them found storage and shared tails that cannot happen, and that
was most of the first run's refusals. (A *cons* flow is still followed with
both alternatives live, because its tail alias need not be a cons; that is
strictly more conservative than the census and can only make the verifier
refuse more.) The second: it treated a value stored in a constructor as a
non-text-shaped consumer, which is wrong — storage is a fact about lifetime,
not about what is demanded, and it is what an `Iterator` claim turns on and
what a `StrongString` claim does not. The third: it applied the `Iterator`
storage rule to `Vec`, which *requires* storage or re-entry.

### The residue: what the verifier declines to re-derive

Ten refusals on `-O1`, none of them a claim about the census:

| n | claim | reason |
|---:|---|---|
| 5 | `IteratorCandidate` | `entries-counted-across-a-consed-as-tail-hop` |
| 5 | `VecCandidate` | `the-Whole-spine-of-a-loop-is-not-re-derivable-here` |

The first: the verifier counts every consumer reached across an `L7` hop as
an independent entry into the spine, because from the suffix's point of view
the longer spine's cells *are* these cells. Where the longer spines are
alternatives of one `case` — a `go` whose result is consed at five different
branches of `ShellCheck.Analytics` — that is one entry at run time and five
here. Refusing on it is a coverage loss.

The second: `Whole` for a `go`-loop is M2.3c's `L4-LOOP-WHOLE`, which turns
on where the recursive call *stands* (an evaluating position, a constructor
field, or under a `case` — `L4` vs `L17` vs `L5`). Re-deriving that would
mean writing the loop-position analysis a second time rather than checking
it. The verifier establishes every *other* fact those five `VecCandidate`
verdicts rest on — no shared tail, no value knot, a spine that is demanded,
storage or re-entry — and leaves the `Whole` fact to the census.

`R3-SAME-FRONTIER` is the third thing it declines, for the same reason: it
is a statement about the census' own walk. What it does instead is count the
`R3` verdicts, because the milestone's claim is that on `-O1` there are
**none** — and there are none, on every profile.

### `Direct`, by what actually proved it

| | `-O1` |
|---|---:|
| `R1-STRICT-FIELD` (GHC made the field strict) | 3,323 |
| `R2-FIELD-IS-VALUE` (the expression is already a value) | 85 |
| …of which the **only** evidence is that it is a string literal | **0** |
| `R3-SAME-FRONTIER` | 0 |

The middle row is the one worth calling out. `R2` accepts a string literal —
`unpackCString# "…"#` — and that is the one clause in the whole census that
does **not** argue from WHNF: GHC's `exprIsHNF` rejects it, and it is
accepted on `okForSpeculation` grounds instead (total, terminating, cheap,
so evaluating it eagerly can neither diverge nor error). The verifier
accepts it on the same grounds and counts the verdicts that rest on it
alone. On `-O1` there are **none**: of the 85, 73 are saturated constructor
applications and 12 are variables whose binding GHC itself marks `whnf` or
`okForSpec`. The clause is exercised only by its regression test.

### The axiom audit

The unsafe direction for the [axiom table](#the-library-demand-semantics-table)
is a wrong **alias** claim, because it turns a `PersistentCandidate` into an
`IteratorCandidate`. Every aliasing entry was checked against
base-4.18.3.0's own source *and* against a real call site in this dump.

`$base$GHC.List$reverse1` carries the most weight — its accumulator becoming
the result's tail is asserted, and 138 consumer sites depend on it. The
assertion is that the list is at `End(1)` and the accumulator at `End(0)`;
`reverse l = rev l []` makes that the order, and **all 87** `reverse1` call
spines in the dump pass a literal `[]` as the *second* value argument and
none as the first, which makes the position observable rather than assumed.

| entry | outcome |
|---|---|
| `reverse1` | confirmed — 87/87 call sites, `[]` second |
| `unpackAppendCString#` / `…Utf8#` | confirmed — 1,086 + 1 call sites, the list is the second argument and becomes the result's tail |
| `++`, `++_$s++` | confirmed — 927 + 68 call sites; the right operand *is* the result's tail |
| `drop`, `span`, `break`, `splitAt`, `tail` | order and suffix-aliasing confirmed against base; **0 call sites in this dump** |
| `dropWhile`, `$wspan`, `$wbreak` | confirmed — 29 / 16 / 6 call sites |
| `GHC.Magic.lazy` | confirmed — the identity, 72 call sites |
| `Data.Foldable.toList` | kept; it is a class-method key and the entry is only reached at the list instance, where it is the identity. 0 call sites |
| `GHC.List.concat`, `Data.Foldable.concat` | **corrected to `NoAlias`.** `concat = foldr (++) []` copies every inner list (each is a *left* operand of `++`), and a `[[a]]` spine cell can never be an `[a]` result cell. 0 call sites, so no output moved |
| `Data.OldList.lines` | **corrected to `NoAlias`**, same reasoning: each line is `break`'s freshly built first component, and a `[String]` spine cell is not a `String` cell. 5 consumer sites |

Eleven entries were added, each confirmed from base-4.18.3.0's source *and*
from the dump's own types at a call site:

| added | confirmed by | calls |
|---|---|---:|
| `$fEqList_$s$c==1`, `$s$c==2` | ghc-prim's `instance Eq a => Eq [a]`; the dump types both arguments `[Char]`/`[String]` and the result `Bool` | 81, 2 |
| `$fOrdList_$s$ccompare`, `$s$ccompare1` | the matching `Ord [a]` instance; result `Ordering` | 3, 72 |
| `Data.OldList.dropLength` | `dropLength :: [a] -> [b] -> [b]`, returns a **suffix of the second** argument; the dump's binders are literally `ns`/`hs`/`delta`, `isSuffixOf`'s own names | 11 |
| `Data.OldList.dropLengthMaybe` | the same, returning `Maybe [b]` | 31 |
| `Data.OldList.prependToAll` | `prependToAll sep (x:xs) = sep : x : …`; separator first, list second, confirmed by the dump's `[[Char]]` second argument | 3 |
| `GHC.List.splitAt_$s$wsplitAt'` | base's local `splitAt' :: Int -> [a] -> ([a],[a])`; the dump shows `Int#` then the list, and a literal `3#`/`1#` count | 10 |
| `GHC.List.flipSeq` | base's `flipSeq x !_n = x`, "just flip seq": the result **is** the first argument and the second is forced and discarded | 11 |
| `GHC.List.init1` | base's local `init' :: t -> [t] -> [t]`, floated out of `init`; the dump types the arguments `Token` and `[Token]` | 0 |
| `GHC.List.head1` | base's `badHead :: HasCallStack => a`, the `head []` error: **no list argument at all**, which the dump confirms (the type argument is the *result* type and the value argument is a CallStack) | 0 |

The last two fire zero times in this dump and are kept as the written record
of what they are: `head1` can never be a list consumer, and `init1`'s list
argument is never reached by a tracked flow.

Two heads keep their refusal, and for different reasons:

* `$base$Data.OldList$intercalate_$spoly_go1` (3 call spines, **0** consumer
  sites) — `poly_go` is a name GHC generated; base contains no such
  definition, so an entry could only be read off the shape of a call site.
  That is a guess, and the table does not take guesses.
* `$text-2.0.2$Data.Text.Show$$wunpackCStringAscii#` (27 call sites) — it is
  **not a list function**. Every `case` that consumes it binds
  `(# ByteArray#, Int#, Int# #)`: it builds a `Data.Text.Text`. M2.3d
  recorded its absence as a coverage loss; it is not one, and an axiom would
  have been a soundness bug.

`$base$GHC.List$dropLength`/`dropLengthMaybe` were listed in M2.3c as
`GHC.List` helpers; they are `Data.OldList`'s, which is why the dump reports
them under that module.

### The text-head overrides, challenged

* **`eqString` is classed `CompleteOutput` although its spine demand is a
  data-dependent prefix.** *Kept.* The two facts answer different questions
  and both are recorded: M2.3c says how many cells are walked (a prefix —
  the comparison stops at the first difference), M2.3d says what the value
  is *for* (the whole text is the subject of the comparison). A
  representation decision turns on the second: you do not choose a prefix
  representation for something that is compared for equality against another
  whole string. The `Prefix` fact is still there, uncontradicted, and the
  advisory still refuses `StrongStringCandidate` whenever a `Prefix`
  *consumer class* is present — which is the safety-relevant use of it.
* **`isPrefixOf` is deliberately not overridden.** *Kept.* It is the case
  where the prefix really is the value's role: `"foo" isPrefixOf s` reads as
  much of `s` as it needs and no more, and a representation that can answer
  it from a prefix is a legitimate choice. Overriding it to
  `CompleteOutput` would have removed 173 `Affix` consumers' only reason to
  keep the flow undecided.

### The two derivation orderings, challenged

* **A value knot wins over everything.** *Kept.* `Recursion::RecursiveKnot`
  is M1's verdict that the binding refers to itself *through the value*;
  there is no representation that is not a knot for such a thing, whatever
  the demand facts say, so deciding it first is not a precedence choice but
  the only correct answer. The 31 flows it covers are all `LazyCandidate`.
* **A proven `SharedTail` outranks an `Unknown` spine.** *Kept at M2.3e —
  and **reversed at M2.3g**, which is the one M2.3e ruling that did not
  survive.* The reasoning below is sound about the fact and wrong about the
  advisory: two owners seeing the same cells is indeed a positive
  structural fact, but an advisory is a claim of *sufficiency*, and a flow
  with an unknown consumer supports no such claim. Since M2.3g the fact is
  kept as the constraint `RequiresTailSharing` and the recommendation is
  `Unknown` whenever any other fact is — 265 flows moved. The original
  argument: how much of a spine anyone walks does not change the fact that
  two owners see the same cells, and `SharedTail` is a *positive*
  structural fact where `Unknown` is the absence of one; after M2.3e's
  `Reuse` propagation the rule decided 1,867 flows rather than 1,762, all on
  `PersistentCandidate` — the safe side. What that missed is that "safe
  side" is a property of the *fact*, not a licence to publish it as an
  advisory. The verifier checks the converse directly and always did: no
  flow it accepts as `Vec` or `Iterator` has a shared tail.

### The adversarial cases

Each shape has a hand-built regression test in `h2r-analysis/src/tests.rs`
*and* a count in the real `-O1` dump, printed by `verify-rep`, so that a
hand-built test is never the only evidence a rule was exercised.

| # | shape | in `-O1` | example | verdict |
|---|---|---:|---|---|
| 1 | `Foo (error …)` observed only at WHNF | 53 | `ShellCheck.Checks.ShellSupport` 112 | never `Direct` |
| 2a | an unused **lazy** field | 7 | `ShellCheck.CFG` 10329 | `Dead` |
| 2b | an unused **strict** field | 14 | `ShellCheck.ASTLib` 1626 | **not** `Dead` — forced at WHNF |
| 3 | forced on one branch, not another | 720 | `Main` 411 | `Deferred` |
| 4 | `take 1 (x : expensiveTail)` | 179 | `ShellCheck.ASTLib` 1220 | `Prefix(Known)`, never `Vec` |
| 5 | a `find`/`any` short-circuit | 921 | `Main` 140 | `Prefix(DataDependent)` + short-circuit, never `Vec` |
| 6 | two consumers sharing one tail | 1,860 | `Main` 7448 | `SharedTail` → `Persistent` (or a constraint on an `Unknown`), never `Iterator` |
| 7 | a finite recursive producer (a `go`) | 759 | `Main` 576 | `FiniteProducer`, not a knot |
| 8 | an actual recursive list value | 30 | `ShellCheck.Analytics` 2042 | `RecursiveKnot` → `LazyCandidate` (one more is a knot whose spine demand is `Unknown`) |
| 9a | stored in another ADT, holder read structurally | 181 | `Main` 140 | `StoredIn`, spine facts propagate |
| 9b | stored in another ADT, holder escapes | 4,357 | `Main` 74 | `Unknown` |
| 10 | through a higher-order parameter | 1,402 | `Main` 349 | `Unknown` with a reason |
| 11 | `[Char]` used textually **and** structurally | 151 | `Main` 135 | `TextValueUndecided` + `char_semantics_required`, never `StrongString` |
| 12 | `foldl'` over a whole list | 38 | `Main` 5566 | `Whole` spine, `IteratorCandidate` not `Vec` |
| 13 | the right operand of `xs ++ ys` | 1,770 | `Main` 7448 | `SharedTail` on `ys` |
| 14 | a case-binder alias under an unreachable alternative | 4 | `ShellCheck.Analytics` 99 | no escape — confirmed from both sides |

Case 14 is the one both sides had to agree on separately: the verifier does
its own constructor-relative alternative selection and skips the case
binder's occurrences that stand inside an alternative this value cannot
take, so `case v of { C x -> k x; D y -> store v }` on a known `C` is not an
escape for it either.

### M2.3e acceptance

* `h2r verify-rep` re-derives every `Direct`, `Dead`, `Recursive`,
  `RecursiveKnot`, `VecCandidate`, `IteratorCandidate` and
  `StrongStringCandidate` verdict with **0 disagreements** on `-O1` and on
  all six matrix profiles; the ten remaining refusals are the two
  weakenings written down above, both coverage-only, both named in the
  output as `C` rather than `D`.
* `h2r tuples`, `--verify`, `--boundaries`, `h2r laziness` and `h2r parsec`
  are byte-identical on `-O1` before and after.
* `cargo test` (141), `cargo clippy --all-targets` (0 warnings) and
  `cargo fmt --check` are clean; `ListAccounting::check`,
  `FieldAccounting::check` and `TextAccounting::check` still close on all
  seven dumps.

### Still unsound, or still unchecked

* The axiom table and the text-head table remain **asserted**, and the
  verifier consults them rather than checking them. What M2.3e added is that
  every aliasing claim now cites base's own definition and a call site in
  this dump; the demand claims (`Whole`, `Incremental`, prefix) are still
  read off contracts and not proved.
* `Produces::SameAsInput` on a polymorphic identity (`GHC.Magic.lazy`) makes
  every call a list producer regardless of the result type. `flipSeq` was
  given `NotAList` for exactly that reason, but `lazy`'s 72 call spines were
  left as they were rather than changing published output on a point the
  verifier does not depend on.
* The five `VecCandidate` verdicts whose `Whole` fact comes from
  `L4-LOOP-WHOLE` rest on one walk, not two.

## M2.3f — the representation view, and what the milestone claims

M2.3b/c/d record the facts, M2.3e re-derives every verdict whose being wrong
would be a miscompile. This section adds the three things a milestone needs
before it can be closed: a **view** that lays one site's proof out so a
person can audit it, **provenance** in `h2r show` so any Core node can be
asked what the three censuses say about it, and the milestone's own
**accounting**, asserted in code and printed by every command. It changes no
verdict: `h2r tuples`, `--verify`, `h2r laziness` and `h2r parsec` are
byte-identical on `-O1`, and `h2r fields`, `lists`, `text` and `verify-rep`
gain sections without a single existing line changing.

```sh
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.CFG --view 10329
cargo run --release --bin h2r -- fields ../core-json --module ShellCheck.AST --view-all --json
cargo run --release --bin h2r -- lists ../core-json --module ShellCheck.ASTLib --view 1220
cargo run --release --bin h2r -- text ../core-json --module ShellCheck.Formatter.GCC --view 11
cargo run --release --bin h2r -- show ../core-json ShellCheck.AST 5293       # + its M2.3 footers
```

### Three views, each with its own completeness assertion

The **field view** puts every field of one construction on one line — the
three facts, the derived rep, and the *route* that proved it — and under it
the observations that justify the facts, each with its node ids, plus (for
`Unknown`) the escape with its refined reason. `FieldView::check` asserts
that every field of the construction appears exactly once and that no line
names a field outside its arity:

```
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

`verified:` is `verify_rep`'s answer and only its answer: `yes`,
`coverage-refused (<reason>)`, `DISAGREED (<reason>)`, or `not a claim` for
the reps nothing re-derives because a wrong one only costs coverage.

The **list view** prints the producer, every cell, every consumer with the
rule that classified it *and the demand that one consumer contributes*, the
the facts each with the rule that decided it, and the advisory with the
fact conjunction it came from. `ListView::check` asserts every consumer
appears exactly once. Where a fact is the *absence* of a rule firing —
`SinglePass` is "no `L14` and no `L15`" — the view says that rather than
naming a rule that did not fire:

```
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

The **text view** is the text facts *on top of* the list view — selection
evidence with the rule that established `Char`, shape, per-consumer classes
with `(asserted)` marked where `TEXT_HEADS` overrode M2.3c's spine demand,
the char-semantics reasons, the append chain — and then prints the whole
list view underneath, so the inherited facts are visible rather than cited:

```
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

`--view-all --module M` does every site in a module and `--json` dumps the
views as structured data. Each has a hand-built regression test: the field
view lists every field once, the list view lists every consumer once, and
the text view shows the selection evidence (`X5-AXIOM-FIXES-CHAR` on a flow
no type would have selected).

### Provenance in `h2r show`

The three proof objects are loaded by default whenever the module has any,
exactly as the Parsec and tuple objects are, and `--no-fields`,
`--no-lists`, `--no-text` opt out one at a time. They annotate
constructions, field binders, producers, cells, tail aliases and consumers
inline, and print one footer per site the node takes part in — as itself or
as an *occurrence* of one of those binders:

```
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

A list footer carries the facts and the advisory
(`SpineDemand Prefix(DataDependent) [L8-AXIOM] … advisory PersistentCandidate
[verified: not a claim]`), and a text footer the consumer classes, the
append chain and the text advisory. All five proof objects' marks are
concatenated rather than merged, so it stays visible which object said what.
`show` verifies only the module it was asked about, so it stays a per-node
query and not a whole-program analysis.

### The milestone accounting

Asserted in code (`m23::RepAccounting::check`) and printed by `h2r fields`,
`lists`, `text` and `verify-rep` — always whole, so no command shows a
fragment of it. The rule is M2.2's, pointing the same way: **any claim the
verifier did not confirm, for coverage or otherwise, is unsupported and
never proven.**

```
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

*proven-eager* is `Direct` **and** re-derived; *proven-lazy* is `Deferred`
plus `Recursive` where it was re-derived. `Deferred` needs no second walk
and gets none: a wrong `Deferred` loses an optimisation and cannot
miscompile, which is exactly the criterion that decides what `verify-rep`
checks. The ten coverage refusals show up here as the difference between
M2.3c's published 32 `VecCandidate` / 727 `IteratorCandidate` and the 27 /
722 counted as *advised* — the five and five the verifier declined are
unsupported, not advised.

The **route-set histogram** is printed unconditionally, zero rows included,
because the overlap between the three `Direct` rules is the interesting
part and an absent row hides a zero:

```
Direct, by the route **set** that proves it (printed in full, zeros included)
     2648  R1
      675  R1+R2
        0  R1+R2+R3
        0  R1+R3
       85  R2
        0  R2+R3
        0  R3
```

M2.3b reports `Direct` by the rule that *fired first* (3,323 `R1`, 85 `R2`,
0 `R3`); this asks all three of every verdict. 675 of the 3,323 GHC-strict
fields are **also** already values, so `R2` would have proved them
independently — which is a real redundancy, not a coincidence, and it is why
the histogram exists. `R3` still proves nothing on the dump, and the
regression test that exercises it lands in `R1+R2+R3`, which is the only
place all three are visible together.

### The cross-milestone link

Three rules, each narrow, each requiring the verifier's confirmation:

| rule | what the thunk's right-hand side is | why it stops being a thunk |
|---|---|---|
| `M23-A-FIELD-ALREADY-A-VALUE` | a binding whose occurrence is a constructor field proven `Direct` by **`R2`** | the field expression is already a value, so there is no evaluation to defer |
| `M23-B-SELECTOR-OVER-AN-EAGER-FIELD` | a lazy selection `case c of C .. x .. -> x` over a field proven `Direct` | the field is forced at construction; no deferred selection remains |
| `M23-C-CELL-OF-A-SINGLE-PASS-SPINE` | the tail of a cell (or a text append operand) of a `Vec`/`Iterator` flow whose spine demand is `Whole` or `Incremental` | one eager pass consumes the spine, so the cell thunk becomes an iterator step |

```
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

`remaining + explained-by-tuples + explained-by-M2.3 = 2,242` is asserted,
as is "no site is counted twice": a site M2.2 already explains is M2.2's,
and the M2.3 walk skips it before it can claim it. The tuple column is read
from `link::ThunkLink` rather than recomputed, so the two milestones cannot
disagree about who owns a site.

From the other side, **29** of the M2 census' 1,996 constructor-field
argument sites stop being lazy positions — all 29 through the list cons,
where the spine the argument is consed into is consumed by one eager pass —
and **0** of the 1,118 append argument sites do.

**Eleven, and why it is not four hundred.** The number is small and the
reasons are structural rather than a missing rule:

* the whole `Deferred` population (986 fields) is *by definition* the
  thunks that stay: `Deferred` says the evaluation remains where GHC put it;
* the whole `PersistentCandidate` population (1,925 flows) has a shared tail
  or a second entry, so its cells outlive any one pass;
* 239 flows are `Vec`/`Iterator` over a **prefix** spine, which is precisely
  a spine whose tail may never be reached — eager consumption of a prefix
  does not make the unreached tail eager;
* and `M23-A` can almost never fire *by construction*: `R2` accepts a bare
  variable only when GHC's own `whnf`/`okForSpec` flag is set on its
  binding, and a binding GHC marks `whnf` is one M1 does not call a thunk in
  the first place. The five that do fire are the shapes where the flag sits
  on a different binding from the one M1 reports.

That itemisation is printed by `verify-rep` beside the table, in the same
spirit as M2.2's 288 holders: an adjacent population that would make the
number larger and the claim weaker.

### M2.3 acceptance

**The criterion is that every claim this milestone makes about *eager* or
*streaming* evaluation is re-derived by a second walk that shares nothing
with the first but the IR — not that coverage is high.** A wrong `Direct`
moves a divergence; a wrong `Vec`/`Iterator`/`StrongString` materialises or
one-shots a value that is shared. A wrong `Deferred`, `Persistent` or
`Unknown` costs an optimisation, so nothing re-derives those and nothing
needs to. And the facts come before the reps everywhere: three orthogonal
facts per field, seven per list flow, and the M2.3d facts on top — the rep is
a *function* of them, and for lists and text it is explicitly **advisory**,
a named conjunction of facts and not a decision about a Rust type.

Against the `-O1` dump, all of the following hold.

**The populations are partitioned and every equation closes.** 9,166
constructions / 19,830 fields, 11,818 list flows, 4,431 text flows;
`FieldAccounting::check`, `ListAccounting::check`, `TextAccounting::check`
and `RepAccounting::check` all close, on `-O1` and on all six matrix
profiles. The three tables are
[above](#the-milestone-accounting): 19,830 = 3,408 + 995 + 9 + 15,418 fields,
11,818 = 2,704 + 9,114 list flows, 4,431 = 2,748 + 1,683 text flows, and the
1,996 / 1,310 / 1,118 site tables close the same way.

**Every claim is proven twice.** `h2r verify-rep` re-derives all 4,401
claims — 3,408 `Direct`, 9 `Dead`, 9 `Recursive`, 31 `RecursiveKnot`, 32
`VecCandidate`, 727 `IteratorCandidate`, 185 `StrongStringCandidate` —
with **0 disagreements** on `-O1` and on B–F. Ten refusals remain on `-O1`,
all coverage-only and both named:

| n | claim | refusal | why it is a coverage loss |
|---:|---|---|---|
| 5 | `IteratorCandidate` | `entries-counted-across-a-consed-as-tail-hop` | the verifier counts every consumer across an `L7` hop as an independent entry; where the longer spines are alternatives of one `case`, that is one entry at run time and five here |
| 5 | `VecCandidate` | `the-Whole-spine-of-a-loop-is-not-re-derivable-here` | `Whole` for a `go`-loop is `L4-LOOP-WHOLE`, a statement about where the recursive call *stands*; re-deriving it would be writing the loop-position analysis twice rather than checking it |

All ten are counted as **unsupported** in the accounting, never as advised.
`R3-SAME-FRONTIER` is declined for the same reason and there are 0 of them
to decline.

**The two census bugs M2.3e found were fixed, and both were in the unsafe
direction.** `Reuse` was not propagated across `L7-CONSED-AS-TAIL`, so a
spine whose longer form was walked twice, shared a tail or escaped stayed
`SinglePass` — 21 flows were `IteratorCandidate` on that basis. And
`tail_derived`'s closure marked a callee's parameter tail-derived as soon as
*one* call site handed it a tail-derived argument, which under-counts
traversals; it now requires **every** call site to. Together they moved
`VecCandidate` 49 → 32 and `IteratorCandidate` 740 → 713 (727 after the new
axioms), and `PersistentCandidate` 1,951 → 2,197 (1,925 after M2.3g's
[ordering correction](#correction-m23g--the-axiom-layer)).

**One axiom would have been a soundness bug.**
`$text-2.0.2$Data.Text.Show$$wunpackCStringAscii#` (27 call sites) is not a
list function at all — every `case` consuming it binds
`(# ByteArray#, Int#, Int# #)` and builds a `Data.Text.Text`. M2.3d had
recorded its absence from the axiom table as a coverage loss; it is not one,
and an entry would have given a `Text` a `[Char]`'s demand semantics.

**Every adversarial shape has a count in the real dump**, not only a
hand-built test —
[the table](#the-adversarial-cases) — 53 / 7 / 14 / 720 / 179 / 921 / 1,860
/ 759 / 30 / 181 / 4,357 / 1,402 / 151 / 38 / 1,770 / 4, printed by
`verify-rep` so a rule can never be exercised by its test alone.

**The two asserted tables are labelled as asserted.** The 101-entry library
demand-semantics table and the text-head table sit at evidence level 5 —
below def-use dataflow because nothing in the dump proves them, above
textual type comparison because they are statements about semantics. Every
*aliasing* claim is now confirmed against base-4.18.3.0's own source **and**
against a call site in this dump (`reverse1` 87/87 with `[]` second,
`unpackAppendCString#` 1,086+1, `++` 927+68, `dropWhile`/`$wspan`/`$wbreak`
29/16/6, `GHC.Magic.lazy` 72); two were **corrected to `NoAlias`**
(`concat`, `lines`) and two heads keep their refusal. The *demand* claims
(`Whole`, `Incremental`, prefix) are still read off contracts and are not
proved.

**No verdict rests on a name.** Every population is selected through GHC's
`DataConInfo` or through an import test, never by spelling; the
program/library split, the constructor names in the residual and the family
attributions are diagnostics. The one thing keyed on a name is the axiom
lookup, which is applied **only** to an imported id, with a regression test
that a program function called `map` is never looked up.

**The residual, itemised and owned:**

| | | whose problem it is |
|---:|---|---|
| 15,418 | fields `Unknown` | 2,264 stored in a list cell (M2.3c's population, followed as a spine but not as a field), 311 in a tuple field (M2.2's), 1,919 (998 + 573 + 348) a **program** construction that escapes — `TokenComment`, `OuterToken`, `Comment` — which is M2.4's whole-program work, 1,912 (760 + 595 + 557) a **library** construction that escapes, and 1,708 (1,143 `eta` + 565 `eok`) an unknown higher-order callee → M2.4 higher-order |
| 9,114 | list flows `Unknown` | 2,228 stored with no visible spine demand in a holder this module never takes apart, 620 in a holder the field census *does* know, 1,718 reaching a holder that escapes, 1,044 an unknown spine demand — and 266 of the 9,114, cutting across those reasons, carry a proven constraint (`RequiresTailSharing`, `RequiresRecursiveLaziness`) beside the unknown |
| 80 | imported heads with **no axiom**, 1,545 of the 6,660 imported consumer sites | the largest are `ShellCheck.Interface.$wgo` (394), `GHC.Show.showLitString` (168), `Text.Parsec.Char.string1` (88), `GHC.Show.showList__` (66), `GHC.IO.Handle.Text.hPutStr2` (61), regex-tdfa's `compile` (49), `Data.Set.Internal.$fDataSet1` (45) — whole-program (the ShellCheck ones) or more axioms (the base ones) |
| 1,683 | text flows `Unknown` | 2,837 consumers are imported heads neither table knows, or points at which the value left the walk |
| 2,345 | text flows with no text-shaped consumer at all | the honest measure of how much of ShellCheck's text is handled by code this dump does not contain |
| 10 | claims the verifier refuses | the two weakenings above, both coverage-only |

**How to audit a site.** `h2r show <dir> <module> <node>` for the footers,
`h2r fields --view <node>` for the field-by-field proof, `h2r lists --view
<node>` for the producer / cells / consumers / facts, `h2r text --view
<node>` for the text facts on top of them; `--view-all --module M` for a
whole module and `--json` for any of them. All four are shown above.

**Known limits, stated rather than hidden:**

* ~~**rendered types are level-6 evidence.**~~ **Fixed by
  [M2.4a](#m24a--stable-global-identity-and-structured-types):** dump
  format 5 carries structured types and selection of `[Char]` is `TyConApp`
  with a stable `TyCon` (level 4). 58 of the 4,431 text flows rest on the
  type alone; the population and every verdict are unchanged.
* **`R3-SAME-FRONTIER` is exercised only by its tests.** GHC's
  case-of-known-constructor has already eliminated every construction
  scrutinised in the frame that built it, so `R3` fires on nothing in any
  of the seven dumps. The rule stays, with a positive and a negative
  regression test, and the route-set histogram is where its absence is
  visible.
* **the five `VecCandidate` verdicts** whose `Whole` fact comes from
  `L4-LOOP-WHOLE` rest on one walk, not two — and are therefore counted as
  unsupported.

`cargo test` (159), `cargo clippy --all-targets` (0 warnings) and
`cargo fmt --check` are clean; `h2r tuples`, `--verify`, `h2r laziness`,
`h2r parsec` and `h2r compare` are byte-identical on `-O1` before and after
M2.3f **and after M2.3g**. All four accounting checks close on all seven
dumps.

### Correction (M2.3g) — the axiom layer

*2026-09-14. The acceptance above was written before this review; it is
amended here rather than re-stamped.*

**The verifier's 0 disagreements never validated the axiom table.**
`verify_rep.rs` re-derives which argument of which saturated call to which
*import* a value lands in, and then **reads the table's row for it**. The
table is the milestone's asserted semantic dependency: aliasing claims are
confirmed against base-4.18.3.0's source *and* a call site in this dump,
demand and forcing claims are read off base's definitions. Two independent
walks that consult the same asserted table agree about the table by
construction. A review of the table's *contents* found three classes of
error, none of which the verifier could have caught.

**1. `Produces` conflated "returns a list" with "returns something
containing a list" — a population bug.** Any entry whose `Produces` was not
`NotAList` made its call an `L0-IMPORTED` producer, so calls whose result is
a *pair* of lists, an *action* returning a list, or a polymorphic identity
were flows whose producer node is not a list at all. The schema now states
the outer return type honestly — `NotAList`, `DirectList(kind)`,
`ProductContainsList{components}`, `EffectContainsList(kind)`,
`OtherContainsList` — and **only `DirectList` starts a flow**. The other
variants keep their argument-demand and aliasing facts for the consumer
side; recovering the components is tuple and effect normalisation's work.

| entry | `Produces` before → after | base |
|---|---|---|
| `GHC.List.span`, `GHC.List.break` | `Incremental` → `ProductContainsList(2)` | `span p xs = (takeWhile p xs, dropWhile p xs)` — GHC/List.hs |
| `GHC.List.$wspan`, `GHC.List.$wbreak` | `Incremental` → `ProductContainsList(2)` | the worker returns `(# [a], [a] #)`; the old note said so and the field still claimed a list |
| `GHC.List.splitAt` | `Incremental` → `ProductContainsList(2)` | `splitAt n xs = (take n xs, drop n xs)` |
| `GHC.List.splitAt_$s$wsplitAt'` | `Incremental` → `ProductContainsList(2)` | the specialised worker of `splitAt' :: Int -> [a] -> ([a],[a])` |
| `GHC.List.unzip` | `Incremental` → `ProductContainsList(2)` | `unzip :: [(a,b)] -> ([a],[b])` |
| `Data.Traversable.mapM`, `forM`, `traverse`, `sequence` | `WholeBeforeFirstCell` → `EffectContainsList(WholeBeforeFirstCell)` | `mapM :: (a -> m b) -> [a] -> m [b]` |
| `Data.OldList.dropLengthMaybe` | `NotAList` → `OtherContainsList` | returns `Maybe [b]`; the old value was honest but said nothing about the suffix inside |
| `GHC.Magic.lazy` | `SameAsInput` → `NotAList` | `lazy :: a -> a`; `a` is not a list at every call site, which is exactly why `flipSeq` was already `NotAList`. The "known limit" M2.3f recorded about this entry is now fixed rather than tolerated |

**99 `L0-IMPORTED` flows disappeared** on `-O1`: `$wspan` 16, `$wbreak` 6,
`splitAt_$s$wsplitAt'` 5, `GHC.Magic.lazy` 72. (`span`, `break`, `splitAt`,
`unzip` and the `Traversable` four never occur saturated as producers in
this dump — GHC's worker/wrapper had already replaced them — so their rows
cost nothing here and are corrected anyway.) 92 of the 99 were `Unknown`
and 7 were `PersistentCandidate`.

**2. `HeadDemand` claimed forcing where the axiom only proves exposure.**
The enum is documented as "which elements are forced", and entries like
`any`, `all`, `find`, `takeWhile`, `elem`, `nub`, `sort` marked heads
`Prefix`/`All` — but `any (const True) xs` forces no element, and an `Eq` or
`Ord` method may ignore its argument. The fact is split: `HeadDemand` is now
**proven forcing only** and the new `HeadExposure` records which callback an
element reaches (`Predicate`, `Eq`, `Ord`, `Show`, `Other`), with
`BoundAndUsed` for a `(:)` alternative's head binder.

| kept as forcing (and why) | moved to exposure |
|---|---|
| `eqString` — at `Char` the comparison is the `eqChar#` primop | `elem`, `notElem`, `lookup`, `isPrefixOf`, `isSuffixOf`, `isInfixOf`, `nub`, `group`, the four specialised list `==`/`compare` copies → `Eq`/`Ord` |
| `and`, `or` — `foldr (&&)`, and `(&&)` case-analyses its argument | `takeWhile`, `dropWhile`, `span`, `break`, `any`, `all`, `find` (both copies) → `Predicate` |
| `lines` — `break (== '\n')` on `Char` | `sort`, `sortOn`, `maximum`, `minimum` → `Ord`/`Other`; base's `sortOn` `seq`s the computed **key**, not the element |
| `words` — `isSpace` case-analyses the `Char` | `sum` → `Other` (`(+)` comes from a dictionary) |
| | `map`, `filter`, `foldr`, `foldl`, `foldl'`, `zipWith`, `concatMap`, `mapMaybe`, `nubBy`, `sortBy`, `groupBy`, `mapM_`/`forM_`/`traverse_`/`sequence_` and the `Traversable` four, which previously claimed `None` and now say **which** callback sees the elements |

**31 entries had a `head` claim weakened** from `Prefix`/`All` to `None`,
and 53 of the 101 now carry a non-trivial `exposure`. On `-O1`,
`HeadDemand::Prefix` fell **972 → 544** and `None` rose 5,054 → 5,482;
nothing moved into `All`, which had come from `L4`-shaped loops and from
`lines`/`words`, both of which are proven. The new fact reads: 5,340
`NotExposed`, 460 `BoundAndUsed`, 401 `Eq`, 61 `Other`, 46 `Predicate`, 7
`Ord` (515 callback exposures in all), 5,503 `Unknown`.

In the text census, `char_semantics_required` now cites which of the two it
saw. The flag itself barely moved — an element handed to a callback still
has to exist as a `Char` — but the evidence did:

| reason | before | after |
|---|---:|---:|
| `an-element-is-forced` | 510 | 383 |
| `an-element-is-exposed-to-a-callback` | — | 161 |
| flows with `char_semantics_required` | 887 of 4,436 | 882 of 4,431 |

(The five lost are flows the population correction removed; no flow lost
the requirement.) The verifier splits the same way: its `StrongString`
refusal is `an-individual-character-is-observed` for proven forcing and
`an-individual-character-is-exposed-to-a-callback` for exposure. Neither
fires on `-O1` — all 185 claims are re-derived — but the distinction is
in the walk, not only in the census.

**3. `cycle` and `isInfixOf` encoded the wrong *kind* of demand.**
`cycle xs = xs' where xs' = xs ++ xs'` consumes its argument incrementally
and **replays** it forever; `Whole` said the call walks to the end before
returning, which on an infinite argument never happens. `isInfixOf needle
hay = any (isPrefixOf needle) (tails hay)` retries the needle at successive
positions: neither spine is necessarily walked whole, and both are
re-traversed. The new fact is `Axiom::replays` (end-indexed arguments) and
`Reuse::Replayed`, distinct from `Whole`, `MultiPass` and `SharedTail`:

| entry | before → after | base |
|---|---|---|
| `GHC.List.cycle` | `Whole` → `Incremental` + replays `End(0)` | `cycle xs = xs' where xs' = xs ++ xs'` — GHC/List.hs |
| `Data.OldList.isInfixOf` | needle `Whole` → `PrefixDataDependent`, both arguments replayed | `isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)` — OldList.hs |
| `Data.OldList.isSuffixOf` | both spines replayed (the `Whole` demand is right here) | `isSuffixOf ns hs = maybe False id $ do delta <- dropLengthMaybe ns hs; return $ ns == dropLength delta hs` — both spines are walked once to measure and once to compare |
| `Data.OldList.intercalate` | separator replayed, `streaming` true → **false** | `intercalate xs xss = concat (intersperse xs xss)` — the separator is inserted at every gap and copied by `concat` |

The rest of the table was searched for the same shape: `dropLength` and
`dropLengthMaybe` each make **one** pass — the replay in `isSuffixOf` is at
the call site that uses both, and it is recorded there, not in the helpers;
a `zip xs xs` style self-reuse is a property of the *call site*, not of the
entry, and the walk already records it as two consumers of one flow
(`MultiPass`). **None of the four entries carrying a replayed argument — six arguments in
all — is called anywhere in these seven dumps, so `Reuse::Replayed` has 0
firings.** It is printed with
its zero.

**4. Every `Alias` was type-checked.** `ResultSharesArg(i)` is only
possible when the result spine and the argument spine can have the same
element type. Two new variants were needed, and the audit is entry by
entry:

| entry | alias | base definition it rests on |
|---|---|---|
| `unpackAppendCString#`, `…Utf8#` | `ResultIsTailOfArg(0)` *kept* | `unpackAppendCString# :: Addr# -> [Char] -> [Char]` — the second argument is returned as the tail |
| `GHC.Base.++`, `++_$s++` | `ResultIsTailOfArg(0)` *kept* | `(++) [] ys = ys` — GHC/Base.hs |
| `GHC.List.tail` | `ResultIsTailOfArg(0)` *kept* | `tail (_:xs) = xs` |
| `GHC.List.reverse1` | `ResultIsTailOfArg(0)` *kept* | `rev [] a = a` — the accumulator is returned |
| `GHC.List.dropWhile` | `ResultSharesArg(0)` *kept* | `dropWhile p xs@(x:xs') = if p x then dropWhile p xs' else xs` |
| `GHC.List.drop` | `ResultSharesArg(0)` *kept* | `drop n xs` returns a suffix |
| `Data.OldList.dropLength` | `ResultSharesArg(0)` *kept* | `dropLength :: [a] -> [b] -> [b]`; the result is a suffix of the `[b]`, and the types agree |
| `GHC.List.flipSeq` | `ResultSharesArg(1)` *kept* | `flipSeq x !_n = x` — the result *is* the first argument; `Produces` stays `NotAList` because `a` need not be a list |
| `GHC.Magic.lazy` | `ResultSharesArg(0)` *kept* | `lazy :: a -> a`; only `Produces` was wrong |
| `Data.Foldable.toList` | `ResultSharesArg(0)` *kept* | at the list instance, `toList = id` |
| `GHC.List.span`, `break`, `$wspan`, `$wbreak`, `splitAt`, `splitAt_$s$wsplitAt'` | `ResultSharesArg(0)` → **`ResultContainsSuffixOfArg(0)`** | the suffix is the pair's *second component*; the outer result is a pair, and the two axes must not be spelled with one field |
| `Data.OldList.dropLengthMaybe` | `ResultSharesArg(0)` → **`ResultContainsSuffixOfArg(0)`** | the suffix is inside the `Just` |
| `GHC.List.head`, `last`, `!!`, `$w!!` | `NoAlias` → **`ResultSharesElementOf(i)`** | `head (x:_) = x`, `last`/`(!!)` likewise return an *element*: when the elements are lists the result shares cells with one of them, and that is **not** a shared tail on this spine |
| `concat`, `Data.Foldable.concat`, `intercalate`, `unwords`, `unlines`, `lines` | `NoAlias` *kept* | `concat = foldr (++) []` (GHC/List.hs) makes every inner list a **left** operand of `(++)`, so it is copied — even the final `xs ++ []`; `intercalate xs xss = concat (intersperse xs xss)` (OldList.hs) inherits that; `unlines (l:ls) = l ++ '\n' : unlines ls` and `unwords (w:ws) = w ++ go ws` copy every line and every word, the last one included (the Report-prelude `foldr1` `unwords` would share it; base-4.18 does not) |
| every remaining entry | `NoAlias` *kept* | result cells are freshly allocated |

`ResultContainsSuffixOfArg` still puts `RequiresTailSharing` on the
**input** flow — `span`'s second component really does keep the argument's
cells alive — while the call itself is no longer a producer. That is the
point of separating the axes. `ResultSharesElementOf` is the one category
M2.3e could not express; it is *not* assigned to `concat`, `intercalate`,
`unwords` or `unlines`, where base copies, but to the four entries whose
result **is** an element.

**5. The advisory ordering was wrong about what an advisory means.** A
proven `SharedTail` and M1's `RecursiveKnot` used to be decided *before*
the `Unknown` checks, so "one known property points this way" was published
as `PersistentCandidate`/`LazyCandidate` — which reads as "this
representation is sufficient". It is not sufficient when another consumer
is unknown. Every `Unknown` fact now wins, the positive facts are recorded
as constraints, and the accounting counts a constrained `Unknown` as
unsupported like any other:

| moved | from → to | constraint it now carries |
|---:|---|---|
| 265 | `PersistentCandidate` → `Unknown` | `RequiresTailSharing` |
| 1 | `LazyCandidate` → `Unknown` | `RequiresRecursiveLaziness` |

**The tables, before → after, on `-O1`:**

| `h2r lists` | before | after |
|---|---:|---:|
| flows | 11,917 | **11,818** |
| `L0-IMPORTED` producers | 5,065 | **4,966** |
| `SpineDemand::Unknown` | 5,602 | **5,503** |
| `HeadDemand::Prefix` / `None` | 972 / 5,054 | **544 / 5,482** |
| `HeadExposure` (new) | — | 5,340 NotExposed, 460 BoundAndUsed, 515 callbacks, 5,503 Unknown |
| `Reuse::SharedTail` | 1,867 | **1,860** |
| `VecCandidate` | 32 | 32 |
| `IteratorCandidate` | 727 | 727 |
| `PersistentCandidate` | 2,197 | **1,925** |
| `LazyCandidate` | 31 | **30** |
| `Unknown` | 8,930 | **9,104** |
| constraints (new) | — | 1,860 tail sharing, 31 recursive laziness, 0 replay; 266 of them on an `Unknown` |

| `h2r text` | before | after |
|---|---:|---:|
| text flows | 4,436 | **4,431** |
| `char_semantics_required` | 887 | **882** |
| — of those, `an-element-is-forced` | 510 | **383** |
| — of those, exposed to a callback | — | **161** |
| `StrongStringCandidate` | 185 | 185 |
| `Unknown` | 1,688 | **1,683** |

| `h2r verify-rep` | before | after |
|---|---:|---:|
| claims checked / re-derived / refused | 4,401 / 4,391 / 10 | **4,401 / 4,391 / 10** |
| disagreements | 0 | **0** |
| shape 6 (a tail in a second place) | 1,867 | **1,860** |
| shape 8 (a value knot) | 31 | **30** |
| shape 9b (holder escapes) | 4,297 | **4,357** |
| shape 10 (higher-order parameter) | 1,355 | **1,402** |
| shape 11 (`[Char]` textual **and** structural) | 156 | **151** |
| shape 13 (right operand of `++`) | 1,777 | **1,770** |

| accounting | before | after |
|---|---|---|
| list flows | 11,917 = 2,977 + 8,940 | **11,818 = 2,704 + 9,114** |
| text flows | 4,436 = 2,748 + 1,688 | **4,431 = 2,748 + 1,683** |
| the 1,310 list-cons sites | 29 + 402 + 879 | **29 + 303 + 978** |
| the M1 link | 2,242 = 2,139 + 92 + 11 | **unchanged** |
| fields | 19,830 = 3,408 + 995 + 9 + 15,418 | **unchanged** |

All four accounting `check()`s close on `-O1` and on all six matrix
profiles, where the flow counts fall by 99 / 127 / 101 / 101 / 101 / 101 and
the text counts by 5 each, with **0 disagreements** and the same 10 / 11 /
15 / 15 / 15 / 15 coverage refusals as before.

**What is still asserted rather than proven.** The same thing as before,
now stated where it belongs: **the axiom table is this milestone's semantic
dependency.** Its aliasing claims are checked against base's source and a
call site; its demand, replay and forcing claims are read off base's
definitions and are not derived from anything in the dump. The verifier
consults it and cannot confirm it. What M2.3g adds is that each of those
claims now has a field of its own, so a wrong one is a wrong *statement*
rather than a conflation — and `h2r lists --axioms` prints all six per
entry.

**Regression gate.** `h2r tuples`, `--verify`, `h2r laziness`, `h2r parsec`
and `h2r compare` are byte-identical on `-O1` before and after M2.3g. `h2r
fields`'s own census output is byte-identical too; the only lines of it
that move are the two rows of the shared M2.3 accounting block that belong
to lists and text. `cargo test` 144 lib tests (151 in all crates, 10 of them
new and adversarial: a pair-returning head is not a producer, a product- or
effect-returning head is not a producer, only `DirectList` may produce,
`cycle` is incremental and replayed, `isInfixOf`'s needle is replayed,
`concat` shares neither spine nor element, an element alias is not a shared
tail, a predicate exposes without forcing, a primop does force, and a shared
tail beside an unknown consumer is `Unknown` with a constraint).

## M2.4a — stable global identity and structured types

Two things the earlier milestones had to work around were properties of the
*dump*, not of the program:

* the imported-id table was keyed by GHC **unique**, which
  [M2.1 showed is not an identity](#scoping-uniques-are-not-unique) — 116,340
  binders share 42,572 uniques — so the one place a unique was still a
  linkage key was the last place a merge could hide;
* every type arrived only as GHC's **pretty-printed string**, so
  "the element is a `Char`" was a textual comparison (level 6) against the
  four spellings `Char`, `GHC.Types.Char`, `[Char]`, `String`, `FilePath`
  that GHC might print.

Dump format 5 removes both. The format bump is the whole of this milestone:
**no analysis was allowed to change its mind about anything.**

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

**Identity.** `nameStableString` is `$unit$Module$occ`. It is the key of the
id table and of every `TyCon`. Uniques are still dumped — on `Var` nodes,
binders, type variables and type constructors — and are now **diagnostics
only**; the loader rejects format 4 with a message that says to re-extract.
The check that this is sound is not an argument but a count: of the 44,992
occurrences the resolver classifies as `Ref::Global` on the `-O1` dump,
**0** carry `isGlobal = false` and **0** have no entry in the table, and the
2,972 stable names in the new tables are in bijection with the 2,972
distinct global uniques the old ones held.

**Where the module's own top-level binders went.** Nowhere: they were never
in the table. GHC globalises a module's top-level binders in CoreTidy, which
runs *after* the simplifier, so at the point this plugin runs they are
`LocalId`s and `isGlobalId` is false for them. That is the right answer
anyway — they are bound in the module, so `Module::resolve` resolves their
occurrences lexically to their binders, and a binder is the authoritative
source for arity and demand where an occurrence's `IdInfo` may be stale.
`Scope::head_sig` reads the id table only when nothing in the module binds
the head.

**Types.** The plugin emits the `expandTypeSynonyms` form, so `String` and
`FilePath` arrive as `TyConApp List [TyConApp Char []]` and no consumer has
to know either name. The unexpanded rendering stays alongside in `"type"`,
which is what `h2r`'s reports print — a label, never a verdict. The Rust
side rebuilds the table into owned `Ty` values and adds `Ty::is_char`,
`list_elem`, `is_list_of`, `fun_args`/`fun_result`, `tycon` and
`Ty::alpha_eq` (structural alpha-equivalence, iterative, over a worklist).

**Size.** Interning matters: `ShellCheck.Parser` has 61,494 type occurrences
over 1,041 distinct renderings, and its table has 9,516 entries (19,944 over
all 28 modules). Emitting types inline would have multiplied the dump;
emitting a table, and dropping the 32,789 local entries the id table no
longer needs, made it **smaller** — 82,171,834 → 78,691,280 bytes on `-O1`,
−4.2%.

### What moved up the evidence hierarchy

`X0-ELEM-TYPE` and `X1-LIST-TYPE` in [M2.3d](#m23d--which-of-those-flows-are-text-and-what-is-done-with-them),
and the `X7`/`element-type-unknown` refusals with them, now read `TyCon`
identity: **level 4, GHC type compatibility**, where they were level 6.
Nothing else moved. In particular [M2.1's](#m21--proving-parsecs-cps-roles)
`R1-LAYOUT`, `R1-UNPARSER-SIG`, `R1-TYPE-AGREE` and `R1-TRAILING-ERASURE`
still read rendered types and still sit at levels 4/5 with
`alpha_normalise`; migrating them is a later milestone's work and needs its
own gate, so it was deliberately left alone here.

### The gate

The acceptance condition was that **not one semantic number changes**. All
113 reports — `stats`, `laziness`, `parsec`, `tuples` (plus `--verify` and
`--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus
`--heads` and `--explain`), `verify-rep` (plus `--explain`), the `--json`
form of each, and `compare` — were captured on the old binary and the old
dumps; the dumps were then re-extracted with the new plugin (`-O1` and all
six matrix profiles) and every report re-captured and diffed.

**86 of the 113 are byte-identical**, `h2r compare` over all six profiles
among them. The 27 that are not:

| what | diff |
|---|---|
| `text`, `text --heads` (×7 dumps) | 17 lines each: the header paragraph, and three labels that said "level 6" / "type-string" / "a rendered type". Every count identical. |
| `text --explain` | 5,451 lines: 2,598 `X1-LIST-TYPE` and 61 `X0-ELEM-TYPE` evidence notes, 59 `type-string only` → `type only` labels, and the 17 above. |
| `text --json` | the same 2,659 notes, plus 58 `element_type_evidence` values renamed `TypeStringOnly` → `TypeOnly`. |
| `laziness --json` | 5,395 `unique` strings (below). Identical field-for-field once `unique` is removed. |
| `parsec --json` | each region's edge *list order*, and `binder_unique` (below). Every region's edge multiset is identical modulo that field, and the accounting is identical. |
| `parsec` on B, C, D | one line each: the `e.g.` exemplar of a reject-reason histogram. **Pre-existing nondeterminism**, reproduced by running the *same* binary on the *same* dump twice; the counts never move. Not introduced here and not fixed here. |
| `matrix/<P>/provenance` (×6) | `date`, `repo_head`, `repo_dirty_inputs`, `plugin_sha256`, `binary_sha256`. `stripped_source_sha256`, `flags`, `ghc`, `cabal`, `modules` and `binary_version` are unchanged, and the module lists are identical. |

**GHC renumbered the uniques, and nothing noticed.** Re-extracting with the
new plugin shifted GHC's unique supply: **98,135 of the 116,340 binder
uniques changed.** Compared field by field with uniques and the new type
index excluded, the two dumps differ in **2,124 strings in total, all of
them pretty-printed demand signatures that embed a unique** (`{a8Ia->M!P(L)
…}` → `{a8Jr->M!P(L) …}`) — the Core is otherwise identical node for node,
which is why every node id in every report is unchanged. That 98,135
uniques can move without a single census number moving is the strongest
statement available that no analysis keys by one; it is what
[M2.1](#scoping-uniques-are-not-unique) set out to make true and what this
milestone finished.

**And the two element-type readings agree.** `rendered_element` is kept
beside `structured_element`, and `elem_readings_disagree` compares them
flow by flow. Over all **seven dumps — 11,818 / 11,818 / 12,146 / 13,647 /
23,886 / 22,688 / 22,807 list flows — it reports 0 disagreements**: the
structured reading selects exactly the flows the string reading did. The
linkage check runs beside it: of the `Ref::Global` occurrences (44,992 on
`-O1`, 99,824 on D), **0** carry `isGlobal = false` and **0** are missing
from the stable-name id table, on every dump.

`cargo test` (159 — eight new: the `Ty` helpers, `alpha_eq`, the type
table's forward-reference refusal, the format-4 rejection, and three that
make a fixture's rendering and its structure disagree on purpose to show
which one a rule reads), `cargo clippy --all-targets` (0 warnings) and
`cargo fmt --check` are clean.

## M2.4b — the closed-world class-op census

Two questions are easy to run together and must not be: *which instance and
which method can run at this site?* and *can the dictionary disappear?*
**A known method target is not a removable dictionary.** This milestone
answers only the first. What bears on the second — is the dictionary
forced, could it be bottom, is it also used as an ordinary value — is
recorded as an *observation*, with no verdict attached; the verdict is
M2.4c's.

`h2r classops` takes as its population **every application spine whose head
is a class-op selector**, decided by GHC's own `isClassOpId` through the one
signature lookup (`K0-CLASSOP-SITE`), never by a name. On `-O1` that is
**565 sites**. Superclass selectors (`$p1Ord`) *are* class ops, so
superclass selection is both a member of the population and a dictionary
source, and one mechanism handles both.

The [residual-laziness census](#m2--who-receives-the-lazy-arguments) leaves
**294** class-op *argument* sites in the unresolved tier. Each is an
argument of exactly one population site, and the mapping is asserted: **294
of 294 map**, on all seven dumps. The other 271 population sites are
class-op applications the census never counted, because none of their
arguments is a non-trivial computation in a lazy position.

### The answer

| | `-O1` | |
|---|---:|---:|
| population — class-op application sites | **565** | |
| … `Exact(target)` | **0** | 0% |
| … `FiniteSet(targets)` | **0** | 0% |
| … `Unresolved` | **565** | 100% |
| … partially-applied selectors (the selector is the value) | 0 | |

`population = Exact + FiniteSet + Unresolved` is asserted, and so is the
294 mapping.

**Not one residual class-op site in ShellCheck has a statically known
dictionary.** That is the finding, and it is not a weakness of the walk:
the walk resolves dfuns, dfuns applied to argument dictionaries, superclass
chains, dictionary-constructor fields read back by a `case`, lexical
aliases and the parameters of local functions (its nine unit tests exercise
each, and produce `Exact` and `FiniteSet(2)` where a dictionary is
statically known). The reason it finds none here is that GHC has **already
taken every such site**: a selector applied to a visible dfun is exactly
what the simplifier rewrites to the instance method. What survives
optimisation is, by construction, only the dispatch whose dictionary is a
*run-time* parameter. Of the 565 dictionary arguments, 499 are lambda
parameters, 41 are superclass selections applied to one, 19 are bound by a
`case` alternative and 6 are `let`-bound superclass selections — **none is
a dfun**.

| by class | sites | | by class | sites |
|---|---:|---|---|---:|
| Applicative | 191 | | Monoid | 55 |
| Show | 91 | | Eq | 54 |
| Monad | 69 | | Functor | 38 |
| Exception | 17 | | Ord | 11 |
| Ranged (ShellCheck's own) | 11 | | MonadState | 9 |
| MonadReader | 7 | | MonadWriter | 7 |
| Num | 2 | | Semigroup | 2 |
| Foldable | 1 | | | |

Every site's class is identified, and 524 of the 565 from the *structured
type* of the dictionary argument (`K2-DICT-TYPE`, level 4) rather than from
any name; the remaining 41 are superclass selections, whose class the
selector's own name gives (level 1) and whose table entry the dump's
`repArity` checks.

### Why each site is unresolved

| | reason | representative |
|---:|---|---|
| 252 | the dictionary is a parameter of an **exported** function — callers outside this module cannot be enumerated | `ShellCheck.AST` node 3465 |
| 280 | the dictionary is a parameter of an instance method (`$ctraverse` 220, `$cfoldMap` 53, `$cfoldMap'` 3, `$celem`/`$cmaximum`/`$cminimum`/`$csum`/`$cproduct` 1 each, `$fTraversableInnerToken` 2) — a function **reached only through dispatch**: its callers are the class-op sites that select it | `ShellCheck.AST` node 6559 |
| 17 | the dictionary is read back from a **constructor field** (`SomeException`'s existential `Exception` dictionary, 11 in `Main` + 6 in `Paths_ShellCheck`) | `Main` node 659 |
| 7 | the **instance method is not in the dump**: mtl's `$fMonadStatesReaderT` (5), `$fMonadStatesParsecT` (2) — the instance is known exactly, its body is in another package with no unfolding | `ShellCheck.Parser` node 128333 |
| 6 | the dictionary expression reached is not a constructor application (the mtl chains above, at a second step) | `ShellCheck.Parser` node 138963 |

The second row is the one that says what a closed-world specialiser would
have to do. An instance method's dictionary parameter is bound at
*dispatch* time, by whichever dictionary the selector site used; enumerating
it means propagating dictionaries **forward through dispatch**, and that is
only sound if no dictionary of that class escapes into code the dump cannot
see. It does — 166 of the 565 sites have a dictionary that is also used as
an ordinary value — so the union is not claimed here. Nothing is guessed.

### Dictionary sources in the closed world

| kind | `-O1` |
|---|---:|
| dfun — a top-level binding whose type is a class constraint | 259 |
| dfun applied at a use site, building an instance dictionary | 609 |
| dictionary-constructor application (`C:Show f g h`) | 10 |
| superclass selection (`$p…`) | 72 |
| local (`let`) dictionary binding | 206 |
| dictionary parameter of a function | 216 |
| dictionary bound by a `case` alternative | 35 |
| … of all of these, admitted on their *name* because the class table does not carry their class | 838 |
| … whose binding is not in the dump at all | 681 |

The closed world is every module in the dump, indexed by stable name, so a
dfun defined in `ShellCheck.AST` is followed from `ShellCheck.Analytics`;
`--module` and `--class` restrict the *report*, never the resolution.

### The class table, and why there is one

One thing the dump cannot answer: **which field of a dictionary a selector
reads**. Class-op selectors are globals, and format 5 carries no type and no
unfolding for a global, so neither the selector's type (`C a => …`) nor its
`case d of C:C … m … -> m` body is available. The field order is therefore
asserted per class — 17 classes, in the style of the [list
axioms](#the-axiom-layer) — and **every use of an entry is cross-checked
against that dictionary constructor's own `repArity` in the dump**. Over all
seven dumps the check reports **0 disagreements**, and **0** sites fall
outside the table.

### The rules

| rule | level | what it says |
|---|---:|---|
| `K0-CLASSOP-SITE` | 5 | the spine head is a class-op selector — GHC's `isClassOpId` |
| `K1-DICT-ARG` | 2 | the first value argument of a class-op application is the dictionary |
| `K2-DICT-TYPE` | 4 | the class is the head `TyCon` of the dictionary's structured type |
| `K3-CLASS-TABLE` | 5 | the method's field index, checked against `repArity` |
| `K4-SUPERCLASS-SEL` | 1 | `$pN<Class>` selects superclass field N-1 |
| `K5-ALIAS` | 3 | a `let`-/top-bound dictionary is followed to its right-hand side |
| `K6-DFUN` | 3 | a global dictionary is followed to its binding in the closed world |
| `K7-DICT-CON` | 2 | a saturated dictionary-constructor application is a dictionary |
| `K8-PARAM-UNION` | 3 | a local function's dictionary parameter is the union over its call sites |
| `K9-METHOD-FIELD` | 2 | the method target is the dictionary's field at the method's index |
| `K10-FORCED` | 5 | a class-op application forces its dictionary (strict field selection) |
| `K11-DICT-ESCAPES` | 3 | the dictionary is also used as an ordinary value |
| `K12-PARTIAL` | 2 | the selector is applied to no value argument: the selector is the value |

### Dictionary-evaluation observations (no verdict)

| | `-O1` |
|---|---:|
| the selector application forces its dictionary (`K10`) | 565 |
| the dictionary is a variable GHC records as strict at its binder | 247 |
| … with no strictness recorded: nothing here says it is not bottom | 277 |
| the dictionary is also used as an ordinary value (`K11`) | 166 |

The first row is every site, and it is the fact M2.4c has to answer to: a
class op is a strict field selection, so a site that dispatches on a
dictionary also *evaluates* it. Whether that matters — whether the
dictionary can be erased anyway — is the next milestone's question.

### Across the flag matrix

| | A `-O1` | B `-O2` | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| class-op sites (population) | 565 | 587 | 595 | 595 | 595 | 596 |
| … resolved to a target | 0 | 0 | 0 | 0 | 0 | 0 |
| census sites mapped 1:1 | 294/294 | 305/305 | 314/314 | 314/314 | 314/314 | 314/314 |
| class-table disagreements | 0 | 0 | 0 | 0 | 0 | 0 |
| classes outside the table | 0 | 0 | 0 | 0 | 0 | 0 |
| dfun bindings | 259 | 259 | 271 | 282 | 282 | 282 |
| dfun applications | 609 | 646 | 639 | 558 | 558 | 564 |

### The gate

Every earlier report — `laziness`, `parsec`, `tuples`, `tuples --verify`,
`fields`, `lists`, `text`, `verify-rep` — is **byte-identical** before and
after this milestone: the census adds a population, it changes no existing
one. `cargo test` (**172** — thirteen new: a selector on a known dfun, a
dfun applied to an argument dictionary, a dfun parameter appearing in a
field, a superclass selection followed to its superclass, a class
cross-check that refuses, a two-call-site union, an exported function's
parameter, a dictionary read from a constructor field, a partially applied
selector, a dictionary also used as a value, the source enumeration, a dfun
followed across modules, and an imported dfun that names its instance and
refuses the method), `cargo clippy --all-targets` (0 warnings) and `cargo
fmt --check` are clean.

Aggressive specialisation (D–F) does not resolve a single one, which is the
same finding as the flag matrix's: GHC's specialiser has already taken
everything it can take, and the residue is dispatch on a run-time
dictionary. Closed-world specialisation is ours to do, and this census says
exactly what it would have to prove: the dictionaries reaching 252 exported
functions' parameters, and the dictionaries that reach 280 instance-method
parameters through dispatch.

## M2.4c — whole-program dictionary flow, and whether the dictionary can go

[M2.4b](#m24b--the-closed-world-class-op-census) answered *which method can
run here* one module at a time and found **0 of 565** sites resolved: every
dictionary was a run-time parameter. It also said what a closed-world
specialiser would have to do, and this milestone does it — and, separately,
asks the question M2.4b refused to mix in.

### The closed-world assumption, stated

The 28 modules of the dump are **the entire program**, and `Main.main` is
its only root. Nothing outside the dump calls into ShellCheck's library
modules: there is no plugin interface, no `dlopen`, and the `prop_*` corpus
— the only other importer — is what `striptests` removes from a production
build. This is `W0-CLOSED-WORLD`, and it is an **assumption**: the dump
cannot prove it. Everything in Part 1 rests on it, which is why it is
written into `dictflow.rs`'s header, into `h2r dictflow`'s first paragraph,
and here.

Under it, an exported function's dictionary parameter *does* have an
enumerable producer set: the union over **all** call sites in **all**
modules, found by stable name through the global occurrences of the
function (`W1-GLOBAL-CALLERS`) — unless the function is also used as a
value, which makes the set unenumerable exactly as
[`boundary.rs`](#m221--locally-removable-is-not-globally-composable) found
for tuples.

### Part 1 — the fixpoint

`crates/h2r-analysis/src/dictflow.rs` is a whole-program worklist over one
abstract set per dictionary parameter. Dictionary **values** are
dictionary-constructor applications, dfuns applied or not, and superclass
selections of those (`W2-DICT-VALUE`); **parameters** accumulate the union
of what reaches them across modules (`W3-PARAM-UNION`); **dispatch**
(`W4-DISPATCH`) is what makes it more than a call graph: a class-op site
with a known dictionary set selects, per dictionary, the method at the
class's field index, and where that method is a separate binding in the
dump — `$fTraversableInnerToken_$ctraverse` and its kin — the site's own
remaining arguments *are* that binding's actual arguments, so the method's
dictionary parameters are fed from the dispatch and propagation continues
through it.

The analysis is **monovariant** (`W5-MONOVARIANT`): one abstract value per
dictionary identity, one set per parameter, no calling context. It loses
precision and never soundness. Anything it cannot account for taints
(`W6-TAINT`): a `Top` set at a class-op site means *any* instance of that
class could be selected there, including one outside the dump, so every
method at that class's field index is tainted too — that is how the taint
crosses dispatch in the other direction. Budgets are stated and exceeding
one is `Unresolved`, never a guess (`W7-BUDGET`): 40 rounds, 32
dictionaries per set, 4,000 expression steps per evaluation, 8 nested field
reads. **On all seven dumps the fixpoint settles in 7 rounds and no budget
is hit.**

### What it found

| | per module (M2.4b) | whole program |
|---|---:|---:|
| class-op sites (population) | 565 | 565 |
| … `Exact(target)` | **0** | **7** |
| … `FiniteSet(targets)` | 0 | 0 |
| … `Unresolved` | 565 | 558 |

`population = Exact + FiniteSet + Unresolved` is asserted. Seven sites —
all of `Ranged`, ShellCheck's own class, dispatching on
`$fRangedPositionedComment` — now have a known method. That is the whole of
the improvement in *method targets*, and stating only that would be
misleading, because the fixpoint did far more than seven sites' worth of
work:

> **the dictionary set is bounded at 118 of the 565 sites** (74 reach
> exactly one instance, 44 reach exactly two) **and at 106 of the 216
> dictionary parameters.**

`ShellCheck.Parser`'s `parseScript`, `readArray`, `readNewlineList`,
`tryWordToken` — 36 dictionary parameters in all — resolve their `$dMonad` to exactly
`{$fMonadIdentity, $fMonadIO}` — the two monads ShellCheck really runs the
parser in, proved by enumerating every caller in the program. The *method*
stays `Unresolved` only because `$fMonadIdentity` and `$fMonadIO` are
`base`'s, and their method bodies are not in the dump. Per the milestone's
own rule, the target is the instance method's stable name only when GHC
exported it as a separate binding referenced somewhere in the dump;
otherwise `Unresolved(instance-method-not-in-the-dump)`, with the instance
named. Nothing is guessed.

### Why the other 558 are unresolved

| | reason | representative |
|---:|---|---|
| 413 | the function holding the dictionary parameter is **unreachable**: it has no occurrence anywhere in the closed world, so under `W0` nothing can name it and the site never runs | `ShellCheck.AST` node 3465 (`doAnalysis`) |
| 53 | `instance-method-not-in-the-dump($fMonoidDual)` — `$cfoldMap`'s `Monoid` is `Dual (Endo …)`, `base`'s | `ShellCheck.AST` node 27756 |
| 48 | `instance-method-not-in-the-dump($fMonadIO)` | `ShellCheck.Checker` node 49 |
| 17 | the dictionary is read from a **non-dictionary constructor field** (`SomeException`'s existential) | `Main` node 659 |
| 9 | the method sits in a dictionary field **no class-op site in the program ever selects**: it is never dispatched | `ShellCheck.AST` node 6501 |
| 7 + 5 + 1 | mtl's `$fMonadStatesParsecT`, `$fMonadStatesReaderT`, `$fMonadReaderrParsecT` — instance known, body in another package | `ShellCheck.Parser` node 138695 |
| 4 | the dictionary is **returned by a call the dump cannot see** | `ShellCheck.AnalyzerLib` node 734 |
| 1 | dispatched from a site whose own dictionary is unknown | `ShellCheck.AST` node 27609 |

The first row is the milestone's most uncomfortable finding and it is not
an artefact. **922 of the 2,235 top-level bindings in the dump are never
referenced anywhere in it** — `doAnalysis` occurs exactly once in all 28
modules, as its own binder. They are ShellCheck's exported library API,
whose only other consumers are the `prop_*` corpus and downstream packages,
neither of which is in a production build. Under `W0` they are dead code,
and 413 of the 565 class-op sites live in them. M2.4b called these
"parameter of an exported function"; the closed world says something
sharper and less flattering: most of that population is not reachable at
all.

The taint over the 216 dictionary parameters, for comparison: 90
unreachable, 12 never dispatched, 4 from a call the dump cannot see, 3 a
function used as a value, 1 dispatch-tainted — and 106 bounded.

### Part 2 — erasure agreement, a separate proof object

> **A KNOWN METHOD TARGET IS NOT A REMOVABLE DICTIONARY.**

This is the exact analogue of M2.2.1's *locally removable is not globally
composable*. Part 1 says which method runs and says **nothing whatever**
about whether the dictionary itself can disappear: a dictionary with one
known instance may still be forced where erasure would move divergence,
stored in a constructor, or handed to a callee the dump cannot see. The
verdicts below come from facts recorded **separately** from Part 1, and the
two are crossed rather than collapsed.

* **Evaluation** (`E1-TOTAL`). A class-op application is a strict field
  selection, so it forces its dictionary; replacing `classOp d x` by
  `method x` changes behaviour only if `d` could be ⊥. A
  dictionary-constructor or dfun application *is* a value, so a boundary
  all of whose producers are such values is total and erasure moves no
  divergence; a parameter GHC records as strict is forced at entry already.
* **Representation agreement** (`E2-AGREE`, `E3-CLONE`). Every producer at
  every boundary a dictionary crosses must request the same erased form —
  the same instance. One instance ⇒ `Erasable`. Several, at a function that
  is never used as a value (which is what kept the set finite), ⇒
  `ErasableWithClone`, one clone per instance, **counted, never made**.
* **Escape** (`E4-ESCAPE`). Used as an ordinary value — stored, passed to
  an imported callee, handed to a non-dictionary parameter — ⇒ `Preserve`,
  with the holder named.

| verdict | dictionary values | dictionary parameters |
|---|---:|---:|
| `Erasable` | 102 | 36 |
| `ErasableWithClone` | 0 | 4 |
| `Preserve` | 89 | 84 |
| `Unresolved` | 0 | 92 |
| **total** | **191** | **216** |

`values = Erasable + WithClone + Preserve + Unresolved` and the same for
parameters are both asserted. The four `WithClone` parameters cost **8**
clones between them (two instances each); no value needs one, a value being
one instance by construction.

The dominant reasons: 133 `passed to a callee outside the dump` (a `base`
dfun handed to a `base` function), 80 `function-is-unreachable-in-the-closed-world`,
40 `used as an ordinary value`, 7 `method-is-never-dispatched`, 4
`dictionary-returned-by-a-call-the-dump-cannot-see`, 1 dispatch-tainted.

### The two questions, crossed

The 3×4 matrix is asserted to sum to the population:

| target ⟍ dictionary | `Erasable` | `ErasableWithClone` | `Preserve` | `Unresolved` |
|---|---:|---:|---:|---:|
| `Exact` | 7 | 0 | **0** | 0 |
| `FiniteSet` | 0 | 0 | **0** | 0 |
| `Unresolved` | 10 | 0 | 154 | 394 |

The bolded cells are the population this milestone exists to keep separate:
a site whose method is known but whose dictionary must survive anyway — a
dispatch on a preserved dictionary. On `-O1` it is **0**, which is a
result, not an absence: the seven resolved sites all dispatch on a
dictionary that nothing else holds. The other direction is populated and
just as instructive: **10 sites whose dictionary is `Erasable` still have
no known method target**, because the instance is `base`'s and its body is
not here. Erasability and dispatch resolution are independent, and the
matrix shows it in both directions.

### Across the flag matrix

| | A `-O1` | B `-O2` | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| class-op sites | 565 | 587 | 595 | 595 | 595 | 596 |
| … `Exact` | 7 | 7 | 7 | 0 | 0 | 0 |
| sites with a bounded dictionary | 118 | 138 | 140 | 65 | 65 | 65 |
| parameters bounded / total | 106/216 | 98/210 | 109/222 | 64/223 | 64/223 | 72/231 |
| values `Erasable` / total | 102/191 | 102/191 | 101/191 | 139/238 | 139/238 | 139/238 |
| parameters `Erasable` | 36 | 28 | 34 | 28 | 28 | 28 |
| clones a `WithClone` would cost | 8 | 6 | 8 | 12 | 12 | 12 |
| fixpoint rounds | 7 | 7 | 7 | 7 | 7 | 7 |

Aggressive specialisation (D–F) makes the whole-program answer *worse*, not
better: it duplicates dictionaries into more inline constructor
applications (238 values rather than 191) and loses the seven `Ranged`
targets. Specialising harder does not help a closed-world analysis; it
scatters the evidence.

### A hazard the milestone had to fix

A top-level binder GHC has not externalised carries an **internal** name —
`$_in$$ctraverse`, `$_sys$$fTraversableInnerToken` — and those are **not
unique**: `ShellCheck.AST` alone has three distinct top-level bindings whose
name is `$_sys$$fTraversableInnerToken`. [M2.4a](#m24a--stable-global-identity-and-structured-types)'s
bijection is over the *global Ids a module refers to*, which are external by
construction; it says nothing about a module's own un-externalised binders.
So `dictflow.rs` keys every dictionary identity by
`Module#node` of its constructor application, keeps the name for the report
only, and puts nothing with an internal name into the cross-module linkage
table. The check that this is enough is a count: **0 global `Var`
occurrences in the whole dump carry an internal name**, so nothing can refer
to one from another module anyway. `classops.rs`'s `World` has the same
latent collision and is not reachable through it for the same reason; it was
left alone rather than changed under a byte-identity gate. (M2.4c′ closes
it, and finds that the "external ⇒ unique" test was itself too weak — see
[Correction (M2.4c′)](#correction-m24c--totality-is-not-the-same-fact-as-identity).)

### The CLI

`h2r classops` gains `--whole-program` (**on by default**), which appends
the re-derivation and the erasure section to the M2.4b report, and
`--per-module`, which reproduces M2.4b exactly. `h2r dictflow <dir>
[--explain] [--json]` prints the closed-world assumption, the fixpoint, both
tables and the 3×4 matrix (M2.4c′ adds a fifth verdict column, the totality
table and the owner-level clone plan).

### The gate

Every earlier report — `laziness`, `parsec`, `tuples` (plus `--verify`),
`fields`, `lists`, `text`, `verify-rep` — is **byte-identical** before and
after, and so is `h2r classops --per-module` (plus `--explain` and `--json`)
against M2.4b's `h2r classops`. `cargo test` (**181** — nine new: one caller
in the closed world giving `Exact`, two callers in two modules giving
`FiniteSet(2)`, a third module using the function as a value making it
unenumerable, dispatch feeding an instance method's own dictionary
parameter, a tainted producer unresolved downstream, the set budget
exceeded, an `Exact` target on an escaping dictionary `Preserve`d, two
instances costing one clone each, and two dictionaries sharing an internal
name staying distinct), `cargo clippy --all-targets` (0 warnings) and
`cargo fmt --check` are clean.

### What remains, stated rather than hidden

* The closed world is an **assumption**. If ShellCheck is built as a
  library for someone else, 413 of the 565 sites stop being dead and the
  answer changes.
* The analysis is monovariant: a dfun applied to two different argument
  dictionaries has one identity here. A call-string or per-instantiation
  analysis would split some of the 44 two-instance sites.
* `Unresolved` for a parameter is not a proof that it *cannot* be erased,
  only that this proof object declines to say so.
* A dictionary reaching an imported callee is `Preserve`d on the strength
  of the callee being outside the dump; a hand-written Rust replacement for
  that callee could take the erased form instead, and 133 of the 265
  non-`Erasable` verdicts are that case. The lowering, not this analysis,
  decides those.

### Correction (M2.4c′) — totality is not the same fact as identity

The `Part 2` verdicts above were computed with a bug the project owner's
review of `96e4733` found. `erasure()` decided `Erasable` from
`!x.set.is_top()` and the instance count — but `eval_nested()` is a
**MAY**-analysis of which dictionary values an expression can produce: for a
`case` it walks the alternatives' right-hand sides and ignores the
scrutinee entirely. "Bounded dictionary identity" had silently become "the
producer is total". The counterexample:

```haskell
f d    = classOp d x
main   = f (case bottom of A -> knownDict; B -> knownDict)
```

The set is exactly `{knownDict}` — the old code says `Erasable` — but the
selector forces `d` (`K10`), and deleting the dictionary computation
deletes the divergence. `known_strict` was recorded on the parameter and
copied to the report and **never consulted**; and consulting it would not
have helped, because strictness at entry is not permission to drop the
force: if the parameter disappears, its entry force still has to happen
somewhere.

#### An independent totality domain

`Totality` is now its own lattice, propagated by its own transfer in its own
fixpoint, sharing the settled dictionary sets **only** to resolve dispatch.
The chain is `ProvenTotal < MustPreserveForce < Unknown`, bottom
`ProvenTotal`, join `max`.

| rule | level | what it says |
|---|---:|---|
| `E6-TOTALITY-VALUE` | 2 | a saturated dictionary-constructor application, a dfun applied or not, and a superclass selection out of a `ProvenTotal` dictionary are values ⇒ `ProvenTotal` |
| `E6-TOTALITY-CASE` | 5 | a `case` whose scrutinee is not *already evaluated* ⇒ `MustPreserveForce`, **even when every alternative yields the same dictionary** |
| `E6-TOTALITY-LET` | 3 | a let- or top-bound dictionary inherits its right-hand side's totality |
| `E6-TOTALITY-PARAM` | 3 | a parameter is the join over the totality of every producer that reaches it |
| `E6-TOTALITY-UNKNOWN` | 3 | through a call the dump cannot see, a non-dictionary constructor field, a higher-order parameter, or a budget ⇒ `Unknown` |
| `E6-TOTALITY-OBLIGATION` | 5 | `Erasable` requires `ProvenTotal`, **or** a named `ForceObligation`; strictness is evidence, never a verdict |
| `E7-OWNER-CLONES` | 3 | a function's clones are its distinct call-site assignment tuples |

*Already evaluated* is deliberately narrow: a value (a literal, a lambda, a
saturated constructor application, a dfun), a variable bound by an
enclosing `case`, or a variable GHC marks strict **and** that an enclosing
`case` on that same binder dominates. Strict-at-entry alone does not
qualify — GHC's promise is that the force happens, not that it has happened
*here*.

*Corrected by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found):
"a variable bound by an enclosing `case`" was still too wide. It admitted
every **alternative** binder, and matching an outer constructor forces the
constructor, not its fields — the binder of a lazy field is an unevaluated
thunk. Only the scrutinee binder and the binder of a field GHC marks strict
qualify.*

The verdict is then: `ProvenTotal` ⇒ identity decides as before;
`MustPreserveForce` ⇒ `ErasableWithObligation { at, what }`, naming the node
whose evaluation erasure would delete and the scrutinee that must still be
evaluated, or `Preserve(erasure-would-delete-a-force)` when no obligation
can be expressed; `Unknown` ⇒
`Preserve(totality-unknown-erasure-could-move-divergence)`.

*Amended by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found):
`ErasableWithObligation` carries the whole obligation **set**. The join kept
one witness, so a dictionary standing behind two distinct forces was erased
against one of them.*

#### Erasure tables, before → after

| verdict | values before | values after | parameters before | parameters after |
|---|---:|---:|---:|---:|
| `Erasable` | 102 | 102 | 36 | 36 |
| `ErasableWithObligation` | — | 0 | — | 0 |
| `ErasableWithClone` | 0 | 0 | 4 | 4 |
| `Preserve` | 89 | 89 | 84 | 84 |
| `Unresolved` | 0 | 0 | 92 | 92 |
| **total** | **191** | **191** | **216** | **216** |

**No verdict moved, and that is a result rather than a no-op.** The totality
domain answers, over the 216 dictionary parameters: **118 `ProvenTotal`, 0
`MustPreserveForce`, 98 `Unknown`** (asserted to sum to 216). The 40
erasable parameters are all `ProvenTotal`; the 98 `Unknown` ones were
already `Preserve` or `Unresolved` on escape or on a `Top` set. The reason
`MustPreserveForce` is **0** is stronger than "nothing changed": an
instrumented run shows the walk reaches **no `case` node at all** on any
dictionary path in the dump — GHC's `-O1` floats every dictionary out of
every scrutinee. The old code was unsound *in principle* and, on this
program, accidentally right. It is now right on purpose, and the
counterexample is a unit test.

Named force obligations carried: **0**.

The matrix gains a column and no cell moves:

| target ⟍ dictionary | `Erasable` | `ErasableWithObligation` | `ErasableWithClone` | `Preserve` | `Unresolved` |
|---|---:|---:|---:|---:|---:|
| `Exact` | 7 | 0 | 0 | **0** | 0 |
| `FiniteSet` | 0 | 0 | 0 | **0** | 0 |
| `Unresolved` | 10 | 0 | 0 | 154 | 394 |

#### Clone planning is per owner, not per parameter

`ErasableWithClone(n)` is a per-**parameter** cardinality and `Accounting`
used to **sum** it: 4 parameters × 2 instances = **8 clones**. That is not
a clone plan. A function needs one specialisation per *distinct assignment
tuple actually seen at its call sites* — one tuple per call site,
deduplicated — which is neither the sum nor the product of the
per-parameter cardinalities. The cardinalities stay, as evidence.

On `-O1` all four `WithClone` parameters belong to four different
single-parameter functions, and each has exactly **one** call site:

| module | function | dictionary parameters | cardinalities | tuples seen | clones |
|---|---|---:|---|---:|---:|
| `ShellCheck.Parser` | `allspacingOrFail` | 1 | `[2]` | 1 | 1 |
| `ShellCheck.Parser` | `commentWarning` | 1 | `[2]` | 1 | 1 |
| `ShellCheck.Parser` | `readNormalLiteral` | 1 | `[2]` | 1 | 1 |
| `ShellCheck.Parser` | `splitBy` | 1 | `[2]` | 1 | 1 |
| | | | | **total** | **8 → 4** |

The "2 instances" never meant two call sites: it is one call site whose
dictionary argument is itself a two-instance parameter, which the
monovariant analysis (`W5-MONOVARIANT`) can only give as a *set*. Such a
tuple is counted as the one call site it is, so **4 is a lower bound** — the
true figure is between 4 and 8 and only a call-string analysis can close
it. Every set-valued tuple is flagged in the report rather than smoothed
over.

`-O2` and the specialising profiles make the same point more loudly: in
D–F the four parameters collapse onto **two** two-parameter functions,
`parseProblemAtWithEnd` and `shouldIgnoreCode`, each with cardinalities
`[3, 3]` — a sum of 12 and a product of 9 — whose call sites use only 3 and
4 distinct tuples: **12 → 7**.

| clone plan | A `-O1` | B `-O2` | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| per-parameter cardinality sum (the old number) | 8 | 6 | 8 | 12 | 12 | 12 |
| owner-level clones (distinct tuples) | **4** | **3** | **4** | **7** | **7** | **7** |
| owning functions | 4 | 3 | 4 | 2 | 2 | 2 |
| parameters `ProvenTotal` / `MustPreserveForce` / `Unknown` | 118/0/98 | 110/0/100 | 121/0/101 | 77/0/146 | 77/0/146 | 85/0/146 |

#### Identity cleanups

* `classops::World::new` keyed `tops` by `b.name` with `or_insert`, which
  admits internal, non-unique names exactly as the hazard above describes.
  It now admits only external stable names, as `dictflow::Program` does,
  and **asserts there is no collision**. Doing so found a second defect:
  `is_external_name` split `$_sys$poly_$j` into unit `_sys`, module `poly_`,
  occurrence `$j` and passed it as external. GHC's `nameStableString`
  renders a non-external name as `$_sys$<occ>` or `$_in$<occ>` with no unit
  and no module, and when that `<occ>` itself contains a `$` — GHC's
  worker/wrapper and join-point names are full of them — the three-way
  split is fooled. Two distinct top-level bindings of the dump claim
  `$_sys$poly_$j`. Rejecting the two pseudo-units makes *external ⇒ unique*
  true rather than nearly true, in `dictflow`, `higher` and now `classops`
  alike. **Collisions asserted: 0.** No target-enumeration number moved.
* The doc comments on `scope.rs` and on `Ref::Global` still said a GHC
  *unique* is the key into the imported-id table. It is not, and has not
  been since dump format 5: the key is the stable name. Corrected.
* `KVar`/`KAll` interning in the plugin and free-type-variable comparison in
  `Ty::alpha_eq` **still rest on GHC uniques**. `alpha_eq` alpha-maps
  *bound* type variables but compares *free* ones by unique, and free type
  variables are not scope-identified: format 5 carries no lexical identity
  for a type variable, and a unique is not unique in an optimised dump. So
  `alpha_eq` must not be used for any free-tyvar-sensitive proof until a
  later format carries lexical type-variable identity; every current caller
  compares closed or same-scope types. This is now stated on the function.
* The "**922 unreachable top-level bindings**" above are the **zero-reference
  subset** under `W0` — bindings with no occurrence anywhere in the dump.
  That is a valid *dead* subset (nothing can name them, so they cannot run),
  but it is **not** a `Main.main`-rooted transitive reachability set: a
  binding referenced only by another unreachable binding is not in it. M3
  needs the rooted set, and will have to compute it.

#### The gate for this correction

Every report is byte-identical before and after except `dictflow` and the
erasure section of `classops` — `stats`, `higher`, `tuples`, `fields`,
`lists`, `text`, `verify-rep`, `laziness` and `compare`, with `--explain`
and `--json`, on `core-json` and on all six matrix profiles. The
target-enumeration half of `dictflow` (Part 1, in full) and of `classops`
is byte-identical too; the `classops` diff is exactly its erasure block, six
lines becoming ten. `cargo test` is **201** (six new: the `case`-on-⊥
counterexample, an unknown-call producer, a dfun application, a strict
parameter with total producers, a strict parameter with one forced
producer, and the owner-level clone plan), clippy is 0 and `cargo fmt
--check` is clean.

One pre-existing defect surfaced and is **not** fixed here: `h2r parsec
--explain` and `h2r parsec --json` are **nondeterministic run to run** —
two consecutive runs of the same binary on the same input differ in the
order of the per-role edge lines. The multiset of lines, and `h2r parsec`
itself, are stable; the ordering comes from a `HashMap` iteration in the
report. It predates this milestone and is unrelated to it, but it means
those two outputs cannot carry a byte-identity gate until they are sorted.

## M2.4d — higher-order representation agreement

M2.2.1 refused 67 tuple flows because the **closure** that returns the tuple
is handed to a local callee's parameter: rewriting the tuple away changes
that parameter's type, and the flow does not see the other closures that
arrive there. That refusal is not a tuple problem. A formal parameter is one
slot and one representation, and a closure's representation is its *arity
plus its captured environment*, so the question "can this slot be one
representation" has to be asked of every function-valued slot in the
program, independently of any flow. This milestone asks it. The 67 are read
back out of the answer at the end, as feedback; **no existing verdict
changes**.

### The population, by type and nothing else

Three kinds of function-valued boundary, each decided by the structured type
(`H1-FUNCTION-TYPED`, GHC type identity — a `FunTy`, or a `ForAllTy` over
one), never by a name and never by a rendering:

| kind | what it is | producers are |
|---|---|---|
| **parameter** | a value lambda binder of function type | the argument at that index of every call site of its function, in every module |
| **field** | a constructor field at which some match in the closed world binds a function-typed binder | the argument at that index of every saturated application of that constructor |
| **return** | a function whose result, after its manifest value parameters, is still a function | every syntactic return point of its body, at the deepest lambda depth |

On the `-O1` dump that is **5,574 boundaries**: 5,464 parameters, 35 fields,
75 returns.

Producers are enumerated **from the IR's own occurrences**, whole-program by
stable name under `H0-CLOSED-WORLD` (`H2-PRODUCERS`) — the same discipline
[`boundary.rs`](#composing-the-views-can-all-1453-be-applied-at-once) and
[M2.4c](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go)
use, and for the same reason: a function used as a value, or one nothing in
the closed world names, has no enumerable call-site set and the slot is
refused rather than guessed. A producer that is itself a boundary — the
parameter of a parameter, the result of a known saturated call — contributes
*that* boundary's set, in a monovariant worklist fixpoint with the same
budgets (`H3-PROPAGATE`). It settles in **10 rounds**; no budget is hit
except one set cap, below.

### The shape class, stated conservatively

Two closures can share one representation only when

* they take the **same number of further arguments**, and
* they capture the **same ordered list of types**, compared up to
  alpha-equivalence of the *structured* type

(`H4-SHAPE-CLASS`). A lambda's captures are the local binders its body reads
that it does not bind; a partial application's are the arguments it already
holds; a bare known function's are none. A producer whose environment the
closed world cannot see — a closure read back out of a constructor field, a
closure returned by a call into a library — is **opaque**, and an opaque
shape is equal to nothing, not even to another opaque shape.

Where a partial application's argument is not a variable there is no type to
read, so it gets a key unique to its node and can never merge with anything:
refusing to merge is the conservative direction.

On the `-O1` dump the producers fall into **261 distinct full class keys**.
By the printable `(arity, captures)` summary, the commonest are arity 3 with
1, 3 or 5 captures (86 / 77 / 48 boundaries carry one) — Parsec's four-way
CPS continuations, closed over the state they were built with.

### Two facts, and only then a verdict

**AN ENUMERATED PRODUCER SET IS NOT ONE REPRESENTATION.** This is the exact
analogue of M2.4c's *known method target ≠ removable dictionary*, and it is
kept apart the same way: `enumerated` and `classes` are recorded separately
on every boundary (`H11-SEPARATE`) and crossed only afterwards.

| | one class | several / none |
|---|---:|---:|
| **not enumerated** | 0 | 5,322 |
| **enumerated** | **103** | **149** |

252 boundaries have a fully accounted producer set. Of those, 103 need
exactly one representation and 149 do not — a boundary can have a perfect
enumeration of nine producers and still need nine closure types.

### The verdicts

*(The tables in this section are as M2.4d computed them. Six of these
numbers are wrong; see [Correction (M2.4d′)](#correction-m24d--sharing-is-decided-before-agreement-and-a-free-type-variable-identifies-nothing)
below for what moved and why, and note that `UniformRepresentation` is now
called `TypeShapeUniform`.)*

| kind | ExactClosure | UniformRepresentation | CloneRequired | FiniteClosureSet | Preserve | Unresolved | total |
|---|---:|---:|---:|---:|---:|---:|---:|
| parameter | 47 | 20 | 138 | 0 | 6 | 5,253 | 5,464 |
| field | 6 | 0 | 0 | 0 | 10 | 19 | 35 |
| return | 14 | 0 | 0 | 1 | 10 | 50 | 75 |
| **all** | **67** | **20** | **138** | **1** | **26** | **5,322** | **5,574** |

The population is asserted to be the six verdicts, and the per-kind rows to
sum to it, in `Accounting::check`. **418 clones** are counted over the 138
`CloneRequired` parameters — one per shape class, counted and never made,
exactly as M2.4c counts dictionary clones.

`Preserve` names its holder. The 22 largest are *a closure read back from a
constructor field*, which is precisely what one would hope: `SystemInterface`'s
three fields, `Checker`'s two, `Formatter`'s two — ShellCheck's records of
run-time behaviour really are records of run-time closures, and nothing here
pretends otherwise.

### Why the other 5,322 are unresolved

| | | |
|---:|---|---|
| 2,660 | the slot's function is used somewhere as a value, so its call sites are not an enumerable set | the same refusal `boundary.rs` and `dictflow.rs` make |
| 1,953 | the slot belongs to an **anonymous** lambda, which has no name to enumerate callers by | a lambda-lifted naming, or a call-site-directed walk |
| 413 | a call site of the function is a partial application, so the argument never lands | the partial application's own consumers |
| 227 | the function has no occurrence anywhere in the closed world: under `H0` it is dead | a non-answer, but a different one |
| 44 | the body's lambda chain and the binder's type disagree about the return | refused rather than picked |
| 19 | a closure arrives from a higher-order parameter the analysis does not track | the propagation, once the anonymous lambdas are named |
| 5 | the constructor is never applied in the closed world | dead, like the 227 |
| 1 | the producer set exceeded the 32-entry budget (`CommandCheck` field 1) | a larger budget, or a per-caller analysis |

The 2,660 and the 1,953 are one shape between them: `ShellCheck.Parser` is
CPS, its continuations are anonymous lambdas passed as values, and a
higher-order analysis that wants them has to name them first. That is
[M2.4e](#m24e--the-41-residual-parsec-continuation-edges)'s ground, and this
milestone deliberately does not guess at it.

### Feeding the proof back — nothing is reclassified

Each section below is an **additional column** beside a residual M2.2.1 or
M2.1 already recorded. Every fate and every tier stands exactly as it was;
`could be reclassified` counts what a *later* pass could act on, and this
one does not.

**(a) the 67 `closure-returning-the-tuple-is-passed-into-a-parameter` flows**
land on the callee's function-typed parameters, chosen by the callee's own
binder types (`H13-LANDING`):

| | | |
|---:|---|---|
| 31 | `CloneRequired` | the other closures at the slot disagree; a clone would carry it |
| 22 | no boundary | the callee has no function-typed parameter at all — the closure lands on a slot whose type is instantiated out of sight |
| 13 | `UniformRepresentation` | one representation already serves the slot |
| 1 | `ExactClosure` | the flow's own closure is the only one there |

**14 of the 67 could be reclassified by a later pass** (the 13 uniform plus
the 1 exact): their receiving parameter is *already* one representation, so
the reason M2.2.1 refused them — "the other closures reaching the parameter
are not in this flow" — is answered. It is answered, not acted on.

**(b) the closure paths of the tuple residual:**

| population | where it lands | |
|---:|---|---|
| 187 | passed to an **imported** call | 187 × no boundary: the receiving parameter belongs to a function outside the dump. `H0` says the *program* is closed; it does not make a library's parameter a slot of it. **0** reclassifiable, and the honest answer is that the lowering of that callee decides, not this analysis. |
| 134 | **consed onto a list** | 134 × `Unresolved` on *field 0 of `(:)`* — every cons cell in the program shares one slot, and its producer set blows the budget. A closed-world list-of-closures pass has to split that slot per list, which this one deliberately does not. |
| 114 | **stored in a program constructor** | 45 `Preserve` (`SystemInterface` and kin: read back as run-time closures), 58 `Unresolved` (mostly the shared `(,)` and `(,,)` fields, the same one-slot-for-everything problem as `(:)`), 11 no boundary (no function-typed field of that constructor is ever read back). **0** reclassifiable. |

**(c) the census' unresolved higher-order sites.** The population is the
census' own: computations in lazy or unknown argument positions, still in
the unresolved tier once the Parsec proof has been fed back, and — for the
first row — outside the Parsec-shaped population, so the 10 sites the
recogniser rejected stay M2.1's residual and not this one's.

| population | | |
|---:|---|---|
| **99** fold/traversal callbacks (`f`, `go1`, `f1`, `ww`, …) | 66 `Unresolved`, 31 no boundary (the head's binder type is not a `FunTy` — a type variable instantiated out of sight), 1 `UniformRepresentation`, 1 `ExactClosure` | **2** could be reclassified |
| **22** computed closures (a `case`- or `let`-selected function) | 22 `Unresolved` — judged as expressions, since a computed closure is not a slot | **0** |

The 31 "not function-typed" is worth stating plainly: a third of the control
group is not a higher-order *representation* question at all. The callback
arrives at a slot whose type is a type variable, so there is no `FunTy` to
agree about until the polymorphism is resolved.

**(d) the 41 Parsec continuation edges** are left to M2.4e, which asks this
analysis directly rather than re-deriving it:
`higher::Higher::verdict_for(module, binder)` returns the boundary a binder
names, with its producers, its uses and its verdict.

### The rules

| | level | |
|---|---:|---|
| `H0-CLOSED-WORLD` | 5 | the dump is the whole program and `Main.main` its only root (assumption) |
| `H1-FUNCTION-TYPED` | 4 | a boundary is function-valued when its structured type is a `FunTy` |
| `H2-PRODUCERS` | 3 | producers are enumerated from the IR's occurrences over the whole closed world |
| `H3-PROPAGATE` | 3 | a producer that is a boundary contributes that boundary's set; a monovariant fixpoint |
| `H4-SHAPE-CLASS` | 2 over 4 | same arity and the same ordered capture types, up to alpha-equivalence |
| `H5-EXACT` | 3 | exactly one known producer reaches the slot |
| `H6-UNIFORM` | 3 | every producer is known and they all fall in one shape class |
| `H7-CLONE` | 3 | disagreeing producers at a local never-a-value parameter cost one clone per class |
| `H8-PRESERVE` | 3 | a run-time closure reaches the slot, or the slot is shared outside the rewrite |
| `H9-TAINT` | 3 | an unaccountable producer taints the set and the boundary is `Unresolved` |
| `H10-BUDGET` | 2 | a walk over budget is `Unresolved`, never a guess |
| `H11-SEPARATE` | 5 | an enumerated producer set is **not** one representation: separate facts |
| `H12-USES` | 3 | uses are read from the occurrences of the boundary's binders, through aliases |
| `H13-LANDING` | 4 | a residual closure flow lands on the callee's function-typed slots, by binder type |

Nothing rests on a name. Binder names appear in the report and in nothing
else, and the identity of a producer is `Module#node` (or the stable name of
an imported function) for exactly the reason M2.4c gives: an internal
top-level name is not unique.

### Uses, for completeness

A slot's uses are read from the occurrences of its binders, through local
aliases (`H12-USES`): 10,038 passed on to another slot, 4,255 stored in a
constructor, 2,882 called (3 over-applied, 6 under-applied, 236 saturated
against a slot whose arity the producers agreed on, the rest at a slot with
no agreed arity), 1,849 forced without being applied, 1,022 returned.

### Across the flag matrix

| | A (`-O1`) | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| boundaries | 5,574 | 6,347 | 8,082 | 34,094 | 31,686 | 31,701 |
| rounds | 10 | 10 | 11 | 11 | 11 | 11 |
| Exact + Uniform | 87 | 178 | 231 | 862 | 850 | 833 |
| CloneRequired | 138 | 184 | 227 | 1,006 | 996 | 1,017 |
| Preserve | 26 | 27 | 26 | 39 | 39 | 39 |

More inlining makes more anonymous lambdas and more boundaries, and the
resolved share stays roughly flat: the limit is the anonymous-lambda and
used-as-a-value populations, not the fixpoint. The accounting assertion
holds on every profile.

### The CLI

```sh
h2r higher compiler/core-json                      # the whole report
h2r higher compiler/core-json --module ShellCheck.Analytics
h2r higher compiler/core-json --explain            # every boundary, producers and uses
h2r higher compiler/core-json --boundary 36827     # just the boundaries touching one node
h2r higher compiler/core-json --json
```

### The gate

Every existing report is byte-identical: `laziness`, `parsec`, `tuples`,
`tuples --verify`, `tuples --boundaries`, `fields`, `lists`, `text`,
`verify-rep`, `classops`, `dictflow`. `cargo test` is 194 (13 new),
`cargo clippy --all-targets` 0 warnings, `cargo fmt --check` clean. No Core
is mutated, no codegen is emitted, and no GHC flag changed.

### What remains, stated rather than hidden

* **The anonymous-lambda wall.** 4,613 of the 5,322 unresolved boundaries
  are one of two things: a slot on a function used as a value (2,660) or a
  slot on an anonymous lambda (1,953). Both are the same shape — CPS Parsec
  — and both need a naming pass before a producer set exists at all. The
  numbers above are therefore a floor, not a ceiling.
* **`(:)` and `(,)` are one slot for the whole program.** Treating a
  constructor field as a single boundary is sound and useless for the
  ubiquitous constructors: 134 + 58 of the residual land there. A per-list
  or per-site field boundary would split them; this one does not.
* **The shape class is conservative on purpose** and merges less than a real
  closure-conversion would. Two lambdas that capture the same types in a
  different order, or capture through a `newtype`, are two classes here.
  Every `CloneRequired` count is therefore an upper bound on the clones.
* **An `Unresolved` is not a proof that a slot cannot be uniform**, only
  that this proof object declines to say so — the same disclaimer M2.4c
  makes about erasure.

### Correction (M2.4d′) — sharing is decided before agreement, and a free type variable identifies nothing

The M2.4d tables above were computed with six defects the project owner's
review of `3741ec5` found. Every one of them is a place where the proof
object said something stronger than its evidence.

#### 1. `H8` was decided after `H5`/`H6`

`judge()` returned `ExactClosure` as soon as one producer reached a slot,
and `TypeShapeUniform` as soon as they fell in one class, **before** it
looked at `exported` or `valued`. But how well the producers the dump can
see agree says nothing about the code outside the rewrite that names the
same slot. Constructor fields are collected with `exported: true` on
purpose — a constructor's fields are shared by every module that can build
or match it — and the -O1 run still reported **6 field `ExactClosure`s**,
which is exactly the contradiction. `H8-PRESERVE` is now decided first,
and its documentation says so.

#### 2. Two different "one representation" theorems

`Accounting` counted `enumerated && classes == 1` (103) while the method
`Verdict::one_representation()` accepted only `ExactClosure |
TypeShapeUniform` (67 + 20 = 87). Worse, `Shape::class()` mapped every
opaque producer with the same reason to the same string `opaque:<reason>`,
although the rule says an opaque shape equals **nothing, not even another
opaque one**. Two closures read back out of two different constructor
fields were being counted as one representation.

* every opaque producer now carries its own identity (the producer key), so
  `opaque:` classes never merge;
* there is now **one** statement of the theorem,
  `Boundary::one_representation()` — enumerated, one class, and no opaque
  producer — and `Accounting::one_representation` is that method and
  nothing else;
* the strictly stronger question the *rewrite* asks is named separately,
  `Verdict::rewritable_as_one()`, and is reported beside it.

| | before | after |
|---|---:|---:|
| `Accounting::one_representation` (`enumerated && classes == 1`) | 103 | — |
| `Boundary::one_representation()` (the single theorem) | — | **84** |
| `Verdict::one_representation()` / `rewritable_as_one()` | 87 | **66** |
| distinct shape classes | 261 | **353** |

#### 3. The clone count was a sum of per-parameter numbers

`CloneRequired(classes)` is a count **per parameter** and `Accounting` added
them up: 418. That is the same mistake M2.4c made and M2.4c′ fixed with
`E7-OWNER-CLONES`. Clones are now planned per **owning function**
(`H15-OWNER-CLONES`): the function-valued parameters of one function are
grouped, the *actual* call-site shape-assignment tuples are enumerated and
deduplicated, and the function's clones are its distinct tuples. The
per-slot class counts stay as evidence and are never summed. A call site
that cannot be enumerated refuses that owner's plan rather than guessing.

| | before | after |
|---|---:|---:|
| per-parameter class cardinality (evidence) | 418 | 509 |
| **clones planned** | 418 | **53** (→ **68** in [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)) |
| owning functions wanting a plan | — | 87 |
| plans refused rather than guessed | — | 66 |

The owners that need clones, largest first:

| module | function | params | call sites | tuples | clones | per-slot classes |
|---|---|---:|---:|---:|---:|---|
| ShellCheck.Parser | `k` | 4 | 4 | 4 | 4 | [1, 1, 4, 3] |
| ShellCheck.Parser | `k` | 4 | 4 | 4 | 4 | [1, 1, 4, 4] |
| ShellCheck.Analytics | `$srunNodeAnalysis` | 1 | 5 | 3 | 3 | [5] |
| ShellCheck.Analytics | `doVariableFlowAnalysis` | 2 | 3 | 3 | 3 | [3, 1] |
| ShellCheck.CFGAnalysis | `go15` | 1 | 3 | 3 | 3 † | [2] |
| ShellCheck.CFGAnalysis | `go15` | 1 | 3 | 3 | 3 † | [2] |
| ShellCheck.CFGAnalysis | `go4` | 1 | 3 | 3 | 3 † | [2] |
| ShellCheck.Checks.ShellSupport | `go1` | 1 | 3 | 3 | 3 † | [2] |
| ShellCheck.Parser | `$wpoly_k` | 1 | 4 | 3 | 3 † | [6] |
| ShellCheck.Parser | `k` | 4 | 4 | 3 | 3 | [1, 1, 4, 3] |
| ShellCheck.Parser | `k` | 4 | 4 | 3 | 3 † | [1, 1, 6, 5] |
| ShellCheck.Parser | `k` | 4 | 4 | 3 | 3 † | [1, 1, 6, 5] |
| ShellCheck.ASTLib | `$sgetLiteralStringExt` | 1 | 5 | 2 | 2 | [2] |
| ShellCheck.Analytics | `analyse` | 1 | 3 | 2 | 2 | [2] |
| ShellCheck.Parser | `$wreadIoVariable` | 3 | 2 | 2 | 2 | [2, 2, 2] |
| ShellCheck.Parser | `k` | 4 | 4 | 2 | 2 | [1, 1, 4, 3] |
| ShellCheck.Parser | `k` | 4 | 4 | 2 | 2 | [1, 1, 4, 3] |
| ShellCheck.Parser | `k` | 4 | 2 | 2 | 2 † | [3, 1, 4, 2] |
| ShellCheck.Fixer | `$srealignColumn` | 2 | 2 | 1 | 1 | [2, 2] |
| ShellCheck.Parser | `$wisFollowedBy` | 1 | 4 | 1 | 1 | [4] |

† a tuple has a **set-valued** component — one call site whose
function-valued argument is itself a multi-class parameter, which the
monovariant fixpoint can only give as a set. Those counts are **lower
bounds**, closable only by a call-string analysis.
`$srunNodeAnalysis` is the point of the correction in one row: five shape
classes at one parameter, three clones.

#### 4. Free type variables could merge two unrelated closures

`ty_key()` wrote an unbound type variable as `f<unique>`. A GHC unique is
neither module- nor scope-qualified, so two closures in two modules — or
two closures under two different `forall`s in one module — whose captures
are free variables could get the **same key** and be merged into one shape
class. (The `ty_key == alpha_eq` test is not independent evidence: both
sides use the same rule, and `Ty::alpha_eq` compares free variables by
unique too, which M2.4c′ already recorded as a hazard.) A capture type
containing a free type variable now gets a key private to its producer
(`H14-FREE-TYVAR`) and merges with nothing.

Distinct shape classes **261 → 332** on -O1 — 71 classes that were being
merged on the strength of a free variable's name — and with the opaque
identity of defect 2, **353**.

#### 5. Existential/GADT fields were indexed by raw binder position

`alt_field` enumerated *all* the binders of an alternative and skipped the
type binders with `continue`, keeping the raw position as the field index.
Constructor applications, however, are indexed by **value** arguments. For
`case e of C @a dict f -> ...` the runtime field `dict` is value index 0 and
was recorded as 1, so a function-valued binder could be paired with the
wrong constructor argument and read a producer set that is not its own. A
separate value-field counter now does the indexing (`H2-PRODUCERS`), with a
test that pins the pairing for a type binder before a function-typed field.

**No number moves on the -O1 dump**, but not for the reason first given
here. *(Corrected at [M2.4f](#the-one-correction-this-produced): the original
text said ShellCheck's Core has no alternative binding a function-typed field
after an existential type binder. It has four — `ShellCheck.Formatter.JSON`
nodes 4217 and 4219, `ShellCheck.Formatter.JSON1` nodes 4896 and 4898, all
matches on `vector`'s existential `Data.Stream.Monadic.Stream`. Raw binder
position would put its step function at field 1 where the value-field counter
puts it at field 0; no number moves because that boundary is
`Unresolved(constructor-is-never-applied-in-the-closed-world)` at either
index.)* The pairing was wrong wherever such an alternative appears, and the
flag matrix and any future dump are not the same program.

#### 6. `UniformRepresentation` → `TypeShapeUniform`

`H4` compares arity and the ordered list of captured **Haskell** types:
`captures()` feeds `binder_ty` and nothing else to `ty_key`. Calling the
result *one Rust representation* contradicts the earlier milestones on
purpose-built grounds: M2.1 lets one Haskell type be a thunk or a value,
M2.3 lets one be `Vec` or an iterator, owned or borrowed, `String` or
`&str`. The verdict is therefore renamed **`TypeShapeUniform`**, and the
reading *one Rust representation* is sound **only if** the M3 lowering
promises a canonical closure-boundary carrier per Haskell type with
conversions inserted at the boundary. **That invariant is open**, and the
report says so on every run.

#### The verdicts, before → after (-O1)

| kind | | ExactClosure | TypeShapeUniform | CloneRequired | FiniteClosureSet | Preserve | Unresolved | total |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| parameter | before | 47 | 20 | 138 | 0 | 6 | 5,253 | 5,464 |
| | **after** | 47 | **16** | **141** | 0 | **7** | 5,253 | 5,464 |
| field | before | 6 | 0 | 0 | 0 | 10 | 19 | 35 |
| | **after** | **0** | 0 | 0 | 0 | **16** | 19 | 35 |
| return | before | 14 | 0 | 0 | 1 | 10 | 50 | 75 |
| | **after** | **3** | 0 | 0 | 1 | **21** | 50 | 75 |
| **all** | before | 67 | 20 | 138 | 1 | 26 | 5,322 | 5,574 |
| | **after** | **50** | **16** | **141** | 1 | **44** | 5,322 | 5,574 |

Every number that moves, with its cause:

| number | before | after | cause |
|---|---:|---:|---|
| field `ExactClosure` | 6 | 0 | defect 1 — an exported field slot is `Preserve` |
| return `ExactClosure` | 14 | 3 | defect 1 — exported / used-as-a-value returns |
| parameter `TypeShapeUniform` | 20 | 16 | 3 by defect 4 (a free-tyvar class split makes them `CloneRequired`), 1 by defect 1 |
| `CloneRequired` | 138 | 141 | defect 4 — three slots whose producers stop agreeing |
| `Preserve` | 26 | 44 | defect 1 — +6 field, +11 return, +1 parameter |
| enumerated | 252 | 252 | unchanged: enumeration is a different fact (`H11`) |
| one representation | 103 | 84 | 3 by defect 4, 16 by defect 2 (opaque never shares) |
| rewritable as one | 87 | 66 | 3 by defect 4, 18 by defect 1 |
| distinct shape classes | 261 | 353 | +71 defect 4, +21 defect 2 |
| per-parameter class sum | 418 | 509 | defect 4 — more classes, still only evidence |
| **clones** | 418 | **53** | defect 3 — distinct call-site tuples, per owner (**68** since [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), which corrected how a tuple is deduplicated) |

#### M2.4e re-checked against the corrected `Higher`

`parsec::residual_edges` reads `Higher::verdict_for`, so it was re-run. The
41-row status table is **unchanged, row for row**:

| status | before | after |
|---|---:|---:|
| closed by the closure graph (`P-HO-EXACT` / `P-HO-FINITE`) | 0 | 0 |
| `boundary-Unresolved(parameter-of-an-anonymous-lambda)` | 20 | 20 |
| `boundary-Unresolved(function-used-as-a-value)` | 19 | 19 |
| `boundary-Unresolved(call-site-is-a-partial-application)` | 2 | 2 |

This is the expected result and not a coincidence: all 41 land on
boundaries whose producer set is `Top`, and `H9-TAINT` is decided before
anything the correction touched. None of the six defects can move an
`Unresolved`.

#### Across the flag matrix, before → after

| | | A (`-O1`) | B | C | D | E | F |
|---|---|---:|---:|---:|---:|---:|---:|
| boundaries | | 5,574 | 6,347 | 8,082 | 34,094 | 31,686 | 31,701 |
| Exact + TypeShapeUniform | before | 87 | 178 | 231 | 862 | 850 | 833 |
| | **after** | **66** | **125** | **172** | **695** | **683** | **682** |
| `CloneRequired` | before | 138 | 184 | 227 | 1,006 | 996 | 1,017 |
| | **after** | **141** | **219** | **269** | **1,150** | **1,140** | **1,145** |
| `Preserve` | before | 26 | 27 | 26 | 39 | 39 | 39 |
| | **after** | **44** | **45** | **43** | **62** | **62** | **62** |
| clones | before (a sum) | 418 | 621 | 770 | 3,118 | 3,132 | 3,210 |
| | **after (planned)** | **53** | **61** | **65** | **154** | **154** | **176** |
| per-slot class sum (evidence) | after | 509 | 916 | 1,182 | 5,058 | 4,982 | 5,020 |

The shape of the correction is the same on every profile: more inlining
makes more shape classes once free type variables stop merging, so
`CloneRequired` rises and `Exact + TypeShapeUniform` falls, while the
*planned* clone count is an order of magnitude below the old sum. The
accounting assertion holds on all six.

#### The gate

Every report except `higher` and the **appended M2.4e sections** of
`parsec` and `tuples --verify` is byte-identical, on `compiler/core-json`
and on all six matrix profiles: `laziness`, `tuples`, `tuples --explain`,
`tuples --boundaries`, `fields`, `lists`, `text`, `verify-rep`, `classops`,
`dictflow`, and `parsec` itself on -O1 — including its 41-row M2.4e table.
What does move, and why:

* `boundary-CloneRequired(5)` → `boundary-CloneRequired(8)` in the M2.4e
  section of `parsec` and `tuples --verify` on profiles C–F: defect 4, a
  free-tyvar class split at that one boundary. The M2.4e **status** of
  every row is unchanged.
* `parsec --json` and three `e.g.` exemplar lines of `parsec` on the matrix
  profiles differ — the known nondeterminism recorded at M2.4e. It was
  re-confirmed here by running the **unchanged** binary three times over
  the same dump: `arg-of-unrecognised-call`, `cont-in-non-cont-slot` and
  `cont-wrong-arity` pick a different witness each run with identical
  counts, and `--json` differs only in the order of each region's `edges`
  (972 of 1,301 regions, before against before).

`cargo test` is 208 (7 new), `cargo clippy --all-targets` 0 warnings,
`cargo fmt --check` clean. No Core is mutated, no codegen is emitted, no
GHC flag changed.

#### Still unsound, stated rather than hidden

* **The M3 carrier invariant** behind `TypeShapeUniform` (defect 6) is
  assumed, not proved, and nothing in M2 can prove it.
* **`Ty::alpha_eq` still compares free type variables by unique.** `H14`
  keeps the *shape class* from resting on that, but the IR predicate itself
  is unchanged and must not be given a free-tyvar-sensitive proof to carry.
* **66 of 87 clone plans are refused**, because some function-valued
  parameter of the owner has an unenumerable producer set. 53 is therefore
  the clone count of the 21 owners that can be planned, not of the program.
* **Set-valued tuples are lower bounds** (†): the fixpoint is monovariant.
* Everything M2.4d already listed under *What remains* still stands.

## M2.4e — the 41 residual Parsec continuation edges

[M2.2](#m22--which-tuples-are-transport-and-which-are-values) stage 2 resolved a continuation
call's target by the **region graph** alone: every call of the region has to
be a saturated call to a visible binder, and what fills the continuation
slot at each has to be a manifest lambda. 41 tuple sites sit on a
continuation call where that failed, and the tuple census counts them as
`parsec-continuation-target-not-in-the-region-graph`. [M2.4d](#m24d--higher-order-representation-agreement)
left them to this one, which asks a second, independent question per edge
and asks it of the **closure graph**: the continuation parameter is a
function-valued slot of the closed world, so the whole-program fixpoint
already knows what reaches it.

The question, per edge:

1. `higher::Higher::verdict_for(module, binder)` — the boundary the
   continuation binder names. No boundary, no answer.
2. Is the verdict one of the three **enumerated** ones — `ExactClosure`,
   `UniformRepresentation`, `FiniteClosureSet`? `Preserve`, `Unresolved`
   and `CloneRequired` are recorded as the refusal they are.
3. Is **every** producer at that boundary a continuation of *known role* —
   a region continuation (a parameter, or a connected derived one) or a
   nested region? Read off `Analysis::cont_source`, the recogniser's own
   classifier; nothing here re-decides what a continuation is, and no name
   is read.

Only then does the edge gain a structural role target: one producer is an
exact one (`P-HO-EXACT`), several a finite one (`P-HO-FINITE`), both level 3
over M2.4d's facts and citing the boundary node and every producer.

| | level | |
|---|---:|---|
| `P-HO-EXACT` | 3 | the continuation slot's boundary is enumerated, every producer is a continuation of known role, and there is exactly one |
| `P-HO-FINITE` | 3 | the same, with more than one: a finite set of role targets |

### The answer: 0 of 41

**No edge closes.** The closure graph refuses every one of the 41, and — the
result worth reporting — it refuses each of them for the *same reason the
region graph did*, one for one:

| | the region graph's refusal (M2.2 stage 2) | the closure graph's answer (M2.4d) |
|---:|---|---|
| 20 | the region's chain is not bound to a binder | `Unresolved(parameter-of-an-anonymous-lambda)` |
| 19 | the region's parser is used as a value | `Unresolved(function-used-as-a-value)` |
| 2 | a call of the region is not saturated exactly | `Unresolved(call-site-is-a-partial-application)` |

The cross-tabulation is exact: the 20/19/2 split of the region graph's
reasons maps onto the 20/19/2 split of the closure graph's, edge by edge.
That is not a coincidence and it is not a second failure either — it is the
same three facts about the Core seen from two sides. A region whose chain is
not bound to a binder *is* an anonymous lambda, so M2.4d's `collect_params`
has no owner to enumerate call sites of; a parser used as a value *is* a
function used as a value, which is `H8-PRESERVE`'s and `H9-TAINT`'s reason
to refuse a slot; a call that is not saturated exactly *is* a partial
application, whose argument never lands. Two analyses that share nothing but
the IR agree about which 41 edges they cannot see, and agree about why.

So M2.4e's honest contribution is a **negative result with provenance**, not
a reclassification: nothing moves, no count in any report changes, and the
41 stay exactly where M2.2 put them — now each with the closure graph's own
reason beside the region graph's. Closing them needs what both refusals
point at and neither pass does: naming the anonymous CPS lambdas of
`ShellCheck.Parser` (M2.4d says the same about its 2,660 + 1,953), and a
per-call-site rather than monovariant view of a parser that is also a value.

### The 41, individually

`site` is the continuation call the tuple reached; `boundary` is the M2.4d
slot that was asked about it.

*Recomputed by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found),
which changed the condition. The **new status** column now says what the
enumeration question answered, with the representation verdict named inside
it rather than standing in for it: all 41 boundaries are **unenumerated**,
which is why none of them closes. Nothing else in the table moves, and the
count is still 0 closed / 41 open.*

| module | node | edge | previous reason | new status | boundary |
|---|---:|---|---|---|---|
| `ShellCheck.Parser` | 1946 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 119: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 1930 |
| `ShellCheck.Parser` | 1962 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 119: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 1930 |
| `ShellCheck.Parser` | 1996 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 119: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 1 (cok) of #? at node 1928 |
| `ShellCheck.Parser` | 2012 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 119: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 1 (cok) of #? at node 1928 |
| `ShellCheck.Parser` | 17769 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 546: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 17767 |
| `ShellCheck.Parser` | 40016 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 659: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 40014 |
| `ShellCheck.Parser` | 44120 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 687: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 3 (eta) of eta#14436 at node 44107 |
| `ShellCheck.Parser` | 44121 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 687: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 3 (eta) of eta#14436 at node 44107 |
| `ShellCheck.Parser` | 44170 | `eta Cok → Cok [R3-CONT-CALL]` | eta of region 687: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (eta) of eta#14436 at node 44105 |
| `ShellCheck.Parser` | 44171 | `eta Cok → Cok [R3-CONT-CALL]` | eta of region 687: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (eta) of eta#14436 at node 44105 |
| `ShellCheck.Parser` | 55495 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 769: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 55491 |
| `ShellCheck.Parser` | 57894 | `eta Eok → Eok [R3-CONT-CALL-ETA]` | eta of region 444: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 3 (eta) of lvl#4458 at node 57887 |
| `ShellCheck.Parser` | 57919 | `eta Cok → Cok [R3-CONT-CALL-ETA]` | eta of region 444: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (eta) of lvl#4458 at node 57885 |
| `ShellCheck.Parser` | 58867 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 439: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 2 (eok) of $wps#4447 at node 58854 |
| `ShellCheck.Parser` | 58868 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 439: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 2 (eok) of $wps#4447 at node 58854 |
| `ShellCheck.Parser` | 58921 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 439: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (cok) of $wps#4447 at node 58853 |
| `ShellCheck.Parser` | 58922 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 439: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (cok) of $wps#4447 at node 58853 |
| `ShellCheck.Parser` | 61995 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 802: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 61982 |
| `ShellCheck.Parser` | 61996 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 802: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 61982 |
| `ShellCheck.Parser` | 62045 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 802: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 1 (cok) of #? at node 61980 |
| `ShellCheck.Parser` | 62046 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 802: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 1 (cok) of #? at node 61980 |
| `ShellCheck.Parser` | 66715 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 407: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 4 (eta) of k#4393 at node 66700 |
| `ShellCheck.Parser` | 66716 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 407: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 4 (eta) of k#4393 at node 66700 |
| `ShellCheck.Parser` | 66765 | `eta Cok → Cok [R3-CONT-CALL]` | eta of region 407: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 2 (eta) of k#4393 at node 66698 |
| `ShellCheck.Parser` | 66766 | `eta Cok → Cok [R3-CONT-CALL]` | eta of region 407: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 2 (eta) of k#4393 at node 66698 |
| `ShellCheck.Parser` | 79705 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 866: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 79701 |
| `ShellCheck.Parser` | 87005 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 891: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eok) of #? at node 87003 |
| `ShellCheck.Parser` | 98148 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 976: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eta) of #? at node 98146 |
| `ShellCheck.Parser` | 123694 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 5 (eta) of $wk#36309 at node 123689 |
| `ShellCheck.Parser` | 123725 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 5 (eta) of $wk#36309 at node 123689 |
| `ShellCheck.Parser` | 123767 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 5 (eta) of $wk#36309 at node 123689 |
| `ShellCheck.Parser` | 123824 | `eta Cok → Cok [R3-CONT-CALL]` | eta of region 1155: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 3 (eta) of $wk#36309 at node 123687 |
| `ShellCheck.Parser` | 123881 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 1157: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 4 (eta) of k#36395 at node 123877 |
| `ShellCheck.Parser` | 124015 | `eta3 Eok → Eok [R3-CONT-CALL]` | eta3 of region 1149: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 2 (eta3) of $wm1#36087 at node 123991 |
| `ShellCheck.Parser` | 124668 | `eta Eok → Eok [R3-CONT-CALL]` | eta of region 1161: the region's chain is not bound to a binder | `boundary-producer-set-is-not-enumerated (Unresolved: parameter-of-an-anonymous-lambda)` | parameter 4 (eta) of k#36617 at node 124648 |
| `ShellCheck.Parser` | 125675 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 54: a call of the region is not saturated exactly | `boundary-producer-set-is-not-enumerated (Unresolved: call-site-is-a-partial-application)` | parameter 3 (eok) of lvl#397 at node 125673 |
| `ShellCheck.Parser` | 125720 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 53: a call of the region is not saturated exactly | `boundary-producer-set-is-not-enumerated (Unresolved: call-site-is-a-partial-application)` | parameter 3 (eok) of lvl#382 at node 125718 |
| `ShellCheck.Parser` | 126651 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 1166: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 3 (eok) of lvl#36967 at node 126635 |
| `ShellCheck.Parser` | 126675 | `eok Eok → Eok [R3-CONT-CALL]` | eok of region 1166: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 3 (eok) of lvl#36967 at node 126635 |
| `ShellCheck.Parser` | 126717 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 1166: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (cok) of lvl#36967 at node 126633 |
| `ShellCheck.Parser` | 126741 | `cok Cok → Cok [R3-CONT-CALL]` | cok of region 1166: the region's parser is used as a value | `boundary-producer-set-is-not-enumerated (Unresolved: function-used-as-a-value)` | parameter 1 (cok) of lvl#36967 at node 126633 |

### What this is checked by

`parsec::residual_edges(&[Analysis], &Higher)` builds the population the way
the tuple census itself records it — the escape evidence of every flow whose
fate is `parsec-continuation-target-not-in-the-region-graph`, one row per
flow — so the 41 here are the same 41 `h2r tuples` counts, not a second
population that happens to have the same size. The section prints in
`h2r parsec` and, in summary, in `h2r tuples --verify`; both are additions,
and every other line of every existing report is byte-identical.

*Corrected by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found).
The condition this section states — "one of the three enumerated verdicts" —
was the wrong condition, and the paragraph below called
`residual_edge_closes_through_a_uniform_boundary_of_known_continuations`
"the" regression test as though `parsec.rs` had no others. It carries
**29** unit tests of its own (27 before M2.4h), in its own `mod tests`, and
`cargo test` counts every one of them; this is one of three that cover
`residual_edges`.*

That regression test
covers the branch the real dump does not reach: two regions that each hand a
tuple to their `cok` and are each called twice with a continuation the region
graph refuses to follow. One closes — `P-HO-FINITE` over a
`UniformRepresentation` boundary whose two producers are both nested regions
— and one stays open with `producer-is-not-a-region-continuation`, because
one of its two producers is a lambda that is no continuation at all: opaque
to the role question however well its representation agrees. That the rule
*can* fire is therefore evidence, and that it does not fire on ShellCheck is
a fact about ShellCheck's Core.

## M2.4f — re-deriving the M2.4 verdicts independently

`h2r verify-m24 <dir> [--json] [--explain]`.

[M2.2 stage 2](#the-independent-verifier) and
[M2.3e](#m23e--re-deriving-the-representation-verdicts-independently) are the
model, and the discipline is theirs: a second implementation that **shares
nothing with the analyses it checks beyond the IR** and a short, named list
of trusted inputs, re-deriving every claim whose being wrong would be a
miscompile, with every disagreement settled by fixing whichever side is
wrong. `crates/h2r-analysis/src/verify_m24.rs` does that for M2.4b–d′. It
does **not** use [`classops.rs`](#m24b--the-closed-world-class-op-census)'s
walk, [`dictflow.rs`](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go),
[`higher.rs`](#m24d--higher-order-representation-agreement) or `flow.rs`; it
has its own closed-world index, its own dictionary test, its own call-site
enumeration, its own dispatch, its own three fixpoints, its own totality domain
with its own definition of *already evaluated*, its own escape walk, its own
type key and its own shape classes.

The analyses' verdicts reach it as **plain data**, through
`m24_claims.rs` — the same split `m23.rs` makes for `verify_rep.rs`, and for
the same reason: the verifier must not be able to see a `Verdict` at all.

### What it re-derives, and why those

| claim | `-O1` | a wrong one costs |
|---|---:|---|
| class-op site `Exact(target)` | 7 | a call redirected into the wrong instance's method |
| class-op site, bounded `DictSet` | 118 | an instance outside the set dispatched at run time |
| dictionary parameter, bounded `DictSet` | 106 | the same, one level up |
| dictionary value `Erasable` | 102 | a dictionary that is still needed is deleted |
| dictionary parameter `Erasable` / `WithClone` / `WithObligation` | 36 / 4 / 0 | a dictionary, or a force, that is still needed is deleted |
| owner-level dictionary clone plan | 4 | fewer specialisations than the call sites that exist |
| higher-order `ExactClosure` / `TypeShapeUniform` / `CloneRequired` / `FiniteClosureSet` | 50 / 16 / 141 / 1 | one representation given to a slot two live closures disagree about |
| owner-level closure clone plan | 21 plans, 68 clones (53 before [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)) | ditto |
| | **606 claims** | |

A wrong `Unresolved` or a wrong `Preserve` costs only coverage, so nothing
re-derives those — the same asymmetry M2.3e states.

### Trusted inputs, named

These are **consulted, not verified**, and nothing in this milestone may be
read as a check of them. They are printed at the top of every run.

1. **The 17-class method-field table** (`classops::CLASSES`). It is a
   [level-5 axiom](#the-class-table-and-why-there-is-one): format 5 carries
   neither a type nor an unfolding for a global, so a selector's
   `C a => …` type and its `case d of C:C … m … -> m` body are both absent
   and the field order is not derivable from the dump at all. Asserting it a
   second time here would be inventing a second unchecked assertion rather
   than checking the first — M2.3e's argument about the list axioms, exactly.
   The **data** is shared; every *use* of it is re-derived: which selector
   names which class, which field a method sits at, the `$pN<Class>`
   superclass reading, and the cross-check against the dictionary
   constructor's own `repArity`.
2. **`W0-CLOSED-WORLD` / `H0-CLOSED-WORLD`** — the 28 modules are the whole
   program. An assumption about the build, which no walk can prove.
3. **GHC's own flags**: `isClassOpId` (the id table's `isClassOp`),
   `isExportedId` (a binder's `exported`) and the demand signatures'
   strictness bits, read from the authoritative source — the binder at a
   binding site, the id table for an import.
4. **The structured `Ty`**, and `TyCon` stable-name identity.

**Addressing is not sharing.** A claim has to name what it is about, and the
names are IR addresses: a module and a node id, a module and a `BinderId`, a
constructor's stable name and a value-field index. A dictionary identity is
addressed the way any dictionary built in the dump has to be — the module and
node of its constructor application, or the stable name of an imported dfun —
and *which node that is* is re-derived here. Agreeing on an address is not
agreeing on a derivation; disagreeing about which node is the constructor
application would be a disagreement, and is reported as one.

*[M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found) adds
one shared **rendering** for the same reason: `dictflow::group_lines`, which
lays a clone plan's partition of call sites out as text. It derives nothing
— it sorts and joins addresses each walk computed for itself — and both
sides need one spelling for the same set, exactly as they need one spelling
for a method target. Nothing else crosses; in particular the two walks'
shape classes, capture keys and type keys stay their own and are rendered
differently on purpose, which is why a closure clone plan is checked by its
partition and not by its tuple strings.*

The linkage table that addressing rests on is re-derived too, including
[M2.4c′'s identity cleanup](#identity-cleanups): this walk writes its own
*external name* test, rejects the two pseudo-units `_sys` and `_in` that a
three-way split on `$` would otherwise read as a unit and a module, and
**asserts that no two top-level bindings claim one external stable name**.
That assertion holds on all seven dumps, and it is load-bearing: accepting
the pseudo-units makes this walk's own assertion fail on `-O1` with exactly
`external stable names are not unique: ["$_sys$poly_$j"]`.

### What it found

| dump | claims | re-derived | **disagreements** | coverage refusals |
|---|---:|---:|---:|---:|
| `-O1` (and matrix A) | 606 | 606 | **0** | 0 |
| B | 749 | 749 | **0** | 0 |
| C | 867 | 867 | **0** | 0 |
| D | 2,209 | 2,209 | **0** | 0 |
| E | 2,187 | 2,187 | **0** | 0 |
| F | 2,209 | 2,209 | **0** | 0 |

Not one claim refused, on any dump, in either sense: this walk re-derived
every positive verdict M2.4 publishes, and it never had to decline. The
populations it built on the way are the same ones, which is a second
agreement and a separate one — the claim list says nothing about how many
class-op sites exist:

| this walk's own population | A (`-O1`) | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| class-op sites | 565 | 587 | 595 | 595 | 595 | 596 |
| dictionary parameters | 216 | 210 | 222 | 223 | 223 | 231 |
| dictionary identities | 191 | 191 | 191 | 238 | 238 | 238 |
| function-valued boundaries | 5,574 | 6,347 | 8,082 | 34,094 | 31,686 | 31,701 |
| rounds (dictionary / totality / closure) | 7/4/10 | 7/4/10 | 7/4/11 | 7/7/11 | 7/7/11 | 7/7/11 |

### The whole population, not just the claimed part

A claim check is **one-sided**: only the positive verdicts are re-derived, so
a walk that called everything `Erasable` would pass it. `verify-m24`
therefore also prints what this walk says about *every* value, parameter and
boundary, in the analyses' own column order, and every published table comes
back cell for cell on `-O1`:

| this walk's own verdicts (`-O1`) | `Erasable` | `…WithObligation` | `…WithClone` | `Preserve` | `Unresolved` |
|---|---:|---:|---:|---:|---:|
| dictionary values (191) | 102 | 0 | 0 | 89 | 0 |
| dictionary parameters (216) | 36 | 0 | 4 | 84 | 92 |

| | `ProvenTotal` | `MustPreserveForce` | `Unknown` |
|---|---:|---:|---:|
| dictionary parameters (216) | 118 | 0 | 98 |

| | `ExactClosure` | `TypeShapeUniform` | `CloneRequired` | `FiniteClosureSet` | `Preserve` | `Unresolved` |
|---|---:|---:|---:|---:|---:|---:|
| boundaries (5,574) | 50 | 16 | 141 | 1 | 44 | 5,322 |

It holds on every profile too. Every cell of
[M2.4c′'s](#across-the-flag-matrix-1) and
[M2.4d′'s](#across-the-flag-matrix-before--after) matrix tables comes back:

| this walk's own verdicts | A (`-O1`) | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| values `Erasable` | 102 | 102 | 101 | 139 | 139 | 139 |
| parameters `Erasable` | 36 | 28 | 34 | 28 | 28 | 28 |
| parameters `ErasableWithClone` | 4 | 3 | 4 | 4 | 4 | 4 |
| parameters `ProvenTotal` / `MustPreserveForce` / `Unknown` | 118/0/98 | 110/0/100 | 121/0/101 | 77/0/146 | 77/0/146 | 85/0/146 |
| `ExactClosure` + `TypeShapeUniform` | 66 | 125 | 172 | 695 | 683 | 682 |
| `CloneRequired` | 141 | 219 | 269 | 1,150 | 1,140 | 1,145 |
| boundary `Preserve` | 44 | 45 | 43 | 62 | 62 | 62 |

These are not claim checks — a difference here would be a difference to look
at, not a `D` — and there is no difference: the erasure table of
[M2.4c′](#erasure-tables-before--after), its totality row (118/0/98) and the
whole of [M2.4d′](#the-verdicts-before--after--o1)'s corrected verdict table
are reproduced by a walk that has never seen them.

### Why silence here is evidence

A verifier that agrees with everything has said nothing unless it can be
shown to bite. Two tests do that, and they are the reason the tables above
are worth printing: `m24f_the_verifier_refuses_a_claim_that_names_the_wrong_target`
rewrites one `Exact` claim's target to the *other* instance's method and the
walk refuses it as `X_TARGET_DIFFERS` (a `D`, not a `C`), and
`m24f_the_verifier_refuses_a_clone_plan_with_the_wrong_count` turns a
two-tuple clone plan into a one-clone claim and gets `X_CLONES_DIFFER`. Both
assert that the refusal is counted as a disagreement and not as a coverage
loss.

### The adversarial shapes

Each shape is a hand-built fixture in `tests.rs` **and** a count in the real
`-O1` dump, printed by `h2r verify-m24`, so that a fixture is never the only
evidence a rule was exercised. Every count is this walk's own.

| # | shape | in `-O1` | example | must be |
|---:|---|---:|---|---|
| 1 | bounded dictionary identity whose producer is not total | **0** | — | never `Erasable` |
| 2 | one dictionary parameter, two or more instances | 36 | `ShellCheck.Parser` 1645 | a finite set; `ErasableWithClone(n)` where it is erasable at all (4 of the 36 here) |
| 3 | a dictionary used as an ordinary value *and* as a selector's dictionary | 11 | `ShellCheck.AST` 23582 | `Preserve`; the target is unaffected |
| 4 | a dictionary parameter of unknown totality | 98 | `ShellCheck.AST` 3461 | `Unresolved` / `Preserve(totality)` |
| 5 | a superclass selector site (`$pN<Class>`) | 72 | `Main` 659 | follows to the superclass instance |
| 6 | a dictionary parameter fed through dispatch | 15 | `Main` 7766 | terminates; the fixpoint is monotone |
| 7 | a partially applied class-op selector | **0** | — | recorded, no target claimed |
| 8 | an exported or valued function slot whose producers *do* agree | 18 | `ShellCheck.AnalyzerLib` binder 2508 | `Preserve`, decided before agreement |
| 9 | a slot two opaque producers reach | 4 | `ShellCheck.Interface` field 0 of `SystemInterface` | two classes: opaque unifies with nothing |
| 10 | a capture type carrying a free type variable | 292 | `ShellCheck.AST` 3463 | a producer-private key: unifies with nothing |
| 11 | a value field bound after an existential type binder | 25 | `Main` 623 | value-field indexing, not raw binder position |
| 11a | …and the field is function-typed | 4 | `ShellCheck.Formatter.JSON` 4217 | pairs with the constructor's value argument |
| 12 | an owner with two or more slots, planned jointly | 11 | `ShellCheck.Analytics` `doVariableFlowAnalysis` (2 slots, 3 tuples) | clones = distinct call-site tuples |
| 13 | several representations at one slot, at a local | 141 | `ShellCheck.ASTLib` binder 1422 | `CloneRequired` |
| 13a | …the same, at an exported or valued slot | 10 | `ShellCheck.AnalyzerLib` field 0 of `Checker` | `Preserve` |
| 14 | a finite closure set at a slot no clone can serve | 1 | `ShellCheck.Checks.ShellSupport` return binder 942 | `FiniteClosureSet(n)` |
| 15 | a three-argument closure named like a Parsec continuation | 124 | `ShellCheck.Parser` 3450 | arity and captures decide; no name is read |
| 16 | a `case` on the alternative binder of a **lazy** field | 6,625 | `Main` 518 | a force: the binder is an unevaluated thunk |
| 17 | …the same, on a **GHC-strict** field's binder | 168 | `ShellCheck.ASTLib` 8186 | already evaluated: the `case` deletes nothing |
| 18 | a `case`/`let` head carrying outer value arguments | **0** | — | refused, never peeled: the arguments would be dropped |

*Rows 16–18 were added by
[M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), one
per defect it found in the totality domain.*

Rows 1 and 7 are zero, and both are load-bearing zeroes rather than gaps: the
fixtures exercise each rule, and the dump's zero is the finding. Row 1 is the
`-O1` half of [M2.4c′](#correction-m24c--totality-is-not-the-same-fact-as-identity)'s
counterexample; row 12 is [M2.4d′](#3-the-clone-count-was-a-sum-of-per-parameter-numbers)'s
`(A,X)`, `(B,X)`, `(A,Y)` shape, whose fixture wants **three** clones where
the per-slot sum and the product both say four.

Row 15 belongs half to [M2.4e](#m24e--the-41-residual-parsec-continuation-edges).
On this side of the line the finding is that the 124 three-argument
`cok`/`eok`/`cerr`/`eerr`-shaped closures buy nothing from their names:
a shape class is an arity and an ordered list of captured types, and the
fixture pins that an identically shaped `zzz` lands in the same class while a
two-argument `cok2` does not. On the M2.4e side, role admission is decided by
the layout check and never by a name — `h2r parsec` reports 1,301/1,301
regions proven with **0** refused on continuation *order* and 10 census sites
rejected outright as `head-is-not-a-parsec-role-binder` (e.g.
`ShellCheck.Checks.Commands` node 16805). A Parsec-looking head that is
structurally not a continuation gets no role and no edge.

### M2.4c′'s instrumented claim, re-derived

M2.4c′ says `MustPreserveForce` is **0** for a reason stronger than "every
force was discharged": an instrumented run showed the totality walk reaches
*no `case` node at all* on any dictionary path, GHC's `-O1` having floated
every dictionary out of every scrutinee. This walk counts the same thing in
its own transfer and reports it on every run:

```
  case nodes this walk's totality transfer reaches on a dictionary path: 0
```

That matters because this walk's definition of *already evaluated* is
deliberately **narrower** than M2.4c′'s: a literal, a lambda, a saturated
constructor application, a dfun, or a variable a `case` has already bound.
M2.4c′ additionally admits a variable GHC marks strict at its binder that an
enclosing `case` on that binder dominates — a sound clause, but one this
module would be *re-running* rather than checking, so it is left out.

*Amended by [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found):
"a variable a `case` has already bound" was too generous on **both** sides.
An alternative binder of a lazy field is an unevaluated thunk, and this walk
had taken that clause from M2.4c′ rather than deciding it. Both now admit
only the scrutinee binder and a GHC-strict field's binder.*
Omitting it can only make this walk find more forces than the analysis, which
is the conservative direction for a verifier; it finds none, because there is
no `case` to find.

### The one correction this produced

There was no disagreement about a verdict. There was one about the **record**:

* [M2.4d′ defect 5](#5-existentialgadt-fields-were-indexed-by-raw-binder-position)
  says "No number moves on the -O1 dump — GHC's ShellCheck Core has no
  alternative binding a function-typed field after an existential type
  binder". The first half is right and the second half is **wrong**. There
  are four such alternatives: `ShellCheck.Formatter.JSON` nodes 4217 and
  4219 and `ShellCheck.Formatter.JSON1` nodes 4896 and 4898, all of them
  matches on `vector`'s existential `Data.Stream.Monadic.Stream`, whose
  first runtime field is the step function. The value-field counter puts it
  at *field 0*, raw binder position would have put it at field 1, and the
  reason no number moves is not that the shape is absent but that the
  boundary is `Unresolved(constructor-is-never-applied-in-the-closed-world)`
  at either index. Resolution: the **analysis was right and the prose was
  wrong**; M2.4d′'s paragraph is corrected above, and the shape is now
  counted on every run (rows 11 and 11a).

### Where this walk declines, and why that is not a disagreement

Two weakenings are written down rather than hidden, and neither fired on any
of the seven dumps:

* **A `Top` set of this walk's own is a coverage refusal (`C`), never a
  disagreement (`D`).** `Top` says only that *this* walk could not account
  for every producer, which is this walk being blunter. What would be a
  disagreement is naming a producer the analysis does not have, and that is
  `X_SET_DIFFERS`.
* **The narrower *already evaluated*** above. A refusal it caused would be
  this walk over-refusing, and would be reported as a disagreement for a
  human to resolve — `X_NOT_TOTAL` — rather than silently absorbed.

### The gate

Every existing report is **byte-identical** before and after, on
`compiler/core-json` and on all six matrix profiles: `stats`, `laziness`,
`parsec`, `tuples` (plus `--explain`, `--verify`, `--boundaries`), `fields`,
`lists` (plus `--axioms`), `text` (plus `--heads`, `--explain`),
`verify-rep`, `classops` (plus `--per-module`, `--explain`), `dictflow` and
`higher`, with the `--json` form of each — 238 captured reports over the
seven dumps, of which **224 are byte-identical** and the other 14 are the
**pre-existing `parsec` nondeterminism** and nothing else (every run's
standard error was captured too, and all 224 are empty):

* `parsec` on B, C and D and `parsec --explain` on B, C, E and F differ in
  exactly **one `e.g.` exemplar line each** — the same reject reason with a
  different witness, every count identical. That is the witness-picking
  M2.4a's gate recorded and M2.4d′ re-confirmed by running an unchanged
  binary three times; *which* of the profiles it lands on moves from run to
  run, which is the point.
* `parsec --json` differs on all seven dumps in each region's edge list
  order, and is **multiset-identical on all seven** when every list is
  canonicalised.

**No census number moved**, because nothing but new code was added:
`verify_m24.rs` and `m24_claims.rs` are new, `h2r verify-m24` is new, and the
only edit to an existing analysis is an `owner_binder` field on
`dictflow::OwnerPlan` and `higher::OwnerPlan` — an address a claim needs,
`#[serde(skip)]`, read by no report.

`cargo test` is **225** (17 new: one per adversarial shape, plus the two that
make the verifier bite), `cargo clippy --all-targets` 0 warnings and
`cargo fmt --check` clean. No Core is mutated, no codegen is emitted, no GHC
flag changed.

### Still unsound, or still unchecked

* **The four trusted inputs are trusted.** In particular the class table is
  an axiom on both sides of this check, and a wrong field order would be
  wrong in the same way twice. What the two sides do check against each other
  is every *use* of it, including the `repArity` cross-check, which is what a
  wrong entry would have to survive.
* **The closed world is an assumption**, and this walk rests on it exactly as
  M2.4c and M2.4d do. Re-deriving a producer set does not re-derive the right
  to enumerate it.
* **`Unresolved` and `Preserve` are not re-derived *as claims*.** A milestone
  that refused too much would pass the claim check in silence; that is the
  deliberate asymmetry, because only the positive verdicts can miscompile.
  What narrows it is the whole-population table above, where this walk's own
  `Preserve` and `Unresolved` counts are printed and agree cell for cell —
  but a difference there is a difference to look at and not a `D`, and no
  *reason* attached to a refusal is compared at all.
* **The monovariant lower bounds stand.** Four dictionary plans and eight
  closure plans on `-O1` have a set-valued tuple component, and their clone
  counts are lower bounds on both sides — this walk re-derives the same
  tuples and flags the same lower bound, which is agreement about a bound
  and not a closing of it.
* **`TypeShapeUniform`'s M3 carrier invariant** is assumed here too. This
  walk re-derives the shape classes; it cannot promise a lowering.

## M2.4g — the views, the provenance, the accounting, and what the milestone claims

M2.4b–e record the facts and [M2.4f](#m24f--re-deriving-the-m24-verdicts-independently)
re-derives every verdict whose being wrong would be a miscompile. This
section adds the three things a milestone needs before it can be closed —
exactly the three [M2.3f](#m23f--the-representation-view-and-what-the-milestone-claims)
added for M2.3: **views** that lay one site's proof out so a person can
audit it, **provenance** in `h2r show` so any Core node can be asked what
M2.4 says about it, and the milestone's own **accounting**, asserted in
code and printed whole. It changes no verdict.

```sh
cargo run --release --bin h2r -- classops ../core-json --view 1154
cargo run --release --bin h2r -- classops ../core-json --view-all --module ShellCheck.Fixer --json
cargo run --release --bin h2r -- higher ../core-json --view 51239
cargo run --release --bin h2r -- higher ../core-json --view-all --module ShellCheck.AST --json
cargo run --release --bin h2r -- show ../core-json ShellCheck.Fixer 1154      # + its M2.4 footers
cargo run --release --bin h2r -- m24 ../core-json                             # the whole milestone
```

### Two views, each with its own completeness assertion

The **class-op view** puts one dispatch site on the page: the class and the
method with the field the selector reads, the dictionary argument, the
per-module origin chain with each step's rule, the **whole-program producer
set at every parameter hop** the dictionary passes through, the target
outcome, the totality fact, the erasure verdict with its reason, and the
owner's clone-plan row where the owner has one. Every fact carries the
verifier's answer, and a claim `verify-m24` refused is never printed as
proven. `ClassopViews::check` asserts that **every site of the module
appears exactly once**, and `ClassopView::check` that no parameter hop is
listed twice — the walk up the parameter chain terminates and never doubles
back.

```
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

That one site is the milestone in miniature: M2.4b could only say
`Unresolved(dictionary-parameter-of-an-exported-function)`, the closed-world
fixpoint bounds the dictionary to one instance and the method to one
binding, the totality domain says the producer is a value so erasing it
moves no divergence, and the second walk re-derived all three.

The **boundary view** puts one function-valued slot on the page: the slot
with its owner and whether it is exported or belongs to a function used as
a value, every producer with its **full shape class and its capture types**,
every use, and — the part the milestone's own corrections make necessary —
the **rule order** that produced the verdict, with the answer at every step
and an arrow on the one that fired. `H8-PRESERVE` is decided before `H5`
and `H6` ([M2.4d′ defect 1](#1-h8-was-decided-after-h5h6)), and the view
shows the earlier questions answered rather than skipped.
`BoundaryViews::check` asserts **every boundary of the module appears
exactly once**, and `BoundaryView::check` that every producer appears once
and that *rewritable as one* never exceeds *one representation*.

```
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

`--view-all --module M` does every site or boundary of a module and `--json`
dumps the views as structured data. Both assertions are exercised on the
real dump rather than on a fixture: over the 28 modules they lay out **565
of 565** class-op sites and **5,548** boundaries, each exactly once —
`ShellCheck.AST` 429 sites and 240 boundaries, `ShellCheck.Parser` 57 and
5,154. The 26 boundaries the 28 modules do not cover are constructor
*fields* of constructors defined outside the dump — nine of `GHC.Prim`'s,
nine of `GHC.Tuple.Prim`'s, three of `GHC.Base`'s and five more — and
`--module GHC.Tuple.Prim` lays those out on the same terms. 5,548 + 26 =
5,574.

### Provenance in `h2r show`

The two proof objects are loaded by default whenever the module has any,
exactly as the Parsec, tuple and three representation objects are, and
`--no-classops` / `--no-higher` opt out one at a time. They annotate
class-op sites, dictionary values, dictionary-parameter binders and their
occurrences, function-valued slots and their binders, and every closure
producer — inline, and with one footer per site the node takes part in:

```
$ h2r show compiler/core-json ShellCheck.Fixer 1154 --depth 1
([#1154]{class-op site Ranged.setRange ⇒ Exact}setRange[#1253]
   $dRanged[#1252]{occurrence of dictionary parameter 0 of removeTabStops} … )

node 1154
  classop: Ranged.setRange at node 1154 dictionary $dRanged at node 1252 (param 0 of removeTabStops#312) → whole-program {ShellCheck.Fixer#14} → target Exact(ShellCheck.Fixer.$csetRange)
  totality ProvenTotal … erasure Erasable [verified: yes]
  this node: the class-op application itself; per-module Unresolved(dictionary-parameter-of-an-exported-function) [verified target: yes]
```

```
$ h2r show compiler/core-json ShellCheck.Analytics 51239 --depth 0
\readFunc{function-valued param ⇒ CloneRequired} writeFunc¹{function-valued param ⇒ TypeShapeUniform} … ->

node 51239
  boundary: parameter 0 (readFunc) of doVariableFlowAnalysis#1867 producers 3 (classes 3) → CloneRequired(3) … owner plan 3 clones
  one representation false … rewritable as one false [verified: yes]
  this node: the param slot itself; not exported
  H11-SEPARATE: enumerated true — an enumerated producer set is not one representation
```

All seven proof objects' marks are concatenated rather than merged, so it
stays visible which object said what. Unlike M2.3's, these two are
*whole-program by construction* — a dictionary parameter's producer set and
a slot's closure set are unions over every module — so the objects are built
over the whole dump and only the asked-about module's sites, values,
parameters, boundaries and producers are indexed. The whole M2.4 object,
`verify-m24` included, costs about three seconds on the `-O1` dump: `h2r
show` on a class-op site takes **2.7s** with both objects loaded against
**1.8s** with `--no-classops --no-higher`, most of which is reading the
dump either way. That is why `show` can load them by default and stay a
per-node query.

### The milestone accounting — three questions, never collapsed

Asserted in code (`m24::Accounting::check`) and printed whole by `h2r
classops`, `h2r higher` and `h2r m24`. The milestone has spent two
corrections learning that these are three questions and not one: **a known
method target is not a removable dictionary** (M2.4c) and **an enumerated
producer set is not one representation** (M2.4d). They are never added
together and never reported as one number.

```
(1) can the call target be enumerated?   sites = Exact + FiniteSet + Unresolved
  class-op dispatch sites (population)              565
  Exact(target)                                       7
  FiniteSet(targets)                                  0
  Unresolved                                        558
  … sites whose dictionary is bounded               118   a SEPARATE fact, never added in
  re-derived by verify-m24 (Exact / bounded)          7 / 118
```

```
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

```
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

`rewritable as one` (66) ≤ `one representation` (84) ≤ `enumerated` (252) is
asserted, and the direction is the point: 18 boundaries whose producers
genuinely agree are still `Preserve`, because the rewrite does not own the
slot. Twelve of the twenty-five `-O1` clone plans that carry a
number are flagged where a tuple has a set-valued component — **4 of 4**
dictionary plans and **8 of 21** closure plans are lower bounds, closable
only by a call-string analysis.

**The 3×5 matrix** crosses questions 1 and 3 rather than collapsing them:

| target ⟍ dictionary | `Erasable` | `…WithObligation` | `…WithClone` | `Preserve` | `Unresolved` |
|---|---:|---:|---:|---:|---:|
| `Exact` | 7 | 0 | 0 | **0** | 0 |
| `FiniteSet` | 0 | 0 | 0 | **0** | 0 |
| `Unresolved` | 10 | 0 | 0 | 154 | 394 |

The bolded cells — a site whose method is known but whose dictionary must
survive anyway — are **0**, and the other direction is populated: 10 sites
whose dictionary is `Erasable` still have no known method target.

**The residual, itemised and owned.** Every row is attributed; an
unattributed row would be the milestone hiding what it did not do. The site
rows sum to the 558 `Unresolved` and the boundary rows to the 44 `Preserve`
plus 5,322 `Unresolved`, both asserted.

| | class-op sites | whose problem it is |
|---:|---|---|
| 413 | `function-is-unreachable-in-the-closed-world` | `W0`: dead in the closed world — if ShellCheck is built as a library they come back |
| 53 + 48 + 7 + 5 + 1 | `instance-method-not-in-the-dump` (`$fMonoidDual`, `$fMonadIO`, `$fMonadStatesParsecT`, `$fMonadStatesReaderT`, `$fMonadReaderrParsecT`) | the instance is known and its body is in another package: a bigger dump, or a hand-written callee |
| 17 | `dictionary-read-from-a-non-dictionary-constructor-field` | `SomeException`'s existential dictionary field: M3, or a hand-written `Exception` lowering |
| 9 | `method-is-never-dispatched-in-the-closed-world` | no class-op site in the program selects that field: dead under `W0` |
| 4 | `dictionary-returned-by-a-call-the-dump-cannot-see` | a bigger dump |
| 1 | `dispatched-from-a-site-with-an-unknown-dictionary` | closable only when that site's dictionary is |

| | function-valued boundaries | whose problem it is |
|---:|---|---|
| 2,660 + 1,953 = **4,613** | `function-used-as-a-value`, `parameter-of-an-anonymous-lambda` | the Parsec CPS wall: a naming pass for the anonymous lambdas, then a call-string view |
| 413 | `call-site-is-a-partial-application` | the partial application's own consumers |
| 227 | `function-is-unreachable-in-the-closed-world` | dead under `H0` |
| 44 | `expression-is-not-a-closure` | the body's lambda chain and the binder's type disagree about the return: refused rather than picked |
| 22 + 3 | `a-closure-read-back-from-a-constructor-field`, `a-closure-returned-by-an-imported-call` | a genuine run-time closure: the lowering decides, not this analysis |
| 19 | `closure-from-an-untracked-higher-order-parameter` | the propagation, once the anonymous lambdas are named |
| 14 + 5 | `the-boundary-is-exported-…`, `…-belongs-to-a-function-used-as-a-value` | shared outside the rewrite: M3's ownership question |
| 5 | `constructor-is-never-applied-in-the-closed-world` | dead under `H0` |
| 1 | `closure-set-exceeded-the-budget` | a larger budget, or a per-caller analysis |

### The cross-milestone links

Four, and **nothing is reclassified**: every fate M2.2 recorded, every tier
M2.1 recorded and every rep M2.3 recorded stands exactly as it was. `h2r
m24` recomputes each rather than quoting it, so the two sides cannot drift.

**Back to M2.2 — the 67 closure-into-a-parameter tuple flows.** Recomputed
against the corrected `Higher`: 31 `CloneRequired`, 22 no boundary, 13
`TypeShapeUniform`, 1 `ExactClosure`, and **14 could be reclassified by a
later pass** — the 13 uniform plus the 1 exact. That is the same 14
[M2.4d](#feeding-the-proof-back--nothing-is-reclassified) published and it
is **unchanged after M2.4d′**. That is visible in the table rather than
argued: not one of the 67 lands on a `Preserve` slot, so none of them is at
an exported or valued boundary — which is where defect 1 moved verdicts —
and the 13 uniform slots survived the free-tyvar class split of defect 4.

**Back to M2.3 — the closure residual, by holder.** M2.3b left **2,454**
constructor fields `Unknown` because the callee that consumes them is an
unknown higher-order value — the population whose two largest rows M2.3's
residual table names as *1,143 `eta` + 565 `eok`*. Each is now asked of the
closure graph, by the callee binder M2.3 itself named:

| holder | n | what the closure graph says |
|---|---:|---|
| `eta` | 1,143 | `Unresolved` 1,035, `CloneRequired` 84, `ExactClosure` 20, no boundary 4 |
| `eok` | 565 | `Unresolved` 554, `CloneRequired` 11 |
| `cok` | 282 | `Unresolved` 275, `CloneRequired` 7 |
| `eerr` | 182 | `Unresolved` 178, `CloneRequired` 4 |
| `cerr` | 146 | `Unresolved` 146 |
| `reader` | 36 | `TypeShapeUniform` 36 |
| `eta3` | 29 | `Unresolved` 29 |
| `z'` | 21 | `CloneRequired` 21 |
| 14 more | 50 | no boundary 36, `Unresolved` 8, `ExactClosure` 3, `Preserve` 3 |

**59 could be reclassified** (36 `reader` + 20 `eta` + 3 `color`). The shape
of the answer is M2.4d's own: five of the six largest holders are Parsec's
CPS continuations, and they are `Unresolved` for the same reason 4,613
boundaries are.

**Back to M2.1 — the 41 residual Parsec continuation edges.** Re-run here
against the same `Higher`: **0 of 41** closed, 20
`boundary-Unresolved(parameter-of-an-anonymous-lambda)`, 19
`boundary-Unresolved(function-used-as-a-value)`, 2
`boundary-Unresolved(call-site-is-a-partial-application)` — row for row what
[M2.4e](#m24e--the-41-residual-parsec-continuation-edges) published.

**Back to M1 — the thunk sites.** The M1 table gains a fourth column, and
the invariant it exists to state is asserted:

```
Thunk sites explained by M2.4 (M1 × M2.2 × M2.3 × M2.4)
                                                      before  by tuples   by M2.3   by M2.4   after
  sinkable, lands in an evaluating position               14          0         3         0      11
  sinkable, lands in a lazy position                     254          3         3         0     248
  memoisation required                                  1905         89         5         0    1811
  recursive value                                         69          0         0         0      69
  potential thunk sites                                 2242         92        11         0    2139
```

`remaining + explained-by-tuples + explained-by-M2.3 + explained-by-M2.4 =
2,242` is asserted, as is *no site is counted twice*: a site an earlier
milestone explains is that milestone's, and this walk skips it before it can
claim it. The two earlier columns are read from `link::ThunkLink` and
`m23::RepLink` rather than recomputed.

**M2.4's column is 0, and the reason is a fact about the dump rather than a
missing rule.** The one rule
(`M24-D-DICTIONARY-BINDING-ERASED`) is: a `$d…` binding whose right-hand
side is a saturated application of a dfun the whole-program flow holds as a
dictionary identity, and whose identity is `Erasable` with the verifier's
confirmation. The population and every refusal are printed:

| | | |
|---:|---|---|
| 152 | of the 2,242 thunk sites are `$d…` bindings (`Origin::Dictionary`) | the population this link draws on |
| 131 | name a dictionary the whole-program flow holds an identity for | …and **all 131** are `Preserve(used as an ordinary value)` |
| 18 | have a head the flow holds no identity for | not a dictionary M2.4c gave a verdict to |
| 3 | are a superclass selection (`$pN<Class> d`) | a *field of* a dictionary, not an identity of its own |
| 0 | are `Erasable` but unconfirmed | an unconfirmed claim is unsupported and never proven |

Every one of the 152 is `Memo` in M1's own table, and 131 of them build a
dictionary that `E4-ESCAPE` says is handed on as an ordinary value. A
dictionary that escapes keeps its box, so the binding that builds it keeps
its thunk. The number is 0 and it is a result.

### Across the flag matrix

| | A (`-O1`) | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| class-op sites / `Exact` | 565 / 7 | 587 / 7 | 595 / 7 | 595 / 0 | 595 / 0 | 596 / 0 |
| … dictionary bounded | 118 | 138 | 140 | 65 | 65 | 65 |
| boundaries | 5,574 | 6,347 | 8,082 | 34,094 | 31,686 | 31,701 |
| … enumerated / one representation / rewritable as one | 252 / 84 / 66 | 391 / 143 / 125 | 486 / 189 / 172 | 1,909 / 718 / 695 | 1,887 / 706 / 683 | 1,891 / 705 / 682 |
| dictionary values / parameters | 191 / 216 | 191 / 210 | 191 / 222 | 238 / 223 | 238 / 223 | 238 / 231 |
| clone plans (dictionary / closure) | 4 / 68 | 3 / 83 | 4 / 87 | 7 / 207 | 7 / 207 | 7 / 227 |
| claims / disagreements | 606 / 0 | 749 / 0 | 867 / 0 | 2,209 / 0 | 2,187 / 0 | 2,209 / 0 |
| M1 thunk sites explained by M2.4 | 0 | 0 | 0 | 0 | 0 | 0 |

The accounting closes on all seven dumps, and `rewritable ≤ one
representation ≤ enumerated` holds on all seven.

*The closure clone row is as
[M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)
recomputed it; M2.4g published 53 / 61 / 65 / 154 / 154 / 176, planning with
`Shape::short()` instead of `Shape::class()`. It is the only row that moved,
and it moved upward on every dump — the defect always under-counted.*

### The `h2r parsec` nondeterminism, fixed

[M2.4c′](#correction-m24c--totality-is-not-the-same-fact-as-identity)
recorded that `h2r parsec --explain` and `h2r parsec --json` differ run to
run, and [M2.4d′](#correction-m24d--sharing-is-decided-before-agreement-and-a-free-type-variable-identifies-nothing)
and [M2.4f](#m24f--re-deriving-the-m24-verdicts-independently) had to keep them out
of every byte-identity gate because of it. The cause is one line:
`Analysis::prove` walked `self.role`, a `HashMap<BinderId, RoleInfo>`, and
that walk order is the order every region's `edges`, `evidence` and
`rejects` come out in — hence the per-role line order in `--explain`, the
per-region `edges` order in `--json`, and the `e.g.` witness of a reject
reason, which is whichever reject was pushed first.

Sorting that walk by the binder fixes all three. It is a **report-order
change only**: nothing in the proof depends on the order, and every count is
an aggregate over all of it.

* **the counts are unchanged.** Apart from the `e.g.` exemplar lines,
  `parsec --explain` is line-for-line **multiset identical** before and
  after on all seven dumps, and `parsec --json` is identical on all seven
  once each region's `edges`, `evidence` and `rejects` lists are
  canonicalised — the exact comparison M2.4f had to make. `h2r parsec`
  itself is **byte-identical on `-O1`, A and D**, and on B, C, E and F it
  differs in **exactly one `e.g.` exemplar line** — the same reject reason
  (`arg-of-unrecognised-call`, `cont-in-non-cont-slot`, `cont-wrong-arity`)
  with a different witness and the same count. `parsec --explain` differs
  in two such lines on C and one on E and on F, and in none on the other
  four. That is the wobble itself: the old binary picked a witness at
  random, so the *before* capture is one of several outputs it could have
  produced, and the new one always picks the lowest-numbered role binder's.
  The 41-row M2.4e table is byte-identical on every dump.
* **two runs are now identical.** Three consecutive runs of `h2r parsec`,
  `parsec --explain` and `parsec --json` on `-O1`, on B and on C give
  **one md5 each — nine hashes for twenty-seven runs**. Against the same
  three runs of the *unchanged* binary on B, `--json` and `--explain` give
  **three distinct hashes each**, which is the defect being measured rather
  than assumed.

Those two reports can now carry a byte-identity gate, and this milestone is
the first to put them under one.

### Correction (M2.4h) — four defects the owner's review of M2.4 found

Four defects in `e2055bc`, found by the project owner's review of the
published work and not by a failing test. Three of them are the analysis
claiming more than its evidence; the fourth is a proof object answering the
wrong question. Every one is in the same direction as the earlier
corrections, and one of them the **verifier had copied rather than
derived** — which is a defect in the verification and not only in the
analysis.

| | what was wrong | what it moved |
|---|---|---|
| **1** | three defects in the totality domain, in `dictflow.rs` **and** reproduced in `verify_m24.rs`: every alternative binder counted as *already evaluated*; the totality join kept one obligation and lost the rest; an applied `case`/`let` head was peeled, dropping its arguments | no verdict on any of the seven dumps, and `dictflow`'s report is byte-identical on all seven — but the first shape occurs **6,625** times in `-O1` and misses every verdict only because none of them sits on a dictionary path, where the totality transfer reaches no `case` at all. Each defect now has a hand-built counterexample and a counted row (16–18) |
| **2** | `H15-OWNER-CLONES` deduplicated clone tuples with `Shape::short()` — arity and capture **count** — contradicting `Shape::class()`, which is what every other part of M2.4d calls a representation | closure clones **53 → 68** on `-O1`, and up on every dump: 61 → **83** (B), 65 → **87** (C), 154 → **207** (D and E), 176 → **227** (F). The verifier's independent recount agrees on all seven |
| **3** | a clone-plan claim carried only its cardinality and an `ErasableWithObligation` claim carried no obligation at all, so `check_plan` compared `tuples == n` and a different plan of the same size passed | no number; the claim protocol and two refusal reasons are new, and `[verified: yes]` now requires a content-checked claim |
| **4** | `parsec::residual_edges` gated target enumeration on the *representation* verdict, admitting three verdicts and refusing `CloneRequired` | still **0 closed** on all seven dumps, and the 41-row `-O1` table keeps every other column — but on C, D, E and F four edges per profile that the old rule refused as `boundary-CloneRequired(8)` are now asked the role question and refused by it instead, and every status names the enumeration answer with the verdict beside it |

#### 1 — the totality domain, three defects, and a verifier that had copied them

**(a) an alternative binder is not already evaluated.** `is_already_evaluated`
returned `true` for `BindSite::CaseBinder | BindSite::AltBinder`. The
scrutinee binder is sound: it could not be named before the scrutinee was
forced. The alternative binder is not. Matching `P d` forces `P`, not `d`,
and if the field is lazy then `d` is an unevaluated thunk — so a `case` on
`d` deletes an evaluation that erasure would have to put back. Both walks
now admit only the scrutinee binder, the binder of a field GHC's own
`strictFields` marks strict, and the values they already admitted; a
constructor the dump does not carry, or one whose source-field strictness
vector and representation arity disagree, contributes no strict field at all
rather than a guess. `an_alt_binder_of_a_lazy_field_is_not_already_evaluated`
and its strict twin pin both directions.

**(b) an obligation set is a set.** `Tot::join` kept the lexicographically
smallest `ForceObligation` and dropped every other one, so a dictionary
standing behind two distinct forces was erasable against one of them and the
second force disappeared with it. An obligation is a proof debt, not a
witness to be chosen. `Tot` now carries a `BTreeSet<ForceObligation>`, the
join is a **union**, and `ErasableWithObligation` carries the whole set;
`dictflow`'s accounting gained `named_forces` beside `obligations` because
one verdict can now carry several. `every_force_obligation_survives_the_join`
builds two call sites forcing different scrutinees and requires both.

**(c) an applied `case`/`let` head is not its alternatives.** `eval_nested`
and `tot_nested` matched `Expr::Case`/`Expr::Let` in head position and
walked into the alternatives — but `m.spine()` puts the *outer value
arguments* in `args`, and `(case x of A -> f; B -> g) d` is not
`case x of A -> f; B -> g`. Peeling it answered about an expression `d` had
been dropped from. Pushing the arguments through would mean building Core,
which this compiler never does, so both walks refuse:
`case-or-let-head-with-outer-value-arguments`, a `Top` for the set and
`Unknown` for the totality.
`a_case_head_with_outer_arguments_is_refused_not_peeled` builds exactly that
shape with `d` the dictionary, and pins that the old walk's answer — the
two-element set `{$fShowT, $fShowU}` for an expression whose value is
neither — is now a refusal.

**In the dump.** Each shape is now searched for over the whole closed world
and counted by `h2r verify-m24` (rows **16**, **17** and **18**), so that the
hand-built counterexamples are not the only evidence the corrected rules were
exercised, and so that a zero is a fact about the dump rather than about
where the walk looked:

| row | shape | `-O1`/A | B | C | D | E | F | example on `-O1` |
|---:|---|---:|---:|---:|---:|---:|---:|---|
| 16 | a `case` on the alternative binder of a **lazy** field | **6,625** | 7,539 | 7,570 | 12,372 | 11,348 | 11,287 | `Main` node 518 |
| 17 | …the same, on a **GHC-strict** field's binder | 168 | 204 | 222 | 459 | 339 | 339 | `ShellCheck.ASTLib` node 8186 |
| 18 | a `case`/`let` head carrying outer value arguments | **0** | **0** | **0** | **0** | **0** | **0** | — |

Defect (a) was therefore **live in the program** — 6,625 of the 6,793
alternative-binder scrutinees in `-O1` bind a lazy field and were being read
as already evaluated, against 168 that really are — and the only reason no
verdict moves is that none of the 6,625 sits on a **dictionary** path: the
totality transfer reaches **0** `case` nodes there at all, the instrumented
fact M2.4c′ recorded and M2.4f re-derives on every run. "It did not matter
here" is not "it was right": the rule was stated in the report, it was wrong
as stated, and 6,625 is how much of this program it was wrong about.

Defects (b) and (c) have nothing to bite on for the same reason, and (c)
additionally because shape 18 is itself zero: 0 verdicts carry more than one
obligation,
`MustPreserveForce` is still 0 of 216, and no expression in any of the seven
dumps applies a `case` or `let` head to value arguments. `dictflow`'s report
is **byte-identical** on all seven dumps.

**(d) the totality partition is asserted in its own right.**
`m24::Accounting::check()` asserted it only inside `ErasureRow::closes()`,
where a failure would have been reported as the whole erasure row not
closing. It is now its own equation with its own message:
`ProvenTotal + MustPreserveForce + Unknown = parameters` — 118 + 0 + 98 =
216 on `-O1`.

**And the verifier had copied all three.** `verify_m24.rs` claims to share
nothing with `dictflow.rs` but the IR and four named inputs, and for these
three points that was not true: its `already_evaluated`, its `TotFact::join`
and its `tot_eval` reproduced the analysis's decisions, defect included, so
the check agreed for the wrong reason. Each is now decided there on its own
terms — its own `alt_strict` map built from GHC's `strictFields`, its own
witness **set**, its own refusal of an applied head — and the module's
documentation says that these three were previously copied, because a
verifier that had copied a decision is a fact about the verification that
belongs in the record.

#### 2 — a representation class is arity *and* the capture types

`H15-OWNER-CLONES` plans one clone per distinct call-site assignment tuple.
Building the tuple, `component()` rendered each settled producer set with
`Shape::short()` — *arity and the number of captures* — and deduplicated on
that. `Shape::class()`, which is what `Boundary::classes`, `class_keys()`,
`one_representation()` and `H14-FREE-TYVAR` all mean by a representation, is
*arity and the ordered capture-type keys*. Two closures of the same arity
capturing the same number of differently-typed values are one variant under
`short()` and two under `class()`, and the plan used the wrong one — so it
under-counted the specialisations the lowering has to emit, which is the one
direction a clone plan must not err in.

The tuple component is `class()` now. `short()` survives as `tuples_short`,
display only, and the correction is visible in it: `ShellCheck.Fixer`
`$srealignColumn` has two call sites whose tuples both render as
`arity 1, 1 capture(s), arity 1, 1 capture(s)` and whose classes are
(type names abbreviated to their last component)

```
arity=1;captures=[!ShellCheck.Fixer#1181!F(C(Many),faYH6,C(Position))], arity=1;captures=[!ShellCheck.Fixer#1170!C(Ranged,faYH6)]
arity=1;captures=[!ShellCheck.Fixer#1225!F(C(Many),faYH6,C(Position))], arity=1;captures=[!ShellCheck.Fixer#1214!C(Ranged,faYH6)]
```

— two `H14-FREE-TYVAR` producer-private keys, which is exactly the
distinction `short()` erases. One clone before, two after.
`clone_tuples_use_the_full_shape_class_not_the_short_rendering` pins the
minimal version: two closures of arity 1 capturing one `T` and one `R`.

`verify_m24.rs`'s own planner had the same defect and is corrected
independently.

**Closure clones, per owning function, before → after (`-O1`):**

| module | owning function | plans | clones before | clones after |
|---|---|---:|---:|---:|
| `ShellCheck.ASTLib` | `$sgetLiteralStringExt` | 1 | 2 | 2 |
| `ShellCheck.Analytics` | `$srunNodeAnalysis` | 1 | 3 | **5** |
| `ShellCheck.Analytics` | `analyse` | 1 | 2 | 2 |
| `ShellCheck.Analytics` | `doVariableFlowAnalysis` | 1 | 3 | 3 |
| `ShellCheck.CFGAnalysis` | `go15` | 2 | 6 | 6 |
| `ShellCheck.CFGAnalysis` | `go4` | 1 | 3 | 3 |
| `ShellCheck.Checks.ShellSupport` | `go1` | 1 | 3 | 3 |
| `ShellCheck.Fixer` | `$srealignColumn` | 1 | 1 | **2** |
| `ShellCheck.Parser` | `$wisFollowedBy` | 1 | 1 | **4** |
| `ShellCheck.Parser` | `$wpoly_k` | 1 | 3 | **4** |
| `ShellCheck.Parser` | `$wreadIoVariable` | 1 | 2 | 2 |
| `ShellCheck.Parser` | `k` (eight distinct binders) | 8 | 23 | **30** |
| `ShellCheck.Parser` | `readAmbiguous` | 1 | 1 | **2** |
| **total** | | **21** | **53** | **68** |

Six of the thirteen owning functions move and seven do not; the refusals do
not move either (66 of 87 owners still refuse rather than guess), the
per-parameter class cardinality is still 509 and is still evidence rather
than a count, and the eight plans with a set-valued component are still
lower bounds. `h2r verify-m24` re-derives all 21 plans from its own walk
with **0 disagreements**, so 68 is two independent counts and not one.

#### 3 — a claim has to carry what the check needs

`m24_claims.rs` wrote a clone plan down as a cardinality — `n` — and
`verify_m24::check_plan` compared `p.tuples == c.n`. A plan with completely
different variants of the same size therefore re-derived as agreeing, which
is a check of arithmetic and not of a plan. An `ErasableWithObligation`
claim carried no obligation at all, so the check could compare only the
verdict *label*: an obligation at the wrong node would have passed.

A claim now carries its content:

* **`Claim::groups`** — the plan as a **partition of the owner's call
  sites**, one entry per planned clone, each site by address
  (`Module#node`), rendered by one shared `group_lines`. This is the content
  of a clone plan that survives being derived twice: *which call shares a
  clone with which*. It is compared for every plan.
* **`Claim::tuples`** — the deduplicated tuple set itself. For a
  **dictionary** plan the components are dictionary identities — addresses —
  and the set is compared directly. For a **closure** plan they are shape
  classes, and the two walks derive their capture keys independently and
  render them differently on purpose (`arity=1;captures=[…]` against
  `1/[…]`); comparing those strings would compare two renderings and not two
  facts, so the tuples are the record and `groups` is the check. Addressing
  is not sharing; rendering a derived fact would be.
* **`Claim::obligations`** — every force the verdict leaves to be
  discharged, as `Module#at forces what`, an address both sides build from
  their own derivation.

`check_plan` compares the partition, then the tuple set where its components
are addresses, then the cardinality **last** — agreeing about a number after
disagreeing about the content is the defect this corrects. Two new refusals
carry it: `X_GROUPS_DIFFER` and `X_TUPLES_DIFFER`, plus `X_OBLIGATIONS_DIFFER`
for the obligation set. And `m24.rs` will not print `[verified: yes]` for a
claim that carried no content to check: a clone-plan claim whose `tuples` or
`groups` do not have one entry per planned clone, or an
`ErasableWithObligation` claim with an empty obligation set, is refused with
`X_NO_CONTENT` rather than silently counted as proven.

Four tests make it bite, and all four corrupt the **content** while leaving
every count intact: `a_clone_plan_claim_with_swapped_tuples_is_refused`
reassigns the call sites between two planned clones and gets
`X_GROUPS_DIFFER`;
`a_dictionary_clone_plan_claim_with_swapped_tuples_is_refused` replaces one
tuple with a copy of the other and gets `X_TUPLES_DIFFER`;
`an_obligation_claim_with_a_changed_address_is_refused` moves the obligation
to a node that does not exist and gets `X_OBLIGATIONS_DIFFER`; and
`a_contentless_clone_plan_claim_is_never_marked_verified` strips the content
and keeps the count, and asserts the view no longer says `yes`. Each asserts
the refusal is a `D` and not a `C`.

#### 4 — enumeration and representation are different questions

`parsec::residual_edges` asks, of each of the 41 residual Parsec
continuation edges, whether the closure graph gives it a finite set of
continuation targets. It admitted `ExactClosure | TypeShapeUniform |
FiniteClosureSet` and refused `CloneRequired` — which is the exact
conflation `H11-SEPARATE` exists to prevent. Whether the producers are
**enumerated** and
whether **one representation** can serve them are two facts M2.4d records
separately. A `CloneRequired` boundary is enumerated — that is how its
clones could be counted at all — and its continuation-target set is exactly
as finite as an `ExactClosure` one; needing two representations says nothing
about how many targets there are.

The condition is now `bd.enumerated && every producer has a known
continuation role`, read from the recogniser's own `cont_source` as before.
The representation verdict is recorded beside every edge as evidence
(`representation verdict …`) and gates nothing, and an unenumerated boundary
gets the new status `boundary-producer-set-is-not-enumerated`, naming the
verdict inside the parentheses rather than in place of the answer.

**The 41-row table is recomputed and still closes 0.** Every one of the 41
boundaries is `Unresolved` and therefore unenumerated — 20
`parameter-of-an-anonymous-lambda`, 19 `function-used-as-a-value`, 2
`call-site-is-a-partial-application` — so none of them could have closed
under either condition, and the rule never reached the role question. What
changed is that the table now says *why* in the terms of the question it
asked. The count is the same as M2.4e published, and it was the same for a
different reason: the old rule refused these 41 by verdict, and on `-O1` the
verdict happened to be the same `Unresolved` that also means unenumerated.

**On four of the six matrix profiles the two part.** On C, D, E and F —
every profile built with `-fno-full-laziness` — **four** residual edges sit
on a boundary the closure graph calls `CloneRequired(8)`: enumerated, eight
shape classes. The old rule turned those four away on the representation
verdict and never asked the role question. The corrected rule asks it, and
all four fail it: `producer-is-not-a-region-continuation` goes from 1 to
**5** on each of the four, and the `boundary-CloneRequired(8)` row
disappears. The closed count is still 0 on all seven dumps, so no verdict
moves — but four edges per profile are now refused for a reason about
*continuations*, which is the question M2.4e set out to ask, instead of for a
reason about *representations*, which is not. That is the defect showing
itself in real dumps and not only in a fixture, and it is why "nothing moved
on `-O1`" was not enough to leave the condition alone.

**And the rule now fires where it could not.**
`residual_edge_closes_through_a_clone_required_boundary` builds the case the
old condition refused by name: one region whose `cok` boundary has two
producers, both nested regions of **known role**, whose representations
disagree — `CloneRequired(2)`, and enumerated. The edge closes with
`P-HO-FINITE`, and the test asserts that the representation verdict is
present in the evidence as `representation verdict CloneRequired(2)` rather
than as the answer. `residual_edge_at_an_unenumerated_boundary_says_so` pins
the other direction. Both are new, and they are what makes this more than a
rewording where the dumps are silent: on `-O1` and A no edge changes its
answer, because the wall M2.4e found there is the anonymous-lambda wall and
not a representation one, and the fixture is the only place the corrected
rule can be seen firing.

*(`parsec.rs` carries **29** unit tests of its own — 27 before these two;
M2.4e's text called one of them "the" regression test. That is corrected
above.)*

#### The gate for this correction

**312 reports** were captured over the seven dumps before and after —
`stats`, `laziness`, `tuples` (plus `--verify`, `--scalar-all`,
`--boundaries`), `fields`, `lists` (plus `--axioms`), `text` (plus
`--heads`, `--explain`), `verify-rep` (plus `--explain`), `parsec` (plus
`--explain`, `--cfg-all`), `classops` (plus `--per-module`, `--view-all`),
`dictflow` (plus `--explain`), `higher` (plus `--view-all`), `verify-m24`
(plus `--explain`), `m24`, `compare`, three `show` nodes and the `--json`
form of each. **214 are byte-identical**, **98 moved**, and every one of the
98 is a report this correction was allowed to move; every run's standard
error was captured too and is identical on both sides everywhere.

The 98 are fourteen reports × seven dumps, and nothing else:

| report | lines moved (`-O1` … F) | what moved |
|---|---|---|
| `classops` | 2 | the one closure-clone line of the accounting block it shares with `higher` |
| `classops --json` | — | the `named_forces` key, added; no existing value |
| `dictflow --json` | — | `obligation` → `obligations` on values and parameters (empty on every dump), plus `groups` on each clone plan and `named_forces`; **no existing value changes** |
| `higher` | 52 … 70 | the clone-plan table: 53 → 68 and the per-owner rows that produced it |
| `higher --json` | 1 | `owner_clones`, and nothing else |
| `higher --view-all` | 20 | the clone tuples in each boundary view, now the full shape class |
| `m24` | 8 … 9 | the closure-clone row, and the three `parsec` residual status lines |
| `m24 --json` | — | the same two, in `accounting.erasure.plans` and `m21ResidualEdges` |
| `parsec`, `parsec --explain` | 135 … 1,007 | every residual edge's status string, plus one `representation verdict …` evidence line each |
| `tuples --verify` | 6 … 7 | the same residual summary, which this report prints in brief |
| `verify-m24`, `--explain`, `--json` | 3, and 5 on E and F | the three appended shape rows (16–18); on E and F also row 12's exemplar, `Main $s$wgo1` 1 → 2 tuples, which is the H15 correction again |

Everything else is **byte-identical on all seven dumps**, including
`dictflow` itself (the totality corrections move no verdict), `parsec
--json` and `parsec --cfg-all` (the residual section is not in either),
`classops --per-module` and `classops --view-all`, `tuples`, `fields`,
`lists`, `text`, `verify-rep`, `compare`, and all three `show` nodes with
their M2.4 footers.

No Core is mutated, no codegen is emitted, no GHC flag changed, no
`rust-port` file is touched. `cargo test` is **243** (eleven new: one per
defect in the totality domain and its strict twin, one for the shape class
against the short rendering, three for a claim whose contents are corrupted
while its counts are preserved, one for a claim with no content at all, and
two for the corrected `parsec` condition), `cargo clippy
--all-targets` 0 warnings and `cargo fmt --check` clean.

### M2.4 acceptance

*(Every count below is as M2.4g measured it, with
[M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found)'s one
moved number — 53 planned closure clones → **68** — folded in.)*

**The criterion is that the three questions are answered separately, that
every positive answer is re-derived by a walk that shares nothing with the
first but the IR and four named trusted inputs, and that every residual is
itemised and owned.** Not that coverage is high: on this program it is low, and the
milestone's contribution is knowing exactly why.

**Question 1 — can the call target be enumerated?** `sites = Exact +
FiniteSet + Unresolved` closes on all seven dumps.
[7 of 565](#m24c--whole-program-dictionary-flow-and-whether-the-dictionary-can-go)
on `-O1`, and **0 per module**: GHC's simplifier has already taken every
site whose dictionary is visible, so what survives is dispatch on a run-time
parameter. The closed-world fixpoint bounds the *dictionary* at 118 sites
and at 106 of the 216 parameters, which is a different and larger result
than the seven targets, and the accounting prints it as a separate fact.
[The residual table above](#the-milestone-accounting--three-questions-never-collapsed)
itemises all 558, and the largest row — 413 — is not a weakness of the walk
but `W0` biting: those sites live in bindings nothing in the closed world
references.

**Question 2 — can this abstraction boundary use one representation?**
`boundaries = ExactClosure + TypeShapeUniform + CloneRequired +
FiniteClosureSet + Preserve + Unresolved` closes on all seven dumps.
There are **three** counts here and M2.4d′ had to separate them: 252
boundaries have an enumerated producer set, 84 satisfy the *one* statement
of the theorem (`Boundary::one_representation` — enumerated, one shape
class, no opaque producer), and 66 are `rewritable_as_one`, which
additionally requires the rewrite to own the slot. The accounting prints all
three side by side and asserts the inclusion. 4,613 of the 5,322
`Unresolved` are the Parsec CPS wall.

**Question 3 — can the object actually disappear?** `values = Erasable +
WithObligation + WithClone + Preserve + Unresolved` and the same for
parameters, both closing on all seven dumps, with the totality domain's
118/0/98 asserted to sum to 216 beside them. Erasure is computed from facts
recorded **separately** from the targets and crossed with them in the 3×5
matrix rather than collapsed. Both clone plans are **owner-level** —
distinct call-site assignment tuples, never the sum of per-slot
cardinalities — and every plan with a set-valued tuple is flagged as the
lower bound it is.

**The verifier.** `h2r verify-m24` re-derives **606** positive claims on
`-O1` (749 / 867 / 2,209 / 2,187 / 2,209 on B–F) with **0 disagreements and
0 coverage refusals on all seven dumps**, and reproduces every published
table cell for cell on a walk that has never seen them. Two tests make it
bite. Every number in this section is the verifier's own or carries its
answer beside it.

**The corrections history.** Three, all found by review of the published
work rather than by a failing test, and all in the direction of the analysis
having claimed more than its evidence:

| | what was wrong | what it moved |
|---|---|---|
| [M2.4c′](#correction-m24c--totality-is-not-the-same-fact-as-identity) | `Erasable` was decided from *bounded dictionary identity*, which a MAY-analysis over a `case` gives without the producer being total; and the per-parameter clone cardinalities were summed | no verdict moved (`MustPreserveForce` is 0 because `-O1` floats every dictionary out of every scrutinee — an instrumented fact, re-derived by M2.4f) and 8 clones → **4** |
| [M2.4d′](#correction-m24d--sharing-is-decided-before-agreement-and-a-free-type-variable-identifies-nothing) | six defects: `H8` decided after `H5`/`H6`; two different one-representation theorems and opaque shapes merging; per-parameter clone counts summed; free type variables merging unrelated closures; existential fields indexed by raw binder position; `UniformRepresentation` named a Rust fact it is not | `ExactClosure` 67 → **50**, `Preserve` 26 → **44**, one representation 103 → **84**, rewritable 87 → **66**, shape classes 261 → **353**, clones 418 → **53** (→ **68** in M2.4h) |
| [M2.4f](#the-one-correction-this-produced) | the *record*, not a verdict: M2.4d′ said ShellCheck's Core has no alternative binding a function-typed field after an existential type binder. It has four | no number moved; the prose was corrected and the shape is now counted on every run (rows 11 and 11a) |
| [M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found) | four: three in the totality domain (every alternative binder read as already evaluated, the obligation join keeping one of a set, an applied `case`/`let` head peeled) which `verify_m24.rs` had **copied rather than derived**; clone tuples deduplicated by arity-and-capture-count instead of by representation class; a claim protocol that carried counts where the check needed contents; and `parsec::residual_edges` gating target enumeration on the representation verdict | closure clones 53 → **68**; nothing else moved as a number — the three totality shapes are absent from all seven dumps and the 41 Parsec edges still close **0** — but the claim protocol, two refusal reasons and the `parsec` status column are new |

**Trusted inputs and assumptions, named.** The first four are the trusted
inputs: consulted and never verified, on both sides of the M2.4f check, and
printed at the top of every `verify-m24` run. The last two are assumptions
the *verdicts* rest on rather than inputs either walk reads.

1. **the 17-class method-field table** (`classops::CLASSES`), a level-5
   axiom: format 5 carries neither a type nor an unfolding for a global, so
   a selector's `C a => …` type and its `case d of C:C … m … -> m` body are
   both absent and the field order is **not derivable from the dump at
   all**. Every *use* of the table is re-derived, including the cross-check
   against the dictionary constructor's own `repArity` — 0 disagreements and
   0 classes outside the table on all seven dumps;
2. **`W0-CLOSED-WORLD` / `H0-CLOSED-WORLD`** — the 28 modules are the whole
   program and `Main.main` its only root. An assumption about the *build*,
   which no walk can prove, and the one 413 of the 558 unresolved sites rest
   on;
3. **GHC's own flags** — `isClassOpId`, `isExportedId` and the demand
   signatures' strictness bits, read from the authoritative source;
4. **the structured `Ty`** and `TyCon` stable-name identity (format 5);
5. **free type variables are compared by GHC unique** in `Ty::alpha_eq`, and
   a unique is not an identity in optimised Core. `H14-FREE-TYVAR` keeps the
   *shape class* off that — a capture type with a free type variable gets a
   producer-private key — but the IR predicate itself is unchanged and must
   not be handed a free-tyvar-sensitive proof;
6. **the M3 carrier invariant** behind `TypeShapeUniform`: the verdict is a
   fact about *Haskell* types (same arity, same ordered captured Haskell
   types). Reading it as *one Rust representation* is sound only if the
   lowering promises a canonical closure-boundary carrier per Haskell type
   with conversions inserted at the boundary. **That invariant is open**,
   and every `h2r higher` run says so.

**What remains, and who owns it.**

* **M3: `Main.main`-rooted reachability.** The 922 "unreachable" top-level
  bindings are the *zero-reference* subset under `W0` — a valid dead subset,
  but not a rooted transitive one: a binding referenced only by another
  unreachable binding is not in it. 413 of the 558 unresolved sites and 227
  of the unresolved boundaries rest on that subset, so the real dead set is
  larger and M3 has to compute it.
* **M3: the canonical closure carrier.** Until the lowering promises one,
  `TypeShapeUniform` is a Haskell-type fact and the 16 boundaries carrying
  it are not yet one Rust representation.
* **M3: a call-string analysis for the set-valued tuples.** 4 dictionary
  plans and 8 closure plans on `-O1` have a tuple with a set-valued
  component, because the fixpoint is monovariant (`W5`, `H3`). Their clone
  counts are lower bounds on both sides of the verifier — agreement about a
  bound, not a closing of it.
* **The anonymous-lambda naming pass.** 4,613 of the 5,322 unresolved
  boundaries, all 41 Parsec edges and five of the six largest M2.3 closure
  holders are one shape: `ShellCheck.Parser` is CPS, its continuations are
  anonymous lambdas passed as values, and a higher-order analysis that wants
  them has to name them first.
* **A future dump format: global types and unfoldings.** The class table is
  an axiom only because format 5 carries neither for a global. A format that
  did would make it **derivable**, and the one level-5 assumption that both
  sides of the M2.4f check share would go.
* **`Unresolved` and `Preserve` are not re-derived as claims** — the
  deliberate asymmetry, narrowed but not closed by M2.4f's whole-population
  table.

`cargo test` (**232** — seven new: the class-op view over a module, the
boundary view's rule order at a slot that is and is not exported, the
boundary view over a module, the accounting's three questions, the `show`
provenance with both opt-outs, the M1 link's invariant under a milestone
that already claims every site, and a planted refusal that must never be
reported as proven; **243** since
[M2.4h](#correction-m24h--four-defects-the-owners-review-of-m24-found), which
added eleven), `cargo clippy --all-targets` (0 warnings) and `cargo
fmt --check` are clean.

### The gate

**262 reports** were captured over the seven dumps before and after: **215
byte-identical**, 28 appended-only, 11 multiset-identical up to an `e.g.`
exemplar, 7 canonical-JSON-identical and one `show` that gains its footer.
Every existing report is **byte-identical** before and after, on
`compiler/core-json` and on all six matrix profiles — `stats`, `laziness`,
`tuples` (plus `--explain`, `--verify`, `--boundaries`), `fields`, `lists`
(plus `--axioms`), `text` (plus `--heads`, `--explain`), `verify-rep` (plus
`--explain`), `dictflow` (plus `--explain`), `verify-m24` (plus
`--explain`), `classops --per-module`, `compare` and the `--json` form of
each — with three deliberate movements and nothing else:

* **`classops` and `higher` gain the accounting section**, 85 lines
  appended after everything they already print, so **not one existing line
  moves** — the *after* file starts with the *before* file byte for byte,
  on all seven dumps and with `--explain`. Their `--json` gains no key at
  all, because the views are their own `--view`/`--view-all` reports, and
  `classops --per-module` gains nothing at all: that mode exists to
  reproduce M2.4b exactly.
* **`parsec --explain` and `parsec --json`** change *order* only —
  multiset-identical and canonical-JSON-identical on all seven dumps — and
  `parsec` itself changes one `e.g.` exemplar line on B, C, E and F, which
  is the nondeterminism being fixed rather than a report changing. All
  three are now stable across runs.
* **`show`** gains M2.4 marks and footers on nodes that have them —
  `ShellCheck.Parser 141341` gains one inline mark and an eight-line
  boundary footer, `ShellCheck.AST 5293` is unchanged because it has
  neither — and `--no-classops --no-higher` reproduces the previous output
  **byte for byte**.

`h2r m24`, `h2r classops --view/--view-all` and `h2r higher
--view/--view-all` are new commands. No Core is mutated, no codegen is
emitted, no GHC flag changed.

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
  [M2.4b](#m24b--the-closed-world-class-op-census) measured what is left:
  on every profile, **none** of the 565–596 class-op sites has a statically
  known dictionary, because a selector applied to a visible dfun is exactly
  what GHC has already rewritten.
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
