# ShellCheck → Rust: structural port with a conformance guarantee

This directory holds a from-scratch Rust port of ShellCheck, built to a hard
acceptance bar: **behavioural parity with the Haskell implementation, proven by
a conformance harness**, not by hand-checking.

## Goals

1. **Structural fidelity.** Module and type structure mirror `ShellCheck.*` so
   the port can be reviewed against the original and maintained alongside it.
2. **Conformance-driven.** A harness runs the Haskell **oracle** and the Rust
   **port** over the same corpus, both emitting `--format=json1`, and diffs the
   diagnostics (code, severity, span, message, autofix, order). Parity per rule
   is a number, tracked in `harness/coverage.json`.
3. **Reusable core.** The analyzer is a pure, IO-free library crate
   (`shellcheck-rs`) so a language server or editor integration can embed it and
   get diagnostics-with-ranges directly. CLI, option parsing, and text
   formatters live in a separate consumer crate (`shellcheck-cli`).
4. **Latest Rust, edition 2024.**

## Workspace layout

```
rust/
  Cargo.toml                     # workspace (resolver 3, edition 2024)
  crates/
    shellcheck-rs/               # CORE library (LSP-embeddable, std + regex)
      src/interface.rs           # ShellCheck.Interface  (Position, Comment, Fix, Shell, specs)
      src/ast.rs                 # ShellCheck.AST         (Token/InnerToken, traversal)
      src/astlib.rs              # ShellCheck.ASTLib      (getLiteralString, oversimplify, ...)
      src/regex.rs               # ShellCheck.Regex
      src/parser.rs              # ShellCheck.Parser      (recursive descent)
      src/analyzer_lib.rs        # ShellCheck.AnalyzerLib (Parameters, Checker, warn/err/...)
      src/analytics.rs           # ShellCheck.Analytics   (node/tree checks: SC2xxx)
      src/checks/commands.rs     # ShellCheck.Checks.Commands
      src/checks/control_flow.rs # ShellCheck.Checks.ControlFlow
      src/checks/shell_support.rs# ShellCheck.Checks.ShellSupport
      src/cfg.rs, cfg_analysis.rs# ShellCheck.CFG / CFGAnalysis
      src/checker.rs             # ShellCheck.Checker     (pipeline glue)
      src/fixer.rs               # ShellCheck.Fixer
    shellcheck-cli/              # CLI + formatters (consumer of the core)
      src/bin/shellcheck.rs
      src/formatter/{tty,json,json1,gcc,checkstyle,diff,quiet}.rs
    conformance/                 # in-process harness driver (optional)
  harness/
    extract_corpus.py            # prop_ tests -> corpus.json (exact, via GHCi eval)
    corpus.json                  # 1600+ exact input scripts + per-rule metadata
    run_conformance.py           # oracle vs port json1 diff -> coverage.json
    goldens.jsonl                # cached oracle output per corpus id
    coverage.json                # per-code parity dashboard
```

## The pipeline (mirrors `ShellCheck.Checker.checkScript`)

1. **Parse** (`parser`): source → `Token` AST + `Map<Id,(Position,Position)>`
   span map + SC1xxx parse comments. Parser *notes* are non-fatal and dropped if
   parsing fails; parser *problems* are always emitted.
2. **Analyze** (`analyzer_lib` + `analytics` + `checks`): walk the AST, emit
   `TokenComment { id, comment, fix }` (SC2xxx/SC3xxx). Context (shell flags,
   linear dataflow, id/parent maps, CFG) is precomputed into `Parameters`.
3. **Resolve + filter + sort** (`checker`): map each `TokenComment`'s id to a
   span, filter by severity / `--include` / `--exclude` / inline directives,
   `nub` (dedup identical), then sort by
   `(file, line, column, severity, code, message)`.

### Data model notes

- `Token = { id: Id, inner: Box<InnerToken> }`. **Equality ignores `id`** and
  compares `inner` structurally — matching Haskell's `instance Eq Token`. Many
  checks compare tokens for structural equality, so this is load-bearing.
- `InnerToken` is a ~110-variant enum whose variants hold `Token`/`Vec<Token>`
  children. `InnerToken::children()` yields child refs in Haskell `Traversable`
  order; `Token::visit_preorder` reproduces `doAnalysis` (parent-before-children).
- `Severity` derives `Ord` in declaration order (`ErrorC < WarningC < InfoC <
  StyleC`) to match Haskell's derived `Ord`, used for `--severity` filtering and
  output sorting.

## Conformance methodology

- **Oracle**: `shellcheck` built from *this* repo HEAD (not a release binary),
  so parity is against the exact tree being ported.
- **Corpus**: every `prop_*` input across the source (1600+ snippets), decoded
  exactly by evaluating each Haskell string expression in GHCi. This exercises
  every rule by construction. Real-world scripts can be appended later.
- **Comparison**: both tools emit `json1`; comments are compared as multisets on
  `(line, column, endLine, endColumn, level, code, message, fix)`. A corpus
  script is "exact" only if the port reproduces the oracle's comment set
  identically. Per-code counters track matched / missing / extra.
- **Definition of done**: `exact_pct == 100` over the corpus, and every distinct
  SC code present in the oracle output has `missing == 0 && extra == 0`. New
  behaviour is guarded by regenerating goldens from the oracle.

## Porting order (dependency-first)

interface/ast (done) → regex/astlib → parser → analyzer_lib → checker + json1 +
CLI (first end-to-end number) → checks fanned out per module/code, each gated by
the harness → formatters → fixer → CFG-dependent checks → iterate to 100%.
