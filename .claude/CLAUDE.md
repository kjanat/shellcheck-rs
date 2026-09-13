# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and test commands

```sh
cabal build                          # compile
cabal test                           # run unit tests (source of truth)
cabal run shellcheck -- file.sh      # run on a file
cabal run shellcheck - <<< 'cmd'     # run on inline input
./quickrun - <<< 'cmd'               # run interpreted (fast, no recompile)
./quicktest                          # run tests interpreted (fast, no recompile)
./nextnumber                         # print next available SC1xxx/SC2xxx/SC3xxx code
```

For interactive development, use `cabal repl` then `:load ShellCheck.Debug`. After editing, reload with `:r` and test with `shellcheckString "your shell code"`.

To inspect the AST without an interactive session:

```sh
cabal run -fdev-mode shellcheck-dev -- ast 'myshellcommand'
```

## Architecture

ShellCheck processes shell scripts in three stages:

1. **Parsing** (`Parser.hs`) — produces an AST plus warnings (SC1xxx). Parser notes (non-fatal) are buffered and discarded if parsing fails; parser problems (fatal) are always emitted.
2. **AST Analysis** (`Analytics.hs`, `Checks/`) — walks the AST and emits warnings (SC2xxx/SC3xxx).
3. **Output** (`Formatter/`) — formats results as TTY, JSON, GCC-style, diff, etc.

### Key source files

| File                                      | Purpose                                                           |
| ----------------------------------------- | ----------------------------------------------------------------- |
| `src/ShellCheck/AST.hs`                   | Token type definitions (the AST node types)                       |
| `src/ShellCheck/ASTLib.hs`                | Helpers for working with AST nodes (e.g. `getLiteralString`)      |
| `src/ShellCheck/Analytics.hs`             | Main analysis: `treeChecks` and `nodeChecks` lists                |
| `src/ShellCheck/AnalyzerLib.hs`           | Shared utilities for check authors (`warn`, `err`, `style`, etc.) |
| `src/ShellCheck/Checks/Commands.hs`       | Per-command checks (dispatched by command name)                   |
| `src/ShellCheck/Checks/ShellSupport.hs`   | Shell-specific checks (dispatched by shell dialect)               |
| `src/ShellCheck/Checks/ControlFlow.hs`    | Control-flow / CFG-based checks                                   |
| `src/ShellCheck/CFG.hs`, `CFGAnalysis.hs` | Control-flow graph construction and analysis                      |
| `src/ShellCheck/Parser.hs`                | The Parsec-based shell parser                                     |
| `src/ShellCheck/Interface.hs`             | Public API types (`CheckResult`, `PositionedComment`, etc.)       |
| `src/ShellCheck/Debug.hs`                 | Dev helpers: `stringToAst`, `shellcheckString`, etc.              |

### Adding a check

Most checks live in `Analytics.hs` as either:

- **Node checks** — run on every AST node; append to `nodeChecks`.
- **Tree checks** — run once on the root; append to `treeChecks`.

Checks are pure functions `Parameters -> Token -> Writer [TokenComment] ()`. Use `warn`, `err`, `info`, or `style` from `AnalyzerLib.hs` to emit diagnostics.

Each check should have `prop_` unit tests immediately above it:

```haskell
prop_checkFoo1 = verify   checkFoo "bad shell code"
prop_checkFoo2 = verifyNot checkFoo "good shell code"
```

`cabal test` auto-discovers all `prop_` functions. Tests must pass before submitting.

Command-specific checks go in `Checks/Commands.hs`; shell-dialect-specific checks go in `Checks/ShellSupport.hs`.

### AST conventions

Always use the sugared pattern aliases when matching or constructing AST nodes, e.g. `T_Literal id str` or `T_IoFile id op filename`. Never use the desugared internal classes like `OuterToken (Id id) (Inner_T_Literal str)` — those are GHC's internal representation and should not appear in check code.

### Guidelines

- Add unit tests for new and updated checks; cover both positive and negative cases.
- Keep changes targeted — avoid sweeping refactors to propagate new data.
- Account for equivalent command forms (e.g. `echo > foo bar` vs `echo bar > foo`).
- Always verify `cabal test` passes cleanly.
- Verify new and modified checks end-to-end via `cabal run shellcheck - <<< 'bad code'` (or `./quickrun`) to confirm the warning fires as expected.

## Rust port (`rust/`)

A structural port of the Haskell code lives in the `rust/` workspace and is
gated against the Haskell binary as an oracle. Toolchain via `mise` (`mise.toml`).

```sh
cargo lint                                   # clippy, -D warnings; must be clean
mise run fmt                                 # dprint; run before committing
cargo test --workspace                       # prop_ tests ported from the Haskell
cargo build --release                        # target/release/rshellcheck

# Conformance, both against the Haskell binary as an oracle:
cargo run --release -p conformance -- gate --oracle .cache/shellcheck-oracle
cargo run --release -p conformance -- fuzz --oracle .cache/shellcheck-oracle

# External validity: both tools against the shells themselves (bash, dash,
# ksh93, busybox sh via `-n`). Needs those interpreters installed; a missing
# one is reported, never silently skipped.
cargo run --release -p conformance -- shells --iterations 300

# Where the port rewinds over a commitment instead of using a `try`. Needs no
# oracle, but does need a debug build: the instrumentation is behind
# debug_assertions, so do NOT pass --release.
cargo conformance-audit

# Refactor safety net (no oracle needed). See "Before refactoring" below.
mise run snapshot          # did any observable behaviour change? (--write to re-freeze)
mise run coverage          # what the snapshot corpus exercises, per file
mise run mutants -- --file rust/crates/shellcheck-rs/src/cfg.rs
```

`cargo conformance-*` aliases live in `.cargo/config.toml`; everything runs from
the repository root, which is the Cargo workspace root (`members = ["rust/crates/*"]`).

`gate` takes the shell script out of every `prop_` property in
`src/ShellCheck/**/*.hs` that has one (extracted from the sources at run time,
so there is no corpus file to go stale) and runs it through both tools' full
pipeline, comparing the whole json1 payload. It must stay at 0 divergences.

Two things it is not. It does not call the helper the property called
(`verifyTree`, `verifyCodes`, …), so it is a corpus *derived from* the upstream
properties rather than an execution of them. And it covers only the properties
with an extractable script — 2026 of 2252 definitions, the count its own banner
prints; the other 226 test the Fixer, the Checker's IO, `ASTLib` helpers and the
like, and have no shell to replay. (2252 definitions, 2238 distinct names: a
dozen names are defined in two modules, and both are replayed.)

`fuzz` runs the same comparison over generated and mutated shell; it is the only
one of the two that can say anything about parity, because `gate` only ever
covers what upstream already wrote a test for. A green `gate` with a divergent
`fuzz` means the port is incomplete, not correct.

Layout mirrors the Haskell modules one-to-one: `ast_lib.rs` = `ASTLib.hs`,
`data.rs` = `Data.hs`, `parser/` = `Parser.hs`, `analytics/` = `Analytics.hs`,
`checks/commands/` = `Checks/Commands.hs`, `checks/shell_support.rs` =
`Checks/ShellSupport.hs`. A check keeps its Haskell shape: a plain fn, a
`CommandCheck::new(Basename("x"), ..)`, or a `ForShell::new(&[Shell::Sh], ..)`.
Rules for every change there: one definition per helper (grep before adding
one), no blanket `#![allow(..)]`, every touched file clippy-clean, and a check
is only registered once both conformance commands agree about its codes.

### Before refactoring

The safety net today is that structure: the port reads like the Haskell, so a
divergence can be traced to a line in `Parser.hs`, and an invented condition
stands out as one. A refactor to idiomatic Rust gives that up, and then three
instruments are all that is left.

| Instrument | Question it answers                            |
| ---------- | ---------------------------------------------- |
| `snapshot` | Did any observable output change, anywhere?    |
| `coverage` | Which code does the corpus actually reach?     |
| `mutants`  | Would the tests have noticed if it were wrong? |

`snapshot` is what a refactor is gated on, and it is deliberately *not* a
comparison against the oracle: the port still diverges in places
(`DIVERGENCES.md`), so "still diverges identically" is success, and only a
record of the port's own behaviour can express that. `rust/snapshot.txt` holds
one line per input (2026 property scripts + 2000 generated, each checked in all
six dialect settings); the output hash decides the comparison, the codes, spans
and message hash beside it make the diff readable. Every `--write` claims that a
behaviour change was intended, so its diff belongs in the commit causing it.

`coverage` reports what that corpus reaches: 85.1% of regions and 84.7% of lines
of `shellcheck-rs`, against 82.7% for the unit tests alone. `mutants` answers
what coverage cannot -- 7499 mutants workspace-wide, so run it scoped or
sharded, and treat each survivor as a place the refactor could break silently.
