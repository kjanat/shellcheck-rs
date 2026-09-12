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
```

`gate` replays every `prop_` property in `src/ShellCheck/**/*.hs` (extracted
from the sources at run time, so there is no corpus file to go stale) and must
stay at 0 divergences. `fuzz` runs the same comparison over generated and
mutated shell; it is the only one of the two that can say anything about
parity, because `gate` only ever covers what upstream already wrote a test for.
A green `gate` with a divergent `fuzz` means the port is incomplete, not
correct.

Layout mirrors the Haskell modules one-to-one: `ast_lib.rs` = `ASTLib.hs`,
`data.rs` = `Data.hs`, `parser/` = `Parser.hs`, `analytics/` = `Analytics.hs`,
`checks/commands/` = `Checks/Commands.hs`, `checks/shell_support.rs` =
`Checks/ShellSupport.hs`. A check keeps its Haskell shape: a plain fn, a
`CommandCheck::new(Basename("x"), ..)`, or a `ForShell::new(&[Shell::Sh], ..)`.
Rules for every change there: one definition per helper (grep before adding
one), no blanket `#![allow(..)]`, every touched file clippy-clean, and a check
is only registered once both conformance commands agree about its codes.
