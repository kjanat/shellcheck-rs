<a name="idtop"></a>

# 2 Rust port

*Branch `rust-port`, [PR #1](https://github.com/kjanat/shellcheck-rs/pull/1).*

A structural, module-for-module port of the Haskell to Rust. The guiding principle: **the port reads like the Haskell**, so a divergence can be traced to a line in `Parser.hs`, and an invented condition stands out as one. Parity is enforced mechanically, not by review.

## 2.1 Layout

```
rust/
  PERF.md                      performance notes and work packages (see Rust Port Performance)
  snapshot.txt                 one line per corpus input: output hash + codes/spans/message hash
  crates/
    shellcheck-rs/             the library: parser/, analytics/, checks/{commands/,shell_support.rs},
                               cfg.rs, cfg_analysis.rs, analyzer_lib.rs, ast.rs, ast_lib.rs, data.rs,
                               checker.rs, interface.rs, formatter(s), idhash.rs
    shellcheck-cli/            the binary `rshellcheck` (same CLI surface as `shellcheck`)
    conformance/               the differential harness binary `conformance`
DIVERGENCES.md                 open port defects (currently none) and how to reproduce fuzz runs
PARITY-NOTES.md                upstream oddities reproduced on purpose, with shell evidence
.cargo/config.toml             cargo aliases
```

Haskell → Rust file mapping: `ASTLib.hs` = `ast_lib.rs`, `Data.hs` = `data.rs`, `Parser.hs` = `parser/`, `Analytics.hs` = `analytics/`, `Checks/Commands.hs` = `checks/commands/`, `Checks/ShellSupport.hs` = `checks/shell_support.rs`, `CFG.hs` = `cfg.rs`, `CFGAnalysis.hs` = `cfg_analysis.rs`, `AnalyzerLib.hs` = `analyzer_lib.rs`. A check keeps its Haskell shape: a plain `fn`, a `CommandCheck::new(Basename("x"), ..)`, or a `ForShell::new(&[Shell::Sh], ..)`.

Dependencies of the library: `regex` (mirrors regex-tdfa) and, since WP-R1, `im-rc` 15.1 (persistent `OrdMap`, MPL-2.0; GPL-compatible, flagged by Socket as license score 70). Everything else is std. The core is IO-free so an LSP or other tool can embed it.

**[⬆ Top](#idtop)**

## 2.2 The conformance harness

*`cargo run --release -p conformance -- <cmd>`.*

The oracle is the Haskell binary built from the same tree (`.cache/shellcheck-oracle` in CI; `--oracle PATH` or `ORACLE=` otherwise). The banner says MISMATCH if the oracle's version is not the tree's.

| command                                     | what it does                                                                                                                                                                              | invariant                                                                                                                        |
| ------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------- |
| `gate`                                      | extracts the shell script from every `prop_` in `src/ShellCheck/**/*.hs` (2026 of 2252) plus 22 optional-check examples, runs both tools' full pipeline, compares the whole json1 payload | **0 divergences**; prints `2048 agree, 0 diverge, 0 sanctioned deviations`                                                       |
| `fuzz --seed N --iterations K`              | generated + mutated shell through both tools; shrinks reproducers; survives oracle crashes (re-runs the batch one script at a time)                                                       | **0 divergences** for seed 0 ×2000 and the wide seeds in `DIVERGENCES.md` (1013, 148, 156 ×4000); CI uses the run number as seed |
| `shells --iterations N`                     | both tools against bash, dash, ksh93, busybox `-n`: external validity                                                                                                                     | a missing shell is reported, never skipped                                                                                       |
| `audit`                                     | where the port rewinds over a commitment instead of using `try` (needs a **debug** build)                                                                                                 |                                                                                                                                  |
| `snapshot [--write]`                        | freeze/check the port's own behaviour on 2026 property scripts + 2000 generated inputs × 6 dialect settings = 4026 entries                                                                | unchanged, or regenerated with the reason in the commit                                                                          |
| `bench --input FILE` / `--lines N --seed S` | per-phase in-process timing: parse, maps, cfg, params-other, checks, resolve (a residual)                                                                                                 |                                                                                                                                  |

In CI every finding is also a GitHub Actions annotation (via the `actions-rs` crate): `error` for a divergence pointing at the `prop_` file and line, `warning` for an oracle crash, `notice` for a sanctioned deviation.

**What the gate is not:** it replays the *script* a property names through the whole pipeline, not the helper (`verifyTree`, `verifyCodes`) the property called; and it covers only properties with an extractable script. A green gate with a divergent fuzz means the port is incomplete. The fuzzer is the only instrument that says anything about parity beyond upstream's own tests.

**Sanctioned deviations** (`rust/crates/conformance/src/deviations.rs`): the one class is `upstream-false-parse-error` (the oracle rejects a file, the port accepts it, and `<shell> -n` agrees with the port). Anything the harness cannot justify from shell evidence counts as a divergence; it fails closed.

**Refactor instruments** (`mise run snapshot | coverage | mutants`): snapshot gates every refactor (it is deliberately not an oracle comparison, so "still diverges identically" is success); coverage is 85.1 % regions / 84.7 % lines of `shellcheck-rs` from the corpus; `cargo mutants` has 7499 mutants workspace-wide, run it scoped.

**[⬆ Top](#idtop)**

## 2.3 Known parity facts

- Upstream oracle crash: `checkCmd` is non-exhaustive on `coproc` inside `$(...)`; the fuzzer reports it as an upstream defect, not a divergence.
- `PARITY-NOTES.md` lists upstream diagnostics that are wrong or strange, each run through bash 5.2.21 and dash 0.5.12 as the arbiter; most are reproduced on purpose.
- The latest two defects fixed (WP-R0, `a8266e6`, found by CI seed 156): a `time` flag word that fails after consuming input must commit the parse and fail, as Parsec's `many readFlag` cannot recover from a consuming failure; and `T_CoProc`'s `children()` must yield only the body, as Haskell's traversal of `Inner_T_CoProc (Maybe Token) t` does not visit the name.
- Command-check ordering: for two checks registered under one `CommandName`, the port runs them in registration order with `Exactly`/`Basename` interleaved, Haskell's `insertWith composeAnalyzers` runs the later-registered first and all `Exactly` before all `Basename`. It is unobservable because the final comment list is sorted; recorded in `rust/PERF.md` under WP-R4.
- Pre-existing nondeterminism (not observable today): `Ctx::invocations` in `cfg_analysis.rs` is a `HashMap<Vec<Node>, _>` with `RandomState`, iterated before merging the states of nodes reached from several call paths; Haskell's `M.Map` iterates by key. Fix proposed as WP-R5 (`BTreeMap`).

**[⬆ Top](#idtop)**

## 2.4 Rules for changing the port

*From `.claude/CLAUDE.md` and PERF.md.*

1. One definition per helper (grep before adding one); no blanket `#![allow(..)]`; every touched file clippy-clean under `cargo lint`.
2. A check is only registered once both conformance commands agree about its codes.
3. The CFG analysis is a port of `CFGAnalysis.hs`: keep versions, cache, invocation paths, merge/patch semantics and observable iteration order; **change representations, not the algorithm**.
4. Output parity: gate 0, fuzz 0 (seed 0 ×2000 at least; a new seed when in doubt), `-f gcc` and `-f json1` byte-identical to the oracle on the corpus scripts, snapshot unchanged or regenerated with a reason.
5. Add unit tests next to the code (`cargo test -p shellcheck-rs`, 1524 tests at `0c9cb40`); the Rust tests are the `prop_` tests ported plus the port's own.
6. `mise run fmt` (dprint) before committing; CI enforces it.

**[⬆ Top](#idtop)**

## 2.5 Fast loops

*Measured in the cloud container.*

| loop                                                                    |                time |
| ----------------------------------------------------------------------- | ------------------: |
| `cargo test -p shellcheck-rs`                                           | ~25 s (incremental) |
| `cargo build --release` (CLI + harness, thin LTO)                       |        40 s – 4 min |
| `conformance gate --quiet`                                              |               ~10 s |
| `conformance fuzz --seed 0 --iterations 2000`                           |             1–3 min |
| `conformance snapshot`                                                  |             seconds |
| byte parity on the four corpus scripts (sha256 of stdout, both formats) |             seconds |
| callgrind on `large.sh`                                                 |              ~1 min |

**[⬆ Top](#idtop)**

<a name="idend"></a>
