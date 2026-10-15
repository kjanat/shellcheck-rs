<a name="idtop"></a>

# 11 Open items

As of 2026-10-15, from `DIVERGENCES.md`, the GitHub issues, `rust/PERF.md` and the branch files.

## 11.1 Port defects

`DIVERGENCES.md` has no open entry. The last recorded wide fuzz runs (seeds 0, 1013, 148, 156) found zero distinct divergences. The oracle crashes on one input of seed 0; that is an upstream defect, counted separately.

**[⬆ Top](#idtop)**

## 11.2 Issue #3: diagnostic bugs and conformance gaps

[Issue #3](https://github.com/kjanat/shellcheck-rs/issues/3) has these boxes still open:

- Report the `coproc` and `$'\U110000'` crashes to upstream Haskell. The October 13 comment adds a reproducer: with `-x` and `lib.sh` present, `` echo `. ./lib.sh` `` and a here-document body holding `$(. ./lib.sh)` crash the oracle on the same `checkCmd` equation, since the last pipeline element is a `T_SourceCommand`.
- Report upstream's rejection of valid Bash `! # comment`.

`.claude/CLAUDE.md` names the same three upstream reports as unfiled. Once filed, each report's link goes into the issue and the matching `PARITY-NOTES.md` entry. The issue's investigation table records that upstream `master` was still `98deabe126a2` on October 11.

**[⬆ Top](#idtop)**

## 11.3 Issue #4: zed-editor comparison

[Issue #4](https://github.com/kjanat/shellcheck-rs/issues/4) keeps one box open: "Implement a carefully bounded SC2064 refinement, preserving warnings when values can change or leave scope before the trap runs." `docs/diagnostics.md` and the October 11 section of `PARITY-NOTES.md` describe an SC2064 exemption for plain variables assigned before the trap as shipped, and `crates/conformance/src/deviations.rs` holds no class for it. `.claude/CLAUDE.md` says the refinement is a divergence that follows the deviation procedure, or lands upstream first.

**[⬆ Top](#idtop)**

## 11.4 Documents

- `PARITY-NOTES.md` opens by naming one deviation class, `upstream-false-parse-error`. `deviations.rs` holds five: `upstream-false-parse-error`, `interpreter-path-typo`, `upstream-function-tail-cd`, `completed-statement-notes`, `unclosed-test-quote`. The rule in `.claude/CLAUDE.md` wants the header to list every class.
- `rust/PERF.md` still says `--jobs` defaults to 1; `README.md` says `rshellcheck` uses up to four CPUs by default.

**[⬆ Top](#idtop)**

## 11.5 Performance

`rust/PERF.md` lists WP-R5 (a deterministic `BTreeMap` order for `Ctx::invocations`) and the parser, CFG-build and check targets in [[Performance|07 Performance]].

**[⬆ Top](#idtop)**

## 11.6 Other branches

- `bench`: the Cabal build of the `upstream` candidate has run only in the unit test fixture; the first CI run after the baseline change proves the GHC install and build on the runner.
- `h2r-compiler`: `todo.md` lists the open compiler items in [[H2R Compiler|09 H2R compiler]]. No further work is planned there.

**[⬆ Top](#idtop)**

<a name="idend"></a>
