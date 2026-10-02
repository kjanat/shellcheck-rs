<a name="idtop"></a>

# 1 Repository overview

## 1.1 Branches

| branch         | base                                                                         | commits past master | purpose                                                                                                                                                                              |
| -------------- | ---------------------------------------------------------------------------- | ------------------: | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `master`       | upstream `koalaman/shellcheck` at [`9af7ee2`] (merge of upstream [PR #3445]) |                   0 | the Haskell ShellCheck 0.11.0 code, built with cabal; it is the **oracle**                                                                                                           |
| `rust-port`    | master                                                                       |                 211 | hand-written Rust port in `rust/` plus the conformance harness, `DIVERGENCES.md`, `PARITY-NOTES.md`, `rust/PERF.md`                                                                  |
| `h2r-compiler` | master                                                                       |                 179 | GHC-Core-to-Rust compiler (`compiler/`, `crates/h2r-*`), the generated-program layer crates (`crates/hs-*`, `crates/shellcheck-core`, `crates/rshellcheck`), `crates/h2r-rt/PERF.md` |
| `bench`        | master                                                                       |                   7 | benchmark harness in `bench/`, `.github/workflows/bench.yml`, archived results under `bench/results/`                                                                                |

[`9af7ee2`]: https://github.com/koalaman/shellcheck/commit/9af7ee28ce587baadd950b85dd6826a16b9c068d
[PR #3445]: https://github.com/koalaman/shellcheck/pull/3445

All three experiment branches keep the upstream Haskell tree in place (`src/ShellCheck/*.hs`, `ShellCheck.cabal`, `test/`) because every one of them builds the Haskell binary as its oracle. Each branch has its own `mise.toml` and `mise.lock`; the bench branch builds the other two in git worktrees using *their* lockfiles.

**[⬆ Top](#idtop)**

## 1.2 Pull requests

- **#1 "Scaffold Rust port, conformance harness, and corpus"** — `rust-port` → `master`, open since 2026-09-11. Has 22 unresolved review threads from an automated review bot on 2026-09-11; the author answered all of them ("fixed, resolved") and most are outdated against the current diff. CI is green on the head (`0c9cb40`).
- **#2 "h2r-compiler"** — `h2r-compiler` → `master`, open since 2026-09-14. Head `f0009d0` (a `mise lock` commit on top of the last PERF.md commit `b705a31`).

Both PRs were watched from the Claude session through the server-side webhook subscription (`subscribe_pr_activity`); events arrive as wake-ups, nothing polls. The Socket bot re-posts its dependency table on every push (it flags `im-rc`, MPL-2.0, license score 70; that is informational).

**[⬆ Top](#idtop)**

## 1.3 CI workflows

| workflow                                             | branch    | what it runs                                                                                                                                                                                                                                                                                                                                             |
| ---------------------------------------------------- | --------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `.github/workflows/rust.yml` "Rust port conformance" | rust-port | actionlint; format + `cargo lint` (clippy `--workspace --all-targets --all-features -D warnings -D clippy::all`); build the Haskell oracle with cabal (cached), `cargo build --release`, `cargo test -p shellcheck-rs`, `cargo test -p shellcheck-cli`, `cargo conformance-gate`, `cargo conformance-fuzz --seed "$GITHUB_RUN_NUMBER" --iterations 4000` |
| `.github/workflows/bench.yml`                        | bench     | resolve candidates → build each in its own job with a content-keyed binary cache → measure all three on one runner → report in the job summary, raw data as the `bench-results` artifact                                                                                                                                                                 |
| upstream `build.yml` and friends                     | all       | inherited from koalaman                                                                                                                                                                                                                                                                                                                                  |

The fuzz seed in the rust-port workflow is the run number, so **every CI run fuzzes a different seed** ("seed roulette"). A docs-only push can therefore fail CI by exposing a latent divergence; that is by design and it is how seed 156 was found (see [[Rust Port|02 Rust port]]).

Checks that also post on PRs: Socket Security (dependency diff), GitGuardian (secrets, neutral), actionlint.

**[⬆ Top](#idtop)**

## 1.4 Tooling conventions

- **mise** (`mise.toml`, `mise.lock`) pins every tool: rust, cabal/GHC (9.6.7 on h2r), hyperfine (bench branch and h2r branch; *not* on rust-port), uv/python (bench), dprint. Run tools through `mise exec -- <tool>` or `mise run <task>`. If a tool is not in the branch's `mise.toml`, `mise exec <tool>@<version> -- <tool>` still works (e.g. `mise exec hyperfine@1.20.0 -- hyperfine` on rust-port).
- **dprint** formats Markdown and TOML (`mise run fmt`, `dprint check`). CI fails on unformatted Markdown; always run it before committing docs.
- **Cargo aliases** live in the repo-root `.cargo/config.toml`: `cargo lint`, `cargo conformance-gate`, `cargo conformance-fuzz`, `cargo conformance-snapshot`, `cargo conformance-audit` (rust-port); `cargo locked-release` (h2r).
- **Workspace root is the repository root** (`Cargo.toml` with `members = ["rust/crates/*"]` on rust-port; `crates/*` on h2r). Edition 2024, `rust-version = 1.85`, release profile `opt-level = 3`, `lto = "thin"`.
- **`.claude/CLAUDE.md`** on each branch is the agent-facing guide (build/test commands, architecture, rules). The rust-port one also documents the conformance tools and the "before refactoring" instruments.
- **No model names** in commits, PR text or code comments (session rule).
- Commits are written as sentences describing what changed and why, no conventional-commit prefixes, no emoji.

**[⬆ Top](#idtop)**

## 1.5 Upstream Haskell architecture

*What all ports reproduce.*

ShellCheck runs in three stages: parsing (`Parser.hs`, Parsec, emits SC1xxx), AST analysis (`Analytics.hs`, `Checks/Commands.hs`, `Checks/ShellSupport.hs`, `CFG.hs` + `CFGAnalysis.hs` for the control-flow dataflow, emits SC2xxx/SC3xxx), output formatting (`Formatter/`). Checks are pure functions `Parameters -> Token -> Writer [TokenComment] ()`, either node checks (every AST node) or tree checks (once at the root). `cabal test` auto-discovers `prop_` functions; there are 2252 `prop_` definitions, 2026 of which name a shell script that the Rust conformance gate replays.

**[⬆ Top](#idtop)**

<a name="idend"></a>
