<a name="idtop"></a>

# 10 Working method

How work on `master` is done and verified. `.claude/CLAUDE.md` is the authoritative version of the rules.

## 10.1 Build and test

```sh
cargo build --release --locked                       # the port, the harness
cargo test --workspace --locked --lib --bins          # unit tests
cargo conformance-snapshot                            # behaviour snapshot, offline
dprint fmt                                            # formatting
cargo lint                                            # clippy, warnings denied
```

With GHC, Cabal and an authenticated `gh`:

```sh
python tools/oracle.py                                # fetch and build the oracle into .cache/
cargo conformance-gate
cargo conformance-fuzz
```

Gates before "done": `dprint fmt`, `cargo lint`, `cargo test --workspace --locked --lib --bins`, `cargo conformance-snapshot`. With the reference binary built, the gate and the fuzzer run too, and their output is reported verbatim.

Other suites: `python3 -m unittest discover -s tools -v` (tests of `tools/oracle.py` and the cell selection); the publishing tooling tests in [[Releases and Distributions|06 Releases and distributions]]; the WASM validation commands in [[Rust Port|02 Rust port]]; `cd go && go vet ./... && go test -race ./...` for the Go installer, whose tests use a local HTTP server and need no network.

Timing of the fast loops recorded in `rust/PERF.md`: unit tests of the library about 23 s, an optimised build of the CLI and `conformance` about 4 min, the gate about 10 s, the fuzzer 1 to 3 min, the snapshot seconds.

**[⬆ Top](#idtop)**

## 10.2 Rules for a change

- Translated functions keep the Haskell name in snake_case and carry every Haskell comment. A check lives in the file matching its neighbours in the Haskell source.
- Each Haskell `prop_` becomes a `#[test] fn prop_<sameCamelName>()`. Rust-only regressions get a descriptive snake_case name in the same module.
- A snapshot change ships in the same commit as the behaviour change, with one sentence in the commit body naming the codes that moved.
- `DIVERGENCES.md` entries are bugs in the Rust code. A fixed entry moves to the fixed ledger in the same commit as the fix.
- The `PARITY-NOTES.md` header lists every class id in `deviations.rs`. Adding a class updates the header and adds a section.
- The CFG analysis stays a translation of `CFGAnalysis.hs`: change representations and keep the algorithm.
- Haskell source stays in `.cache/`. It is never vendored.
- Moving the tracked revision follows the six steps in [[Conformance and Parity|04 Conformance and parity]].

**[⬆ Top](#idtop)**

## 10.3 Issues

Tracking issues carry checkbox lists; each box names one deliverable with a commit or ShellCheck link once done. A commit that completes a box edits the issue in the same session. A ShellCheck pull request this project intends to follow gets one issue labelled `conformance` with the link, the Rust locations it touches and the plan for moving the tracked revision. An issue is closed only after reading it in full and confirming every box. A parent stays open until every sub-issue is done.

`gh issue view --comments` prints only the comments when stdout is a pipe, and nothing at all for zero comments. Read the body with `gh issue view <n>` and the comments with `gh api repos/{owner}/{repo}/issues/<n>/comments`.

**[⬆ Top](#idtop)**

## 10.4 Measuring

- Compare instruction counts (callgrind) before wall time; they are deterministic and unaffected by other load. Measure wall time and RSS only when nothing else runs.
- Peak RSS: one GNU `time` run per binary and workload. hyperfine with several commands in one invocation reports a cumulative maximum, so one hyperfine process per candidate.
- `callgrind_annotate --inclusive=yes` misreports recursive frames; use the non-recursive caller's row.
- `conformance bench` reports `params-other` and `resolve` as residuals; do not chase them.
- `im_rc::OrdMap::union` is not left-biased when the left operand is the smaller map. `cfg_analysis::union_left` exists for that reason.
- An empty `im_rc::OrdMap` allocates about 2 KB; the analysis shares one empty map.

**[⬆ Top](#idtop)**

## 10.5 Environment facts

- `tools/oracle.py` refuses a `.cache/upstream-shellcheck` checkout at another revision or with local changes. Move it aside before changing the tracked revision.
- CI caches the Haskell binary by the hash of `tools/oracle.json` and `tools/oracle.py`. `--verify-only` checks the cached identity on every run.
- The CI fuzz seed and iteration count come from the repository variable `FUZZ`, read by `conformance` as `SEED` and `ITERATIONS`. A run that finds a divergence found a real one. Fix the Rust code.
- `dprint fmt` runs `tombi` for TOML and `rustfmt` for Rust through the exec plugin. The toolchain must come from `mise install`. The generated validity files are excluded from formatting.
- Python commands run through `uv run` from the repository root. The root `.venv` holds the editable binding packages and the publishing tooling.
- The validity runner needs Docker; the VM cells need `/dev/kvm`.
- The `bench` branch has its own `mise.toml` with hyperfine 1.20.0, Python 3.14 and uv 0.12.23.

**[⬆ Top](#idtop)**

<a name="idend"></a>
