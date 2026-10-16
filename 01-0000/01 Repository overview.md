<a name="idtop"></a>

# 1 Repository overview

`kjanat/shellcheck-rs` holds `rshellcheck`, a Rust port of [ShellCheck](https://github.com/koalaman/shellcheck), on `master`. The Haskell source is never checked in. `tools/oracle.py` fetches the reference revision into the ignored `.cache/` directory and builds it as the judge for conformance runs.

## 1.1 Layout of `master`

| Path                           | Holds                                                                                                                                         |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------- |
| `crates/shellcheck-rs`         | The analysis library: parser, analytics, checks, control-flow graph and dataflow analysis. Depends on `regex` and `im-rc` only.               |
| `crates/shellcheck-cli`        | The `rshellcheck` binary and its formatters.                                                                                                  |
| `crates/shellcheck-wasm`       | The JSON ABI over the library, built for `wasm32-unknown-unknown`.                                                                            |
| `crates/conformance`           | The differential harness binary `conformance`: gate, fuzz, shells, extract, audit, snapshot, bench, validity.                                 |
| `bindings/wasm/{js,python,go}` | Host wrappers for the WASM module: `@kjanat/rshellcheck-wasm`, `rshellcheck-wasm`, module `github.com/kjanat/shellcheck-rs/bindings/wasm/go`. |
| `bindings/native/{npm,python}` | Launchers for the native binary: `@kjanat/rshellcheck` with its platform packages, and the `rshellcheck` Python wheels.                       |
| `go/`                          | Module `github.com/kjanat/shellcheck-rs/go`: a `shellcheck` command that downloads and runs the matching release binary.                      |
| `docker/{cli,binaries,shells}` | Dockerfiles for the CLI image, the copy-only binary images and one interpreter image per shell of the validity matrix.                        |
| `docs/`                        | `diagnostics.md` (every SC9xxx code) and `validity.md` (the validity matrix design).                                                          |
| `rust/`                        | `conformance-corpus.json` (the frozen property corpus), `snapshot.txt` (frozen behaviour), `PERF.md` (measurements and work packages).        |
| `tools/`                       | `oracle.json` (the upstream pin), `oracle.py`, `affected_shell_cells.py`, with unit tests.                                                    |
| `validity/`                    | `sources.toml` (hand-written), generated `matrix.toml`, `outcomes.toml`, `REPORT.md`, and `specs/SC<code>.toml`.                              |
| `.github/workflows/`           | `rust.yml`, `wasm.yml`, `go.yml`, `shells.yml`, `release.yml`.                                                                                |
| `.github/release/`             | The Python release tooling, a private uv package named `rshellcheck-release`, with its README and unit tests.                                 |
| `.cargo/config.toml`           | Cargo aliases and `rustflags = ["-Dwarnings"]`.                                                                                               |
| `.claude/CLAUDE.md`            | The contributor guide: build commands, source map, test rules, document rules, divergence policy, issue rules, gates.                         |
| `UPSTREAM.md`                  | The pinned upstream revision, one table row per imported commit, corpus provenance.                                                           |
| `PARITY-NOTES.md`              | Upstream oddities reproduced on purpose, and the sanctioned deviations with evidence.                                                         |
| `DIVERGENCES.md`               | Open port defects from the last fuzz run, and the fixed ledger.                                                                               |
| `CHANGELOG.md`                 | User-facing release notes for `rshellcheck`, followed by upstream ShellCheck's own history.                                                   |

Root manifests: `Cargo.toml` (workspace, edition 2024, `rust-version = "1.99"`, release profile `opt-level = 3` and thin LTO), `mise.toml`, `dprint.toml`, `pyproject.toml` (uv workspace), `package.json` (npm workspaces), `mutants.toml`, `clippy.toml`, `rustfmt.toml`, `tombi.toml`.

**[⬆ Top](#idtop)**

## 1.2 Branches

| Branch         | Content                                                                                                          |
| -------------- | ---------------------------------------------------------------------------------------------------------------- |
| `master`       | The Rust port, its harness, bindings, release pipeline and documents.                                            |
| `bench`        | The benchmark harness, a Python project with its own `mise.toml`. See [Benchmark harness](08-Benchmark-harness). |
| `h2r-compiler` | The Haskell-to-Rust compiler experiment, finished. See [H2R compiler](09-H2R-compiler).                          |
| `wiki`         | These pages. `.github/workflows/wiki.yml` mirrors every push into the wiki repository.                           |

Development happened on a `rust-port` branch, merged into `master` through [pull request #1](https://github.com/kjanat/shellcheck-rs/pull/1). That branch is gone from the remote.

**[⬆ Top](#idtop)**

## 1.3 Tags and releases

| Tag pattern                                                                | Meaning                                                                                                                             |
| -------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| `rshellcheck-v<version>`                                                   | A binary release. `rshellcheck-v0.11.0` carried the upstream version number; from `rshellcheck-v1.0.0` the port has its own scheme. |
| `go/v<version>`                                                            | Go module tag on the same commit as the binary release, required there by the planner.                                              |
| `go/v<version>-wrapper.<n>`                                                | A Go wrapper fix shipped without a new binary release.                                                                              |
| `upstream-<version>`                                                       | Moved by the release pipeline to the newest stable release of that upstream version.                                                |
| `h2r-m1` … `h2r-m2.4`, `h2r-dump-v5`, `h2r-dump-v6`, `h2r-a5-linkage-hole` | Milestones of the H2R compiler experiment.                                                                                          |

The [tags page](https://github.com/kjanat/shellcheck-rs/tags) lists the current tags. See [Releases and distributions](06-Releases-and-distributions).

**[⬆ Top](#idtop)**

## 1.4 CI workflows

| Workflow                                 | Trigger                                                                                                                                                        | Jobs                                                                                                                                                                                                                                                                                                                                                             |
| ---------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `rust.yml` "Rust port conformance"       | Push to `master` and pull requests touching `crates/**`, `rust/**`, Cargo files, `.cargo/**`, `mise.toml`, `mutants.toml`, `tools/oracle*`.                    | `actionlint`; `lint` (mise toolchain, `kjanat/dprint-check`, `cargo lint`); `conformance-gate` (fetch and build the cached Haskell oracle, `cargo build --release`, `cargo test -p shellcheck-rs`, `cargo test -p shellcheck-cli`, `cargo conformance-gate`, `cargo conformance-fuzz`); `validity-smoke` (build and run the `bash:5.3` and `dash:0.5.13` cells). |
| `wasm.yml` "WASM core"                   | Push to `master` and pull requests touching crates, bindings, lockfiles; manual dispatch.                                                                      | `test` "One module, Go / Python / browser": builds the module with Rust 1.99.0, runs the native parity example, then the Node, Go, Python and Chromium tests.                                                                                                                                                                                                    |
| `go.yml` "Go installer"                  | Push to `master` and pull requests touching `go/**`.                                                                                                           | `test` per operating system: `go vet` and `go test -race` in `go/`.                                                                                                                                                                                                                                                                                              |
| `shells.yml` "Shell images and validity" | Mondays at 04:00 UTC, manual dispatch with `rebuild-all`, push to `master`, pull requests touching `docker/shells/**`, `validity/**`, `crates/conformance/**`. | `pin` (`cargo validity pin`, select affected cells); `build` per cell (push the image to ghcr.io with build provenance and an SPDX SBOM attestation); `run` (`cargo validity --record`, then open a pull request from branch `validity/drift` when `matrix.toml`, `outcomes.toml` or `REPORT.md` changed).                                                       |
| `release.yml`                            | Tags `rshellcheck-v*`, pull requests touching release inputs, manual dispatch.                                                                                 | See [Releases and distributions](06-Releases-and-distributions).                                                                                                                                                                                                                                                                                                 |

The `bench` branch carries `.github/workflows/bench.yml` (jobs `resolve`, `prepare`, `measure`). The `wiki` branch carries `wiki.yml` (jobs `actionlint`, `publish`).

**[⬆ Top](#idtop)**

## 1.5 Toolchain

`mise.toml` fixes the tool versions. `mise install` provides rust (with `rustfmt`, `clippy`, `rust-src`), dprint from `github:kjanat/dprint`, go 1.27, node 26, python, tombi 1.8, uv 0.13, cargo-binstall, cargo-mutants, droast and `shellcheck` itself from the `github:kjanat/shellcheck-rs` backend. mise installs no Haskell tool. Building the reference binary needs GHC, Cabal and an authenticated `gh` separately.

mise tasks: `format` (`dprint fmt`), `snapshot` (`cargo conformance-snapshot`), `coverage` (`cargo llvm-cov` over the snapshot run), `mutants` (`cargo mutants`), `check-py` (`ruff check`, `ty check`, `basedpyright`), `oracle` (`python tools/oracle.py`).

Cargo aliases in `.cargo/config.toml`:

| Alias                        | Expands to                                                                                                 |
| ---------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `cargo lint`                 | `clippy --workspace --all-targets --all-features -- -D warnings -D clippy::all`                            |
| `cargo conformance-gate`     | `run --release -p conformance -- gate --oracle .cache/shellcheck-oracle --repo .cache/upstream-shellcheck` |
| `cargo conformance-fuzz`     | `run --release -p conformance -- fuzz --oracle .cache/shellcheck-oracle --repo .cache/upstream-shellcheck` |
| `cargo conformance-shells`   | `run --release -p conformance -- shells --iterations 300`                                                  |
| `cargo conformance-snapshot` | `run --release -q -p conformance -- snapshot`                                                              |
| `cargo conformance-audit`    | `run -q -p conformance -- audit`                                                                           |
| `cargo validity`             | `run --release -q -p conformance -- validity`                                                              |
| `cargo install-bin`          | `install --path=crates/shellcheck-cli --bin=rshellcheck --force`                                           |
| `cargo rshellcheck`          | `run --release --bin rshellcheck --`                                                                       |

An alias is the argument list after `cargo`. None of them starts with the word `cargo`.

Formatting: `dprint fmt` formats Markdown, TOML (through `tombi`) and Rust (through `rustfmt`). `dprint.toml` excludes `shellcheck.1.md`, the issue templates and the generated validity files. Python tooling runs through `uv run` from the root `.venv`; the uv workspace members are `bindings/wasm/python`, `bindings/native/python` and `.github/release`. The npm workspaces are `bindings/wasm/js` and `bindings/native/npm`.

Workspace lints: clippy `all`, `pedantic` and `nursery` at warn with a long deny list (`unwrap_used`, `expect_used`, `redundant_clone`, `uninlined_format_args` and others), `unsafe_code = "forbid"` (the WASM crate lowers it to `deny` for its export attributes), `missing_docs = "warn"`, and `non_camel_case_types = "allow"`, which lets the Rust code keep ShellCheck's constructor names such as `T_Literal` and `TC_Binary`.

**[⬆ Top](#idtop)**

## 1.6 Licences

`shellcheck-rs`, `shellcheck-cli`, `shellcheck-wasm` and every binding are GPL-3.0-or-later. The `conformance` crate is MIT and never published.

**[⬆ Top](#idtop)**

<a name="idend"></a>
