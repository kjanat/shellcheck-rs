<a name="idtop"></a>

# 2 Rust port

A module-for-module port of ShellCheck's Haskell to Rust. Each port function keeps the Haskell name in snake_case and carries every Haskell comment, so a difference from upstream can be traced to one line of the original source. Parity is enforced by the harness described in [[Conformance and Parity|04 Conformance and parity]].

## 2.1 Crates

| Crate             | Kind                    | Version | Dependencies                                                     | Role                                                                                   |
| ----------------- | ----------------------- | ------- | ---------------------------------------------------------------- | -------------------------------------------------------------------------------------- |
| `shellcheck-rs`   | library `shellcheck_rs` | 1.0.0   | `im-rc`, `regex`                                                 | Parse and analyse. IO-free, so an editor integration can embed it.                     |
| `shellcheck-cli`  | binary `rshellcheck`    | 1.0.0   | `serde`, `serde_json`, `shellcheck-rs`                           | The command line and the TTY, JSON, JSON1, GCC, CheckStyle, Diff and Quiet formatters. |
| `shellcheck-wasm` | `cdylib` and `rlib`     | 1.0.0   | `serde`, `serde_json`, `shellcheck-rs`                           | A JSON request and response ABI over the library for `wasm32-unknown-unknown`.         |
| `conformance`     | binary `conformance`    | 0.0.0   | `actions-rs`, `clap`, `serde`, `serde_json`, `toml`, both crates | The differential harness. MIT, `publish = false`.                                      |

The three published crates share one version number, set together with the four binding manifests under `bindings/` at release time.

**[⬆ Top](#idtop)**

## 2.2 Source map

Upstream Haskell module to Rust location, from `.claude/CLAUDE.md`:

| Upstream                   | Rust                                                 |
| -------------------------- | ---------------------------------------------------- |
| `AnalyzerLib.hs`           | `crates/shellcheck-rs/src/analyzer_lib.rs`           |
| `Analytics.hs`             | `crates/shellcheck-rs/src/analytics/<theme>.rs`      |
| `Checks/*.hs`              | `crates/shellcheck-rs/src/checks/`                   |
| `Data.hs`                  | `crates/shellcheck-rs/src/data.rs`                   |
| `Parser.hs`                | `crates/shellcheck-rs/src/parser/`                   |
| `CFG.hs`, `CFGAnalysis.hs` | `crates/shellcheck-rs/src/cfg.rs`, `cfg_analysis.rs` |
| `Checker.hs`               | `crates/shellcheck-rs/src/checker.rs`                |
| CLI, formatters            | `crates/shellcheck-cli`                              |
| WASM bindings              | `crates/shellcheck-wasm`                             |
| differential harness       | `crates/conformance`                                 |

Analytics themes: `variables.rs` holds scope and subshell checks, `flow.rs` holds variable-flow checks (SC2034, errexit), then `commands.rs`, `quoting.rs`, `conditions.rs`, `arithmetic.rs`, `loops.rs`, `redirections.rs`, `script.rs`. `extensions.rs` holds every SC9xxx check. A new check goes in the file that holds its upstream neighbours.

Parser modules: `arithmetic.rs`, `commands.rs`, `compound.rs`, `conditions.rs`, `directives.rs`, `words.rs`, `tests.rs`. Other library modules: `ast.rs`, `ast_lib.rs`, `interface.rs`, `editor_config.rs`, `regex_lib.rs`, `tdfa.rs` (a parser accepting exactly what Haskell's regex-tdfa accepts, used for EditorConfig globs), `idhash.rs` (an integer-key hasher for node and id maps), `test_support.rs`.

**[⬆ Top](#idtop)**

## 2.3 Test conventions

- Each upstream `prop_` becomes `#[test] fn prop_<sameCamelName>()` in the `tests` module of the file holding the check. Upstream numbering is kept.
- Rust-only regressions use a descriptive snake_case name in the same module.
- A deviation class in `crates/conformance/src/deviations.rs` carries two negative tests: a shifted span and an unrelated extra finding both break the sanction.
- Unit tests: `cargo test --workspace --locked --lib --bins`. `rust/PERF.md` records 2,145 workspace tests at its latest measurement.

**[⬆ Top](#idtop)**

## 2.4 The `rshellcheck` command

`rshellcheck` takes ShellCheck's command line. Differences a user sees:

- `--version` prints a `version:` line with the port's own version and an `upstream:` line with the ported ShellCheck version and the first twelve characters of the git revision from `tools/oracle.json`.
- Checking several regular files uses up to four CPUs by default. `-j N` or `--jobs N` sets the worker count; `-j 1` is serial. Quiet mode and runs with non-regular inputs stay serial. Diagnostics keep input order.
- `--files-from` reads the input list from a file. EditorConfig `shellcheck.*` keys are honoured.
- json1 documents carry a `sources` member listing every file the run read through `source` or `.`.
- `--enable=clarify-parse-errors` selects clearer fatal-parser messages. See [[Additional Diagnostics|03 Additional diagnostics]] for this and the SC9xxx codes.
- When a dataflow invariant fails, the run reports `RSC1001` on stderr, prints the file's other comments and exits 2. Upstream dies with an internal error there.
- A filename starting with `-` is read as a file when the option does not exist or the file exists. Upstream stops with an unrecognized option.

Build and install:

```sh
cargo build --release --locked -p shellcheck-cli      # target/release/rshellcheck
cargo install --locked --git 'https://github.com/kjanat/shellcheck-rs' 'shellcheck-cli' --bin 'rshellcheck'
```

**[⬆ Top](#idtop)**

## 2.5 The library

`CheckResult` carries the comments, `sources` (the sourced files, each once, in first-read order) and `dataflow_error`. A non-empty `dataflow_error` means the dataflow checks were skipped for that file; no include, exclude, severity or disable filter removes it. The WASM response exposes both as `sources` and `dataflowError`.

`rust/PERF.md` records API facts of the latest optimisation rounds: `ProgramState::exit_codes` is an `Rc<BTreeSet<Id>>`, `Parameters::{parent_map,id_map}` and `build_maps()` expose `IdMap` with unspecified iteration order, and `CFGResult::cf_id_to_nodes` and `CFGAnalysis::token_to_nodes` are `NodeAssociations`. The analysis state holds `Rc` values, so it is not `Send`.

**[⬆ Top](#idtop)**

## 2.6 WASM module and bindings

One `shellcheck_wasm.wasm` runs in Go, Python and JavaScript. It contains the analysis core and a JSON adapter, with no WASI, filesystem or JavaScript imports.

```sh
rustup target add wasm32-unknown-unknown
cargo build --release --locked -p shellcheck-wasm --target wasm32-unknown-unknown
```

ABI v1 exports `memory`, `sc_abi_version() -> 1`, `sc_prepare(len) -> ptr`, `sc_check() -> ptr`, `sc_output_len() -> len`, `sc_reset()`. A caller writes the request bytes into the range `sc_prepare` returns, calls `sc_check`, copies `sc_output_len` bytes from the result pointer, and parses the response before the next call. Input is limited to 16 MiB of UTF-8 JSON. One request at a time per instance; an instance is never reused after a trap.

Request fields: `script` (required), `filename` (default `script.sh`), `shell` (`bash`, `sh`, `dash`, `ksh`, `busybox`, else inferred), `files` (virtual source files), `checkSourced`, `exclude`, `include`, `optionalChecks`, `extendedAnalysis`, `severity`. The response is `{comments, dataflowError, sources}`. Columns are 1-based character columns with eight-column tab stops.

| Host       | Package                                                                                 | Runtime                                 |
| ---------- | --------------------------------------------------------------------------------------- | --------------------------------------- |
| JavaScript | `@kjanat/rshellcheck-wasm`: `createChecker()`, `./worker` module Worker, `./wasm` asset | Node or a browser                       |
| Python     | `rshellcheck-wasm`: `Checker()`; Python 3.12 or later                                   | `wasmtime` 38.0.0, fuel budget per call |
| Go         | `github.com/kjanat/shellcheck-rs/bindings/wasm/go`, package `shellcheck`                | wazero 1.9.0, no CGO                    |

The same 26 fixture cases run against the native core in Go, Python, Node and a Chromium module worker (`bindings/wasm/fixtures.py`, `npm run test:wasm`, `npm run test:browser`, the Python `unittest` suite, `go test -race`).

**[⬆ Top](#idtop)**

## 2.7 Native launchers

- `@kjanat/rshellcheck` on npm installs the `rshellcheck` command through optional platform packages `@rshellcheck/rshellcheck-<os>-<arch>` listed in `bindings/native/npm/platforms.json`. `binaryPath()` returns the executable path for programmatic use.
- `rshellcheck` on PyPI ships platform wheels containing the release executable: `uv tool install rshellcheck`.
- `go install github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v1.0.0` installs a `shellcheck` command. Its first run downloads the matching `rshellcheck-v<version>` release archive for `GOOS/GOARCH`, checks it against `SHA256SUMS`, verifies SLSA provenance when a signed-in `gh` is on `PATH`, and caches the binary under the user cache directory. Later runs exec the binary directly. The command exits 69 when it cannot resolve, download, verify or start the binary; ShellCheck never uses that code.

**[⬆ Top](#idtop)**

<a name="idend"></a>
