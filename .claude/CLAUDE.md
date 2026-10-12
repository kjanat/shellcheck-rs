# Rust port development

This repository ships Rust, with Go, Python and JavaScript WASM bindings.
Haskell reference source is fetched into an ignored cache; do not vendor it.

- Build: `cargo build --release --locked`.
- Unit tests: `cargo test --workspace --locked --lib --bins`.
- Behavior snapshots: `cargo conformance-snapshot` (offline, no oracle).
- Formatting: `dprint fmt`; lint: `cargo lint`.
- Oracle: `python tools/oracle.py` (requires GHC, Cabal and gh).
- Conformance: `cargo conformance-gate` and `cargo conformance-fuzz`.

See UPSTREAM.md for the exact upstream revision, frozen corpus provenance and
intentional SC2164 difference. Keep rust/snapshot.txt unchanged unless behavior
changes are intentional. Preserve Rust regression tests when updating upstream.

## Source map

Upstream Haskell module to Rust location. Port functions keep the Haskell
name in snake_case and carry every Haskell comment.

| Upstream                | Rust                                                 |
| ----------------------- | ---------------------------------------------------- |
| `AnalyzerLib.hs`        | `crates/shellcheck-rs/src/analyzer_lib.rs`           |
| `Analytics.hs`          | `crates/shellcheck-rs/src/analytics/<theme>.rs`      |
| `Checks/*.hs`           | `crates/shellcheck-rs/src/checks/`                   |
| `Data.hs`               | `crates/shellcheck-rs/src/data.rs`                   |
| `Parser.hs`             | `crates/shellcheck-rs/src/parser/`                   |
| `CFG.hs`, `CFGAnalysis` | `crates/shellcheck-rs/src/cfg.rs`, `cfg_analysis.rs` |
| `Checker.hs`            | `crates/shellcheck-rs/src/checker.rs`                |
| CLI, formatters         | `crates/shellcheck-cli`                              |
| WASM bindings           | `crates/shellcheck-wasm`                             |
| differential harness    | `crates/conformance`                                 |

Analytics themes: `variables.rs` holds scope and subshell checks,
`flow.rs` holds variable-flow checks (SC2034, errexit), `commands.rs`,
`quoting.rs`, `conditions.rs`, `arithmetic.rs`, `loops.rs`,
`redirections.rs`, `script.rs`. `extensions.rs` holds every SC9xxx check.
A check lives in the file matching its upstream neighbours.

## Tests

- Each upstream `prop_` becomes a `#[test] fn prop_<sameCamelName>()` in the
  `tests` module of the file holding the check. Keep upstream numbering.
- Rust-only regressions use a descriptive snake_case name in the same module.
- A deviation class in `deviations.rs` carries two negative tests: a shifted
  span and an unrelated extra finding both break the sanction.

## Documents

| File                                   | Holds                                                                                        |
| -------------------------------------- | -------------------------------------------------------------------------------------------- |
| `UPSTREAM.md`                          | Pinned upstream revision, commit table of each imported change, corpus provenance.           |
| `PARITY-NOTES.md`                      | Upstream oddities reproduced on purpose, and every sanctioned deviation class with evidence. |
| `DIVERGENCES.md`                       | Open port defects from the last fuzz run, and the fixed ledger.                              |
| `docs/diagnostics.md`                  | Every SC9xxx code: trigger, message, how to enable.                                          |
| `docs/validity.md`                     | Validity matrix design: cells, specs, outcomes, gate, images, automation.                    |
| `validity/sources.toml`                | Hand-written: per shell, how to fetch and which versions. `cargo validity pin` resolves it.  |
| `validity/`                            | Generated `matrix.toml`, `outcomes.toml`, `REPORT.md`; hand-written `specs/SC<code>.toml`.   |
| `rust/snapshot.txt`                    | Frozen behaviour over `rust/conformance-corpus.json`.                                        |
| `rust/PERF.md`                         | Benchmark method and numbers.                                                                |
| `CHANGELOG.md`                         | User-facing release notes.                                                                   |
| `crates/conformance/src/deviations.rs` | Module header states the fail-closed rule and the three-part procedure.                      |

Rules:

- The PARITY-NOTES header lists every class id in `deviations.rs`. Adding a
  class updates the header and adds a section.
- DIVERGENCES entries are port bugs. A fixed entry moves to the fixed ledger
  in the same commit as the fix.
- A snapshot change ships in the same commit as the behaviour change, with
  one sentence in the commit body naming the codes that moved.
- Haskell source stays in `.cache/`. Never vendor it.

## Divergence policy

Default: bug-compatible with the pinned upstream revision. Same codes, same
messages, same spans, same ordering.

We diverge only when one of these holds, and the harness can prove it from
evidence at comparison time:

1. Upstream rejects a file that `<shell> -n` accepts.
2. Upstream crashes or emits an internal error. The port reports the script.
3. Upstream suppresses a diagnostic for a construct where the shell behaves
   as the diagnostic warns, and the port can match the exact span from the AST.
4. Additive SC9xxx diagnostics documented in `docs/diagnostics.md`, each
   reproducible from the triggering lines alone.
5. Clearer fatal-parser messages behind `--enable=clarify-parse-errors`.

Dialects: upstream's set (sh, bash, dash, ksh, busybox) is the floor. The
port covers every shell the validity matrix runs: zsh native and
`emulate sh`, mksh, oksh, loksh, yash, posh, bosh, FreeBSD sh, NetBSD sh,
osh, brush, tcsh. A rule about a dialect is proven by executing it in that
shell at each version, with upstream as reference only for the floor. Added
dialects and their codes are ours and documented in `docs/diagnostics.md`.

We never diverge on:

- Message wording or column placement of an upstream code.
- Which code fires, outside the classes above.
- Diagnostic ordering.
- Anything justified by a hand-written script list. A class is a predicate.
- Unmerged upstream pull requests. Port a change after it lands and the pin
  moves. Porting ahead is a conscious decision recorded in `UPSTREAM.md`
  with the PR number and a dated re-pin plan.

## Adding a sanctioned deviation

1. Add a `Deviation` const and a predicate in `deviations.rs`. The predicate
   checks that all remaining findings equal the oracle's and fails closed
   when evidence is missing.
2. Add the two negative tests.
3. Add a port regression test pinning the better behaviour.
4. Add the PARITY-NOTES section with verbatim oracle output and shell
   behaviour, and list the id in the header.
5. Run `cargo conformance-gate` and `cargo conformance-fuzz`. Zero divergences.

## Syncing upstream

1. Move the pin in `UPSTREAM.md` and add one table row per imported commit.
2. Port each commit with its `prop_` tests in the matching Rust module.
3. Rebuild the oracle with `python tools/oracle.py`.
4. Run `cargo conformance-snapshot`, review the diff, commit it with the port.
5. Run `cargo conformance-gate` and `cargo conformance-fuzz`.
6. Preserve every Rust-only regression test and the SC2164 correction.

## Issues

Tracking issues in kjanat/shellcheck-rs carry checkbox lists. Each box names
one deliverable with a commit or upstream link once done.

- #3 tracks parser and conformance findings and the upstream reports still
  unfiled: the coproc crash, the `\U110000` crash, and `! # comment`.
- #4 tracks the zed-editor comparison and the SC2064 variable-flow
  refinement. That refinement is a divergence and follows the deviation
  procedure, or lands upstream first.
- An upstream pull request we intend to port gets one issue here, labelled
  `conformance`, holding the PR link, the Rust locations it touches and the
  re-pin plan. Close it when the port lands with the moved pin.

Rules:

- `gh issue view --comments` prints only the comments when stdout is a pipe.
  Zero comments prints nothing. Read the body with `gh issue view <n>` and
  the comments with `gh api repos/{owner}/{repo}/issues/<n>/comments`.
  Never run `gh` under `script`.
- A commit that completes a box edits the issue in the same working session:
  tick the box, link the commit.
- An upstream report, once filed, gets its link in the issue and in the
  matching PARITY-NOTES entry.
- Close an issue only after reading it in full and confirming every box.
- Issue bodies carry only what the reader needs. Status headers carry a date.

## Gates before "done"

```sh
dprint fmt
cargo lint
cargo test --workspace --locked --lib --bins
cargo conformance-snapshot
```

Gate and fuzz run when the oracle is built. Report their result verbatim.
