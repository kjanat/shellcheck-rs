<a name="idtop"></a>

# 4 Conformance and parity

The port is bug-compatible with one pinned upstream revision: same codes, same messages, same spans, same ordering. A Haskell oracle built from that revision is the judge. `crates/conformance` compares the two.

## 4.1 The oracle

`tools/oracle.json` pins the source:

```json
{
  "repository": "koalaman/shellcheck",
  "revision": "c36c85a05ed3a1560e31bf7d89db040f84ef4556",
  "version": "0.11.0"
}
```

`python tools/oracle.py` clones that repository with `gh repo clone` (blob filter, depth 1), checks out the revision detached into `.cache/upstream-shellcheck`, runs `cabal build exe:shellcheck`, checks that the binary reports `version: 0.11.0`, copies it to `.cache/shellcheck-oracle` and records the pin plus the binary's SHA-256 in `.cache/shellcheck-oracle.json`. The script refuses a checkout at another revision or with local changes. `--fetch-only` stops after the checkout; `--verify-only` checks the recorded identity without rebuilding. GHC, Cabal and an authenticated `gh` are required; mise does not install them.

`UPSTREAM.md` names the pinned revision, the date it was integrated (2026-10-14 for `c36c85a05ed3`) and one table row per imported upstream commit. The pinned source is newer than the published ShellCheck 0.11.0 binary.

**[⬆ Top](#idtop)**

## 4.2 The harness

`cargo run --release -p conformance -- <command>`, or the aliases in [[Repository Overview|01 Repository overview]]. Options are flags or environment variables: `ORACLE`, `REPO`, `SEED`, `ITERATIONS`, `MAX_FINDINGS`, `ALL_SHELLS`, `WRITE`, `LIMIT`, `QUIET`.

| Command    | What it does                                                                                                                                                                                                                              |
| ---------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `gate`     | Extracts the shell script from every `prop_` in the pristine upstream checkout, runs both tools' full pipeline and compares the whole json1 payload. Required: 0 divergences. `rust/PERF.md` records 2,086 comparisons at its latest run. |
| `fuzz`     | Generated and mutated shell through both tools, with shrinking. When the oracle crashes on a batch, the batch is rerun one script at a time and the crash is counted as `oracle crashed on N input(s)`.                                   |
| `shells`   | Both tools against bash, dash, ksh93 and busybox `-n`: for each dialect, how many scripts each tool rejects that the shell accepts, and the reverse. A missing shell is reported.                                                         |
| `extract`  | Lists or exports the property corpus the gate replays (`--repo .cache/upstream-shellcheck --corpus-output <file>`).                                                                                                                       |
| `audit`    | Where the port rewinds over a commitment at a point where upstream uses a `try`. Needs a debug build.                                                                                                                                     |
| `snapshot` | Freezes the port's own behaviour over `rust/conformance-corpus.json` into `rust/snapshot.txt`, or checks nothing changed. `--write` regenerates. No oracle needed.                                                                        |
| `bench`    | Per-phase in-process timing of the port against the oracle for one input.                                                                                                                                                                 |
| `validity` | Runs diagnostic reproducers in real shells. See [Validity matrix](05-Validity-matrix).                                                                                                                                                    |

In GitHub Actions each finding is also an annotation through the `actions-rs` crate: an error for a divergence, a warning for an oracle crash, a notice for a sanctioned deviation.

`rust.yml` runs `cargo conformance-gate` and `cargo conformance-fuzz` after building the cached oracle. The fuzz job takes its environment (the `SEED` and `ITERATIONS` variables) from the repository variable `FUZZ`. `DIVERGENCES.md` describes the policy: CI fuzzes with a fresh seed on every run, and each run that finds something is a new batch for that file.

**[⬆ Top](#idtop)**

## 4.3 The frozen corpus and the snapshot

`rust/conformance-corpus.json` holds the 2,067 scripts extracted from the property tests at repository revision `c488d7fb`, plus nine local SC2164 regressions. Its source paths and line numbers refer to that historical revision. `rust/snapshot.txt` has one line per entry: the property or generated id, the input hash, the output hash, the codes seen with their positions, and a message hash. Two header lines precede 4,067 entries.

The snapshot answers a different question from the gate: did the port's own output move anywhere in the corpus. It runs offline with Rust alone, so it is the refactor gate. A snapshot change ships in the same commit as the behaviour change, with one sentence in the commit body naming the codes that moved. `rust/snapshot.txt` stays unchanged otherwise.

The gate and fuzz aliases extract their corpus from the pristine upstream checkout. The frozen file serves the snapshot alone. Replacing the frozen corpus also changes the generated fuzz seeds, so a re-pin reviews corpus and snapshot changes together.

**[⬆ Top](#idtop)**

## 4.4 Divergence policy

Default: bug-compatible with the pinned revision. The port diverges only when one of these holds and the harness can prove it from evidence at comparison time:

1. Upstream rejects a file that `<shell> -n` accepts.
2. Upstream crashes or emits an internal error. The port reports the script.
3. Upstream suppresses a diagnostic for a construct where the shell behaves as the diagnostic warns, and the port can match the exact span from the AST.
4. Additive SC9xxx diagnostics documented in `docs/diagnostics.md`, each reproducible from the triggering lines alone.
5. Clearer fatal-parser messages behind `--enable=clarify-parse-errors`.

The port never diverges on message wording or column placement of an upstream code, on which code fires outside those classes, on diagnostic ordering, on anything justified by a hand-written script list, or on unmerged upstream pull requests. Porting an upstream change ahead of the pin is recorded in `UPSTREAM.md` with the pull request number and a dated re-pin plan.

**[⬆ Top](#idtop)**

## 4.5 Sanctioned deviation classes

`crates/conformance/src/deviations.rs` recognises a deviation by class. Each class is a predicate over the AST or the shell's own verdict, and it fails closed: missing evidence, such as an uninstalled shell, counts as a divergence.

| Class id                     | The port does                                                                                  |
| ---------------------------- | ---------------------------------------------------------------------------------------------- |
| `upstream-false-parse-error` | Analyses a script the shell accepts; upstream rejects the whole file.                          |
| `interpreter-path-typo`      | Diagnoses a likely misspelling in the interpreter directory (SC9001).                          |
| `upstream-function-tail-cd`  | Keeps SC2164 for an unchecked `cd` inside a final compound statement that upstream suppresses. |
| `completed-statement-notes`  | Keeps parse notes from complete top-level statements across a later fatal parse.               |
| `unclosed-test-quote`        | Names the unterminated quote in a test's operator position.                                    |

Adding a class:

1. Add a `Deviation` const and a predicate in `deviations.rs`. The predicate checks that all remaining findings equal the oracle's.
2. Add the two negative tests.
3. Add a port regression test pinning the better behaviour.
4. Add the `PARITY-NOTES.md` section with verbatim oracle output and shell behaviour, and list the id in the header.
5. Run `cargo conformance-gate` and `cargo conformance-fuzz`. Zero divergences.

**[⬆ Top](#idtop)**

## 4.6 Parity documents

`PARITY-NOTES.md` lists upstream diagnostics that are wrong or merely strange, each with a reproducer, verbatim ShellCheck 0.11.0 output, and what bash 5.2.21 and dash 0.5.12 do with the same input. Items 1 to 5 look like bugs (misattributed syntax errors, `! # comment` rejected for bash, a Unicode dash reported as a command substitution, the `coproc` crash inside a command substitution, the `$'\U110000'` crash). Items 6 to 9 are Parsec behaviour reproduced on purpose (an error positioned inside a quoted operator, the column of a failed multi-character token, zero-width parser notes, a note discarded when a later parse fails). The file ends with the SC2164 difference, the follow-up diagnostics, and the `conformance shells` table: 2,326 scripts per dialect, where the port matches upstream exactly on rejects-valid for every dialect.

`DIVERGENCES.md` holds every input where the two still disagree as of the last fuzz run, grouped by cause. At `master` it has no open entry; sections A through G are all in the fixed ledger, and the next batch takes the letter H. Its Z section records cases where the port's own output is the better one:

- Z3: `x=$(coproc foo)` and `$'\U110000'` kill upstream outright; the port analyses both.
- Z4: `! # comment` under a bash dialect, the `upstream-false-parse-error` class.
- Z5: a filename that starts with `-`.
- Z6: an EditorConfig glob that is not a regex ends upstream with a regex-tdfa error; the port reports SC1134.
- Z7: an internal error in the dataflow analysis becomes `RSC1001`.

**[⬆ Top](#idtop)**

## 4.7 Syncing upstream

1. Move the pin in `UPSTREAM.md` and add one table row per imported commit.
2. Port each commit with its `prop_` tests in the matching Rust module.
3. Rebuild the oracle with `python tools/oracle.py`.
4. Run `cargo conformance-snapshot`, review the diff, commit it with the port.
5. Run `cargo conformance-gate` and `cargo conformance-fuzz`.
6. Preserve every Rust-only regression test and the SC2164 correction.

The October 11 integration imported the nine commits after `6dce0df7`, among them the SC2016 sed-address fix, the SC2218 coverage for command substitutions after `return`, and the SC2034 suppression when `allexport` is mentioned anywhere.

**[⬆ Top](#idtop)**

<a name="idend"></a>
