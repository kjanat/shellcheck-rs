# Upstream source baseline

The upstream source baseline and oracle are pinned to
[`919d37c4d77a`](https://github.com/koalaman/shellcheck/commit/919d37c4d77a7ce16cfc76ebdd781dd6e8081fa5)
(2026-10-26). This source baseline is newer than the published ShellCheck 0.11.0
binary; use the pinned upstream oracle for port-conformance comparisons.
rshellcheck's own version number is independent of the upstream version;
`rshellcheck --version` prints both, the upstream one from `tools/oracle.json`.

The November 2 sync reviews [all changes after `c36c85a05ed3`](https://github.com/koalaman/shellcheck/compare/c36c85a05ed3a1560e31bf7d89db040f84ef4556...919d37c4d77a7ce16cfc76ebdd781dd6e8081fa5):
24 ordinary commits and 21 merge commits. The behavioral changes listed below
are implemented in Rust, including Bats variable-flow and control-flow handling.
The frozen snapshot was regenerated against the unchanged 4,067 inputs: four
rows changed, and the subsequent snapshot check reported zero drift. The verified
oracle gate covers 2,102 upstream properties and 24 optional-check examples:
2,125 agree, none diverge, and one has the sanctioned added-dialect difference.
A focused comparison of all 44 newly added properties and the 24 optional-check
examples also passes without deviations. The full property extractor skips 292
properties without a replayable script; these results do not establish parity
for arbitrary inputs.

| Commit                                                                                                                                                                                                     | Upstream behavioral change                                                                                                                                                                                                                                                                                                                                   |
| ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| [c868fcbc](https://github.com/koalaman/shellcheck/commit/c868fcbc)                                                                                                                                         | SC2030/SC2031: analyze function bodies independently of preceding subshell assignments and do not attribute function assignments to their enclosing definition-time subshell. Preserve effects of subshells inside functions. Plain `export`/`declare` assignments do not read the previous value; append assignments still do.                              |
| [612e8a9f](https://github.com/koalaman/shellcheck/commit/612e8a9f)                                                                                                                                         | SC2218: Bats tests may call functions defined later outside tests, including in setup helpers. Calls at top level or before a definition within the same test still warn.                                                                                                                                                                                    |
| [2af55458](https://github.com/koalaman/shellcheck/commit/2af55458)                                                                                                                                         | SC2016: recognize single-quoted shell scripts passed through wrappers to a shell with a `-c` option, including combined flags and shell paths. Only the script argument is exempt.                                                                                                                                                                           |
| [2be06cc7](https://github.com/koalaman/shellcheck/commit/2be06cc7)                                                                                                                                         | Bats `run` sets `status`, `output`, and `lines`, plus `stderr` and `stderr_lines` with `--separate-stderr`. These implicit assignments and those attributed to `@test` are exempt from SC2034; explicit assignments remain checked. Remove globally predefined stderr variables and pretend Bats references, affecting SC2154 and subshell analysis as well. |
| [7a43730f](https://github.com/koalaman/shellcheck/commit/7a43730f)                                                                                                                                         | SC2312: treat `command \|\| echo ...` as deliberate return-status handling, including inside command substitutions passed to `eval`.                                                                                                                                                                                                                         |
| [f4d10519](https://github.com/koalaman/shellcheck/commit/f4d10519), [9ac74744](https://github.com/koalaman/shellcheck/commit/9ac74744), [32442c3a](https://github.com/koalaman/shellcheck/commit/32442c3a) | Optional-check descriptions gain diagnostic IDs; `--list-optional` prints `id:` and `wiki:` fields. Examples cover both SC2310/SC2311 and SC2243/SC2244; upstream tests verify the exact advertised codes.                                                                                                                                                   |
| [83ad2576](https://github.com/koalaman/shellcheck/commit/83ad2576)                                                                                                                                         | SC2236/SC2237: diagnose unnecessary `-n`/`-z` negation in `test ! ...` and `! test ...` commands.                                                                                                                                                                                                                                                            |
| [5f51b960](https://github.com/koalaman/shellcheck/commit/5f51b960), [776ed08f](https://github.com/koalaman/shellcheck/commit/776ed08f)                                                                     | SC2114: expand protected system directories (`/opt`, `/proc`, `/root`, `/run`, `/sbin`, `/srv`, `/sys`, and additional `/usr` directories) and recognize glob arguments such as `rm -rf /boot/*`.                                                                                                                                                            |

The remaining 13 ordinary commits are documentation and infrastructure updates:

- Seven manpage commits document `--help`, the default of three wiki links,
  `--norc` skipping both `.shellcheckrc` and `.editorconfig` and overriding
  `--rcfile`, half-open disable ranges, the GCC diagnostic suffix, the current
  bashism-disable range, and a duplicated-word correction. These changes are
  incorporated into `shellcheck.1.md`.
- Four README commits add upstream's mise installation instructions and Linux
  riscv64 binary link, and remove the obsolete Apple Silicon binary caveat.
  These describe upstream distribution, so they do not replace this port's
  installation instructions.
- The two builder Dockerfiles receive a comment typo correction, and distro
  tests move into a GitHub Actions workflow. These upstream Haskell build
  changes do not alter the Rust build or release workflow.

The October 15 integration imports the changes after `98deabe1`: one ordinary
commit and its merge commit.

| Commit                                                             | Change                                                                                       |
| ------------------------------------------------------------------ | -------------------------------------------------------------------------------------------- |
| [814a2d24](https://github.com/koalaman/shellcheck/commit/814a2d24) | SC2292 fix adds no `]` when the test was closed with `]]`; `T_Condition` records the closer. |

The October 11 integration imports the changes after `6dce0df7`: nine ordinary
commits and three merge commits. The Rust SC2164 function-tail correction is preserved. The oracle now uses
pristine upstream source, so it does not contain that local correction.

| Commit                                                             | Change                                                                           |
| ------------------------------------------------------------------ | -------------------------------------------------------------------------------- |
| [d260dd9c](https://github.com/koalaman/shellcheck/commit/d260dd9c) | Fix SC2016 false positives in sed address blocks; ported to Rust.                |
| [e8a68fac](https://github.com/koalaman/shellcheck/commit/e8a68fac) | Add SC2218 coverage for command substitutions after return; also tested in Rust. |
| [b7918ab3](https://github.com/koalaman/shellcheck/commit/b7918ab3) | Require fgl 5.8.1.1 or newer.                                                    |
| [e4e02750](https://github.com/koalaman/shellcheck/commit/e4e02750) | Update Stack to lts-22.6.                                                        |
| [db4cd9b2](https://github.com/koalaman/shellcheck/commit/db4cd9b2) | Document recently added upstream features.                                       |
| [facfe1d1](https://github.com/koalaman/shellcheck/commit/facfe1d1) | Rename Haskell SetE helpers to Errexit; Rust keeps its existing public names.    |
| [2ed8c311](https://github.com/koalaman/shellcheck/commit/2ed8c311) | Share long/short option detection; Rust uses a shared helper too.                |
| [2d5cc896](https://github.com/koalaman/shellcheck/commit/2d5cc896) | Suppress SC2034 when allexport is mentioned anywhere; ported to Rust.            |
| [bd642d27](https://github.com/koalaman/shellcheck/commit/bd642d27) | Update distro tests and Arch Cabal configuration.                                |

The allexport check follows upstream's whole-script approximation, including
short flags and shebang options. It does not track where the option is enabled
or disabled at runtime.

## Oracle and snapshot corpus

`tools/oracle.json` pins the external oracle source, and
`crates/shellcheck-cli/upstream.json` carries the same pin into the published
`rshellcheck` package. A conformance test fails when the two differ. Run `python tools/oracle.py`
with GHC, Cabal and `gh` installed to fetch and build it. The helper refuses a
modified or differently pinned checkout, and records the source revision and
binary SHA-256. `--verify-only` checks that record without rebuilding.
No Haskell compiler is installed by the ordinary project mise configuration.

`rust/conformance-corpus.json` preserves the 2,067 extracted scripts and skipped
property metadata from this repository at `c488d7fb`, before source removal.
It includes nine local SC2164 regressions alongside upstream properties. This
keeps all 4,067 snapshot inputs unchanged and lets snapshots run offline with
Rust alone. Source paths and line numbers in this corpus refer to that historical
revision, not files in the current checkout.

The gate and fuzz aliases explicitly extract their corpus from the pristine
upstream checkout. Rust unit tests and the frozen snapshots retain coverage for
the intentional SC2164 difference; the upstream oracle remains unmodified.
To inspect or export a newly pinned corpus, use:

```sh
cargo run --release -p conformance -- extract --repo .cache/upstream-shellcheck --corpus-output /tmp/upstream-corpus.json
```

Review corpus and snapshot changes together when updating the pin. Do not replace
the frozen corpus blindly: doing so also changes the generated fuzz seeds.
