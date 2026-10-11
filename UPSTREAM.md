# Upstream source baseline

Upstream changes are integrated through
[`98deabe126a2`](https://github.com/koalaman/shellcheck/commit/98deabe126a26861fb02aa2b431eaf31e39e6abe)
(2026-10-08). This source baseline is newer than the published ShellCheck 0.11.0
binary; use the pinned upstream oracle for port-conformance comparisons.

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

`tools/oracle.json` pins the external oracle source. Run `python tools/oracle.py`
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
