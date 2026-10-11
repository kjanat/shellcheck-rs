# Upstream source baseline

Upstream changes are integrated through
[`98deabe126a2`](https://github.com/koalaman/shellcheck/commit/98deabe126a26861fb02aa2b431eaf31e39e6abe)
(2026-10-08). This source baseline is newer than the published ShellCheck 0.11.0
binary; use the bundled Haskell source for port-conformance comparisons.

The October 11 integration imports the changes after `6dce0df7`: nine ordinary
commits and three merge commits. Local formatting, release workflows, and the
SC2164 function-tail correction are preserved.

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
