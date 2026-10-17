# Additional diagnostics

These checks extend upstream ShellCheck. Interpreter-path and signal-only cleanup warnings run by
default. Clearer parser messages can be enabled explicitly or with `--enable=all`. Normal severity filters and `--exclude` apply.

```sh
rshellcheck script.sh
rshellcheck --enable=clarify-parse-errors broken.sh
```

Codes SC9000 to SC9999 belong to this project. They are diagnostics: integer
codes in every output format, filtered by `--include`, `--exclude`, severity
and `disable=` like upstream codes. Codes with the `RSC` prefix report on the
run itself. They never appear in a comment or in a json, json1, gcc or diff
document and no filter removes them. The tty footer links SC9xxx codes to this
page.

`clarify-parse-errors` is a presentation option selected through `--enable`, the
library's `optional_checks`, or the rc file; it does not change what parses.

## SC9001

The default interpreter-path check compares directory components against common interpreter
locations: `/bin`, `/sbin`, `/usr/bin`, `/usr/sbin`, `/usr/local/bin`, and
`/usr/local/sbin`. It suggests a correction only when exactly one component is
one insertion, deletion, substitution, or adjacent transposition away from a
unique candidate, and the basename is a known shell interpreter or `env`.
For example, `/usr/bni/env` suggests `/usr/bin/env` and `/usr/locla/bin/bash`
suggests `/usr/local/bin/bash`.

It does not consult the host filesystem, rewrite paths, or reject custom locations
such as `/opt/company/bin/bash` or Nix store paths. Exact standard directories,
unknown interpreter names, and ambiguous suggestions are left alone. A custom
path deliberately resembling a standard location can be excluded with
`--exclude=9001` or `# shellcheck disable=9001`.

## SC9002

The default cleanup-trap check spots cleanup handlers registered for INT, TERM, or HUP
without the same action registered for EXIT (or signal 0) in the same execution
scope. It recognizes `rm`, `rmdir`, `kill`, `cleanup`, and Docker/Podman
`stop`, `rm`, or `kill`, including a variable used as the container engine.
Literal actions and actions containing simple parameter expansions are supported.

```sh
trap '"$ENGINE" stop "$CONTAINER_ID"' INT       # warns
trap '"$ENGINE" stop "$CONTAINER_ID"' EXIT INT  # covers exit too
```

An INT-only handler does not run when `set -e` exits on an error or `read` reaches
EOF. Choose an EXIT handler when the resource should be cleaned up on those paths.
Cleanup handlers may run twice when registered for both EXIT and a signal, so make
them idempotent, or have the signal handler exit and leave cleanup to EXIT.

This is a focused heuristic, not resource-lifetime or trap-reachability analysis.
Matching actions in separate EXIT registrations are recognized textually. It does
not prove that registration executes, remains installed, or releases a resource.
Functions, subshells, and command substitutions are treated separately. Arbitrary
helper names, dynamically assembled actions, and resources without any cleanup
trap remain outside its coverage. Suppress SC9002 when signal-only cleanup is
intentional.

## RSC1001

An invariant of the control flow graph or of its dataflow analysis did not hold.
Upstream dies with `ShellCheck internal error, please report`. The port checks
the file without the dataflow checks, prints its comments, then reports

```
file: RSC1001: ShellCheck internal error, please report: <detail>. The checks that need dataflow analysis were skipped.
```

on stderr, or on stdout for checkstyle. The run exits 2, and `--quiet` exits 1.
DIVERGENCES.md Z7 holds the evidence.

## Sourced files in json1

The json1 document carries a `sources` member after `comments`:

```json
{ "comments": [], "sources": ["./lib.sh", "lib/util.sh"] }
```

It lists every file the run read through `source` or `.`, by the name the
`file` field of its comments would carry, each once, in the order the inputs
first read them. Nested sources are included. A file that was not followed is
absent: SC1090 (non-constant name), SC1091 (refused or missing), SC1093
(recursion). A sourced file that was read and then failed to parse (SC1094) is
present. The inputs themselves are not listed. `json` stays a bare array of
comments. The library returns the same list in `CheckResult::sources`, and the
WASM response carries it as `sources`.

## Dialects

`--shell`, rc `shell=`, `# shellcheck shell=`, EditorConfig `shellcheck.shell`
and the shebang accept these dialects beyond upstream's sh, bash, dash, ksh and
busybox. Each is checked with the rules of its floor, the upstream shell its
grammar extends. No SC1071 or SC1008 is reported for them.

| Dialect      | Floor |
| ------------ | ----- |
| `zsh`        | bash  |
| `osh`        | bash  |
| `brush`      | bash  |
| `mksh`       | ksh   |
| `oksh`       | ksh   |
| `loksh`      | ksh   |
| `yash`       | sh    |
| `posh`       | sh    |
| `bosh`       | sh    |
| `freebsd-sh` | sh    |
| `netbsd-sh`  | sh    |

```sh
rshellcheck --shell zsh script.zsh
```

A dialect's own rules come from `validity/outcomes.toml`, where each diagnostic
is run in the real shell at each pinned version. `cargo validity rules` writes
them to `crates/shellcheck-rs/src/dialect_rules.rs`, one entry per code,
dialect, version and outcome. A code applies to a dialect when the table has no
entry for it, or when any version records `reproduces`; it is dropped when every
version records `absent`. Other outcomes carry no weight. The matrix runs each
shell with its default options. A script that runs `setopt`, `unsetopt`,
`emulate`, or `set` with an option flag keeps every code of its floor, also
behind a zsh precommand modifier such as `builtin`. A zsh script with
`setopt SH_WORD_SPLIT` keeps SC2086. Upstream dialects
never consult the table. `tcsh` is not a dialect: its grammar is unrelated and
its shebang still draws SC1071.

## Clearer parser errors

`clarify-parse-errors` omits redundant enclosing-context notes at the same position
as the failed construct, describes `${ ..; }` as a command expansion with its
expected terminator, and fills empty SC1072 details. Codes and source positions of
retained diagnostics are unchanged. Upstream-compatible wording remains the default.

Unicode dashes used as arithmetic minus operators are diagnosed as SC1100 by
default. The parser recovers the arithmetic structure to avoid unrelated
command-substitution advice; the diagnostic still has error severity. Quoted
literal text is unaffected.

## Issue follow-up

For [#3](https://github.com/kjanat/shellcheck-rs/issues/3), interpreter-path checks,
clearer parser errors, and Unicode arithmetic diagnostics are implemented here.
Regression tests cover the upstream coprocess crash and out-of-range/surrogate
ANSI-C escape cases. Those escapes still use the documented lossy string decoder;
this is not a byte-exact emulation of Bash's non-Unicode strings. The existing
Bash `! # comment` correction remains covered by conformance tests.

Unterminated quotes in a test's operator position now name the missing closing
quote instead of asking for a comparison operator. Parse notes from complete,
separated top-level statements survive a later fatal parse; notes from unfinished
compound statements and speculative alternatives remain discarded. These fixes
apply by default. Zero-width insertion-point diagnostics retain their existing
spans. This work does not alter or claim to fix upstream Haskell itself.

For [#4](https://github.com/kjanat/shellcheck-rs/issues/4), SC9002 addresses the
signal-only cleanup-trap pattern. General resource-lifetime analysis remains
outside this check's scope.

## Trap expansion timing (SC2064)

Early expansion of a plain variable in a double-quoted trap action no longer
warns when its assignments precede the trap and no later writes are visible.
This includes a container engine selected by an earlier `if` and a container ID
captured before installing cleanup. Command substitutions and complex parameter
expansions in the action still warn.

The exemption is conservative: functions, loop-local traps, additional trap
registrations, source/eval, unresolved variable commands and variable-writing
builtins retain the warning. Resolvable variable commands must have only literal,
non-mutating command alternatives. Shell-maintained values such as `RANDOM`,
`SECONDS`, `PWD` and `REPLY` are not treated as stable. This is static analysis of
the visible script, not a guarantee about an externally customized shell environment.

SC2162 remains enabled for bare `read`, including discarded input: a trailing
backslash continues onto another line and changes how much input is consumed.
