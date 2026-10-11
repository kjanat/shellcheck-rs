# Additional diagnostics

These checks extend upstream ShellCheck. Interpreter-path and signal-only cleanup warnings run by
default. Clearer parser messages can be enabled explicitly or with `--enable=all`. Normal severity filters and `--exclude` apply.

```sh
rshellcheck script.sh
rshellcheck --enable=clarify-parse-errors broken.sh
```

SC9001 and SC9002 codes are local to this project, not upstream ShellCheck codes.
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

The remaining quote-position, zero-width-span, and discarded-note behaviors in
[PARITY-NOTES.md](../PARITY-NOTES.md) were reviewed and retain their compatibility
semantics. In particular, discarding speculative notes after a fatal parse avoids
reporting findings from an abandoned interpretation. This work does not alter or
claim to fix upstream Haskell itself.

For [#4](https://github.com/kjanat/shellcheck-rs/issues/4), SC9002 addresses the
signal-only cleanup-trap pattern. General resource-lifetime analysis remains
outside this check's scope.
