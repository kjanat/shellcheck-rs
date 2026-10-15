<a name="idtop"></a>

# 3 Additional diagnostics

The port adds diagnostics beyond upstream ShellCheck. `docs/diagnostics.md` on `master` is the reference; the TTY footer links SC9xxx codes to it.

## 3.1 Code namespaces

- `SC9000` to `SC9999` belong to this project. They are ordinary diagnostics: integer codes in every output format, filtered by `--include`, `--exclude`, severity and `disable=` like upstream codes.
- `RSC` codes report on the run itself. They never appear in a comment or in a json, json1, gcc or diff document, and no filter removes them.
- `clarify-parse-errors` is a presentation option selected through `--enable`, the library's `optional_checks` or the rc file. It changes wording only.

**[⬆ Top](#idtop)**

## 3.2 SC9001 interpreter-path typo

On by default. The check compares the shebang's directory components against `/bin`, `/sbin`, `/usr/bin`, `/usr/sbin`, `/usr/local/bin` and `/usr/local/sbin`. It suggests a correction only when exactly one component is one insertion, deletion, substitution or adjacent transposition away from a unique candidate, and the basename is a known shell interpreter or `env`. `/usr/bni/env` suggests `/usr/bin/env`. The check never reads the host filesystem and leaves custom locations such as `/opt/company/bin/bash` alone. Suppress with `--exclude=9001` or `# shellcheck disable=9001`.

The conformance class `interpreter-path-typo` permits only added SC9001 findings reproducible from the shebang alone.

**[⬆ Top](#idtop)**

## 3.3 SC9002 signal-only cleanup trap

On by default. The check reports a cleanup handler registered for INT, TERM or HUP without the same action registered for EXIT (or signal 0) in the same execution scope. It recognizes `rm`, `rmdir`, `kill`, `cleanup`, and Docker or Podman `stop`, `rm` or `kill`, including a variable used as the container engine. An INT-only handler does not run when `set -e` exits on an error or `read` reaches end of file.

```sh
trap '"$ENGINE" stop "$CONTAINER_ID"' INT       # warns
trap '"$ENGINE" stop "$CONTAINER_ID"' EXIT INT  # covers exit too
```

Functions, subshells and command substitutions are separate scopes. Helper names outside the list, dynamically assembled actions and resources without any cleanup trap are outside its coverage. The check came from [issue #4](https://github.com/kjanat/shellcheck-rs/issues/4).

**[⬆ Top](#idtop)**

## 3.4 RSC1001 dataflow internal error

When an invariant of the control-flow graph or its dataflow analysis fails, upstream prints `ShellCheck internal error, please report` and no output. The port checks the file without the dataflow checks, prints its comments, then reports

```
file: RSC1001: ShellCheck internal error, please report: <detail>. The checks that need dataflow analysis were skipped.
```

on stderr, or on stdout for checkstyle. The run exits 2; `--quiet` exits 1. `DIVERGENCES.md` entry Z7 holds the evidence.

**[⬆ Top](#idtop)**

## 3.5 Sourced files in json1

The json1 document carries `sources` after `comments`: every file the run read through `source` or `.`, by the name the `file` field of its comments would carry, each once, in first-read order, nested sources included. Files that were not followed (SC1090, SC1091, SC1093) are absent; a sourced file that was read and then failed to parse (SC1094) is present. The inputs themselves are not listed. `json` stays a bare array.

**[⬆ Top](#idtop)**

## 3.6 Parser messages

- Unicode dashes used as an arithmetic minus are diagnosed as SC1100 by default, and the parser keeps the arithmetic structure. Upstream reports SC1102, SC2046 and SC2005 for a command substitution the user did not write.
- An unterminated quote in a test's operator position names the missing closing quote. Upstream asks for a comparison operator one column past the end of the input (`PARITY-NOTES.md` item 6).
- Parse notes from complete, separated top-level statements survive a later fatal parse. `echo $10` followed by an incomplete `if` keeps SC1037. Notes inside unfinished compounds are still discarded.
- `clarify-parse-errors` omits redundant enclosing-context notes at the same position as the failed construct, describes `${ ..; }` as a command expansion with its expected terminator, and fills empty SC1072 details. Codes and positions do not change.

**[⬆ Top](#idtop)**

## 3.7 SC2064 trap expansion timing

Early expansion of a plain variable in a double-quoted trap action does not warn when every visible assignment precedes the trap and no later write is visible. Command substitutions and complex parameter expansions still warn. Functions, loop-local traps, additional trap registrations, `source`, `eval`, unresolved variable commands and variable-writing builtins keep the warning. `RANDOM`, `SECONDS`, `PWD` and `REPLY` are never treated as stable.

SC2162 stays enabled for a bare `read` whose input is discarded: a trailing backslash continues onto the next line and changes how much input is consumed.

**[⬆ Top](#idtop)**

## 3.8 SC2164 in a function tail

The port warns when a failed `cd` inside a final compound statement can be followed by another command or loop iteration. `f() { if true; then cd /missing; echo continued; fi; }` warns. A direct final `cd`, or a final `cd` in a status-preserving branch, stays exempt. The pinned upstream suppresses these by checking only whether the enclosing compound statement is last in the function. The class `upstream-function-tail-cd` sanctions the added findings at exact directory-command spans.

**[⬆ Top](#idtop)**

<a name="idend"></a>
