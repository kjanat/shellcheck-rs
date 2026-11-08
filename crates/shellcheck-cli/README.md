# rshellcheck

A Rust port of [ShellCheck](https://www.shellcheck.net), the static analysis
tool for shell scripts. `rshellcheck` takes the same options, reads the same
`.shellcheckrc` files and prints the same output as the `shellcheck` binary.

```sh
cargo install --locked rshellcheck
rshellcheck deploy.sh
```

```text
In deploy.sh line 1:
echo $1
^-- SC2148 (error): Tips depend on target shell and yours is unknown. Add a shebang or a 'shell' directive.
     ^-- SC2086 (info): Double quote to prevent globbing and word splitting.

Did you mean:
echo "$1"

For more information:
  https://www.shellcheck.net/wiki/SC2148 -- Tips depend on target shell and y...
  https://www.shellcheck.net/wiki/SC2086 -- Double quote to prevent globbing ...
```

The port follows ShellCheck at upstream commit
[`919d37c4d77a`](https://github.com/koalaman/shellcheck/commit/919d37c4d77a7ce16cfc76ebdd781dd6e8081fa5).
It reports the same codes, messages, positions and order as that build of
ShellCheck. A differential harness in the repository compares the two in CI.
[PARITY-NOTES.md](https://github.com/kjanat/shellcheck-rs/blob/master/PARITY-NOTES.md)
lists the sanctioned differences. `rshellcheck --version` prints the port's
version and the upstream version it follows.

## Usage

```sh
rshellcheck -s bash -f gcc scripts/*.sh
rshellcheck --exclude=SC2086 --severity=warning deploy.sh
rshellcheck --list-optional
```

`-f` selects the output format: `tty` (the default), `gcc`, `json`, `json1`,
`checkstyle`, `diff` or `quiet`. `-j N` checks files on N workers, up to four
by default. `rshellcheck --help` lists every option.

The exit status is 0 when no file has a finding and 1 when one does. It is 2
when a file could not be read or checked, 3 for a malformed option, and 4 for
an unsupported value, such as `--shell=fish` or an invalid `.editorconfig`.
`-f quiet` prints nothing and exits 1 for a finding and for a file it could not
read or check.

## What the port adds

- `-s` accepts zsh, mksh, oksh, loksh, yash, posh, bosh, osh, brush,
  freebsd-sh and netbsd-sh besides ShellCheck's sh, bash, dash, ksh and
  busybox. Each is checked with the rules of its closest upstream shell.
- SC9001 suggests a fix for a misspelled interpreter path such as
  `#!/usr/bni/env bash`, and SC9002 warns about a cleanup `trap` set for INT,
  TERM or HUP and not for EXIT.
- `--enable=clarify-parse-errors` rewords some fatal parser messages.
- The json1 document lists the sourced files the run read, in `sources`.
- Scripts nested thousands of levels deep check in linear time and do not
  overflow the stack.

[docs/diagnostics.md](https://github.com/kjanat/shellcheck-rs/blob/master/docs/diagnostics.md)
describes each of these.

## Library

This crate's library holds the output formatters, the rc-file reader and the
option parser that the binary uses. The parser and the checks are in
[`rshellcheck-core`](https://crates.io/crates/rshellcheck-core).

## Versions

Versions follow semver from 1.0.0. A patch release fixes the port, a minor
release moves the upstream commit or adds diagnostics, and a major release
breaks the API or the command line. `rshellcheck` and `rshellcheck-core` are
released together with the same version.

The minimum supported Rust version is 1.99. Prebuilt binaries, npm, PyPI and
container images are described in the
[repository README](https://github.com/kjanat/shellcheck-rs#installing).

## License

GPL-3.0-or-later, the license of ShellCheck.
