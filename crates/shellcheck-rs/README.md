# rshellcheck-core

The parser and analyzer of [rshellcheck](https://crates.io/crates/rshellcheck), a
Rust port of [ShellCheck](https://www.shellcheck.net). Give it a shell script and
it returns ShellCheck's diagnostics, with positions and suggested fixes, as Rust
values.

The port follows ShellCheck at upstream commit
[`919d37c4d77a`](https://github.com/koalaman/shellcheck/commit/919d37c4d77a7ce16cfc76ebdd781dd6e8081fa5).
It reports the same codes, messages, positions and order as that build of
ShellCheck. A differential harness in the repository compares the two in CI.
[PARITY-NOTES.md](https://github.com/kjanat/shellcheck-rs/blob/master/PARITY-NOTES.md)
lists the sanctioned differences.

## Usage

```sh
cargo add rshellcheck-core
```

```rust
use rshellcheck_core::{CheckSpec, check_script};

let spec = CheckSpec {
    filename: "deploy.sh".to_string(),
    script: "#!/bin/sh\nrm -rf $dir/*\n".to_string(),
    ..CheckSpec::default()
};
let result = check_script(&spec);

for c in &result.comments {
    println!(
        "{}:{}:{}: SC{} {}",
        c.start.file, c.start.line, c.start.column, c.comment.code, c.comment.message
    );
}
assert!(result.comments.iter().any(|c| c.comment.code == 2115));
```

`CheckSpec` holds the options of the `shellcheck` command line: excluded and
included codes, the minimum severity, optional checks, the shell, and whether to
run the dataflow analysis. `CheckSpec::default()` is ShellCheck's empty spec.

The crate reads no files. `check_script` treats every `source` as unreadable and
reports SC1091 for it. To follow sourced files, implement the `System` trait and
call `check_script_with`. `check_script_as` checks a script as one of the 16
shells in `Dialect`: the five ShellCheck supports (sh, bash, dash, ksh and
BusyBox sh) and 11 more, each checked with the rules of its closest upstream
shell.

The parser and the dataflow analysis keep their recursion on the heap, so a
script nested thousands of levels deep needs no large thread stack. The crate
runs in WebAssembly as well.

## Versions

Versions follow semver from 1.0.0. A patch release fixes the port, a minor
release moves the upstream commit or adds diagnostics, and a major release
breaks the API or the command line. `rshellcheck-core` and `rshellcheck` are
released together with the same version.

The minimum supported Rust version is 1.99.

## License

GPL-3.0-or-later, the license of ShellCheck.
