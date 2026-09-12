//! Sanctioned deviations: where the port is deliberately *not* bug-compatible.
//!
//! The gate's whole value is that any difference from the oracle is a defect, so
//! deviating from it needs more than an opinion. A hand-written list of scripts
//! would also rot on contact with the fuzzer, which invents new spellings of the
//! same shape faster than anyone can enumerate them.
//!
//! So a deviation is not recognised by matching text. It is recognised by a
//! *class*, and each class is decided by evidence the harness can gather at
//! comparison time — for the one class that exists today, by asking the shell
//! itself. If the evidence is unavailable (no such shell installed), the
//! difference counts as a divergence: this fails closed, never open.
//!
//! Adding a deviation means adding a class here, an entry in `PARITY-NOTES.md`
//! explaining what upstream does and why the port refuses to, and a test in the
//! port pinning the better behaviour.

use std::io::Write;
use std::process::{Command, Stdio};

use crate::CommentKey;

/// The codes ShellCheck emits when a script does not parse: SC1073 names the
/// construct, SC1009 the enclosing one, SC1072 ends the run. Nothing else is
/// reported, and no analysis happens.
const FATAL_PARSE_CODES: [i64; 3] = [1073, 1009, 1072];

pub struct Deviation {
    /// Stable id, quoted in gate/fuzz output and in `PARITY-NOTES.md`.
    pub id: &'static str,
    /// What the port does instead, in one line.
    pub what: &'static str,
}

const FALSE_PARSE_ERROR: Deviation = Deviation {
    id: "upstream-false-parse-error",
    what: "the shell accepts this script, so the port analyses it instead of \
           rejecting the whole file",
};

/// The interpreter to check a script against: what `--shell` said, else what the
/// shebang says, else bash — the dialect ShellCheck itself assumes.
fn interpreter(script: &str, shell: Option<&str>) -> &'static str {
    let named = shell.map(str::to_string).or_else(|| {
        let first = script.lines().next()?.strip_prefix("#!")?.trim();
        let last = first.rsplit('/').next()?;
        // `#!/usr/bin/env bash`
        let word = last.split_whitespace().next()?;
        Some(if word == "env" {
            last.split_whitespace().nth(1)?.to_string()
        } else {
            word.to_string()
        })
    });
    match named.as_deref() {
        Some("sh") | Some("dash") => "dash",
        Some("ksh") => "ksh",
        Some("busybox") => "busybox",
        _ => "bash",
    }
}

/// Does `interpreter` consider `script` syntactically valid? `-n` reads and
/// parses without running anything.
///
/// `None` means no answer is available — the interpreter is not installed, or
/// could not be run — which callers must treat as "not sanctioned".
fn shell_accepts(script: &str, interpreter: &str) -> Option<bool> {
    let mut cmd = Command::new(interpreter);
    if interpreter == "busybox" {
        cmd.arg("sh");
    }
    let mut child = cmd
        .arg("-n")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(script.as_bytes()).ok()?;
    Some(child.wait().ok()?.success())
}

fn codes(keys: &[CommentKey]) -> Vec<i64> {
    keys.iter().map(|k| k.code).collect()
}

/// Is this difference one the port is entitled to?
///
/// Only one class so far: the oracle rejects the file outright, the port does
/// not, and the shell being checked agrees with the port that the script parses.
/// A script no shell accepts is not covered, and neither is any difference that
/// leaves the oracle's fatal codes in the port's own output.
pub fn sanctioned(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
) -> Option<&'static Deviation> {
    let oracle_codes = codes(oracle);
    let port_codes = codes(port);
    let oracle_is_fatal_only = !oracle_codes.is_empty()
        && oracle_codes.contains(&1072)
        && oracle_codes.iter().all(|c| FATAL_PARSE_CODES.contains(c));
    let port_parsed = !port_codes.iter().any(|c| FATAL_PARSE_CODES.contains(c));
    if !(oracle_is_fatal_only && port_parsed) {
        return None;
    }
    match shell_accepts(script, interpreter(script, shell)) {
        Some(true) => Some(&FALSE_PARSE_ERROR),
        // Either the shell rejects it too (so the oracle was right), or there is
        // no shell to ask (so nothing is established).
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(code: i64) -> CommentKey {
        CommentKey {
            line: 1,
            column: 1,
            end_line: 1,
            end_column: 1,
            level: "error".to_string(),
            code,
            message: String::new(),
            fix: None,
        }
    }

    #[test]
    fn interpreter_comes_from_shell_then_shebang_then_bash() {
        assert_eq!(interpreter("echo hi", Some("dash")), "dash");
        assert_eq!(interpreter("#!/bin/sh\necho hi", None), "dash");
        assert_eq!(interpreter("#!/usr/bin/env bash\necho hi", None), "bash");
        assert_eq!(interpreter("echo hi", None), "bash");
    }

    #[test]
    fn a_script_bash_accepts_and_the_oracle_rejects_is_sanctioned() {
        let oracle = [key(1072)];
        assert!(sanctioned("! # c", Some("bash"), &[], &oracle).is_some());
    }

    #[test]
    fn a_script_the_shell_also_rejects_is_not_sanctioned() {
        let oracle = [key(1073), key(1072)];
        assert!(sanctioned("if", Some("bash"), &[], &oracle).is_none());
        // dash rejects `! # c`, so for a POSIX target the oracle is right.
        assert!(sanctioned("! # c", Some("dash"), &[], &oracle).is_none());
    }

    #[test]
    fn an_ordinary_difference_is_never_sanctioned() {
        // Same script, but the disagreement is about an analysis code rather
        // than about whether the file parses at all.
        assert!(sanctioned("echo $1", Some("bash"), &[key(2086)], &[]).is_none());
        assert!(sanctioned("! # c", Some("bash"), &[key(1072)], &[key(1072)]).is_none());
    }
}
