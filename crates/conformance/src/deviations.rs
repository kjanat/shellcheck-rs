//! Sanctioned deviations: where the port is deliberately *not* bug-compatible.
//!
//! The gate's whole value is that any difference from the oracle is a defect, so
//! deviating from it needs more than an opinion. A hand-written list of scripts
//! would also rot on contact with the fuzzer, which invents new spellings of the
//! same shape faster than anyone can enumerate them.
//!
//! So a deviation is not recognised by matching text. It is recognised by a
//! *class*, and each class is decided by evidence the harness can gather at
//! comparison time — by examining the AST or asking the shell itself. If the evidence is unavailable (no such shell installed), the
//! difference counts as a divergence: this fails closed, never open.
//!
//! Adding a deviation means adding a class here, an entry in `PARITY-NOTES.md`
//! explaining what upstream does and why the port refuses to, and a test in the
//! port pinning the better behaviour.

use std::io::Write;
use std::process::{Command, Stdio};

use shellcheck_rs::Dialect;

use crate::CommentKey;
use crate::oracle::Oracle;

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

const INTERPRETER_PATH_TYPO: Deviation = Deviation {
    id: "interpreter-path-typo",
    what: "the port diagnoses a likely misspelling in the interpreter directory",
};

const FUNCTION_TAIL_CD: Deviation = Deviation {
    id: "upstream-function-tail-cd",
    what: "upstream suppresses unchecked directory changes inside a final compound statement",
};

const COMPLETED_PARSE_NOTES: Deviation = Deviation {
    id: "completed-statement-notes",
    what: "parse notes from complete top-level statements survive a later fatal parse",
};
const UNCLOSED_TEST_QUOTE: Deviation = Deviation {
    id: "unclosed-test-quote",
    what: "the port identifies an unterminated quote instead of a missing test operator",
};

const ADDED_DIALECT: Deviation = Deviation {
    id: "added-dialect",
    what: "the shebang or shell= directive names a dialect upstream lacks, so the port \
           checks the script as that dialect's upstream floor",
};

/// The codes upstream emits for an interpreter it does not know: SC1071 for a
/// shell on its refusal list (the body is then not parsed), SC1008 for any
/// other shebang, SC1103 for a `shell=` directive.
const UNKNOWN_INTERPRETER_CODES: [i64; 3] = [1071, 1008, 1103];

/// The port's parse of the script, else of its first line alone, so a body
/// that does not parse still yields its shebang.
fn parsed_root(script: &str) -> Option<shellcheck_rs::ast::Token> {
    shellcheck_rs::parser::parse_script_with("-", script, false, None)
        .root
        .or_else(|| {
            let first = script.lines().next()?;
            shellcheck_rs::parser::parse_script_with("-", &format!("{first}\n"), false, None).root
        })
}

/// Whether upstream refuses the body outright (SC1071): a shebang on its
/// refusal list and no `shell=` directive to override it.
fn upstream_refuses_body(root: &shellcheck_rs::ast::Token) -> bool {
    use shellcheck_rs::ast::{Annotation, InnerToken};
    let InnerToken::T_Annotation { annotations, token } = &*root.inner else {
        return false;
    };
    if annotations
        .iter()
        .any(|a| matches!(a, Annotation::ShellOverride(_)))
    {
        return false;
    }
    let InnerToken::T_Script { shebang, .. } = &*token.inner else {
        return false;
    };
    let InnerToken::T_Literal(sb) = &*shebang.inner else {
        return false;
    };
    shellcheck_rs::parser::is_valid_shell(&shellcheck_rs::ast_lib::executable_from_shebang(sb))
        == Some(false)
}

fn added_dialect(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
    runner: Option<&Oracle>,
) -> bool {
    if shell.is_some() {
        return false;
    }
    let Some(root) = parsed_root(script) else {
        return false;
    };
    let Some(dialect) = shellcheck_rs::analyzer_lib::named_dialect(&root).filter(|d| d.is_added())
    else {
        return false;
    };
    let flagged: Vec<_> = oracle
        .iter()
        .filter(|k| UNKNOWN_INTERPRETER_CODES.contains(&k.code))
        .collect();
    if flagged.len() > 1
        || port
            .iter()
            .any(|k| UNKNOWN_INTERPRETER_CODES.contains(&k.code))
    {
        return false;
    }
    let refused = upstream_refuses_body(&root);
    // Upstream's verdict fixes which code it can have reported, and where.
    let consistent = flagged.first().is_none_or(|flag| match flag.code {
        1071 => refused && (flag.line, flag.column) == (1, 1),
        1008 => !refused && (flag.line, flag.column) == (1, 1),
        _ => !refused,
    });
    // A refused body leaves upstream nothing else to say.
    if !consistent || (refused && oracle.len() != flagged.len()) {
        return false;
    }
    let Some(runner) = runner else {
        return false;
    };
    let floor_name = Dialect::from(dialect.floor()).name();
    let Ok((comments, _)) = runner.check_one(script, Some(floor_name)) else {
        return false;
    };
    let floor: Vec<_> = crate::oracle_keys(&comments)
        .into_iter()
        .filter(|k| k.code != 1103 && shellcheck_rs::dialect_policy::applies(k.code, dialect))
        .collect();
    port == floor.as_slice()
}

fn completed_statement_notes(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
) -> bool {
    if !oracle.iter().any(|k| k.code == 1072) {
        return false;
    }
    let extra: Vec<_> = port.iter().filter(|k| !oracle.contains(k)).collect();
    if extra.is_empty()
        || extra
            .iter()
            .any(|k| !(1000..2000).contains(&k.code) || FATAL_PARSE_CODES.contains(&k.code))
    {
        return false;
    }
    if !port.iter().filter(|k| !extra.contains(k)).eq(oracle.iter()) {
        return false;
    }
    // Demand a complete, independently parsable prefix that reproduces every
    // extra finding exactly. Never waive an arbitrary added SC1xxx diagnostic.
    script
        .char_indices()
        .filter(|(_, c)| matches!(c, ';' | '\n' | '&'))
        .any(|(i, c)| {
            let prefix = &script[..i + c.len_utf8()];
            let parsed = shellcheck_rs::parser::parse_script_with(
                "-",
                prefix,
                shell.is_some(),
                shell.and_then(crate::parse_shell).map(Dialect::floor),
            );
            if parsed.root.is_none()
                || parsed
                    .notes
                    .iter()
                    .any(|n| FATAL_PARSE_CODES.contains(&n.code))
            {
                return false;
            }
            crate::port_keys(prefix, "-", shell)
                .is_ok_and(|keys| extra.iter().all(|k| keys.contains(k)))
        })
}

fn unclosed_test_quote(script: &str, port: &[CommentKey], oracle: &[CommentKey]) -> bool {
    let removed: Vec<_> = oracle.iter().filter(|k| !port.contains(k)).collect();
    let added: Vec<_> = port.iter().filter(|k| !oracle.contains(k)).collect();
    if removed.len() != 1 || added.len() != 1 {
        return false;
    }
    let old = removed[0];
    let new = added[0];
    if old.code != 1072
        || new.code != 1072
        || old.level != new.level
        || old.fix != new.fix
        || !matches!(
            old.message.as_str(),
            "Expected comparison operator (don't wrap commands in []/[[]]). Fix any mentioned problems and try again."
                | " Fix any mentioned problems and try again."
        )
        || !matches!(
            new.message.as_str(),
            "Expected end of single quoted string. Fix any mentioned problems and try again."
                | "Expected end of double quoted string. Fix any mentioned problems and try again."
        )
        || !oracle
            .iter()
            .any(|k| k.code == 1073 && k.message.contains("test expression"))
        || !port
            .iter()
            .filter(|k| *k != new)
            .eq(oracle.iter().filter(|k| *k != old))
    {
        return false;
    }
    let eof = script.chars().fold((1, 1), |(line, col), c| match c {
        '\n' => (line + 1, 1),
        '\t' => (line, col + 8 - ((col - 1) % 8)),
        _ => (line, col + 1),
    });
    if (new.line, new.column) != eof || (new.end_line, new.end_column) != eof {
        return false;
    }
    // Independent syntax-only shell evidence, never execute the input.
    let Ok(mut child) = Command::new("bash")
        .args(["--noprofile", "--norc", "-n"])
        .env("LC_ALL", "C")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
    else {
        return false;
    };
    let Some(mut input) = child.stdin.take() else {
        return false;
    };
    if input.write_all(script.as_bytes()).is_err() {
        let _ = child.kill();
        let _ = child.wait();
        return false;
    }
    drop(input);
    child.wait_with_output().is_ok_and(|out| {
        !out.status.success()
            && String::from_utf8_lossy(&out.stderr)
                .contains("unexpected EOF while looking for matching")
    })
}

// Recognize the old upstream predicate AND an ancestor that can overwrite the
// command's status. Match the precise diagnostic span; never waive SC2164 by code.
fn function_tail_cd(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
) -> bool {
    use shellcheck_rs::ast::InnerToken;
    let extra: Vec<_> = port.iter().filter(|k| !oracle.contains(k)).collect();
    if extra.is_empty() || extra.iter().any(|k| k.code != 2164) {
        return false;
    }
    let remaining: Vec<_> = port.iter().filter(|k| !extra.contains(k)).collect();
    if !remaining.iter().copied().eq(oracle.iter()) {
        return false;
    }
    let parsed = shellcheck_rs::parser::parse_script_with(
        "-",
        script,
        shell.is_some(),
        shell.and_then(crate::parse_shell).map(Dialect::floor),
    );
    let Some(root) = parsed.root else {
        return false;
    };
    let (parents, tokens) = shellcheck_rs::analyzer_lib::build_maps(&root);
    extra.iter().all(|finding| {
        tokens.values().any(|command| {
            if !matches!(&*command.inner, InnerToken::T_SimpleCommand { .. })
                || !(match &*command.inner {
                    InnerToken::T_SimpleCommand { words, .. } => words
                        .first()
                        .and_then(shellcheck_rs::ast_lib::get_literal_string),
                    _ => None,
                })
                .is_some_and(|name| matches!(name.as_str(), "cd" | "pushd" | "popd"))
            {
                return false;
            }
            let Some((start, end)) = parsed.positions.get(&command.id()) else {
                return false;
            };
            if (start.line, start.column, end.line, end.column)
                != (
                    finding.line,
                    finding.column,
                    finding.end_line,
                    finding.end_column,
                )
            {
                return false;
            }
            let mut child = command;
            let mut overwritten = false;
            while let Some(parent) = parents.get(&child.id()).and_then(|id| tokens.get(id)) {
                let follows = |commands: &[shellcheck_rs::ast::Token]| {
                    commands.iter().any(|t| t.id() == child.id())
                        && commands.last().is_some_and(|t| t.id() != child.id())
                };
                match &*parent.inner {
                    InnerToken::T_BraceGroup(commands) => {
                        if parents
                            .get(&parent.id())
                            .and_then(|id| tokens.get(id))
                            .is_some_and(|t| matches!(&*t.inner, InnerToken::T_Function { .. }))
                        {
                            return overwritten
                                && commands.last().is_some_and(|t| t.id() == child.id());
                        }
                        overwritten |= follows(commands);
                    }
                    InnerToken::T_Subshell(commands) | InnerToken::T_Pipeline { commands, .. } => {
                        overwritten |= follows(commands);
                    }
                    InnerToken::T_IfExpression { clauses, elses } => {
                        overwritten |=
                            clauses.iter().any(|(_, body)| follows(body)) || follows(elses);
                    }
                    InnerToken::T_CaseExpression { cases, .. } => {
                        overwritten |= cases.iter().any(|(kind, _, body)| {
                            follows(body)
                                || (*kind != shellcheck_rs::ast::CaseType::CaseBreak
                                    && body.iter().any(|t| t.id() == child.id()))
                        });
                    }
                    InnerToken::T_DollarExpansion(_)
                    | InnerToken::T_Backticked(_)
                    | InnerToken::T_Banged(_)
                    | InnerToken::T_Backgrounded(_)
                    | InnerToken::T_CoProc { .. }
                    | InnerToken::T_SelectIn { .. }
                    | InnerToken::T_ForIn { .. }
                    | InnerToken::T_ForArithmetic { .. }
                    | InnerToken::T_WhileExpression { .. }
                    | InnerToken::T_UntilExpression { .. } => overwritten = true,
                    InnerToken::T_Function { .. } => return false,
                    _ => {}
                }
                child = parent;
            }
            false
        })
    })
}

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
        Some("sh" | "dash") => "dash",
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
/// The parse-error class: the oracle rejects the file outright, the port does
/// not, and the shell being checked agrees with the port that the script parses.
/// Whatever else the oracle reported before it gave up, the port must report
/// too. A script no shell accepts is not covered, and neither is any difference
/// that leaves the oracle's fatal codes in the port's own output.
pub fn sanctioned(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
    runner: Option<&Oracle>,
) -> Option<&'static Deviation> {
    // SC9001 is a documented extension. Require the exact finding to be
    // reproducible from the shebang alone; unrelated body diagnostics must
    // still agree, or independently satisfy an existing structural sanction.
    let added_paths: Vec<_> = port
        .iter()
        .filter(|k| k.code == 9001 && !oracle.contains(k))
        .collect();
    if !added_paths.is_empty() {
        let header_lines = usize::try_from(added_paths.iter().map(|k| k.end_line).max()?).ok()?;
        let header = format!(
            "{}\n",
            script
                .lines()
                .take(header_lines)
                .collect::<Vec<_>>()
                .join("\n")
        );
        let expected = crate::port_keys(&header, "-", shell).ok()?;
        if !added_paths.iter().all(|k| expected.contains(k)) {
            return None;
        }
        let remaining: Vec<_> = port
            .iter()
            .filter(|k| !added_paths.contains(k))
            .cloned()
            .collect();
        if remaining == oracle || sanctioned(script, shell, &remaining, oracle, runner).is_some() {
            return Some(&INTERPRETER_PATH_TYPO);
        }
        return None;
    }
    if added_dialect(script, shell, port, oracle, runner) {
        return Some(&ADDED_DIALECT);
    }
    if completed_statement_notes(script, shell, port, oracle) {
        return Some(&COMPLETED_PARSE_NOTES);
    }
    if unclosed_test_quote(script, port, oracle) {
        return Some(&UNCLOSED_TEST_QUOTE);
    }
    if function_tail_cd(script, shell, port, oracle) {
        return Some(&FUNCTION_TAIL_CD);
    }
    let port_codes = codes(port);
    let oracle_rejected = codes(oracle).contains(&1072)
        && oracle
            .iter()
            .all(|k| FATAL_PARSE_CODES.contains(&k.code) || port.contains(k));
    let port_parsed = !port_codes.iter().any(|c| FATAL_PARSE_CODES.contains(c));
    if !(oracle_rejected && port_parsed) {
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
    fn completed_notes_require_exact_independent_prefix_evidence() {
        let script = "echo $10\nif\n";
        let port = crate::port_keys(script, "-", Some("bash")).expect("port");
        let oracle: Vec<_> = port.iter().filter(|k| k.code != 1037).cloned().collect();
        assert!(completed_statement_notes(
            script,
            Some("bash"),
            &port,
            &oracle
        ));
        let mut shifted = port.clone();
        shifted.iter_mut().find(|k| k.code == 1037).unwrap().column += 1;
        assert!(!completed_statement_notes(
            script,
            Some("bash"),
            &shifted,
            &oracle
        ));
        let mut unrelated = port;
        unrelated.push(key(1100));
        assert!(!completed_statement_notes(
            script,
            Some("bash"),
            &unrelated,
            &oracle
        ));
    }

    #[test]
    fn quote_explanation_requires_an_unterminated_quote_and_exact_span() {
        let script = "[* '";
        let port = crate::port_keys(script, "-", Some("bash")).expect("port");
        let mut oracle = port.clone();
        oracle.iter_mut().find(|k| k.code == 1072).unwrap().message =
            "Expected comparison operator (don't wrap commands in []/[[]]). Fix any mentioned problems and try again.".into();
        if Command::new("bash").arg("--version").output().is_err() {
            return;
        }
        assert!(unclosed_test_quote(script, &port, &oracle));
        assert!(!unclosed_test_quote("echo ok", &port, &oracle));
        let mut shifted = port;
        shifted.iter_mut().find(|k| k.code == 1072).unwrap().column += 1;
        assert!(!unclosed_test_quote(script, &shifted, &oracle));
    }

    #[test]
    fn interpreter_path_extension_does_not_hide_other_differences() {
        let script = "#!/usr/bni/env bash\necho ok";
        let port = crate::port_keys(script, "-", Some("bash")).expect("port");
        let oracle: Vec<_> = port.iter().filter(|k| k.code != 9001).cloned().collect();
        assert_eq!(
            sanctioned(script, Some("bash"), &port, &oracle, None).map(|d| d.id),
            Some("interpreter-path-typo")
        );
        let mut unrelated = port.clone();
        unrelated.push(key(9999));
        assert!(sanctioned(script, Some("bash"), &unrelated, &oracle, None).is_none());
        let mut shifted = port;
        for k in &mut shifted {
            if k.code == 9001 {
                k.line += 1;
            }
        }
        assert!(sanctioned(script, Some("bash"), &shifted, &oracle, None).is_none());
    }

    #[test]
    fn only_proven_function_tail_cd_differences_are_sanctioned() {
        for script in [
            "f() { if true; then cd /missing; echo continued; fi; }",
            "f() { for x in a b; do cd /missing; done; }",
            "f() { select x in a b; do cd /missing; done; }",
            "f() { cd /missing | cat; }",
            "function f{1|cd !()'t'|o;}",
            "f() { ! cd /missing; }",
            "r(){!cd;}",
            "!/zsh\nf(){!cd;}",
            "!/zsh\nfunction f{cd |o;}",
            "!/zsh\nf(){coproc select x in `` do cd<'';done }",
            "r(){coproc N select x in `` do cd<'';done;}",
            "f() { echo $(cd /missing); }",
            "f() { coproc { cd /missing; }; }",
            "f() { cd /missing & }",
            "f() { case x in x) cd /missing; echo continued;; esac; }",
        ] {
            let port = crate::port_keys(script, "-", Some("bash")).expect("port");
            let oracle: Vec<_> = port.iter().filter(|k| k.code != 2164).cloned().collect();
            assert!(
                function_tail_cd(script, Some("bash"), &port, &oracle),
                "{script}"
            );
            let mut unrelated = oracle.clone();
            unrelated.push(key(9999));
            assert!(!function_tail_cd(script, Some("bash"), &port, &unrelated));
            let mut shifted = port.clone();
            shifted
                .iter_mut()
                .filter(|k| k.code == 2164)
                .for_each(|k| k.column += 1);
            assert!(!function_tail_cd(script, Some("bash"), &shifted, &oracle));
        }
        for script in [
            "f() { printf x | cd /missing; }",
            "cd /missing; echo continued",
            "f() { cd /missing; echo continued; }",
        ] {
            let port = crate::port_keys(script, "-", Some("bash")).expect("port");
            let oracle: Vec<_> = port.iter().filter(|k| k.code != 2164).cloned().collect();
            assert!(
                !function_tail_cd(script, Some("bash"), &port, &oracle),
                "{script}"
            );
        }
    }

    fn unsupported(code: i64, message: &str) -> CommentKey {
        CommentKey {
            message: message.to_string(),
            ..key(code)
        }
    }

    const SC1071: &str = "ShellCheck only supports sh/bash/dash/ksh/'busybox sh' scripts. Sorry!";

    #[test]
    fn a_zsh_shebang_the_oracle_refuses_is_checked_as_bash() {
        let script = "#!/bin/zsh\necho $x\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        assert!(port.iter().any(|k| k.code == 2154), "{port:?}");
        let oracle = [unsupported(1071, SC1071)];
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        assert_eq!(
            sanctioned(script, None, &port, &oracle, Some(&runner)).map(|d| d.id),
            Some("added-dialect")
        );
        assert!(sanctioned(script, None, &port, &oracle, None).is_none());
        assert!(sanctioned(script, Some("bash"), &port, &oracle, Some(&runner)).is_none());
    }

    #[test]
    fn a_code_the_matrix_drops_for_zsh_is_sanctioned_against_the_bash_floor() {
        let script = "#!/bin/zsh\nx=\"a b\"; echo $x\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        assert_eq!(port, Vec::<CommentKey>::new());
        let bash = "#!/bin/bash\nx=\"a b\"; echo $x\n";
        let bash_port = crate::port_keys(bash, "-", None).expect("port");
        assert!(bash_port.iter().any(|k| k.code == 2086), "{bash_port:?}");
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(script, None).expect("oracle runs");
        let oracle = crate::oracle_keys(&comments);
        assert!(
            oracle.iter().any(|k| k.code == 1071 && k.message == SC1071),
            "{oracle:?}"
        );
        assert_eq!(
            sanctioned(script, None, &port, &oracle, Some(&runner)).map(|d| d.id),
            Some("added-dialect")
        );
        let (comments, _) = runner.check_one(script, Some("bash")).expect("oracle runs");
        let floor = crate::oracle_keys(&comments);
        assert!(floor.iter().any(|k| k.code == 2086), "{floor:?}");
        let mut extra = port;
        extra.push(key(9999));
        assert!(sanctioned(script, None, &extra, &oracle, Some(&runner)).is_none());
        let (comments, _) = runner.check_one(bash, None).expect("oracle runs");
        let bash_oracle = crate::oracle_keys(&comments);
        assert_eq!(bash_oracle, bash_port);
        let without: Vec<_> = bash_port
            .iter()
            .filter(|k| k.code != 2086)
            .cloned()
            .collect();
        assert!(sanctioned(bash, None, &without, &bash_oracle, Some(&runner)).is_none());
    }

    #[test]
    fn a_mksh_directive_the_oracle_rejects_is_checked_as_ksh() {
        let script = "# shellcheck shell=mksh\n[[ -n $1 ]]\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        assert!(port.iter().all(|k| k.code != 1103), "{port:?}");
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(script, None).expect("oracle runs");
        let oracle = crate::oracle_keys(&comments);
        assert!(oracle.iter().any(|k| k.code == 1103), "{oracle:?}");
        assert_eq!(
            sanctioned(script, None, &port, &oracle, Some(&runner)).map(|d| d.id),
            Some("added-dialect")
        );
    }

    #[test]
    fn added_dialect_requires_the_oracle_to_have_said_only_that_it_refused() {
        let script = "#!/bin/zsh\necho $x\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        let runner = crate::oracle::test_oracle();
        let mut extra = vec![unsupported(1071, SC1071)];
        extra.push(key(9999));
        assert!(sanctioned(script, None, &port, &extra, runner.as_ref()).is_none());
        let shifted = [CommentKey {
            column: 2,
            ..unsupported(1071, SC1071)
        }];
        assert!(sanctioned(script, None, &port, &shifted, runner.as_ref()).is_none());
        let mut unrelated = port;
        unrelated.push(key(9999));
        let oracle = [unsupported(1071, SC1071)];
        assert!(sanctioned(script, None, &unrelated, &oracle, runner.as_ref()).is_none());
    }

    #[test]
    fn a_zsh_body_the_oracle_never_parsed_is_sanctioned_even_with_sc1071_disabled() {
        let script = "#!/bin/zsh\n# shellcheck disable=SC1071\nfor f (a b); echo $f\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        assert!(port.iter().any(|k| k.code == 1073), "{port:?}");
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        assert_eq!(
            sanctioned(script, None, &port, &[], Some(&runner)).map(|d| d.id),
            Some("added-dialect")
        );
    }

    #[test]
    fn added_dialect_requires_the_oracle_code_to_match_upstreams_verdict() {
        let runner = crate::oracle::test_oracle();
        let zsh = "#!/bin/zsh\necho $x\n";
        let port = crate::port_keys(zsh, "-", None).expect("port");
        assert!(sanctioned(zsh, None, &port, &[key(1008)], runner.as_ref()).is_none());
        assert!(sanctioned(zsh, None, &port, &[key(1103)], runner.as_ref()).is_none());
        let mksh = "#!/bin/mksh\necho $x\n";
        let port = crate::port_keys(mksh, "-", None).expect("port");
        assert!(sanctioned(mksh, None, &port, &[key(1071)], runner.as_ref()).is_none());
    }

    #[test]
    fn added_dialect_requires_the_shebang_to_name_an_added_dialect() {
        let runner = crate::oracle::test_oracle();
        let oracle = [unsupported(1071, SC1071)];
        for script in [
            "#!/bin/bash\necho $x\n",
            "#!/usr/bin/python\necho $x\n",
            "echo $x\n",
        ] {
            let port = crate::port_keys(script, "-", None).expect("port");
            assert!(
                sanctioned(script, None, &port, &oracle, runner.as_ref()).is_none(),
                "{script}"
            );
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
        assert!(sanctioned("! # c", Some("bash"), &[], &oracle, None).is_some());
    }

    #[test]
    fn a_problem_both_tools_report_does_not_block_the_sanction() {
        let oracle = [key(1035), key(1072)];
        assert!(sanctioned("!;true", Some("bash"), &[key(1035)], &oracle, None).is_some());
        assert!(sanctioned("!;true", Some("bash"), &[], &oracle, None).is_none());
    }

    #[test]
    fn a_script_the_shell_also_rejects_is_not_sanctioned() {
        let oracle = [key(1073), key(1072)];
        assert!(sanctioned("if", Some("bash"), &[], &oracle, None).is_none());
        // dash rejects `! # c`, so for a POSIX target the oracle is right.
        assert!(sanctioned("! # c", Some("dash"), &[], &oracle, None).is_none());
    }

    #[test]
    fn an_ordinary_difference_is_never_sanctioned() {
        // Same script, but the disagreement is about an analysis code rather
        // than about whether the file parses at all.
        assert!(sanctioned("echo $1", Some("bash"), &[key(2086)], &[], None).is_none());
        assert!(sanctioned("! # c", Some("bash"), &[key(1072)], &[key(1072)], None).is_none());
    }
}
