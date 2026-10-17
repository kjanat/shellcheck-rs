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

const SIGNAL_ONLY_CLEANUP_TRAP: Deviation = Deviation {
    id: "signal-only-cleanup-trap",
    what: "the port warns that a cleanup trap handles signals without EXIT",
};

const STABLE_TRAP_VARIABLES: Deviation = Deviation {
    id: "stable-trap-variables",
    what: "the port withholds SC2064 for trap variables assigned before the trap and never \
           written after it",
};

/// The codes upstream emits for an unknown interpreter: SC1071 for a shell on
/// its refusal list, SC1008 for any other shebang, SC1103 for a `shell=`
/// directive.
const UNKNOWN_INTERPRETER_CODES: [i64; 3] = [1071, 1008, 1103];

fn parsed_root(script: &str) -> Option<shellcheck_rs::ast::Token> {
    shellcheck_rs::parser::parse_script_with("-", script, false, None)
        .root
        .or_else(|| {
            let first = script.lines().next()?;
            shellcheck_rs::parser::parse_script_with("-", &format!("{first}\n"), false, None).root
        })
}

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
) -> Option<Vec<CommentKey>> {
    if shell.is_some() {
        return None;
    }
    let root = parsed_root(script)?;
    let dialect = shellcheck_rs::analyzer_lib::named_dialect(&root).filter(|d| d.is_added())?;
    let flagged: Vec<_> = oracle
        .iter()
        .filter(|k| UNKNOWN_INTERPRETER_CODES.contains(&k.code))
        .collect();
    if flagged.len() > 1
        || port
            .iter()
            .any(|k| UNKNOWN_INTERPRETER_CODES.contains(&k.code))
    {
        return None;
    }
    let refused = upstream_refuses_body(&root);
    let consistent = flagged.first().is_none_or(|flag| match flag.code {
        1071 => refused && (flag.line, flag.column) == (1, 1),
        1008 => !refused && (flag.line, flag.column) == (1, 1),
        _ => !refused,
    });
    if !consistent || (refused && oracle.len() != flagged.len()) {
        return None;
    }
    let floor_name = Dialect::from(dialect.floor()).name();
    let (comments, _) = runner?.check_one(script, Some(floor_name)).ok()?;
    let policy = shellcheck_rs::dialect_policy::Policy::of(dialect, &root);
    Some(
        crate::oracle_keys(&comments)
            .into_iter()
            .filter(|k| k.code != 1103 && policy.keeps(k.code))
            .collect(),
    )
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
                shell.and_then(crate::parse_dialect).map(Dialect::floor),
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
        shell.and_then(crate::parse_dialect).map(Dialect::floor),
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

fn port_parameters(
    script: &str,
    shell: Option<&str>,
) -> Option<shellcheck_rs::analyzer_lib::Parameters> {
    let dialect = shell.and_then(crate::parse_dialect);
    let parsed = shellcheck_rs::parser::parse_script_with(
        "-",
        script,
        shell.is_some(),
        dialect.map(Dialect::floor),
    );
    Some(shellcheck_rs::analyzer_lib::make_parameters_as(
        parsed.root?,
        parsed.positions,
        dialect,
        None,
        None,
    ))
}

fn without_withheld_traps(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
) -> Option<Vec<CommentKey>> {
    if !oracle.iter().any(|k| k.code == 2064 && !port.contains(k)) {
        return None;
    }
    let params = port_parameters(script, shell)?;
    let withheld = crate::json1_keys(
        &shellcheck_rs::checks::commands::withheld_trap_warnings(&params),
        script,
        "-",
    )
    .ok()?;
    let rest: Vec<_> = oracle
        .iter()
        .filter(|k| k.code != 2064 || port.contains(k) || !withheld.contains(k))
        .cloned()
        .collect();
    (rest.len() < oracle.len()).then_some(rest)
}

fn without_cleanup_traps(
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
) -> Option<Vec<CommentKey>> {
    if !port.iter().any(|k| k.code == 9002 && !oracle.contains(k)) {
        return None;
    }
    let params = port_parameters(script, shell)?;
    let reported = crate::json1_keys(
        &shellcheck_rs::analytics::cleanup_trap_warnings(&params),
        script,
        "-",
    )
    .ok()?;
    let rest: Vec<_> = port
        .iter()
        .filter(|k| k.code != 9002 || oracle.contains(k) || !reported.contains(k))
        .cloned()
        .collect();
    (rest.len() < port.len()).then_some(rest)
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

const CLASSES: [&Deviation; 8] = [
    &INTERPRETER_PATH_TYPO,
    &SIGNAL_ONLY_CLEANUP_TRAP,
    &STABLE_TRAP_VARIABLES,
    &ADDED_DIALECT,
    &COMPLETED_PARSE_NOTES,
    &UNCLOSED_TEST_QUOTE,
    &FUNCTION_TAIL_CD,
    &FALSE_PARSE_ERROR,
];

/// Is this difference one the port is entitled to?
///
/// Returns every class that took part, outermost first. An empty list means
/// the difference stands.
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
) -> Vec<&'static Deviation> {
    explain(&CLASSES, script, shell, port, oracle, runner).unwrap_or_default()
}

fn agree_or_explain(
    classes: &[&'static Deviation],
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
    runner: Option<&Oracle>,
) -> Option<Vec<&'static Deviation>> {
    if port == oracle {
        Some(Vec::new())
    } else {
        explain(classes, script, shell, port, oracle, runner)
    }
}

fn explain(
    classes: &[&'static Deviation],
    script: &str,
    shell: Option<&str>,
    port: &[CommentKey],
    oracle: &[CommentKey],
    runner: Option<&Oracle>,
) -> Option<Vec<&'static Deviation>> {
    let enabled = |d: &Deviation| classes.iter().any(|c| c.id == d.id);
    let with = |d: &'static Deviation, rest: Option<Vec<&'static Deviation>>| {
        rest.map(|ids| std::iter::once(d).chain(ids).collect())
    };
    // SC9001 is a documented extension. Require the exact finding to be
    // reproducible from the shebang alone; unrelated body diagnostics must
    // still agree, or independently satisfy an existing structural sanction.
    let added_paths: Vec<_> = port
        .iter()
        .filter(|k| k.code == 9001 && !oracle.contains(k))
        .collect();
    if enabled(&INTERPRETER_PATH_TYPO) && !added_paths.is_empty() {
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
        return with(
            &INTERPRETER_PATH_TYPO,
            agree_or_explain(classes, script, shell, &remaining, oracle, runner),
        );
    }
    if enabled(&SIGNAL_ONLY_CLEANUP_TRAP)
        && let Some(rest) = without_cleanup_traps(script, shell, port, oracle)
    {
        return with(
            &SIGNAL_ONLY_CLEANUP_TRAP,
            agree_or_explain(classes, script, shell, &rest, oracle, runner),
        );
    }
    if enabled(&STABLE_TRAP_VARIABLES)
        && let Some(rest) = without_withheld_traps(script, shell, port, oracle)
    {
        return with(
            &STABLE_TRAP_VARIABLES,
            agree_or_explain(classes, script, shell, port, &rest, runner),
        );
    }
    if enabled(&ADDED_DIALECT)
        && let Some(floor) = added_dialect(script, shell, port, oracle, runner)
    {
        let others: Vec<_> = classes
            .iter()
            .copied()
            .filter(|c| c.id != ADDED_DIALECT.id)
            .collect();
        return with(
            &ADDED_DIALECT,
            agree_or_explain(&others, script, shell, port, &floor, runner),
        );
    }
    if enabled(&COMPLETED_PARSE_NOTES) && completed_statement_notes(script, shell, port, oracle) {
        return Some(vec![&COMPLETED_PARSE_NOTES]);
    }
    if enabled(&UNCLOSED_TEST_QUOTE) && unclosed_test_quote(script, port, oracle) {
        return Some(vec![&UNCLOSED_TEST_QUOTE]);
    }
    if enabled(&FUNCTION_TAIL_CD) && function_tail_cd(script, shell, port, oracle) {
        return Some(vec![&FUNCTION_TAIL_CD]);
    }
    if !enabled(&FALSE_PARSE_ERROR) {
        return None;
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
        Some(true) => Some(vec![&FALSE_PARSE_ERROR]),
        // Either the shell rejects it too (so the oracle was right), or there is
        // no shell to ask (so nothing is established).
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(deviations: &[&Deviation]) -> Vec<&'static str> {
        deviations.iter().map(|d| d.id).collect()
    }

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
            ids(&sanctioned(script, Some("bash"), &port, &oracle, None)),
            ["interpreter-path-typo"]
        );
        let mut unrelated = port.clone();
        unrelated.push(key(9999));
        assert!(sanctioned(script, Some("bash"), &unrelated, &oracle, None).is_empty());
        let mut shifted = port;
        for k in &mut shifted {
            if k.code == 9001 {
                k.line += 1;
            }
        }
        assert!(sanctioned(script, Some("bash"), &shifted, &oracle, None).is_empty());
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
            ids(&sanctioned(script, None, &port, &oracle, Some(&runner))),
            ["added-dialect"]
        );
        assert!(sanctioned(script, None, &port, &oracle, None).is_empty());
        assert!(sanctioned(script, Some("bash"), &port, &oracle, Some(&runner)).is_empty());
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
            ids(&sanctioned(script, None, &port, &oracle, Some(&runner))),
            ["added-dialect"]
        );
        let (comments, _) = runner.check_one(script, Some("bash")).expect("oracle runs");
        let floor = crate::oracle_keys(&comments);
        assert!(floor.iter().any(|k| k.code == 2086), "{floor:?}");
        let mut extra = port;
        extra.push(key(9999));
        assert!(sanctioned(script, None, &extra, &oracle, Some(&runner)).is_empty());
        let (comments, _) = runner.check_one(bash, None).expect("oracle runs");
        let bash_oracle = crate::oracle_keys(&comments);
        assert_eq!(bash_oracle, bash_port);
        let without: Vec<_> = bash_port
            .iter()
            .filter(|k| k.code != 2086)
            .cloned()
            .collect();
        assert!(sanctioned(bash, None, &without, &bash_oracle, Some(&runner)).is_empty());
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
            ids(&sanctioned(script, None, &port, &oracle, Some(&runner))),
            ["added-dialect"]
        );
    }

    #[test]
    fn added_dialect_requires_the_oracle_to_have_said_only_that_it_refused() {
        let script = "#!/bin/zsh\necho $x\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        let runner = crate::oracle::test_oracle();
        let mut extra = vec![unsupported(1071, SC1071)];
        extra.push(key(9999));
        assert!(sanctioned(script, None, &port, &extra, runner.as_ref()).is_empty());
        let shifted = [CommentKey {
            column: 2,
            ..unsupported(1071, SC1071)
        }];
        assert!(sanctioned(script, None, &port, &shifted, runner.as_ref()).is_empty());
        let mut unrelated = port;
        unrelated.push(key(9999));
        let oracle = [unsupported(1071, SC1071)];
        assert!(sanctioned(script, None, &unrelated, &oracle, runner.as_ref()).is_empty());
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
            ids(&sanctioned(script, None, &port, &[], Some(&runner))),
            ["added-dialect"]
        );
    }

    #[test]
    fn added_dialect_requires_the_oracle_code_to_match_upstreams_verdict() {
        let runner = crate::oracle::test_oracle();
        let zsh = "#!/bin/zsh\necho $x\n";
        let port = crate::port_keys(zsh, "-", None).expect("port");
        assert!(sanctioned(zsh, None, &port, &[key(1008)], runner.as_ref()).is_empty());
        assert!(sanctioned(zsh, None, &port, &[key(1103)], runner.as_ref()).is_empty());
        let mksh = "#!/bin/mksh\necho $x\n";
        let port = crate::port_keys(mksh, "-", None).expect("port");
        assert!(sanctioned(mksh, None, &port, &[key(1071)], runner.as_ref()).is_empty());
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
                sanctioned(script, None, &port, &oracle, runner.as_ref()).is_empty(),
                "{script}"
            );
        }
    }

    const SC2064: &str =
        "Use single quotes, otherwise this expands now rather than when signalled.";

    const STABLE_TRAP: &str = "ENGINE=podman; trap \"$ENGINE rm -f x\" EXIT\n";

    fn sc2064(column: i64, end_column: i64) -> CommentKey {
        CommentKey {
            column,
            end_column,
            level: "warning".to_string(),
            message: SC2064.to_string(),
            ..key(2064)
        }
    }

    #[test]
    fn a_stable_trap_variable_the_oracle_flags_is_sanctioned() {
        let port = crate::port_keys(STABLE_TRAP, "-", None).expect("port");
        assert!(port.iter().all(|k| k.code != 2064), "{port:?}");
        let mut oracle = port.clone();
        oracle.push(sc2064(22, 29));
        assert_eq!(
            ids(&sanctioned(STABLE_TRAP, None, &port, &oracle, None)),
            ["stable-trap-variables"]
        );
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(STABLE_TRAP, None).expect("oracle runs");
        assert_eq!(crate::oracle_keys(&comments), oracle);
    }

    #[test]
    fn stable_trap_variables_require_the_withheld_span_and_nothing_else() {
        let port = crate::port_keys(STABLE_TRAP, "-", None).expect("port");
        let mut shifted = port.clone();
        shifted.push(sc2064(23, 30));
        assert!(sanctioned(STABLE_TRAP, None, &port, &shifted, None).is_empty());
        let mut oracle = port.clone();
        oracle.push(sc2064(22, 29));
        let mut unrelated = oracle.clone();
        unrelated.push(key(9999));
        assert!(sanctioned(STABLE_TRAP, None, &port, &unrelated, None).is_empty());
        let mut extra = port;
        extra.push(key(9999));
        assert!(sanctioned(STABLE_TRAP, None, &extra, &oracle, None).is_empty());
    }

    #[test]
    fn a_trap_variable_written_afterwards_is_not_sanctioned() {
        let script = "trap \"$x\" INT; x=1\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        assert!(port.contains(&sc2064(7, 9)), "{port:?}");
        let without: Vec<_> = port.iter().filter(|k| k.code != 2064).cloned().collect();
        assert!(sanctioned(script, None, &without, &port, None).is_empty());
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(script, None).expect("oracle runs");
        assert_eq!(crate::oracle_keys(&comments), port);
    }

    #[test]
    fn stable_trap_variables_fail_closed_when_the_script_does_not_parse() {
        let script = "ENGINE=podman; trap \"$ENGINE rm -f x\" EXIT\nif\n";
        assert!(
            shellcheck_rs::parser::parse_script_with("-", script, false, None)
                .root
                .is_none()
        );
        let port = crate::port_keys(script, "-", None).expect("port");
        let mut oracle = port.clone();
        oracle.push(sc2064(22, 29));
        assert!(without_withheld_traps(script, None, &port, &oracle).is_none());
        assert!(sanctioned(script, None, &port, &oracle, None).is_empty());
    }

    const SC9002: &str = "This cleanup trap only handles signals. Consider EXIT to also clean up after errors, end of input, and normal exit.";

    const CLEANUP_TRAP: &str = "trap 'cleanup' INT\n";

    fn sc9002(column: i64, end_column: i64) -> CommentKey {
        CommentKey {
            column,
            end_column,
            level: "warning".to_string(),
            message: SC9002.to_string(),
            ..key(9002)
        }
    }

    #[test]
    fn a_signal_only_cleanup_trap_the_oracle_ignores_is_sanctioned() {
        let port = crate::port_keys(CLEANUP_TRAP, "-", None).expect("port");
        assert!(port.contains(&sc9002(1, 19)), "{port:?}");
        let oracle: Vec<_> = port.iter().filter(|k| k.code != 9002).cloned().collect();
        assert_eq!(
            ids(&sanctioned(CLEANUP_TRAP, None, &port, &oracle, None)),
            ["signal-only-cleanup-trap"]
        );
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(CLEANUP_TRAP, None).expect("oracle runs");
        assert_eq!(crate::oracle_keys(&comments), oracle);
    }

    #[test]
    fn signal_only_cleanup_traps_require_the_reported_span_and_nothing_else() {
        let port = crate::port_keys(CLEANUP_TRAP, "-", None).expect("port");
        let oracle: Vec<_> = port.iter().filter(|k| k.code != 9002).cloned().collect();
        let mut shifted = port.clone();
        shifted
            .iter_mut()
            .filter(|k| k.code == 9002)
            .for_each(|k| k.column += 1);
        assert!(sanctioned(CLEANUP_TRAP, None, &shifted, &oracle, None).is_empty());
        let mut unrelated = port.clone();
        unrelated.push(key(9999));
        assert!(sanctioned(CLEANUP_TRAP, None, &unrelated, &oracle, None).is_empty());
        let mut missing = oracle;
        missing.push(key(9999));
        assert!(sanctioned(CLEANUP_TRAP, None, &port, &missing, None).is_empty());
    }

    #[test]
    fn a_signal_only_cleanup_trap_fails_closed_when_the_script_does_not_parse() {
        let script = "trap 'cleanup' INT\nif\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        let mut added = port.clone();
        added.push(sc9002(1, 19));
        assert!(without_cleanup_traps(script, None, &added, &port).is_none());
        assert!(sanctioned(script, None, &added, &port, None).is_empty());
    }

    #[test]
    fn a_stable_signal_cleanup_trap_needs_both_trap_classes() {
        let script = "ENGINE=podman; trap \"$ENGINE rm -f x\" INT\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        assert!(port.contains(&sc9002(16, 42)), "{port:?}");
        assert!(port.iter().all(|k| k.code != 2064), "{port:?}");
        let mut oracle: Vec<_> = port.iter().filter(|k| k.code != 9002).cloned().collect();
        oracle.push(sc2064(22, 29));
        assert_eq!(
            ids(&sanctioned(script, None, &port, &oracle, None)),
            ["signal-only-cleanup-trap", "stable-trap-variables"]
        );
        for excluded in [&SIGNAL_ONLY_CLEANUP_TRAP, &STABLE_TRAP_VARIABLES] {
            let classes = without(&[excluded]);
            assert!(
                explain(&classes, script, None, &port, &oracle, None).is_none(),
                "{}",
                excluded.id
            );
        }
        let mut shifted = oracle.clone();
        shifted
            .iter_mut()
            .filter(|k| k.code == 2064)
            .for_each(|k| k.column += 1);
        assert!(sanctioned(script, None, &port, &shifted, None).is_empty());
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(script, None).expect("oracle runs");
        assert_eq!(crate::oracle_keys(&comments), oracle);
    }

    fn without(excluded: &[&Deviation]) -> Vec<&'static Deviation> {
        CLASSES
            .iter()
            .copied()
            .filter(|c| excluded.iter().all(|e| e.id != c.id))
            .collect()
    }

    #[test]
    fn a_stable_signal_cleanup_trap_in_zsh_needs_all_three_classes() {
        let script = "#!/bin/zsh\nENGINE=podman; trap \"$ENGINE rm -f x\" INT\n";
        let port = crate::port_keys(script, "-", None).expect("port");
        let Some(runner) = crate::oracle::test_oracle() else {
            return;
        };
        let (comments, _) = runner.check_one(script, None).expect("oracle runs");
        let oracle = crate::oracle_keys(&comments);
        assert_eq!(
            ids(&sanctioned(script, None, &port, &oracle, Some(&runner))),
            [
                "signal-only-cleanup-trap",
                "added-dialect",
                "stable-trap-variables"
            ]
        );
        let three = [
            &SIGNAL_ONLY_CLEANUP_TRAP,
            &ADDED_DIALECT,
            &STABLE_TRAP_VARIABLES,
        ];
        for mask in 1..8 {
            let excluded: Vec<_> = (0..3)
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| three[i])
                .collect();
            let classes = without(&excluded);
            assert!(
                explain(&classes, script, None, &port, &oracle, Some(&runner)).is_none(),
                "{:?}",
                ids(&excluded)
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
        assert_eq!(
            ids(&sanctioned("! # c", Some("bash"), &[], &oracle, None)),
            ["upstream-false-parse-error"]
        );
    }

    #[test]
    fn a_problem_both_tools_report_does_not_block_the_sanction() {
        let oracle = [key(1035), key(1072)];
        assert_eq!(
            ids(&sanctioned(
                "!;true",
                Some("bash"),
                &[key(1035)],
                &oracle,
                None
            )),
            ["upstream-false-parse-error"]
        );
        assert!(sanctioned("!;true", Some("bash"), &[], &oracle, None).is_empty());
    }

    #[test]
    fn a_script_the_shell_also_rejects_is_not_sanctioned() {
        let oracle = [key(1073), key(1072)];
        assert!(sanctioned("if", Some("bash"), &[], &oracle, None).is_empty());
        // dash rejects `! # c`, so for a POSIX target the oracle is right.
        assert!(sanctioned("! # c", Some("dash"), &[], &oracle, None).is_empty());
    }

    #[test]
    fn an_ordinary_difference_is_never_sanctioned() {
        // Same script, but the disagreement is about an analysis code rather
        // than about whether the file parses at all.
        assert!(sanctioned("echo $1", Some("bash"), &[key(2086)], &[], None).is_empty());
        assert!(sanctioned("! # c", Some("bash"), &[key(1072)], &[key(1072)], None).is_empty());
    }
}
