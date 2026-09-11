//! Ported check batch f. See rust/PORTING.md.
//!
//! Implemented (logic ports; NOT registered — see the blocker below):
//! - SC2015  checkShorthandIf — `A && B || C` is not if-then-else
//! - SC2166  checkConditionalAndOrs (the `[ .. -a .. ]` / `[ .. -o .. ]` branches)
//!
//! Skipped:
//! - SC2128  checkArrayWithoutIndex — needs `doVariableFlowAnalysis`/`variableFlow`
//!   (dataflow), which is not yet ported.
//! - SC2145 / SC2077 — already handled elsewhere / not assigned.
//!
//! BLOCKER — parser node positioning (cannot register these two):
//! The check logic below is correct: against the oracle corpus each fires on
//! exactly the right scripts (SC2015: 3/3, SC2166: 8/8). But every diagnostic
//! lands at the wrong COLUMN, so all count as `extra` under the conformance
//! harness, and the hard rule forbids registering a check with `extra > 0`.
//!
//! The Haskell oracle positions the binary AST nodes at their *operator token*:
//! `T_AndIf`/`T_OrIf` take the id of the `&&`/`||` token (Parser.hs readAndOr),
//! and `TC_And`/`TC_Or` take the id of the `-a`/`-o`/`&&`/`||` operator
//! (readAndOrOp). The Rust parser instead assigns these nodes a span covering
//! the whole `lhs .. rhs` (parser.rs `read_and_or` and `read_cond_or`/
//! `read_cond_and`, all via `next_id_between(lhs.start, rhs.end)`), and there is
//! no separate operator id to emit on. The emit API positions a comment solely
//! from `token_positions[id]`, so matching the oracle requires the parser to
//! record the operator position for these nodes — a change to `parser.rs`, which
//! this batch may not edit. Once the parser positions `T_AndIf`/`T_OrIf`/
//! `TC_And`/`TC_Or` at their operator (as Haskell does), register the two checks
//! below and they should reach `extra == 0`.
//!
//! Note: `checkConditionalAndOrs` in Haskell also emits SC2107/2108/2109/2110;
//! only the SC2166 branches are ported here (the others are out of scope).
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::interface::Shell;

pub fn register(c: &mut Checker) {
    // Enabled now that the parser anchors T_OrIf/T_AndIf/TC_And/TC_Or on the
    // operator token (matching ShellCheck). SC2128 still needs dataflow (skipped).
    c.node(check_shorthand_if);
    c.node(check_conditional_and_ors);
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib/AnalyzerLib; kept local so this
// module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

fn basename(path: &str) -> String {
    match path.rsplit('/').next() {
        Some(x) => x.to_string(),
        None => path.to_string(),
    }
}

/// `getWordParts`.
fn get_word_parts(t: &Token) -> Vec<&Token> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(l) => l.iter().flat_map(get_word_parts).collect(),
        T_DoubleQuoted(l) => l.iter().collect(),
        TA_Expansion(l) => l.iter().flat_map(get_word_parts).collect(),
        _ => vec![t],
    }
}

/// `isFlag`: word whose first part is an unquoted `-...` literal.
fn is_flag(t: &Token) -> bool {
    match get_word_parts(t).first() {
        Some(w) => matches!(&*w.inner, InnerToken::T_Literal(s) if s.starts_with('-')),
        None => false,
    }
}

/// `getCommand`: unwrap redirections/annotations to the T_SimpleCommand.
fn get_command(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command(cmd),
        InnerToken::T_Annotation { token, .. } => get_command(token),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        _ => None,
    }
}

fn simple_command_words(t: &Token) -> Option<&Vec<Token>> {
    let cmd = get_command(t)?;
    if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
        Some(words)
    } else {
        None
    }
}

/// `getEffectiveCommandToken` for exec: parse `getBsdOpts "cla:"`.
fn exec_effective(args: &[Token]) -> Option<&Token> {
    fn needs_arg(c: char) -> Option<bool> {
        match c {
            'c' | 'l' => Some(false),
            'a' => Some(true),
            _ => None,
        }
    }
    let mut i = 0;
    while i < args.len() {
        let s = astlib::get_literal_string(&args[i]).unwrap_or_else(|| "\0".to_string());
        if s == "--" {
            return args.get(i + 1);
        } else if s.starts_with("--") {
            return None;
        } else if s.starts_with('-') && s.len() > 1 {
            let cluster: Vec<char> = s[1..].chars().collect();
            let mut ci = 0;
            loop {
                if ci >= cluster.len() {
                    i += 1;
                    break;
                }
                match needs_arg(cluster[ci]) {
                    None => return None,
                    Some(false) => ci += 1,
                    Some(true) => {
                        if ci + 1 == cluster.len() {
                            i += 2;
                        } else {
                            i += 1;
                        }
                        break;
                    }
                }
            }
        } else {
            return Some(&args[i]);
        }
    }
    None
}

/// `getCommandName`: resolving `command`/`builtin`/`busybox`/`run`/`exec` prefixes.
fn get_command_name(t: &Token) -> Option<String> {
    let words = simple_command_words(t)?;
    let w = words.first()?;
    let s = astlib::get_literal_string(w)?;
    let rest = &words[1..];
    let effective: Option<&Token> = match s.as_str() {
        "busybox" | "builtin" | "command" | "run" => rest.first().filter(|a| !is_flag(a)),
        "exec" => exec_effective(rest),
        _ => None,
    };
    match effective {
        Some(tok) => astlib::get_literal_string(tok),
        None => Some(s),
    }
}

fn get_command_basename(t: &Token) -> Option<String> {
    get_command_name(t).map(|s| basename(&s))
}

/// `isCommand token str`: command name equals `str` or ends with `/str`.
fn is_command(t: &Token, str: &str) -> bool {
    match get_command_name(t) {
        Some(name) => name == str || name.ends_with(&format!("/{}", str)),
        None => false,
    }
}

/// `isAssignment`.
fn is_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => is_assignment(cmd),
        InnerToken::T_SimpleCommand { assignments, words } => {
            !assignments.is_empty() && words.is_empty()
        }
        InnerToken::T_Assignment { .. } => true,
        InnerToken::T_Annotation { token, .. } => is_assignment(token),
        _ => false,
    }
}

/// `isTestCommand`.
fn is_test_command(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Condition { .. } => true,
        InnerToken::T_SimpleCommand { .. } => is_command(t, "test"),
        InnerToken::T_Redirecting { cmd, .. } => is_test_command(cmd),
        InnerToken::T_Annotation { token, .. } => is_test_command(token),
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => {
            is_test_command(&commands[0])
        }
        _ => false,
    }
}

/// Condition-children of a parent node, per `isCondition`'s `getConditionChildren`.
fn condition_children(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_AndIf { lhs, .. } => vec![lhs],
        InnerToken::T_OrIf { lhs, .. } => vec![lhs],
        InnerToken::T_IfExpression { clauses, .. } => {
            // concatMap (take 1 . reverse . fst) conditions
            clauses.iter().filter_map(|(cond, _)| cond.last()).collect()
        }
        InnerToken::T_WhileExpression { condition, .. } => condition.last().into_iter().collect(),
        InnerToken::T_UntilExpression { condition, .. } => condition.last().into_iter().collect(),
        _ => vec![],
    }
}

/// `isCondition (getPath ..)`: walking from `t` up to the root, is each node a
/// condition-child of its parent (or is any node a bats test)?
fn in_condition(params: &Parameters, t: &Token) -> bool {
    let mut child = t;
    loop {
        // `go _ _ T_BatsTest{} = True`: any node examined that is a bats test.
        if matches!(&*child.inner, InnerToken::T_BatsTest { .. }) {
            return true;
        }
        let parent = match params.parent(child) {
            Some(p) => p,
            None => return false,
        };
        if condition_children(parent)
            .iter()
            .any(|c| c.id() == child.id())
        {
            return true;
        }
        child = parent;
    }
}

// ---------------------------------------------------------------------------
// SC2015 — checkShorthandIf
// ---------------------------------------------------------------------------

fn check_shorthand_if(params: &Parameters, x: &Token, out: &mut Out) {
    // x@(T_OrIf _ (T_AndIf id _ b) (T_Pipeline _ _ t))
    let (or_lhs, or_rhs) = match &*x.inner {
        InnerToken::T_OrIf { lhs, rhs } => (lhs, rhs),
        _ => return,
    };
    let (and_id, b) = match &*or_lhs.inner {
        InnerToken::T_AndIf { rhs, .. } => (or_lhs.id(), rhs),
        _ => return,
    };
    let commands = match &*or_rhs.inner {
        InnerToken::T_Pipeline { commands, .. } => commands,
        _ => return,
    };

    // isOk [t] = isAssignment t || basename in [echo, exit, return, printf, true, :]
    let is_ok = if commands.len() == 1 {
        let cmd = &commands[0];
        is_assignment(cmd)
            || get_command_basename(cmd)
                .map(|name| {
                    matches!(
                        name.as_str(),
                        "echo" | "exit" | "return" | "printf" | "true" | ":"
                    )
                })
                .unwrap_or(false)
    } else {
        false
    };

    if !(is_ok || in_condition(params, x)) && !is_test_command(b) {
        info(
            out,
            and_id,
            2015,
            "Note that A && B || C is not if-then-else. C may run when A is true.",
        );
    }
}

// ---------------------------------------------------------------------------
// SC2166 — checkConditionalAndOrs (SC2166 branches only)
// ---------------------------------------------------------------------------

fn check_conditional_and_ors(_params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_And {
            typ: ConditionType::SingleBracket,
            op,
            ..
        } if op == "-a" => {
            warn(
                out,
                t.id(),
                2166,
                "Prefer [ p ] && [ q ] as [ p -a q ] is not well defined.",
            );
        }
        InnerToken::TC_Or {
            typ: ConditionType::SingleBracket,
            op,
            ..
        } if op == "-o" => {
            warn(
                out,
                t.id(),
                2166,
                "Prefer [ p ] || [ q ] as [ p -o q ] is not well defined.",
            );
        }
        _ => {}
    }
}
