//! Ported check batch k. See rust/PORTING.md.
//!
//! Ported (pure AST / conditions):
//! - SC2107  checkConditionalAndOrs — `[ a && b ]` (the SC2107 branch only)
//! - SC2108  checkConditionalAndOrs — `[[ a -a b ]]` (the SC2108 branch only)
//! - SC2076  checkQuotedCondRegex   — quoting the RHS of `=~` in `[[ ]]`
//! - SC2025  checkPS1Assignments    — escape sequences not enclosed in `\[..\]`
//! - SC2199  checkTestArgumentSplitting — array used in `[[ ]]` (the SC2199 branch)
//! - SC2251  checkUselessBang       — `!` that is not on a condition (errexit)
//!
//! Skipped:
//! - SC2222  checkUnmatchableCases — needs the pseudo-glob overlap machinery
//!   (`wordToPseudoGlob`, `pseudoGlobIsSuperSetof`, `pseudoGlobsCanOverlap`) that
//!   is tangled with SC2194/2195/2221; not self-contained, out of scope here.
//! - SC2223  checkSpacefulnessCfg — dataflow/CFG (`isClean`, variable flow); blocked.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::is_array_expansion;
use crate::astlib::is_glob;
use crate::astlib::is_closing_range;
use crate::astlib::is_half_open_range;
use crate::astlib::has_split_range;
use crate::astlib::get_word_parts;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::oversimplify;
use crate::astlib::get_literal_string;
use crate::interface::Shell;
use std::sync::OnceLock;

pub fn register(c: &mut Checker) {
    c.node(check_conditional_and_ors);
    c.node(check_quoted_cond_regex);
    c.node(check_ps1_assignments);
    c.node(check_test_argument_splitting_arrays);
    c.node(check_useless_bang);
}

// ---------------------------------------------------------------------------
// Private helpers (ported from ASTLib/AnalyzerLib; kept local so this module
// does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// SC2107 / SC2108 — checkConditionalAndOrs (only these two branches)
// ---------------------------------------------------------------------------

fn check_conditional_and_ors(_params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_And {
            typ: ConditionType::SingleBracket,
            op,
            ..
        } if op == "&&" => {
            err(
                out,
                t.id(),
                2107,
                "Instead of [ a && b ], use [ a ] && [ b ].",
            );
        }
        InnerToken::TC_And {
            typ: ConditionType::DoubleBracket,
            op,
            ..
        } if op == "-a" => {
            err(out, t.id(), 2108, "In [[..]], use && instead of -a.");
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2076 — checkQuotedCondRegex
// ---------------------------------------------------------------------------

fn has_metachars(s: &str) -> bool {
    s.chars()
        .any(|c| matches!(c, '[' | ']' | '*' | '.' | '+' | '(' | ')' | '|'))
}

/// `isConstantNonRe`: a literal with no regex metacharacters.
fn is_constant_non_re(t: &Token) -> bool {
    match get_literal_string(t) {
        Some(s) => !has_metachars(&s),
        None => false,
    }
}

fn check_quoted_cond_regex(_params: &Parameters, t: &Token, out: &mut Out) {
    let rhs = match &*t.inner {
        InnerToken::TC_Binary { op, rhs, .. } if op == "=~" => rhs,
        _ => return,
    };
    let is_quoted = match &*rhs.inner {
        InnerToken::T_NormalWord(parts) if parts.len() == 1 => matches!(
            &*parts[0].inner,
            InnerToken::T_DoubleQuoted(_) | InnerToken::T_SingleQuoted(_)
        ),
        _ => false,
    };
    if is_quoted && !is_constant_non_re(rhs) {
        warn(
            out,
            rhs.id(),
            2076,
            "Remove quotes from right-hand side of =~ to match as a regex rather than literally.",
        );
    }
}

// ---------------------------------------------------------------------------
// SC2025 — checkPS1Assignments
// ---------------------------------------------------------------------------

fn enclosed_regex() -> &'static regex::Regex {
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"\\\[.*\\\]").unwrap())
}

fn escape_regex() -> &'static regex::Regex {
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"\\x1[Bb]|\\e|\x1b|\\033").unwrap())
}

fn contains_unescaped(s: &str) -> bool {
    let unenclosed = enclosed_regex().replace_all(s, "");
    escape_regex().is_match(&unenclosed)
}

fn check_ps1_assignments(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Assignment { var, value, .. } = &*t.inner {
        if var == "PS1" {
            let contents = oversimplify(value).concat();
            if contains_unescaped(&contents) {
                info(
                    out,
                    value.id(),
                    2025,
                    "Make sure all escape sequences are enclosed in \\[..\\] to prevent line wrapping issues",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2199 — checkTestArgumentSplitting (only the array-in-[[ ]] branch)
// ---------------------------------------------------------------------------
//
// In the Haskell `checkTestArgumentSplitting`, `checkArrays` runs on every
// DoubleBracket operand (Nullary token, Unary operand, and both Binary
// operands), except a Unary operand that is itself a glob (which takes the
// glob branch that skips `checkArrays`). The SingleBracket case emits SC2198,
// which is out of scope here.

fn check_array_operand(token: &Token, out: &mut Out) {
    if get_word_parts(token).iter().any(|p| is_array_expansion(p)) {
        err(
            out,
            token.id(),
            2199,
            "Arrays implicitly concatenate in [[ ]]. Use a loop (or explicit * instead of @).",
        );
    }
}

fn check_test_argument_splitting_arrays(_params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_Nullary {
            typ: ConditionType::DoubleBracket,
            token,
        } => {
            check_array_operand(token, out);
        }
        InnerToken::TC_Unary {
            typ: ConditionType::DoubleBracket,
            token,
            ..
        } => {
            // The glob branch in the oracle does not run checkArrays.
            if !is_glob(token) {
                check_array_operand(token, out);
            }
        }
        InnerToken::TC_Binary {
            typ: ConditionType::DoubleBracket,
            lhs,
            rhs,
            ..
        } => {
            check_array_operand(lhs, out);
            check_array_operand(rhs, out);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2251 — checkUselessBang
// ---------------------------------------------------------------------------

/// Condition-children of a parent node, per `isCondition`'s `getConditionChildren`.
fn condition_children(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_AndIf { lhs, .. } => vec![lhs],
        InnerToken::T_OrIf { lhs, .. } => vec![lhs],
        InnerToken::T_IfExpression { clauses, .. } => {
            clauses.iter().filter_map(|(cond, _)| cond.last()).collect()
        }
        InnerToken::T_WhileExpression { condition, .. } => condition.last().into_iter().collect(),
        InnerToken::T_UntilExpression { condition, .. } => condition.last().into_iter().collect(),
        _ => vec![],
    }
}

/// `isCondition (getPath ..)`.
fn in_condition(params: &Parameters, t: &Token) -> bool {
    let mut child = t;
    loop {
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

fn drop_last<T>(v: &[T]) -> &[T] {
    if v.is_empty() { v } else { &v[..v.len() - 1] }
}

/// Is the immediate parent of `t` a `T_Function`?
fn is_function_body(params: &Parameters, t: &Token) -> bool {
    matches!(
        params.parent(t).map(|p| &*p.inner),
        Some(InnerToken::T_Function { .. })
    )
}

/// `getNonReturningCommands`.
fn non_returning_commands<'a>(params: &Parameters, t: &'a Token) -> Vec<&'a Token> {
    match &*t.inner {
        InnerToken::T_Script { commands, .. } => drop_last(commands).iter().collect(),
        InnerToken::T_BraceGroup(list) => {
            if is_function_body(params, t) {
                drop_last(list).iter().collect()
            } else {
                list.iter().collect()
            }
        }
        InnerToken::T_Subshell(list) => drop_last(list).iter().collect(),
        InnerToken::T_WhileExpression { condition, body } => {
            let mut v: Vec<&Token> = drop_last(condition).iter().collect();
            v.extend(body.iter());
            v
        }
        InnerToken::T_UntilExpression { condition, body } => {
            let mut v: Vec<&Token> = drop_last(condition).iter().collect();
            v.extend(body.iter());
            v
        }
        InnerToken::T_ForIn { body, .. } => body.iter().collect(),
        InnerToken::T_ForArithmetic { body, .. } => body.iter().collect(),
        InnerToken::T_Annotation { token, .. } => non_returning_commands(params, token),
        InnerToken::T_IfExpression { clauses, elses } => {
            let mut v: Vec<&Token> = Vec::new();
            for (cond, then) in clauses {
                v.extend(drop_last(cond).iter());
                v.extend(then.iter());
            }
            v.extend(elses.iter());
            v
        }
        _ => vec![],
    }
}

fn check_bang(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Banged(cmd) => {
            if !in_condition(params, t) {
                info_with_fix(
                    out,
                    t.id(),
                    2251,
                    "This ! is not on a condition and skips errexit. Use `&& exit 1` instead, or make sure $? is checked.",
                    fix_with(vec![
                        replace_start(params, t.id(), 1, ""),
                        replace_end(params, cmd.id(), 0, " && exit 1"),
                    ]),
                );
            }
        }
        InnerToken::T_Annotation { token, .. } => check_bang(params, token, out),
        _ => {}
    }
}

fn check_useless_bang(params: &Parameters, t: &Token, out: &mut Out) {
    if !params.has_set_e {
        return;
    }
    for c in non_returning_commands(params, t) {
        check_bang(params, c, out);
    }
}
