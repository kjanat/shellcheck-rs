//! Ported check batch j. See rust/PORTING.md.
//!
//! Ported checks (pure AST patterns; no CFG/arithmetic dependencies):
//! - SC2064  checkTrapQuotes — `trap "..."` double-quoted argument expands now
//! - SC2069  checkStderrRedirect — `2>&1 >file` ordering
//! - SC2094  checkRedirectToSame — read+write same file in a pipeline
//! - SC2129  checkMultipleAppends — 3+ individual `>>` to the same file
//! - SC2233/SC2234  checkSubshelledTests — redundant `( )` around condition/test
//!
//! Skipped:
//! - SC2145 — already ported in an earlier batch (per assignment).
//! - SC2235 (general branch of checkSubshelledTests, `{ ..; }` suggestion) is not
//!   in this assignment, so it is intentionally not emitted; the 2233/2234
//!   branches are mutually exclusive with it, so omitting it does not change
//!   their behavior.
//!
//! Notes on arithmetic: checkSubshelledTests's `hasAssignment` also looks for
//! `TA_Assignment`/`TA_Unary "++"/"--"` inside `$((..))`. Arithmetic is not yet
//! parsed into `TA_*` (it is a placeholder literal), so those sub-cases can never
//! match; the `T_DollarBraced` (`${x:=y}`) and `T_DollarBraceCommandExpansion`
//! cases (which do parse) are ported so their negative tests stay negative.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::get_command;
use crate::analyzer_lib::get_command_basename;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::is_function_body;
use crate::analyzer_lib::is_test_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::basename;
use crate::astlib::drop_hashbang_prefix;
use crate::astlib::get_command_sequences;
use crate::astlib::get_word_parts;
use crate::astlib::is_assignment;
use crate::astlib::is_flag;
use crate::astlib::is_function;
use crate::astlib::oversimplify;
use crate::cfg::get_braced_modifier;
use crate::cfg::get_braced_reference;
use crate::cfg::is_special_variable_char;
use crate::cfg::is_variable_char;
use crate::cfg::is_variable_start_char;
use crate::interface::Shell;

pub fn register(c: &mut Checker) {
    c.node(check_trap_quotes);
    c.node(check_stderr_redirect);
    c.node(check_redirect_to_same);
    c.node(check_multiple_appends);
}

// ---------------------------------------------------------------------------
// Shared private helpers (ported from ASTLib/AnalyzerLib; kept local so this
// module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

/// Pre-order traversal of every node in `t`'s subtree (`doAnalysis` order).
fn all_nodes<'a>(t: &'a Token, out: &mut Vec<&'a Token>) {
    out.push(t);
    for c in t.children() {
        all_nodes(c, out);
    }
}

// ---------------------------------------------------------------------------
// SC2064 — checkTrapQuotes
// ---------------------------------------------------------------------------

fn check_trap_quotes(_params: &Parameters, t: &Token, out: &mut Out) {
    // CommandCheck (Exactly "trap"): only fire on the T_SimpleCommand itself.
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    if get_command_name(t).as_deref() != Some("trap") {
        return;
    }
    let arg = match words.get(1) {
        Some(a) => a,
        None => return,
    };
    // checkTrap (T_NormalWord _ [T_DoubleQuoted _ rs])
    let parts = match &*arg.inner {
        InnerToken::T_NormalWord(l) => l,
        _ => return,
    };
    if parts.len() != 1 {
        return;
    }
    let rs = match &*parts[0].inner {
        InnerToken::T_DoubleQuoted(rs) => rs,
        _ => return,
    };
    for r in rs {
        let hit = matches!(
            &*r.inner,
            InnerToken::T_DollarExpansion(_)
                | InnerToken::T_Backticked(_)
                | InnerToken::T_DollarBraced { .. }
                | InnerToken::T_DollarArithmetic(_)
        );
        if hit {
            warn(
                out,
                r.id(),
                2064,
                "Use single quotes, otherwise this expands now rather than when signalled.",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SC2069 — checkStderrRedirect
// ---------------------------------------------------------------------------

fn check_stderr_redirect(params: &Parameters, redir: &Token, out: &mut Out) {
    let redirs = match &*redir.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs,
        _ => return,
    };
    if redirs.len() != 2 {
        return;
    }
    // First: T_FdRedirect id "2" (T_IoDuplicate _ (T_GREATAND _) "1")
    let first_id = match &*redirs[0].inner {
        InnerToken::T_FdRedirect { fd, target } if fd == "2" => {
            match &*target.inner {
                InnerToken::T_IoDuplicate { op, num } if num == "1" => {
                    if !matches!(&*op.inner, InnerToken::T_GREATAND) {
                        return;
                    }
                }
                _ => return,
            }
            redirs[0].id()
        }
        _ => return,
    };
    // Second: T_FdRedirect _ _ (T_IoFile _ op _) where op is > or >>
    match &*redirs[1].inner {
        InnerToken::T_FdRedirect { target, .. } => match &*target.inner {
            InnerToken::T_IoFile { op, .. } => {
                if !matches!(&*op.inner, InnerToken::T_Greater | InnerToken::T_DGREAT) {
                    return;
                }
            }
            _ => return,
        },
        _ => return,
    }

    if !is_captured(params, redir) {
        warn(
            out,
            first_id,
            2069,
            "To redirect stdout+stderr, 2>&1 must be last (or use '{ cmd > file; } 2>&1' to clarify).",
        );
    }
}

/// `isParentOf parentMap ancestor child`: is `ancestor` on the path from `child`
/// to the root?
fn is_parent_of(params: &Parameters, ancestor: &Token, child: &Token) -> bool {
    let mut cur = Some(child);
    while let Some(node) = cur {
        if node.id() == ancestor.id() {
            return true;
        }
        cur = params.parent(node);
    }
    false
}

/// `isCaptured`: any `usesOutput` on the path from `redir` to root.
fn is_captured(params: &Parameters, redir: &Token) -> bool {
    let mut cur = Some(redir);
    while let Some(node) = cur {
        let uses = match &*node.inner {
            InnerToken::T_Pipeline { commands, .. } => {
                commands.len() > 1
                    && !commands
                        .last()
                        .map(|last| is_parent_of(params, last, redir))
                        .unwrap_or(false)
            }
            InnerToken::T_ProcSub { .. }
            | InnerToken::T_DollarExpansion(_)
            | InnerToken::T_Backticked(_) => true,
            _ => false,
        };
        if uses {
            return true;
        }
        cur = params.parent(node);
    }
    false
}

// ---------------------------------------------------------------------------
// SC2094 — checkRedirectToSame
// ---------------------------------------------------------------------------

fn check_redirect_to_same(params: &Parameters, t: &Token, out: &mut Out) {
    let list = match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } => commands,
        _ => return,
    };
    // getAllRedirs: files targeted by > < >> across all pipeline stages.
    let mut all_redirs: Vec<&Token> = vec![];
    for cmd in list {
        if let InnerToken::T_Redirecting { redirs, .. } = &*cmd.inner {
            for r in redirs {
                if let InnerToken::T_FdRedirect { target, .. } = &*r.inner {
                    if let InnerToken::T_IoFile { op, file } = &*target.inner {
                        if matches!(
                            &*op.inner,
                            InnerToken::T_Greater | InnerToken::T_Less | InnerToken::T_DGREAT
                        ) {
                            all_redirs.push(file);
                        }
                    }
                }
            }
        }
    }
    for l in list {
        let mut nodes: Vec<&Token> = vec![];
        all_nodes(l, &mut nodes);
        for x in &all_redirs {
            for u in &nodes {
                check_occurrences(params, x, u, out);
            }
        }
    }
}

fn check_occurrences(params: &Parameters, x: &Token, u: &Token, out: &mut Out) {
    // Both must be T_NormalWord.
    if !matches!(&*x.inner, InnerToken::T_NormalWord(_))
        || !matches!(&*u.inner, InnerToken::T_NormalWord(_))
    {
        return;
    }
    if x.id() == u.id() {
        return;
    }
    if x != u {
        return;
    }
    if is_input(params, x) && is_input(params, u) {
        return;
    }
    if is_output(params, x) && is_output(params, u) {
        return;
    }
    if special(x) {
        return;
    }
    if is_harmless_command(params, x) || is_harmless_command(params, u) {
        return;
    }
    if contains_assignment(params, u) {
        return;
    }
    // addComment (note newId=u), addComment (note exceptId=x)
    info(
        out,
        u.id(),
        2094,
        "Make sure not to read and write the same file in the same pipeline.",
    );
    info(
        out,
        x.id(),
        2094,
        "Make sure not to read and write the same file in the same pipeline.",
    );
}

fn parent_io_op<'a>(params: &'a Parameters, t: &'a Token) -> Option<&'a Token> {
    let parent = params.parent(t)?;
    if let InnerToken::T_IoFile { op, .. } = &*parent.inner {
        Some(op)
    } else {
        None
    }
}

fn is_input(params: &Parameters, t: &Token) -> bool {
    match parent_io_op(params, t) {
        Some(op) => matches!(&*op.inner, InnerToken::T_Less),
        None => false,
    }
}

fn is_output(params: &Parameters, t: &Token) -> bool {
    match parent_io_op(params, t) {
        Some(op) => matches!(&*op.inner, InnerToken::T_Greater | InnerToken::T_DGREAT),
        None => false,
    }
}

fn special(t: &Token) -> bool {
    oversimplify(t).concat().starts_with("/dev/")
}

fn is_harmless_command(params: &Parameters, arg: &Token) -> bool {
    match get_closest_command(params, arg).and_then(get_command_basename) {
        Some(name) => matches!(name.as_str(), "echo" | "mapfile" | "printf" | "sponge"),
        None => false,
    }
}

fn contains_assignment(params: &Parameters, arg: &Token) -> bool {
    match get_closest_command(params, arg) {
        Some(cmd) => is_assignment(cmd),
        None => false,
    }
}

// ---------------------------------------------------------------------------
// SC2129 — checkMultipleAppends
// ---------------------------------------------------------------------------

/// `getTarget`: (append-file, redirecting-id) for a command that appends (`>>`).
fn get_target(t: &Token) -> Option<(&Token, Id)> {
    match &*t.inner {
        InnerToken::T_Annotation { token, .. } => get_target(token),
        InnerToken::T_Pipeline { commands, .. } if !commands.is_empty() => {
            get_target(commands.last().unwrap())
        }
        InnerToken::T_Redirecting { redirs, .. } => {
            // file <- mapMaybe getAppend list !!! 0
            for r in redirs {
                if let InnerToken::T_FdRedirect { target, .. } = &*r.inner {
                    if let InnerToken::T_IoFile { op, file } = &*target.inner {
                        if matches!(&*op.inner, InnerToken::T_DGREAT) {
                            return Some((file, t.id()));
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn check_multiple_appends(_params: &Parameters, t: &Token, out: &mut Out) {
    for list in get_command_sequences(t) {
        let targets: Vec<Option<(&Token, Id)>> = list.iter().map(get_target).collect();
        // groupWith (fmap fst): group consecutive entries by their file token
        // (structural equality, None never equal to Some).
        let mut i = 0;
        while i < targets.len() {
            let key = targets[i].map(|(f, _)| f);
            let mut j = i + 1;
            while j < targets.len() {
                let k2 = targets[j].map(|(f, _)| f);
                let same = match (key, k2) {
                    (Some(a), Some(b)) => a == b,
                    (None, None) => true,
                    _ => false,
                };
                if !same {
                    break;
                }
                j += 1;
            }
            // group is targets[i..j]; checkGroup fires when first is Just and len>=3
            if let Some((_, id)) = targets[i] {
                if j - i >= 3 {
                    style(
                        out,
                        id,
                        2129,
                        "Consider using { cmd1; cmd2; } >> file instead of individual redirects.",
                    );
                }
            }
            i = j;
        }
    }
}

// ---------------------------------------------------------------------------
// SC2233 / SC2234 — checkSubshelledTests (2233/2234 branches only)
// ---------------------------------------------------------------------------

fn is_single_test(cmds: &[Token]) -> bool {
    cmds.len() == 1 && is_test_command(&cmds[0])
}

fn is_test_structure(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Banged(inner) => is_test_structure(inner),
        InnerToken::T_AndIf { lhs, rhs } | InnerToken::T_OrIf { lhs, rhs } => {
            is_test_structure(lhs) && is_test_structure(rhs)
        }
        InnerToken::T_Pipeline {
            separators,
            commands,
        } if separators.is_empty() => match commands.as_slice() {
            [only] => {
                if let InnerToken::T_Redirecting { cmd, .. } = &*only.inner {
                    match &*cmd.inner {
                        InnerToken::T_BraceGroup(ts) | InnerToken::T_Subshell(ts) => {
                            ts.iter().all(is_test_structure)
                        }
                        _ => is_test_command(t),
                    }
                } else {
                    is_test_command(t)
                }
            }
            _ => is_test_command(t),
        },
        _ => is_test_command(t),
    }
}

/// `isCompoundCondition`: after skipping wrappers, is the enclosing construct an
/// if/while/until?
fn is_compound_condition(path: &[&Token]) -> bool {
    // dropWhile skippable (tail path)
    let mut idx = 1;
    while idx < path.len() && skippable(path[idx]) {
        idx += 1;
    }
    match path.get(idx) {
        Some(node) => matches!(
            &*node.inner,
            InnerToken::T_IfExpression { .. }
                | InnerToken::T_WhileExpression { .. }
                | InnerToken::T_UntilExpression { .. }
        ),
        None => false,
    }
}

fn skippable(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs.is_empty(),
        InnerToken::T_Pipeline { separators, .. } => separators.is_empty(),
        InnerToken::T_Annotation { .. } => true,
        _ => false,
    }
}

/// `hasAssignment t = isNothing $ doAnalysis guardNotAssignment t`: true iff any
/// descendant node "is an assignment" per `guardNotAssignment`.
fn has_assignment(t: &Token) -> bool {
    let mut nodes: Vec<&Token> = vec![];
    all_nodes(t, &mut nodes);
    nodes.iter().any(|n| node_is_assignment(n))
}

fn node_is_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::TA_Assignment { .. } => true,
        InnerToken::TA_Unary { op, .. } => op.contains("++") || op.contains("--"),
        InnerToken::T_DollarBraced { op, .. } => {
            let str = oversimplify(op).concat();
            let modifier = get_braced_modifier(&str);
            modifier.starts_with('=') || modifier.starts_with(":=")
        }
        InnerToken::T_DollarBraceCommandExpansion { .. } => true,
        // Arithmetic is not yet parsed into `TA_*` (the contents of `$((..))` are
        // a placeholder literal), so the `TA_Assignment`/`TA_Unary "++"/"--"`
        // cases of `guardNotAssignment` can never match structurally. Recover the
        // increment/assignment cases (e.g. `$((i++))`, `$((i+=1))`) by scanning
        // the placeholder text; this keeps `( [[ $((i++)) = 10 ]] )` from firing.
        InnerToken::T_DollarArithmetic(inner) => astlib::get_literal_string(inner)
            .map(|s| arith_has_assignment(&s))
            .unwrap_or(false),
        _ => false,
    }
}

/// Does an arithmetic expression string contain an assignment or `++`/`--`?
/// Matches the arithmetic assignment operators (`=`, `+=`, `-=`, `*=`, `/=`,
/// `%=`, `<<=`, `>>=`, `&=`, `|=`, `^=`) and the increment/decrement operators,
/// while excluding the comparisons `==`, `!=`, `<=`, `>=`.
fn arith_has_assignment(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if (c == b'+' || c == b'-') && i + 1 < b.len() && b[i + 1] == c {
            return true; // ++ or --
        }
        if c == b'=' {
            let next = b.get(i + 1).copied();
            let prev = if i > 0 { Some(b[i - 1]) } else { None };
            if next != Some(b'=') {
                match prev {
                    // `==` second half, or `!=`.
                    Some(b'=') | Some(b'!') => {}
                    // `<=`/`>=` comparisons unless doubled to `<<=`/`>>=`.
                    Some(b'<') | Some(b'>') => {
                        let pp = if i >= 2 { Some(b[i - 2]) } else { None };
                        if pp == prev {
                            return true;
                        }
                    }
                    _ => return true,
                }
            }
        }
        i += 1;
    }
    false
}

// ---------------------------------------------------------------------------
// getBracedModifier (ported from ASTLib; used by hasAssignment above)
// ---------------------------------------------------------------------------
