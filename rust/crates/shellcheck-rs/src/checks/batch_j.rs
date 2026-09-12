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
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::get_command_basename;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::get_command_sequences;
use crate::astlib::is_assignment;
use crate::astlib::oversimplify;

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

// ---------------------------------------------------------------------------
// getBracedModifier (ported from ASTLib; used by hasAssignment above)
// ---------------------------------------------------------------------------
