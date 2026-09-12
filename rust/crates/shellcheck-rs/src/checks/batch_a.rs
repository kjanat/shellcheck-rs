//! Ported check batch a. See rust/PORTING.md.
//!
//! Ported checks (all pure AST patterns; no TC_/TA_/CFG dependencies):
//! - SC2045  checkForInLs          (Analytics.hs) — also emits SC2044 (find branch)
//! - SC2048  checkDollarStar       (Analytics.hs)
//! - SC2068  checkUnquotedDollarAt (Analytics.hs)
//! - SC2124  checkArrayAsString    (Analytics.hs) — also emits SC2125 (glob/brace branch)
use crate::analyzer_lib::assignment_is_quoting;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::is_quote_free_element;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::oversimplify;
use crate::cfg::get_braced_modifier;
use crate::cfg::is_variable_char;
use crate::cfg::will_become_multiple_args;
use crate::cfg::will_concat_in_assignment;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_for_in_ls);
    c.node(check_dollar_star);
    c.node(check_unquoted_dollar_at);
    c.node(check_array_as_string);
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib/AnalyzerLib; kept local so
// this module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

/// `isQuotedAlternativeReference`: matches the regex `(^|\])​:?\+` on the modifier.
fn is_quoted_alternative_reference(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let modifier = get_braced_modifier(&oversimplify(op).concat());
            matches_alternative_regex(&modifier)
        }
        _ => false,
    }
}

/// Search for `(^|\])​:?\+`: at start or after a `]`, an optional `:` then `+`.
fn matches_alternative_regex(m: &str) -> bool {
    // `^:?\+`
    if m.starts_with('+') || m.starts_with(":+") {
        return true;
    }
    // `\]:?\+`
    let bytes = m.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b']' {
            let mut j = i + 1;
            if j < bytes.len() && bytes[j] == b':' {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'+' {
                return true;
            }
        }
    }
    false
}

// ---- isStrictlyQuoteFree (AnalyzerLib.isQuoteFreeNode strict=True) ----------

/// `isQuoteFreeContext` with `strict = True` (so for/select contexts are NOT
/// treated as quoting).
fn is_quote_free_context_strict(params: &Parameters, t: &Token) -> Option<bool> {
    use ConditionType::DoubleBracket;
    match &*t.inner {
        InnerToken::TC_Nullary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TC_Unary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TC_Binary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TA_Sequence(_) => Some(true),
        InnerToken::T_Arithmetic(_) => Some(true),
        InnerToken::T_Assignment { .. } => Some(assignment_is_quoting(params, t)),
        InnerToken::T_Redirecting { .. } => Some(false),
        InnerToken::T_DoubleQuoted(_) => Some(true),
        InnerToken::T_DollarDoubleQuoted(_) => Some(true),
        InnerToken::T_CaseExpression { .. } => Some(true),
        InnerToken::T_HereDoc { .. } => Some(true),
        InnerToken::T_DollarBraced { .. } => Some(true),
        // strict = True.
        InnerToken::T_ForIn { .. } => Some(false),
        InnerToken::T_SelectIn { .. } => Some(false),
        _ => None,
    }
}

fn is_strictly_quote_free(params: &Parameters, t: &Token) -> bool {
    if is_quote_free_element(params, t) {
        return true;
    }
    // msum over the ancestors (NE.tail of getPath): first `Just` wins.
    let mut cur = t;
    while let Some(p) = params.parent(cur) {
        if let Some(v) = is_quote_free_context_strict(params, p) {
            return v;
        }
        cur = p;
    }
    false
}

// ---------------------------------------------------------------------------
// SC2045 — checkForInLs (and SC2044 for the `find` branch)
// ---------------------------------------------------------------------------

fn check_for_in_ls(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_ForIn { items, .. } = &*t.inner {
        if items.len() != 1 {
            return;
        }
        if let InnerToken::T_NormalWord(parts) = &*items[0].inner {
            if parts.len() != 1 {
                return;
            }
            match &*parts[0].inner {
                InnerToken::T_DollarExpansion(cmds) if cmds.len() == 1 => {
                    check_flls(out, parts[0].id(), &cmds[0]);
                }
                InnerToken::T_Backticked(cmds) if cmds.len() == 1 => {
                    check_flls(out, parts[0].id(), &cmds[0]);
                }
                _ => {}
            }
        }
    }
}

fn check_flls(out: &mut Out, id: Id, x: &Token) {
    let words = oversimplify(x);
    let head = match words.first() {
        Some(h) => h.as_str(),
        None => return,
    };
    match head {
        "ls" => {
            let rest = &words[1..];
            if rest.iter().any(|w| w.starts_with('-')) {
                warn(
                    out,
                    id,
                    2045,
                    "Iterating over ls output is fragile. Use globs.",
                );
            } else {
                err(
                    out,
                    id,
                    2045,
                    "Iterating over ls output is fragile. Use globs.",
                );
            }
        }
        "find" => {
            warn(
                out,
                id,
                2044,
                "For loops over find output are fragile. Use find -exec or a while read loop.",
            );
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2048 — checkDollarStar
// ---------------------------------------------------------------------------

fn check_dollar_star(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(parts) = &*t.inner {
        if parts.len() != 1 {
            return;
        }
        if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
            if is_strictly_quote_free(params, t) {
                return;
            }
            let id = parts[0].id();
            let s = oversimplify(op).concat();
            if s.starts_with('*') {
                warn(
                    out,
                    id,
                    2048,
                    "Use \"$@\" (with quotes) to prevent whitespace problems.",
                );
            }
            let head = s.chars().next().unwrap_or('!');
            if get_braced_modifier(&s).starts_with("[*]") && is_variable_char(head) {
                warn(
                    out,
                    id,
                    2048,
                    "Use \"${array[@]}\" (with quotes) to prevent whitespace problems.",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2068 — checkUnquotedDollarAt
// ---------------------------------------------------------------------------

fn check_unquoted_dollar_at(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(parts) = &*t.inner {
        if is_strictly_quote_free(params, t) {
            return;
        }
        if let Some(x) = parts.iter().find(|p| is_array_expansion(p)) {
            if !is_quoted_alternative_reference(x) {
                err(
                    out,
                    x.id(),
                    2068,
                    "Double quote array expansions to avoid re-splitting elements.",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2124 — checkArrayAsString (and SC2125 for the glob/brace branch)
// ---------------------------------------------------------------------------

fn check_array_as_string(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Assignment { value, .. } = &*t.inner {
        if will_concat_in_assignment(value) {
            warn(
                out,
                value.id(),
                2124,
                "Assigning an array to a string! Assign as array, or use * instead of @ to concatenate.",
            );
        } else if will_become_multiple_args(value) {
            warn(
                out,
                value.id(),
                2125,
                "Brace expansions and globs are literal in assignments. Quote it or use an array.",
            );
        }
    }
}
