//! Ported check batch a. See rust/PORTING.md.
//!
//! Ported checks (all pure AST patterns; no TC_/TA_/CFG dependencies):
//! - SC2045  checkForInLs          (Analytics.hs) — also emits SC2044 (find branch)
//! - SC2048  checkDollarStar       (Analytics.hs)
//! - SC2068  checkUnquotedDollarAt (Analytics.hs)
//! - SC2124  checkArrayAsString    (Analytics.hs) — also emits SC2125 (glob/brace branch)
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::interface::Shell;

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

/// Faithful port of `ShellCheck.ASTLib.oversimplify`.
///
/// The `astlib::oversimplify` in this crate is deliberately simplified (it only
/// flattens fully-literal words), so we reproduce the real behaviour here —
/// notably the `T_SimpleCommand`/`T_Glob`/expansion cases needed by these
/// checks.
fn oversimplify(token: &Token) -> Vec<String> {
    use InnerToken::*;
    match &*token.inner {
        T_NormalWord(l) => {
            vec![
                l.iter()
                    .flat_map(oversimplify)
                    .collect::<Vec<String>>()
                    .concat(),
            ]
        }
        T_DoubleQuoted(l) => {
            vec![
                l.iter()
                    .flat_map(oversimplify)
                    .collect::<Vec<String>>()
                    .concat(),
            ]
        }
        T_SingleQuoted(s) => vec![s.clone()],
        T_DollarBraced { .. } => vec!["${VAR}".to_string()],
        T_DollarArithmetic(_) => vec!["${VAR}".to_string()],
        T_DollarExpansion(_) => vec!["${VAR}".to_string()],
        T_Backticked(_) => vec!["${VAR}".to_string()],
        T_Glob(s) => vec![s.clone()],
        T_Pipeline { commands, .. } if commands.len() == 1 => oversimplify(&commands[0]),
        T_Literal(x) => vec![x.clone()],
        T_ParamSubSpecialChar(x) => vec![x.clone()],
        T_SimpleCommand { words, .. } => words.iter().flat_map(oversimplify).collect(),
        T_Redirecting { cmd, .. } => oversimplify(cmd),
        T_DollarSingleQuoted(s) => vec![s.clone()],
        T_Annotation { token, .. } => oversimplify(token),
        // Workaround for `let "foo = bar"` parsing.
        TA_Sequence(seq) if seq.len() == 1 => match &*seq[0].inner {
            TA_Expansion(v) => v.iter().flat_map(oversimplify).collect(),
            _ => vec![],
        },
        _ => vec![],
    }
}

fn is_variable_start_char(c: char) -> bool {
    c == '_' || c.is_ascii_lowercase() || c.is_ascii_uppercase()
}
fn is_variable_char(c: char) -> bool {
    is_variable_start_char(c) || c.is_ascii_digit()
}
fn is_special_variable_char(c: char) -> bool {
    matches!(c, '*' | '@' | '#' | '?' | '-' | '$' | '!')
}

/// `getBracedReference`: the variable name from `${var:-foo}` etc.
fn get_braced_reference(s: &str) -> String {
    if let Some(r) = name_expansion(s) {
        return r;
    }
    let no_prefix = drop_hashbang_prefix(s);
    if let Some(r) = take_name(no_prefix) {
        return r;
    }
    if let Some(r) = get_special(no_prefix) {
        return r;
    }
    if let Some(r) = get_special(s) {
        return r;
    }
    s.to_string()
}

fn drop_hashbang_prefix(s: &str) -> &str {
    match s.chars().next() {
        Some(c) if c == '!' || c == '#' => &s[c.len_utf8()..],
        _ => s,
    }
}

fn take_name(s: &str) -> Option<String> {
    let name: String = s.chars().take_while(|c| is_variable_char(*c)).collect();
    if name.is_empty() { None } else { Some(name) }
}

fn get_special(s: &str) -> Option<String> {
    match s.chars().next() {
        Some(c) if is_special_variable_char(c) => Some(c.to_string()),
        _ => None,
    }
}

/// `nameExpansion "!foo*bar"` etc. — returns Some("") when it matches.
fn name_expansion(s: &str) -> Option<String> {
    let mut chars = s.chars();
    if chars.next()? != '!' {
        return None;
    }
    let next = chars.next()?;
    if !is_variable_char(next) {
        return None;
    }
    // `rest` = everything after `next`.
    let first = chars.find(|c| !is_variable_char(*c))?;
    if matches!(first, '*' | '?' | '@') {
        Some(String::new())
    } else {
        None
    }
}

/// `getBracedModifier`: the modifier like `/a/b` in `${var/a/b}`.
fn get_braced_modifier(s: &str) -> String {
    let var = get_braced_reference(s);
    // dropModifier: if s starts with '#' or '!', try [rest, s]; else [s].
    let candidates: Vec<&str> = match s.chars().next() {
        Some(c) if c == '#' || c == '!' => vec![&s[c.len_utf8()..], s],
        _ => vec![s],
    };
    for a in candidates {
        if let Some(rest) = a.strip_prefix(var.as_str()) {
            return rest.to_string();
        }
    }
    String::new()
}

/// `isArrayExpansion`: an expansion of multiple array items.
fn is_array_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let string = oversimplify(op).concat();
            string.starts_with('@') || (!string.starts_with('#') && string.contains("[@]"))
        }
        _ => false,
    }
}

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

/// `willConcatInAssignment`: does this token cause implicit concatenation in an
/// assignment (i.e. an array expansion embedded in a scalar assignment)?
fn will_concat_in_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { .. } => is_array_expansion(t),
        InnerToken::T_DoubleQuoted(parts) => parts.iter().any(will_concat_in_assignment),
        InnerToken::T_NormalWord(parts) => parts.iter().any(will_concat_in_assignment),
        _ => false,
    }
}

/// `willBecomeMultipleArgs`: certain to expand to multiple words.
fn will_become_multiple_args(t: &Token) -> bool {
    will_concat_in_assignment(t) || will_become_multiple_args_f(t)
}
fn will_become_multiple_args_f(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Extglob { .. } => true,
        InnerToken::T_Glob(_) => true,
        InnerToken::T_BraceExpansion(_) => true,
        InnerToken::T_NormalWord(parts) => parts.iter().any(will_become_multiple_args_f),
        _ => false,
    }
}

// ---- isStrictlyQuoteFree (AnalyzerLib.isQuoteFreeNode strict=True) ----------

fn is_assignment_param_to_command(params: &Parameters, id: Id) -> bool {
    let parent = match params
        .parent_map
        .get(&id)
        .and_then(|pid| params.id_map.get(pid))
    {
        Some(p) => p,
        None => return false,
    };
    if let InnerToken::T_SimpleCommand { words, .. } = &*parent.inner {
        if let Some((_first, args)) = words.split_first() {
            return args.iter().any(|a| a.id() == id);
        }
    }
    false
}

fn assignment_is_quoting(params: &Parameters, id: Id) -> bool {
    let shell_parses_params_as_assignments = params.shell != Shell::Sh;
    shell_parses_params_as_assignments || !is_assignment_param_to_command(params, id)
}

fn is_quote_free_element(params: &Parameters, t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Assignment { .. } => assignment_is_quoting(params, t.id()),
        InnerToken::T_FdRedirect { .. } => true,
        _ => false,
    }
}

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
        InnerToken::T_Assignment { .. } => Some(assignment_is_quoting(params, t.id())),
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

fn check_for_in_ls(params: &Parameters, t: &Token, out: &mut Out) {
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

fn check_array_as_string(params: &Parameters, t: &Token, out: &mut Out) {
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
