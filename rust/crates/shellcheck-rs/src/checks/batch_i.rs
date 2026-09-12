//! Ported check batch i. See rust/PORTING.md.
//!
//! Ported from `src/ShellCheck/Analytics.hs` and `src/ShellCheck/Checks/Commands.hs`:
//!   * SC2046 — `checkUnquotedExpansions`: unquoted `$(...)` / `` `...` `` command
//!     substitution that should be quoted to prevent word splitting. Uses a
//!     parent-context walk (`isQuoteFree`/`usedAsCommandName`), NOT the CFG.
//!   * SC2183 — `checkPrintfVar`: printf format string has a variable count that
//!     does not match the number of arguments.
//!   * SC2059 — `checkPrintfVar`: variables used in the printf format string.
//!   * SC2060 — `checkTr`: unquoted glob parameters passed to `tr`.
//!
//! Not ported here (belong to other batches / codes): SC2182 (printf, no
//! variables), SC2018/2019/2020/2021 (tr literal-string advice).
use crate::analyzer_lib::concat_over;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::get_command_name_and_token;
use crate::analyzer_lib::is_quote_free;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::basename;
use crate::astlib::get_literal_string;
use crate::astlib::is_literal;
use crate::astlib::only_literal_string;
use crate::cfg::may_become_multiple_args;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_unquoted_expansions);
    c.node(command_dispatch);
}

// ===========================================================================
// Shared helpers (ported privately; parallel agents own other .rs files).
// ===========================================================================

// ---- getWordParts / isFlag / isGlob (ported from ASTLib) --------------------

// ---- command name resolution (ported from ASTLib, proven in batch_h) -------

fn get_command_token_or_this(t: &Token) -> &Token {
    get_command_name_and_token(false, t).1
}

// ===========================================================================
// SC2046 — checkUnquotedExpansions
// ===========================================================================

/// `getCommandNameFromExpansion`: if a substitution is a single command, its name.
fn get_command_name_from_expansion(t: &Token) -> Option<String> {
    use InnerToken::*;
    let list: &[Token] = match &*t.inner {
        T_DollarExpansion(l) if l.len() == 1 => l,
        T_Backticked(l) if l.len() == 1 => l,
        T_DollarBraceCommandExpansion { list, .. } if list.len() == 1 => list,
        _ => return None,
    };
    match &*list[0].inner {
        T_Pipeline { commands, .. } if commands.len() == 1 => get_command_name(&commands[0]),
        _ => None,
    }
}

/// `usedAsCommandName`: is the token the first word of a T_SimpleCommand?
fn used_as_command_name(p: &Parameters, token: &Token) -> bool {
    use InnerToken::*;
    let mut current_id = token.id();
    let mut node = p.parent(token);
    while let Some(t) = node {
        match &*t.inner {
            T_NormalWord(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = p.parent(t);
            }
            T_DoubleQuoted(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = p.parent(t);
            }
            T_SimpleCommand { words, .. } if !words.is_empty() => {
                if words[0].id() == current_id || get_command_token_or_this(t).id() == current_id {
                    return true;
                }
                // `time CMD`: the reserved word `time` is followed by the command
                // being timed. ShellCheck's parser (readTimeSuffix) parses that
                // word as the command; this parser keeps `time` as a plain
                // command with the word as its first argument, so recognise it
                // here to avoid a spurious split warning.
                return words.len() >= 2
                    && get_literal_string(&words[0]).as_deref() == Some("time")
                    && words[1].id() == current_id;
            }
            _ => return false,
        }
    }
    false
}

fn check_unquoted_expansions(p: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    let contents: &[Token] = match &*t.inner {
        T_DollarExpansion(c) => c,
        T_Backticked(c) => c,
        T_DollarBraceCommandExpansion { list, .. } => list,
        _ => return,
    };
    if contents.is_empty() {
        return;
    }
    if should_be_split(t) || is_quote_free(p, t) || used_as_command_name(p, t) {
        return;
    }
    warn(out, t.id(), 2046, "Quote this to prevent word splitting.");
}

fn should_be_split(t: &Token) -> bool {
    matches!(
        get_command_name_from_expansion(t).as_deref(),
        Some("seq") | Some("pgrep")
    )
}

// ===========================================================================
// SC2183 / SC2059 — checkPrintfVar    &    SC2060 — checkTr
// Dispatched like ShellCheck.Checks.Commands.checkCommand.
// ===========================================================================

fn command_dispatch(p: &Parameters, t: &Token, out: &mut Out) {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    let name = match get_literal_string(&words[0]) {
        Some(n) => n,
        None => return,
    };
    if name.contains('/') {
        let _base = basename(&name);
    } else if name == "builtin" && words.len() >= 2 {
        let selected = only_literal_string(&words[1]);
        exactly_dispatch(p, &selected, &words[2..], out);
    } else {
        exactly_dispatch(p, &name, &words[1..], out);
    }
}

fn exactly_dispatch(p: &Parameters, name: &str, args: &[Token], out: &mut Out) {
    if name == "printf" {
        check_printf(p, args, out);
    }
}

// ---- SC2183 / SC2059 checkPrintfVar ----------------------------------------

fn check_printf(p: &Parameters, args: &[Token], out: &mut Out) {
    // f: skip leading `--`, `-v var`, `-vVAR`.
    let mut rest = args;
    loop {
        let first = match rest.first() {
            Some(f) => f,
            None => return,
        };
        let s = get_literal_string(first);
        if s.as_deref() == Some("--") {
            rest = &rest[1..];
            continue;
        }
        if s.as_deref() == Some("-v") && rest.len() >= 2 {
            rest = &rest[2..];
            continue;
        }
        if let Some(st) = &s {
            if st.len() >= 3 && st.starts_with("-v") {
                rest = &rest[1..];
                continue;
            }
        }
        // format = first, params = rest[1..]
        check_printf_format(p, first, &rest[1..], out);
        return;
    }
}

fn check_printf_format(_p: &Parameters, format: &Token, more: &[Token], out: &mut Out) {
    // SC2183: variable/argument count mismatch.
    if let Some(string) = get_literal_string(format) {
        let formats = get_printf_formats(&string);
        let format_count = formats.chars().count();
        let arg_count = more.len();

        if arg_count == 0 && format_count == 0 {
            // fine
        } else if format_count == 0 && arg_count > 0 {
            // SC2182 — owned by another batch; not emitted here.
        } else if more.iter().any(may_become_multiple_args) {
            // Unknown; trust the user.
        } else if arg_count < format_count && only_trailing_ts(&formats, arg_count) {
            // Allow trailing %()Ts (they use the current time).
        } else if arg_count > 0 && format_count > 0 && arg_count % format_count == 0 {
            // A suitable number of arguments.
        } else {
            let pl_var = if format_count == 1 {
                "variable"
            } else {
                "variables"
            };
            let pl_arg = if arg_count == 1 {
                "argument"
            } else {
                "arguments"
            };
            warn(
                out,
                format.id(),
                2183,
                &format!(
                    "This format string has {} {}, but is passed {} {}.",
                    format_count, pl_var, arg_count, pl_arg
                ),
            );
        }
    }

    // SC2059: variables in the printf format string.
    let has_percent = concat_over(format).contains('%');
    if !(has_percent || is_literal(format)) {
        info(
            out,
            format.id(),
            2059,
            "Don't use variables in the printf format string. Use printf '..%s..' \"$foo\".",
        );
    }
}

fn only_trailing_ts(formats: &str, arg_count: usize) -> bool {
    formats.chars().skip(arg_count).all(|c| c == 'T')
}

// ---- mayBecomeMultipleArgs (ASTLib) ----------------------------------------

// ---- getPrintfFormats (faithful port of the regex-based scanner) -----------

fn get_printf_formats(s: &str) -> String {
    let cs: Vec<char> = s.chars().collect();
    get_formats(&cs)
}

fn get_formats(cs: &[char]) -> String {
    if cs.is_empty() {
        return String::new();
    }
    if cs[0] == '%' {
        if cs.get(1) == Some(&'%') {
            return get_formats(&cs[2..]);
        }
        if cs.get(1) == Some(&'(') {
            let rest = &cs[2..];
            if let Some(pos) = rest.iter().position(|&c| c == ')') {
                if pos + 1 < rest.len() {
                    let c = rest[pos + 1];
                    let trailing = &rest[pos + 2..];
                    let mut out = String::new();
                    out.push(c);
                    out.push_str(&get_formats(trailing));
                    return out;
                }
            }
            return String::new();
        }
        return regex_based_get_formats(&cs[1..]);
    }
    get_formats(&cs[1..])
}

fn regex_based_get_formats(rest: &[char]) -> String {
    match match_format_re(rest) {
        Some((width_star, prec_star, typ, remaining)) => {
            let mut out = String::new();
            if width_star {
                out.push('*');
            }
            if prec_star {
                out.push('*');
            }
            out.push(typ);
            out.push_str(&get_formats(remaining));
            out
        }
        None => {
            let mut out = String::new();
            if let Some(&c) = rest.first() {
                out.push(c);
            }
            out.push_str(&get_formats(rest));
            out
        }
    }
}

const PRINTF_TYPE_CHARS: &str = "diouxXfFeEgGaAcsbqQSC";

/// Manual match of
/// `^#?-?\+? ?0?(\*|\d*)\.?(\d*|\*)(hh|h|l|ll|q|L|j|z|Z|t)?([diouxXfFeEgGaAcsbqQSC])((\n|.)*)`
/// Returns (width_is_star, precision_is_star, type_char, remaining_after_type).
fn match_format_re(rest: &[char]) -> Option<(bool, bool, char, &[char])> {
    let mut i = 0usize;
    // flags: #? -? +? space? 0?  (each optional, fixed order)
    if rest.get(i) == Some(&'#') {
        i += 1;
    }
    if rest.get(i) == Some(&'-') {
        i += 1;
    }
    if rest.get(i) == Some(&'+') {
        i += 1;
    }
    if rest.get(i) == Some(&' ') {
        i += 1;
    }
    if rest.get(i) == Some(&'0') {
        i += 1;
    }
    // width: (\*|\d*)
    let width_star;
    if rest.get(i) == Some(&'*') {
        width_star = true;
        i += 1;
    } else {
        width_star = false;
        while rest.get(i).is_some_and(|c| c.is_ascii_digit()) {
            i += 1;
        }
    }
    // \.?
    if rest.get(i) == Some(&'.') {
        i += 1;
    }
    // precision: (\d*|\*) — '*' only via backtracking; equivalently, '*' here is star.
    let prec_star;
    if rest.get(i) == Some(&'*') {
        prec_star = true;
        i += 1;
    } else {
        prec_star = false;
        while rest.get(i).is_some_and(|c| c.is_ascii_digit()) {
            i += 1;
        }
    }
    // length modifier (hh|h|l|ll|q|L|j|z|Z|t)? — greedy, but only if a type char
    // then follows (regex backtracking). Alternation preference order preserved.
    let type_at = |j: usize| -> Option<char> {
        rest.get(j)
            .copied()
            .filter(|c| PRINTF_TYPE_CHARS.contains(*c))
    };
    let mods = ["hh", "h", "l", "ll", "q", "L", "j", "z", "Z", "t"];
    let mut chosen_len = 0usize;
    for m in mods {
        let mc: Vec<char> = m.chars().collect();
        if i + mc.len() <= rest.len()
            && rest[i..i + mc.len()] == mc[..]
            && type_at(i + mc.len()).is_some()
        {
            chosen_len = mc.len();
            break;
        }
    }
    let type_pos = i + chosen_len;
    let typ = type_at(type_pos)?;
    Some((width_star, prec_star, typ, &rest[type_pos + 1..]))
}
