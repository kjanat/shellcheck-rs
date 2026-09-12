//! Ported check batch r. See rust/PORTING.md.
//!
//! Faithful ports of the shell-portability (`ForShell`) checks from
//! `src/ShellCheck/Checks/ShellSupport.hs`:
//!
//!   * `checkBashisms`              — the full SC30xx family (implemented WHOLE
//!                                    here for parity + tests; see the module
//!                                    tail for why only a *gap-filling* subset
//!                                    is registered).
//!   * `checkForDecimals`          — SC2079
//!   * `checkBraceExpansionVars`   — SC2051 / SC2175
//!   * `checkMultiDimensionalArrays` — SC2180
//!   * `checkBangAfterPipe`        — SC2326
//!   * `checkNegatedUnaryOps`      — SC2332
//!
//! Every `ForShell` check is dispatched by the target shell dialect
//! (`Parameters.shell`), replicated exactly by the gate in each registration
//! wrapper. The check bodies themselves are ungated (mirroring Haskell's
//! `ForShell [..] f`, whose `f` runs regardless of shell under `testChecker`),
//! so the `prop_` tests exercise them the same way the QuickCheck props do.
#![allow(unused_imports, unused_variables, dead_code)]

use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::arguments;
use crate::astlib::is_only_redirection;
use crate::astlib::is_flag;
use crate::astlib::is_glob;
use crate::astlib::has_split_range;
use crate::astlib::get_word_parts;
use crate::analyzer_lib::{Checker, Out, Parameters, err, info, style, warn};
use crate::ast::*;
use crate::astlib::{self, get_literal_string, only_literal_string};
use crate::cfg::{
    get_braced_modifier, get_braced_reference, is_variable_char, is_variable_name, oversimplify,
    oversimplify_concat,
};
use crate::interface::Shell;

// ===========================================================================
// Registration.
//
// checkBashisms is intentionally NOT registered here: `checks::batch_h`
// already registers a (partial) `checkBashisms` covering most SC30xx codes.
// Registering the whole function again would double-emit every code batch_h
// already produces (extra > 0 on all of them), violating the conformance
// guardrail. Instead we register `check_bashisms_gaps`, which handles ONLY the
// branches batch_h omits and whose positions match the oracle (see tail note).
// ===========================================================================
pub fn register(c: &mut Checker) {
    c.node(check_for_decimals_gated);
    c.node(check_brace_expansion_vars_gated);
    c.node(check_multi_dimensional_arrays_gated);
    c.node(check_bashisms_gaps);
    // Now registered (the parser gaps that held these back are fixed):
    //   * checkBangAfterPipe (SC2326): the parser now wraps a mid-pipeline `!`
    //     in `T_Banged`, so the check matches. ForShell [Dash,BusyboxSh,Sh,Bash].
    //   * checkNegatedUnaryOps (SC2332): the `!` `TC_Unary` node now spans the
    //     `!` alone, matching the oracle. ForShell [Bash].
    //   * The TC_Unary bashism codes (SC3016/3062/3065/…): the `TC_Unary` node
    //     now spans the operator alone, so they are handled in
    //     `check_bashisms_gaps`.
    c.node(check_bang_after_pipe_gated);
    c.node(check_negated_unary_ops_gated);
}

// ===========================================================================
// Shared helpers.
// ===========================================================================

fn is_busybox(p: &Parameters) -> bool {
    p.shell == Shell::BusyboxSh
}
fn is_dash(p: &Parameters) -> bool {
    p.shell == Shell::Dash || is_busybox(p)
}

/// `warnMsg`: dash/busybox -> err "In dash, X not supported.", sh -> warn
/// "In POSIX sh, X undefined."
fn warn_msg(out: &mut Out, p: &Parameters, id: Id, code: i64, s: &str) {
    if is_dash(p) {
        err(out, id, code, &format!("In dash, {} not supported.", s));
    } else {
        warn(out, id, code, &format!("In POSIX sh, {} undefined.", s));
    }
}

/// Faithful `getLiteralStringExt (const Nothing)` — unlike the crate's
/// `astlib::get_literal_string`, this one also flattens `TA_Expansion`
/// (needed by `checkForDecimals`).
fn lit_string(t: &Token) -> Option<String> {
    fn go(t: &Token, out: &mut String) -> bool {
        use InnerToken::*;
        match &*t.inner {
            T_Literal(s)
            | T_SingleQuoted(s)
            | T_DollarSingleQuoted(s)
            | T_ParamSubSpecialChar(s) => {
                out.push_str(s);
                true
            }
            T_NormalWord(l) | T_DoubleQuoted(l) | T_DollarDoubleQuoted(l) | TA_Expansion(l) => {
                for p in l {
                    if !go(p, out) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
    let mut s = String::new();
    if go(t, &mut s) { Some(s) } else { None }
}

// ===========================================================================
// checkForDecimals — SC2079
// ForShell [Sh, Dash, BusyboxSh, Bash]
// ===========================================================================

fn check_for_decimals_gated(p: &Parameters, t: &Token, out: &mut Out) {
    if matches!(
        p.shell,
        Shell::Sh | Shell::Dash | Shell::BusyboxSh | Shell::Bash
    ) {
        check_for_decimals(p, t, out);
    }
}

fn check_for_decimals(_p: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TA_Expansion(_) = &*t.inner {
        if let Some(s) = lit_string(t) {
            let mut chars = s.chars();
            if let Some(first) = chars.next() {
                let rest: String = chars.collect();
                if first.is_ascii_digit() && rest.contains('.') {
                    err(
                        out,
                        t.id(),
                        2079,
                        "(( )) doesn't support decimals. Use bc or awk.",
                    );
                }
            }
        }
    }
}

// ===========================================================================
// checkBraceExpansionVars — SC2051 / SC2175
// ForShell [Bash]
// ===========================================================================

fn check_brace_expansion_vars_gated(p: &Parameters, t: &Token, out: &mut Out) {
    if p.shell == Shell::Bash {
        check_brace_expansion_vars(p, t, out);
    }
}

fn check_brace_expansion_vars(p: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_BraceExpansion(list) = &*t.inner {
        let id = t.id();
        for element in list {
            let s = brace_element_to_string(element);
            if s.contains("$..") || s.contains("..$") {
                if is_evaled(p, element) {
                    style(
                        out,
                        id,
                        2175,
                        "Quote this invalid brace expansion since it should be passed literally to eval.",
                    );
                } else {
                    warn(
                        out,
                        id,
                        2051,
                        "Bash doesn't support variables in brace range expansions.",
                    );
                }
            }
        }
    }
}

/// `toString`: `getLiteralStringExt literalExt` where `literalExt` yields "$"
/// for `$`-expansions and "-" for anything else non-literal.
fn brace_element_to_string(t: &Token) -> String {
    fn go(t: &Token, out: &mut String) {
        use InnerToken::*;
        match &*t.inner {
            T_Literal(s)
            | T_SingleQuoted(s)
            | T_DollarSingleQuoted(s)
            | T_ParamSubSpecialChar(s) => out.push_str(s),
            T_NormalWord(l) | T_DoubleQuoted(l) | T_DollarDoubleQuoted(l) | TA_Expansion(l) => {
                for p in l {
                    go(p, out);
                }
            }
            T_DollarBraced { .. } | T_DollarExpansion(_) | T_DollarArithmetic(_) => out.push('$'),
            _ => out.push('-'),
        }
    }
    let mut s = String::new();
    go(t, &mut s);
    s
}

/// `isEvaled`: the closest enclosing command is an unqualified `eval`.
fn is_evaled(p: &Parameters, t: &Token) -> bool {
    match get_closest_command(p, t) {
        Some(cmd) => crate::analyzer_lib::get_command_name(cmd).as_deref() == Some("eval"),
        None => false,
    }
}

// ===========================================================================
// checkMultiDimensionalArrays — SC2180
// ForShell [Bash]
// ===========================================================================

fn check_multi_dimensional_arrays_gated(p: &Parameters, t: &Token, out: &mut Out) {
    if p.shell == Shell::Bash {
        check_multi_dimensional_arrays(p, t, out);
    }
}

fn check_multi_dimensional_arrays(_p: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Assignment { indices, .. } if indices.len() >= 2 => {
            about(out, &indices[1]);
        }
        InnerToken::T_IndexedElement { indices, .. } if indices.len() >= 2 => {
            about(out, &indices[1]);
        }
        InnerToken::T_DollarBraced { op, .. } => {
            if is_multi_dim(op) {
                about(out, t);
            }
        }
        _ => {}
    }
}

fn about(out: &mut Out, t: &Token) {
    warn(
        out,
        t.id(),
        2180,
        "Bash does not support multidimensional arrays. Use 1D or associative arrays.",
    );
}

/// `getBracedModifier (concat $ oversimplify l) matches ^\[.*\]\[.*\]`.
fn is_multi_dim(l: &Token) -> bool {
    let modifier = get_braced_modifier(&oversimplify_concat(l));
    matches_bracket_bracket(&modifier)
}

/// `^\[.*\]\[.*\]`: `[`, then `]`, then `[`, then `]` in order.
fn matches_bracket_bracket(s: &str) -> bool {
    let cs: Vec<char> = s.chars().collect();
    if cs.first() != Some(&'[') {
        return false;
    }
    let mut i = 1;
    while i < cs.len() && cs[i] != ']' {
        i += 1;
    }
    // i at first ']'
    while i < cs.len() && cs[i] != '[' {
        i += 1;
    }
    // i at '[' after the ']'
    if i >= cs.len() {
        return false;
    }
    while i < cs.len() && cs[i] != ']' {
        i += 1;
    }
    i < cs.len()
}

// ===========================================================================
// checkBangAfterPipe — SC2326
// ForShell [Dash, BusyboxSh, Sh, Bash]
// ===========================================================================

fn check_bang_after_pipe_gated(p: &Parameters, t: &Token, out: &mut Out) {
    if matches!(
        p.shell,
        Shell::Dash | Shell::BusyboxSh | Shell::Sh | Shell::Bash
    ) {
        check_bang_after_pipe(p, t, out);
    }
}

fn check_bang_after_pipe(_p: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Pipeline { commands, .. } = &*t.inner {
        for cmd in commands {
            if let InnerToken::T_Banged(_) = &*cmd.inner {
                err(
                    out,
                    cmd.id(),
                    2326,
                    "! is not allowed in the middle of pipelines. Use command group as in cmd | { ! cmd; } if necessary.",
                );
            }
        }
    }
}

// ===========================================================================
// checkNegatedUnaryOps — SC2332  (HELD BACK — see module tail)
// ForShell [Bash]
// ===========================================================================

fn check_negated_unary_ops_gated(p: &Parameters, t: &Token, out: &mut Out) {
    if p.shell == Shell::Bash {
        check_negated_unary_ops(p, t, out);
    }
}

fn check_negated_unary_ops(_p: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Unary {
        typ: ConditionType::SingleBracket,
        op,
        token,
    } = &*t.inner
    {
        if op == "!" {
            if let InnerToken::TC_Unary { op: inner_op, .. } = &*token.inner {
                if inner_op == "-o" {
                    err(
                        out,
                        t.id(),
                        2332,
                        "[ ! -o opt ] is always true because -o becomes logical OR. Use [[ ]] or ! [ -o opt ].",
                    );
                } else if inner_op == "-a" {
                    err(
                        out,
                        t.id(),
                        2332,
                        "[ ! -a file ] is always true because -a becomes logical AND. Use -e instead.",
                    );
                }
            }
        }
    }
}

// ===========================================================================
// checkBashisms — the full SC30xx family.
//
// `bashism` is the ungated body (Haskell's `f`). It is exercised by the
// prop_ tests but not registered (batch_h owns registration; double
// registration would double-emit). `check_bashisms_gaps` (registered) runs
// only the branches batch_h omits.
// ===========================================================================

// ---- test-operator tables (`bashismBinaryTestFlags` / `bashismUnaryTestFlags`) ----

fn bashism_binary_test(op: &str) -> Option<(i64, &'static [Shell], String)> {
    Some(match op {
        "<" | ">" | "\\<" | "\\>" | "<=" | ">=" | "\\<=" | "\\>=" => (
            3012,
            &[Shell::Dash, Shell::BusyboxSh][..],
            format!("lexicographical {} is", op),
        ),
        "==" => (
            3014,
            &[Shell::BusyboxSh][..],
            format!("{} in place of = is", op),
        ),
        "=~" => (3015, &[][..], format!("{} regex matching is", op)),
        _ => return None,
    })
}

fn bashism_unary_test(op: &str) -> Option<(i64, &'static [Shell], String)> {
    Some(match op {
        "-v" => (
            3016,
            &[][..],
            format!("test {} (in place of [ -n \"${{var+x}}\" ]) is", op),
        ),
        "-a" => (3017, &[][..], format!("unary {} in place of -e is", op)),
        "-o" => (3062, &[][..], format!("test {} to check options is", op)),
        "-R" => (
            3063,
            &[][..],
            format!("test {} and namerefs in general are", op),
        ),
        "-N" => (3064, &[][..], format!("test {} is", op)),
        "-k" => (
            3065,
            &[Shell::Dash, Shell::BusyboxSh][..],
            format!("test {} is", op),
        ),
        "-G" => (
            3066,
            &[Shell::Dash, Shell::BusyboxSh][..],
            format!("test {} is", op),
        ),
        "-O" => (
            3067,
            &[Shell::Dash, Shell::BusyboxSh][..],
            format!("test {} is", op),
        ),
        _ => return None,
    })
}

fn check_test_op(
    out: &mut Out,
    p: &Parameters,
    id: Id,
    op: &str,
    table: fn(&str) -> Option<(i64, &'static [Shell], String)>,
) {
    if let Some((code, exempt, msg)) = table(op) {
        if !exempt.contains(&p.shell) {
            warn_msg(out, p, id, code, &msg);
        }
    }
}

// ---- bash-only variables (SC3028) ----

const BASH_VARS: &[&str] = &[
    "OSTYPE",
    "MACHTYPE",
    "HOSTTYPE",
    "HOSTNAME",
    "DIRSTACK",
    "EUID",
    "UID",
    "SHLVL",
    "PIPESTATUS",
    "SHELLOPTS",
    "_",
    "BASH",
    "BASHOPTS",
    "BASHPID",
    "BASH_ALIASES",
    "BASH_ARGC",
    "BASH_ARGV",
    "BASH_ARGV0",
    "BASH_CMDS",
    "BASH_COMMAND",
    "BASH_EXECUTION_STRING",
    "BASH_LINENO",
    "BASH_LOADABLES_PATH",
    "BASH_REMATCH",
    "BASH_SOURCE",
    "BASH_SUBSHELL",
    "BASH_VERSINFO",
    "COMP_CWORD",
    "COMP_KEY",
    "COMP_LINE",
    "COMP_POINT",
    "COMP_TYPE",
    "COMP_WORDBREAKS",
    "COMP_WORDS",
    "COPROC",
    "FUNCNAME",
    "GROUPS",
    "HISTCMD",
    "MAPFILE",
];
const BASH_DYNAMIC_VARS: &[&str] = &[
    "BASH_MONOSECONDS",
    "EPOCHREALTIME",
    "EPOCHSECONDS",
    "RANDOM",
    "SECONDS",
    "SRANDOM",
];
const DASH_VARS: &[&str] = &["_"];

fn is_assigned(p: &Parameters, name: &str) -> bool {
    p.id_map
        .values()
        .any(|t| matches!(&*t.inner, InnerToken::T_Assignment { var, .. } if var == name))
}

fn is_bash_variable(p: &Parameters, var: &str) -> bool {
    let dyn_or_static =
        BASH_DYNAMIC_VARS.contains(&var) || (BASH_VARS.contains(&var) && !is_assigned(p, var));
    dyn_or_static && !(is_dash(p) && DASH_VARS.contains(&var))
}

// ---- DollarBraced expansion regex matchers (varChars = [_0-9a-zA-Z]) ----

fn is_v(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}
fn is_v_star_at(c: char) -> bool {
    is_v(c) || c == '*' || c == '@'
}
fn re_3053(s: &[char]) -> bool {
    s.first() == Some(&'!') && s.len() >= 2 && is_v(s[1])
}
fn re_3054(s: &[char]) -> bool {
    let i = s.iter().take_while(|&&c| is_v(c)).count();
    i >= 1 && i < s.len() && s[i] == '[' && s.last() == Some(&']') && s.len() - 1 > i
}
fn re_3055(s: &[char]) -> bool {
    if s.first() != Some(&'!') {
        return false;
    }
    let cnt = s[1..].iter().take_while(|&&c| is_v(c)).count();
    if cnt < 1 {
        return false;
    }
    let i = 1 + cnt;
    i + 3 == s.len() && s[i] == '[' && (s[i + 1] == '*' || s[i + 1] == '@') && s[i + 2] == ']'
}
fn re_3056(s: &[char]) -> bool {
    if s.first() != Some(&'!') {
        return false;
    }
    let cnt = s[1..].iter().take_while(|&&c| is_v(c)).count();
    if cnt < 1 {
        return false;
    }
    let i = 1 + cnt;
    i + 1 == s.len() && (s[i] == '*' || s[i] == '@')
}
fn re_3059(s: &[char]) -> bool {
    let i = s.iter().take_while(|&&c| is_v_star_at(c)).count();
    if i == 0 {
        return false;
    }
    if i < s.len() && (s[i] == ',' || s[i] == '^') {
        return true;
    }
    if i < s.len() && s[i] == '[' {
        for p in (i + 1)..s.len() {
            if s[p] == ']' && p + 1 < s.len() && (s[p + 1] == ',' || s[p + 1] == '^') {
                return true;
            }
        }
    }
    false
}
fn re_3057(s: &[char]) -> bool {
    let i = s.iter().take_while(|&&c| is_v_star_at(c)).count();
    i >= 1 && i < s.len() && s[i] == ':' && i + 1 < s.len() && !"-=?+".contains(s[i + 1])
}
fn re_3058(s: &[char]) -> bool {
    if s.len() < 2 {
        return false;
    }
    ((s[0] == '*' || s[0] == '@') && (s[1] == '%' || s[1] == '#'))
        || (s[0] == '#' && (s[1] == '@' || s[1] == '*'))
}
fn re_3060(s: &[char]) -> bool {
    let i = s.iter().take_while(|&&c| is_v_star_at(c)).count();
    if i == 0 {
        return false;
    }
    if i < s.len() && s[i] == '/' {
        return true;
    }
    if i < s.len() && s[i] == '[' {
        for p in (i + 1)..s.len() {
            if s[p] == ']' && p + 1 < s.len() && s[p + 1] == '/' {
                return true;
            }
        }
    }
    false
}

// ---- echo flag regexes ----

fn echo_flag(s: &str) -> bool {
    s.len() >= 2 && s.starts_with('-') && s[1..].chars().all(|c| "eEsn".contains(c))
}
fn busybox_echo_flag(s: &str) -> bool {
    s.len() >= 2 && s.starts_with('-') && s[1..].chars().all(|c| "en".contains(c))
}

// ---- radix literal (`^[0-9]+#`) ----

fn matches_radix(s: &str) -> bool {
    let mut it = s.chars();
    let mut saw_digit = false;
    for c in it.by_ref() {
        if c.is_ascii_digit() {
            saw_digit = true;
        } else if c == '#' {
            return saw_digit;
        } else {
            return false;
        }
    }
    false
}

// ---- glob / redirection predicates ----

// ---- leading flags (`getLeadingFlags` / `getFlagsUntil`) ----

fn get_leading_flags(t: &Token) -> Vec<(&Token, String)> {
    let args = arguments(t);
    let mut broken = false;
    let mut out: Vec<(&Token, String)> = vec![];
    for x in args {
        let txt = oversimplify_concat(x);
        if !broken && (txt == "--" || !txt.starts_with('-')) {
            broken = true;
        }
        if broken {
            out.push((x, String::new()));
        } else if let Some(a) = txt.strip_prefix("--") {
            out.push((x, a.split('=').next().unwrap_or("").to_string()));
        } else if let Some(a) = txt.strip_prefix('-') {
            for v in a.chars() {
                out.push((x, v.to_string()));
            }
        } else {
            out.push((x, String::new()));
        }
    }
    out
}

// ---- the ungated body ----

fn bashism(p: &Parameters, t: &Token, out: &mut Out) {
    let id = t.id();
    use InnerToken::*;
    match &*t.inner {
        T_ProcSub { .. } => warn_msg(out, p, id, 3001, "process substitution is"),
        T_Extglob { .. } => warn_msg(out, p, id, 3002, "extglob is"),
        T_DollarDoubleQuoted(_) => warn_msg(out, p, id, 3004, "$\"..\" is"),
        T_ForArithmetic { .. } => warn_msg(out, p, id, 3005, "arithmetic for loops are"),
        T_Arithmetic(_) => warn_msg(out, p, id, 3006, "standalone ((..)) is"),
        T_DollarBracket(_) => warn_msg(out, p, id, 3007, "$[..] in place of $((..)) is"),
        T_SelectIn { .. } => warn_msg(out, p, id, 3008, "select loops are"),
        T_BraceExpansion(_) => warn_msg(out, p, id, 3009, "brace expansion is"),
        T_Condition {
            typ: ConditionType::DoubleBracket,
            ..
        } => {
            if !is_busybox(p) {
                warn_msg(out, p, id, 3010, "[[ ]] is");
            }
        }
        T_HereString(_) => warn_msg(out, p, id, 3011, "here-strings are"),

        TC_Binary { op, .. } => check_test_op(out, p, id, op, bashism_binary_test),
        TC_Unary { op, .. } => check_test_op(out, p, id, op, bashism_unary_test),

        TA_Unary { op, .. } if matches!(op.as_str(), "|++" | "|--" | "++|" | "--|") => {
            let filtered: String = op.chars().filter(|&c| c != '|').collect();
            warn_msg(out, p, id, 3018, &format!("{} is", filtered));
        }
        TA_Binary { op, .. } if op == "**" => {
            warn_msg(out, p, id, 3019, "exponentials are");
        }

        T_FdRedirect { fd, target } => bashism_fd_redirect(p, id, fd, target, out),

        T_Assignment {
            mode: AssignmentMode::Append,
            ..
        } => {
            warn_msg(out, p, id, 3024, "+= is");
        }

        T_IoFile { file, .. } => {
            let f = only_literal_string(file);
            if f.starts_with("/dev/tcp") || f.starts_with("/dev/udp") {
                warn_msg(out, p, id, 3025, "/dev/{tcp,udp} is");
            } else if is_glob(file) {
                warn_msg(out, p, id, 3031, "redirecting to/from globs is");
            }
        }

        T_Glob(s) if s.contains("[^") => {
            warn_msg(
                out,
                p,
                id,
                3026,
                "^ in place of ! in glob bracket expressions is",
            );
        }

        TA_Variable { name, .. } if is_bash_variable(p, name) => {
            warn_msg(out, p, id, 3028, &format!("{} is", name));
        }

        T_Pipe(op) if op == "|&" => warn_msg(out, p, id, 3029, "|& in place of 2>&1 | is"),
        T_Array(_) => warn_msg(out, p, id, 3030, "arrays are"),
        T_CoProc { .. } => warn_msg(out, p, id, 3032, "coproc is"),

        T_Function { name, .. } if !is_variable_name(name) => {
            warn_msg(
                out,
                p,
                id,
                3033,
                "naming functions outside [a-zA-Z_][a-zA-Z0-9_]* is",
            );
        }

        T_DollarExpansion(list) if list.len() == 1 && is_only_redirection(&list[0]) => {
            warn_msg(out, p, id, 3034, "$(<file) to read files is");
        }
        T_Backticked(list) if list.len() == 1 && is_only_redirection(&list[0]) => {
            warn_msg(out, p, id, 3035, "`<file` to read files is");
        }

        T_DollarBraced { op, .. } => bashism_dollar_braced(p, id, op, out),

        T_SourceCommand { includer, .. } => {
            if crate::analyzer_lib::get_command_name(includer).as_deref() == Some("source")
                && !is_busybox(p)
            {
                warn_msg(out, p, id, 3051, "'source' in place of '.' is");
            }
        }

        TA_Expansion(pieces) => {
            if let Some(first) = pieces.first() {
                if let InnerToken::T_Literal(s) = &*first.inner {
                    if matches_radix(s) {
                        warn_msg(out, p, first.id(), 3052, "arithmetic base conversion is");
                    }
                }
            }
        }

        T_SimpleCommand { words, .. } => check_simple_command(p, t, words, out),

        _ => {}
    }
}

fn bashism_fd_redirect(p: &Parameters, id: Id, fd: &str, target: &Token, out: &mut Out) {
    // &>  (T_FdRedirect "&" (T_IoFile (T_Greater) _))
    if fd == "&" {
        if let InnerToken::T_IoFile { op, .. } = &*target.inner {
            if matches!(&*op.inner, InnerToken::T_Greater) {
                if !is_busybox(p) {
                    warn_msg(out, p, id, 3020, "&> is");
                }
                return;
            }
        }
    }
    // >& filename  (T_FdRedirect "" (T_IoFile (T_GREATAND) file))
    if fd.is_empty() {
        if let InnerToken::T_IoFile { op, file } = &*target.inner {
            if matches!(&*op.inner, InnerToken::T_GREATAND) {
                if !only_literal_string(file)
                    .chars()
                    .all(|c| c.is_ascii_digit())
                {
                    warn_msg(out, p, id, 3021, ">& filename (as opposed to >& fd) is");
                }
                return;
            }
        }
    }
    // named file descriptors  (T_FdRedirect ('{':_) _)
    if fd.starts_with('{') {
        warn_msg(out, p, id, 3022, "named file descriptors are");
        return;
    }
    // FDs outside 0-9  (all digits, length > 1)
    if fd.len() > 1 && fd.chars().all(|c| c.is_ascii_digit()) {
        warn_msg(out, p, id, 3023, "FDs outside 0-9 are");
    }
}

fn bashism_dollar_braced(p: &Parameters, id: Id, op: &Token, out: &mut Out) {
    let s = oversimplify_concat(op);
    let cs: Vec<char> = s.chars().collect();
    if !is_busybox(p) {
        if re_3057(&cs) {
            warn_msg(out, p, id, 3057, "string indexing is");
        }
        if re_3058(&cs) {
            warn_msg(out, p, id, 3058, "string operations on $@/$* are");
        }
        if re_3060(&cs) {
            warn_msg(out, p, id, 3060, "string replacement is");
        }
    }
    if re_3053(&cs) {
        warn_msg(out, p, id, 3053, "indirect expansion is");
    }
    if re_3054(&cs) {
        warn_msg(out, p, id, 3054, "array references are");
    }
    if re_3055(&cs) {
        warn_msg(out, p, id, 3055, "array key expansion is");
    }
    if re_3056(&cs) {
        warn_msg(out, p, id, 3056, "name matching prefixes are");
    }
    if re_3059(&cs) {
        warn_msg(out, p, id, 3059, "case modification is");
    }
    let var = get_braced_reference(&s);
    if is_bash_variable(p, &var) {
        warn_msg(out, p, id, 3028, &format!("{} is", var));
    }
}

fn check_simple_command(p: &Parameters, t: &Token, words: &[Token], out: &mut Out) {
    if words.is_empty() {
        return;
    }
    let id = t.id();

    // test-command forms: `test x == y`, `test -v var`.
    if words.len() == 4 && get_literal_string(&words[0]).as_deref() == Some("test") {
        if let Some(op) = get_literal_string(&words[2]) {
            check_test_op(out, p, id, &op, bashism_binary_test);
        }
    }
    if words.len() == 3 && get_literal_string(&words[0]).as_deref() == Some("test") {
        if let Some(op) = get_literal_string(&words[1]) {
            check_test_op(out, p, id, &op, bashism_unary_test);
        }
    }

    let cmd = &words[0];

    if words.len() >= 2 && crate::analyzer_lib::is_command(t, "echo") {
        let arg = &words[1];
        let arg_string = oversimplify_concat(arg);
        if echo_flag(&arg_string) {
            if is_busybox(p) {
                if !busybox_echo_flag(&arg_string) {
                    warn_msg(out, p, arg.id(), 3036, "echo flags besides -n and -e");
                }
            } else if is_dash(p) {
                if arg_string != "-n" {
                    warn_msg(out, p, arg.id(), 3036, "echo flags besides -n");
                }
            } else {
                warn_msg(out, p, arg.id(), 3037, "echo flags are");
            }
            return;
        }
    }
    if words.len() >= 2 && get_literal_string(cmd).as_deref() == Some("exec") {
        let arg = &words[1];
        if oversimplify_concat(arg).starts_with('-') {
            warn_msg(out, p, arg.id(), 3038, "exec flags are");
            return;
        }
    }
    if crate::analyzer_lib::is_command(t, "let") {
        warn_msg(out, p, id, 3039, "'let' is");
        return;
    }
    if crate::analyzer_lib::is_command(t, "set") {
        if !is_dash(p) {
            check_set_options(p, t, out);
        }
        return;
    }

    check_general_command(p, t, words, out);
}

const UNSUPPORTED_COMMANDS: &[&str] = &[
    "let",
    "caller",
    "builtin",
    "complete",
    "compgen",
    "declare",
    "dirs",
    "disown",
    "enable",
    "mapfile",
    "readarray",
    "pushd",
    "popd",
    "shopt",
    "suspend",
    "typeset",
];

fn allowed_flags(name: &str, p: &Parameters) -> Option<Vec<&'static str>> {
    let dash = is_dash(p);
    let busybox = is_busybox(p);
    Some(match name {
        "cd" => vec!["L", "P"],
        "exec" => vec![],
        "export" => vec!["p"],
        "hash" => {
            if dash {
                vec!["r", "v"]
            } else {
                vec!["r"]
            }
        }
        "jobs" => vec!["l", "p"],
        "printf" => vec![],
        "read" => {
            if dash || busybox {
                vec!["r", "p"]
            } else {
                vec!["r"]
            }
        }
        "readonly" => vec!["p"],
        "trap" => vec![],
        "type" => {
            if busybox {
                vec!["p"]
            } else {
                vec![]
            }
        }
        "ulimit" => {
            if dash {
                vec![
                    "H", "S", "a", "c", "d", "f", "l", "m", "n", "p", "r", "s", "t", "v", "w",
                ]
            } else {
                vec!["H", "S", "a", "c", "d", "f", "n", "s", "t", "v"]
            }
        }
        "umask" => vec!["S"],
        "unset" => vec!["f", "v"],
        "wait" => vec![],
        _ => return None,
    })
}

fn is_assignment_form(s: &str) -> bool {
    let c: Vec<char> = s.chars().collect();
    if c.is_empty() || !(c[0] == '_' || c[0].is_ascii_alphabetic()) {
        return false;
    }
    let mut i = 1;
    while i < c.len() && (c[i] == '_' || c[i].is_ascii_alphanumeric()) {
        i += 1;
    }
    if i < c.len() && c[i] == '+' {
        i += 1;
    }
    i < c.len() && c[i] == '='
}

fn check_general_command(p: &Parameters, t: &Token, words: &[Token], out: &mut Out) {
    let id = t.id();
    let cmd = &words[0];
    let name = crate::analyzer_lib::get_command_name(t).unwrap_or_default();
    let rest = &words[1..];

    let ends_in_assignment = words.len() > 1
        && words
            .last()
            .map(|w| is_assignment_form(&oversimplify_concat(w)))
            .unwrap_or(false);

    if name == "local" && !is_dash(p) && !ends_in_assignment {
        warn_msg(out, p, id, 3043, "'local' is");
    }
    if UNSUPPORTED_COMMANDS.contains(&name.as_str()) && !ends_in_assignment {
        warn_msg(out, p, id, 3044, &format!("'{}' is", name));
    }

    if let Some(allowed) = allowed_flags(&name, p) {
        let flags = get_leading_flags(t);
        if let Some((word, flag)) = flags
            .iter()
            .find(|(_, f)| !f.is_empty() && !allowed.contains(&f.as_str()))
        {
            warn_msg(out, p, word.id(), 3045, &format!("{} -{} is", name, flag));
        }
    }

    if name == "source" && !is_busybox(p) {
        warn_msg(out, p, id, 3046, "'source' in place of '.' is");
    }

    if name == "trap" {
        for token in rest.iter().skip(1) {
            if let Some(s) = get_literal_string(token) {
                let upper = s.to_uppercase();
                if matches!(upper.as_str(), "ERR" | "DEBUG" | "RETURN") {
                    warn_msg(out, p, token.id(), 3047, &format!("trapping {} is", s));
                }
                if !is_busybox(p) && upper.starts_with("SIG") {
                    warn_msg(
                        out,
                        p,
                        token.id(),
                        3048,
                        "prefixing signal names with 'SIG' is",
                    );
                }
                if !is_dash(p) && upper != s {
                    warn_msg(
                        out,
                        p,
                        token.id(),
                        3049,
                        "using lower/mixed case for signal names is",
                    );
                }
            }
        }
    }

    if name == "printf" {
        if let Some(format) = rest.first() {
            if only_literal_string(format).contains("%q") {
                warn_msg(out, p, format.id(), 3050, "printf %q is");
            }
        }
    }

    if name == "read" && rest.iter().all(is_flag) {
        warn_msg(out, p, cmd.id(), 3061, "read without a variable is");
    }
}

// ---- set option/flag checking (SC3040/SC3041/SC3042) ----

const SET_OPTIONS: &str = "abCefhmnuvxo";
const SET_LONG_OPTIONS: &[&str] = &[
    "allexport",
    "errexit",
    "ignoreeof",
    "monitor",
    "noclobber",
    "noexec",
    "noglob",
    "nolog",
    "notify",
    "nounset",
    "pipefail",
    "verbose",
    "vi",
    "xtrace",
];

fn set_starts_option(s: &str) -> bool {
    let b = s.as_bytes();
    s.starts_with('+') || (b.first() == Some(&b'-') && b.len() >= 2 && b[1] != b'-')
}
fn set_begins_double_dash(s: &str) -> bool {
    s.starts_with("--") && s.len() > 2
}
fn set_o_flag(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() >= 2
        && (b[0] == b'-' || b[0] == b'+')
        && s.ends_with('o')
        && s[1..].chars().all(|c| SET_OPTIONS.contains(c))
}
fn set_valid_flags(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() >= 2
        && (b[0] == b'-' || b[0] == b'+')
        && s[1..].chars().all(|c| SET_OPTIONS.contains(c))
}

fn check_set_options(p: &Parameters, t: &Token, out: &mut Out) {
    let mut args: Vec<(Id, String)> = vec![];
    for a in arguments(t) {
        match get_literal_string(a) {
            Some(s) => args.push((a.id(), s)),
            None => break,
        }
    }
    check_set_options_rec(p, &args, out);
}

fn check_set_options_rec(p: &Parameters, args: &[(Id, String)], out: &mut Out) {
    if args.len() >= 2 {
        let (_fid, flag) = &args[0];
        let (oid, opt) = &args[1];
        if set_o_flag(flag) {
            if !SET_LONG_OPTIONS.contains(&opt.as_str()) {
                warn_msg(out, p, *oid, 3040, &format!("set option {} is", opt));
            }
            let mut next = vec![args[0].clone()];
            next.extend_from_slice(&args[2..]);
            check_set_flags_rec(p, &next, out);
            return;
        }
        check_set_flags_rec(p, args, out);
        return;
    }
    if args.len() == 1 {
        check_set_flags_rec(p, args, out);
    }
}

fn check_set_flags_rec(p: &Parameters, args: &[(Id, String)], out: &mut Out) {
    if args.is_empty() {
        return;
    }
    let (fid, flag) = &args[0];
    let rest = &args[1..];
    if set_starts_option(flag) {
        if !set_valid_flags(flag) {
            for letter in flag.chars().skip(1) {
                if !SET_OPTIONS.contains(letter) {
                    warn_msg(out, p, *fid, 3041, &format!("set flag -{} is", letter));
                }
            }
        }
        check_set_options_rec(p, rest, out);
    } else if set_begins_double_dash(flag) {
        warn_msg(out, p, *fid, 3042, &format!("set flag {} is", flag));
        check_set_options_rec(p, rest, out);
    }
}

// ===========================================================================
// Registered gap-filler: the SC30xx branches batch_h omits, restricted to
// those whose node span matches the oracle. Gated to sh/dash/busybox exactly
// like checkBashisms.
// ===========================================================================

fn check_bashisms_gaps(p: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(p.shell, Shell::Sh | Shell::Dash | Shell::BusyboxSh) {
        return;
    }
    let id = t.id();
    use InnerToken::*;
    match &*t.inner {
        // TC_Binary inherits the operator span (matches the oracle).
        TC_Binary { op, .. } => check_test_op(out, p, id, op, bashism_binary_test),

        // TC_Unary now spans the operator alone (matches the oracle), so the
        // unary test-operator bashisms (SC3016/3017/3062/3063/3064/3065/3066/
        // 3067) can be emitted here. batch_h handles only the `test`
        // SimpleCommand form, so there is no double emission.
        TC_Unary { op, .. } => check_test_op(out, p, id, op, bashism_unary_test),

        // Arithmetic increments/decrements and exponentials.
        TA_Unary { op, .. } if matches!(op.as_str(), "|++" | "|--" | "++|" | "--|") => {
            let filtered: String = op.chars().filter(|&c| c != '|').collect();
            warn_msg(out, p, id, 3018, &format!("{} is", filtered));
        }
        TA_Binary { op, .. } if op == "**" => {
            warn_msg(out, p, id, 3019, "exponentials are");
        }

        // &> / >&file / {n}> — but NOT the all-digit 3023 (batch_h owns it).
        T_FdRedirect { fd, target } => {
            if fd == "&" {
                if let InnerToken::T_IoFile { op, .. } = &*target.inner {
                    if matches!(&*op.inner, InnerToken::T_Greater) && !is_busybox(p) {
                        warn_msg(out, p, id, 3020, "&> is");
                    }
                }
            } else if fd.is_empty() {
                if let InnerToken::T_IoFile { op, file } = &*target.inner {
                    if matches!(&*op.inner, InnerToken::T_GREATAND)
                        && !only_literal_string(file)
                            .chars()
                            .all(|c| c.is_ascii_digit())
                    {
                        warn_msg(out, p, id, 3021, ">& filename (as opposed to >& fd) is");
                    }
                }
            } else if fd.starts_with('{') {
                warn_msg(out, p, id, 3022, "named file descriptors are");
            }
        }

        // += append assignments.
        T_Assignment {
            mode: AssignmentMode::Append,
            ..
        } => {
            warn_msg(out, p, id, 3024, "+= is");
        }

        // 'source' in place of '.' (T_SourceCommand form).
        T_SourceCommand { includer, .. } => {
            if crate::analyzer_lib::get_command_name(includer).as_deref() == Some("source")
                && !is_busybox(p)
            {
                warn_msg(out, p, id, 3051, "'source' in place of '.' is");
            }
        }

        // Arithmetic base conversion (radix literal).
        TA_Expansion(pieces) => {
            if let Some(first) = pieces.first() {
                if let InnerToken::T_Literal(s) = &*first.inner {
                    if matches_radix(s) {
                        warn_msg(out, p, first.id(), 3052, "arithmetic base conversion is");
                    }
                }
            }
        }

        _ => {}
    }
}

// ===========================================================================
// Tests (ported from the QuickCheck `prop_` properties).
// ===========================================================================
#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::interface::Shell;
    use crate::parser::parse_script;

    fn params_auto(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }

    /// Run an ungated check body over every node (mirrors `testChecker`, which
    /// bypasses the ForShell dialect gate), returning whether any comment fired.
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_auto(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // ---- checkForDecimals (SC2079) ----
    #[test]
    fn prop_checkForDecimals1() {
        assert!(emits(check_for_decimals, "((3.14*c))"));
    }
    #[test]
    fn prop_checkForDecimals2() {
        assert!(emits(check_for_decimals, "foo[1.2]=bar"));
    }
    #[test]
    fn prop_checkForDecimals3() {
        assert!(!emits(check_for_decimals, "declare -A foo; foo[1.2]=bar"));
    }

    // ---- checkBashisms (full SC30xx family) ----
    #[test]
    fn prop_checkBashisms() {
        assert!(emits(bashism, "while read a; do :; done < <(a)"));
    }
    #[test]
    fn prop_checkBashisms2() {
        assert!(!emits(bashism, "[ foo -nt bar ]"));
    }
    #[test]
    fn prop_checkBashisms3() {
        assert!(emits(bashism, "echo $((i++))"));
    }
    #[test]
    fn prop_checkBashisms4() {
        assert!(emits(bashism, "rm !(*.hs)"));
    }
    #[test]
    fn prop_checkBashisms5() {
        assert!(emits(bashism, "source file"));
    }
    #[test]
    fn prop_checkBashisms6() {
        assert!(emits(bashism, "[ \"$a\" == 42 ]"));
    }
    #[test]
    fn prop_checkBashisms6b() {
        assert!(emits(bashism, "test \"$a\" == 42"));
    }
    #[test]
    fn prop_checkBashisms6c() {
        assert!(emits(bashism, "[ foo =~ bar ]"));
    }
    #[test]
    fn prop_checkBashisms6d() {
        assert!(emits(bashism, "test foo =~ bar"));
    }
    #[test]
    fn prop_checkBashisms7() {
        assert!(emits(bashism, "echo ${var[1]}"));
    }
    #[test]
    fn prop_checkBashisms8() {
        assert!(emits(bashism, "echo ${!var[@]}"));
    }
    #[test]
    fn prop_checkBashisms9() {
        assert!(emits(bashism, "echo ${!var*}"));
    }
    #[test]
    fn prop_checkBashisms10() {
        assert!(emits(bashism, "echo ${var:4:12}"));
    }
    #[test]
    fn prop_checkBashisms11() {
        assert!(!emits(bashism, "echo ${var:-4}"));
    }
    #[test]
    fn prop_checkBashisms12() {
        assert!(emits(bashism, "echo ${var//foo/bar}"));
    }
    #[test]
    fn prop_checkBashisms13() {
        assert!(emits(bashism, "exec -c env"));
    }
    #[test]
    fn prop_checkBashisms14() {
        assert!(emits(bashism, "echo -n \"Foo: \""));
    }
    #[test]
    fn prop_checkBashisms15() {
        assert!(emits(bashism, "let n++"));
    }
    #[test]
    fn prop_checkBashisms16() {
        assert!(emits(bashism, "echo $RANDOM"));
    }
    #[test]
    fn prop_checkBashisms17() {
        assert!(emits(bashism, "echo $((RANDOM%6+1))"));
    }
    #[test]
    fn prop_checkBashisms18() {
        assert!(emits(bashism, "foo &> /dev/null"));
    }
    #[test]
    fn prop_checkBashisms19() {
        assert!(emits(bashism, "foo > file*.txt"));
    }
    #[test]
    fn prop_checkBashisms20() {
        assert!(emits(bashism, "read -ra foo"));
    }
    #[test]
    fn prop_checkBashisms21() {
        assert!(emits(bashism, "[ -a foo ]"));
    }
    #[test]
    fn prop_checkBashisms21b() {
        assert!(emits(bashism, "test -a foo"));
    }
    #[test]
    fn prop_checkBashisms22() {
        assert!(!emits(bashism, "[ foo -a bar ]"));
    }
    #[test]
    fn prop_checkBashisms23() {
        assert!(emits(bashism, "trap mything ERR INT"));
    }
    #[test]
    fn prop_checkBashisms24() {
        assert!(!emits(bashism, "trap mything INT TERM"));
    }
    #[test]
    fn prop_checkBashisms25() {
        assert!(emits(bashism, "cat < /dev/tcp/host/123"));
    }
    #[test]
    fn prop_checkBashisms26() {
        assert!(emits(bashism, "trap mything ERR SIGTERM"));
    }
    #[test]
    fn prop_checkBashisms27() {
        assert!(emits(bashism, "echo *[^0-9]*"));
    }
    #[test]
    fn prop_checkBashisms28() {
        assert!(emits(bashism, "exec {n}>&2"));
    }
    #[test]
    fn prop_checkBashisms29() {
        assert!(emits(bashism, "echo ${!var}"));
    }
    #[test]
    fn prop_checkBashisms30() {
        assert!(emits(bashism, "printf -v '%s' \"$1\""));
    }
    #[test]
    fn prop_checkBashisms31() {
        assert!(emits(bashism, "printf '%q' \"$1\""));
    }
    #[test]
    fn prop_checkBashisms32() {
        assert!(!emits(bashism, "#!/bin/dash\n[ foo -nt bar ]"));
    }
    #[test]
    fn prop_checkBashisms33() {
        assert!(emits(bashism, "#!/bin/sh\necho -n foo"));
    }
    #[test]
    fn prop_checkBashisms34() {
        assert!(!emits(bashism, "#!/bin/dash\necho -n foo"));
    }
    #[test]
    fn prop_checkBashisms35() {
        assert!(!emits(bashism, "#!/bin/dash\nlocal foo"));
    }
    #[test]
    fn prop_checkBashisms36() {
        assert!(!emits(bashism, "#!/bin/dash\nread -p foo -r bar"));
    }
    #[test]
    fn prop_checkBashisms37() {
        assert!(!emits(bashism, "HOSTNAME=foo; echo $HOSTNAME"));
    }
    #[test]
    fn prop_checkBashisms38() {
        assert!(emits(bashism, "RANDOM=9; echo $RANDOM"));
    }
    #[test]
    fn prop_checkBashisms39() {
        assert!(emits(bashism, "foo-bar() { true; }"));
    }
    #[test]
    fn prop_checkBashisms40() {
        assert!(emits(bashism, "echo $(<file)"));
    }
    #[test]
    fn prop_checkBashisms41() {
        assert!(emits(bashism, "echo `<file`"));
    }
    #[test]
    fn prop_checkBashisms42() {
        assert!(emits(bashism, "trap foo int"));
    }
    #[test]
    fn prop_checkBashisms43() {
        assert!(emits(bashism, "trap foo sigint"));
    }
    #[test]
    fn prop_checkBashisms44() {
        assert!(!emits(bashism, "#!/bin/dash\ntrap foo int"));
    }
    #[test]
    fn prop_checkBashisms45() {
        assert!(!emits(bashism, "#!/bin/dash\ntrap foo INT"));
    }
    #[test]
    fn prop_checkBashisms46() {
        assert!(emits(bashism, "#!/bin/dash\ntrap foo SIGINT"));
    }
    #[test]
    fn prop_checkBashisms47() {
        assert!(emits(bashism, "#!/bin/dash\necho foo 42>/dev/null"));
    }
    #[test]
    fn prop_checkBashisms48() {
        assert!(!emits(bashism, "#!/bin/sh\necho $LINENO"));
    }
    #[test]
    fn prop_checkBashisms49() {
        assert!(emits(bashism, "#!/bin/dash\necho $MACHTYPE"));
    }
    #[test]
    fn prop_checkBashisms50() {
        assert!(emits(bashism, "#!/bin/sh\ncmd >& file"));
    }
    #[test]
    fn prop_checkBashisms51() {
        assert!(!emits(bashism, "#!/bin/sh\ncmd 2>&1"));
    }
    #[test]
    fn prop_checkBashisms52() {
        assert!(!emits(bashism, "#!/bin/sh\ncmd >&2"));
    }
    #[test]
    fn prop_checkBashisms52b() {
        assert!(!emits(bashism, "#!/bin/sh\ncmd >& $var"));
    }
    #[test]
    fn prop_checkBashisms52c() {
        assert!(emits(bashism, "#!/bin/sh\ncmd >& $dir/$var"));
    }
    #[test]
    fn prop_checkBashisms53() {
        assert!(!emits(bashism, "#!/bin/sh\nprintf -- -f\n"));
    }
    #[test]
    fn prop_checkBashisms54() {
        assert!(emits(bashism, "#!/bin/sh\nfoo+=bar"));
    }
    #[test]
    fn prop_checkBashisms55() {
        assert!(emits(bashism, "#!/bin/sh\necho ${@%foo}"));
    }
    #[test]
    fn prop_checkBashisms56() {
        assert!(!emits(bashism, "#!/bin/sh\necho ${##}"));
    }
    #[test]
    fn prop_checkBashisms57() {
        assert!(!emits(bashism, "#!/bin/dash\nulimit -m unlimited"));
    }
    #[test]
    fn prop_checkBashisms58() {
        assert!(emits(bashism, "#!/bin/sh\nulimit -x unlimited"));
    }
    #[test]
    fn prop_checkBashisms59() {
        assert!(emits(bashism, "#!/bin/sh\njobs -s"));
    }
    #[test]
    fn prop_checkBashisms60() {
        assert!(!emits(bashism, "#!/bin/sh\njobs -p"));
    }
    #[test]
    fn prop_checkBashisms61() {
        assert!(!emits(bashism, "#!/bin/sh\njobs -lp"));
    }
    #[test]
    fn prop_checkBashisms62() {
        assert!(emits(bashism, "#!/bin/sh\nexport -f foo"));
    }
    #[test]
    fn prop_checkBashisms63() {
        assert!(!emits(bashism, "#!/bin/sh\nexport -p"));
    }
    #[test]
    fn prop_checkBashisms64() {
        assert!(emits(bashism, "#!/bin/sh\nreadonly -a"));
    }
    #[test]
    fn prop_checkBashisms65() {
        assert!(!emits(bashism, "#!/bin/sh\nreadonly -p"));
    }
    #[test]
    fn prop_checkBashisms66() {
        assert!(!emits(bashism, "#!/bin/sh\ncd -P ."));
    }
    #[test]
    fn prop_checkBashisms67() {
        assert!(emits(bashism, "#!/bin/sh\ncd -P -e ."));
    }
    #[test]
    fn prop_checkBashisms68() {
        assert!(emits(bashism, "#!/bin/sh\numask -p"));
    }
    #[test]
    fn prop_checkBashisms69() {
        assert!(!emits(bashism, "#!/bin/sh\numask -S"));
    }
    #[test]
    fn prop_checkBashisms70() {
        assert!(emits(bashism, "#!/bin/sh\ntrap -l"));
    }
    #[test]
    fn prop_checkBashisms71() {
        assert!(emits(bashism, "#!/bin/sh\ntype -a ls"));
    }
    #[test]
    fn prop_checkBashisms72() {
        assert!(!emits(bashism, "#!/bin/sh\ntype ls"));
    }
    #[test]
    fn prop_checkBashisms73() {
        assert!(emits(bashism, "#!/bin/sh\nunset -n namevar"));
    }
    #[test]
    fn prop_checkBashisms74() {
        assert!(!emits(bashism, "#!/bin/sh\nunset -f namevar"));
    }
    #[test]
    fn prop_checkBashisms75() {
        assert!(!emits(bashism, "#!/bin/sh\necho \"-n foo\""));
    }
    #[test]
    fn prop_checkBashisms76() {
        assert!(!emits(bashism, "#!/bin/sh\necho \"-ne foo\""));
    }
    #[test]
    fn prop_checkBashisms77() {
        assert!(!emits(bashism, "#!/bin/sh\necho -Q foo"));
    }
    #[test]
    fn prop_checkBashisms78() {
        assert!(emits(bashism, "#!/bin/sh\necho -ne foo"));
    }
    #[test]
    fn prop_checkBashisms79() {
        assert!(emits(bashism, "#!/bin/sh\nhash -l"));
    }
    #[test]
    fn prop_checkBashisms80() {
        assert!(!emits(bashism, "#!/bin/sh\nhash -r"));
    }
    #[test]
    fn prop_checkBashisms81() {
        assert!(!emits(bashism, "#!/bin/dash\nhash -v"));
    }
    #[test]
    fn prop_checkBashisms82() {
        assert!(!emits(
            bashism,
            "#!/bin/sh\nset -v +o allexport -o errexit -C"
        ));
    }
    #[test]
    fn prop_checkBashisms83() {
        assert!(!emits(bashism, "#!/bin/sh\nset --"));
    }
    #[test]
    fn prop_checkBashisms84() {
        assert!(!emits(bashism, "#!/bin/sh\nset -o pipefail"));
    }
    #[test]
    fn prop_checkBashisms85() {
        assert!(emits(bashism, "#!/bin/sh\nset -B"));
    }
    #[test]
    fn prop_checkBashisms86() {
        assert!(!emits(bashism, "#!/bin/dash\nset -o emacs"));
    }
    #[test]
    fn prop_checkBashisms87() {
        assert!(emits(bashism, "#!/bin/sh\nset -o emacs"));
    }
    #[test]
    fn prop_checkBashisms88() {
        assert!(!emits(
            bashism,
            "#!/bin/sh\nset -- wget -o foo 'https://some.url'"
        ));
    }
    #[test]
    fn prop_checkBashisms89() {
        assert!(!emits(bashism, "#!/bin/sh\nopts=$-\nset -\"$opts\""));
    }
    #[test]
    fn prop_checkBashisms90() {
        assert!(!emits(bashism, "#!/bin/sh\nset -o \"$opt\""));
    }
    #[test]
    fn prop_checkBashisms91() {
        assert!(emits(bashism, "#!/bin/sh\nwait -n"));
    }
    #[test]
    fn prop_checkBashisms92() {
        assert!(emits(bashism, "#!/bin/sh\necho $((16#FF))"));
    }
    #[test]
    fn prop_checkBashisms93() {
        assert!(emits(bashism, "#!/bin/sh\necho $(( 10#$(date +%m) ))"));
    }
    #[test]
    fn prop_checkBashisms94() {
        assert!(emits(bashism, "#!/bin/sh\n[ -v var ]"));
    }
    #[test]
    fn prop_checkBashisms95() {
        assert!(emits(bashism, "#!/bin/sh\necho $_"));
    }
    #[test]
    fn prop_checkBashisms96() {
        assert!(!emits(bashism, "#!/bin/dash\necho $_"));
    }
    #[test]
    fn prop_checkBashisms97() {
        assert!(emits(bashism, "#!/bin/sh\necho ${var,}"));
    }
    #[test]
    fn prop_checkBashisms98() {
        assert!(emits(bashism, "#!/bin/sh\necho ${var^^}"));
    }
    #[test]
    fn prop_checkBashisms99() {
        assert!(emits(bashism, "#!/bin/dash\necho [^f]oo"));
    }
    #[test]
    fn prop_checkBashisms100() {
        assert!(emits(bashism, "read -r"));
    }
    #[test]
    fn prop_checkBashisms101() {
        assert!(emits(bashism, "read"));
    }
    #[test]
    fn prop_checkBashisms102() {
        assert!(!emits(bashism, "read -r foo"));
    }
    #[test]
    fn prop_checkBashisms103() {
        assert!(!emits(bashism, "read foo"));
    }
    #[test]
    fn prop_checkBashisms104() {
        assert!(!emits(bashism, "read ''"));
    }
    #[test]
    fn prop_checkBashisms105() {
        assert!(!emits(bashism, "#!/bin/busybox sh\nset -o pipefail"));
    }
    #[test]
    fn prop_checkBashisms106() {
        assert!(!emits(
            bashism,
            "#!/bin/busybox sh\nx=x\n[[ \"$x\" = \"$x\" ]]"
        ));
    }
    #[test]
    fn prop_checkBashisms107() {
        assert!(!emits(
            bashism,
            "#!/bin/busybox sh\nx=x\n[ \"$x\" == \"$x\" ]"
        ));
    }
    #[test]
    fn prop_checkBashisms108() {
        assert!(!emits(
            bashism,
            "#!/bin/busybox sh\necho magic &> /dev/null"
        ));
    }
    #[test]
    fn prop_checkBashisms109() {
        assert!(!emits(bashism, "#!/bin/busybox sh\ntrap stop EXIT SIGTERM"));
    }
    #[test]
    fn prop_checkBashisms110() {
        assert!(!emits(bashism, "#!/bin/busybox sh\nsource /dev/null"));
    }
    #[test]
    fn prop_checkBashisms111() {
        assert!(emits(bashism, "#!/bin/dash\nx='test'\n${x:0:3}"));
    }
    #[test]
    fn prop_checkBashisms112() {
        assert!(!emits(bashism, "#!/bin/busybox sh\nx='test'\n${x:0:3}"));
    }
    #[test]
    fn prop_checkBashisms113() {
        assert!(emits(bashism, "#!/bin/dash\nx='test'\n${x/st/xt}"));
    }
    #[test]
    fn prop_checkBashisms114() {
        assert!(!emits(bashism, "#!/bin/busybox sh\nx='test'\n${x/st/xt}"));
    }
    #[test]
    fn prop_checkBashisms115() {
        assert!(emits(bashism, "#!/bin/busybox sh\nx='test'\n${!x}"));
    }
    #[test]
    fn prop_checkBashisms116() {
        assert!(emits(bashism, "#!/bin/busybox sh\nx='test'\n${x[1]}"));
    }
    #[test]
    fn prop_checkBashisms117() {
        assert!(emits(bashism, "#!/bin/busybox sh\nx='test'\n${!x[@]}"));
    }
    #[test]
    fn prop_checkBashisms118() {
        assert!(emits(bashism, "#!/bin/busybox sh\nxyz=1\n${!x*}"));
    }
    #[test]
    fn prop_checkBashisms119() {
        assert!(emits(bashism, "#!/bin/busybox sh\nx='test'\n${x^^[t]}"));
    }
    #[test]
    fn prop_checkBashisms120() {
        assert!(emits(bashism, "#!/bin/sh\n[ x == y ]"));
    }
    #[test]
    fn prop_checkBashisms121() {
        assert!(!emits(
            bashism,
            "#!/bin/sh\n# shellcheck shell=busybox\n[ x == y ]"
        ));
    }
    #[test]
    fn prop_checkBashisms122() {
        assert!(!emits(bashism, "#!/bin/dash\n$'a'"));
    }
    #[test]
    fn prop_checkBashisms123() {
        assert!(!emits(bashism, "#!/bin/busybox sh\n$'a'"));
    }
    #[test]
    fn prop_checkBashisms124() {
        assert!(emits(bashism, "#!/bin/dash\ntype -p test"));
    }
    #[test]
    fn prop_checkBashisms125() {
        assert!(!emits(bashism, "#!/bin/busybox sh\ntype -p test"));
    }
    #[test]
    fn prop_checkBashisms126() {
        assert!(!emits(bashism, "#!/bin/busybox sh\nread -p foo -r bar"));
    }
    #[test]
    fn prop_checkBashisms127() {
        assert!(!emits(bashism, "#!/bin/busybox sh\necho -ne foo"));
    }
    #[test]
    fn prop_checkBashisms128() {
        assert!(emits(bashism, "#!/bin/dash\ntype -p test"));
    }
    #[test]
    fn prop_checkBashisms129() {
        assert!(emits(bashism, "#!/bin/sh\n[ -k /tmp ]"));
    }
    #[test]
    fn prop_checkBashisms130() {
        assert!(!emits(bashism, "#!/bin/dash\ntest -k /tmp"));
    }
    #[test]
    fn prop_checkBashisms131() {
        assert!(emits(bashism, "#!/bin/sh\n[ -o errexit ]"));
    }
    #[test]
    fn prop_checkBashisms132() {
        assert!(emits(bashism, "echo $\"hello\""));
    }
    #[test]
    fn prop_checkBashisms133() {
        assert!(emits(bashism, "for ((;;)); do break; done"));
    }
    #[test]
    fn prop_checkBashisms134() {
        assert!(emits(bashism, "((var))"));
    }
    #[test]
    fn prop_checkBashisms135() {
        assert!(emits(bashism, "var=$[1 + 2]"));
    }
    #[test]
    fn prop_checkBashisms136() {
        assert!(emits(bashism, "select x; do :; done"));
    }
    #[test]
    fn prop_checkBashisms137a() {
        assert!(emits(bashism, "echo {a,b}"));
    }
    #[test]
    fn prop_checkBashisms137b() {
        assert!(emits(bashism, "echo {1..3}"));
    }
    #[test]
    fn prop_checkBashisms138() {
        assert!(emits(bashism, "[[ -z $var ]]"));
    }
    #[test]
    fn prop_checkBashisms139() {
        assert!(emits(bashism, "cat <<< foo"));
    }
    #[test]
    fn prop_checkBashisms140a() {
        assert!(emits(bashism, "[ a '<' b ]"));
    }
    #[test]
    fn prop_checkBashisms140b() {
        assert!(emits(bashism, "test a \\> b"));
    }
    #[test]
    fn prop_checkBashisms141() {
        assert!(emits(bashism, "echo $((2 ** 3))"));
    }
    #[test]
    fn prop_checkBashisms142() {
        assert!(emits(bashism, "make |& less"));
    }
    #[test]
    fn prop_checkBashisms143() {
        assert!(emits(bashism, "a=(foo bar)"));
    }
    #[test]
    fn prop_checkBashisms144() {
        assert!(emits(bashism, "coproc foo { :; }"));
    }
    #[test]
    fn prop_checkBashisms145a() {
        assert!(emits(bashism, "#!/bin/sh\nf() { local i=; }"));
    }
    #[test]
    fn prop_checkBashisms145b() {
        assert!(!emits(bashism, "#!/bin/dash\nf() { local i=; }"));
    }
    #[test]
    fn prop_checkBashisms146() {
        assert!(emits(bashism, "readarray < file"));
    }
    #[test]
    fn prop_checkBashisms147() {
        assert!(emits(bashism, "[ -R ref ]"));
    }
    #[test]
    fn prop_checkBashisms148() {
        assert!(emits(bashism, "[ -N file ]"));
    }
    #[test]
    fn prop_checkBashisms149() {
        assert!(emits(bashism, "[ -G file ]"));
    }
    #[test]
    fn prop_checkBashisms150() {
        assert!(emits(bashism, "[ -O file ]"));
    }

    // ---- checkBraceExpansionVars (SC2051 / SC2175) ----
    #[test]
    fn prop_checkBraceExpansionVars1() {
        assert!(emits(check_brace_expansion_vars, "echo {1..$n}"));
    }
    #[test]
    fn prop_checkBraceExpansionVars2() {
        assert!(!emits(check_brace_expansion_vars, "echo {1,3,$n}"));
    }
    #[test]
    fn prop_checkBraceExpansionVars3() {
        assert!(emits(
            check_brace_expansion_vars,
            "eval echo DSC{0001..$n}.jpg"
        ));
    }
    #[test]
    fn prop_checkBraceExpansionVars4() {
        assert!(emits(check_brace_expansion_vars, "echo {$i..100}"));
    }

    // ---- checkMultiDimensionalArrays (SC2180) ----
    #[test]
    fn prop_checkMultiDimensionalArrays1() {
        assert!(emits(check_multi_dimensional_arrays, "foo[a][b]=3"));
    }
    #[test]
    fn prop_checkMultiDimensionalArrays2() {
        assert!(!emits(check_multi_dimensional_arrays, "foo[a]=3"));
    }
    #[test]
    fn prop_checkMultiDimensionalArrays3() {
        assert!(emits(check_multi_dimensional_arrays, "foo=( [a][b]=c )"));
    }
    #[test]
    fn prop_checkMultiDimensionalArrays4() {
        assert!(!emits(check_multi_dimensional_arrays, "foo=( [a]=c )"));
    }
    #[test]
    fn prop_checkMultiDimensionalArrays5() {
        assert!(emits(
            check_multi_dimensional_arrays,
            "echo ${foo[bar][baz]}"
        ));
    }
    #[test]
    fn prop_checkMultiDimensionalArrays6() {
        assert!(!emits(check_multi_dimensional_arrays, "echo ${foo[bar]}"));
    }

    // ---- checkBangAfterPipe (SC2326) ----
    #[test]
    fn prop_checkBangAfterPipe1() {
        assert!(emits(check_bang_after_pipe, "true | ! true"));
    }
    #[test]
    fn prop_checkBangAfterPipe2() {
        assert!(!emits(check_bang_after_pipe, "true | ( ! true )"));
    }
    #[test]
    fn prop_checkBangAfterPipe3() {
        assert!(!emits(check_bang_after_pipe, "! ! true | true"));
    }

    // ---- checkNegatedUnaryOps (SC2332) ----
    #[test]
    fn prop_checkNegatedUnaryOps1() {
        assert!(emits(check_negated_unary_ops, "[ ! -o braceexpand ]"));
    }
    #[test]
    fn prop_checkNegatedUnaryOps2() {
        assert!(!emits(check_negated_unary_ops, "[ -o braceexpand ]"));
    }
    #[test]
    fn prop_checkNegatedUnaryOps3() {
        assert!(!emits(check_negated_unary_ops, "[[ ! -o braceexpand ]]"));
    }
    #[test]
    fn prop_checkNegatedUnaryOps4() {
        assert!(!emits(check_negated_unary_ops, "! [ -o braceexpand ]"));
    }
    #[test]
    fn prop_checkNegatedUnaryOps5() {
        assert!(emits(check_negated_unary_ops, "[ ! -a file ]"));
    }
}
