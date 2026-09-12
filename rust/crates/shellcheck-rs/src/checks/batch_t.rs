//! Ported check batch t. See rust/PORTING.md.
//!
//! Per-command / assignment checks ported faithfully from
//! `ShellCheck.Checks.Commands`. Each check is self-contained: it performs the
//! `checkCommand` dispatch (Exactly / Basename, with the `builtin` and `/path`
//! special cases) inline, mirroring `ShellCheck.Checks.Commands.checkCommand`,
//! so the module does not need a shared dispatcher and each function is
//! independently testable.
//!
//!   * SC2003 / SC2304 / SC2305 / SC2306 / SC2307 / SC2308 — checkExpr
//!   * SC2151 / SC2152 — checkReturn
//!   * SC2241 / SC2242 — checkExit
//!   * SC2121 — checkSetAssignment
//!   * SC2163 — checkExportedExpansions
//!   * SC2142 — checkAliasesUsesArgs
//!   * SC2139 — checkAliasesExpandEarly
//!   * SC2184 — checkUnsetGlobs
//!   * SC2168 — checkLocalScope
//!   * SC2155 — checkMaskedReturns
//!   * SC2182 / SC2183 / SC2059 — checkPrintfVar
//!   * SC2029 — checkSshCommandString
//!   * SC2291 — checkUnquotedEchoSpaces
//!   * SC2293 / SC2294 — checkEvalArray
//!   * SC2224 / SC2225 / SC2226 — checkMv/Cp/LnArguments (missingDestination)
//!   * SC2232 — checkSudoArgs
//!   * SC2290 — checkArgComparison
//!   * SC2316 — checkMultipleDeclaring
//!   * SC2318 — checkBackreferencingDeclaration
//!   * SC2024 — checkSudoRedirect
//!   * SC2213 / SC2214 / SC2220 — checkWhileGetoptsCase
//!   * SC2229 / SC2313 — checkReadExpansions
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::is_true_assignment_source;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::basename;
use crate::astlib::e4m;
use crate::astlib::get_literal_string_def;
use crate::astlib::get_word_parts;
use crate::astlib::is_constant;
use crate::astlib::is_glob;
use crate::astlib::is_literal;
use crate::astlib::oversimplify_concat;
use crate::cfg::may_become_multiple_args;
use crate::cfg::will_become_multiple_args;
use crate::cfg::{
    get_braced_modifier, get_braced_reference, get_bsd_opts, get_gnu_opts, get_unquoted_literal,
    is_variable_name,
};
use crate::interface::{Code, Shell};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

pub fn register(c: &mut Checker) {
    c.node(check_expr);
    c.node(check_return);
    c.node(check_exit);
    c.node(check_set_assignment);
    c.node(check_exported_expansions);
    c.node(check_aliases_uses_args);
    c.node(check_aliases_expand_early);
    c.node(check_unset_globs);
    c.node(check_local_scope);
    c.node(check_masked_returns);
    c.node(check_printf_var);
    c.node(check_ssh_command_string);
    c.node(check_unquoted_echo_spaces);
    c.node(check_eval_array);
    c.node(check_mv_arguments);
    c.node(check_cp_arguments);
    c.node(check_ln_arguments);
    c.node(check_sudo_args);
    c.node(check_sudo_redirect);
    c.node(check_arg_comparison);
    c.node(check_multiple_declaring);
    c.node(check_backreferencing_declaration);
    c.node(check_while_getopts_case);
    c.node(check_read_expansions);
}

// ===========================================================================
// Shared local helpers (ported from ASTLib / AnalyzerLib; kept private so this
// module does not touch shared files that parallel agents also edit).
// ===========================================================================

const DECLARING_COMMANDS: [&str; 6] = ["local", "declare", "export", "readonly", "typeset", "let"];
const PRIVILEGE_ELEVATION_COMMANDS: [&str; 3] = ["sudo", "doas", "run0"];

/// `willSplit`.
fn will_split(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => true,
        T_DollarExpansion(_) => true,
        T_Backticked(_) => true,
        T_BraceExpansion(_) => true,
        T_Glob(_) => true,
        T_Extglob { .. } => true,
        T_DoubleQuoted(l) => l.iter().any(will_become_multiple_args),
        T_NormalWord(l) => l.iter().any(will_split),
        _ => false,
    }
}

/// `isFunctionLike`.
fn is_function_like(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_Function { .. } | InnerToken::T_BatsTest { .. }
    )
}

// ---- checkCommand dispatch -------------------------------------------------

/// Effective command token if a check registered under `Exactly target` would
/// fire on `t`, per `checkCommand`.
fn dispatch_exactly(t: &Token, target: &str) -> Option<Token> {
    let (assignments, words) = match &*t.inner {
        InnerToken::T_SimpleCommand { assignments, words } if !words.is_empty() => {
            (assignments, words)
        }
        _ => return None,
    };
    let name = astlib::get_literal_string(&words[0])?;
    if name.contains('/') {
        return None; // slash -> only Basename dispatch
    }
    if name == "builtin" && words.len() >= 2 {
        let selected = astlib::only_literal_string(&words[1]);
        if selected == target {
            return Some(Token::new(
                t.id(),
                InnerToken::T_SimpleCommand {
                    assignments: assignments.clone(),
                    words: words[1..].to_vec(),
                },
            ));
        }
        return None;
    }
    if name == target {
        Some(t.clone())
    } else {
        None
    }
}

/// Like `dispatch_exactly` but matches any of the given names.
fn dispatch_exactly_any(t: &Token, targets: &[&str]) -> Option<Token> {
    for name in targets {
        if let Some(te) = dispatch_exactly(t, name) {
            return Some(te);
        }
    }
    None
}

/// Effective command token if a check registered under `Basename target` would
/// fire on `t`, per `checkCommand`.
fn dispatch_basename(t: &Token, target: &str) -> Option<Token> {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return None,
    };
    let name = astlib::get_literal_string(&words[0])?;
    if name.contains('/') {
        return if basename(&name) == target {
            Some(t.clone())
        } else {
            None
        };
    }
    if name == "builtin" && words.len() >= 2 {
        return None; // builtin branch: no Basename dispatch
    }
    if name == target {
        Some(t.clone())
    } else {
        None
    }
}

// ===========================================================================
// SC2003 / SC2304 / SC2305 / SC2306 / SC2307 / SC2308 — checkExpr
// ===========================================================================

const EXPR_EXCEPTIONS: [&str; 9] = [
    ":", "<", ">", "<=", ">=", "match", "length", "substr", "index",
];

fn expr_check_op(side: &Token, out: &mut Out) {
    if let Some(s) = astlib::get_literal_string(side) {
        let msg = match s.as_str() {
            "match" => "'expr match' has unspecified results. Prefer 'expr str : regex'.",
            "length" => "'expr length' has unspecified results. Prefer ${#var}.",
            "substr" => "'expr substr' has unspecified results. Prefer 'cut' or ${var#???}.",
            "index" => {
                "'expr index' has unspecified results. Prefer x=${var%%[chars]*}; $((${#x}+1))."
            }
            _ => return,
        };
        info(out, side.id(), 2308, msg);
    }
}

fn check_expr(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_basename(t, "expr") {
        Some(x) => x,
        None => return,
    };
    let args = arguments(&te);

    let literal_args: Vec<String> = args.iter().filter_map(astlib::get_literal_string).collect();
    if literal_args
        .iter()
        .all(|x| !EXPR_EXCEPTIONS.contains(&x.as_str()))
    {
        style(
            out,
            get_command_token_or_this(&te).id(),
            2003,
            "expr is antiquated. Consider rewriting this using $((..)), ${} or [[ ]].",
        );
    }

    match args {
        [lhs, op, rhs] => {
            expr_check_op(lhs, out);
            let wp = get_word_parts(op);
            if wp.len() == 1 {
                match &*wp[0].inner {
                    InnerToken::T_Glob(g) if g == "*" => err(
                        out,
                        op.id(),
                        2304,
                        "* must be escaped to multiply: \\*. Modern $((x * y)) avoids this issue.",
                    ),
                    InnerToken::T_Literal(s) if s == ":" && is_glob(rhs) => {
                        warn(
                            out,
                            rhs.id(),
                            2305,
                            "Quote regex argument to expr to avoid it expanding as a glob.",
                        );
                    }
                    _ => {}
                }
            }
        }
        [single] if !will_split(single) => {
            warn(
                out,
                single.id(),
                2307,
                "'expr' expects 3+ arguments but sees 1. Make sure each operator/operand is a separate argument, and escape <>&|.",
            );
        }
        [first, second]
            if astlib::only_literal_string(first) != "length"
                && !(will_split(first) || will_split(second)) =>
        {
            expr_check_op(first, out);
            warn(
                out,
                te.id(),
                2307,
                "'expr' expects 3+ arguments, but sees 2. Make sure each operator/operand is a separate argument, and escape <>&|.",
            );
        }
        _ => {
            if let Some((first, rest)) = args.split_first() {
                expr_check_op(first, out);
                for r in rest {
                    if is_glob(r) {
                        warn(
                            out,
                            r.id(),
                            2306,
                            "Escape glob characters in arguments to expr to avoid pathname expansion.",
                        );
                    }
                }
            }
        }
    }
}

// ===========================================================================
// SC2151 / SC2152 — checkReturn   &   SC2241 / SC2242 — checkExit
// ===========================================================================

fn return_lit(value: &Token) -> String {
    astlib::get_literal_string_ext(value, &|inner| {
        Some(
            match inner {
                InnerToken::T_DollarBraced { .. }
                | InnerToken::T_DollarArithmetic(_)
                | InnerToken::T_DollarExpansion(_)
                | InnerToken::T_Backticked(_) => "0",
                _ => "WTF",
            }
            .to_string(),
        )
    })
    .unwrap_or_default()
}

fn return_is_invalid(s: &str) -> bool {
    s.is_empty()
        || s.chars().any(|c| !c.is_ascii_digit())
        || s.chars().count() > 5
        || s.parse::<u64>().is_ok_and(|v| v > 255)
}

fn return_or_exit(args: &[Token], out: &mut Out, multi: (Code, &str), invalid: (Code, &str)) {
    match args {
        [first, _second, ..] => err(out, first.id(), multi.0, multi.1),
        [value] if return_is_invalid(&return_lit(value)) => {
            err(out, value.id(), invalid.0, invalid.1);
        }
        _ => {}
    }
}

fn check_return(_params: &Parameters, t: &Token, out: &mut Out) {
    if let Some(te) = dispatch_exactly(t, "return") {
        return_or_exit(
            arguments(&te),
            out,
            (
                2151,
                "Only one integer 0-255 can be returned. Use stdout for other data.",
            ),
            (
                2152,
                "Can only return 0-255. Other data should be written to stdout.",
            ),
        );
    }
}

fn check_exit(_params: &Parameters, t: &Token, out: &mut Out) {
    if let Some(te) = dispatch_exactly(t, "exit") {
        return_or_exit(
            arguments(&te),
            out,
            (
                2241,
                "The exit status can only be one integer 0-255. Use stdout for other data.",
            ),
            (
                2242,
                "Can only exit with status 0-255. Other data should be written to stdout/stderr.",
            ),
        );
    }
}

// ===========================================================================
// SC2121 — checkSetAssignment
// ===========================================================================

fn set_literal(t: &Token) -> String {
    match &*t.inner {
        InnerToken::T_NormalWord(l) => l.iter().map(set_literal).collect(),
        InnerToken::T_Literal(s) => s.clone(),
        _ => "*".to_string(),
    }
}

fn check_set_assignment(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "set") {
        Some(x) => x,
        None => return,
    };
    let args = arguments(&te);
    if let Some((var, rest)) = args.split_first() {
        let str = set_literal(var);
        if (!rest.is_empty() && is_variable_name(&str)) || str.contains('=') {
            warn(
                out,
                var.id(),
                2121,
                "To assign a variable, use just 'var=value', no 'set ..'.",
            );
        }
    }
}

// ===========================================================================
// SC2163 — checkExportedExpansions
// ===========================================================================

/// `getSingleUnmodifiedBracedString`.
fn get_single_unmodified_braced_string(word: &Token) -> Option<String> {
    let parts = get_word_parts(word);
    if parts.len() == 1 {
        if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
            let contents = oversimplify_concat(op);
            let name = get_braced_reference(&contents);
            if contents == name {
                return Some(contents);
            }
        }
    }
    None
}

fn check_exported_expansions(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "export") {
        Some(x) => x,
        None => return,
    };
    for arg in arguments(&te) {
        if let Some(name) = get_single_unmodified_braced_string(arg) {
            warn(
                out,
                arg.id(),
                2163,
                &format!(
                    "This does not export '{}'. Remove $/${{}} for that, or use ${{var?}} to quiet.",
                    name
                ),
            );
        }
    }
}

// ===========================================================================
// SC2142 — checkAliasesUsesArgs
// ===========================================================================

/// The regex `\$\{?[0-9*@]`.
fn matches_positional_ref(s: &str) -> bool {
    let b: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < b.len() {
        if b[i] == '$' {
            let mut j = i + 1;
            if j < b.len() && b[j] == '{' {
                j += 1;
            }
            if j < b.len() && (b[j].is_ascii_digit() || b[j] == '*' || b[j] == '@') {
                return true;
            }
        }
        i += 1;
    }
    false
}

fn check_aliases_uses_args(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "alias") {
        Some(x) => x,
        None => return,
    };
    for arg in arguments(&te) {
        let string = get_literal_string_def("_", arg);
        if string.contains('=') && matches_positional_ref(&string) {
            err(
                out,
                arg.id(),
                2142,
                "Aliases can't use positional parameters. Use a function.",
            );
        }
    }
}

// ===========================================================================
// SC2139 — checkAliasesExpandEarly
// ===========================================================================

fn check_aliases_expand_early(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "alias") {
        Some(x) => x,
        None => return,
    };
    for arg in arguments(&te) {
        if oversimplify_concat(arg).contains('=') {
            if let Some(x) = get_word_parts(arg).into_iter().find(|p| !is_literal(p)) {
                warn(
                    out,
                    x.id(),
                    2139,
                    "This expands when defined, not when used. Consider escaping.",
                );
            }
        }
    }
}

// ===========================================================================
// SC2184 — checkUnsetGlobs
// ===========================================================================

fn check_unset_globs(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "unset") {
        Some(x) => x,
        None => return,
    };
    for arg in arguments(&te) {
        if is_glob(arg) {
            warn(
                out,
                arg.id(),
                2184,
                "Quote arguments to unset so they're not glob expanded.",
            );
        }
    }
}

// ===========================================================================
// SC2168 — checkLocalScope
// ===========================================================================

fn check_local_scope(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "local") {
        Some(x) => x,
        None => return,
    };
    // whenShell [Bash, Dash, BusyboxSh]
    if !matches!(params.shell, Shell::Bash | Shell::Dash | Shell::BusyboxSh) {
        return;
    }
    let path = get_path(params, &te);
    if !path.iter().any(is_function_like) {
        err(
            out,
            get_command_token_or_this(&te).id(),
            2168,
            "'local' is only valid in functions.",
        );
    }
}

// ===========================================================================
// SC2155 — checkMaskedReturns
// ===========================================================================

fn masked_has_return(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_Backticked(_)
            | InnerToken::T_DollarExpansion(_)
            | InnerToken::T_DollarBraceCommandExpansion { .. }
    )
}

fn is_scoped_function(shell: Shell, t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_BatsTest { .. } => true,
        // In ksh, only functions declared with 'function' have their own scope.
        InnerToken::T_Function { keyword, .. } => shell != Shell::Ksh || *keyword,
        _ => false,
    }
}

fn check_masked_returns(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly_any(t, &DECLARING_COMMANDS) {
        Some(x) => x,
        None => return,
    };
    let name = match get_command_name(&te) {
        Some(n) => n,
        None => return,
    };
    let path = get_path(params, &te);
    let shell = params.shell;

    let flags: Vec<String> = get_all_flags(&te).into_iter().map(|(_, s)| s).collect();
    let has_dash_r = flags.iter().any(|f| f == "r");
    let has_dash_g = flags.iter().any(|f| f == "g");
    let is_in_scoped_function = path.iter().any(|x| is_scoped_function(shell, x));

    let is_local_in_function = matches!(name.as_str(), "local" | "declare" | "typeset");
    let is_local = !has_dash_g && is_local_in_function && is_in_scoped_function;
    let is_read_only = name == "readonly" || has_dash_r;

    // Don't warn about local variables declared readonly.
    if is_local && is_read_only {
        return;
    }

    for a in arguments(&te) {
        if let InnerToken::T_Assignment { value, .. } = &*a.inner {
            if get_word_parts(value).iter().any(|x| masked_has_return(x)) {
                warn(
                    out,
                    a.id(),
                    2155,
                    "Declare and assign separately to avoid masking return values.",
                );
            }
        }
    }
}

// ===========================================================================
// SC2182 / SC2183 / SC2059 — checkPrintfVar
// ===========================================================================

fn check_printf_var(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "printf") {
        Some(x) => x,
        None => return,
    };
    // f: skip leading `--`, `-v var`, `-vVAR`.
    let mut rest = arguments(&te);
    loop {
        let first = match rest.first() {
            Some(f) => f,
            None => return,
        };
        let s = astlib::get_literal_string(first);
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
        printf_check(first, &rest[1..], out);
        return;
    }
}

/// `check format more`.
fn printf_check(format: &Token, more: &[Token], out: &mut Out) {
    if let Some(string) = astlib::get_literal_string(format) {
        let formats = get_printf_formats(&string);
        let format_count = formats.chars().count();
        let arg_count = more.len();
        let pluralise = |word: &str, n: usize| {
            if n == 1 {
                word.to_string()
            } else {
                format!("{}s", word)
            }
        };
        if arg_count == 0 && format_count == 0 {
            // This is fine
        } else if format_count == 0 && arg_count > 0 {
            err(
                out,
                format.id(),
                2182,
                "This printf format string has no variables. Other arguments are ignored.",
            );
        } else if more.iter().any(may_become_multiple_args) {
            // We don't know so trust the user
        } else if arg_count < format_count && printf_only_trailing_ts(&formats, arg_count) {
            // Allow trailing %()Ts since they use the current time
        } else if arg_count > 0 && arg_count % format_count == 0 {
            // Great: a suitable number of arguments
        } else {
            warn(
                out,
                format.id(),
                2183,
                &format!(
                    "This format string has {} {}, but is passed {}{}.",
                    format_count,
                    pluralise("variable", format_count),
                    arg_count,
                    pluralise(" argument", arg_count)
                ),
            );
        }
    }
    if !(oversimplify_concat(format).contains('%') || is_literal(format)) {
        info(
            out,
            format.id(),
            2059,
            "Don't use variables in the printf format string. Use printf '..%s..' \"$foo\".",
        );
    }
}

fn printf_only_trailing_ts(formats: &str, arg_count: usize) -> bool {
    formats.chars().skip(arg_count).all(|c| c == 'T')
}

// ===========================================================================
// SC2029 — checkSshCommandString
// ===========================================================================

fn ssh_is_option(x: &Token) -> bool {
    oversimplify_concat(x).starts_with('-')
}

fn check_ssh_command_string(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_basename(t, "ssh") {
        Some(x) => x,
        None => return,
    };
    let args = arguments(&te);
    let options: Vec<&Token> = args.iter().filter(|x| ssh_is_option(x)).collect();
    let non_options: Vec<&Token> = args.iter().filter(|x| !ssh_is_option(x)).collect();
    // ([], hostport:r@(_:_))
    if !options.is_empty() || non_options.len() < 2 {
        return;
    }
    let last = *non_options.last().unwrap();
    // checkArg (T_NormalWord _ [T_DoubleQuoted id parts])
    if let InnerToken::T_NormalWord(l) = &*last.inner {
        if l.len() == 1 {
            if let InnerToken::T_DoubleQuoted(parts) = &*l[0].inner {
                if let Some(x) = parts.iter().find(|p| !is_constant(p)) {
                    info(
                        out,
                        x.id(),
                        2029,
                        "Note that, unescaped, this expands on the client side.",
                    );
                }
            }
        }
    }
}

// ===========================================================================
// SC2291 — checkUnquotedEchoSpaces
// ===========================================================================

fn check_unquoted_echo_spaces(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_basename(t, "echo") {
        Some(x) => x,
        None => return,
    };
    let args = arguments(&te);
    let m = &params.token_positions;

    let positions: Vec<(crate::interface::Position, crate::interface::Position)> = args
        .iter()
        .filter_map(|c| m.get(&c.id()).cloned())
        .collect();
    if positions.len() < 2 {
        return;
    }

    let redir = match get_closest_command(params, t) {
        Some(r) => r,
        None => return,
    };
    let redir_tokens = match &*redir.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs,
        _ => return,
    };
    let redir_positions: Vec<crate::interface::Position> = redir_tokens
        .iter()
        .filter_map(|c| m.get(&c.id()).map(|(s, _)| s.clone()))
        .collect();

    let has_spaces_between = |first: &(crate::interface::Position, crate::interface::Position),
                              second: &(crate::interface::Position, crate::interface::Position)|
     -> bool {
        let (a, b) = first;
        let (c, d) = second;
        a.line == d.line
            && (c.column - b.column) >= 4
            && !redir_positions.iter().any(|x| b < x && x < c)
    };

    let fires = positions
        .windows(2)
        .any(|w| has_spaces_between(&w[0], &w[1]));
    if fires {
        info(
            out,
            t.id(),
            2291,
            "Quote repeated spaces to avoid them collapsing into one.",
        );
    }
}

// ===========================================================================
// SC2293 / SC2294 — checkEvalArray
// ===========================================================================

fn eval_is_escaped(q: &Token) -> bool {
    match &*q.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            get_braced_modifier(&oversimplify_concat(op)).contains('Q')
        }
        _ => false,
    }
}

fn check_eval_array(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "eval") {
        Some(x) => x,
        None => return,
    };
    for arg in arguments(&te) {
        for part in get_word_parts(arg) {
            if is_array_expansion(part) {
                if eval_is_escaped(part) {
                    style(
                        out,
                        part.id(),
                        2293,
                        "When eval'ing @Q-quoted words, use * rather than @ as the index.",
                    );
                } else {
                    warn(
                        out,
                        part.id(),
                        2294,
                        "eval negates the benefit of arrays. Drop eval to preserve whitespace/symbols (or eval as string).",
                    );
                }
            }
        }
    }
}

// ===========================================================================
// SC2224 / SC2225 / SC2226 — checkMv/Cp/LnArguments (missingDestination)
// ===========================================================================

fn missing_destination(te: &Token, out: &mut Out, handler: impl Fn(&mut Out, Id)) {
    let args = get_all_flags(te);
    let params_ops: Vec<&(&Token, String)> = args.iter().filter(|(_, x)| x.is_empty()).collect();
    let has_target = args
        .iter()
        .any(|(_, x)| !x.is_empty() && "target-directory".starts_with(x.as_str()));
    if params_ops.len() == 1 {
        let single: &Token = params_ops[0].0;
        if !(has_target || may_become_multiple_args(single)) {
            handler(out, te.id());
        }
    }
}

fn check_mv_arguments(_params: &Parameters, t: &Token, out: &mut Out) {
    if let Some(te) = dispatch_basename(t, "mv") {
        missing_destination(&te, out, |o, id| {
            err(
                o,
                id,
                2224,
                "This mv has no destination. Check the arguments.",
            );
        });
    }
}
fn check_cp_arguments(_params: &Parameters, t: &Token, out: &mut Out) {
    if let Some(te) = dispatch_basename(t, "cp") {
        missing_destination(&te, out, |o, id| {
            err(
                o,
                id,
                2225,
                "This cp has no destination. Check the arguments.",
            );
        });
    }
}
fn check_ln_arguments(_params: &Parameters, t: &Token, out: &mut Out) {
    if let Some(te) = dispatch_basename(t, "ln") {
        missing_destination(&te, out, |o, id| {
            warn(
                o,
                id,
                2226,
                "This ln has no destination. Check the arguments, or specify '.' explicitly.",
            );
        });
    }
}

// ===========================================================================
// SC2232 — checkSudoArgs
// ===========================================================================

const SUDO_BUILTINS: [&str; 25] = [
    "cd", "command", "declare", "eval", "exec", "exit", "export", "hash", "history", "local",
    "popd", "pushd", "read", "readonly", "return", "set", "source", "trap", "type", "typeset",
    "ulimit", "umask", "unset", "wait", "builtin",
];

fn check_sudo_args(_params: &Parameters, t: &Token, out: &mut Out) {
    let found_te = {
        let mut found = None;
        for cmd in PRIVILEGE_ELEVATION_COMMANDS {
            if let Some(x) = dispatch_basename(t, cmd) {
                found = Some(x);
                break;
            }
        }
        found
    };
    let te = match found_te {
        Some(x) => x,
        None => return,
    };
    let opts = match get_bsd_opts("vAknSbEHPa:g:h:p:u:c:T:r:", arguments(&te)) {
        Some(o) => o,
        None => return,
    };
    // find (null . fst) opts  -> first operand
    if let Some((_, (command_arg, _))) = opts.iter().find(|(name, _)| name.is_empty()) {
        if let Some(command) = astlib::get_literal_string(command_arg) {
            if SUDO_BUILTINS.contains(&command.as_str()) {
                warn(
                    out,
                    te.id(),
                    2232,
                    &format!(
                        "Can't use sudo/doas/run0 with builtins like {}. Did you want sudo/doas/run0 sh -c .. instead?",
                        command
                    ),
                );
            }
        }
    }
}

// ===========================================================================
// SC2024 — checkSudoRedirect
// ===========================================================================

/// `checkSudoRedirect cmd` for each of `privilegeElevationCommands`: a
/// redirect on the enclosing `T_Redirecting` applies to the shell, not the
/// elevated command.
fn check_sudo_redirect(params: &Parameters, t: &Token, out: &mut Out) {
    if !PRIVILEGE_ELEVATION_COMMANDS
        .iter()
        .any(|cmd| dispatch_basename(t, cmd).is_some())
    {
        return;
    }
    let Some(t_redir) = get_closest_command(params, t) else {
        return;
    };
    if let InnerToken::T_Redirecting { redirs, .. } = &*t_redir.inner {
        for redir in redirs {
            sudo_redirect_warn_about(redir, out);
        }
    }
}

fn sudo_redirect_warn_about(redir: &Token, out: &mut Out) {
    use InnerToken::*;
    let T_FdRedirect { fd, target } = &*redir.inner else {
        return;
    };
    let T_IoFile { op, file } = &*target.inner else {
        return;
    };
    // special file = concat (oversimplify file) == "/dev/null"
    if !(fd.is_empty() || fd == "&") || oversimplify_concat(file) == "/dev/null" {
        return;
    }
    match &*op.inner {
        T_Less => info(
            out,
            op.id(),
            2024,
            "sudo/doas/run0 doesn't affect redirects. Use sudo cat file | ..",
        ),
        T_Greater => warn(
            out,
            op.id(),
            2024,
            "sudo/doas/run0 doesn't affect redirects. Use ..| sudo tee file",
        ),
        T_DGREAT => warn(
            out,
            op.id(),
            2024,
            "sudo/doas/run0 doesn't affect redirects. Use .. | sudo tee -a file",
        ),
        _ => {}
    }
}

// ===========================================================================
// SC2290 — checkArgComparison
// ===========================================================================

/// `map checkArgComparison ("alias" : declaringCommands)`.
fn check_arg_comparison(_params: &Parameters, t: &Token, out: &mut Out) {
    let targets = [
        "alias", "local", "declare", "export", "readonly", "typeset", "let",
    ];
    let te = match dispatch_exactly_any(t, &targets) {
        Some(x) => x,
        None => return,
    };
    for arg in arguments(&te) {
        let Some(s) = astlib::get_leading_unquoted_string(arg) else {
            continue;
        };
        if s.starts_with('=') {
            err(out, head_id(arg), 2290, "Remove spaces around = to assign.");
        } else if s.starts_with("+=") {
            err(
                out,
                head_id(arg),
                2290,
                "Remove spaces around += to append.",
            );
        }
    }
}

// ===========================================================================
// SC2316 — checkMultipleDeclaring
// ===========================================================================

/// `map checkMultipleDeclaring declaringCommands`.
fn check_multiple_declaring(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly_any(t, &DECLARING_COMMANDS) {
        Some(x) => x,
        None => return,
    };
    let Some(cmd) = get_command_name(&te) else {
        return;
    };
    for arg in arguments(&te) {
        let Some(lit) = get_unquoted_literal(arg) else {
            continue;
        };
        if DECLARING_COMMANDS.contains(&lit.as_str()) {
            err(
                out,
                get_command_token_or_this(arg).id(),
                2316,
                &format!(
                    "This applies {} to the variable named {}, which is probably not what you want. Use a separate command or the appropriate `declare` options instead.",
                    cmd, lit
                ),
            );
        }
    }
}

// ===========================================================================
// SC2318 — checkBackreferencingDeclaration
// ===========================================================================

/// `map checkBackreferencingDeclaration declaringCommands`: an argument of a
/// declaring command that reads a variable assigned earlier in the same
/// command, where that assignment has not taken effect yet.
fn check_backreferencing_declaration(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly_any(t, &DECLARING_COMMANDS) {
        Some(x) => x,
        None => return,
    };
    let Some(cfga) = params.cfg_analysis.as_ref() else {
        return;
    };
    let Some(cmd) = get_command_name(&te) else {
        return;
    };
    // foldM_ (perArg cfga) M.empty (arguments t)
    let mut left_args: BTreeMap<String, Id> = BTreeMap::new();
    for arg in arguments(&te) {
        match &*arg.inner {
            InnerToken::T_Assignment {
                var,
                indices,
                value,
                ..
            } => {
                let mut l: Vec<&Token> = vec![value];
                l.extend(indices.iter());
                backref_warn(cfga, &left_args, &l, &cmd, out);
                left_args.insert(var.clone(), arg.id());
            }
            _ => backref_warn(cfga, &left_args, &[arg], &cmd, out),
        }
    }
}

/// `warnIfBackreferencing cfga backrefs l`.
fn backref_warn(
    cfga: &crate::cfg_analysis::CFGAnalysis,
    backrefs: &BTreeMap<String, Id>,
    list: &[&Token],
    cmd: &str,
    out: &mut Out,
) {
    // findReferences: every CFReadVariable effect on the CFG nodes of `list`.
    let mut nodes: BTreeSet<crate::cfg::Node> = BTreeSet::new();
    for t in list {
        if let Some(ns) = cfga.token_to_nodes.get(&t.id()) {
            nodes.extend(ns.iter().copied());
        }
    }
    let mut references: BTreeMap<String, Id> = BTreeMap::new();
    for n in nodes {
        if let Some(crate::cfg::CFNode::CFApplyEffects(effects)) = cfga.graph.lab(n) {
            for e in effects {
                if let crate::cfg::CFEffect::CFReadVariable(name) = &e.value {
                    references.insert(name.clone(), e.id);
                }
            }
        }
    }
    // M.intersection backrefs references: keys of both, values from backrefs.
    for (name, id) in backrefs {
        if references.contains_key(name) {
            warn(
                out,
                *id,
                2318,
                &format!(
                    "This assignment is used again in this '{}', but won't have taken effect. Use two '{}'s.",
                    cmd, cmd
                ),
            );
        }
    }
}

// ===========================================================================
// SC2213 / SC2214 / SC2220 — checkWhileGetoptsCase
// ===========================================================================

fn modifies_variable(params: &Parameters, token: &Token, name: &str) -> bool {
    let flow = get_variable_flow(
        &params.parent_map,
        &params.id_map,
        params.has_lastpipe,
        token,
    );
    flow.iter().any(|sd| match sd {
        StackData::Assignment(_, _, n, source) => is_true_assignment_source(source) && n == name,
        _ => false,
    })
}

/// `findCase`.
fn getopts_find_case(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Annotation { token, .. } => getopts_find_case(token),
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => {
            getopts_find_case(&commands[0])
        }
        InnerToken::T_Redirecting { cmd, .. } => {
            if matches!(&*cmd.inner, InnerToken::T_CaseExpression { .. }) {
                Some(cmd)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `literal` for a case glob: `getLiteralString t <> fromGlob t`.
fn getopts_case_literal(t: &Token) -> Option<String> {
    astlib::get_literal_string(t).or_else(|| getopts_from_glob(t))
}
fn getopts_from_glob(t: &Token) -> Option<String> {
    if let InnerToken::T_Glob(s) = &*t.inner {
        let cs: Vec<char> = s.chars().collect();
        if cs.len() == 3 && cs[0] == '[' && cs[2] == ']' {
            return Some(cs[1].to_string());
        }
        if s == "*" {
            return Some("*".to_string());
        }
        if s == "?" {
            return Some("?".to_string());
        }
    }
    None
}

fn check_while_getopts_case(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "getopts") {
        Some(x) => x,
        None => return,
    };
    // f t@(T_SimpleCommand _ _ (cmd:arg1:name:_))
    let words = match &*te.inner {
        InnerToken::T_SimpleCommand { words, .. } if words.len() >= 3 => words,
        _ => return,
    };
    let arg1 = &words[1];
    let name = &words[2];

    let options = match astlib::get_literal_string(arg1) {
        Some(o) => o,
        None => return,
    };
    let getopts_var = match astlib::get_literal_string(name) {
        Some(v) => v,
        None => return,
    };

    let path = get_path(params, &te);
    // findFirst whileLoop path
    let mut while_body: Option<&Vec<Token>> = None;
    for node in &path {
        match &*node.inner {
            InnerToken::T_WhileExpression { body, .. } => {
                while_body = Some(body);
                break;
            }
            InnerToken::T_Script { .. } => break,
            _ => {}
        }
    }
    let body = match while_body {
        Some(b) => b,
        None => return,
    };

    // mapMaybe findCase body !!! 0
    let case_tok = match body.iter().find_map(|s| getopts_find_case(s)) {
        Some(c) => c,
        None => return,
    };
    let (word, cases, case_id) = match &*case_tok.inner {
        InnerToken::T_CaseExpression { word, cases } => (word, cases, case_tok.id()),
        _ => return,
    };

    // [T_DollarBraced _ _ bracedWord] <- return $ getWordParts var
    let wp = get_word_parts(word);
    if wp.len() != 1 {
        return;
    }
    let braced_word = match &*wp[0].inner {
        InnerToken::T_DollarBraced { op, .. } => op,
        _ => return,
    };
    // [T_Literal _ caseVar] <- return $ getWordParts bracedWord
    let wp2 = get_word_parts(braced_word);
    if wp2.len() != 1 {
        return;
    }
    let case_var = match &*wp2[0].inner {
        InnerToken::T_Literal(s) => s.clone(),
        _ => return,
    };
    if case_var != getopts_var {
        return;
    }

    // guard . not $ modifiesVariable params (T_BraceGroup (Id 0) body) getoptsVar
    let brace_group = Token::new(Id(0), InnerToken::T_BraceGroup(body.clone()));
    if modifies_variable(params, &brace_group, &getopts_var) {
        return;
    }

    let opts: Vec<String> = options
        .chars()
        .filter(|c| *c != ':')
        .map(|c| c.to_string())
        .collect();
    getopts_check(&opts, case_id, cases, out);
}

fn getopts_check(opts: &[String], case_id: Id, cases: &[CaseClause], out: &mut Out) {
    // handledMap: key -> glob token (last wins, like M.fromList).
    let mut handled: HashMap<Option<String>, Token> = HashMap::new();
    for (_, globs, _) in cases {
        for g in globs {
            handled.insert(getopts_case_literal(g), g.clone());
        }
    }
    let requested: HashSet<Option<String>> = opts.iter().map(|o| Some(o.clone())).collect();

    // unless (Nothing `M.member` handledMap)
    if !handled.contains_key(&None) {
        // notHandled = requested - handled; catMaybes keys = requested opts not handled.
        let mut unhandled: Vec<String> = opts
            .iter()
            .filter(|o| !handled.contains_key(&Some((*o).clone())))
            .cloned()
            .collect();
        unhandled.sort();
        for str in &unhandled {
            warn(
                out,
                case_id,
                2213,
                &format!(
                    "getopts specified -{}, but it's not handled by this 'case'.",
                    e4m(str)
                ),
            );
        }
        if !(handled.contains_key(&Some("*".to_string()))
            || handled.contains_key(&Some("?".to_string())))
        {
            warn(
                out,
                case_id,
                2220,
                "Invalid flags are not handled. Add a *) case.",
            );
        }
    }

    // notRequested = handled - requested
    let mut redundant: Vec<(String, Token)> = vec![];
    for (key, expr) in &handled {
        if !requested.contains(key) {
            if let Some(str) = key {
                if !["*", ":", "?"].contains(&str.as_str()) {
                    redundant.push((str.clone(), expr.clone()));
                }
            }
        }
    }
    redundant.sort_by(|a, b| a.0.cmp(&b.0));
    for (_, expr) in redundant {
        warn(
            out,
            expr.id(),
            2214,
            "This case is not specified by getopts.",
        );
    }
}

// ===========================================================================
// SC2229 / SC2313 — checkReadExpansions
// ===========================================================================

fn read_is_unquoted_bracket(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Glob(s) if s.starts_with('['))
}

const FLAGS_FOR_READ: &str = "sreu:n:N:i:p:a:t:";

fn check_read_expansions(_params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, "read") {
        Some(x) => x,
        None => return,
    };
    let args = arguments(&te);
    // getVars: the option values for positional arguments and `-a`.
    if let Some(opts) = get_gnu_opts(FLAGS_FOR_READ, args) {
        for (x, (_, y)) in &opts {
            if x.is_empty() || x == "a" {
                // dollarWarning
                if let Some(name) = get_single_unmodified_braced_string(y) {
                    if is_variable_name(&name) {
                        warn(
                            out,
                            y.id(),
                            2229,
                            &format!(
                                "This does not read '{}'. Remove $/${{}} for that, or use ${{var?}} to quiet.",
                                name
                            ),
                        );
                    }
                }
            }
        }
    }
    // arrayWarning
    for word in args {
        if get_word_parts(word)
            .iter()
            .any(|p| read_is_unquoted_bracket(p))
        {
            warn(
                out,
                word.id(),
                2313,
                "Quote array indices to avoid them expanding as globs.",
            );
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }

    /// `verify`: run one check over every node, drop diagnostics disabled by an
    /// inline annotation (as the real pipeline does), and report whether any
    /// survive.
    fn produces(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.retain(|c| !is_ignored(&params, c.comment.code, c.id));
        !out.is_empty()
    }

    fn is_ignored(params: &Parameters, code: Code, id: Id) -> bool {
        let token = match params.id_map.get(&id) {
            Some(t) => t.clone(),
            None => return false,
        };
        get_path(params, &token).iter().any(|p| {
            if let InnerToken::T_Annotation { annotations, .. } = &*p.inner {
                annotations.iter().any(|a| match a {
                    Annotation::DisableComment(from, to) => code >= *from && code < *to,
                    _ => false,
                })
            } else {
                false
            }
        })
    }

    // checkExpr
    #[test]
    fn prop_checkExpr() {
        assert!(produces(check_expr, "foo=$(expr 3 + 2)"));
    }
    #[test]
    fn prop_checkExpr2() {
        assert!(produces(check_expr, "foo=`echo \\`expr 3 + 2\\``"));
    }
    #[test]
    fn prop_checkExpr3() {
        assert!(!produces(check_expr, "foo=$(expr foo : regex)"));
    }
    #[test]
    fn prop_checkExpr4() {
        assert!(!produces(check_expr, "foo=$(expr foo \\< regex)"));
    }
    #[test]
    fn prop_checkExpr5() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr match foo bar"
        ));
    }
    #[test]
    fn prop_checkExpr6() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr foo : fo*"
        ));
    }
    #[test]
    fn prop_checkExpr7() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr 5 -3"
        ));
    }
    #[test]
    fn prop_checkExpr8() {
        assert!(!produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr \"$@\""
        ));
    }
    #[test]
    fn prop_checkExpr9() {
        assert!(!produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr 5 $rest"
        ));
    }
    #[test]
    fn prop_checkExpr10() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr length \"$var\""
        ));
    }
    #[test]
    fn prop_checkExpr11() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr foo > bar"
        ));
    }
    #[test]
    fn prop_checkExpr12() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr 1 | 2"
        ));
    }
    #[test]
    fn prop_checkExpr13() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr 1 * 2"
        ));
    }
    #[test]
    fn prop_checkExpr14() {
        assert!(produces(
            check_expr,
            "# shellcheck disable=SC2003\nexpr \"$x\" >=  \"$y\""
        ));
    }

    // checkReturn
    #[test]
    fn prop_checkReturn1() {
        assert!(!produces(check_return, "return"));
    }
    #[test]
    fn prop_checkReturn2() {
        assert!(!produces(check_return, "return 1"));
    }
    #[test]
    fn prop_checkReturn3() {
        assert!(!produces(check_return, "return $var"));
    }
    #[test]
    fn prop_checkReturn4() {
        assert!(!produces(check_return, "return $((a|b))"));
    }
    #[test]
    fn prop_checkReturn5() {
        assert!(produces(check_return, "return -1"));
    }
    #[test]
    fn prop_checkReturn6() {
        assert!(produces(check_return, "return 1000"));
    }
    #[test]
    fn prop_checkReturn7() {
        assert!(produces(check_return, "return 'hello world'"));
    }

    // checkExit
    #[test]
    fn prop_checkExit1() {
        assert!(!produces(check_exit, "exit"));
    }
    #[test]
    fn prop_checkExit2() {
        assert!(!produces(check_exit, "exit 1"));
    }
    #[test]
    fn prop_checkExit3() {
        assert!(!produces(check_exit, "exit $var"));
    }
    #[test]
    fn prop_checkExit4() {
        assert!(!produces(check_exit, "exit $((a|b))"));
    }
    #[test]
    fn prop_checkExit5() {
        assert!(produces(check_exit, "exit -1"));
    }
    #[test]
    fn prop_checkExit6() {
        assert!(produces(check_exit, "exit 1000"));
    }
    #[test]
    fn prop_checkExit7() {
        assert!(produces(check_exit, "exit 'hello world'"));
    }

    // checkSetAssignment
    #[test]
    fn prop_checkSetAssignment1() {
        assert!(produces(check_set_assignment, "set foo 42"));
    }
    #[test]
    fn prop_checkSetAssignment2() {
        assert!(produces(check_set_assignment, "set foo = 42"));
    }
    #[test]
    fn prop_checkSetAssignment3() {
        assert!(produces(check_set_assignment, "set foo=42"));
    }
    #[test]
    fn prop_checkSetAssignment4() {
        assert!(!produces(check_set_assignment, "set -- if=/dev/null"));
    }
    #[test]
    fn prop_checkSetAssignment5() {
        assert!(!produces(check_set_assignment, "set 'a=5'"));
    }
    #[test]
    fn prop_checkSetAssignment6() {
        assert!(!produces(check_set_assignment, "set"));
    }

    // checkExportedExpansions
    #[test]
    fn prop_checkExportedExpansions1() {
        assert!(produces(check_exported_expansions, "export $foo"));
    }
    #[test]
    fn prop_checkExportedExpansions2() {
        assert!(produces(check_exported_expansions, "export \"$foo\""));
    }
    #[test]
    fn prop_checkExportedExpansions3() {
        assert!(!produces(check_exported_expansions, "export foo"));
    }
    #[test]
    fn prop_checkExportedExpansions4() {
        assert!(!produces(check_exported_expansions, "export ${foo?}"));
    }

    // checkAliasesUsesArgs
    #[test]
    fn prop_checkAliasesUsesArgs1() {
        assert!(produces(check_aliases_uses_args, "alias a='cp $1 /a'"));
    }
    #[test]
    fn prop_checkAliasesUsesArgs2() {
        assert!(!produces(check_aliases_uses_args, "alias $1='foo'"));
    }
    #[test]
    fn prop_checkAliasesUsesArgs3() {
        assert!(produces(check_aliases_uses_args, "alias a=\"echo \\${@}\""));
    }

    // checkAliasesExpandEarly
    #[test]
    fn prop_checkAliasesExpandEarly1() {
        assert!(produces(
            check_aliases_expand_early,
            "alias foo=\"echo $PWD\""
        ));
    }
    #[test]
    fn prop_checkAliasesExpandEarly2() {
        assert!(!produces(check_aliases_expand_early, "alias -p"));
    }
    #[test]
    fn prop_checkAliasesExpandEarly3() {
        assert!(!produces(
            check_aliases_expand_early,
            "alias foo='echo {1..10}'"
        ));
    }

    // checkUnsetGlobs
    #[test]
    fn prop_checkUnsetGlobs1() {
        assert!(produces(check_unset_globs, "unset foo[1]"));
    }
    #[test]
    fn prop_checkUnsetGlobs2() {
        assert!(!produces(check_unset_globs, "unset foo"));
    }
    #[test]
    fn prop_checkUnsetGlobs3() {
        assert!(produces(check_unset_globs, "unset foo[$i]"));
    }
    #[test]
    fn prop_checkUnsetGlobs4() {
        assert!(produces(check_unset_globs, "unset foo[x${i}y]"));
    }
    #[test]
    fn prop_checkUnsetGlobs5() {
        assert!(!produces(check_unset_globs, "unset foo]["));
    }

    // checkLocalScope
    #[test]
    fn prop_checkLocalScope1() {
        assert!(produces(check_local_scope, "local foo=3"));
    }
    #[test]
    fn prop_checkLocalScope2() {
        assert!(!produces(check_local_scope, "f() { local foo=3; }"));
    }

    // checkMaskedReturns
    #[test]
    fn prop_checkMaskedReturns1() {
        assert!(produces(check_masked_returns, "f() { local a=$(false); }"));
    }
    #[test]
    fn prop_checkMaskedReturns2() {
        assert!(produces(check_masked_returns, "declare a=$(false)"));
    }
    #[test]
    fn prop_checkMaskedReturns3() {
        assert!(produces(check_masked_returns, "declare a=\"`false`\""));
    }
    #[test]
    fn prop_checkMaskedReturns4() {
        assert!(produces(check_masked_returns, "readonly a=$(false)"));
    }
    #[test]
    fn prop_checkMaskedReturns5() {
        assert!(produces(check_masked_returns, "readonly a=\"`false`\""));
    }
    #[test]
    fn prop_checkMaskedReturns6() {
        assert!(!produces(check_masked_returns, "declare a; a=$(false)"));
    }
    #[test]
    fn prop_checkMaskedReturns7() {
        assert!(!produces(
            check_masked_returns,
            "f() { local -r a=$(false); }"
        ));
    }
    #[test]
    fn prop_checkMaskedReturns8() {
        assert!(!produces(check_masked_returns, "a=$(false); readonly a"));
    }
    #[test]
    fn prop_checkMaskedReturns9() {
        assert!(produces(
            check_masked_returns,
            "#!/bin/ksh\n f() { typeset -r x=$(false); }"
        ));
    }
    #[test]
    fn prop_checkMaskedReturns10() {
        assert!(!produces(
            check_masked_returns,
            "#!/bin/ksh\n function f { typeset -r x=$(false); }"
        ));
    }
    #[test]
    fn prop_checkMaskedReturns11() {
        assert!(!produces(
            check_masked_returns,
            "#!/bin/bash\n f() { typeset -r x=$(false); }"
        ));
    }
    #[test]
    fn prop_checkMaskedReturns12() {
        assert!(produces(check_masked_returns, "typeset -r x=$(false);"));
    }
    #[test]
    fn prop_checkMaskedReturns13() {
        assert!(produces(
            check_masked_returns,
            "f() { typeset -g x=$(false); }"
        ));
    }
    #[test]
    fn prop_checkMaskedReturns14() {
        assert!(produces(check_masked_returns, "declare x=${ false; }"));
    }
    #[test]
    fn prop_checkMaskedReturns15() {
        assert!(produces(
            check_masked_returns,
            "f() { declare x=$(false); }"
        ));
    }

    // checkPrintfVar
    #[test]
    fn prop_checkPrintfVar1() {
        assert!(produces(check_printf_var, "printf \"Lol: $s\""));
    }
    #[test]
    fn prop_checkPrintfVar2() {
        assert!(!produces(check_printf_var, "printf 'Lol: $s'"));
    }
    #[test]
    fn prop_checkPrintfVar3() {
        assert!(produces(check_printf_var, "printf -v cow $(cmd)"));
    }
    #[test]
    fn prop_checkPrintfVar4() {
        assert!(!produces(check_printf_var, "printf \"%${count}s\" var"));
    }
    #[test]
    fn prop_checkPrintfVar5() {
        assert!(produces(check_printf_var, "printf '%s %s %s' foo bar"));
    }
    #[test]
    fn prop_checkPrintfVar6() {
        assert!(produces(check_printf_var, "printf foo bar baz"));
    }
    #[test]
    fn prop_checkPrintfVar7() {
        assert!(produces(check_printf_var, "printf -- foo bar baz"));
    }
    #[test]
    fn prop_checkPrintfVar8() {
        assert!(!produces(
            check_printf_var,
            "printf '%s %s %s' \"${var[@]}\""
        ));
    }
    #[test]
    fn prop_checkPrintfVar9() {
        assert!(!produces(check_printf_var, "printf '%s %s %s\\n' *.png"));
    }
    #[test]
    fn prop_checkPrintfVar10() {
        assert!(!produces(check_printf_var, "printf '%s %s %s' foo bar baz"));
    }
    #[test]
    fn prop_checkPrintfVar11() {
        assert!(!produces(check_printf_var, "printf '%(%s%s)T' -1"));
    }
    #[test]
    fn prop_checkPrintfVar12() {
        assert!(produces(check_printf_var, "printf '%s %s\\n' 1 2 3"));
    }
    #[test]
    fn prop_checkPrintfVar13() {
        assert!(!produces(check_printf_var, "printf '%s %s\\n' 1 2 3 4"));
    }
    #[test]
    fn prop_checkPrintfVar14() {
        assert!(produces(check_printf_var, "printf '%*s\\n' 1"));
    }
    #[test]
    fn prop_checkPrintfVar15() {
        assert!(!produces(check_printf_var, "printf '%*s\\n' 1 2"));
    }
    #[test]
    fn prop_checkPrintfVar16() {
        assert!(!produces(check_printf_var, "printf $'string'"));
    }
    #[test]
    fn prop_checkPrintfVar17() {
        assert!(produces(check_printf_var, "printf '%-*s\\n' 1"));
    }
    #[test]
    fn prop_checkPrintfVar18() {
        assert!(!produces(check_printf_var, "printf '%-*s\\n' 1 2"));
    }
    #[test]
    fn prop_checkPrintfVar19() {
        assert!(!produces(check_printf_var, "printf '%(%s)T'"));
    }
    #[test]
    fn prop_checkPrintfVar20() {
        assert!(!produces(check_printf_var, "printf '%d %(%s)T' 42"));
    }
    #[test]
    fn prop_checkPrintfVar21() {
        assert!(produces(check_printf_var, "printf '%d %(%s)T'"));
    }
    #[test]
    fn prop_checkPrintfVar22() {
        assert!(produces(
            check_printf_var,
            "printf '%s
%s' foo"
        ));
    }
    #[test]
    fn prop_checkPrintfVar23() {
        assert!(!produces(check_printf_var, "printf -vTODAY '%(%Y)T'"));
    }

    // checkSshCommandString
    #[test]
    fn prop_checkSshCmdStr1() {
        assert!(produces(check_ssh_command_string, "ssh host \"echo $PS1\""));
    }
    #[test]
    fn prop_checkSshCmdStr2() {
        assert!(!produces(check_ssh_command_string, "ssh host \"ls foo\""));
    }
    #[test]
    fn prop_checkSshCmdStr3() {
        assert!(!produces(check_ssh_command_string, "ssh \"$host\""));
    }
    #[test]
    fn prop_checkSshCmdStr4() {
        assert!(!produces(check_ssh_command_string, "ssh -i key \"$host\""));
    }

    // checkUnquotedEchoSpaces
    #[test]
    fn prop_checkUnquotedEchoSpaces1() {
        assert!(produces(check_unquoted_echo_spaces, "echo foo         bar"));
    }
    #[test]
    fn prop_checkUnquotedEchoSpaces2() {
        assert!(!produces(check_unquoted_echo_spaces, "echo       foo"));
    }
    #[test]
    fn prop_checkUnquotedEchoSpaces3() {
        assert!(!produces(check_unquoted_echo_spaces, "echo foo  bar"));
    }
    #[test]
    fn prop_checkUnquotedEchoSpaces4() {
        assert!(!produces(
            check_unquoted_echo_spaces,
            "echo 'foo          bar'"
        ));
    }
    #[test]
    fn prop_checkUnquotedEchoSpaces5() {
        assert!(!produces(
            check_unquoted_echo_spaces,
            "echo a > myfile.txt b"
        ));
    }
    #[test]
    fn prop_checkUnquotedEchoSpaces6() {
        assert!(!produces(
            check_unquoted_echo_spaces,
            "        echo foo\\\n        bar"
        ));
    }

    // checkEvalArray
    #[test]
    fn prop_checkEvalArray1() {
        assert!(produces(check_eval_array, "eval $@"));
    }
    #[test]
    fn prop_checkEvalArray2() {
        assert!(produces(check_eval_array, "eval \"${args[@]}\""));
    }
    #[test]
    fn prop_checkEvalArray3() {
        assert!(produces(check_eval_array, "eval \"${args[@]@Q}\""));
    }
    #[test]
    fn prop_checkEvalArray4() {
        assert!(!produces(check_eval_array, "eval \"${args[*]@Q}\""));
    }
    #[test]
    fn prop_checkEvalArray5() {
        assert!(!produces(check_eval_array, "eval \"$*\""));
    }

    // checkMvArguments
    #[test]
    fn prop_checkMvArguments1() {
        assert!(produces(check_mv_arguments, "mv 'foo bar'"));
    }
    #[test]
    fn prop_checkMvArguments2() {
        assert!(!produces(check_mv_arguments, "mv foo bar"));
    }
    #[test]
    fn prop_checkMvArguments3() {
        assert!(!produces(check_mv_arguments, "mv 'foo bar'{,bak}"));
    }
    #[test]
    fn prop_checkMvArguments4() {
        assert!(!produces(check_mv_arguments, "mv \"$@\""));
    }
    #[test]
    fn prop_checkMvArguments5() {
        assert!(!produces(check_mv_arguments, "mv -t foo bar"));
    }
    #[test]
    fn prop_checkMvArguments6() {
        assert!(!produces(
            check_mv_arguments,
            "mv --target-directory=foo bar"
        ));
    }
    #[test]
    fn prop_checkMvArguments7() {
        assert!(!produces(check_mv_arguments, "mv --target-direc=foo bar"));
    }
    #[test]
    fn prop_checkMvArguments8() {
        assert!(!produces(check_mv_arguments, "mv --version"));
    }
    #[test]
    fn prop_checkMvArguments9() {
        assert!(!produces(check_mv_arguments, "mv \"${!var}\""));
    }

    // checkArgComparison
    #[test]
    fn prop_checkArgComparison1() {
        assert!(produces(check_arg_comparison, "declare a = b"));
    }
    #[test]
    fn prop_checkArgComparison2() {
        assert!(produces(check_arg_comparison, "declare a =b"));
    }
    #[test]
    fn prop_checkArgComparison3() {
        assert!(!produces(check_arg_comparison, "declare a=b"));
    }
    #[test]
    fn prop_checkArgComparison4() {
        assert!(produces(check_arg_comparison, "export a +=b"));
    }
    #[test]
    fn prop_checkArgComparison7() {
        assert!(!produces(check_arg_comparison, "declare -a +i foo"));
    }
    #[test]
    fn prop_checkArgComparison8() {
        assert!(produces(check_arg_comparison, "let x = 0"));
    }
    #[test]
    fn prop_checkArgComparison9() {
        assert!(produces(check_arg_comparison, "alias x =0"));
    }

    // checkMultipleDeclaring
    #[test]
    fn prop_checkMultipleDeclaring1() {
        assert!(produces(
            check_multiple_declaring,
            "q() { local readonly var=1; }"
        ));
    }
    #[test]
    fn prop_checkMultipleDeclaring2() {
        assert!(!produces(check_multiple_declaring, "q() { local var=1; }"));
    }
    #[test]
    fn prop_checkMultipleDeclaring3() {
        assert!(produces(check_multiple_declaring, "readonly local foo=5"));
    }
    #[test]
    fn prop_checkMultipleDeclaring4() {
        assert!(produces(check_multiple_declaring, "export readonly foo=5"));
    }
    #[test]
    fn prop_checkMultipleDeclaring5() {
        assert!(!produces(
            check_multiple_declaring,
            "f() { local -r foo=5; }"
        ));
    }
    #[test]
    fn prop_checkMultipleDeclaring6() {
        assert!(!produces(check_multiple_declaring, "declare -rx foo=5"));
    }
    #[test]
    fn prop_checkMultipleDeclaring7() {
        assert!(!produces(
            check_multiple_declaring,
            "readonly 'local' foo=5"
        ));
    }

    // checkBackreferencingDeclaration
    #[test]
    fn prop_checkBackreferencingDeclaration1() {
        assert!(produces(
            check_backreferencing_declaration,
            "declare x=1 y=foo$x"
        ));
    }
    #[test]
    fn prop_checkBackreferencingDeclaration2() {
        assert!(produces(
            check_backreferencing_declaration,
            "readonly x=1 y=$((1+x))"
        ));
    }
    #[test]
    fn prop_checkBackreferencingDeclaration3() {
        assert!(produces(
            check_backreferencing_declaration,
            "local x=1 y=$(echo $x)"
        ));
    }
    #[test]
    fn prop_checkBackreferencingDeclaration4() {
        assert!(produces(
            check_backreferencing_declaration,
            "local x=1 y[$x]=z"
        ));
    }
    #[test]
    fn prop_checkBackreferencingDeclaration5() {
        assert!(produces(
            check_backreferencing_declaration,
            "declare x=var $x=1"
        ));
    }
    #[test]
    fn prop_checkBackreferencingDeclaration6() {
        assert!(produces(
            check_backreferencing_declaration,
            "declare x=var $x=1"
        ));
    }
    #[test]
    fn prop_checkBackreferencingDeclaration7() {
        assert!(produces(
            check_backreferencing_declaration,
            "declare x=var $k=$x"
        ));
    }

    // checkSudoRedirect
    #[test]
    fn prop_checkSudoRedirect1() {
        assert!(produces(check_sudo_redirect, "sudo echo 3 > /proc/file"));
    }
    #[test]
    fn prop_checkSudoRedirect2() {
        assert!(produces(check_sudo_redirect, "doas cmd < input"));
    }
    #[test]
    fn prop_checkSudoRedirect3() {
        assert!(produces(check_sudo_redirect, "run0 cmd >> file"));
    }
    #[test]
    fn prop_checkSudoRedirect4() {
        assert!(produces(check_sudo_redirect, "sudo cmd &> file"));
    }
    #[test]
    fn prop_checkSudoRedirect5() {
        assert!(!produces(check_sudo_redirect, "sudo cmd 2>&1"));
    }
    #[test]
    fn prop_checkSudoRedirect6() {
        assert!(!produces(check_sudo_redirect, "doas cmd 2> log"));
    }
    #[test]
    fn prop_checkSudoRedirect7() {
        assert!(!produces(check_sudo_redirect, "run0 cmd > /dev/null 2>&1"));
    }

    // checkSudoArgs
    #[test]
    fn prop_checkSudoArgs1() {
        assert!(produces(check_sudo_args, "sudo cd /root"));
    }
    #[test]
    fn prop_checkSudoArgs2() {
        assert!(produces(check_sudo_args, "run0 export x=3"));
    }
    #[test]
    fn prop_checkSudoArgs3() {
        assert!(!produces(check_sudo_args, "sudo ls /usr/local/protected"));
    }
    #[test]
    fn prop_checkSudoArgs4() {
        assert!(!produces(check_sudo_args, "doas ls && export x=3"));
    }
    #[test]
    fn prop_checkSudoArgs5() {
        assert!(!produces(check_sudo_args, "sudo echo ls"));
    }
    #[test]
    fn prop_checkSudoArgs6() {
        assert!(!produces(check_sudo_args, "sudo -n -u export ls"));
    }
    #[test]
    fn prop_checkSudoArgs7() {
        assert!(!produces(check_sudo_args, "sudo docker export foo"));
    }

    // checkWhileGetoptsCase
    #[test]
    fn prop_checkWhileGetoptsCase1() {
        assert!(produces(
            check_while_getopts_case,
            "while getopts 'a:b' x; do case $x in a) foo;; esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase2() {
        assert!(produces(
            check_while_getopts_case,
            "while getopts 'a:' x; do case $x in a) foo;; b) bar;; esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase3() {
        assert!(!produces(
            check_while_getopts_case,
            "while getopts 'a:b' x; do case $x in a) foo;; b) bar;; *) :;esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase4() {
        assert!(!produces(
            check_while_getopts_case,
            "while getopts 'a:123' x; do case $x in a) foo;; [0-9]) bar;; esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase5() {
        assert!(!produces(
            check_while_getopts_case,
            "while getopts 'a:' x; do case $x in a) foo;; \\?) bar;; *) baz;; esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase6() {
        assert!(!produces(
            check_while_getopts_case,
            "while getopts 'a:b' x; do case $y in a) foo;; esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase7() {
        assert!(!produces(
            check_while_getopts_case,
            "while getopts 'a:b' x; do case x$x in xa) foo;; xb) foo;; esac; done"
        ));
    }
    #[test]
    fn prop_checkWhileGetoptsCase8() {
        assert!(!produces(
            check_while_getopts_case,
            "while getopts 'a:b' x; do x=a; case $x in a) foo;; esac; done"
        ));
    }

    // checkReadExpansions
    #[test]
    fn prop_checkReadExpansions1() {
        assert!(produces(check_read_expansions, "read $var"));
    }
    #[test]
    fn prop_checkReadExpansions2() {
        assert!(produces(check_read_expansions, "read -r $var"));
    }
    #[test]
    fn prop_checkReadExpansions3() {
        assert!(!produces(check_read_expansions, "read -p $var"));
    }
    #[test]
    fn prop_checkReadExpansions4() {
        assert!(!produces(check_read_expansions, "read -rd $delim name"));
    }
    #[test]
    fn prop_checkReadExpansions5() {
        assert!(produces(check_read_expansions, "read \"$var\""));
    }
    #[test]
    fn prop_checkReadExpansions6() {
        assert!(produces(check_read_expansions, "read -a $var"));
    }
    #[test]
    fn prop_checkReadExpansions7() {
        assert!(!produces(check_read_expansions, "read $1"));
    }
    #[test]
    fn prop_checkReadExpansions8() {
        assert!(!produces(check_read_expansions, "read ${var?}"));
    }
    #[test]
    fn prop_checkReadExpansions9() {
        assert!(produces(check_read_expansions, "read arr[val]"));
    }
}
