//! Checks on shell builtins, from `ShellCheck.Checks.Commands`.
use super::common::*;
use super::{CommandCheck, CommandName::*};
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::is_true_assignment_source;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib;
use crate::ast_lib::e4m;
use crate::ast_lib::get_literal_string;
use crate::ast_lib::get_literal_string_def;
use crate::ast_lib::get_word_parts;
use crate::ast_lib::is_flag;
use crate::ast_lib::is_glob;
use crate::ast_lib::is_literal;
use crate::ast_lib::oversimplify_concat;

use crate::cfg::may_become_multiple_args;
use crate::cfg::{
    get_braced_modifier, get_braced_reference, get_gnu_opts, get_unquoted_literal, is_variable_name,
};
use crate::data::{DECLARING_COMMANDS, FLAGS_FOR_READ};
use crate::interface::Code;
use crate::interface::Shell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

pub(super) fn check_trap_quotes() -> CommandCheck {
    CommandCheck::new(Exactly("trap"), |_params, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
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
    })
}

pub(super) fn check_return() -> CommandCheck {
    CommandCheck::new(Exactly("return"), |_params, te, out| {
        return_or_exit(
            arguments(te),
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
    })
}

pub(super) fn check_exit() -> CommandCheck {
    CommandCheck::new(Exactly("exit"), |_params, te, out| {
        return_or_exit(
            arguments(te),
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
    })
}

pub(super) fn check_nonportable_signals() -> CommandCheck {
    CommandCheck::new(Exactly("trap"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let args = word_args(words);
        match args.split_first() {
            Some((first, rest)) if !is_flag(first) => {
                for param in rest {
                    trap_check(param, out);
                }
            }
            _ => {}
        }
    })
}

pub(super) fn check_printf_var() -> CommandCheck {
    CommandCheck::new(Exactly("printf"), |_params, te, out| {
        // f: skip leading `--`, `-v var`, `-vVAR`.
        let mut rest = arguments(te);
        loop {
            let first = match rest.first() {
                Some(f) => f,
                None => return,
            };
            let s = ast_lib::get_literal_string(first);
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
    })
}

pub(super) fn check_set_assignment() -> CommandCheck {
    CommandCheck::new(Exactly("set"), |_params, te, out| {
        let args = arguments(te);
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
    })
}

pub(super) fn check_exported_expansions() -> CommandCheck {
    CommandCheck::new(Exactly("export"), |_params, te, out| {
        for arg in arguments(te) {
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
    })
}

pub(super) fn check_aliases_uses_args() -> CommandCheck {
    CommandCheck::new(Exactly("alias"), |_params, te, out| {
        for arg in arguments(te) {
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
    })
}

pub(super) fn check_aliases_expand_early() -> CommandCheck {
    CommandCheck::new(Exactly("alias"), |_params, te, out| {
        for arg in arguments(te) {
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
    })
}

pub(super) fn check_unset_globs() -> CommandCheck {
    CommandCheck::new(Exactly("unset"), |_params, te, out| {
        for arg in arguments(te) {
            if is_glob(arg) {
                warn(
                    out,
                    arg.id(),
                    2184,
                    "Quote arguments to unset so they're not glob expanded.",
                );
            }
        }
    })
}

pub(super) fn check_local_scope() -> CommandCheck {
    CommandCheck::new(Exactly("local"), |params, te, out| {
        // whenShell [Bash, Dash, BusyboxSh]
        if !matches!(params.shell, Shell::Bash | Shell::Dash | Shell::BusyboxSh) {
            return;
        }
        let path = get_path(params, te);
        if !path.iter().any(is_function_like) {
            err(
                out,
                get_command_token_or_this(te).id(),
                2168,
                "'local' is only valid in functions.",
            );
        }
    })
}

pub(super) fn check_while_getopts_case() -> CommandCheck {
    CommandCheck::new(Exactly("getopts"), |params, te, out| {
        // f t@(T_SimpleCommand _ _ (cmd:arg1:name:_))
        let words = match &*te.inner {
            InnerToken::T_SimpleCommand { words, .. } if words.len() >= 3 => words,
            _ => return,
        };
        let arg1 = &words[1];
        let name = &words[2];

        let options = match ast_lib::get_literal_string(arg1) {
            Some(o) => o,
            None => return,
        };
        let getopts_var = match ast_lib::get_literal_string(name) {
            Some(v) => v,
            None => return,
        };

        let path = get_path(params, te);
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
    })
}

pub(super) fn check_let_usage() -> CommandCheck {
    CommandCheck::new(Exactly("let"), |params, t, out| {
        if matches!(params.shell, Shell::Bash | Shell::Ksh) {
            style(
                out,
                t.id(),
                2219,
                "Instead of 'let expr', prefer (( expr )) .",
            );
        }
    })
}

pub(super) fn check_read_expansions() -> CommandCheck {
    CommandCheck::new(Exactly("read"), |_params, te, out| {
        let args = arguments(te);
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
    })
}

pub(super) fn check_source_args() -> CommandCheck {
    CommandCheck::new(Exactly("."), |params, te, out| {
        // whenShell [Sh, Dash]
        if !matches!(params.shell, Shell::Sh | Shell::Dash) {
            return;
        }
        let args = arguments(te);
        if args.len() >= 2 {
            // (file:arg1:_)
            let arg1 = &args[1];
            warn(
                out,
                arg1.id(),
                2240,
                "The dot command does not support arguments in sh/dash. Set them as variables.",
            );
        }
    })
}

pub(super) fn check_eval_array() -> CommandCheck {
    CommandCheck::new(Exactly("eval"), |_params, te, out| {
        for arg in arguments(te) {
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
    })
}

/// `map checkArgComparison ("alias" : declaringCommands)`.
pub(super) fn check_arg_comparison(cmd: &'static str) -> CommandCheck {
    CommandCheck::new(Exactly(cmd), move |_params, te, out| {
        for arg in arguments(te) {
            if let Some(s) = ast_lib::get_leading_unquoted_string(arg) {
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
            // 'let' is parsed as a sequence of arithmetic expansions, so we
            // want the additional warning for "x=".
            if cmd == "let" {
                if let Some(token) = ast_lib::get_trailing_unquoted_literal(arg) {
                    if ast_lib::get_literal_string(token).is_some_and(|s| s.ends_with('=')) {
                        err(out, token.id(), 2290, "Remove spaces around = to assign.");
                    }
                }
            }
        }
    })
}

pub(super) fn check_masked_returns(cmd: &'static str) -> CommandCheck {
    CommandCheck::new(Exactly(cmd), move |params, te, out| {
        let name = match get_command_name(te) {
            Some(n) => n,
            None => return,
        };
        let path = get_path(params, te);
        let shell = params.shell;

        let flags: Vec<String> = get_all_flags(te).into_iter().map(|(_, s)| s).collect();
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

        for a in arguments(te) {
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
    })
}

/// `map checkMultipleDeclaring declaringCommands`.
pub(super) fn check_multiple_declaring(cmd: &'static str) -> CommandCheck {
    CommandCheck::new(Exactly(cmd), move |_params, te, out| {
        let Some(cmd) = get_command_name(te) else {
            return;
        };
        for arg in arguments(te) {
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
    })
}

/// `map checkBackreferencingDeclaration declaringCommands`: an argument of a
/// declaring command that reads a variable assigned earlier in the same
/// command, where that assignment has not taken effect yet.
pub(super) fn check_backreferencing_declaration(cmd: &'static str) -> CommandCheck {
    CommandCheck::new(Exactly(cmd), move |params, te, out| {
        let Some(cfga) = params.cfg_analysis.as_ref() else {
            return;
        };
        let Some(cmd) = get_command_name(te) else {
            return;
        };
        // foldM_ (perArg cfga) M.empty (arguments t)
        let mut left_args: BTreeMap<String, Id> = BTreeMap::new();
        for arg in arguments(te) {
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
    })
}

fn trap_check(param: &Token, out: &mut Out) {
    let str = match get_literal_string(param) {
        Some(s) => s,
        None => return,
    };
    let id = param.id();
    // checkNumeric
    if !str.is_empty()
        && str.chars().all(|c| c.is_ascii_digit())
        && str != "0"
        && !matches!(str.as_str(), "1" | "2" | "3" | "6" | "9" | "14" | "15")
    {
        warn(
            out,
            id,
            2172,
            "Trapping signals by number is not well defined. Prefer signal names.",
        );
    }
    // checkUntrappable
    let lower = str.to_lowercase();
    if matches!(
        lower.as_str(),
        "kill" | "9" | "sigkill" | "stop" | "sigstop"
    ) {
        err(out, id, 2173, "SIGKILL/SIGSTOP can not be trapped.");
    }
}

/// `isFunctionLike`.
fn is_function_like(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_Function { .. } | InnerToken::T_BatsTest { .. }
    )
}

fn return_lit(value: &Token) -> String {
    ast_lib::get_literal_string_ext(value, &|inner| {
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

fn set_literal(t: &Token) -> String {
    match &*t.inner {
        InnerToken::T_NormalWord(l) => l.iter().map(set_literal).collect(),
        InnerToken::T_Literal(s) => s.clone(),
        _ => "*".to_string(),
    }
}

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

/// `check format more`.
fn printf_check(format: &Token, more: &[Token], out: &mut Out) {
    if let Some(string) = ast_lib::get_literal_string(format) {
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

fn eval_is_escaped(q: &Token) -> bool {
    match &*q.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            get_braced_modifier(&oversimplify_concat(op)).contains('Q')
        }
        _ => false,
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
    ast_lib::get_literal_string(t).or_else(|| getopts_from_glob(t))
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

fn read_is_unquoted_bracket(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Glob(s) if s.starts_with('['))
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::interface::Shell;
    use crate::test_support::*;

    #[test]
    fn prop_checkLetUsage1() {
        assert!(emits_code_shell(
            check_let_usage(),
            "let a=1",
            2219i64,
            Shell::Bash
        ));
    }

    #[test]
    fn prop_checkLetUsage2() {
        assert!(!emits_code_shell(
            check_let_usage(),
            "(( a=1 ))",
            2219i64,
            Shell::Bash
        ));
    }

    // ---- SC2209 / SC2037 checkAssignAteCommand ----

    #[test]
    fn prop_checkNonportableSignals1() {
        assert!(emits(check_nonportable_signals(), "trap f 8"));
    }

    #[test]
    fn prop_checkNonportableSignals2() {
        assert!(!emits(check_nonportable_signals(), "trap f 0"));
    }

    #[test]
    fn prop_checkNonportableSignals3() {
        assert!(!emits(check_nonportable_signals(), "trap f 14"));
    }

    #[test]
    fn prop_checkNonportableSignals4() {
        assert!(emits(check_nonportable_signals(), "trap f SIGKILL"));
    }

    #[test]
    fn prop_checkNonportableSignals5() {
        assert!(emits(check_nonportable_signals(), "trap f 9"));
    }

    #[test]
    fn prop_checkNonportableSignals6() {
        assert!(emits(check_nonportable_signals(), "trap f stop"));
    }

    #[test]
    fn prop_checkNonportableSignals7() {
        assert!(!emits(check_nonportable_signals(), "trap 'stop' int"));
    }

    // ---- SC2023 checkTimeParameters ----

    #[test]
    fn prop_checkReturn1() {
        assert!(!produces(check_return(), "return"));
    }

    #[test]
    fn prop_checkReturn2() {
        assert!(!produces(check_return(), "return 1"));
    }

    #[test]
    fn prop_checkReturn3() {
        assert!(!produces(check_return(), "return $var"));
    }

    #[test]
    fn prop_checkReturn4() {
        assert!(!produces(check_return(), "return $((a|b))"));
    }

    #[test]
    fn prop_checkReturn5() {
        assert!(produces(check_return(), "return -1"));
    }

    #[test]
    fn prop_checkReturn6() {
        assert!(produces(check_return(), "return 1000"));
    }

    #[test]
    fn prop_checkReturn7() {
        assert!(produces(check_return(), "return 'hello world'"));
    }

    // checkExit

    #[test]
    fn prop_checkExit1() {
        assert!(!produces(check_exit(), "exit"));
    }

    #[test]
    fn prop_checkExit2() {
        assert!(!produces(check_exit(), "exit 1"));
    }

    #[test]
    fn prop_checkExit3() {
        assert!(!produces(check_exit(), "exit $var"));
    }

    #[test]
    fn prop_checkExit4() {
        assert!(!produces(check_exit(), "exit $((a|b))"));
    }

    #[test]
    fn prop_checkExit5() {
        assert!(produces(check_exit(), "exit -1"));
    }

    #[test]
    fn prop_checkExit6() {
        assert!(produces(check_exit(), "exit 1000"));
    }

    #[test]
    fn prop_checkExit7() {
        assert!(produces(check_exit(), "exit 'hello world'"));
    }

    // checkSetAssignment

    #[test]
    fn prop_checkSetAssignment1() {
        assert!(produces(check_set_assignment(), "set foo 42"));
    }

    #[test]
    fn prop_checkSetAssignment2() {
        assert!(produces(check_set_assignment(), "set foo = 42"));
    }

    #[test]
    fn prop_checkSetAssignment3() {
        assert!(produces(check_set_assignment(), "set foo=42"));
    }

    #[test]
    fn prop_checkSetAssignment4() {
        assert!(!produces(check_set_assignment(), "set -- if=/dev/null"));
    }

    #[test]
    fn prop_checkSetAssignment5() {
        assert!(!produces(check_set_assignment(), "set 'a=5'"));
    }

    #[test]
    fn prop_checkSetAssignment6() {
        assert!(!produces(check_set_assignment(), "set"));
    }

    // checkExportedExpansions

    #[test]
    fn prop_checkExportedExpansions1() {
        assert!(produces(check_exported_expansions(), "export $foo"));
    }

    #[test]
    fn prop_checkExportedExpansions2() {
        assert!(produces(check_exported_expansions(), "export \"$foo\""));
    }

    #[test]
    fn prop_checkExportedExpansions3() {
        assert!(!produces(check_exported_expansions(), "export foo"));
    }

    #[test]
    fn prop_checkExportedExpansions4() {
        assert!(!produces(check_exported_expansions(), "export ${foo?}"));
    }

    // checkAliasesUsesArgs

    #[test]
    fn prop_checkAliasesUsesArgs1() {
        assert!(produces(check_aliases_uses_args(), "alias a='cp $1 /a'"));
    }

    #[test]
    fn prop_checkAliasesUsesArgs2() {
        assert!(!produces(check_aliases_uses_args(), "alias $1='foo'"));
    }

    #[test]
    fn prop_checkAliasesUsesArgs3() {
        assert!(produces(
            check_aliases_uses_args(),
            "alias a=\"echo \\${@}\""
        ));
    }

    // checkAliasesExpandEarly

    #[test]
    fn prop_checkAliasesExpandEarly1() {
        assert!(produces(
            check_aliases_expand_early(),
            "alias foo=\"echo $PWD\""
        ));
    }

    #[test]
    fn prop_checkAliasesExpandEarly2() {
        assert!(!produces(check_aliases_expand_early(), "alias -p"));
    }

    #[test]
    fn prop_checkAliasesExpandEarly3() {
        assert!(!produces(
            check_aliases_expand_early(),
            "alias foo='echo {1..10}'"
        ));
    }

    // checkUnsetGlobs

    #[test]
    fn prop_checkUnsetGlobs1() {
        assert!(produces(check_unset_globs(), "unset foo[1]"));
    }

    #[test]
    fn prop_checkUnsetGlobs2() {
        assert!(!produces(check_unset_globs(), "unset foo"));
    }

    #[test]
    fn prop_checkUnsetGlobs3() {
        assert!(produces(check_unset_globs(), "unset foo[$i]"));
    }

    #[test]
    fn prop_checkUnsetGlobs4() {
        assert!(produces(check_unset_globs(), "unset foo[x${i}y]"));
    }

    #[test]
    fn prop_checkUnsetGlobs5() {
        assert!(!produces(check_unset_globs(), "unset foo]["));
    }

    // checkLocalScope

    #[test]
    fn prop_checkLocalScope1() {
        assert!(produces(check_local_scope(), "local foo=3"));
    }

    #[test]
    fn prop_checkLocalScope2() {
        assert!(!produces(check_local_scope(), "f() { local foo=3; }"));
    }

    // checkMaskedReturns

    #[test]
    fn prop_checkMaskedReturns1() {
        assert!(produces(
            check_masked_returns("local"),
            "f() { local a=$(false); }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns2() {
        assert!(produces(
            check_masked_returns("declare"),
            "declare a=$(false)"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns3() {
        assert!(produces(
            check_masked_returns("declare"),
            "declare a=\"`false`\""
        ));
    }

    #[test]
    fn prop_checkMaskedReturns4() {
        assert!(produces(
            check_masked_returns("readonly"),
            "readonly a=$(false)"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns5() {
        assert!(produces(
            check_masked_returns("readonly"),
            "readonly a=\"`false`\""
        ));
    }

    #[test]
    fn prop_checkMaskedReturns6() {
        assert!(!produces(
            check_masked_returns("declare"),
            "declare a; a=$(false)"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns7() {
        assert!(!produces(
            check_masked_returns("local"),
            "f() { local -r a=$(false); }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns8() {
        assert!(!produces(
            check_masked_returns("readonly"),
            "a=$(false); readonly a"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns9() {
        assert!(produces(
            check_masked_returns("typeset"),
            "#!/bin/ksh\n f() { typeset -r x=$(false); }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns10() {
        assert!(!produces(
            check_masked_returns("typeset"),
            "#!/bin/ksh\n function f { typeset -r x=$(false); }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns11() {
        assert!(!produces(
            check_masked_returns("typeset"),
            "#!/bin/bash\n f() { typeset -r x=$(false); }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns12() {
        assert!(produces(
            check_masked_returns("typeset"),
            "typeset -r x=$(false);"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns13() {
        assert!(produces(
            check_masked_returns("typeset"),
            "f() { typeset -g x=$(false); }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns14() {
        assert!(produces(
            check_masked_returns("declare"),
            "declare x=${ false; }"
        ));
    }

    #[test]
    fn prop_checkMaskedReturns15() {
        assert!(produces(
            check_masked_returns("declare"),
            "f() { declare x=$(false); }"
        ));
    }

    // checkPrintfVar

    #[test]
    fn prop_checkPrintfVar1() {
        assert!(produces(check_printf_var(), "printf \"Lol: $s\""));
    }

    #[test]
    fn prop_checkPrintfVar2() {
        assert!(!produces(check_printf_var(), "printf 'Lol: $s'"));
    }

    #[test]
    fn prop_checkPrintfVar3() {
        assert!(produces(check_printf_var(), "printf -v cow $(cmd)"));
    }

    #[test]
    fn prop_checkPrintfVar4() {
        assert!(!produces(check_printf_var(), "printf \"%${count}s\" var"));
    }

    #[test]
    fn prop_checkPrintfVar5() {
        assert!(produces(check_printf_var(), "printf '%s %s %s' foo bar"));
    }

    #[test]
    fn prop_checkPrintfVar6() {
        assert!(produces(check_printf_var(), "printf foo bar baz"));
    }

    #[test]
    fn prop_checkPrintfVar7() {
        assert!(produces(check_printf_var(), "printf -- foo bar baz"));
    }

    #[test]
    fn prop_checkPrintfVar8() {
        assert!(!produces(
            check_printf_var(),
            "printf '%s %s %s' \"${var[@]}\""
        ));
    }

    #[test]
    fn prop_checkPrintfVar9() {
        assert!(!produces(check_printf_var(), "printf '%s %s %s\\n' *.png"));
    }

    #[test]
    fn prop_checkPrintfVar10() {
        assert!(!produces(
            check_printf_var(),
            "printf '%s %s %s' foo bar baz"
        ));
    }

    #[test]
    fn prop_checkPrintfVar11() {
        assert!(!produces(check_printf_var(), "printf '%(%s%s)T' -1"));
    }

    #[test]
    fn prop_checkPrintfVar12() {
        assert!(produces(check_printf_var(), "printf '%s %s\\n' 1 2 3"));
    }

    #[test]
    fn prop_checkPrintfVar13() {
        assert!(!produces(check_printf_var(), "printf '%s %s\\n' 1 2 3 4"));
    }

    #[test]
    fn prop_checkPrintfVar14() {
        assert!(produces(check_printf_var(), "printf '%*s\\n' 1"));
    }

    #[test]
    fn prop_checkPrintfVar15() {
        assert!(!produces(check_printf_var(), "printf '%*s\\n' 1 2"));
    }

    #[test]
    fn prop_checkPrintfVar16() {
        assert!(!produces(check_printf_var(), "printf $'string'"));
    }

    #[test]
    fn prop_checkPrintfVar17() {
        assert!(produces(check_printf_var(), "printf '%-*s\\n' 1"));
    }

    #[test]
    fn prop_checkPrintfVar18() {
        assert!(!produces(check_printf_var(), "printf '%-*s\\n' 1 2"));
    }

    #[test]
    fn prop_checkPrintfVar19() {
        assert!(!produces(check_printf_var(), "printf '%(%s)T'"));
    }

    #[test]
    fn prop_checkPrintfVar20() {
        assert!(!produces(check_printf_var(), "printf '%d %(%s)T' 42"));
    }

    #[test]
    fn prop_checkPrintfVar21() {
        assert!(produces(check_printf_var(), "printf '%d %(%s)T'"));
    }

    #[test]
    fn prop_checkPrintfVar22() {
        assert!(produces(
            check_printf_var(),
            "printf '%s
%s' foo"
        ));
    }

    #[test]
    fn prop_checkPrintfVar23() {
        assert!(!produces(check_printf_var(), "printf -vTODAY '%(%Y)T'"));
    }

    // checkSshCommandString

    #[test]
    fn prop_checkEvalArray1() {
        assert!(produces(check_eval_array(), "eval $@"));
    }

    #[test]
    fn prop_checkEvalArray2() {
        assert!(produces(check_eval_array(), "eval \"${args[@]}\""));
    }

    #[test]
    fn prop_checkEvalArray3() {
        assert!(produces(check_eval_array(), "eval \"${args[@]@Q}\""));
    }

    #[test]
    fn prop_checkEvalArray4() {
        assert!(!produces(check_eval_array(), "eval \"${args[*]@Q}\""));
    }

    #[test]
    fn prop_checkEvalArray5() {
        assert!(!produces(check_eval_array(), "eval \"$*\""));
    }

    // checkMvArguments

    #[test]
    fn prop_checkArgComparison1() {
        assert!(produces(check_arg_comparison("declare"), "declare a = b"));
    }

    #[test]
    fn prop_checkArgComparison2() {
        assert!(produces(check_arg_comparison("declare"), "declare a =b"));
    }

    #[test]
    fn prop_checkArgComparison3() {
        assert!(!produces(check_arg_comparison("declare"), "declare a=b"));
    }

    #[test]
    fn prop_checkArgComparison4() {
        assert!(produces(check_arg_comparison("export"), "export a +=b"));
    }

    #[test]
    fn prop_checkArgComparison7() {
        assert!(!produces(
            check_arg_comparison("declare"),
            "declare -a +i foo"
        ));
    }

    #[test]
    fn prop_checkArgComparison8() {
        assert!(produces(check_arg_comparison("let"), "let x = 0"));
    }

    #[test]
    fn prop_checkArgComparison9() {
        assert!(produces(check_arg_comparison("alias"), "alias x =0"));
    }

    // checkMultipleDeclaring

    #[test]
    fn prop_checkMultipleDeclaring1() {
        assert!(produces(
            check_multiple_declaring("local"),
            "q() { local readonly var=1; }"
        ));
    }

    #[test]
    fn prop_checkMultipleDeclaring2() {
        assert!(!produces(
            check_multiple_declaring("local"),
            "q() { local var=1; }"
        ));
    }

    #[test]
    fn prop_checkMultipleDeclaring3() {
        assert!(produces(
            check_multiple_declaring("readonly"),
            "readonly local foo=5"
        ));
    }

    #[test]
    fn prop_checkMultipleDeclaring4() {
        assert!(produces(
            check_multiple_declaring("export"),
            "export readonly foo=5"
        ));
    }

    #[test]
    fn prop_checkMultipleDeclaring5() {
        assert!(!produces(
            check_multiple_declaring("local"),
            "f() { local -r foo=5; }"
        ));
    }

    #[test]
    fn prop_checkMultipleDeclaring6() {
        assert!(!produces(
            check_multiple_declaring("declare"),
            "declare -rx foo=5"
        ));
    }

    #[test]
    fn prop_checkMultipleDeclaring7() {
        assert!(!produces(
            check_multiple_declaring("readonly"),
            "readonly 'local' foo=5"
        ));
    }

    // checkBackreferencingDeclaration

    #[test]
    fn prop_checkBackreferencingDeclaration1() {
        assert!(produces(
            check_backreferencing_declaration("declare"),
            "declare x=1 y=foo$x"
        ));
    }

    #[test]
    fn prop_checkBackreferencingDeclaration2() {
        assert!(produces(
            check_backreferencing_declaration("readonly"),
            "readonly x=1 y=$((1+x))"
        ));
    }

    #[test]
    fn prop_checkBackreferencingDeclaration3() {
        assert!(produces(
            check_backreferencing_declaration("local"),
            "local x=1 y=$(echo $x)"
        ));
    }

    #[test]
    fn prop_checkBackreferencingDeclaration4() {
        assert!(produces(
            check_backreferencing_declaration("local"),
            "local x=1 y[$x]=z"
        ));
    }

    #[test]
    fn prop_checkBackreferencingDeclaration5() {
        assert!(produces(
            check_backreferencing_declaration("declare"),
            "declare x=var $x=1"
        ));
    }

    #[test]
    fn prop_checkBackreferencingDeclaration6() {
        assert!(produces(
            check_backreferencing_declaration("declare"),
            "declare x=var $x=1"
        ));
    }

    #[test]
    fn prop_checkBackreferencingDeclaration7() {
        assert!(produces(
            check_backreferencing_declaration("declare"),
            "declare x=var $k=$x"
        ));
    }

    // checkSudoRedirect

    #[test]
    fn prop_checkWhileGetoptsCase1() {
        assert!(produces(
            check_while_getopts_case(),
            "while getopts 'a:b' x; do case $x in a) foo;; esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase2() {
        assert!(produces(
            check_while_getopts_case(),
            "while getopts 'a:' x; do case $x in a) foo;; b) bar;; esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase3() {
        assert!(!produces(
            check_while_getopts_case(),
            "while getopts 'a:b' x; do case $x in a) foo;; b) bar;; *) :;esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase4() {
        assert!(!produces(
            check_while_getopts_case(),
            "while getopts 'a:123' x; do case $x in a) foo;; [0-9]) bar;; esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase5() {
        assert!(!produces(
            check_while_getopts_case(),
            "while getopts 'a:' x; do case $x in a) foo;; \\?) bar;; *) baz;; esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase6() {
        assert!(!produces(
            check_while_getopts_case(),
            "while getopts 'a:b' x; do case $y in a) foo;; esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase7() {
        assert!(!produces(
            check_while_getopts_case(),
            "while getopts 'a:b' x; do case x$x in xa) foo;; xb) foo;; esac; done"
        ));
    }

    #[test]
    fn prop_checkWhileGetoptsCase8() {
        assert!(!produces(
            check_while_getopts_case(),
            "while getopts 'a:b' x; do x=a; case $x in a) foo;; esac; done"
        ));
    }

    // checkReadExpansions

    #[test]
    fn prop_checkReadExpansions1() {
        assert!(produces(check_read_expansions(), "read $var"));
    }

    #[test]
    fn prop_checkReadExpansions2() {
        assert!(produces(check_read_expansions(), "read -r $var"));
    }

    #[test]
    fn prop_checkReadExpansions3() {
        assert!(!produces(check_read_expansions(), "read -p $var"));
    }

    #[test]
    fn prop_checkReadExpansions4() {
        assert!(!produces(check_read_expansions(), "read -rd $delim name"));
    }

    #[test]
    fn prop_checkReadExpansions5() {
        assert!(produces(check_read_expansions(), "read \"$var\""));
    }

    #[test]
    fn prop_checkReadExpansions6() {
        assert!(produces(check_read_expansions(), "read -a $var"));
    }

    #[test]
    fn prop_checkReadExpansions7() {
        assert!(!produces(check_read_expansions(), "read $1"));
    }

    #[test]
    fn prop_checkReadExpansions8() {
        assert!(!produces(check_read_expansions(), "read ${var?}"));
    }

    #[test]
    fn prop_checkReadExpansions9() {
        assert!(produces(check_read_expansions(), "read arr[val]"));
    }

    #[test]
    fn prop_checkSourceArgs1() {
        assert!(produces(check_source_args(), "#!/bin/sh\n. script arg"));
    }

    #[test]
    fn prop_checkSourceArgs2() {
        assert!(!produces(check_source_args(), "#!/bin/sh\n. script"));
    }

    #[test]
    fn prop_checkSourceArgs3() {
        assert!(!produces(check_source_args(), "#!/bin/bash\n. script arg"));
    }

    // readSource: SC1090 (non-constant) / SC1091 (constant, not followed).
}
