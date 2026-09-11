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
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_literal_string;
use crate::interface::Shell;
use std::collections::HashMap;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_unquoted_expansions);
    c.node(command_dispatch);
}

// ===========================================================================
// Shared helpers (ported privately; parallel agents own other .rs files).
// ===========================================================================

/// Faithful port of `ShellCheck.ASTLib.oversimplify`.
fn oversimplify(token: &Token) -> Vec<String> {
    use InnerToken::*;
    match &*token.inner {
        T_NormalWord(l) => vec![l.iter().flat_map(oversimplify).collect::<Vec<String>>().concat()],
        T_DoubleQuoted(l) => vec![l.iter().flat_map(oversimplify).collect::<Vec<String>>().concat()],
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
        _ => vec![],
    }
}

fn concat_over(t: &Token) -> String {
    oversimplify(t).concat()
}

/// `onlyLiteralString`: literal parts concatenated, non-literals skipped.
fn only_literal_string(t: &Token) -> String {
    astlib::get_literal_string_ext(t, &|_| Some(String::new())).unwrap_or_default()
}

/// `isLiteral t = isJust $ getLiteralString t`.
fn is_literal(t: &Token) -> bool {
    get_literal_string(t).is_some()
}

fn basename(s: &str) -> String {
    match s.rfind('/') {
        Some(i) => s[i + 1..].to_string(),
        None => s.to_string(),
    }
}

// ---- getWordParts / isFlag / isGlob (ported from ASTLib) --------------------

fn get_word_parts(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_NormalWord(l) => l.iter().flat_map(|x| get_word_parts(x)).collect(),
        InnerToken::T_DoubleQuoted(l) => l.iter().collect(),
        _ => vec![t],
    }
}

fn is_flag(t: &Token) -> bool {
    match get_word_parts(t).first() {
        Some(p) => matches!(&*p.inner, InnerToken::T_Literal(s) if s.starts_with('-')),
        None => false,
    }
}

/// `isGlob`.
fn is_glob(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_Extglob { .. } => true,
        T_Glob(_) => true,
        T_NormalWord(l) => l.iter().any(is_glob) || has_split_range(l),
        _ => false,
    }
}
fn has_split_range(l: &[Token]) -> bool {
    let after: Vec<&Token> = l
        .iter()
        .skip_while(|t| !matches!(&*t.inner, InnerToken::T_Literal(s) if s == "["))
        .collect();
    after
        .iter()
        .any(|t| matches!(&*t.inner, InnerToken::T_Literal(s) if s.contains(']')))
}

// ---- command name resolution (ported from ASTLib, proven in batch_h) -------

fn get_command(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command(cmd),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        InnerToken::T_Annotation { token, .. } => get_command(token),
        _ => None,
    }
}

fn parse_flag_list(spec: &str) -> Vec<(String, bool)> {
    let mut out = vec![];
    let chars: Vec<char> = spec.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if i + 1 < chars.len() && chars[i + 1] == ':' {
            out.push((c.to_string(), true));
            i += 2;
        } else {
            out.push((c.to_string(), false));
            i += 1;
        }
    }
    out
}

fn get_bsd_opts<'a>(spec: &str, args: &'a [Token]) -> Option<Vec<(String, (&'a Token, &'a Token))>> {
    let mut flag_map: HashMap<String, bool> = HashMap::new();
    flag_map.insert(String::new(), false);
    for (k, v) in parse_flag_list(spec) {
        flag_map.insert(k, v);
    }
    opts_process(false, &flag_map, args)
}

fn list_to_args<'a>(args: &'a [Token]) -> Vec<(String, (&'a Token, &'a Token))> {
    args.iter().map(|x| (String::new(), (x, x))).collect()
}

fn opts_process<'a>(
    gnu: bool,
    flag_map: &HashMap<String, bool>,
    tokens: &'a [Token],
) -> Option<Vec<(String, (&'a Token, &'a Token))>> {
    if tokens.is_empty() {
        return Some(vec![]);
    }
    let token = &tokens[0];
    let rest = &tokens[1..];
    let s = get_literal_string(token).unwrap_or_else(|| "\0".to_string());

    if s == "--" {
        return Some(list_to_args(rest));
    }
    if let Some(word) = s.strip_prefix("--") {
        let (name, arg): (&str, &str) = match word.find('=') {
            Some(i) => (&word[..i], &word[i..]),
            None => (word, ""),
        };
        let needs_arg = *flag_map.get(name)?;
        if needs_arg && arg.is_empty() {
            if rest.is_empty() {
                return None;
            }
            let a = &rest[0];
            let mut more = opts_process(gnu, flag_map, &rest[1..])?;
            let mut out = vec![(name.to_string(), (token, a))];
            out.append(&mut more);
            return Some(out);
        } else {
            let mut more = opts_process(gnu, flag_map, rest)?;
            let mut out = vec![(name.to_string(), (token, token))];
            out.append(&mut more);
            return Some(out);
        }
    }
    if let Some(opts) = s.strip_prefix('-') {
        return short_to_opts(gnu, flag_map, opts, token, rest);
    }
    if gnu {
        let mut more = opts_process(gnu, flag_map, rest)?;
        let mut out = vec![(String::new(), (token, token))];
        out.append(&mut more);
        Some(out)
    } else {
        Some(list_to_args(tokens))
    }
}

fn short_to_opts<'a>(
    gnu: bool,
    flag_map: &HashMap<String, bool>,
    opts: &str,
    token: &'a Token,
    args: &'a [Token],
) -> Option<Vec<(String, (&'a Token, &'a Token))>> {
    let chars: Vec<char> = opts.chars().collect();
    if chars.is_empty() {
        return opts_process(gnu, flag_map, args);
    }
    let c = chars[0].to_string();
    let rest_opts: String = chars[1..].iter().collect();
    let needs_arg = *flag_map.get(&c)?;
    if needs_arg && rest_opts.is_empty() {
        if args.is_empty() {
            return None;
        }
        let next = &args[0];
        let mut more = opts_process(gnu, flag_map, &args[1..])?;
        let mut out = vec![(c, (token, next))];
        out.append(&mut more);
        Some(out)
    } else if needs_arg {
        let mut more = opts_process(gnu, flag_map, args)?;
        let mut out = vec![(c, (token, token))];
        out.append(&mut more);
        Some(out)
    } else {
        let mut more = short_to_opts(gnu, flag_map, &rest_opts, token, args)?;
        let mut out = vec![(c, (token, token))];
        out.append(&mut more);
        Some(out)
    }
}

fn get_effective_command_token<'a>(s: &str, args: &'a [Token]) -> Option<&'a Token> {
    let first_arg = || -> Option<&'a Token> {
        let arg = args.first()?;
        if is_flag(arg) {
            None
        } else {
            Some(arg)
        }
    };
    match s {
        "busybox" | "builtin" | "command" | "run" => first_arg(),
        "exec" => {
            let opts = get_bsd_opts("cla:", args)?;
            let (_, (t, _)) = opts.into_iter().find(|(name, _)| name.is_empty())?;
            Some(t)
        }
        _ => None,
    }
}

fn get_command_name_and_token(direct: bool, t: &Token) -> (Option<String>, &Token) {
    if let Some(cmd) = get_command(t) {
        if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
            if let Some((w, rest)) = words.split_first() {
                if let Some(s) = get_literal_string(w) {
                    if !direct {
                        if let Some(actual) = get_effective_command_token(&s, rest) {
                            return (get_literal_string(actual), actual);
                        }
                    }
                    return (Some(s), w);
                }
            }
        }
    }
    (None, t)
}

fn get_command_name(t: &Token) -> Option<String> {
    get_command_name_and_token(false, t).0
}

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

/// `isQuoteFree` = `isQuoteFreeNode False` (parent-context walk, no CFG).
fn is_quote_free(p: &Parameters, t: &Token) -> bool {
    is_quote_free_element(p, t) || {
        let mut node = p.parent(t);
        let mut result = false;
        while let Some(a) = node {
            if let Some(b) = is_quote_free_context(p, a) {
                result = b;
                break;
            }
            node = p.parent(a);
        }
        result
    }
}

fn is_quote_free_element(p: &Parameters, t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Assignment { .. } => assignment_is_quoting(p, t),
        InnerToken::T_FdRedirect { .. } => true,
        _ => false,
    }
}

fn is_quote_free_context(p: &Parameters, t: &Token) -> Option<bool> {
    use InnerToken::*;
    match &*t.inner {
        TC_Nullary { typ: ConditionType::DoubleBracket, .. } => Some(true),
        TC_Unary { typ: ConditionType::DoubleBracket, .. } => Some(true),
        TC_Binary { typ: ConditionType::DoubleBracket, .. } => Some(true),
        T_Arithmetic(_) => Some(true),
        T_DollarArithmetic(_) => Some(true),
        T_Assignment { .. } => Some(assignment_is_quoting(p, t)),
        T_Redirecting { .. } => Some(false),
        T_DoubleQuoted(_) => Some(true),
        T_DollarDoubleQuoted(_) => Some(true),
        T_CaseExpression { .. } => Some(true),
        T_HereDoc { .. } => Some(true),
        T_DollarBraced { .. } => Some(true),
        // strict == False: pragmatically assume splitting is desirable here.
        T_ForIn { .. } => Some(true),
        T_SelectIn { .. } => Some(true),
        // A `name=...` argument word to a declaration utility (declare/export/
        // local/readonly/typeset). ShellCheck's parser reads these as
        // T_Assignment nodes; this parser keeps them as plain words, so the
        // equivalent quoting context (`assignmentIsQuoting` on a command
        // parameter = shell parses params as assignments = shell /= Sh) is
        // reconstructed here.
        T_NormalWord(_) if is_declaration_assignment_word(p, t) => Some(p.shell != Shell::Sh),
        _ => None,
    }
}

/// True if `word` is a `name=` / `name+=` argument to a declaration utility.
fn is_declaration_assignment_word(p: &Parameters, word: &Token) -> bool {
    let is_form = match &*word.inner {
        InnerToken::T_NormalWord(parts) => parts.first().map_or(false, |f| {
            matches!(&*f.inner, InnerToken::T_Literal(s) if literal_is_assignment_prefix(s))
        }),
        _ => false,
    };
    if !is_form {
        return false;
    }
    let parent = match p.parent(word) {
        Some(x) => x,
        None => return false,
    };
    if let InnerToken::T_SimpleCommand { words, .. } = &*parent.inner {
        if words.is_empty() || !words[1..].iter().any(|w| w.id() == word.id()) {
            return false;
        }
        return matches!(
            decl_command_name(words).as_deref(),
            Some("declare") | Some("export") | Some("local") | Some("readonly") | Some("typeset")
        );
    }
    false
}

fn decl_command_name(words: &[Token]) -> Option<String> {
    let n0 = get_literal_string(&words[0])?;
    if n0 == "builtin" && words.len() >= 2 {
        Some(only_literal_string(&words[1]))
    } else {
        Some(n0)
    }
}

/// `name` / `name+` followed by `=` at the start of a literal.
fn literal_is_assignment_prefix(s: &str) -> bool {
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

/// `assignmentIsQuoting`: recognized assignment passed to a declaration utility.
fn assignment_is_quoting(p: &Parameters, assign: &Token) -> bool {
    // shellParsesParamsAsAssignments = shell /= Sh
    if p.shell != Shell::Sh {
        return true;
    }
    !is_assignment_param_to_command(p, assign)
}

fn is_assignment_param_to_command(p: &Parameters, assign: &Token) -> bool {
    if let Some(parent) = p.parent(assign) {
        if let InnerToken::T_SimpleCommand { words, .. } = &*parent.inner {
            if !words.is_empty() {
                return words[1..].iter().any(|w| w.id() == assign.id());
            }
        }
    }
    false
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
                if words[0].id() == current_id
                    || get_command_token_or_this(t).id() == current_id
                {
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
    matches!(get_command_name_from_expansion(t).as_deref(), Some("seq") | Some("pgrep"))
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
        let base = basename(&name);
        basename_dispatch(p, &base, &words[1..], out);
    } else if name == "builtin" && words.len() >= 2 {
        let selected = only_literal_string(&words[1]);
        exactly_dispatch(p, &selected, &words[2..], out);
    } else {
        exactly_dispatch(p, &name, &words[1..], out);
        basename_dispatch(p, &name, &words[1..], out);
    }
}

fn exactly_dispatch(p: &Parameters, name: &str, args: &[Token], out: &mut Out) {
    if name == "printf" {
        check_printf(p, args, out);
    }
}

fn basename_dispatch(p: &Parameters, name: &str, args: &[Token], out: &mut Out) {
    if name == "tr" {
        check_tr(args, out);
    }
}

// ---- SC2060 checkTr (only the glob branch) ---------------------------------

fn check_tr(args: &[Token], out: &mut Out) {
    for w in args {
        if is_glob(w) {
            warn(out, w.id(), 2060, "Quote parameters to tr to prevent glob expansion.");
        }
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

fn check_printf_format(p: &Parameters, format: &Token, more: &[Token], out: &mut Out) {
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
            let pl_var = if format_count == 1 { "variable" } else { "variables" };
            let pl_arg = if arg_count == 1 { "argument" } else { "arguments" };
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

fn may_become_multiple_args(t: &Token) -> bool {
    will_become_multiple_args(t) || mbma_f(false, t)
}
fn mbma_f(quoted: bool, t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { op, .. } => {
            let string = concat_over(op);
            !quoted || string.starts_with('!')
        }
        T_DoubleQuoted(parts) => parts.iter().any(|x| mbma_f(true, x)),
        T_NormalWord(parts) => parts.iter().any(|x| mbma_f(quoted, x)),
        _ => false,
    }
}

fn will_become_multiple_args(t: &Token) -> bool {
    will_concat_in_assignment(t) || wbma_f(t)
}
fn wbma_f(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_Extglob { .. } => true,
        T_Glob(_) => true,
        T_BraceExpansion(_) => true,
        T_NormalWord(parts) => parts.iter().any(wbma_f),
        _ => false,
    }
}
fn will_concat_in_assignment(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => is_array_expansion(t),
        T_DoubleQuoted(parts) => parts.iter().any(will_concat_in_assignment),
        T_NormalWord(parts) => parts.iter().any(will_concat_in_assignment),
        _ => false,
    }
}
fn is_array_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let string = concat_over(op);
            string.starts_with('@') || (!string.starts_with('#') && string.contains("[@]"))
        }
        _ => false,
    }
}

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
        while rest.get(i).map_or(false, |c| c.is_ascii_digit()) {
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
        while rest.get(i).map_or(false, |c| c.is_ascii_digit()) {
            i += 1;
        }
    }
    // length modifier (hh|h|l|ll|q|L|j|z|Z|t)? — greedy, but only if a type char
    // then follows (regex backtracking). Alternation preference order preserved.
    let type_at = |j: usize| -> Option<char> {
        rest.get(j).copied().filter(|c| PRINTF_TYPE_CHARS.contains(*c))
    };
    let mods = ["hh", "h", "l", "ll", "q", "L", "j", "z", "Z", "t"];
    let mut chosen_len = 0usize;
    for m in mods {
        let mc: Vec<char> = m.chars().collect();
        if i + mc.len() <= rest.len() && rest[i..i + mc.len()] == mc[..] && type_at(i + mc.len()).is_some() {
            chosen_len = mc.len();
            break;
        }
    }
    let type_pos = i + chosen_len;
    let typ = type_at(type_pos)?;
    Some((width_star, prec_star, typ, &rest[type_pos + 1..]))
}
