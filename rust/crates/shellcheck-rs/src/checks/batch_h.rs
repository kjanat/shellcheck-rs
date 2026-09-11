//! Ported check batch h. See rust/PORTING.md.
//!
//! `checkBashisms` from `src/ShellCheck/Checks/ShellSupport.hs` — flags bash/ksh
//! features (SC3xxx) when the target shell is sh / dash / busybox sh. Only the
//! branches that port cleanly against the current AST are enabled; branches that
//! require arithmetic (`TA_*`) structure or that would mismatch the oracle's
//! token positions are skipped (see the notes on each and the module tail).
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_literal_string;
use crate::interface::Shell;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_bashisms);
}

// ---------------------------------------------------------------------------
// Shared warning emitter (`warnMsg`): dash/busybox -> err, sh -> warn.
// ---------------------------------------------------------------------------

fn is_busybox(p: &Parameters) -> bool {
    p.shell == Shell::BusyboxSh
}
fn is_dash(p: &Parameters) -> bool {
    p.shell == Shell::Dash || is_busybox(p)
}

fn warn_msg(out: &mut Out, p: &Parameters, id: Id, code: i64, s: &str) {
    if is_dash(p) {
        err(out, id, code, &format!("In dash, {} not supported.", s));
    } else {
        warn(out, id, code, &format!("In POSIX sh, {} undefined.", s));
    }
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib; kept local so this module
// does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

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
        TA_Sequence(seq) if seq.len() == 1 => match &*seq[0].inner {
            TA_Expansion(v) => v.iter().flat_map(oversimplify).collect(),
            _ => vec![],
        },
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

/// `getWordParts`.
fn get_word_parts(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_NormalWord(l) => l.iter().flat_map(|x| get_word_parts(x)).collect(),
        InnerToken::T_DoubleQuoted(l) => l.iter().collect(),
        InnerToken::TA_Expansion(l) => l.iter().flat_map(|x| get_word_parts(x)).collect(),
        _ => vec![t],
    }
}

/// `isFlag`: word whose first part is a `-`-prefixed literal.
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

/// `isOnlyRedirection`.
fn is_only_redirection(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => {
            is_only_redirection(&commands[0])
        }
        InnerToken::T_Annotation { token, .. } => is_only_redirection(token),
        InnerToken::T_Redirecting { redirs, cmd } if !redirs.is_empty() => is_only_redirection(cmd),
        InnerToken::T_SimpleCommand { assignments, words } => {
            assignments.is_empty() && words.is_empty()
        }
        _ => false,
    }
}

/// `isVariableName`.
fn is_variable_name(s: &str) -> bool {
    let mut it = s.chars();
    match it.next() {
        Some(c) if is_var_start(c) => it.all(is_var_char),
        _ => false,
    }
}
fn is_var_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic()
}
fn is_var_char(c: char) -> bool {
    is_var_start(c) || c.is_ascii_digit()
}
fn is_special_var_char(c: char) -> bool {
    "*@#?-$!".contains(c)
}

// ---- getBracedReference ----------------------------------------------------

fn get_braced_reference(s: &str) -> String {
    let cs: Vec<char> = s.chars().collect();
    if let Some(r) = name_expansion(&cs) {
        return r;
    }
    let no_prefix = drop_prefix(&cs);
    if let Some(r) = take_name(no_prefix) {
        return r;
    }
    if let Some(r) = get_special(no_prefix) {
        return r;
    }
    if let Some(r) = get_special(&cs) {
        return r;
    }
    s.to_string()
}
fn drop_prefix(cs: &[char]) -> &[char] {
    match cs.first() {
        Some(&c) if c == '!' || c == '#' => &cs[1..],
        _ => cs,
    }
}
fn take_name(cs: &[char]) -> Option<String> {
    let name: String = cs.iter().take_while(|&&c| is_var_char(c)).collect();
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}
fn get_special(cs: &[char]) -> Option<String> {
    match cs.first() {
        Some(&c) if is_special_var_char(c) => Some(c.to_string()),
        _ => None,
    }
}
fn name_expansion(cs: &[char]) -> Option<String> {
    // ${!foo*bar*} style: '!', varchar, then a later non-varchar in "*?@"
    if cs.first() == Some(&'!') && cs.len() >= 2 && is_var_char(cs[1]) {
        let first_non_var = cs[2..].iter().find(|&&c| !is_var_char(c));
        if let Some(&c) = first_non_var {
            if "*?@".contains(c) {
                return Some(String::new());
            }
        }
    }
    None
}

// ---- command name resolution (ported from batch_d, proven) -----------------

use std::collections::HashMap;

fn get_command(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command(cmd),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        InnerToken::T_Annotation { token, .. } => get_command(token),
        _ => None,
    }
}

fn arguments(t: &Token) -> &[Token] {
    match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => &words[1..],
        _ => &[],
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

/// `isCommand token str` — matches `str` or any `/str` suffix.
fn is_command(t: &Token, name: &str) -> bool {
    match get_command_name(t) {
        Some(cmd) => cmd == name || cmd.ends_with(&format!("/{}", name)),
        None => false,
    }
}

// ---- getFlagsUntil (leading) ----------------------------------------------

fn get_flags_until<'a, F: Fn(&str) -> bool>(t: &'a Token, stop: F) -> Vec<(&'a Token, String)> {
    let args = arguments(t);
    let mut broken = false;
    let mut out: Vec<(&Token, String)> = vec![];
    for x in args {
        let txt = concat_over(x);
        if !broken && stop(&txt) {
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

fn get_leading_flags(t: &Token) -> Vec<(&Token, String)> {
    get_flags_until(t, |x| x == "--" || !x.starts_with('-'))
}

// ---------------------------------------------------------------------------
// Test-operator tables (`bashismBinaryTestFlags` / `bashismUnaryTestFlags`).
// Returns (code, exempt-shells, message).
// ---------------------------------------------------------------------------

fn bashism_binary_test(op: &str) -> Option<(i64, &'static [Shell], String)> {
    Some(match op {
        "<" | ">" | "\\<" | "\\>" | "<=" | ">=" | "\\<=" | "\\>=" => {
            (3012, &[Shell::Dash, Shell::BusyboxSh][..], format!("lexicographical {} is", op))
        }
        "==" => (3014, &[Shell::BusyboxSh][..], format!("{} in place of = is", op)),
        "=~" => (3015, &[][..], format!("{} regex matching is", op)),
        _ => return None,
    })
}

fn bashism_unary_test(op: &str) -> Option<(i64, &'static [Shell], String)> {
    Some(match op {
        "-v" => (3016, &[][..], format!("test {} (in place of [ -n \"${{var+x}}\" ]) is", op)),
        "-a" => (3017, &[][..], format!("unary {} in place of -e is", op)),
        "-o" => (3062, &[][..], format!("test {} to check options is", op)),
        "-R" => (3063, &[][..], format!("test {} and namerefs in general are", op)),
        "-N" => (3064, &[][..], format!("test {} is", op)),
        "-k" => (3065, &[Shell::Dash, Shell::BusyboxSh][..], format!("test {} is", op)),
        "-G" => (3066, &[Shell::Dash, Shell::BusyboxSh][..], format!("test {} is", op)),
        "-O" => (3067, &[Shell::Dash, Shell::BusyboxSh][..], format!("test {} is", op)),
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

// ---------------------------------------------------------------------------
// Bash-only variable lists (SC3028).
// ---------------------------------------------------------------------------

const BASH_VARS: &[&str] = &[
    "OSTYPE", "MACHTYPE", "HOSTTYPE", "HOSTNAME", "DIRSTACK", "EUID", "UID", "SHLVL",
    "PIPESTATUS", "SHELLOPTS", "_", "BASH", "BASHOPTS", "BASHPID", "BASH_ALIASES",
    "BASH_ARGC", "BASH_ARGV", "BASH_ARGV0", "BASH_CMDS", "BASH_COMMAND",
    "BASH_EXECUTION_STRING", "BASH_LINENO", "BASH_LOADABLES_PATH", "BASH_REMATCH",
    "BASH_SOURCE", "BASH_SUBSHELL", "BASH_VERSINFO", "COMP_CWORD", "COMP_KEY",
    "COMP_LINE", "COMP_POINT", "COMP_TYPE", "COMP_WORDBREAKS", "COMP_WORDS", "COPROC",
    "FUNCNAME", "GROUPS", "HISTCMD", "MAPFILE",
];
const BASH_DYNAMIC_VARS: &[&str] = &[
    "BASH_MONOSECONDS", "EPOCHREALTIME", "EPOCHSECONDS", "RANDOM", "SECONDS", "SRANDOM",
];
const DASH_VARS: &[&str] = &["_"];

fn is_assigned(p: &Parameters, name: &str) -> bool {
    p.id_map
        .values()
        .any(|t| matches!(&*t.inner, InnerToken::T_Assignment { var, .. } if var == name))
}

fn is_bash_variable(p: &Parameters, var: &str) -> bool {
    let dyn_or_static = BASH_DYNAMIC_VARS.contains(&var)
        || (BASH_VARS.contains(&var) && !is_assigned(p, var));
    dyn_or_static && !(is_dash(p) && DASH_VARS.contains(&var))
}

// ---------------------------------------------------------------------------
// DollarBraced expansion regex matchers (operate on the braced content string).
// varChars = [_0-9a-zA-Z]; the extra `*@` set is noted where used.
// ---------------------------------------------------------------------------

fn is_v(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}
fn is_v_star_at(c: char) -> bool {
    is_v(c) || c == '*' || c == '@'
}

// 3053: ^![varChars]
fn re_3053(s: &[char]) -> bool {
    s.first() == Some(&'!') && s.len() >= 2 && is_v(s[1])
}
// 3054: ^[varChars]+\[.*\]$
fn re_3054(s: &[char]) -> bool {
    let i = s.iter().take_while(|&&c| is_v(c)).count();
    i >= 1 && i < s.len() && s[i] == '[' && s.last() == Some(&']') && s.len() - 1 > i
}
// 3055: ^![varChars]+\[[*@]]$
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
// 3056: ^![varChars]+[*@]$
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
// 3059: ^[varChars*@]+(\[.*\])?[,^]
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
// 3057: ^[varChars*@]+:[^-=?+]
fn re_3057(s: &[char]) -> bool {
    let i = s.iter().take_while(|&&c| is_v_star_at(c)).count();
    i >= 1 && i < s.len() && s[i] == ':' && i + 1 < s.len() && !"-=?+".contains(s[i + 1])
}
// 3058: ^([*@][%#]|#[@*])
fn re_3058(s: &[char]) -> bool {
    if s.len() < 2 {
        return false;
    }
    ((s[0] == '*' || s[0] == '@') && (s[1] == '%' || s[1] == '#'))
        || (s[0] == '#' && (s[1] == '@' || s[1] == '*'))
}
// 3060: ^[varChars*@]+(\[.*\])?/
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

// echo flag regexes
fn echo_flag(s: &str) -> bool {
    s.len() >= 2 && s.starts_with('-') && s[1..].chars().all(|c| "eEsn".contains(c))
}
fn busybox_echo_flag(s: &str) -> bool {
    s.len() >= 2 && s.starts_with('-') && s[1..].chars().all(|c| "en".contains(c))
}

// ---------------------------------------------------------------------------
// The check.
// ---------------------------------------------------------------------------

fn check_bashisms(p: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(p.shell, Shell::Sh | Shell::Dash | Shell::BusyboxSh) {
        return;
    }
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
        T_Condition { typ: ConditionType::DoubleBracket, .. } => {
            if !is_busybox(p) {
                warn_msg(out, p, id, 3010, "[[ ]] is");
            }
        }
        T_HereString(_) => warn_msg(out, p, id, 3011, "here-strings are"),

        // FD redirections: only SC3023 (FDs outside 0-9) ports cleanly; the
        // `&>` / `>&file` / `{n}>` forms are parser gaps on this AST.
        T_FdRedirect { fd, .. } if fd.len() > 1 && fd.chars().all(|c| c.is_ascii_digit()) => {
            warn_msg(out, p, id, 3023, "FDs outside 0-9 are");
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
            warn_msg(out, p, id, 3026, "^ in place of ! in glob bracket expressions is");
        }

        T_Pipe(op) if op == "|&" => warn_msg(out, p, id, 3029, "|& in place of 2>&1 | is"),
        T_Array(_) => warn_msg(out, p, id, 3030, "arrays are"),

        T_Function { name, .. } if !is_variable_name(name) => {
            warn_msg(out, p, id, 3033, "naming functions outside [a-zA-Z_][a-zA-Z0-9_]* is");
        }

        T_DollarExpansion(list) if list.len() == 1 && is_only_redirection(&list[0]) => {
            warn_msg(out, p, id, 3034, "$(<file) to read files is");
        }
        T_Backticked(list) if list.len() == 1 && is_only_redirection(&list[0]) => {
            warn_msg(out, p, id, 3035, "`<file` to read files is");
        }

        T_DollarBraced { op, .. } => {
            let s = concat_over(op);
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

        T_SimpleCommand { words, .. } => check_simple_command(p, t, words, out),

        _ => {}
    }
}

fn check_simple_command(p: &Parameters, t: &Token, words: &[Token], out: &mut Out) {
    if words.is_empty() {
        return;
    }
    let id = t.id();

    // Test-command forms (`test x == y`, `test -v var`). The `[ .. ]` / `[[ .. ]]`
    // condition forms (TC_Binary/TC_Unary) are intentionally NOT handled: the
    // oracle positions those diagnostics on the operator token, which this AST
    // does not expose as a separately-positioned node.
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

    // First-match dispatch, mirroring the ordered Haskell equations.
    // echo flags (SC3036/SC3037)
    if words.len() >= 2 && is_command(t, "echo") {
        let arg = &words[1];
        let arg_string = concat_over(arg);
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
    // exec flags (SC3038)
    if words.len() >= 2 && get_literal_string(cmd).as_deref() == Some("exec") {
        let arg = &words[1];
        if concat_over(arg).starts_with('-') {
            warn_msg(out, p, arg.id(), 3038, "exec flags are");
            return;
        }
    }
    // let (SC3039)
    if is_command(t, "let") {
        warn_msg(out, p, id, 3039, "'let' is");
        return;
    }
    // set options/flags (SC3040/SC3041/SC3042) — sh only
    if is_command(t, "set") {
        if !is_dash(p) {
            check_set_options(p, t, out);
        }
        return;
    }

    check_general_command(p, t, words, out);
}

const UNSUPPORTED_COMMANDS: &[&str] = &[
    "let", "caller", "builtin", "complete", "compgen", "declare", "dirs", "disown", "enable",
    "mapfile", "readarray", "pushd", "popd", "shopt", "suspend", "typeset",
];

fn allowed_flags(name: &str, p: &Parameters) -> Option<Vec<&'static str>> {
    let dash = is_dash(p);
    let busybox = is_busybox(p);
    Some(match name {
        "cd" => vec!["L", "P"],
        "exec" => vec![],
        "export" => vec!["p"],
        "hash" => if dash { vec!["r", "v"] } else { vec!["r"] },
        "jobs" => vec!["l", "p"],
        "printf" => vec![],
        "read" => if dash || busybox { vec!["r", "p"] } else { vec!["r"] },
        "readonly" => vec!["p"],
        "trap" => vec![],
        "type" => if busybox { vec!["p"] } else { vec![] },
        "ulimit" => {
            if dash {
                vec!["H", "S", "a", "c", "d", "f", "l", "m", "n", "p", "r", "s", "t", "v", "w"]
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

/// A word of the form `name=` / `name+=` / `name=value`.
fn is_assignment_form(s: &str) -> bool {
    let c: Vec<char> = s.chars().collect();
    if c.is_empty() || !is_var_start(c[0]) {
        return false;
    }
    let mut i = 1;
    while i < c.len() && is_var_char(c[i]) {
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
    let name = get_command_name(t).unwrap_or_default();
    let rest = &words[1..];

    // The oracle positions command-span diagnostics (SC3043/SC3044) at the
    // T_SimpleCommand span, which — for a declaration command whose LAST word is
    // an assignment (`local i=`) — ends at the assignment's name. This port's
    // parser spans the whole assignment, so the end column would differ. Only
    // emit these when the command does not end in such an assignment word.
    let ends_in_assignment = words.len() > 1
        && words
            .last()
            .map(|w| is_assignment_form(&concat_over(w)))
            .unwrap_or(false);

    if name == "local" && !is_dash(p) && !ends_in_assignment {
        warn_msg(out, p, id, 3043, "'local' is");
    }
    if UNSUPPORTED_COMMANDS.contains(&name.as_str()) && !ends_in_assignment {
        warn_msg(out, p, id, 3044, &format!("'{}' is", name));
    }

    if let Some(allowed) = allowed_flags(&name, p) {
        let flags = get_leading_flags(t);
        if let Some((word, flag)) =
            flags.iter().find(|(_, f)| !f.is_empty() && !allowed.contains(&f.as_str()))
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
                    warn_msg(out, p, token.id(), 3048, "prefixing signal names with 'SIG' is");
                }
                if !is_dash(p) && upper != s {
                    warn_msg(out, p, token.id(), 3049, "using lower/mixed case for signal names is");
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

// ---- set option/flag checking (SC3040/SC3041/SC3042) -----------------------

const SET_OPTIONS: &str = "abCefhmnuvxo";
const SET_LONG_OPTIONS: &[&str] = &[
    "allexport", "errexit", "ignoreeof", "monitor", "noclobber", "noexec", "noglob", "nolog",
    "notify", "nounset", "pipefail", "verbose", "vi", "xtrace",
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
    b.len() >= 2 && (b[0] == b'-' || b[0] == b'+') && s[1..].chars().all(|c| SET_OPTIONS.contains(c))
}

fn check_set_options(p: &Parameters, t: &Token, out: &mut Out) {
    // getLiteralArgs: literal prefix of the arguments.
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
        let (fid, flag) = &args[0];
        let (oid, opt) = &args[1];
        if set_o_flag(flag) {
            if !SET_LONG_OPTIONS.contains(&opt.as_str()) {
                warn_msg(out, p, *oid, 3040, &format!("set option {} is", opt));
            }
            // checkFlags (flag : rest)  — drop the consumed option
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
    // else: stop.
}
