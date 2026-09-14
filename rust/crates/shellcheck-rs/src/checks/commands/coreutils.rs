//! Checks on external commands, from `ShellCheck.Checks.Commands`.
use super::common::*;
use super::{CommandCheck, CommandName::*};
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::find_grep_regex;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::is_confused_glob_regex;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib::get_word_parts;
use crate::ast_lib::is_constant;
use crate::ast_lib::is_glob;
use crate::ast_lib::only_literal_string;
use crate::ast_lib::oversimplify_concat;
use crate::ast_lib::will_split;
use crate::ast_lib::{get_literal_string, get_literal_string_ext};

use crate::ast_lib;

use crate::cfg::get_bsd_opts;
use crate::cfg::may_become_multiple_args;
use crate::data::SAMPLE_WORDS;
use crate::interface::Shell;
use std::sync::OnceLock;

pub(super) fn check_tr() -> CommandCheck {
    CommandCheck::new(Basename("tr"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        for w in word_args(words) {
            tr_arg(w, out);
        }
    })
}

pub(super) fn check_expr() -> CommandCheck {
    CommandCheck::new(Basename("expr"), |_params, te, out| {
        let args = arguments(te);

        let literal_args: Vec<String> = args
            .iter()
            .filter_map(ast_lib::get_literal_string)
            .collect();
        if literal_args
            .iter()
            .all(|x| !EXPR_EXCEPTIONS.contains(&x.as_str()))
        {
            style(
                out,
                get_command_token_or_this(te).id(),
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
                if ast_lib::only_literal_string(first) != "length"
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
    })
}

pub(super) fn check_grep_re() -> CommandCheck {
    CommandCheck::new(Basename("grep"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let re = match find_grep_regex(word_args(words)) {
            Some(re) => re,
            None => return,
        };

        if is_glob(re) {
            warn(
                out,
                re.id(),
                2062,
                "Quote the grep pattern so the shell won't interpret it.",
            );
        }

        let flags: Vec<String> = word_flags(words).into_iter().map(|(_, f)| f).collect();
        if !GREP_GLOB_FLAGS.iter().any(|g| flags.iter().any(|f| f == g)) {
            let string = oversimplify_concat(re);
            if is_confused_glob_regex(&string) {
                warn(
                    out,
                    re.id(),
                    2063,
                    "Grep uses regex, but this looks like a glob.",
                );
            } else if let Some(c) = get_suspicious_regex_wildcard(&string) {
                info(
                    out,
                    re.id(),
                    2022,
                    &format!(
                        "Note that unlike globs, {0}* here matches '{0}{0}{0}' but not '{1}'.",
                        c,
                        word_starting_with(c)
                    ),
                );
            }
        }
    })
}

pub(super) fn check_unused_echo_escapes() -> CommandCheck {
    CommandCheck::new(Basename("echo"), |params, t, out| {
        if !matches!(params.shell, Shell::Sh | Shell::Bash | Shell::Ksh) {
            return;
        }
        let Some(words) = simple_command_words(t) else {
            return;
        };
        let args = &words[1..];
        if has_e_flag(args) {
            return;
        }
        for token in args {
            let str = only_literal_string(token);
            if echo_escapes_re().is_match(&str) {
                info(
                    out,
                    token.id(),
                    2028,
                    "echo may not expand escape sequences. Use printf.",
                );
            }
        }
    })
}

pub(super) fn check_mkdir_dash_pm() -> CommandCheck {
    CommandCheck::new(Basename("mkdir"), |_params, t, out| {
        let flags = get_all_flags(t);
        let has_dash_p = flags.iter().any(|(_, f)| f == "p" || f == "parents");
        let dash_m = flags.iter().find(|(_, f)| f == "m" || f == "mode");
        if !has_dash_p {
            return;
        }
        let dash_m = match dash_m {
            Some(m) => m,
            None => return,
        };
        // guard: any couldHaveSubdirs (drop 1 $ arguments t)
        let args = arguments(t);
        let tail = if args.len() > 1 { &args[1..] } else { &[][..] };
        if tail.iter().any(could_have_subdirs) {
            warn(
                out,
                dash_m.0.id(),
                2174,
                "When used with -p, -m only applies to the deepest directory.",
            );
        }
    })
}

pub(super) fn check_interactive_su() -> CommandCheck {
    CommandCheck::new(Basename("su"), |params, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        if word_args(words).len() <= 1 {
            let path = get_path(params, t);
            if path.iter().all(|n| su_undirected(n)) {
                info(
                    out,
                    t.id(),
                    2117,
                    "To run commands as another user, use su -c or sudo.",
                );
            }
        }
    })
}

pub(super) fn check_ssh_command_string() -> CommandCheck {
    CommandCheck::new(Basename("ssh"), |_params, te, out| {
        let args = arguments(te);
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
    })
}

pub(super) fn check_uuoe_cmd() -> CommandCheck {
    CommandCheck::new(Exactly("echo"), |_params, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        if let Some(args) = echo_arguments(words) {
            if args.len() == 1 && token_is_just_command_output(&args[0]) {
                style(
                    out,
                    args[0].id(),
                    2005,
                    "Useless echo? Instead of 'echo $(cmd)', just use 'cmd'.",
                );
            }
        }
    })
}

pub(super) fn check_time_parameters() -> CommandCheck {
    CommandCheck::new(Exactly("time"), |p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        // f (T_SimpleCommand _ _ (cmd:args:_))
        if words.len() < 2 {
            return;
        }
        if !when_shell(p, &[Shell::Bash, Shell::Sh]) {
            return;
        }
        let cmd = &words[0];
        let s = oversimplify_concat(&words[1]);
        if s.starts_with('-') && s != "-p" {
            info(
                out,
                cmd.id(),
                2023,
                "The shell may override 'time' as seen in man time(1). Use 'command time ..' for that one.",
            );
        }
    })
}

pub(super) fn check_timed_command() -> CommandCheck {
    CommandCheck::new(Exactly("time"), |p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        // f (T_SimpleCommand _ _ (c:args@(_:_)))
        let args = word_args(words);
        if args.is_empty() {
            return;
        }
        if !when_shell(p, &[Shell::Sh, Shell::Dash, Shell::BusyboxSh]) {
            return;
        }
        let c = &words[0];
        let cmd = args.last().unwrap(); // "time" is parsed with a command as argument
        if timed_is_piped(cmd) {
            warn(
                out,
                c.id(),
                2176,
                "'time' is undefined for pipelines. time single stage or bash -c instead.",
            );
        }
        if timed_is_simple(cmd) == Some(false) {
            warn(
                out,
                cmd.id(),
                2177,
                "'time' is undefined for compound commands, time sh -c instead.",
            );
        }
    })
}

pub(super) fn check_deprecated_tempfile() -> CommandCheck {
    CommandCheck::new(Basename("tempfile"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        warn(
            out,
            words[0].id(),
            2186,
            "tempfile is deprecated. Use mktemp instead.",
        );
    })
}

pub(super) fn check_deprecated_egrep() -> CommandCheck {
    CommandCheck::new(Basename("egrep"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        info(
            out,
            words[0].id(),
            2196,
            "egrep is non-standard and deprecated. Use grep -E instead.",
        );
    })
}

pub(super) fn check_deprecated_fgrep() -> CommandCheck {
    CommandCheck::new(Basename("fgrep"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        info(
            out,
            words[0].id(),
            2197,
            "fgrep is non-standard and deprecated. Use grep -F instead.",
        );
    })
}

pub(super) fn check_catastrophic_rm() -> CommandCheck {
    CommandCheck::new(Basename("rm"), |_params, t, out| {
        let recursive = get_all_flags(t)
            .iter()
            .any(|(_, f)| f == "r" || f == "R" || f == "recursive");
        if !recursive {
            return;
        }
        let important = important_paths();
        // `mapM_ (mapM_ checkWord . braceExpand) $ arguments t`
        for arg in arguments(t) {
            for word in ast_lib::brace_expand(arg) {
                check_rm_word(&word, &important, out);
            }
        }
    })
}

pub(super) fn check_mv_arguments() -> CommandCheck {
    CommandCheck::new(Basename("mv"), |_params, te, out| {
        missing_destination(te, out, |o, id| {
            err(
                o,
                id,
                2224,
                "This mv has no destination. Check the arguments.",
            );
        });
    })
}

pub(super) fn check_cp_arguments() -> CommandCheck {
    CommandCheck::new(Basename("cp"), |_params, te, out| {
        missing_destination(te, out, |o, id| {
            err(
                o,
                id,
                2225,
                "This cp has no destination. Check the arguments.",
            );
        });
    })
}

pub(super) fn check_ln_arguments() -> CommandCheck {
    CommandCheck::new(Basename("ln"), |_params, te, out| {
        missing_destination(te, out, |o, id| {
            warn(
                o,
                id,
                2226,
                "This ln has no destination. Check the arguments, or specify '.' explicitly.",
            );
        });
    })
}

pub(super) fn check_chmod_dashr() -> CommandCheck {
    CommandCheck::new(Basename("chmod"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        for a in word_args(words) {
            if get_literal_string(a).as_deref() == Some("-r") {
                warn(
                    out,
                    a.id(),
                    2253,
                    "Use -R to recurse, or explicitly a-r to remove read permissions.",
                );
            }
        }
    })
}

pub(super) fn check_xargs_dashi() -> CommandCheck {
    CommandCheck::new(Basename("xargs"), |_p, t, out| {
        let Some(words) = simple_command_words(t) else {
            return;
        };
        if let Some(opts) = get_bsd_opts("0oprtxadR:S:J:L:l:n:P:s:e:E:i:I:", word_args(words)) {
            if let Some((_, (option, _))) = opts.iter().find(|(name, _)| name == "i") {
                info(
                    out,
                    option.id(),
                    2267,
                    "GNU xargs -i is deprecated in favor of -I{}",
                );
            }
        }
    })
}

pub(super) fn check_unquoted_echo_spaces() -> CommandCheck {
    CommandCheck::new(Basename("echo"), |params, t, out| {
        let args = arguments(t);
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

        let has_spaces_between =
            |first: &(crate::interface::Position, crate::interface::Position),
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
    })
}

/// Effective argument list of an `echo` command per the CommandCheck dispatch:
/// the first word literal must be exactly "echo" (no slash → `Basename`
/// dispatch, which is a different check), with a `builtin echo` re-dispatch.
fn echo_arguments(words: &[Token]) -> Option<&[Token]> {
    let (cmd, rest) = words.split_first()?;
    let name = ast_lib::get_literal_string(cmd)?;
    if name.contains('/') {
        return None; // dispatched via Basename, not Exactly "echo"
    }
    if name == "builtin" {
        let (h, tail) = rest.split_first()?;
        if only_literal_string(h) == "echo" {
            return Some(tail);
        }
        return None;
    }
    if name == "echo" {
        return Some(rest);
    }
    None
}

/// `re = ^(\.\.?/)+[^/]+$` — one-or-more `../`/`./` segments then a single
/// non-slash path component.
fn matches_dotdot_re(name: &str) -> bool {
    let mut s = name;
    let mut count = 0usize;
    loop {
        if let Some(r) = s.strip_prefix("../") {
            s = r;
            count += 1;
        } else if let Some(r) = s.strip_prefix("./") {
            s = r;
            count += 1;
        } else {
            break;
        }
    }
    count >= 1 && !s.is_empty() && !s.contains('/')
}

fn could_have_subdirs(t: &Token) -> bool {
    match get_literal_string(t) {
        None => true,
        Some(name) => name.contains('/') && !matches_dotdot_re(&name),
    }
}

fn important_paths() -> Vec<String> {
    let paths = [
        "",
        "/bin",
        "/etc",
        "/home",
        "/mnt",
        "/usr",
        "/usr/share",
        "/usr/local",
        "/var",
        "/lib",
        "/dev",
        "/media",
        "/boot",
        "/lib64",
        "/usr/bin",
    ];
    let suffixes = ["", "/", "/*", "/*/*"];
    let mut out = vec![];
    for x in suffixes {
        for p in paths {
            let s = format!("{}{}", p, x);
            if !s.is_empty() {
                out.push(s);
            }
        }
    }
    out
}

/// `skipRepeating c`: collapse consecutive runs of `c` down to a single `c`.
fn skip_repeating(c: char, s: &str) -> String {
    let mut out = String::new();
    let mut prev_was_c = false;
    for ch in s.chars() {
        if ch == c && prev_was_c {
            continue;
        }
        out.push(ch);
        prev_was_c = ch == c;
    }
    out
}

fn fix_path(filename: &str) -> String {
    let normalized = skip_repeating('/', &skip_repeating('*', filename));
    if normalized == "/" {
        normalized
    } else {
        normalized.trim_end_matches('/').to_string()
    }
}

/// `getPotentialPath = getLiteralStringExt f` where globs contribute their glob
/// text and `${var}` contributes "" (unless it has a `:?`/`:-`/`:=` default).
fn get_potential_path(token: &Token) -> Option<String> {
    get_literal_string_ext(token, &|inner: &InnerToken| match inner {
        InnerToken::T_Glob(s) => Some(s.clone()),
        // `checkCatastrophicRm` brace-expands each argument first, so a
        // `T_BraceExpansion` node never reaches `getPotentialPath`; the faithful
        // fallback treats everything unlisted as "".
        InnerToken::T_DollarBraced { op, .. } => {
            let var = get_literal_string_ext(op, &|_| Some(String::new())).unwrap_or_default();
            if var.contains(":?") || var.contains(":-") || var.contains(":=") {
                None
            } else {
                Some(String::new())
            }
        }
        _ => Some(String::new()),
    })
}

fn check_rm_word(token: &Token, important: &[String], out: &mut Out) {
    match get_literal_string(token) {
        Some(s) => {
            if important.iter().any(|p| p == &fix_path(&s)) {
                warn(
                    out,
                    token.id(),
                    2114,
                    "Warning: deletes a system directory.",
                );
            }
        }
        None => {
            if let Some(filename) = get_potential_path(token) {
                let path = fix_path(&filename);
                if important.iter().any(|p| p == &path) {
                    warn(
                        out,
                        token.id(),
                        2115,
                        &format!(
                            "Use \"${{var:?}}\" to ensure this never expands to {} .",
                            path
                        ),
                    );
                }
            }
        }
    }
}

fn echo_escapes_re() -> &'static regex::Regex {
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"\\([rntabefv']|[0-7]{1,3}|x[0-9A-Fa-f]{1,2})").unwrap())
}

/// Does the command have short flag `e` (before `--`)?
fn has_e_flag(args: &[Token]) -> bool {
    for arg in args {
        let text = only_literal_string(arg);
        if text == "--" {
            break;
        }
        if text.starts_with("--") {
            // long option; not a short 'e'
        } else if let Some(short) = text.strip_prefix('-') {
            if short.contains('e') {
                return true;
            }
        }
    }
    false
}

/// `getPath`: `t` followed by its ancestors up to the root.
fn get_path<'a>(params: &'a Parameters, t: &'a Token) -> Vec<&'a Token> {
    let mut out = vec![t];
    let mut cur = t;
    while let Some(p) = params.parent(cur) {
        out.push(p);
        cur = p;
    }
    out
}

fn when_shell(p: &Parameters, shells: &[Shell]) -> bool {
    shells.contains(&p.shell)
}

fn tr_arg(word: &Token, out: &mut Out) {
    if is_glob(word) {
        // The user will go [ab] -> '[ab]' -> 'ab'. Fixme?
        warn(
            out,
            word.id(),
            2060,
            "Quote parameters to tr to prevent glob expansion.",
        );
        return;
    }
    match get_literal_string(word) {
        Some(ref s) if s == "a-z" => {
            info(
                out,
                word.id(),
                2018,
                "Use '[:lower:]' to support accents and foreign alphabets.",
            );
        }
        Some(ref s) if s == "A-Z" => {
            info(
                out,
                word.id(),
                2019,
                "Use '[:upper:]' to support accents and foreign alphabets.",
            );
        }
        Some(s) => {
            if !(s.starts_with('-') || s.contains("[:")) && tr_duplicated(&s) {
                info(
                    out,
                    word.id(),
                    2020,
                    "tr replaces sets of chars, not words (mentioned due to duplicates).",
                );
            }
            if !(s.starts_with("[:") || s.starts_with("[="))
                && s.starts_with('[')
                && s.ends_with(']')
                && s.chars().count() > 2
                && !s.contains('*')
            {
                info(
                    out,
                    word.id(),
                    2021,
                    "Don't use [] around classes in tr, it replaces literal square brackets.",
                );
            }
        }
        None => {}
    }
}

fn tr_duplicated(s: &str) -> bool {
    let relevant: Vec<char> = s.chars().filter(|c| c.is_alphabetic()).collect();
    let mut seen = std::collections::HashSet::new();
    for c in &relevant {
        if !seen.insert(*c) {
            return true;
        }
    }
    false
}

const GREP_GLOB_FLAGS: &[&str] = &[
    "fixed-strings",
    "F",
    "include",
    "exclude",
    "exclude-dir",
    "o",
    "only-matching",
];

/// `getSuspiciousRegexWildcard`: first `[A-Za-z1-9]` immediately followed by
/// `*`, unless the string matches the "contra" pattern.
fn get_suspicious_regex_wildcard(s: &str) -> Option<char> {
    let cs: Vec<char> = s.chars().collect();
    let mut found = None;
    for i in 0..cs.len().saturating_sub(1) {
        let c = cs[i];
        if (c.is_ascii_alphabetic() || ('1'..='9').contains(&c)) && cs[i + 1] == '*' {
            found = Some(c);
            break;
        }
    }
    let c = found?;
    if grep_matches_contra(&cs) {
        None
    } else {
        Some(c)
    }
}

/// `contra = "[^a-zA-Z1-9]\\*|[][^$+\\\\]"`: a non-`[a-zA-Z1-9]` char before a
/// `*`, or any of the chars `][^$+\`.
fn grep_matches_contra(cs: &[char]) -> bool {
    for &c in cs {
        if matches!(c, ']' | '[' | '^' | '$' | '+' | '\\') {
            return true;
        }
    }
    for i in 0..cs.len().saturating_sub(1) {
        let c = cs[i];
        let is_alnum19 = c.is_ascii_alphabetic() || ('1'..='9').contains(&c);
        if !is_alnum19 && cs[i + 1] == '*' {
            return true;
        }
    }
    false
}

fn word_starting_with(c: char) -> String {
    let mut candidates: Vec<String> = SAMPLE_WORDS.iter().map(|s| s.to_string()).collect();
    for w in SAMPLE_WORDS {
        let mut chs = w.chars();
        let up: String = match chs.next() {
            Some(first) => first.to_ascii_uppercase().to_string() + chs.as_str(),
            None => String::new(),
        };
        candidates.push(up);
    }
    let prefix = c.to_string();
    match candidates.iter().find(|w| w.starts_with(&prefix)) {
        Some(w) => w.clone(),
        None => format!("{}test", c),
    }
}

fn su_undirected(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } if commands.len() >= 2 => false,
        InnerToken::T_Redirecting { redirs, .. } if !redirs.is_empty() => false,
        _ => true,
    }
}

fn timed_is_piped(cmd: &Token) -> bool {
    matches!(&*cmd.inner, InnerToken::T_Pipeline { commands, .. } if commands.len() >= 2)
}

fn timed_get_command(cmd: &Token) -> Option<&Token> {
    match &*cmd.inner {
        InnerToken::T_Pipeline { commands, .. } if !commands.is_empty() => {
            match &*commands[0].inner {
                InnerToken::T_Redirecting { cmd: inner, .. } => Some(inner),
                _ => None,
            }
        }
        _ => None,
    }
}

fn timed_is_simple(cmd: &Token) -> Option<bool> {
    let inner = timed_get_command(cmd)?;
    Some(matches!(&*inner.inner, InnerToken::T_SimpleCommand { .. }))
}

const EXPR_EXCEPTIONS: [&str; 9] = [
    ":", "<", ">", "<=", ">=", "match", "length", "substr", "index",
];

fn expr_check_op(side: &Token, out: &mut Out) {
    if let Some(s) = ast_lib::get_literal_string(side) {
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

fn ssh_is_option(x: &Token) -> bool {
    oversimplify_concat(x).starts_with('-')
}

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

/// `checkWhich` (optional: `deprecate-which`).
pub(crate) fn check_which() -> CommandCheck {
    CommandCheck::new(Basename("which"), |_p, t, out| {
        info(
            out,
            get_command_token_or_this(t).id(),
            2230,
            "'which' is non-standard. Use builtin 'command -v' instead.",
        );
    })
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::interface::Shell;
    use crate::test_support::*;

    #[test]
    fn prop_checkUuoeCmd1() {
        assert!(emits(check_uuoe_cmd(), "echo $(date)"));
    }

    #[test]
    fn prop_checkUuoeCmd2() {
        assert!(emits(check_uuoe_cmd(), "echo `date`"));
    }

    #[test]
    fn prop_checkUuoeCmd3() {
        assert!(emits(check_uuoe_cmd(), "echo \"$(date)\""));
    }

    #[test]
    fn prop_checkUuoeCmd4() {
        assert!(emits(check_uuoe_cmd(), "echo \"`date`\""));
    }

    #[test]
    fn prop_checkUuoeCmd5() {
        assert!(!emits(check_uuoe_cmd(), "echo \"The time is $(date)\""));
    }

    #[test]
    fn prop_checkUuoeCmd6() {
        assert!(!emits(check_uuoe_cmd(), "echo \"$(<file)\""));
    }

    // Regression guards for FIX B1: SC2005 must fire even when the `echo $(cmd)`
    // is itself nested inside a command substitution (the old command-sub
    // suppression guard was removed since inner spans are now correct).

    #[test]
    fn prop_checkUuoeCmd_nested_dollar_expansion() {
        assert!(emits(check_uuoe_cmd(), "foo $(echo $(bar))"));
    }

    #[test]
    fn prop_checkUuoeCmd_nested_backtick() {
        assert!(emits(check_uuoe_cmd(), "foo=`echo \\`expr 3+2\\``"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes1() {
        assert!(emits(check_unused_echo_escapes(), "echo 'foo\\nbar\\n'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes2() {
        assert!(!emits(check_unused_echo_escapes(), "echo -e 'foi\\nbar'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes3() {
        assert!(emits(check_unused_echo_escapes(), "echo \"n:\\t42\""));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes4() {
        assert!(!emits(check_unused_echo_escapes(), "echo lol"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes5() {
        assert!(!emits(check_unused_echo_escapes(), "echo -n -e '\n'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes6() {
        assert!(emits(check_unused_echo_escapes(), "echo '\\506'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes7() {
        assert!(emits(check_unused_echo_escapes(), "echo '\\5a'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes8() {
        assert!(!emits(check_unused_echo_escapes(), "echo '\\8a'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes9() {
        assert!(!emits(check_unused_echo_escapes(), "echo '\\d5a'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes10() {
        assert!(emits(check_unused_echo_escapes(), "echo '\\x4a'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes11() {
        assert!(emits(check_unused_echo_escapes(), "echo '\\xat'"));
    }

    #[test]
    fn prop_checkUnusedEchoEscapes12() {
        assert!(!emits(check_unused_echo_escapes(), "echo '\\xth'"));
    }

    // SC2062 — checkGrepRe (glob branch)

    // SC2194 — constant case word

    // SC2207 — checkSplittingInArrays (command branch)

    // SC2215 — checkFlagAsCommand

    #[test]
    fn prop_checkTr1() {
        assert!(emits(check_tr(), "tr [a-f] [A-F]"));
    }

    #[test]
    fn prop_checkTr2() {
        assert!(emits(check_tr(), "tr 'a-z' 'A-Z'"));
    }

    #[test]
    fn prop_checkTr2a() {
        assert!(emits(check_tr(), "tr '[a-z]' '[A-Z]'"));
    }

    #[test]
    fn prop_checkTr3() {
        assert!(!emits(check_tr(), "tr -d '[:lower:]'"));
    }

    #[test]
    fn prop_checkTr3a() {
        assert!(!emits(check_tr(), "tr -d '[:upper:]'"));
    }

    #[test]
    fn prop_checkTr3b() {
        assert!(!emits(check_tr(), "tr -d '|/_[:upper:]'"));
    }

    #[test]
    fn prop_checkTr4() {
        assert!(!emits(check_tr(), "ls [a-z]"));
    }

    #[test]
    fn prop_checkTr5() {
        assert!(emits(check_tr(), "tr foo bar"));
    }

    #[test]
    fn prop_checkTr6() {
        assert!(emits(check_tr(), "tr 'hello' 'world'"));
    }

    #[test]
    fn prop_checkTr8() {
        assert!(!emits(check_tr(), "tr aeiou _____"));
    }

    #[test]
    fn prop_checkTr9() {
        assert!(!emits(check_tr(), "a-z n-za-m"));
    }

    #[test]
    fn prop_checkTr10() {
        assert!(!emits(check_tr(), "tr --squeeze-repeats rl lr"));
    }

    #[test]
    fn prop_checkTr11() {
        assert!(!emits(check_tr(), "tr abc '[d*]'"));
    }

    #[test]
    fn prop_checkTr12() {
        assert!(!emits(check_tr(), "tr '[=e=]' 'e'"));
    }

    // ---- SC2061 checkFindNameGlob ----

    #[test]
    fn prop_checkGrepRe1() {
        assert!(emits(check_grep_re(), "cat foo | grep *.mp3"));
    }

    #[test]
    fn prop_checkGrepRe2() {
        assert!(emits(check_grep_re(), "grep -Ev cow*test *.mp3"));
    }

    #[test]
    fn prop_checkGrepRe3() {
        assert!(emits(check_grep_re(), "grep --regex=*.mp3 file"));
    }

    #[test]
    fn prop_checkGrepRe4() {
        assert!(!emits(check_grep_re(), "grep foo *.mp3"));
    }

    #[test]
    fn prop_checkGrepRe5() {
        assert!(!emits(check_grep_re(), "grep-v  --regex=moo *"));
    }

    #[test]
    fn prop_checkGrepRe6() {
        assert!(!emits(check_grep_re(), "grep foo \\*.mp3"));
    }

    #[test]
    fn prop_checkGrepRe7() {
        assert!(emits(check_grep_re(), "grep *foo* file"));
    }

    #[test]
    fn prop_checkGrepRe8() {
        assert!(emits(check_grep_re(), "ls | grep foo*.jpg"));
    }

    #[test]
    fn prop_checkGrepRe9() {
        assert!(!emits(check_grep_re(), "grep '[0-9]*' file"));
    }

    #[test]
    fn prop_checkGrepRe10() {
        assert!(!emits(check_grep_re(), "grep '^aa*' file"));
    }

    #[test]
    fn prop_checkGrepRe11() {
        assert!(!emits(check_grep_re(), "grep --include=*.png foo"));
    }

    #[test]
    fn prop_checkGrepRe12() {
        assert!(!emits(check_grep_re(), "grep -F 'Foo*' file"));
    }

    #[test]
    fn prop_checkGrepRe13() {
        assert!(!emits(check_grep_re(), "grep -- -foo bar*"));
    }

    #[test]
    fn prop_checkGrepRe14() {
        assert!(!emits(check_grep_re(), "grep -e -foo bar*"));
    }

    #[test]
    fn prop_checkGrepRe15() {
        assert!(!emits(check_grep_re(), "grep --regex -foo bar*"));
    }

    #[test]
    fn prop_checkGrepRe16() {
        assert!(!emits(check_grep_re(), "grep --include 'Foo*' file"));
    }

    #[test]
    fn prop_checkGrepRe17() {
        assert!(!emits(check_grep_re(), "grep --exclude 'Foo*' file"));
    }

    #[test]
    fn prop_checkGrepRe18() {
        assert!(!emits(check_grep_re(), "grep --exclude-dir 'Foo*' file"));
    }

    #[test]
    fn prop_checkGrepRe19() {
        assert!(emits(check_grep_re(), "grep -- 'Foo*' file"));
    }

    #[test]
    fn prop_checkGrepRe20() {
        assert!(!emits(check_grep_re(), "grep --fixed-strings 'Foo*' file"));
    }

    #[test]
    fn prop_checkGrepRe21() {
        assert!(!emits(check_grep_re(), "grep -o 'x*' file"));
    }

    #[test]
    fn prop_checkGrepRe22() {
        assert!(!emits(check_grep_re(), "grep --only-matching 'x*' file"));
    }

    #[test]
    fn prop_checkGrepRe23() {
        assert!(!emits(check_grep_re(), "grep '.*' file"));
    }

    // ---- SC2186/2196/2197 deprecated ----

    #[test]
    fn prop_checkDeprecatedTempfile1() {
        assert!(emits(check_deprecated_tempfile(), "var=$(tempfile)"));
    }

    #[test]
    fn prop_checkDeprecatedTempfile2() {
        assert!(!emits(check_deprecated_tempfile(), "tempfile=$(mktemp)"));
    }

    #[test]
    fn prop_checkDeprecatedEgrep() {
        assert!(emits(check_deprecated_egrep(), "egrep '.+'"));
    }

    #[test]
    fn prop_checkDeprecatedFgrep() {
        assert!(emits(check_deprecated_fgrep(), "fgrep '*' files"));
    }

    // ---- SC2117 checkInteractiveSu ----

    #[test]
    fn prop_checkInteractiveSu1() {
        assert!(emits(check_interactive_su(), "su; rm file; su $USER"));
    }

    #[test]
    fn prop_checkInteractiveSu2() {
        assert!(emits(check_interactive_su(), "su foo; something; exit"));
    }

    #[test]
    fn prop_checkInteractiveSu3() {
        assert!(!emits(check_interactive_su(), "echo rm | su foo"));
    }

    #[test]
    fn prop_checkInteractiveSu4() {
        assert!(!emits(check_interactive_su(), "su root < script"));
    }

    // ---- SC2185 checkFindWithoutPath ----

    #[test]
    fn prop_checkChmodDashr1() {
        assert!(emits(check_chmod_dashr(), "chmod -r 0755 dir"));
    }

    #[test]
    fn prop_checkChmodDashr2() {
        assert!(!emits(check_chmod_dashr(), "chmod -R 0755 dir"));
    }

    #[test]
    fn prop_checkChmodDashr3() {
        assert!(!emits(check_chmod_dashr(), "chmod a-r dir"));
    }

    // ---- SC2267 checkXargsDashi ----

    #[test]
    fn prop_checkXargsDashi1() {
        assert!(emits(check_xargs_dashi(), "xargs -i{} echo {}"));
    }

    #[test]
    fn prop_checkXargsDashi2() {
        assert!(!emits(check_xargs_dashi(), "xargs -I{} echo {}"));
    }

    #[test]
    fn prop_checkXargsDashi3() {
        assert!(!emits(check_xargs_dashi(), "xargs sed -i -e foo"));
    }

    #[test]
    fn prop_checkXargsDashi4() {
        assert!(emits(check_xargs_dashi(), "xargs -e sed -i foo"));
    }

    #[test]
    fn prop_checkXargsDashi5() {
        assert!(!emits(check_xargs_dashi(), "xargs -x sed -i foo"));
    }

    // ---- SC2172/2173 checkNonportableSignals ----

    #[test]
    fn prop_checkTimeParameters1() {
        assert!(emits_shell(
            check_time_parameters(),
            "time -f lol sleep 10",
            Shell::Bash
        ));
    }

    #[test]
    fn prop_checkTimeParameters2() {
        assert!(!emits_shell(
            check_time_parameters(),
            "time sleep 10",
            Shell::Bash
        ));
    }

    #[test]
    fn prop_checkTimeParameters3() {
        assert!(!emits_shell(
            check_time_parameters(),
            "time -p foo",
            Shell::Bash
        ));
    }

    #[test]
    fn prop_checkTimeParameters4() {
        assert!(!emits_shell(
            check_time_parameters(),
            "command time -f lol sleep 10",
            Shell::Bash
        ));
    }

    // ---- SC2150 checkFindExecWithSingleArgument ----

    #[test]
    fn prop_checkTimedCommand1() {
        assert!(emits_shell(
            check_timed_command(),
            "#!/bin/sh\ntime -p foo | bar",
            Shell::Sh
        ));
    }

    #[test]
    fn prop_checkTimedCommand2() {
        assert!(emits_shell(
            check_timed_command(),
            "#!/bin/dash\ntime ( foo; bar; )",
            Shell::Dash
        ));
    }

    #[test]
    fn prop_checkTimedCommand3() {
        assert!(!emits_shell(
            check_timed_command(),
            "#!/bin/sh\ntime sleep 1",
            Shell::Sh
        ));
    }

    #[test]
    fn prop_checkExpr() {
        assert!(produces(check_expr(), "foo=$(expr 3 + 2)"));
    }

    #[test]
    fn prop_checkExpr2() {
        assert!(produces(check_expr(), "foo=`echo \\`expr 3 + 2\\``"));
    }

    #[test]
    fn prop_checkExpr3() {
        assert!(!produces(check_expr(), "foo=$(expr foo : regex)"));
    }

    #[test]
    fn prop_checkExpr4() {
        assert!(!produces(check_expr(), "foo=$(expr foo \\< regex)"));
    }

    #[test]
    fn prop_checkExpr5() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr match foo bar"
        ));
    }

    #[test]
    fn prop_checkExpr6() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr foo : fo*"
        ));
    }

    #[test]
    fn prop_checkExpr7() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr 5 -3"
        ));
    }

    #[test]
    fn prop_checkExpr8() {
        assert!(!produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr \"$@\""
        ));
    }

    #[test]
    fn prop_checkExpr9() {
        assert!(!produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr 5 $rest"
        ));
    }

    #[test]
    fn prop_checkExpr10() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr length \"$var\""
        ));
    }

    #[test]
    fn prop_checkExpr11() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr foo > bar"
        ));
    }

    #[test]
    fn prop_checkExpr12() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr 1 | 2"
        ));
    }

    #[test]
    fn prop_checkExpr13() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr 1 * 2"
        ));
    }

    #[test]
    fn prop_checkExpr14() {
        assert!(produces(
            check_expr(),
            "# shellcheck disable=SC2003\nexpr \"$x\" >=  \"$y\""
        ));
    }

    // checkReturn

    #[test]
    fn prop_checkSshCmdStr1() {
        assert!(produces(
            check_ssh_command_string(),
            "ssh host \"echo $PS1\""
        ));
    }

    #[test]
    fn prop_checkSshCmdStr2() {
        assert!(!produces(check_ssh_command_string(), "ssh host \"ls foo\""));
    }

    #[test]
    fn prop_checkSshCmdStr3() {
        assert!(!produces(check_ssh_command_string(), "ssh \"$host\""));
    }

    #[test]
    fn prop_checkSshCmdStr4() {
        assert!(!produces(
            check_ssh_command_string(),
            "ssh -i key \"$host\""
        ));
    }

    // checkUnquotedEchoSpaces

    #[test]
    fn prop_checkUnquotedEchoSpaces1() {
        assert!(produces(
            check_unquoted_echo_spaces(),
            "echo foo         bar"
        ));
    }

    #[test]
    fn prop_checkUnquotedEchoSpaces2() {
        assert!(!produces(check_unquoted_echo_spaces(), "echo       foo"));
    }

    #[test]
    fn prop_checkUnquotedEchoSpaces3() {
        assert!(!produces(check_unquoted_echo_spaces(), "echo foo  bar"));
    }

    #[test]
    fn prop_checkUnquotedEchoSpaces4() {
        assert!(!produces(
            check_unquoted_echo_spaces(),
            "echo 'foo          bar'"
        ));
    }

    #[test]
    fn prop_checkUnquotedEchoSpaces5() {
        assert!(!produces(
            check_unquoted_echo_spaces(),
            "echo a > myfile.txt b"
        ));
    }

    #[test]
    fn prop_checkUnquotedEchoSpaces6() {
        assert!(!produces(
            check_unquoted_echo_spaces(),
            "        echo foo\\\n        bar"
        ));
    }

    // checkEvalArray

    #[test]
    fn prop_checkMvArguments1() {
        assert!(produces(check_mv_arguments(), "mv 'foo bar'"));
    }

    #[test]
    fn prop_checkMvArguments2() {
        assert!(!produces(check_mv_arguments(), "mv foo bar"));
    }

    #[test]
    fn prop_checkMvArguments3() {
        assert!(!produces(check_mv_arguments(), "mv 'foo bar'{,bak}"));
    }

    #[test]
    fn prop_checkMvArguments4() {
        assert!(!produces(check_mv_arguments(), "mv \"$@\""));
    }

    #[test]
    fn prop_checkMvArguments5() {
        assert!(!produces(check_mv_arguments(), "mv -t foo bar"));
    }

    #[test]
    fn prop_checkMvArguments6() {
        assert!(!produces(
            check_mv_arguments(),
            "mv --target-directory=foo bar"
        ));
    }

    #[test]
    fn prop_checkMvArguments7() {
        assert!(!produces(check_mv_arguments(), "mv --target-direc=foo bar"));
    }

    #[test]
    fn prop_checkMvArguments8() {
        assert!(!produces(check_mv_arguments(), "mv --version"));
    }

    #[test]
    fn prop_checkMvArguments9() {
        assert!(!produces(check_mv_arguments(), "mv \"${!var}\""));
    }

    // checkArgComparison
}
