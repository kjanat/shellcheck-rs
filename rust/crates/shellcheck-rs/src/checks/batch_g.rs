//! Ported check batch g. See rust/PORTING.md.
//!
//! Command-argument / pipeline / condition checks:
//! - SC2174  checkMkdirDashPM     (Checks/Commands.hs) — `mkdir -m` with `-p`
//! - SC2219  checkLetUsage        (Checks/Commands.hs) — `let` -> `(( ))`
//! - SC2126  checkPipePitfalls    (Analytics.hs)       — `grep | wc -l` -> grep -c
//! - SC2110  checkConditionalAndOrs (Analytics.hs)     — `[[ .. -o .. ]]` -> `||`
//! - SC2114/SC2115 checkCatastrophicRm (Checks/Commands.hs) — rm of a system dir
//!
//! Note: `checkCatastrophicRm` brace-expands each argument via
//! `astlib::brace_expand` and runs the per-word check on every expanded word,
//! exactly as the Haskell `mapM_ (mapM_ checkWord . braceExpand)` does.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::{get_literal_string, get_literal_string_ext};
use crate::interface::Shell;

/// Register this batch's checks.
///
/// NOT registered (conformance-safety rule — `extra > 0`, caused by shared
/// parser position discrepancies this module cannot fix):
/// - SC2219 (`check_let_usage`): the oracle points SC2219 at the whole
///   `T_SimpleCommand` span; the Rust parser reports an end column one past the
///   oracle's when the last word ends in a single quote (`let 'a=1'`), so 2 of
///   10 corpus cases mismatch (extra == 2). Check logic is correct — see the
///   retained `check_let_usage` fn — but it stays unregistered until the parser
///   computes matching command extents.
/// - SC2110 (`check_conditional_or`): the oracle anchors SC2110 at the `-o`
///   operator token (cols 8-10 of `[[ foo -o bar ]]`), but the Rust `TC_Or`
///   carries only the whole-condition span (cols 4-15) and its operator is a
///   bare `String` with no id, so the position cannot be matched (extra == 1).
pub fn register(c: &mut Checker) {
    c.node(check_mkdir_dash_pm);
    c.node(check_pipe_wc);
    c.node(check_catastrophic_rm);
    // Enabled now that TC_Or is anchored on its operator token.
    c.node(check_conditional_or);
}

// ---------------------------------------------------------------------------
// Local helpers (ported from ASTLib; kept private so this module does not touch
// shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

/// Faithful port of `ShellCheck.ASTLib.oversimplify` (the crate's is simplified).
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
        TA_Sequence(seq) if seq.len() == 1 => match &*seq[0].inner {
            TA_Expansion(v) => v.iter().flat_map(oversimplify).collect(),
            _ => vec![],
        },
        _ => vec![],
    }
}

/// `basename`: the part after the last '/'.
fn basename(path: &str) -> String {
    match path.rfind('/') {
        Some(i) => path[i + 1..].to_string(),
        None => path.to_string(),
    }
}

/// `getCommand`: unwrap redirects/annotations to reach a `T_SimpleCommand`.
fn get_command(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command(cmd),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        InnerToken::T_Annotation { token, .. } => get_command(token),
        _ => None,
    }
}

/// The words after the command name of a `T_SimpleCommand`.
fn arguments(t: &Token) -> &[Token] {
    match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => &words[1..],
        _ => &[],
    }
}

/// The literal name of the first word of a `T_SimpleCommand`, if any.
fn simple_command_name(t: &Token) -> Option<String> {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        let cmd = words.first()?;
        return get_literal_string(cmd);
    }
    None
}

/// `getAllFlags` = `getFlagsUntil (== "--")`. Returns (token, flag-name) pairs.
fn get_all_flags(t: &Token) -> Vec<(&Token, String)> {
    let args = arguments(t);
    let mut broken = false;
    let mut flag_args: Vec<(&Token, String)> = vec![];
    let mut rest: Vec<&Token> = vec![];
    for x in args {
        let txt = oversimplify(x).concat();
        if !broken && txt == "--" {
            broken = true;
        }
        if broken {
            rest.push(x);
        } else {
            flag_args.push((x, txt));
        }
    }
    let mut out: Vec<(&Token, String)> = vec![];
    for (x, txt) in flag_args {
        if let Some(arg) = txt.strip_prefix("--") {
            out.push((x, arg.split('=').next().unwrap_or("").to_string()));
        } else if let Some(a) = txt.strip_prefix('-') {
            for v in a.chars() {
                out.push((x, v.to_string()));
            }
        } else {
            out.push((x, String::new()));
        }
    }
    for x in rest {
        out.push((x, String::new()));
    }
    out
}

// ---------------------------------------------------------------------------
// SC2174 — checkMkdirDashPM
// ---------------------------------------------------------------------------

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

fn check_mkdir_dash_pm(_params: &Parameters, t: &Token, out: &mut Out) {
    let name = match simple_command_name(t) {
        Some(n) => n,
        None => return,
    };
    if basename(&name) != "mkdir" {
        return;
    }
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
}

// ---------------------------------------------------------------------------
// SC2219 — checkLetUsage
// ---------------------------------------------------------------------------

fn check_let_usage(params: &Parameters, t: &Token, out: &mut Out) {
    let name = match simple_command_name(t) {
        Some(n) => n,
        None => return,
    };
    if name != "let" {
        return;
    }
    if matches!(params.shell, Shell::Bash | Shell::Ksh) {
        style(
            out,
            t.id(),
            2219,
            "Instead of 'let expr', prefer (( expr )) .",
        );
    }
}

// ---------------------------------------------------------------------------
// SC2126 — checkPipePitfalls (grep | wc -l)
// ---------------------------------------------------------------------------

fn command_flag_names(cmd_element: &Token) -> Vec<String> {
    match get_command(cmd_element) {
        Some(c) => get_all_flags(c).into_iter().map(|(_, f)| f).collect(),
        None => vec![],
    }
}

fn check_pipe_wc(_params: &Parameters, t: &Token, out: &mut Out) {
    let commands = match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } => commands,
        _ => return,
    };
    if commands.len() < 2 {
        return;
    }
    let names: Vec<String> = commands
        .iter()
        .map(|c| oversimplify(c).into_iter().next().unwrap_or_default())
        .collect();

    const GREP_EXCL: &[&str] = &[
        "l",
        "files-with-matches",
        "L",
        "files-without-matches",
        "o",
        "only-matching",
        "r",
        "R",
        "recursive",
        "A",
        "after-context",
        "B",
        "before-context",
    ];
    const WC_EXCL: &[&str] = &[
        "m",
        "chars",
        "w",
        "words",
        "c",
        "bytes",
        "L",
        "max-line-length",
    ];

    for i in 0..commands.len() - 1 {
        if names[i] == "grep" && names[i + 1] == "wc" {
            let flags_grep = command_flag_names(&commands[i]);
            let flags_wc = command_flag_names(&commands[i + 1]);
            let excluded = flags_grep.iter().any(|f| GREP_EXCL.contains(&f.as_str()))
                || flags_wc.iter().any(|f| WC_EXCL.contains(&f.as_str()))
                || flags_wc.is_empty();
            if !excluded {
                style(
                    out,
                    commands[i].id(),
                    2126,
                    "Consider using 'grep -c' instead of 'grep|wc -l'.",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2110 — checkConditionalAndOrs (only the `[[ .. -o .. ]]` branch)
// ---------------------------------------------------------------------------

fn check_conditional_or(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Or { typ, op, .. } = &*t.inner {
        if *typ == ConditionType::DoubleBracket && op == "-o" {
            err(out, t.id(), 2110, "In [[..]], use || instead of -o.");
        }
    }
}

// ---------------------------------------------------------------------------
// SC2114 / SC2115 — checkCatastrophicRm (rm of a system directory)
// ---------------------------------------------------------------------------

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

fn check_catastrophic_rm(_params: &Parameters, t: &Token, out: &mut Out) {
    let name = match simple_command_name(t) {
        Some(n) => n,
        None => return,
    };
    if basename(&name) != "rm" {
        return;
    }
    let recursive = get_all_flags(t)
        .iter()
        .any(|(_, f)| f == "r" || f == "R" || f == "recursive");
    if !recursive {
        return;
    }
    let important = important_paths();
    // `mapM_ (mapM_ checkWord . braceExpand) $ arguments t`
    for arg in arguments(t) {
        for word in astlib::brace_expand(arg) {
            check_rm_word(&word, &important, out);
        }
    }
}
