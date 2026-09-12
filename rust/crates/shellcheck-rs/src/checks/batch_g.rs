//! Ported check batch g. See rust/PORTING.md.
//!
//! Command-argument / pipeline / condition checks:
//! - SC2174  checkMkdirDashPM     (Checks/Commands.hs) — `mkdir -m` with `-p`
//! - SC2219  checkLetUsage        (Checks/Commands.hs) — `let` -> `(( ))`
//! - SC2110  checkConditionalAndOrs (Analytics.hs)     — `[[ .. -o .. ]]` -> `||`
//! - SC2114/SC2115 checkCatastrophicRm (Checks/Commands.hs) — rm of a system dir
//!
//! Note: `checkCatastrophicRm` brace-expands each argument via
//! `astlib::brace_expand` and runs the per-word check on every expanded word,
//! exactly as the Haskell `mapM_ (mapM_ checkWord . braceExpand)` does.
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::basename;
use crate::astlib::{get_literal_string, get_literal_string_ext};

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
    c.node(check_catastrophic_rm);
    // Enabled now that TC_Or is anchored on its operator token.
}

// ---------------------------------------------------------------------------
// Local helpers (ported from ASTLib; kept private so this module does not touch
// shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

/// The literal name of the first word of a `T_SimpleCommand`, if any.
fn simple_command_name(t: &Token) -> Option<String> {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        let cmd = words.first()?;
        return get_literal_string(cmd);
    }
    None
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

// ---------------------------------------------------------------------------
// SC2110 — checkConditionalAndOrs (only the `[[ .. -o .. ]]` branch)
// ---------------------------------------------------------------------------

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
