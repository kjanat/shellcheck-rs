//! Port of selected `ShellCheck.ASTLib` helpers (grown as checks need them).

use crate::ast::*;
use crate::interface::Shell;

/// `getLiteralString`: the literal string of a word, or None if any part is
/// non-literal (an expansion, glob, etc.).
pub fn get_literal_string(t: &Token) -> Option<String> {
    get_literal_string_ext(t, &|_| None)
}

/// `getLiteralStringExt`: like `getLiteralString` but a fallback decides what
/// non-literal parts contribute (used e.g. to treat globs as "*").
pub fn get_literal_string_ext(t: &Token, fallback: &dyn Fn(&InnerToken) -> Option<String>) -> Option<String> {
    fn go(t: &Token, fb: &dyn Fn(&InnerToken) -> Option<String>, out: &mut String) -> bool {
        match &*t.inner {
            InnerToken::T_Literal(s)
            | InnerToken::T_SingleQuoted(s)
            | InnerToken::T_DollarSingleQuoted(s) => {
                out.push_str(s);
                true
            }
            InnerToken::T_NormalWord(parts)
            | InnerToken::T_DoubleQuoted(parts)
            | InnerToken::T_DollarDoubleQuoted(parts) => {
                for p in parts {
                    if !go(p, fb, out) {
                        return false;
                    }
                }
                true
            }
            other => {
                if let Some(s) = fb(other) {
                    out.push_str(&s);
                    true
                } else {
                    false
                }
            }
        }
    }
    let mut s = String::new();
    if go(t, fallback, &mut s) {
        Some(s)
    } else {
        None
    }
}

/// `oversimplify`: flatten a word to its most literal string form, treating
/// expansions/globs loosely. Used by many command checks.
pub fn oversimplify(t: &Token) -> Vec<String> {
    // Simplified: return the single literal string if fully literal, else empty.
    match get_literal_string(t) {
        Some(s) => vec![s],
        None => Vec::new(),
    }
}

fn basename(path: &str) -> String {
    match path.rsplit('/').next() {
        Some(x) => x.to_string(),
        None => path.to_string(),
    }
}

/// `executableFromShebang`: extract the interpreter name from a shebang string.
pub fn executable_from_shebang(sb: &str) -> String {
    // Handle `/usr/bin/env` forms including -S / --split-string.
    let words: Vec<&str> = sb.split_whitespace().collect();
    // Detect `/env <flags> ...`
    if let Some(env_idx) = words.iter().position(|w| basename(w) == "env") {
        return from_env_args(&words[env_idx + 1..]);
    }
    match words.as_slice() {
        [] => String::new(),
        [x] => basename(x),
        [first, second, ..] if basename(first) == "busybox" => match basename(second).as_str() {
            "sh" => "busybox sh".to_string(),
            "ash" => "busybox ash".to_string(),
            other => other.to_string(),
        },
        [first, ..] => basename(first),
    }
}

fn from_env_args(args: &[&str]) -> String {
    // Skip -S / --split-string[=...] and VAR=val assignments; first bare word is
    // the interpreter.
    let mut i = 0;
    while i < args.len() {
        let a = args[i];
        if a == "-S" || a == "--split-string" {
            i += 1;
            continue;
        }
        if a.starts_with("--split-string=") {
            let rest = &a["--split-string=".len()..];
            if rest.is_empty() {
                i += 1;
                continue;
            }
            if rest.contains('=') {
                i += 1;
                continue;
            }
            return basename(rest);
        }
        if a.contains('=') {
            i += 1;
            continue;
        }
        return basename(a);
    }
    String::new()
}

/// `shellForExecutable` (from `ShellCheck.Data`).
pub fn shell_for_executable(name: &str) -> Option<Shell> {
    Some(match name {
        "sh" => Shell::Sh,
        "bash" => Shell::Bash,
        "bats" => Shell::Bash,
        "busybox" => Shell::BusyboxSh,
        "busybox sh" => Shell::BusyboxSh,
        "busybox ash" => Shell::BusyboxSh,
        "dash" => Shell::Dash,
        "ash" => Shell::Dash,
        "ksh" => Shell::Ksh,
        "ksh88" => Shell::Ksh,
        "ksh93" => Shell::Ksh,
        "oksh" => Shell::Ksh,
        _ => return None,
    })
}
