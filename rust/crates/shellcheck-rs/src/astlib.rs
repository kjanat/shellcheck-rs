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
pub fn get_literal_string_ext(
    t: &Token,
    fallback: &dyn Fn(&InnerToken) -> Option<String>,
) -> Option<String> {
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
            | InnerToken::T_DollarDoubleQuoted(parts)
            | InnerToken::TA_Expansion(parts) => {
                for p in parts {
                    if !go(p, fb, out) {
                        return false;
                    }
                }
                true
            }
            InnerToken::T_ParamSubSpecialChar(s) => {
                out.push_str(s);
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

/// `oversimplify`: flatten a token to its most literal string forms. Faithful
/// to `ShellCheck.ASTLib.oversimplify`: words concatenate their parts,
/// expansions become `"${VAR}"`, globs and literals pass through, and a
/// single-element pipeline / redirected / annotated command is looked through.
/// This is the single implementation in the crate; `cfg::oversimplify`
/// delegates here.
pub fn oversimplify(t: &Token) -> Vec<String> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(l) => {
            let s: String = l.iter().flat_map(oversimplify).collect::<Vec<_>>().concat();
            vec![s]
        }
        T_DoubleQuoted(l) => {
            let s: String = l.iter().flat_map(oversimplify).collect::<Vec<_>>().concat();
            vec![s]
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
        // Workaround for `let "foo = bar"` parsing (as in the Haskell source).
        TA_Sequence(seq) if seq.len() == 1 && matches!(&*seq[0].inner, TA_Expansion(_)) => {
            match &*seq[0].inner {
                TA_Expansion(v) => v.iter().flat_map(oversimplify).collect(),
                _ => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}

/// `onlyLiteralString = getLiteralStringDef ""`: definitely get a literal
/// string, treating every non-literal part as the empty string.
pub fn only_literal_string(t: &Token) -> String {
    get_literal_string_ext(t, &|_| Some(String::new())).unwrap_or_default()
}

/// `braceExpand`: return the list of `T_NormalWord`s that a word would produce
/// under brace expansion. For each part, a `T_BraceExpansion` chooses one of its
/// elements (recursively expanded) while any other part passes through
/// unchanged; the result is the cartesian product, capped at 1000 like Haskell's
/// `take 1000`. Non-`T_NormalWord` input returns the single token. The produced
/// words reuse the original word's id.
pub fn brace_expand(word: &Token) -> Vec<Token> {
    let (id, list) = match &*word.inner {
        InnerToken::T_NormalWord(list) => (word.id, list),
        _ => return vec![word.clone()],
    };
    // Cartesian product over the parts, in Haskell list-monad order.
    let mut results: Vec<Vec<Token>> = vec![Vec::new()];
    for part in list {
        let choices = part_choices(part);
        let mut next: Vec<Vec<Token>> = Vec::new();
        'outer: for acc in &results {
            for ch in &choices {
                let mut v = acc.clone();
                v.push(ch.clone());
                next.push(v);
                if next.len() >= 1000 {
                    break 'outer;
                }
            }
        }
        results = next;
    }
    results
        .into_iter()
        .take(1000)
        .map(|items| Token::new(id, InnerToken::T_NormalWord(items)))
        .collect()
}

/// The list of alternative tokens a single word-part contributes to brace
/// expansion: a `T_BraceExpansion` yields, for each of its element words, all of
/// that element's own brace-expanded `T_NormalWord`s; anything else yields itself.
fn part_choices(part: &Token) -> Vec<Token> {
    match &*part.inner {
        InnerToken::T_BraceExpansion(items) => {
            let mut out = Vec::new();
            for item in items {
                out.extend(brace_expand(item));
            }
            out
        }
        _ => vec![part.clone()],
    }
}

/// `basename = reverse . takeWhile (/= '/') . reverse`: the part after the
/// last `/` (the whole string if there is none).
pub(crate) fn basename(path: &str) -> String {
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

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::ast::{Id, InnerToken, Token};

    fn lit(s: &str) -> Token {
        Token::new(Id(0), InnerToken::T_Literal(s.to_string()))
    }

    // getLiteralStringExt handles TA_Expansion by concatenating its literal parts
    // (mirrors Haskell `g (TA_Expansion _ l) = allInList l`). Regression guard for
    // SC2181 on `(( $? == 0 ))`, whose RHS `0` is a TA_Expansion.
    #[test]
    fn prop_getLiteralString_ta_expansion_literal() {
        let t = Token::new(Id(1), InnerToken::TA_Expansion(vec![lit("0")]));
        assert_eq!(get_literal_string(&t), Some("0".to_string()));
    }

    #[test]
    fn prop_getLiteralString_ta_expansion_multipart() {
        let t = Token::new(Id(1), InnerToken::TA_Expansion(vec![lit("1"), lit("2")]));
        assert_eq!(get_literal_string(&t), Some("12".to_string()));
    }

    // A non-literal part (here a bare expansion) makes the whole thing non-literal.
    #[test]
    fn prop_getLiteralString_ta_expansion_nonliteral() {
        let expansion = Token::new(Id(2), InnerToken::T_DollarExpansion(vec![]));
        let t = Token::new(Id(1), InnerToken::TA_Expansion(vec![lit("0"), expansion]));
        assert_eq!(get_literal_string(&t), None);
    }

    // getLiteralStringExt returns the raw string of T_ParamSubSpecialChar
    // (Haskell `g (T_ParamSubSpecialChar _ s) = return s`).
    #[test]
    fn prop_getLiteralString_param_sub_special_char() {
        let t = Token::new(Id(1), InnerToken::T_ParamSubSpecialChar("%".to_string()));
        assert_eq!(get_literal_string(&t), Some("%".to_string()));
    }
}


// ---- helpers consolidated from the check batches (ports of ASTLib) ----

/// `getWordParts`.
pub(crate) fn get_word_parts(t: &Token) -> Vec<&Token> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(l) => l.iter().flat_map(get_word_parts).collect(),
        T_DoubleQuoted(l) => l.iter().collect(),
        TA_Expansion(l) => l.iter().flat_map(get_word_parts).collect(),
        _ => vec![t],
    }
}

pub(crate) fn has_split_range(l: &[Token]) -> bool {
    let after: Vec<&Token> = l
        .iter()
        .skip_while(|t| !matches!(&*t.inner, InnerToken::T_Literal(s) if s == "["))
        .collect();
    after
        .iter()
        .any(|t| matches!(&*t.inner, InnerToken::T_Literal(s) if s.contains(']')))
}

pub(crate) fn is_half_open_range(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Literal(s) if s == "[")
}

pub(crate) fn is_closing_range(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Literal(s) if s.contains(']'))
}

/// Faithful port of `ShellCheck.ASTLib.isGlob`.
pub(crate) fn is_glob(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_Extglob { .. } => true,
        T_Glob(_) => true,
        T_NormalWord(l) => l.iter().any(is_glob) || has_split_range(l),
        _ => false,
    }
}

/// `isFlag`: word whose first part is a `-`-prefixed literal.
pub(crate) fn is_flag(t: &Token) -> bool {
    match get_word_parts(t).first() {
        Some(p) => matches!(&*p.inner, InnerToken::T_Literal(s) if s.starts_with('-')),
        None => false,
    }
}

/// Faithful port of `ShellCheck.ASTLib.isConstant`.
pub(crate) fn is_constant(token: &Token) -> bool {
    use InnerToken::*;
    match &*token.inner {
        // This ignores some cases like ~"foo": a word whose first part is a
        // literal starting with '~' is treated as non-constant.
        T_NormalWord(l) => {
            if let Some(first) = l.first() {
                if let T_Literal(s) = &*first.inner {
                    if s.starts_with('~') {
                        return false;
                    }
                }
            }
            l.iter().all(is_constant)
        }
        T_DoubleQuoted(l) => l.iter().all(is_constant),
        T_SingleQuoted(_) => true,
        T_Literal(_) => true,
        _ => false,
    }
}

/// `getLeadingUnquotedString`.
pub(crate) fn get_leading_unquoted_string(t: &Token) -> Option<String> {
    if let InnerToken::T_NormalWord(list) = &*t.inner {
        if let Some((first, rest)) = list.split_first() {
            if let InnerToken::T_Literal(s) = &*first.inner {
                let mut out = s.clone();
                for p in rest {
                    match &*p.inner {
                        InnerToken::T_Literal(s2) => out.push_str(s2),
                        _ => break,
                    }
                }
                return Some(out);
            }
        }
    }
    None
}

/// `ShellCheck.ASTLib.isUnquotedFlag`.
pub(crate) fn is_unquoted_flag(t: &Token) -> bool {
    matches!(get_leading_unquoted_string(t), Some(s) if s.starts_with('-'))
}

/// `isLiteral t = isJust $ getLiteralString t`.
pub(crate) fn is_literal(t: &Token) -> bool {
    get_literal_string(t).is_some()
}

/// `isOnlyRedirection` (ASTLib).
pub(crate) fn is_only_redirection(t: &Token) -> bool {
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

/// `isAssignment`.
pub(crate) fn is_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => is_assignment(cmd),
        InnerToken::T_SimpleCommand { assignments, words } => {
            !assignments.is_empty() && words.is_empty()
        }
        InnerToken::T_Assignment { .. } => true,
        InnerToken::T_Annotation { token, .. } => is_assignment(token),
        _ => false,
    }
}

/// `isFunction`.
pub(crate) fn is_function(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Function { .. })
}

/// `isQuotes` (ASTLib).
pub(crate) fn is_quotes(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_DoubleQuoted(_) | InnerToken::T_SingleQuoted(_)
    )
}

/// `isAnnotationIgnoringCode code t`.
pub(crate) fn is_annotation_ignoring_code(code: i64, t: &Token) -> bool {
    if let InnerToken::T_Annotation { annotations, .. } = &*t.inner {
        annotations.iter().any(|a| match a {
            Annotation::DisableComment(from, to) => code >= *from && code < *to,
            _ => false,
        })
    } else {
        false
    }
}

/// `escapeForMessage` (`e4m`).
pub(crate) fn e4m(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{1B}' => out.push_str("\\e"),
            _ => {
                let should_escape = c.is_control() || (!c.is_ascii() && !c.is_alphabetic());
                if should_escape {
                    let n = c as u32;
                    if n < 256 {
                        out.push_str(&format!("\\x{:02X}", n));
                    } else {
                        out.push_str(&format!("\\U{:04X}", n));
                    }
                } else {
                    out.push(c);
                }
            }
        }
    }
    out
}

pub(crate) fn list_to_args<'a>(args: &'a [Token]) -> Vec<(String, (&'a Token, &'a Token))> {
    args.iter().map(|x| (String::new(), (x, x))).collect()
}

pub(crate) fn drop_hashbang_prefix(s: &str) -> &str {
    match s.chars().next() {
        Some(c) if c == '!' || c == '#' => &s[c.len_utf8()..],
        _ => s,
    }
}