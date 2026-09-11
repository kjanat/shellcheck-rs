//! Ported check batch s. See rust/PORTING.md.
//!
//! Per-command checks from `src/ShellCheck/Checks/Commands.hs`, dispatched by
//! command name exactly like `ShellCheck.Checks.Commands.checkCommand`
//! (`Exactly` / `Basename`, including the `builtin X` and `/path/X` forms):
//!
//! - SC2018/2019/2020/2021 (+2060 glob branch)  checkTr           (Basename "tr")
//! - SC2061                                      checkFindNameGlob (Basename "find")
//! - SC2022/2063 (+2062 glob branch)             checkGrepRe       (Basename "grep")
//! - SC2186                                      checkDeprecatedTempfile (Basename "tempfile")
//! - SC2196                                      checkDeprecatedEgrep    (Basename "egrep")
//! - SC2197                                      checkDeprecatedFgrep    (Basename "fgrep")
//! - SC2117                                      checkInteractiveSu      (Basename "su")
//! - SC2185                                      checkFindWithoutPath    (Basename "find")
//! - SC2253                                      checkChmodDashr         (Basename "chmod")
//! - SC2267                                      checkXargsDashi         (Basename "xargs")
//! - SC2172/2173                                 checkNonportableSignals (Exactly "trap")
//! - SC2023                                       checkTimeParameters    (Exactly "time")
//! - SC2176/2177                                 checkTimedCommand       (Exactly "time")
//! - SC2150                                      checkFindExecWithSingleArgument (Basename "find")
//! - SC2156                                      checkInjectableFindSh   (Basename "find")
//! - SC2146                                      checkFindActionPrecedence (Basename "find")
//! - SC2227                                      checkFindRedirections   (Basename "find")
//!
//! SC2060 (tr) and SC2062 (grep) are already emitted by the partial ports in
//! batch_i / batch_n; re-emitting them here from the faithful whole-function
//! port is safe because the pipeline `nub`s identical positioned comments, and
//! the token id / message / (absent) fix are identical.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::{get_literal_string, only_literal_string};
use crate::interface::Shell;

/// Register this batch's checks.
///
/// `check_timed_command` (SC2176/SC2177) is now registered: the parser treats
/// the reserved word `time` as a pipeline prefix, parsing the timed pipeline /
/// compound command as `time`'s argument, so the check can inspect it.
pub fn register(c: &mut Checker) {
    c.node(check_tr);
    c.node(check_find_name_glob);
    c.node(check_grep_re);
    c.node(check_deprecated_tempfile);
    c.node(check_deprecated_egrep);
    c.node(check_deprecated_fgrep);
    c.node(check_interactive_su);
    c.node(check_find_without_path);
    c.node(check_chmod_dashr);
    c.node(check_xargs_dashi);
    c.node(check_nonportable_signals);
    c.node(check_time_parameters);
    c.node(check_timed_command);
    c.node(check_find_exec_with_single_argument);
    c.node(check_injectable_find_sh);
    c.node(check_find_action_precedence);
    c.node(check_find_redirections);
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

/// `getLiteralStringDef def = getLiteralStringExt (const (return def))` — every
/// non-literal part contributes `def`, so the result is always `Some`.
fn get_literal_string_def(def: &str, t: &Token) -> String {
    astlib::get_literal_string_ext(t, &|_| Some(def.to_string())).unwrap_or_default()
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

/// `isFlag`: word whose first part is a `-`-prefixed literal.
fn is_flag(t: &Token) -> bool {
    match get_word_parts(t).first() {
        Some(p) => matches!(&*p.inner, InnerToken::T_Literal(s) if s.starts_with('-')),
        None => false,
    }
}

fn basename(path: &str) -> String {
    match path.rsplit('/').next() {
        Some(x) => x.to_string(),
        None => path.to_string(),
    }
}

// ---------------------------------------------------------------------------
// Command-name dispatch (mirror of `ShellCheck.Checks.Commands.checkCommand`).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum CmdKind {
    Exactly,
    Basename,
}

/// If `t` is a `T_SimpleCommand` whose command-name dispatch selects the check
/// registered under `CommandName kind target`, return the *effective* word list
/// (word 0 is the command token, the rest are its arguments). Mirrors
/// `checkCommand`: `/path/x` dispatches only to `Basename (basename x)`,
/// `builtin x ...` dispatches only to `Exactly x'` with the words after
/// `builtin`, and any other literal name dispatches to both `Exactly name` and
/// `Basename name`.
fn matched_words<'a>(t: &'a Token, kind: CmdKind, target: &str) -> Option<&'a [Token]> {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return None,
    };
    let name = get_literal_string(&words[0])?;
    if name.contains('/') {
        if kind == CmdKind::Basename && basename(&name) == target {
            return Some(&words[..]);
        }
        None
    } else if name == "builtin" && words.len() >= 2 {
        if kind == CmdKind::Exactly && only_literal_string(&words[1]) == target {
            return Some(&words[1..]);
        }
        None
    } else if name == target {
        // Consulted under both Exactly name and Basename name.
        Some(&words[..])
    } else {
        None
    }
}

/// `arguments`: the words after the command name.
fn arguments(words: &[Token]) -> &[Token] {
    &words[1..]
}

// ---- getFlagsUntil / getAllFlags / getLeadingFlags / hasFlag --------------

fn get_flags_until<'a, F: Fn(&str) -> bool>(words: &'a [Token], stop: F) -> Vec<(&'a Token, String)> {
    let args = arguments(words);
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

fn get_all_flags(words: &[Token]) -> Vec<(&Token, String)> {
    get_flags_until(words, |x| x == "--")
}

fn has_flag(words: &[Token], flag: &str) -> bool {
    get_all_flags(words).iter().any(|(_, f)| f == flag)
}

// ---- getOpts (getBsdOpts) --------------------------------------------------

use std::collections::HashMap;

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

fn list_to_args<'a>(args: &'a [Token]) -> Vec<(String, (&'a Token, &'a Token))> {
    args.iter().map(|x| (String::new(), (x, x))).collect()
}

fn get_bsd_opts<'a>(spec: &str, args: &'a [Token]) -> Option<Vec<(String, (&'a Token, &'a Token))>> {
    let mut flag_map: HashMap<String, bool> = HashMap::new();
    flag_map.insert(String::new(), false);
    for (k, v) in parse_flag_list(spec) {
        flag_map.insert(k, v);
    }
    opts_process(false, &flag_map, args)
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
        // -iVALUE : the rest of this token is the argument.
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

// ---- getPath / getClosestCommand ------------------------------------------

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

/// `getClosestCommand`: nearest enclosing `T_Redirecting` on the path, stopping
/// at the enclosing `T_Script`.
fn get_closest_command<'a>(params: &'a Parameters, t: &'a Token) -> Option<&'a Token> {
    for node in get_path(params, t) {
        match &*node.inner {
            InnerToken::T_Redirecting { .. } => return Some(node),
            InnerToken::T_Script { .. } => return None,
            _ => {}
        }
    }
    None
}

fn when_shell(p: &Parameters, shells: &[Shell]) -> bool {
    shells.contains(&p.shell)
}

// ===========================================================================
// SC2018/2019/2020/2021 (+2060) — checkTr  (Basename "tr")
// ===========================================================================

fn check_tr(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "tr") {
        Some(w) => w,
        None => return,
    };
    for w in arguments(words) {
        tr_arg(w, out);
    }
}

fn tr_arg(word: &Token, out: &mut Out) {
    if is_glob(word) {
        // The user will go [ab] -> '[ab]' -> 'ab'. Fixme?
        warn(out, word.id(), 2060, "Quote parameters to tr to prevent glob expansion.");
        return;
    }
    match get_literal_string(word) {
        Some(ref s) if s == "a-z" => {
            info(out, word.id(), 2018, "Use '[:lower:]' to support accents and foreign alphabets.");
        }
        Some(ref s) if s == "A-Z" => {
            info(out, word.id(), 2019, "Use '[:upper:]' to support accents and foreign alphabets.");
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
            if !(s.starts_with("[:") || s.starts_with("[=")) {
                if s.starts_with('[') && s.ends_with(']') && s.chars().count() > 2 && !s.contains('*') {
                    info(
                        out,
                        word.id(),
                        2021,
                        "Don't use [] around classes in tr, it replaces literal square brackets.",
                    );
                }
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

// ===========================================================================
// SC2061 — checkFindNameGlob  (Basename "find")
// ===========================================================================

fn check_find_name_glob(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "find") {
        Some(w) => w,
        None => return,
    };
    let args = arguments(words);
    // Consecutive pairs (a, b): warn on b when a is a glob-accepting flag and b
    // is a glob.
    for pair in args.windows(2) {
        let a = &pair[0];
        let b = &pair[1];
        if let Some(s) = get_literal_string(a) {
            if find_accepts_glob(&s) && is_glob(b) {
                warn(
                    out,
                    b.id(),
                    2061,
                    &format!("Quote the parameter to {} so the shell won't interpret it.", s),
                );
            }
        }
    }
}

fn find_accepts_glob(s: &str) -> bool {
    matches!(
        s,
        "-ilname"
            | "-iname"
            | "-ipath"
            | "-iregex"
            | "-iwholename"
            | "-lname"
            | "-name"
            | "-path"
            | "-regex"
            | "-wholename"
    )
}

// ===========================================================================
// SC2022/2063 (+2062) — checkGrepRe  (Basename "grep")
// ===========================================================================

const SAMPLE_WORDS: &[&str] = &[
    "alpha", "bravo", "charlie", "delta", "echo", "foxtrot", "golf", "hotel", "india", "juliett",
    "kilo", "lima", "mike", "november", "oscar", "papa", "quebec", "romeo", "sierra", "tango",
    "uniform", "victor", "whiskey", "xray", "yankee", "zulu",
];

const GREP_GLOB_FLAGS: &[&str] =
    &["fixed-strings", "F", "include", "exclude", "exclude-dir", "o", "only-matching"];

fn check_grep_re(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "grep") {
        Some(w) => w,
        None => return,
    };
    let re = match find_grep_regex(arguments(words)) {
        Some(re) => re,
        None => return,
    };

    if is_glob(re) {
        warn(out, re.id(), 2062, "Quote the grep pattern so the shell won't interpret it.");
    }

    let flags: Vec<String> = get_all_flags(words).into_iter().map(|(_, f)| f).collect();
    if !GREP_GLOB_FLAGS.iter().any(|g| flags.iter().any(|f| f == g)) {
        let string = concat_over(re);
        if is_confused_glob_regex(&string) {
            warn(out, re.id(), 2063, "Grep uses regex, but this looks like a glob.");
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
}

/// checkGrepRe's `f`: walk args to find the regex argument.
fn find_grep_regex(args: &[Token]) -> Option<&Token> {
    let mut rest = args;
    loop {
        let (x, tail) = rest.split_first()?;
        let s = get_literal_string_def("_", x);
        if s == "--" || s == "-e" || s == "--regex" {
            return tail.first(); // Regex is *after* this
        }
        // skippable: not "--regex=" prefix and starts with "-"
        if !s.starts_with("--regex=") && s.starts_with('-') {
            rest = tail; // Regex is elsewhere
        } else {
            return Some(x); // Regex is this
        }
    }
}

/// `isConfusedGlobRegex`.
fn is_confused_glob_regex(s: &str) -> bool {
    let cs: Vec<char> = s.chars().collect();
    if cs.first() == Some(&'*') {
        return true;
    }
    // [x, '*'] with x `notElem` "\\."
    cs.len() == 2 && cs[1] == '*' && cs[0] != '\\' && cs[0] != '.'
}

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

// ===========================================================================
// SC2186 / SC2196 / SC2197 — deprecated commands
// ===========================================================================

fn check_deprecated_tempfile(_p: &Parameters, t: &Token, out: &mut Out) {
    if let Some(words) = matched_words(t, CmdKind::Basename, "tempfile") {
        warn(out, words[0].id(), 2186, "tempfile is deprecated. Use mktemp instead.");
    }
}

fn check_deprecated_egrep(_p: &Parameters, t: &Token, out: &mut Out) {
    if let Some(words) = matched_words(t, CmdKind::Basename, "egrep") {
        info(out, words[0].id(), 2196, "egrep is non-standard and deprecated. Use grep -E instead.");
    }
}

fn check_deprecated_fgrep(_p: &Parameters, t: &Token, out: &mut Out) {
    if let Some(words) = matched_words(t, CmdKind::Basename, "fgrep") {
        info(out, words[0].id(), 2197, "fgrep is non-standard and deprecated. Use grep -F instead.");
    }
}

// ===========================================================================
// SC2117 — checkInteractiveSu  (Basename "su")
// ===========================================================================

fn check_interactive_su(params: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "su") {
        Some(w) => w,
        None => return,
    };
    if arguments(words).len() <= 1 {
        let path = get_path(params, t);
        if path.iter().all(|n| su_undirected(n)) {
            info(out, t.id(), 2117, "To run commands as another user, use su -c or sudo.");
        }
    }
}

fn su_undirected(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } if commands.len() >= 2 => false,
        InnerToken::T_Redirecting { redirs, .. } if !redirs.is_empty() => false,
        _ => true,
    }
}

// ===========================================================================
// SC2185 — checkFindWithoutPath  (Basename "find")
// ===========================================================================

fn check_find_without_path(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "find") {
        Some(w) => w,
        None => return,
    };
    let cmd = &words[0];
    let args = arguments(words);
    if !(has_flag(words, "help") || find_has_path(args)) {
        info(out, cmd.id(), 2185, "Some finds don't have a default path. Specify '.' explicitly.");
    }
}

fn find_has_path(args: &[Token]) -> bool {
    match args.split_first() {
        None => false,
        Some((first, rest)) => {
            let flag = get_literal_string_def("___", first);
            !flag.starts_with('-') || (find_is_leading_flag(&flag) && find_has_path(rest))
        }
    }
}

fn find_is_leading_flag(flag: &str) -> bool {
    const LEADING: &str = "-EHLPXdfsxO0123456789";
    flag.chars().count() <= 2 || flag.chars().all(|c| LEADING.contains(c))
}

// ===========================================================================
// SC2253 — checkChmodDashr  (Basename "chmod")
// ===========================================================================

fn check_chmod_dashr(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "chmod") {
        Some(w) => w,
        None => return,
    };
    for a in arguments(words) {
        if get_literal_string(a).as_deref() == Some("-r") {
            warn(out, a.id(), 2253, "Use -R to recurse, or explicitly a-r to remove read permissions.");
        }
    }
}

// ===========================================================================
// SC2267 — checkXargsDashi  (Basename "xargs")
// ===========================================================================

fn check_xargs_dashi(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "xargs") {
        Some(w) => w,
        None => return,
    };
    if let Some(opts) = get_bsd_opts("0oprtxadR:S:J:L:l:n:P:s:e:E:i:I:", arguments(words)) {
        if let Some((_, (option, _))) = opts.iter().find(|(name, _)| name == "i") {
            info(out, option.id(), 2267, "GNU xargs -i is deprecated in favor of -I{}");
        }
    }
}

// ===========================================================================
// SC2172/2173 — checkNonportableSignals  (Exactly "trap")
// ===========================================================================

fn check_nonportable_signals(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Exactly, "trap") {
        Some(w) => w,
        None => return,
    };
    let args = arguments(words);
    match args.split_first() {
        Some((first, rest)) if !is_flag(first) => {
            for param in rest {
                trap_check(param, out);
            }
        }
        _ => {}
    }
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
        warn(out, id, 2172, "Trapping signals by number is not well defined. Prefer signal names.");
    }
    // checkUntrappable
    let lower = str.to_lowercase();
    if matches!(lower.as_str(), "kill" | "9" | "sigkill" | "stop" | "sigstop") {
        err(out, id, 2173, "SIGKILL/SIGSTOP can not be trapped.");
    }
}

// ===========================================================================
// SC2023 — checkTimeParameters  (Exactly "time")
// ===========================================================================

fn check_time_parameters(p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Exactly, "time") {
        Some(w) => w,
        None => return,
    };
    // f (T_SimpleCommand _ _ (cmd:args:_))
    if words.len() < 2 {
        return;
    }
    if !when_shell(p, &[Shell::Bash, Shell::Sh]) {
        return;
    }
    let cmd = &words[0];
    let s = concat_over(&words[1]);
    if s.starts_with('-') && s != "-p" {
        info(
            out,
            cmd.id(),
            2023,
            "The shell may override 'time' as seen in man time(1). Use 'command time ..' for that one.",
        );
    }
}

// ===========================================================================
// SC2176/2177 — checkTimedCommand  (Exactly "time")   [implemented, held back]
// ===========================================================================

fn check_timed_command(p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Exactly, "time") {
        Some(w) => w,
        None => return,
    };
    // f (T_SimpleCommand _ _ (c:args@(_:_)))
    let args = arguments(words);
    if args.is_empty() {
        return;
    }
    if !when_shell(p, &[Shell::Sh, Shell::Dash, Shell::BusyboxSh]) {
        return;
    }
    let c = &words[0];
    let cmd = args.last().unwrap(); // "time" is parsed with a command as argument
    if timed_is_piped(cmd) {
        warn(out, c.id(), 2176, "'time' is undefined for pipelines. time single stage or bash -c instead.");
    }
    if timed_is_simple(cmd) == Some(false) {
        warn(out, cmd.id(), 2177, "'time' is undefined for compound commands, time sh -c instead.");
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

// ===========================================================================
// SC2150 — checkFindExecWithSingleArgument  (Basename "find")
// ===========================================================================

fn check_find_exec_with_single_argument(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "find") {
        Some(w) => w,
        None => return,
    };
    let args = arguments(words);
    // mapMaybe check . tails
    for i in 0..args.len() {
        let window = &args[i..];
        if window.len() < 3 {
            continue;
        }
        let exec = &window[0];
        let arg = &window[1];
        let term = &window[2];
        let exec_s = match get_literal_string(exec) {
            Some(s) => s,
            None => continue,
        };
        let term_s = match get_literal_string(term) {
            Some(s) => s,
            None => continue,
        };
        let cmd_s = get_literal_string_def(" ", arg);
        if !matches!(exec_s.as_str(), "-exec" | "-execdir" | "-ok" | "-okdir") {
            continue;
        }
        if !matches!(term_s.as_str(), ";" | "+") {
            continue;
        }
        if !cmd_s.chars().any(|c| c == ' ' || c == '|' || c == ';') {
            continue;
        }
        warn(
            out,
            exec.id(),
            2150,
            &format!("{0} does not invoke a shell. Rewrite or use {0} sh -c .. .", exec_s),
        );
    }
}

// ===========================================================================
// SC2156 — checkInjectableFindSh  (Basename "find")
// ===========================================================================

fn check_injectable_find_sh(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "find") {
        Some(w) => w,
        None => return,
    };
    let id_strings: Vec<(Id, String)> =
        arguments(words).iter().map(|x| (x.id(), only_literal_string(x))).collect();
    injectable_match(0, &id_strings, out);
}

fn injectable_pred(idx: usize, arg: &str) -> bool {
    match idx {
        0 => matches!(arg, "-exec" | "-execdir" | "-ok" | "-okdir"),
        1 => matches!(arg, "sh" | "bash" | "dash" | "ksh"),
        2 => arg == "-c",
        _ => false,
    }
}
const INJECTABLE_PATTERN_LEN: usize = 3;

/// Faithful port of the recursive `match` in checkInjectableFindSh.
fn injectable_match(test_idx: usize, items: &[(Id, String)], out: &mut Out) {
    if items.is_empty() {
        return;
    }
    if test_idx >= INJECTABLE_PATTERN_LEN {
        // Pattern fully consumed: `action` on the current head.
        let (id, arg) = &items[0];
        if arg.contains("{}") {
            warn(out, *id, 2156, "Injecting filenames is fragile and insecure. Use parameters.");
        }
        return;
    }
    let (_, arg) = &items[0];
    if injectable_pred(test_idx, arg) {
        injectable_match(test_idx + 1, &items[1..], out);
    }
    injectable_match(test_idx, &items[1..], out);
}

// ===========================================================================
// SC2146 — checkFindActionPrecedence  (Basename "find")
// ===========================================================================

fn check_find_action_precedence(_p: &Parameters, t: &Token, out: &mut Out) {
    let words = match matched_words(t, CmdKind::Basename, "find") {
        Some(w) => w,
        None => return,
    };
    let list: Vec<&Token> = arguments(words).iter().collect();
    // pattern = [isMatch, const True, isParam ["-o","-or"], isMatch, const True, isAction]
    const PLEN: usize = 6;
    let mut start = 0;
    while start + PLEN <= list.len() {
        let w = &list[start..start + PLEN];
        if fap_is_match(w[0])
            && fap_is_param(w[2], &["-o", "-or"])
            && fap_is_match(w[3])
            && fap_is_action(w[5])
        {
            warn(out, w[5].id(), 2146, "This action ignores everything before the -o. Use \\( \\) to group.");
            return;
        }
        start += 1;
    }
}

fn fap_is_param(t: &Token, strs: &[&str]) -> bool {
    match get_literal_string(t) {
        Some(s) => strs.contains(&s.as_str()),
        None => false,
    }
}
fn fap_is_match(t: &Token) -> bool {
    fap_is_param(t, &["-name", "-regex", "-iname", "-iregex", "-wholename", "-iwholename"])
}
fn fap_is_action(t: &Token) -> bool {
    fap_is_param(
        t,
        &[
            "-exec", "-execdir", "-delete", "-print", "-print0", "-fls", "-fprint", "-fprint0",
            "-fprintf", "-ls", "-ok", "-okdir", "-printf",
        ],
    )
}

// ===========================================================================
// SC2227 — checkFindRedirections  (Basename "find")
// ===========================================================================

fn check_find_redirections(params: &Parameters, t: &Token, out: &mut Out) {
    if matched_words(t, CmdKind::Basename, "find").is_none() {
        return;
    }
    let redirecting = match get_closest_command(params, t) {
        Some(r) => r,
        None => return,
    };
    if let InnerToken::T_Redirecting { redirs, cmd } = &*redirecting.inner {
        if redirs.is_empty() {
            return;
        }
        if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
            if words.len() < 2 {
                return;
            }
            let min_redir = redirs.iter().map(|r| r.id().0).min().unwrap();
            let max_arg = words.iter().map(|w| w.id().0).max().unwrap();
            if min_redir < max_arg {
                let min_id = redirs.iter().min_by_key(|r| r.id().0).unwrap().id();
                warn(
                    out,
                    min_id,
                    2227,
                    "Redirection applies to the find command itself. Rewrite to work per action (or move to end).",
                );
            }
        }
    }
}

// ===========================================================================
// Tests — ported prop_ functions.
// ===========================================================================

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::interface::Shell;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }
    fn params_for_shell(script: &str, shell: Shell) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, Some(shell), None)
    }
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }
    fn emits_shell(f: fn(&Parameters, &Token, &mut Out), s: &str, shell: Shell) -> bool {
        let params = params_for_shell(s, shell);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // ---- SC2018/2019/2020/2021/2060 checkTr ----
    #[test]
    fn prop_checkTr1() { assert!(emits(check_tr, "tr [a-f] [A-F]")); }
    #[test]
    fn prop_checkTr2() { assert!(emits(check_tr, "tr 'a-z' 'A-Z'")); }
    #[test]
    fn prop_checkTr2a() { assert!(emits(check_tr, "tr '[a-z]' '[A-Z]'")); }
    #[test]
    fn prop_checkTr3() { assert!(!emits(check_tr, "tr -d '[:lower:]'")); }
    #[test]
    fn prop_checkTr3a() { assert!(!emits(check_tr, "tr -d '[:upper:]'")); }
    #[test]
    fn prop_checkTr3b() { assert!(!emits(check_tr, "tr -d '|/_[:upper:]'")); }
    #[test]
    fn prop_checkTr4() { assert!(!emits(check_tr, "ls [a-z]")); }
    #[test]
    fn prop_checkTr5() { assert!(emits(check_tr, "tr foo bar")); }
    #[test]
    fn prop_checkTr6() { assert!(emits(check_tr, "tr 'hello' 'world'")); }
    #[test]
    fn prop_checkTr8() { assert!(!emits(check_tr, "tr aeiou _____")); }
    #[test]
    fn prop_checkTr9() { assert!(!emits(check_tr, "a-z n-za-m")); }
    #[test]
    fn prop_checkTr10() { assert!(!emits(check_tr, "tr --squeeze-repeats rl lr")); }
    #[test]
    fn prop_checkTr11() { assert!(!emits(check_tr, "tr abc '[d*]'")); }
    #[test]
    fn prop_checkTr12() { assert!(!emits(check_tr, "tr '[=e=]' 'e'")); }

    // ---- SC2061 checkFindNameGlob ----
    #[test]
    fn prop_checkFindNameGlob1() { assert!(emits(check_find_name_glob, "find / -name *.php")); }
    #[test]
    fn prop_checkFindNameGlob2() { assert!(emits(check_find_name_glob, "find / -type f -ipath *(foo)")); }
    #[test]
    fn prop_checkFindNameGlob3() { assert!(!emits(check_find_name_glob, "find * -name '*.php'")); }

    // ---- SC2062/2063/2022 checkGrepRe ----
    #[test]
    fn prop_checkGrepRe1() { assert!(emits(check_grep_re, "cat foo | grep *.mp3")); }
    #[test]
    fn prop_checkGrepRe2() { assert!(emits(check_grep_re, "grep -Ev cow*test *.mp3")); }
    #[test]
    fn prop_checkGrepRe3() { assert!(emits(check_grep_re, "grep --regex=*.mp3 file")); }
    #[test]
    fn prop_checkGrepRe4() { assert!(!emits(check_grep_re, "grep foo *.mp3")); }
    #[test]
    fn prop_checkGrepRe5() { assert!(!emits(check_grep_re, "grep-v  --regex=moo *")); }
    #[test]
    fn prop_checkGrepRe6() { assert!(!emits(check_grep_re, "grep foo \\*.mp3")); }
    #[test]
    fn prop_checkGrepRe7() { assert!(emits(check_grep_re, "grep *foo* file")); }
    #[test]
    fn prop_checkGrepRe8() { assert!(emits(check_grep_re, "ls | grep foo*.jpg")); }
    #[test]
    fn prop_checkGrepRe9() { assert!(!emits(check_grep_re, "grep '[0-9]*' file")); }
    #[test]
    fn prop_checkGrepRe10() { assert!(!emits(check_grep_re, "grep '^aa*' file")); }
    #[test]
    fn prop_checkGrepRe11() { assert!(!emits(check_grep_re, "grep --include=*.png foo")); }
    #[test]
    fn prop_checkGrepRe12() { assert!(!emits(check_grep_re, "grep -F 'Foo*' file")); }
    #[test]
    fn prop_checkGrepRe13() { assert!(!emits(check_grep_re, "grep -- -foo bar*")); }
    #[test]
    fn prop_checkGrepRe14() { assert!(!emits(check_grep_re, "grep -e -foo bar*")); }
    #[test]
    fn prop_checkGrepRe15() { assert!(!emits(check_grep_re, "grep --regex -foo bar*")); }
    #[test]
    fn prop_checkGrepRe16() { assert!(!emits(check_grep_re, "grep --include 'Foo*' file")); }
    #[test]
    fn prop_checkGrepRe17() { assert!(!emits(check_grep_re, "grep --exclude 'Foo*' file")); }
    #[test]
    fn prop_checkGrepRe18() { assert!(!emits(check_grep_re, "grep --exclude-dir 'Foo*' file")); }
    #[test]
    fn prop_checkGrepRe19() { assert!(emits(check_grep_re, "grep -- 'Foo*' file")); }
    #[test]
    fn prop_checkGrepRe20() { assert!(!emits(check_grep_re, "grep --fixed-strings 'Foo*' file")); }
    #[test]
    fn prop_checkGrepRe21() { assert!(!emits(check_grep_re, "grep -o 'x*' file")); }
    #[test]
    fn prop_checkGrepRe22() { assert!(!emits(check_grep_re, "grep --only-matching 'x*' file")); }
    #[test]
    fn prop_checkGrepRe23() { assert!(!emits(check_grep_re, "grep '.*' file")); }

    // ---- SC2186/2196/2197 deprecated ----
    #[test]
    fn prop_checkDeprecatedTempfile1() { assert!(emits(check_deprecated_tempfile, "var=$(tempfile)")); }
    #[test]
    fn prop_checkDeprecatedTempfile2() { assert!(!emits(check_deprecated_tempfile, "tempfile=$(mktemp)")); }
    #[test]
    fn prop_checkDeprecatedEgrep() { assert!(emits(check_deprecated_egrep, "egrep '.+'")); }
    #[test]
    fn prop_checkDeprecatedFgrep() { assert!(emits(check_deprecated_fgrep, "fgrep '*' files")); }

    // ---- SC2117 checkInteractiveSu ----
    #[test]
    fn prop_checkInteractiveSu1() { assert!(emits(check_interactive_su, "su; rm file; su $USER")); }
    #[test]
    fn prop_checkInteractiveSu2() { assert!(emits(check_interactive_su, "su foo; something; exit")); }
    #[test]
    fn prop_checkInteractiveSu3() { assert!(!emits(check_interactive_su, "echo rm | su foo")); }
    #[test]
    fn prop_checkInteractiveSu4() { assert!(!emits(check_interactive_su, "su root < script")); }

    // ---- SC2185 checkFindWithoutPath ----
    #[test]
    fn prop_checkFindWithoutPath1() { assert!(emits(check_find_without_path, "find -type f")); }
    #[test]
    fn prop_checkFindWithoutPath2() { assert!(emits(check_find_without_path, "find")); }
    #[test]
    fn prop_checkFindWithoutPath3() { assert!(!emits(check_find_without_path, "find . -type f")); }
    #[test]
    fn prop_checkFindWithoutPath4() { assert!(!emits(check_find_without_path, "find -H -L \"$path\" -print")); }
    #[test]
    fn prop_checkFindWithoutPath5() { assert!(!emits(check_find_without_path, "find -O3 .")); }
    #[test]
    fn prop_checkFindWithoutPath6() { assert!(!emits(check_find_without_path, "find -D exec .")); }
    #[test]
    fn prop_checkFindWithoutPath7() { assert!(!emits(check_find_without_path, "find --help")); }
    #[test]
    fn prop_checkFindWithoutPath8() { assert!(!emits(check_find_without_path, "find -Hx . -print")); }

    // ---- SC2253 checkChmodDashr ----
    #[test]
    fn prop_checkChmodDashr1() { assert!(emits(check_chmod_dashr, "chmod -r 0755 dir")); }
    #[test]
    fn prop_checkChmodDashr2() { assert!(!emits(check_chmod_dashr, "chmod -R 0755 dir")); }
    #[test]
    fn prop_checkChmodDashr3() { assert!(!emits(check_chmod_dashr, "chmod a-r dir")); }

    // ---- SC2267 checkXargsDashi ----
    #[test]
    fn prop_checkXargsDashi1() { assert!(emits(check_xargs_dashi, "xargs -i{} echo {}")); }
    #[test]
    fn prop_checkXargsDashi2() { assert!(!emits(check_xargs_dashi, "xargs -I{} echo {}")); }
    #[test]
    fn prop_checkXargsDashi3() { assert!(!emits(check_xargs_dashi, "xargs sed -i -e foo")); }
    #[test]
    fn prop_checkXargsDashi4() { assert!(emits(check_xargs_dashi, "xargs -e sed -i foo")); }
    #[test]
    fn prop_checkXargsDashi5() { assert!(!emits(check_xargs_dashi, "xargs -x sed -i foo")); }

    // ---- SC2172/2173 checkNonportableSignals ----
    #[test]
    fn prop_checkNonportableSignals1() { assert!(emits(check_nonportable_signals, "trap f 8")); }
    #[test]
    fn prop_checkNonportableSignals2() { assert!(!emits(check_nonportable_signals, "trap f 0")); }
    #[test]
    fn prop_checkNonportableSignals3() { assert!(!emits(check_nonportable_signals, "trap f 14")); }
    #[test]
    fn prop_checkNonportableSignals4() { assert!(emits(check_nonportable_signals, "trap f SIGKILL")); }
    #[test]
    fn prop_checkNonportableSignals5() { assert!(emits(check_nonportable_signals, "trap f 9")); }
    #[test]
    fn prop_checkNonportableSignals6() { assert!(emits(check_nonportable_signals, "trap f stop")); }
    #[test]
    fn prop_checkNonportableSignals7() { assert!(!emits(check_nonportable_signals, "trap 'stop' int")); }

    // ---- SC2023 checkTimeParameters ----
    #[test]
    fn prop_checkTimeParameters1() { assert!(emits_shell(check_time_parameters, "time -f lol sleep 10", Shell::Bash)); }
    #[test]
    fn prop_checkTimeParameters2() { assert!(!emits_shell(check_time_parameters, "time sleep 10", Shell::Bash)); }
    #[test]
    fn prop_checkTimeParameters3() { assert!(!emits_shell(check_time_parameters, "time -p foo", Shell::Bash)); }
    #[test]
    fn prop_checkTimeParameters4() { assert!(!emits_shell(check_time_parameters, "command time -f lol sleep 10", Shell::Bash)); }

    // ---- SC2150 checkFindExecWithSingleArgument ----
    #[test]
    fn prop_checkFindExecWithSingleArgument1() { assert!(emits(check_find_exec_with_single_argument, "find . -exec 'cat {} | wc -l' \\;")); }
    #[test]
    fn prop_checkFindExecWithSingleArgument2() { assert!(emits(check_find_exec_with_single_argument, "find . -execdir 'cat {} | wc -l' +")); }
    #[test]
    fn prop_checkFindExecWithSingleArgument3() { assert!(!emits(check_find_exec_with_single_argument, "find . -exec wc -l {} \\;")); }

    // ---- SC2156 checkInjectableFindSh ----
    #[test]
    fn prop_checkInjectableFindSh1() { assert!(emits(check_injectable_find_sh, "find . -exec sh -c 'echo {}' \\;")); }
    #[test]
    fn prop_checkInjectableFindSh2() { assert!(emits(check_injectable_find_sh, "find . -execdir bash -c 'rm \"{}\"' ';'")); }
    #[test]
    fn prop_checkInjectableFindSh3() { assert!(!emits(check_injectable_find_sh, "find . -ok sh -c 'rm \"$@\"' _ {} \\;")); }

    // ---- SC2146 checkFindActionPrecedence ----
    #[test]
    fn prop_checkFindActionPrecedence1() { assert!(emits(check_find_action_precedence, "find . -name '*.wav' -o -name '*.au' -exec rm {} +")); }
    #[test]
    fn prop_checkFindActionPrecedence2() { assert!(!emits(check_find_action_precedence, "find . -name '*.wav' -o \\( -name '*.au' -exec rm {} + \\)")); }
    #[test]
    fn prop_checkFindActionPrecedence3() { assert!(!emits(check_find_action_precedence, "find . -name '*.wav' -o -name '*.au'")); }

    // ---- SC2227 checkFindRedirections ----
    #[test]
    fn prop_checkFindRedirections1() { assert!(emits(check_find_redirections, "find . -exec echo {} > file \\;")); }
    #[test]
    fn prop_checkFindRedirections2() { assert!(!emits(check_find_redirections, "find . -exec echo {} \\; > file")); }
    #[test]
    fn prop_checkFindRedirections3() { assert!(!emits(check_find_redirections, "find . -execdir sh -c 'foo > file' \\;")); }

    // ---- SC2176/2177 checkTimedCommand ----
    #[test]
    fn prop_checkTimedCommand1() { assert!(emits_shell(check_timed_command, "#!/bin/sh\ntime -p foo | bar", Shell::Sh)); }
    #[test]
    fn prop_checkTimedCommand2() { assert!(emits_shell(check_timed_command, "#!/bin/dash\ntime ( foo; bar; )", Shell::Dash)); }
    #[test]
    fn prop_checkTimedCommand3() { assert!(!emits_shell(check_timed_command, "#!/bin/sh\ntime sleep 1", Shell::Sh)); }
}
