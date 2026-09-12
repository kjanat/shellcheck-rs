//! Ported check batch e. See rust/PORTING.md.
//!
//! Ported checks (pure AST patterns; no CFG/arithmetic dependencies):
//! - SC2016  checkSingleQuotedVariables — `$var`/backticks inside single quotes
//! - SC2027  checkInexplicablyUnquoted (expansion-inside-quotes branch)
//! - SC2140  checkInexplicablyUnquoted (adjacent-quoted-literal branch, condition-free)
//!
//! Skipped:
//! - SC2089/SC2090 (checkQuotesInLiterals) — needs `doVariableFlowAnalysis`
//!   (dataflow), which is not yet ported.
//! - SC2026 (the sibling branch of checkInexplicablyUnquoted) — not assigned.
//!
//! The parser already produces `TC_*`/`T_Condition`, so the `[ -v .. ]` branch
//! of SC2016's `isOkAssignment` is ported. The `[[ .. =~ .. ]]` sub-case of
//! SC2140's `isSpecial` (the `TC_Binary "=~"` clause) is intentionally left out
//! (no such construct hits SC2140 in the corpus); the T_Redirecting and
//! T_DollarBraced clauses of `isSpecial` are ported.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::get_command;
use crate::astlib::basename;
use crate::analyzer_lib::get_closest_command;
use crate::astlib::is_flag;
use crate::astlib::get_word_parts;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::interface::Shell;

pub fn register(c: &mut Checker) {
    c.node(check_single_quoted_variables);
    c.node(check_inexplicably_unquoted);
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib/AnalyzerLib; kept local so this
// module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

fn simple_command_words(t: &Token) -> Option<&Vec<Token>> {
    let cmd = get_command(t)?;
    if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
        Some(words)
    } else {
        None
    }
}

/// `getEffectiveCommandToken` for exec: parse `getBsdOpts "cla:"` and return the
/// first positional argument token. Returns None if the option string is
/// unrecognized (Haskell `getBsdOpts` returns Nothing) or no positional exists.
fn exec_effective(args: &[Token]) -> Option<&Token> {
    fn needs_arg(c: char) -> Option<bool> {
        match c {
            'c' | 'l' => Some(false),
            'a' => Some(true),
            _ => None,
        }
    }
    let mut i = 0;
    while i < args.len() {
        let s = astlib::get_literal_string(&args[i]).unwrap_or_else(|| "\0".to_string());
        if s == "--" {
            return args.get(i + 1);
        } else if s.starts_with("--") {
            // Unknown long option (no longopts in "cla:") -> getBsdOpts Nothing.
            return None;
        } else if s.starts_with('-') && s.len() > 1 {
            let cluster: Vec<char> = s[1..].chars().collect();
            let mut ci = 0;
            loop {
                if ci >= cluster.len() {
                    i += 1;
                    break;
                }
                match needs_arg(cluster[ci]) {
                    None => return None, // unknown flag -> parse failure
                    Some(false) => ci += 1,
                    Some(true) => {
                        if ci + 1 == cluster.len() {
                            // arg is the next token
                            i += 2;
                        } else {
                            // arg is the rest of the cluster
                            i += 1;
                        }
                        break;
                    }
                }
            }
        } else {
            // positional (gnu = false)
            return Some(&args[i]);
        }
    }
    None
}

fn get_command_basename(t: &Token) -> Option<String> {
    get_command_name(t).map(|s| basename(&s))
}

// ---------------------------------------------------------------------------
// SC2016 — checkSingleQuotedVariables
// ---------------------------------------------------------------------------

/// `re = \$[{(0-9a-zA-Z_]|`[^`]+``
fn matches_expansion_re(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b'$' {
            if let Some(&c) = bytes.get(i + 1) {
                let ch = c as char;
                if ch == '{' || ch == '(' || ch.is_ascii_alphanumeric() || ch == '_' {
                    return true;
                }
            }
        }
        if bytes[i] == b'`' {
            // `[^`]+`
            let mut j = i + 1;
            let mut count = 0;
            while j < bytes.len() && bytes[j] != b'`' {
                j += 1;
                count += 1;
            }
            if count > 0 && j < bytes.len() && bytes[j] == b'`' {
                return true;
            }
        }
    }
    false
}

/// `sedContra = \$[{dpsaic]($|[^a-zA-Z])`
fn matches_sed_contra(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b'$' {
            if let Some(&c) = bytes.get(i + 1) {
                if matches!(c, b'{' | b'd' | b'p' | b's' | b'a' | b'i' | b'c') {
                    match bytes.get(i + 2) {
                        None => return true,
                        Some(&after) => {
                            if !(after as char).is_ascii_alphabetic() {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

fn get_find_command(cmd: &Token) -> String {
    let words = match simple_command_words(cmd) {
        Some(w) => w,
        None => return "find".to_string(),
    };
    let lits: Vec<Option<String>> = words.iter().map(astlib::get_literal_string).collect();
    let exec_flags = ["-exec", "-execdir", "-ok", "-okdir"];
    // dropWhile (not in exec_flags)
    let start = lits.iter().position(|x| {
        x.as_deref()
            .map(|s| exec_flags.contains(&s))
            .unwrap_or(false)
    });
    match start {
        Some(idx) => {
            // cmd is at idx+1 (flag:cmd:rest)
            match lits.get(idx + 1) {
                Some(Some(c)) => c.clone(),
                _ => "find".to_string(),
            }
        }
        None => "find".to_string(),
    }
}

fn get_git_command(cmd: &Token) -> String {
    if let Some(words) = simple_command_words(cmd) {
        let lits: Vec<Option<String>> = words.iter().map(astlib::get_literal_string).collect();
        if lits.first().and_then(|x| x.as_deref()) == Some("git")
            && lits.get(1).and_then(|x| x.as_deref()) == Some("filter-branch")
        {
            return "git filter-branch".to_string();
        }
    }
    "git".to_string()
}

fn get_mumps_command(cmd: &Token) -> String {
    if let Some(words) = simple_command_words(cmd) {
        let lits: Vec<Option<String>> = words.iter().map(astlib::get_literal_string).collect();
        if lits.first().and_then(|x| x.as_deref()) == Some("mumps")
            && lits.get(1).and_then(|x| x.as_deref()) == Some("-run")
        {
            match lits.get(2).and_then(|x| x.as_deref()) {
                Some("%XCMD") => return "mumps -run %XCMD".to_string(),
                Some("LOOP%XCMD") => return "mumps -run LOOP%XCMD".to_string(),
                _ => {}
            }
        }
    }
    "mumps".to_string()
}

const SC2016_OK_COMMANDS: &[&str] = &[
    "trap",
    "sh",
    "bash",
    "ksh",
    "zsh",
    "ssh",
    "eval",
    "xprop",
    "alias",
    "sudo",
    "doas",
    "run0",
    "docker",
    "podman",
    "oc",
    "dpkg-query",
    "jq",
    "rename",
    "rg",
    "unset",
    "git filter-branch",
    "mumps -run %XCMD",
    "mumps -run LOOP%XCMD",
];

const SC2016_COMMONLY_QUOTED: &[&str] = &["PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND"];

fn check_single_quoted_variables(params: &Parameters, t: &Token, out: &mut Out) {
    let s = match &*t.inner {
        InnerToken::T_SingleQuoted(s) => s,
        _ => return,
    };
    if !matches_expansion_re(s) {
        return;
    }

    let closest = get_closest_command(params, t);

    let command_name: String = closest
        .and_then(|cmd| get_command_basename(cmd).map(|name| (cmd, name)))
        .map(|(cmd, name)| {
            if name == "find" {
                get_find_command(cmd)
            } else if name == "git" {
                get_git_command(cmd)
            } else if name == "mumps" {
                get_mumps_command(cmd)
            } else {
                name
            }
        })
        .unwrap_or_default();

    let show = |out: &mut Out| {
        info(
            out,
            t.id(),
            2016,
            "Expressions don't expand in single quotes, use double quotes for that.",
        );
    };

    if command_name == "sed" {
        if !matches_sed_contra(s) {
            show(out);
        }
        return;
    }

    // isProbablyOk
    let ok_assignment = {
        // any isOkAssignment (NE.take 3 $ getPath parents t)
        let mut ok = false;
        let mut cur = Some(t);
        for _ in 0..3 {
            match cur {
                Some(node) => {
                    match &*node.inner {
                        InnerToken::T_Assignment { var, .. }
                            if SC2016_COMMONLY_QUOTED.contains(&var.as_str()) =>
                        {
                            ok = true;
                            break;
                        }
                        InnerToken::TC_Unary { op, .. } if op == "-v" => {
                            ok = true;
                            break;
                        }
                        _ => {}
                    }
                    cur = params.parent(node);
                }
                None => break,
            }
        }
        ok
    };

    let is_probably_ok = ok_assignment
        || SC2016_OK_COMMANDS.contains(&command_name.as_str())
        || command_name.ends_with("awk")
        || command_name.starts_with("perl");

    if !is_probably_ok {
        show(out);
    }
}

// ---------------------------------------------------------------------------
// SC2027 / SC2140 — checkInexplicablyUnquoted
// ---------------------------------------------------------------------------

/// `quotesSingleThing`: the inner token list of a "..." is a single expansion.
fn quotes_single_thing(parts: &[Token]) -> bool {
    parts.len() == 1
        && matches!(
            &*parts[0].inner,
            InnerToken::T_DollarExpansion(_)
                | InnerToken::T_DollarBraced { .. }
                | InnerToken::T_Backticked(_)
        )
}

/// `isSpecial` over `getPath trapped`. Regexes in `[[ .. =~ re ]]` and the
/// contents of `${x+"foo" "bar"}` parse metacharacters as unquoted literals, so
/// avoid overtriggering there.
fn is_special(params: &Parameters, trapped: &Token) -> bool {
    // getPath = [trapped, parent, grandparent, ...]; recurse tail-wise.
    let mut cur = Some(trapped);
    while let Some(node) = cur {
        match &*node.inner {
            InnerToken::T_Redirecting { .. } => return false,
            InnerToken::T_DollarBraced { .. } => return true,
            _ => {}
        }
        // (a : TC_Binary _ _ "=~" lhs rhs : rest) -> getId a == getId rhs
        if let Some(parent) = params.parent(node) {
            if let InnerToken::TC_Binary { op, rhs, .. } = &*parent.inner {
                if op == "=~" && rhs.id() == node.id() {
                    return true;
                }
            }
        }
        cur = params.parent(node);
    }
    false
}

fn check_inexplicably_unquoted(params: &Parameters, t: &Token, out: &mut Out) {
    let tokens = match &*t.inner {
        InnerToken::T_NormalWord(l) => l,
        _ => return,
    };
    // mapM_ check (tails tokens): examine each suffix's leading triple.
    for start in 0..tokens.len() {
        let a = &tokens[start];
        let trapped = match tokens.get(start + 1) {
            Some(x) => x,
            None => break,
        };
        let b = match tokens.get(start + 2) {
            Some(x) => x,
            None => break,
        };
        let (a_parts, b_parts) = match (&*a.inner, &*b.inner) {
            (InnerToken::T_DoubleQuoted(ap), InnerToken::T_DoubleQuoted(bp)) => (ap, bp),
            _ => continue,
        };
        match &*trapped.inner {
            InnerToken::T_DollarExpansion(_) | InnerToken::T_DollarBraced { .. } => {
                warn(
                    out,
                    trapped.id(),
                    2027,
                    "The surrounding quotes actually unquote this. Remove or escape them.",
                );
            }
            InnerToken::T_Literal(s) => {
                let excluded = (quotes_single_thing(a_parts) && quotes_single_thing(b_parts))
                    || s == "="
                    || s == ":"
                    || s == "/"
                    || is_special(params, trapped);
                if !excluded {
                    warn(
                        out,
                        trapped.id(),
                        2140,
                        "Word is of the form \"A\"B\"C\" (B indicated). Did you mean \"ABC\" or \"A\\\"B\\\"C\"?",
                    );
                }
            }
            _ => {}
        }
    }
}
