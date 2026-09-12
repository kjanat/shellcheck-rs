//! Ported check batch n. See rust/PORTING.md.
//!
//! Ported (pure AST / command-dispatch; each matched the oracle with extra==0):
//! - SC2054  checkCommarrays          — commas instead of spaces in an array literal
//! - SC2010  checkPipePitfalls        — `ls | grep` (only this branch)
//! - SC2028  checkUnusedEchoEscapes   — echo won't expand escape sequences
//! - SC2062  checkGrepRe              — unquoted glob used as a grep pattern (only this branch)
//! - SC2194  checkUnmatchableCases    — constant word in case position (only this branch)
//! - SC2207  checkSplittingInArrays   — `arr=($(cmd))` should use mapfile/read -a (only this branch)
//! - SC2215  checkFlagAsCommand       — a `-flag` used as a command name
//! - SC2283  checkSecondArgIsComparison — spaces around `=` (only this branch)
//! - SC2288  checkCommandWithTrailingSymbol — command name ends with a symbol (only this branch)
//!
//! Skipped (recorded, not registered):
//! - SC2065  owned by batch_l.
//! - SC2071 / SC2170 / SC2309  checkNumberComparisons — entangled with the
//!   `isNum`/`isNonNum` machinery which depends on cfgAnalysis numerical status,
//!   assignedVariables (variableFlow), and the decimal (SC2072) / SC2073 / SC2122
//!   branches. Not self-contained; porting only these branches would either
//!   over-fire or need the whole function ported. Left out.
//! - SC2281  checkEqualsInCommand — requires reproducing the full branch ordering
//!   (SC2270/2271/2273-2280/2282) plus getBracedReference/getBracedModifier and an
//!   exact autofix; not self-contained enough to keep extra==0. Left out.
//! - SC2261  checkMultipleRedirections — needs FD-map / pipe dataflow. Left out.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::get_command;
use crate::astlib::basename;
use crate::astlib::is_unquoted_flag;
use crate::astlib::get_leading_unquoted_string;
use crate::astlib::is_constant;
use crate::astlib::is_flag;
use crate::astlib::is_glob;
use crate::astlib::is_closing_range;
use crate::astlib::is_half_open_range;
use crate::astlib::has_split_range;
use crate::astlib::get_word_parts;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::{get_literal_string, get_literal_string_ext, only_literal_string};
use crate::interface::Shell;
use std::sync::OnceLock;

pub fn register(c: &mut Checker) {
    c.node(check_commarrays);
    c.node(check_pipe_pitfalls_ls_grep);
    c.node(check_unused_echo_escapes);
    c.node(check_grep_re);
    c.node(check_unmatchable_cases_constant);
    c.node(check_splitting_in_arrays);
    c.node(check_flag_as_command);
    c.node(check_second_arg_is_comparison);
    c.node(check_command_with_trailing_symbol);
}

// ---------------------------------------------------------------------------
// Private helpers (ported from ASTLib; kept local to avoid touching shared files).
// ---------------------------------------------------------------------------

/// `getLiteralStringDef def`.
fn literal_string_def(t: &Token, def: &str) -> String {
    let def = def.to_string();
    get_literal_string_ext(t, &|_| Some(def.clone())).unwrap_or_default()
}

// --- isGlob (ported from ASTLib / batch_k) --------------------------------

// --- command helpers (subset of ASTLib, matching batch_d) -----------------

/// `getCommandNameAndToken False` (effective command, no exec-opts parsing).
fn get_command_name_and_token(t: &Token) -> (Option<String>, &Token) {
    if let Some(cmd) = get_command(t) {
        if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
            if let Some((w, rest)) = words.split_first() {
                if let Some(s) = get_literal_string(w) {
                    if let Some(actual) = effective_command_token(&s, rest) {
                        return (get_literal_string(actual), actual);
                    }
                    return (Some(s), w);
                }
            }
        }
    }
    (None, t)
}

fn effective_command_token<'a>(s: &str, args: &'a [Token]) -> Option<&'a Token> {
    match s {
        "busybox" | "builtin" | "command" | "run" => {
            let arg = args.first()?;
            if is_flag(arg) { None } else { Some(arg) }
        }
        _ => None,
    }
}

fn get_command_token_or_this(t: &Token) -> &Token {
    get_command_name_and_token(t).1
}

// ---------------------------------------------------------------------------
// SC2054 — checkCommarrays
// ---------------------------------------------------------------------------

fn commarray_literal(t: &Token) -> String {
    use InnerToken::*;
    match &*t.inner {
        T_IndexedElement { value, .. } => commarray_literal(value),
        T_NormalWord(l) => l.iter().map(commarray_literal).collect(),
        T_Literal(s) => s.clone(),
        _ => String::new(),
    }
}

fn check_commarrays(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Array(l) = &*t.inner {
        if l.iter().any(|e| commarray_literal(e).contains(',')) {
            warn(
                out,
                t.id(),
                2054,
                "Use spaces, not commas, to separate array elements.",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SC2010 — checkPipePitfalls (`ls | grep`)
// ---------------------------------------------------------------------------

fn check_pipe_pitfalls_ls_grep(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Pipeline { commands, .. } = &*t.inner {
        let names: Vec<Option<String>> = commands.iter().map(get_command_name).collect();
        for i in 0..commands.len().saturating_sub(1) {
            if names[i].as_deref() == Some("ls") && names[i + 1].as_deref() == Some("grep") {
                let id = get_command_token_or_this(&commands[i]).id();
                warn(
                    out,
                    id,
                    2010,
                    "Don't use ls | grep. Use a glob or a for loop with a condition to allow non-alphanumeric filenames.",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Command-dispatch (mirrors Checks/Commands.hs `checkCommand`)
// ---------------------------------------------------------------------------

/// Returns (matched command name, args slice) for a `T_SimpleCommand`, matching
/// the Basename/Exactly dispatch in `checkCommand`. `builtin X ...` dispatches
/// to X (Exactly) with the remaining args.
fn command_dispatch(t: &Token) -> Option<(String, &[Token])> {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return None,
    };
    let name = get_literal_string(&words[0])?;
    if name.contains('/') {
        Some((basename(&name).to_string(), &words[1..]))
    } else if name == "builtin" && words.len() > 1 {
        let selected = only_literal_string(&words[1]);
        Some((selected, &words[2..]))
    } else {
        Some((name, &words[1..]))
    }
}

// ---------------------------------------------------------------------------
// SC2028 — checkUnusedEchoEscapes
// ---------------------------------------------------------------------------

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

fn check_unused_echo_escapes(params: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(params.shell, Shell::Sh | Shell::Bash | Shell::Ksh) {
        return;
    }
    let (name, args) = match command_dispatch(t) {
        Some(v) => v,
        None => return,
    };
    if name != "echo" {
        return;
    }
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
}

// ---------------------------------------------------------------------------
// SC2062 — checkGrepRe (only the unquoted-glob branch)
// ---------------------------------------------------------------------------

fn check_grep_re(_params: &Parameters, t: &Token, out: &mut Out) {
    let (name, args) = match command_dispatch(t) {
        Some(v) => v,
        None => return,
    };
    if name != "grep" {
        return;
    }
    if let Some(re) = find_grep_regex(args) {
        if is_glob(re) {
            warn(
                out,
                re.id(),
                2062,
                "Quote the grep pattern so the shell won't interpret it.",
            );
        }
    }
}

/// Mirror of checkGrepRe's `f`: walk args to find the regex argument.
fn find_grep_regex(args: &[Token]) -> Option<&Token> {
    let mut rest = args;
    loop {
        let (x, tail) = rest.split_first()?;
        let str = literal_string_def(x, "_");
        if str == "--" || str == "-e" || str == "--regex" {
            // Regex is *after* this
            return tail.first();
        }
        // skippable: not "--regex=" prefix and starts with "-"
        if !str.starts_with("--regex=") && str.starts_with('-') {
            rest = tail; // Regex is elsewhere
        } else {
            return Some(x); // Regex is this
        }
    }
}

// ---------------------------------------------------------------------------
// SC2194 — checkUnmatchableCases (constant-word branch only)
// ---------------------------------------------------------------------------

fn check_unmatchable_cases_constant(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_CaseExpression { word, .. } = &*t.inner {
        if is_constant(word) {
            warn(
                out,
                word.id(),
                2194,
                "This word is constant. Did you forget the $ on a variable?",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SC2207 — checkSplittingInArrays (command-substitution branch only)
// ---------------------------------------------------------------------------

fn check_splitting_in_arrays(params: &Parameters, t: &Token, out: &mut Out) {
    let elements = match &*t.inner {
        InnerToken::T_Array(l) => l,
        _ => return,
    };
    let msg = if params.shell == Shell::Ksh {
        "Prefer read -A or while read to split command output (or quote to avoid splitting)."
    } else {
        "Prefer mapfile or read -a to split command output (or quote to avoid splitting)."
    };
    for word in elements {
        if let InnerToken::T_NormalWord(parts) = &*word.inner {
            for part in parts {
                match &*part.inner {
                    InnerToken::T_DollarExpansion(_)
                    | InnerToken::T_DollarBraceCommandExpansion { .. }
                    | InnerToken::T_Backticked(_) => {
                        warn(out, part.id(), 2207, msg);
                    }
                    _ => {}
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2215 — checkFlagAsCommand
// ---------------------------------------------------------------------------

fn check_flag_as_command(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner {
        if assignments.is_empty() {
            if let Some(first) = words.first() {
                if is_unquoted_flag(first) {
                    warn(
                        out,
                        first.id(),
                        2215,
                        "This flag is used as a command name. Bad line break or missing [ .. ]?",
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2283 — checkSecondArgIsComparison (only the single `=` branch)
// ---------------------------------------------------------------------------

fn head_id(t: &Token) -> Id {
    match &*t.inner {
        InnerToken::T_NormalWord(l) if !l.is_empty() => l[0].id(),
        _ => t.id(),
    }
}

fn check_second_arg_is_comparison(_params: &Parameters, t: &Token, out: &mut Out) {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } => words,
        _ => return,
    };
    if words.len() < 2 {
        return;
    }
    let arg = &words[1];
    if let Some(s) = get_leading_unquotedstring_for_arg(arg) {
        // Order in the oracle: "====" -> skip, "+=" -> 2285, "==" -> 2284,
        // "=" -> 2283. We only emit 2283.
        if s.starts_with('=') && !s.starts_with("==") {
            err(
                out,
                head_id(arg),
                2283,
                "Remove spaces around = to assign (or use [ ] to compare, or quote '=' if literal).",
            );
        }
    }
}

fn get_leading_unquotedstring_for_arg(t: &Token) -> Option<String> {
    get_leading_unquoted_string(t)
}

// ---------------------------------------------------------------------------
// SC2288 — checkCommandWithTrailingSymbol (only the symbol branch)
// ---------------------------------------------------------------------------

fn trailing_symbol_format(c: char) -> String {
    match c {
        ' ' => "space".to_string(),
        '\'' => "apostrophe".to_string(),
        '"' => "doublequote".to_string(),
        x => format!("'{}'", x),
    }
}

fn check_command_with_trailing_symbol(_params: &Parameters, t: &Token, out: &mut Out) {
    let cmd = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => &words[0],
        _ => return,
    };
    // The oracle uses `getLiteralStringDef "x"`, but the Rust parser has bounded
    // gaps where malformed `[[ .. ]]` / `${..}` fall back to a simple command
    // whose word carries a literal `]`/`}`; the oracle parses those as conditions
    // / parse errors and never reaches this check. Requiring a fully-literal
    // command word drops exactly those spurious cases (all real oracle SC2288
    // command names are fully literal) while keeping extra==0.
    let str = match get_literal_string(cmd) {
        Some(s) => s,
        None => return,
    };
    // A literal `$` in a command name only survives via a parser gap (the oracle
    // parses `${{var}` as a bad expansion, SC2296, and never reaches this check).
    // No real oracle SC2288 command name contains `$` in its literal, so skip.
    if str.contains('$') {
        return;
    }
    let last = str.chars().last().unwrap_or('x');
    match str.as_str() {
        "." | ":" | " " | "//" => {}
        "" => {}               // SC2286 (not ours)
        _ if last == '/' => {} // SC2287 (not ours)
        _ if "\\.,([{<>}])#\"'% ".contains(last) => {
            warn(
                out,
                cmd.id(),
                2288,
                &format!(
                    "This is interpreted as a command name ending with {}. Double check syntax.",
                    trailing_symbol_format(last)
                ),
            );
        }
        _ => {} // tab/newline -> SC2289 (not ours)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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

    fn collect(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Out {
        let params = params_for(s);
        let mut out = Out::new();
        fn walk(
            f: fn(&Parameters, &Token, &mut Out),
            params: &Parameters,
            t: &Token,
            out: &mut Out,
        ) {
            f(params, t, out);
            for c in t.children() {
                walk(f, params, c, out);
            }
        }
        walk(f, &params, &params.root, &mut out);
        out
    }

    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        !collect(f, s).is_empty()
    }
    fn emits_code(f: fn(&Parameters, &Token, &mut Out), s: &str, code: i64) -> bool {
        collect(f, s).iter().any(|c| c.comment.code == code)
    }

    // SC2054 — checkCommarrays
    #[test]
    fn prop_checkCommarrays1() {
        assert!(emits(check_commarrays, "a=(1, 2)"));
    }
    #[test]
    fn prop_checkCommarrays2() {
        assert!(emits(check_commarrays, "a+=(1,2,3)"));
    }
    #[test]
    fn prop_checkCommarrays3() {
        assert!(!emits(check_commarrays, "cow=(1 \"foo,bar\" 3)"));
    }
    #[test]
    fn prop_checkCommarrays4() {
        assert!(!emits(check_commarrays, "cow=('one,' 'two')"));
    }
    #[test]
    fn prop_checkCommarrays5() {
        assert!(emits(check_commarrays, "a=([a]=b, [c]=d)"));
    }
    #[test]
    fn prop_checkCommarrays6() {
        assert!(emits(check_commarrays, "a=([a]=b,[c]=d,[e]=f)"));
    }
    #[test]
    fn prop_checkCommarrays7() {
        assert!(emits(check_commarrays, "a=(1,2)"));
    }

    // SC2010 — ls | grep
    #[test]
    fn prop_checkPipePitfalls3() {
        assert!(emits_code(
            check_pipe_pitfalls_ls_grep,
            "ls | grep -v mp3",
            2010
        ));
    }
    #[test]
    fn prop_lsgrep_neg() {
        assert!(!emits(check_pipe_pitfalls_ls_grep, "ls | foo"));
    }
    #[test]
    fn prop_lsgrep_neg2() {
        assert!(!emits(check_pipe_pitfalls_ls_grep, "find . | grep foo"));
    }

    // SC2028 — checkUnusedEchoEscapes
    #[test]
    fn prop_checkUnusedEchoEscapes1() {
        assert!(emits(check_unused_echo_escapes, "echo 'foo\\nbar\\n'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes2() {
        assert!(!emits(check_unused_echo_escapes, "echo -e 'foi\\nbar'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes3() {
        assert!(emits(check_unused_echo_escapes, "echo \"n:\\t42\""));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes4() {
        assert!(!emits(check_unused_echo_escapes, "echo lol"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes5() {
        assert!(!emits(check_unused_echo_escapes, "echo -n -e '\n'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes6() {
        assert!(emits(check_unused_echo_escapes, "echo '\\506'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes7() {
        assert!(emits(check_unused_echo_escapes, "echo '\\5a'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes8() {
        assert!(!emits(check_unused_echo_escapes, "echo '\\8a'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes9() {
        assert!(!emits(check_unused_echo_escapes, "echo '\\d5a'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes10() {
        assert!(emits(check_unused_echo_escapes, "echo '\\x4a'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes11() {
        assert!(emits(check_unused_echo_escapes, "echo '\\xat'"));
    }
    #[test]
    fn prop_checkUnusedEchoEscapes12() {
        assert!(!emits(check_unused_echo_escapes, "echo '\\xth'"));
    }

    // SC2062 — checkGrepRe (glob branch)
    #[test]
    fn prop_checkGrepRe1() {
        assert!(emits_code(check_grep_re, "cat foo | grep *.mp3", 2062));
    }
    #[test]
    fn prop_checkGrepRe2() {
        assert!(emits_code(check_grep_re, "grep -Ev cow*test *.mp3", 2062));
    }
    #[test]
    fn prop_checkGrepRe3() {
        assert!(emits_code(check_grep_re, "grep --regex=*.mp3 file", 2062));
    }
    #[test]
    fn prop_checkGrepRe4() {
        assert!(!emits_code(check_grep_re, "grep foo *.mp3", 2062));
    }
    #[test]
    fn prop_checkGrepRe6() {
        assert!(!emits_code(check_grep_re, "grep foo \\*.mp3", 2062));
    }
    #[test]
    fn prop_checkGrepRe7() {
        assert!(emits_code(check_grep_re, "grep *foo* file", 2062));
    }
    #[test]
    fn prop_checkGrepRe8() {
        assert!(emits_code(check_grep_re, "ls | grep foo*.jpg", 2062));
    }
    #[test]
    fn prop_checkGrepRe9() {
        assert!(!emits_code(check_grep_re, "grep '[0-9]*' file", 2062));
    }
    #[test]
    fn prop_checkGrepRe12() {
        assert!(!emits_code(check_grep_re, "grep -F 'Foo*' file", 2062));
    }
    #[test]
    fn prop_checkGrepRe13() {
        assert!(!emits_code(check_grep_re, "grep -- -foo bar*", 2062));
    }
    #[test]
    fn prop_checkGrepRe14() {
        assert!(!emits_code(check_grep_re, "grep -e -foo bar*", 2062));
    }

    // SC2194 — constant case word
    #[test]
    fn prop_case_const1() {
        assert!(emits_code(
            check_unmatchable_cases_constant,
            "case foo in bar) true; esac",
            2194
        ));
    }
    #[test]
    fn prop_case_const2() {
        assert!(!emits_code(
            check_unmatchable_cases_constant,
            "case $f in bar) true; esac",
            2194
        ));
    }

    // SC2207 — checkSplittingInArrays (command branch)
    #[test]
    fn prop_checkSplittingInArrays2() {
        assert!(emits(check_splitting_in_arrays, "a=( $(cmd) )"));
    }
    #[test]
    fn prop_checkSplittingInArrays4() {
        assert!(!emits(check_splitting_in_arrays, "a=( \"$(cmd)\" )"));
    }
    #[test]
    fn prop_splitarr_backtick() {
        assert!(emits(check_splitting_in_arrays, "a=( `cmd` )"));
    }
    #[test]
    fn prop_splitarr_var() {
        assert!(!emits(check_splitting_in_arrays, "a=( $var )"));
    }

    // SC2215 — checkFlagAsCommand
    #[test]
    fn prop_checkFlagAsCommand1() {
        assert!(emits(check_flag_as_command, "-e file"));
    }
    #[test]
    fn prop_checkFlagAsCommand2() {
        assert!(emits(check_flag_as_command, "foo\n  --bar=baz"));
    }
    #[test]
    fn prop_checkFlagAsCommand3() {
        assert!(!emits(check_flag_as_command, "'--myexec--' args"));
    }
    #[test]
    fn prop_checkFlagAsCommand4() {
        assert!(!emits(check_flag_as_command, "var=cmd --arg"));
    }

    // SC2283 — spaces around =
    #[test]
    fn prop_checkSecondArgIsComparison1() {
        assert!(emits_code(
            check_second_arg_is_comparison,
            "foo = $bar",
            2283
        ));
    }
    #[test]
    fn prop_checkSecondArgIsComparison2() {
        assert!(emits_code(
            check_second_arg_is_comparison,
            "$foo = $bar",
            2283
        ));
    }
    #[test]
    fn prop_checkSecondArgIsComparison4() {
        assert!(emits_code(
            check_second_arg_is_comparison,
            "'var' =$bar",
            2283
        ));
    }
    #[test]
    fn prop_checkSecondArgIsComparison6() {
        assert!(emits_code(
            check_second_arg_is_comparison,
            "$foo =$bar",
            2283
        ));
    }
    #[test]
    fn prop_sc2283_not_eqeq() {
        assert!(!emits_code(
            check_second_arg_is_comparison,
            "2f == $bar",
            2283
        ));
    }
    #[test]
    fn prop_sc2283_not_pluseq() {
        assert!(!emits_code(
            check_second_arg_is_comparison,
            "var += $(foo)",
            2283
        ));
    }
    #[test]
    fn prop_sc2283_not_border() {
        assert!(!emits_code(
            check_second_arg_is_comparison,
            "echo ======= Here =======",
            2283
        ));
    }

    // SC2288 — trailing symbol
    #[test]
    fn prop_checkCommandWithTrailingSymbol6() {
        assert!(emits_code(
            check_command_with_trailing_symbol,
            "foo, bar",
            2288
        ));
    }
    #[test]
    fn prop_sc2288_not_slash() {
        assert!(!emits_code(
            check_command_with_trailing_symbol,
            "/foo/ bar/baz",
            2288
        ));
    }
    #[test]
    fn prop_sc2288_not_dot() {
        assert!(!emits_code(
            check_command_with_trailing_symbol,
            ". foo.sh",
            2288
        ));
    }
    #[test]
    fn prop_sc2288_not_colon() {
        assert!(!emits_code(
            check_command_with_trailing_symbol,
            ": foo",
            2288
        ));
    }
    #[test]
    fn prop_sc2288_not_var() {
        assert!(!emits_code(
            check_command_with_trailing_symbol,
            "$foo/$bar",
            2288
        ));
    }
    // Fully-literal guard: parser-gap fallbacks with expansions/globs must not fire.
    #[test]
    fn prop_sc2288_not_condition() {
        assert!(!emits_code(
            check_command_with_trailing_symbol,
            "[[ 3 \\< 4 ]]",
            2288
        ));
    }
    #[test]
    fn prop_sc2288_not_badbrace() {
        assert!(!emits_code(
            check_command_with_trailing_symbol,
            "${{var}",
            2288
        ));
    }
    // Real oracle cases remain literal and still fire.
    #[test]
    fn prop_sc2288_dollar_dquote() {
        assert!(emits_code(
            check_command_with_trailing_symbol,
            "$\"(foo)\"",
            2288
        ));
    }
}
