//! Ported check batch w. See rust/PORTING.md.
//!
//! Faithful ports of the following `ShellCheck.Analytics` checks (commands /
//! loops / functions / path / misc), each with all its `prop_` tests as
//! `#[test]`s. Registration is gated by the conformance guardrail (never emit a
//! code with `extra > 0`; a code already owned by another batch is filtered out
//! of this batch's registration to avoid double-emission):
//!
//! - checkEchoWc                     SC2000
//! - checkPipedAssignment            SC2036
//! - checkArithmeticOpCommand        SC2099
//! - checkWrongArithmeticAssignment  SC2100  (variable_flow)
//! - checkPipePitfalls               SC2038 + SC2012 registered; SC2009/SC2011
//!                                   ported+tested but unregistered (out of this
//!                                   batch's scope); SC2010 (batch_n) / SC2126
//!                                   (batch_g) filtered out to avoid duplication.
//! - checkShebangParameters          SC2096 (tree)
//! - checkForInQuoted                SC2066/SC2041/SC2042/SC2043/SC2258
//! - checkFindExec                   SC2014/SC2067
//! - checkLoopKeywordScope           SC2104/SC2105/SC2106
//! - checkFunctionDeclarations       SC2111/SC2112/SC2113
//! - checkStderrPipe                 SC2118
//! - checkOverridingPath             SC2123
//! - checkTildeInPath                SC2147
//! - checkUnsupported                SC2127
//! - checkSuspiciousIFS              SC2141
//! - checkShouldUseGrepQ             SC2143
//! - checkCpLegacyR                  SC2336
//! - checkLoopVariableReassignment   SC2165/SC2167
//! - checkForLoopGlobVariables       SC2231
//! - checkAliasUsedInSameParsingUnit SC2262/SC2263 (tree)
//! - checkBlatantRecursion           SC2264
//! - checkAssignToSelf               SC2269
//! - checkCommandWithTrailingSymbol  SC2287 registered; SC2286/SC2289
//!                                   ported+tested but unregistered (out of
//!                                   scope); SC2288 (batch_n) filtered out.
//! - checkBatsTestDoesNotUseNegation SC2314/SC2315
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::cfg::{get_braced_reference, get_word_parts, is_variable_name, oversimplify};
use crate::interface::Shell;
use std::collections::HashMap;

pub fn register(c: &mut Checker) {
    c.node(check_echo_wc);
    c.node(check_piped_assignment);
    c.node(check_arithmetic_op_command);
    c.node(check_wrong_arithmetic_assignment);
    // checkPipePitfalls: register only SC2038 + SC2012. SC2010 is owned by
    // batch_n, SC2126 by batch_g; SC2009/SC2011 are out of this batch's scope.
    c.node(|p, t, out| {
        let mut tmp = Out::new();
        check_pipe_pitfalls(p, t, &mut tmp);
        for c in tmp {
            if c.comment.code == 2038 || c.comment.code == 2012 {
                out.push(c);
            }
        }
    });
    c.tree(check_shebang_parameters);
    c.node(check_for_in_quoted);
    c.node(check_find_exec);
    c.node(check_loop_keyword_scope);
    c.node(check_function_declarations);
    c.node(check_stderr_pipe);
    c.node(check_overriding_path);
    c.node(check_tilde_in_path);
    c.node(check_unsupported);
    c.node(check_suspicious_ifs);
    // checkShouldUseGrepQ (SC2143): register all branches (TC_Nullary and the
    // TC_Unary -n / -z branches). The shared parser now spans a TC_Unary node on
    // the operator alone (e.g. "-z"), matching the Haskell oracle, so the unary
    // branch anchors correctly and no longer produces span-mismatch extras.
    c.node(check_should_use_grep_q);
    c.node(check_cp_legacy_r);
    c.node(check_loop_variable_reassignment);
    c.node(check_for_loop_glob_variables);
    c.tree(check_alias_used_in_same_parsing_unit);
    c.node(check_blatant_recursion);
    c.node(check_assign_to_self);
    // checkCommandWithTrailingSymbol: register only SC2287. SC2288 is owned by
    // batch_n; SC2286/SC2289 are out of this batch's scope.
    c.node(|p, t, out| {
        let mut tmp = Out::new();
        check_command_with_trailing_symbol(p, t, &mut tmp);
        for c in tmp {
            if c.comment.code == 2287 {
                out.push(c);
            }
        }
    });
    c.node(check_bats_test_does_not_use_negation);
}

// ===========================================================================
// Local AST helpers (ports of ShellCheck.ASTLib helpers not exposed publicly).
// ===========================================================================

fn is_loop(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_WhileExpression { .. }
            | InnerToken::T_UntilExpression { .. }
            | InnerToken::T_ForIn { .. }
            | InnerToken::T_ForArithmetic { .. }
            | InnerToken::T_SelectIn { .. }
    )
}

fn is_function(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Function { .. })
}

/// `willSplit`.
fn will_split(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. }
        | T_DollarExpansion(_)
        | T_Backticked(_)
        | T_BraceExpansion(_)
        | T_Glob(_)
        | T_Extglob { .. } => true,
        T_DoubleQuoted(l) => l.iter().any(will_become_multiple_args),
        T_NormalWord(l) => l.iter().any(will_split),
        _ => false,
    }
}

/// `willConcatInAssignment`.
fn will_concat_in_assignment(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => is_array_expansion(t),
        T_DoubleQuoted(parts) | T_NormalWord(parts) => parts.iter().any(will_concat_in_assignment),
        _ => false,
    }
}

/// `willBecomeMultipleArgs`.
fn will_become_multiple_args(t: &Token) -> bool {
    use InnerToken::*;
    if will_concat_in_assignment(t) {
        return true;
    }
    fn f(t: &Token) -> bool {
        use InnerToken::*;
        match &*t.inner {
            T_Extglob { .. } | T_Glob(_) | T_BraceExpansion(_) => true,
            T_NormalWord(parts) => parts.iter().any(f),
            _ => false,
        }
    }
    f(t)
}

/// `mayBecomeMultipleArgs`.
fn may_become_multiple_args(t: &Token) -> bool {
    if will_become_multiple_args(t) {
        return true;
    }
    fn f(quoted: bool, t: &Token) -> bool {
        use InnerToken::*;
        match &*t.inner {
            T_DollarBraced { op, .. } => {
                let string = oversimplify(op).concat();
                !quoted || string.starts_with('!')
            }
            T_DoubleQuoted(parts) => parts.iter().any(|p| f(true, p)),
            T_NormalWord(parts) => parts.iter().any(|p| f(quoted, p)),
            _ => false,
        }
    }
    f(false, t)
}

/// `isGlob`.
fn is_glob(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_Extglob { .. } | T_Glob(_) => true,
        T_NormalWord(l) => {
            if l.iter().any(is_glob) {
                return true;
            }
            // foo[x${var}y] parses as foo,[,x,$var,y]: detect a half-open range
            // "[" followed later by a literal containing "]".
            let is_half_open = |t: &Token| matches!(&*t.inner, T_Literal(s) if s == "[");
            let is_closing = |t: &Token| matches!(&*t.inner, T_Literal(s) if s.contains(']'));
            let after: Vec<&Token> = l.iter().skip_while(|x| !is_half_open(x)).collect();
            after.iter().any(|x| is_closing(x))
        }
        _ => false,
    }
}

/// `getUnquotedLiteral`.
fn get_unquoted_literal(t: &Token) -> Option<String> {
    if let InnerToken::T_NormalWord(list) = &*t.inner {
        let mut out = String::new();
        for p in list {
            if let InnerToken::T_Literal(s) = &*p.inner {
                out.push_str(s);
            } else {
                return None;
            }
        }
        Some(out)
    } else {
        None
    }
}

/// `getTrailingUnquotedLiteral`.
fn get_trailing_unquoted_literal(t: &Token) -> Option<&Token> {
    if let InnerToken::T_NormalWord(list) = &*t.inner {
        let last = list.last()?;
        if matches!(&*last.inner, InnerToken::T_Literal(_)) {
            return Some(last);
        }
    }
    None
}

/// `getLeadingUnquotedString`.
fn get_leading_unquoted_string(t: &Token) -> Option<String> {
    if let InnerToken::T_NormalWord(list) = &*t.inner {
        if let Some(first) = list.first() {
            if let InnerToken::T_Literal(s) = &*first.inner {
                let mut out = s.clone();
                for p in &list[1..] {
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

/// `wouldHaveBeenGlob s = '*' `elem` s`.
fn would_have_been_glob(s: &str) -> bool {
    s.contains('*')
}

/// `getGlobOrLiteralString`.
fn get_glob_or_literal_string(t: &Token) -> Option<String> {
    astlib::get_literal_string_ext(t, &|inner| match inner {
        InnerToken::T_Glob(s) => Some(s.clone()),
        _ => None,
    })
}

/// `isLiteral`.
fn is_literal(t: &Token) -> bool {
    astlib::get_literal_string(t).is_some()
}

/// `isCommandSubstitution`.
fn is_command_substitution(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_DollarExpansion(_)
            | InnerToken::T_DollarBraceCommandExpansion { .. }
            | InnerToken::T_Backticked(_)
    )
}

/// `isQuoteableExpansion`.
fn is_quoteable_expansion(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_DollarBraced { .. }) || is_command_substitution(t)
}

/// `isUnqualifiedCommand token str` — exact command-name match (no path).
fn is_unqualified_command(t: &Token, name: &str) -> bool {
    get_command_name(t).as_deref() == Some(name)
}

/// `getAllFlags` (== `getFlagsUntil (== "--")`), on a T_SimpleCommand token.
fn get_all_flags(t: &Token) -> Vec<(Token, String)> {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } => words,
        _ => return vec![],
    };
    if words.is_empty() {
        return vec![];
    }
    let args = &words[1..];
    let token_and_text: Vec<(Token, String)> = args
        .iter()
        .map(|x| (x.clone(), oversimplify(x).concat()))
        .collect();
    let mut flag_args: Vec<(Token, String)> = vec![];
    let mut rest: Vec<(Token, String)> = vec![];
    let mut broken = false;
    for (x, txt) in token_and_text {
        if !broken && txt == "--" {
            broken = true;
        }
        if broken {
            rest.push((x, txt));
        } else {
            flag_args.push((x, txt));
        }
    }
    let mut out: Vec<(Token, String)> = vec![];
    for (x, txt) in flag_args {
        if let Some(arg) = txt.strip_prefix("--") {
            out.push((x, arg.split('=').next().unwrap_or("").to_string()));
        } else if let Some(a) = txt.strip_prefix('-') {
            for v in a.chars() {
                out.push((x.clone(), v.to_string()));
            }
        } else {
            out.push((x, String::new()));
        }
    }
    for (x, _) in rest {
        out.push((x, String::new()));
    }
    out
}

/// `getCommand`.
fn get_command_local(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command_local(cmd),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        InnerToken::T_Annotation { token, .. } => get_command_local(token),
        _ => None,
    }
}

/// The flag strings of a command (`map snd . getAllFlags`), given a command token.
fn command_flag_strings(cmd: Option<&Token>) -> Vec<String> {
    match cmd {
        Some(c) => get_all_flags(c).into_iter().map(|(_, s)| s).collect(),
        None => vec![],
    }
}

// ===========================================================================
// checkEchoWc — SC2000
// ===========================================================================

fn check_echo_wc(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Pipeline { commands, .. } = &*t.inner else {
        return;
    };
    if commands.len() != 2 {
        return;
    }
    let acmd = oversimplify(&commands[0]);
    let bcmd = oversimplify(&commands[1]);
    if acmd == ["echo", "${VAR}"] {
        if bcmd == ["wc", "-c"] || bcmd == ["wc", "-m"] {
            style(
                out,
                t.id(),
                2000,
                "See if you can use ${#variable} instead.",
            );
        }
    }
}

// ===========================================================================
// checkPipedAssignment — SC2036
// ===========================================================================

fn check_piped_assignment(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Pipeline { commands, .. } = &*t.inner else {
        return;
    };
    if commands.len() < 2 {
        return;
    }
    let InnerToken::T_Redirecting { cmd, .. } = &*commands[0].inner else {
        return;
    };
    if let InnerToken::T_SimpleCommand { assignments, words } = &*cmd.inner {
        if !assignments.is_empty() && words.is_empty() {
            warn(
                out,
                cmd.id(),
                2036,
                "If you wanted to assign the output of the pipeline, use a=$(b | c) .",
            );
        }
    }
}

// ===========================================================================
// checkArithmeticOpCommand — SC2099
// ===========================================================================

fn check_arithmetic_op_command(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return;
    };
    if assignments.len() != 1 || !matches!(&*assignments[0].inner, InnerToken::T_Assignment { .. })
    {
        return;
    }
    let Some(first_word) = words.first() else {
        return;
    };
    if let Some(op) = get_glob_or_literal_string(first_word) {
        if matches!(op.as_str(), "+" | "-" | "*" | "/") {
            warn(
                out,
                first_word.id(),
                2099,
                &format!("Use $((..)) for arithmetics, e.g. i=$((i {} 2))", op),
            );
        }
    }
}

// ===========================================================================
// checkWrongArithmeticAssignment — SC2100 (variable_flow)
// ===========================================================================

fn get_normal_string(t: &Token) -> Option<String> {
    if let InnerToken::T_NormalWord(words) = &*t.inner {
        let mut out = String::new();
        for w in words {
            match &*w.inner {
                InnerToken::T_Literal(s) | InnerToken::T_Glob(s) => out.push_str(s),
                _ => return None,
            }
        }
        Some(out)
    } else {
        None
    }
}

/// Match `^([_a-zA-Z][_a-zA-Z0-9]*)([+*-]).+$` -> (var, op).
fn match_wrong_arith(s: &str) -> Option<(String, char)> {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    if n == 0 || !(chars[0] == '_' || chars[0].is_ascii_alphabetic()) {
        return None;
    }
    let mut i = 1;
    while i < n && (chars[i] == '_' || chars[i].is_ascii_alphanumeric()) {
        i += 1;
    }
    if i >= n {
        return None;
    }
    let op = chars[i];
    if !matches!(op, '+' | '*' | '-') {
        return None;
    }
    // `.+$`: at least one more character after the operator.
    if i + 1 >= n {
        return None;
    }
    let var: String = chars[..i].iter().collect();
    Some((var, op))
}

fn check_wrong_arithmetic_assignment(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return;
    };
    if assignments.len() != 1 || !words.is_empty() {
        return;
    }
    let InnerToken::T_Assignment { value, .. } = &*assignments[0].inner else {
        return;
    };
    let Some(str) = get_normal_string(value) else {
        return;
    };
    let Some((var, op)) = match_wrong_arith(&str) else {
        return;
    };
    let references: std::collections::HashSet<&str> = params
        .variable_flow
        .iter()
        .filter_map(|sd| match sd {
            StackData::Assignment(_, _, name, _) => Some(name.as_str()),
            _ => None,
        })
        .collect();
    if references.contains(var.as_str()) {
        warn(
            out,
            value.id(),
            2100,
            &format!("Use $((..)) for arithmetics, e.g. i=$((i {} 2))", op),
        );
    }
}

// ===========================================================================
// checkPipePitfalls — full port (SC2038/SC2009/SC2126/SC2010/SC2011/SC2012)
// ===========================================================================

/// `indexOfSublists sub list` with "?" wildcard matching any element.
fn index_of_sublists(sub: &[&str], list: &[String]) -> Vec<usize> {
    fn matches_at(sub: &[&str], list: &[String]) -> bool {
        match (sub.first(), list.first()) {
            (Some(&"?"), Some(_)) => matches_at(&sub[1..], &list[1..]),
            (Some(x), Some(y)) if *x == y.as_str() => matches_at(&sub[1..], &list[1..]),
            (Some(_), Some(_)) => false,
            (Some(_), None) => false,
            (None, _) => true,
        }
    }
    let mut out = vec![];
    for n in 0..list.len() {
        if matches_at(sub, &list[n..]) {
            out.push(n);
        }
    }
    out
}

fn check_pipe_pitfalls(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Pipeline { commands, .. } = &*t.inner else {
        return;
    };
    let names: Vec<String> = commands
        .iter()
        .map(|c| oversimplify(c).into_iter().next().unwrap_or_default())
        .collect();

    let has_short_parameter = |args: &[String], ch: char| -> bool {
        args.iter().any(|x| x.starts_with('-') && x.contains(ch))
    };
    let has_parameter = |args: &[String], string: &str| -> bool {
        args.iter()
            .any(|x| x.trim_start_matches('-').starts_with(string))
    };

    // for ["find", "xargs"] -> SC2038
    for n in index_of_sublists(&["find", "xargs"], &names) {
        let find = &commands[n];
        let xargs = &commands[n + 1];
        let mut args = oversimplify(xargs);
        args.extend(oversimplify(find));
        let ok = has_short_parameter(&args, '0')
            || has_parameter(&args, "null")
            || has_parameter(&args, "print0")
            || has_parameter(&args, "printf");
        if !ok {
            warn(
                out,
                find.id(),
                2038,
                "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.",
            );
        }
    }

    // for ["ps", "grep"] -> SC2009
    for n in index_of_sublists(&["ps", "grep"], &names) {
        let ps = &commands[n];
        let ps_flags = command_flag_strings(get_command_local(ps));
        if !ps_flags
            .iter()
            .any(|f| matches!(f.as_str(), "p" | "pid" | "q" | "quick-pid"))
        {
            info(
                out,
                ps.id(),
                2009,
                "Consider using pgrep instead of grepping ps output.",
            );
        }
    }

    // for ["grep", "wc"] -> SC2126
    for n in index_of_sublists(&["grep", "wc"], &names) {
        let grep = &commands[n];
        let wc = &commands[n + 1];
        let flags_grep = command_flag_strings(get_command_local(grep));
        let flags_wc = command_flag_strings(get_command_local(wc));
        let grep_ok = flags_grep.iter().any(|f| {
            matches!(
                f.as_str(),
                "l" | "files-with-matches"
                    | "L"
                    | "files-without-matches"
                    | "o"
                    | "only-matching"
                    | "r"
                    | "R"
                    | "recursive"
                    | "A"
                    | "after-context"
                    | "B"
                    | "before-context"
            )
        });
        let wc_ok = flags_wc.iter().any(|f| {
            matches!(
                f.as_str(),
                "m" | "chars" | "w" | "words" | "c" | "bytes" | "L" | "max-line-length"
            )
        });
        if !(grep_ok || wc_ok || flags_wc.is_empty()) {
            style(
                out,
                grep.id(),
                2126,
                "Consider using 'grep -c' instead of 'grep|wc -l'.",
            );
        }
    }

    // didLs: ls|grep (SC2010) and ls|xargs (SC2011)
    let mut did_ls = false;
    for n in index_of_sublists(&["ls", "grep"], &names) {
        let x = &commands[n];
        warn(
            out,
            get_command_token_or_this(x).id(),
            2010,
            "Don't use ls | grep. Use a glob or a for loop with a condition to allow non-alphanumeric filenames.",
        );
        did_ls = true;
    }
    for n in index_of_sublists(&["ls", "xargs"], &names) {
        let x = &commands[n];
        warn(
            out,
            get_command_token_or_this(x).id(),
            2011,
            "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.",
        );
        did_ls = true;
    }

    // unless didLs: for ["ls", "?"] -> SC2012
    if !did_ls {
        for n in index_of_sublists(&["ls", "?"], &names) {
            let ls = &commands[n];
            if !has_short_parameter(&oversimplify(ls), 'N') {
                info(
                    out,
                    ls.id(),
                    2012,
                    "Use find instead of ls to better handle non-alphanumeric filenames.",
                );
            }
        }
    }
}

// ===========================================================================
// checkShebangParameters — SC2096 (tree)
// ===========================================================================

fn check_shebang_parameters(_params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Annotation { token, .. } => check_shebang_parameters(_params, token, out),
        InnerToken::T_Script { shebang, .. } => {
            if let InnerToken::T_Literal(sb) = &*shebang.inner {
                use std::sync::OnceLock;
                static RE: OnceLock<regex::Regex> = OnceLock::new();
                let re = RE.get_or_init(|| regex::Regex::new(r"env +(-S|--split-string)").unwrap());
                let is_multi_word = sb.split_whitespace().count() > 2 && !re.is_match(sb);
                if is_multi_word {
                    err(
                        out,
                        shebang.id(),
                        2096,
                        "On most OS, shebangs can only specify a single parameter.",
                    );
                }
            }
        }
        _ => {}
    }
}

// ===========================================================================
// checkForInQuoted — SC2066/SC2041/SC2042/SC2043/SC2258
// ===========================================================================

fn check_for_in_quoted(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_ForIn { items, .. } = &*t.inner else {
        return;
    };

    // Equation 1: [T_NormalWord [word@(T_DoubleQuoted id list)]]
    if items.len() == 1 {
        if let InnerToken::T_NormalWord(nw) = &*items[0].inner {
            if nw.len() == 1 {
                if let InnerToken::T_DoubleQuoted(list) = &*nw[0].inner {
                    let word = &nw[0];
                    let guard1 = (list.iter().any(will_split) && !may_become_multiple_args(word))
                        || astlib::get_literal_string(word)
                            .map(|s| would_have_been_glob(&s))
                            .unwrap_or(false);
                    if guard1 {
                        err(
                            out,
                            word.id(),
                            2066,
                            "Since you double quoted this, it will not word split, and the loop will only run once.",
                        );
                        return;
                    }
                }
            }
        }
    }

    // Equation 2: [T_NormalWord [T_SingleQuoted id _]]
    if items.len() == 1 {
        if let InnerToken::T_NormalWord(nw) = &*items[0].inner {
            if nw.len() == 1 {
                if let InnerToken::T_SingleQuoted(_) = &*nw[0].inner {
                    warn(
                        out,
                        nw[0].id(),
                        2041,
                        "This is a literal string. To run as a command, use $(..) instead of '..' . ",
                    );
                    return;
                }
            }
        }
    }

    // Equation 3: [single]
    if items.len() == 1 {
        let single = &items[0];
        if get_unquoted_literal(single)
            .map(|s| s.contains(','))
            .unwrap_or(false)
        {
            warn(
                out,
                single.id(),
                2042,
                "Use spaces, not commas, to separate loop elements.",
            );
            return;
        }
        if !(will_split(single) || may_become_multiple_args(single)) {
            warn(
                out,
                single.id(),
                2043,
                "This loop will only ever run once. Bad quoting or missing glob/expansion?",
            );
            return;
        }
        // Guards failed: fall through to Equation 4 over [single].
    }

    // Equation 4: multiple (or a single item that fell through) -> SC2258
    for arg in items {
        if let Some(suffix) = get_trailing_unquoted_literal(arg) {
            if let Some(string) = astlib::get_literal_string(suffix) {
                if string.ends_with(',') {
                    warn_with_fix(
                        out,
                        arg.id(),
                        2258,
                        "The trailing comma is part of the value, not a separator. Delete or quote it.",
                        fix_with(vec![replace_end(params, suffix.id(), 1, "")]),
                    );
                }
            }
        }
    }
}

// ===========================================================================
// checkFindExec — SC2014/SC2067
// ===========================================================================

fn check_find_exec(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
        return;
    };
    if words.is_empty() || !is_command(t, "find") {
        return;
    }

    fn should_warn(x: &Token) -> bool {
        matches!(
            &*x.inner,
            InnerToken::T_DollarExpansion(_)
                | InnerToken::T_Backticked(_)
                | InnerToken::T_Glob(_)
                | InnerToken::T_Extglob { .. }
        )
    }
    fn from_word(x: &Token) -> &[Token] {
        match &*x.inner {
            InnerToken::T_NormalWord(l) => l,
            _ => &[],
        }
    }

    // broken over words[1..]
    let r = &words[1..];
    let mut v = false;
    for w in r {
        if v {
            for part in from_word(w) {
                if should_warn(part) {
                    info(
                        out,
                        part.id(),
                        2014,
                        "This will expand once before find runs, not per file found.",
                    );
                }
            }
        }
        v = match astlib::get_literal_string(w).as_deref() {
            Some("-exec") | Some("-execdir") | Some("-ok") | Some("-okdir") => true,
            Some("+") | Some(";") => false,
            _ => v,
        };
    }
    if v {
        // last of t (== words, since assignments precede words but Haskell `t`
        // here is the words list `(h:r)`).
        let last = words.last().unwrap();
        err(
            out,
            last.id(),
            2067,
            "Missing ';' or + terminating -exec. You can't use |/||/&&, and ';' has to be a separate, quoted argument.",
        );
    }
}

// ===========================================================================
// checkLoopKeywordScope — SC2104/SC2105/SC2106
// ===========================================================================

/// `leadType`/`subshellType` for a token (returns the subshell scope string).
fn subshell_type(params: &Parameters, t: &Token) -> Option<String> {
    use InnerToken::*;
    let s = |x: &str| Some(x.to_string());
    match &*t.inner {
        T_DollarExpansion(_) => s("$(..) expansion"),
        T_Backticked(_) => s("`..` expansion"),
        T_Backgrounded(_) => s("backgrounding &"),
        T_Subshell(_) => s("(..) group"),
        T_BatsTest { .. } => s("@bats test"),
        T_CoProcBody(_) => s("coproc"),
        T_Redirecting { .. } => {
            if causes_subshell(params, t) {
                s("pipeline")
            } else {
                None
            }
        }
        _ => None,
    }
}

fn causes_subshell(params: &Parameters, t: &Token) -> bool {
    let Some(parent) = params.parent(t) else {
        return false;
    };
    let InnerToken::T_Pipeline { commands, .. } = &*parent.inner else {
        return false;
    };
    if commands.len() >= 2 {
        !params.has_lastpipe || commands.last().map(|x| x.id()) != Some(t.id())
    } else {
        false
    }
}

fn check_loop_keyword_scope(params: &Parameters, t: &Token, out: &mut Out) {
    let Some(name) = get_command_name(t) else {
        return;
    };
    if name != "continue" && name != "break" {
        return;
    }
    let full_path = get_path(params, t);
    // relevant = isLoop || isFunction || subshellType isJust
    let path: Vec<&Token> = full_path
        .iter()
        .filter(|x| is_loop(x) || is_function(x) || subshell_type(params, x).is_some())
        .collect();

    if path.iter().any(|x| is_loop(x)) {
        // map subshellType (filter (not . isFunction) path); if head is Just -> 2106
        let filtered: Vec<&&Token> = path.iter().filter(|x| !is_function(x)).collect();
        if let Some(first) = filtered.first() {
            if let Some(str) = subshell_type(params, first) {
                warn(
                    out,
                    t.id(),
                    2106,
                    &format!("This only exits the subshell caused by the {}.", str),
                );
            }
        }
    } else {
        match path.first() {
            Some(h) if is_function(h) => {
                err(
                    out,
                    t.id(),
                    2104,
                    &format!("In functions, use return instead of {}.", name),
                );
            }
            _ => {
                err(
                    out,
                    t.id(),
                    2105,
                    &format!("{} is only valid in loops.", name),
                );
            }
        }
    }
}

// ===========================================================================
// checkFunctionDeclarations — SC2111/SC2112/SC2113
// ===========================================================================

fn check_function_declarations(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Function {
        keyword, parens, ..
    } = &*t.inner
    else {
        return;
    };
    let has_keyword = *keyword;
    let has_parens = *parens;
    let id = t.id();
    match params.shell {
        Shell::Bash => {}
        Shell::Ksh => {
            if has_keyword && has_parens {
                err(
                    out,
                    id,
                    2111,
                    "ksh does not allow 'function' keyword and '()' at the same time.",
                );
            }
        }
        Shell::Dash | Shell::BusyboxSh | Shell::Sh => {
            if has_keyword && has_parens {
                warn(
                    out,
                    id,
                    2112,
                    "'function' keyword is non-standard. Delete it.",
                );
            }
            if has_keyword && !has_parens {
                warn(
                    out,
                    id,
                    2113,
                    "'function' keyword is non-standard. Use 'foo()' instead of 'function foo'.",
                );
            }
        }
    }
}

// ===========================================================================
// checkStderrPipe — SC2118
// ===========================================================================

fn check_stderr_pipe(params: &Parameters, t: &Token, out: &mut Out) {
    if params.shell != Shell::Ksh {
        return;
    }
    if let InnerToken::T_Pipe(s) = &*t.inner {
        if s == "|&" {
            err(out, t.id(), 2118, "Ksh does not support |&. Use 2>&1 |.");
        }
    }
}

// ===========================================================================
// checkOverridingPath — SC2123
// ===========================================================================

fn check_overriding_path(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return;
    };
    if !words.is_empty() {
        return;
    }
    for var in assignments {
        let InnerToken::T_Assignment {
            mode,
            var: name,
            indices,
            value,
        } = &*var.inner
        else {
            continue;
        };
        if *mode != AssignmentMode::Assign || name != "PATH" || !indices.is_empty() {
            continue;
        }
        let string = oversimplify(value).concat();
        if ["/bin", "/sbin"].iter().any(|s| string.contains(s)) {
            continue;
        }
        let notify = |out: &mut Out| {
            warn(
                out,
                var.id(),
                2123,
                "PATH is the shell search path. Use another name.",
            );
        };
        if string.contains('/') && !string.contains(':') {
            notify(out);
        }
        if is_literal(value) && !string.contains(':') && !string.contains('/') {
            notify(out);
        }
    }
}

// ===========================================================================
// checkTildeInPath — SC2147
// ===========================================================================

fn check_tilde_in_path(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, .. } = &*t.inner else {
        return;
    };
    for var in assignments {
        let InnerToken::T_Assignment {
            mode,
            var: name,
            indices,
            value,
        } = &*var.inner
        else {
            continue;
        };
        if *mode != AssignmentMode::Assign || name != "PATH" || !indices.is_empty() {
            continue;
        }
        let InnerToken::T_NormalWord(parts) = &*value.inner else {
            continue;
        };
        let is_quoted = |x: &Token| {
            matches!(
                &*x.inner,
                InnerToken::T_DoubleQuoted(_) | InnerToken::T_SingleQuoted(_)
            )
        };
        let has_tilde = |x: &Token| astlib::only_literal_string(x).contains('~');
        if parts.iter().any(|x| is_quoted(x) && has_tilde(x)) {
            warn(
                out,
                var.id(),
                2147,
                "Literal tilde in PATH works poorly across programs.",
            );
        }
    }
}

// ===========================================================================
// checkUnsupported — SC2127
// ===========================================================================

fn shell_lower(s: Shell) -> &'static str {
    match s {
        Shell::Ksh => "ksh",
        Shell::Sh => "sh",
        Shell::Bash => "bash",
        Shell::Dash => "dash",
        Shell::BusyboxSh => "busyboxsh",
    }
}

/// `shellSupport t` -> (name, supported shells).
fn shell_support(t: &Token) -> (&'static str, Vec<Shell>) {
    match &*t.inner {
        InnerToken::T_CaseExpression { cases, .. } => {
            let seps: Vec<CaseType> = cases.iter().map(|(a, _, _)| *a).collect();
            if seps.contains(&CaseType::CaseContinue) {
                ("cases with ;;&", vec![Shell::Bash])
            } else if seps.contains(&CaseType::CaseFallThrough) {
                ("cases with ;&", vec![Shell::Bash, Shell::Ksh])
            } else {
                ("", vec![])
            }
        }
        InnerToken::T_DollarBraceCommandExpansion { .. } => {
            ("${ ..; } command expansion", vec![Shell::Bash, Shell::Ksh])
        }
        _ => ("", vec![]),
    }
}

fn check_unsupported(params: &Parameters, t: &Token, out: &mut Out) {
    let (name, support) = shell_support(t);
    if support.is_empty() || support.contains(&params.shell) {
        return;
    }
    let shells: Vec<&str> = support.iter().map(|s| shell_lower(*s)).collect();
    err(
        out,
        t.id(),
        2127,
        &format!(
            "To use {}, specify #!/usr/bin/env {}",
            name,
            shells.join(" or ")
        ),
    );
}

// ===========================================================================
// checkSuspiciousIFS — SC2141
// ===========================================================================

/// `decodeEscapes` for `$'..'` contents (ANSI-C), matching ASTLib.
fn decode_escapes(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '\\' && i + 1 < chars.len() {
            let c = chars[i + 1];
            match c {
                'a' => {
                    out.push('\u{07}');
                    i += 2;
                }
                'b' => {
                    out.push('\u{08}');
                    i += 2;
                }
                'e' | 'E' => {
                    out.push('\u{1B}');
                    i += 2;
                }
                'f' => {
                    out.push('\u{0C}');
                    i += 2;
                }
                'n' => {
                    out.push('\n');
                    i += 2;
                }
                'r' => {
                    out.push('\r');
                    i += 2;
                }
                't' => {
                    out.push('\t');
                    i += 2;
                }
                'v' => {
                    out.push('\u{0B}');
                    i += 2;
                }
                '\\' => {
                    out.push('\\');
                    i += 2;
                }
                '\'' => {
                    out.push('\'');
                    i += 2;
                }
                '"' => {
                    out.push('"');
                    i += 2;
                }
                '?' => {
                    out.push('?');
                    i += 2;
                }
                'x' => {
                    let hex: String = chars[i + 2..].iter().take(2).collect();
                    match u32::from_str_radix(&hex, 16) {
                        Ok(n) if !hex.is_empty() => {
                            if let Some(ch) = char::from_u32(n) {
                                out.push(ch);
                            }
                            i += 2 + hex.len();
                        }
                        _ => {
                            out.push('\\');
                            out.push('x');
                            i += 2;
                        }
                    }
                }
                'u' | 'U' => {
                    let width = if c == 'u' { 4 } else { 8 };
                    let hex: String = chars[i + 2..].iter().take(width).collect();
                    match u32::from_str_radix(&hex, 16) {
                        Ok(n) if !hex.is_empty() => {
                            if let Some(ch) = char::from_u32(n) {
                                out.push(ch);
                            }
                            i += 2 + hex.len();
                        }
                        _ => {
                            out.push('\\');
                            out.push('x');
                            i += 2;
                        }
                    }
                }
                _ => {
                    let oct: String = chars[i + 1..].iter().take(3).collect();
                    match u32::from_str_radix(&oct, 8) {
                        Ok(n) => {
                            if let Some(ch) = char::from_u32(n % 256) {
                                out.push(ch);
                            }
                            i += 1 + oct.len();
                        }
                        _ => {
                            out.push('\\');
                            out.push(c);
                            i += 2;
                        }
                    }
                }
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

/// `getLiteralString` mirroring ASTLib (decodes `$'..'`).
fn decoded_literal_string(t: &Token) -> Option<String> {
    use InnerToken::*;
    match &*t.inner {
        T_Literal(s) | T_SingleQuoted(s) | T_ParamSubSpecialChar(s) => Some(s.clone()),
        T_DollarSingleQuoted(s) => Some(decode_escapes(s)),
        T_DoubleQuoted(l) | T_DollarDoubleQuoted(l) | T_NormalWord(l) | TA_Expansion(l) => {
            let mut out = String::new();
            for p in l {
                out.push_str(&decoded_literal_string(p)?);
            }
            Some(out)
        }
        _ => None,
    }
}

fn check_suspicious_ifs(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Assignment {
        var,
        indices,
        value,
        ..
    } = &*t.inner
    else {
        return;
    };
    if var != "IFS" || !indices.is_empty() {
        return;
    }
    let Some(v) = decoded_literal_string(value) else {
        return;
    };
    let has_dollar_single = params.shell == Shell::Bash || params.shell == Shell::Ksh;
    let n = if has_dollar_single {
        "$'\\n'"
    } else {
        "'<literal linefeed here>'"
    };
    let tab = if has_dollar_single {
        "$'\\t'"
    } else {
        "\"$(printf '\\t')\""
    };
    let suggest = |out: &mut Out, r: &str| {
        warn(
            out,
            value.id(),
            2141,
            &format!("This backslash is literal. Did you mean IFS={} ?", r),
        );
    };
    let suggest2 = |out: &mut Out, desc: &str| {
        warn(
            out,
            value.id(),
            2141,
            &format!(
                "This IFS value contains {}. For tabs/linefeeds/escapes, use $'..', literal, or printf.",
                desc
            ),
        );
    };
    match v.as_str() {
        "\\n" => suggest(out, n),
        "\\t" => suggest(out, tab),
        x if x.contains('\\') => suggest2(out, "a literal backslash"),
        x if x.contains('n') => suggest2(out, "the literal letter 'n'"),
        x if x.contains('t') => suggest2(out, "the literal letter 't'"),
        _ => {}
    }
}

// ===========================================================================
// checkShouldUseGrepQ — SC2143
// ===========================================================================

const GREP_NAMES: &[&str] = &[
    "grep", "egrep", "fgrep", "bz3grep", "bzgrep", "xzgrep", "zgrep", "zipgrep", "zstdgrep",
];

fn get_pipeline(t: &Token) -> Option<Vec<Token>> {
    match &*t.inner {
        InnerToken::T_NormalWord(l) if l.len() == 1 => get_pipeline(&l[0]),
        InnerToken::T_DoubleQuoted(l) if l.len() == 1 => get_pipeline(&l[0]),
        InnerToken::T_DollarExpansion(l) if l.len() == 1 => get_pipeline(&l[0]),
        InnerToken::T_Pipeline { commands, .. } => Some(commands.clone()),
        _ => None,
    }
}

fn get_final_grep(t: &Token) -> Option<String> {
    let cmds = get_pipeline(t)?;
    if cmds.is_empty() {
        return None;
    }
    let name = get_command_basename(cmds.last().unwrap())?;
    if GREP_NAMES.contains(&name.as_str()) {
        Some(name)
    } else {
        None
    }
}

fn check_should_use_grep_q(_params: &Parameters, t: &Token, out: &mut Out) {
    let (id, bool_, token) = match &*t.inner {
        InnerToken::TC_Nullary { token, .. } => (t.id(), true, token),
        InnerToken::TC_Unary { op, token, .. } if op == "-n" => (t.id(), true, token),
        InnerToken::TC_Unary { op, token, .. } if op == "-z" => (t.id(), false, token),
        _ => return,
    };
    if let Some(name) = get_final_grep(token) {
        let op = if bool_ { "-n" } else { "-z" };
        let flip = if bool_ { "" } else { "! " };
        style(
            out,
            id,
            2143,
            &format!(
                "Use {}{} -q instead of comparing output with [ {} .. ].",
                flip, name, op
            ),
        );
    }
}

// ===========================================================================
// checkCpLegacyR — SC2336
// ===========================================================================

fn check_cp_legacy_r(params: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(&*t.inner, InnerToken::T_SimpleCommand { .. }) || !is_unqualified_command(t, "cp")
    {
        return;
    }
    let flags = get_all_flags(t);
    if let Some((flag_token, _)) = flags.iter().find(|(_, s)| s == "r") {
        warn_with_fix(
            out,
            flag_token.id(),
            2336,
            "cp -r behavior is implementation-defined",
            fix_with(vec![replace_token(params, flag_token.id(), "-R")]),
        );
    }
}

// ===========================================================================
// checkLoopVariableReassignment — SC2165/SC2167
// ===========================================================================

fn loop_variable(t: &Token) -> Option<String> {
    match &*t.inner {
        InnerToken::T_ForIn { var, .. } => Some(var.clone()),
        InnerToken::T_ForArithmetic { init, .. } => {
            // TA_Sequence [TA_Assignment "=" (TA_Variable var _) _]
            if let InnerToken::TA_Sequence(seq) = &*init.inner {
                if seq.len() == 1 {
                    if let InnerToken::TA_Assignment { op, lhs, .. } = &*seq[0].inner {
                        if op == "=" {
                            if let InnerToken::TA_Variable { name, .. } = &*lhs.inner {
                                return Some(name.clone());
                            }
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn check_loop_variable_reassignment(params: &Parameters, token: &Token, out: &mut Out) {
    if !matches!(
        &*token.inner,
        InnerToken::T_ForIn { .. } | InnerToken::T_ForArithmetic { .. }
    ) {
        return;
    }
    let Some(str) = loop_variable(token) else {
        return;
    };
    if str == "_" {
        return;
    }
    let full = get_path(params, token);
    // NE.tail: ancestors
    let path = &full[1..];
    if let Some(next) = path
        .iter()
        .find(|x| loop_variable(x).as_deref() == Some(str.as_str()))
    {
        warn(
            out,
            token.id(),
            2165,
            "This nested loop overrides the index variable of its parent.",
        );
        warn(
            out,
            next.id(),
            2167,
            "This parent loop has its index variable overridden.",
        );
    }
}

// ===========================================================================
// checkForLoopGlobVariables — SC2231
// ===========================================================================

fn check_for_loop_glob_variables(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_ForIn { items, .. } = &*t.inner else {
        return;
    };
    for word in items {
        if let InnerToken::T_NormalWord(parts) = &*word.inner {
            if parts.iter().any(is_glob) {
                for p in parts.iter().filter(|x| is_quoteable_expansion(x)) {
                    info(
                        out,
                        p.id(),
                        2231,
                        "Quote expansions in this for loop glob to prevent wordsplitting, e.g. \"$dir\"/*.txt .",
                    );
                }
            }
        }
    }
}

// ===========================================================================
// checkAliasUsedInSameParsingUnit — SC2262/SC2263 (tree)
// ===========================================================================

fn get_command_sequences<'a>(t: &'a Token) -> Vec<&'a [Token]> {
    use InnerToken::*;
    match &*t.inner {
        T_Script { commands, .. } => vec![&commands[..]],
        T_BraceGroup(cmds) => vec![&cmds[..]],
        T_Subshell(cmds) => vec![&cmds[..]],
        T_WhileExpression { condition, body } => vec![&condition[..], &body[..]],
        T_UntilExpression { condition, body } => vec![&condition[..], &body[..]],
        T_ForIn { body, .. } => vec![&body[..]],
        T_ForArithmetic { body, .. } => vec![&body[..]],
        T_IfExpression { clauses, elses } => {
            let mut out: Vec<&[Token]> = vec![];
            for (a, b) in clauses {
                out.push(&a[..]);
                out.push(&b[..]);
            }
            out.push(&elses[..]);
            out
        }
        T_Annotation { token, .. } => get_command_sequences(token),
        T_DollarExpansion(cmds) => vec![&cmds[..]],
        T_DollarBraceCommandExpansion { list, .. } => vec![&list[..]],
        T_Backticked(cmds) => vec![&cmds[..]],
        _ => vec![],
    }
}

/// `groupByLink`: group consecutive elements where each adjacent pair links.
fn group_by_link<'a, F: Fn(&Token, &Token) -> bool>(
    f: F,
    list: &[&'a Token],
) -> Vec<Vec<&'a Token>> {
    let mut out: Vec<Vec<&'a Token>> = vec![];
    let mut current: Vec<&'a Token> = vec![];
    for &item in list {
        if let Some(&prev) = current.last() {
            if f(prev, item) {
                current.push(item);
            } else {
                out.push(std::mem::take(&mut current));
                current.push(item);
            }
        } else {
            current.push(item);
        }
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}

fn is_annotation_ignoring_code(code: i64, t: &Token) -> bool {
    if let InnerToken::T_Annotation { annotations, .. } = &*t.inner {
        annotations.iter().any(|a| match a {
            Annotation::DisableComment(from, to) => code >= *from && code < *to,
            _ => false,
        })
    } else {
        false
    }
}

fn should_ignore_code(params: &Parameters, code: i64, t: &Token) -> bool {
    get_path(params, t)
        .iter()
        .any(|p| is_annotation_ignoring_code(code, p))
}

fn is_sourced(params: &Parameters, t: &Token) -> bool {
    get_path(params, t)
        .iter()
        .any(|p| matches!(&*p.inner, InnerToken::T_SourceCommand { .. }))
}

fn check_alias_used_in_same_parsing_unit(params: &Parameters, root: &Token, out: &mut Out) {
    let commands: Vec<&Token> = get_command_sequences(root)
        .into_iter()
        .flat_map(|s| s.iter())
        .collect();

    let line_span = |id: Id| -> Option<(i64, i64)> {
        let (start, end) = params.token_positions.get(&id)?;
        Some((start.line, end.line))
    };
    let follows_on_line = |a: &Token, b: &Token| -> bool {
        (|| {
            let (_, end) = line_span(a.id())?;
            let (start, _) = line_span(b.id())?;
            Some(end == start)
        })()
        .unwrap_or(false)
    };

    let units = group_by_link(follows_on_line, &commands);

    for unit in units {
        // doAnalysis findCommands over each token in the unit, sharing state.
        let mut aliases: HashMap<String, Token> = HashMap::new();
        for tok in unit {
            find_alias_commands(params, tok, &mut aliases, out);
        }
    }
}

fn find_alias_commands(
    params: &Parameters,
    t: &Token,
    aliases: &mut HashMap<String, Token>,
    out: &mut Out,
) {
    // preorder: run on t, then recurse into children.
    process_alias_node(params, t, aliases, out);
    for c in t.children() {
        find_alias_commands(params, c, aliases, out);
    }
}

fn process_alias_node(
    params: &Parameters,
    t: &Token,
    aliases: &mut HashMap<String, Token>,
    out: &mut Out,
) {
    let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
        return;
    };
    let Some((cmd, args)) = words.split_first() else {
        return;
    };
    match get_unquoted_literal(cmd).as_deref() {
        Some("alias") => {
            for arg in args {
                add_alias(arg, aliases);
            }
        }
        Some(name) if !name.contains('/') => {
            if let Some(alias) = aliases.get(name) {
                if !(is_sourced(params, t) || should_ignore_code(params, 2262, alias)) {
                    warn(
                        out,
                        alias.id(),
                        2262,
                        "This alias can't be defined and used in the same parsing unit. Use a function instead.",
                    );
                    info(
                        out,
                        t.id(),
                        2263,
                        "Since they're in the same parsing unit, this command will not refer to the previously mentioned alias.",
                    );
                }
            }
        }
        _ => {}
    }
}

fn add_alias(arg: &Token, aliases: &mut HashMap<String, Token>) {
    let full = get_literal_string_def(arg, "-");
    let (name, value) = match full.find('=') {
        Some(i) => (&full[..i], &full[i..]),
        None => (full.as_str(), ""),
    };
    if is_variable_name(name) && !value.is_empty() {
        // insertWith (\new old -> old): keep the first inserted.
        aliases
            .entry(name.to_string())
            .or_insert_with(|| arg.clone());
    }
}

// ===========================================================================
// checkBlatantRecursion — SC2264
// ===========================================================================

/// `getCommandNameAndToken True` (direct): the first word literal.
fn direct_command_name_and_token(cmd: &Token) -> (Option<String>, &Token) {
    if let Some(c) = get_command_local(cmd) {
        if let InnerToken::T_SimpleCommand { words, .. } = &*c.inner {
            if let Some(w) = words.first() {
                if let Some(s) = astlib::get_literal_string(w) {
                    return (Some(s), w);
                }
            }
        }
    }
    (None, cmd)
}

fn check_blatant_recursion(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Function { name, body, .. } = &*t.inner else {
        return;
    };
    let seqs = get_command_sequences(body);
    let first_seq = match seqs.as_slice() {
        [seq] => *seq,
        _ => return,
    };
    let Some(first) = first_seq.first() else {
        return;
    };
    recursion_check_list(params, name, first, out);
}

fn recursion_check_list(params: &Parameters, name: &str, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Backgrounded(inner) => recursion_check_list(params, name, inner, out),
        InnerToken::T_AndIf { lhs, .. } => recursion_check_list(params, name, lhs, out),
        InnerToken::T_OrIf { lhs, .. } => recursion_check_list(params, name, lhs, out),
        InnerToken::T_Pipeline { commands, .. } => {
            for cmd in commands {
                recursion_check_command(params, name, cmd, out);
            }
        }
        _ => {}
    }
}

fn recursion_check_command(params: &Parameters, name: &str, cmd: &Token, out: &mut Out) {
    let (invoked, tok) = direct_command_name_and_token(cmd);
    if let Some(invoked) = invoked {
        if name == invoked {
            err_with_fix(
                out,
                tok.id(),
                2264,
                "This function unconditionally re-invokes itself. Missing 'command'?",
                fix_with(vec![replace_start(params, tok.id(), 0, "command ")]),
            );
        }
    }
}

// ===========================================================================
// checkAssignToSelf — SC2269
// ===========================================================================

fn check_assign_to_self(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return;
    };
    if !words.is_empty() {
        return;
    }
    for var in assignments {
        let InnerToken::T_Assignment {
            mode,
            var: name,
            indices,
            value,
        } = &*var.inner
        else {
            continue;
        };
        if *mode != AssignmentMode::Assign || !indices.is_empty() {
            continue;
        }
        let parts = get_word_parts(value);
        if parts.len() == 1 {
            if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
                if astlib::get_literal_string(op).as_deref() == Some(name.as_str()) {
                    info(
                        out,
                        var.id(),
                        2269,
                        "This variable is assigned to itself, so the assignment does nothing.",
                    );
                }
            }
        }
    }
}

// ===========================================================================
// checkCommandWithTrailingSymbol — SC2286/SC2287/SC2288/SC2289 (full)
// ===========================================================================

fn trailing_symbol_format(x: char) -> String {
    match x {
        ' ' => "space".to_string(),
        '\'' => "apostrophe".to_string(),
        '"' => "doublequote".to_string(),
        _ => format!("'{}'", x),
    }
}

fn check_command_with_trailing_symbol(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
        return;
    };
    let Some(cmd) = words.first() else {
        return;
    };
    let str = get_literal_string_def(cmd, "x");
    let last = str.chars().last().unwrap_or('x');
    match str.as_str() {
        "." | ":" | " " | "//" => {}
        "" => err(
            out,
            cmd.id(),
            2286,
            "This empty string is interpreted as a command name. Double check syntax (or use 'true' as a no-op).",
        ),
        _ if last == '/' => err(
            out,
            cmd.id(),
            2287,
            "This is interpreted as a command name ending with '/'. Double check syntax.",
        ),
        _ if "\\.,([{<>}])#\"'% ".contains(last) => warn(
            out,
            cmd.id(),
            2288,
            &format!(
                "This is interpreted as a command name ending with {}. Double check syntax.",
                trailing_symbol_format(last)
            ),
        ),
        _ if str.contains('\t') => err(
            out,
            cmd.id(),
            2289,
            "This is interpreted as a command name containing a tab. Double check syntax.",
        ),
        _ if str.contains('\n') => err(
            out,
            cmd.id(),
            2289,
            "This is interpreted as a command name containing a linefeed. Double check syntax.",
        ),
        _ => {}
    }
}

// ===========================================================================
// checkBatsTestDoesNotUseNegation — SC2314/SC2315
// ===========================================================================

fn check_bats_test_does_not_use_negation(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_BatsTest { body, .. } = &*t.inner else {
        return;
    };
    let InnerToken::T_BraceGroup(commands) = &*body.inner else {
        return;
    };
    let is_last = |x: &Token| commands.last().map(|c| c == x).unwrap_or(false);
    for cmd in commands {
        if let InnerToken::T_Banged(inner) = &*cmd.inner {
            // T_Banged (T_Pipeline _ _ [T_Redirecting _ _ (T_Condition ..)])
            let is_condition = matches!(&*inner.inner, InnerToken::T_Pipeline { commands, .. }
                if commands.len() == 1
                    && matches!(&*commands[0].inner, InnerToken::T_Redirecting { cmd, .. }
                        if matches!(&*cmd.inner, InnerToken::T_Condition { .. })));
            if is_condition {
                if is_last(cmd) {
                    style(
                        out,
                        cmd.id(),
                        2315,
                        "In Bats, ! will not fail the test if it is not the last command anymore. Fold the `!` into the conditional!",
                    );
                } else {
                    err(
                        out,
                        cmd.id(),
                        2315,
                        "In Bats, ! does not cause a test failure. Fold the `!` into the conditional!",
                    );
                }
            } else {
                if is_last(cmd) {
                    style_with_fix(
                        out,
                        cmd.id(),
                        2314,
                        "In Bats, ! will not fail the test if it is not the last command anymore. Use `run ! ` (on Bats >= 1.5.0) instead.",
                        fix_with(vec![replace_start(params, cmd.id(), 0, "run ")]),
                    );
                } else {
                    err_with_fix(
                        out,
                        cmd.id(),
                        2314,
                        "In Bats, ! does not cause a test failure. Use 'run ! ' (on Bats >= 1.5.0) instead.",
                        fix_with(vec![replace_start(params, cmd.id(), 0, "run ")]),
                    );
                }
            }
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[allow(non_snake_case)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }

    fn collect(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Out {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out
    }
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        !collect(f, s).is_empty()
    }
    fn emits_code(f: fn(&Parameters, &Token, &mut Out), s: &str, code: i64) -> bool {
        collect(f, s).iter().any(|c| c.comment.code == code)
    }
    fn codes(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Vec<i64> {
        let mut v: Vec<i64> = collect(f, s).iter().map(|c| c.comment.code).collect();
        v.sort();
        v.dedup();
        v
    }
    fn tree_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        f(&params, &params.root, &mut out);
        !out.is_empty()
    }

    // ---- checkEchoWc ----
    #[test]
    fn prop_checkEchoWc3() {
        assert!(emits(check_echo_wc, "n=$(echo $foo | wc -c)"));
    }

    // ---- checkPipedAssignment ----
    #[test]
    fn prop_checkPipedAssignment1() {
        assert!(emits(check_piped_assignment, "A=ls | grep foo"));
    }
    #[test]
    fn prop_checkPipedAssignment2() {
        assert!(!emits(check_piped_assignment, "A=foo cmd | grep foo"));
    }
    #[test]
    fn prop_checkPipedAssignment3() {
        assert!(!emits(check_piped_assignment, "A=foo"));
    }

    // ---- checkArithmeticOpCommand ----
    #[test]
    fn prop_checkArithmeticOpCommand1() {
        assert!(emits(check_arithmetic_op_command, "i=i + 1"));
    }
    #[test]
    fn prop_checkArithmeticOpCommand2() {
        assert!(emits(check_arithmetic_op_command, "foo=bar * 2"));
    }
    #[test]
    fn prop_checkArithmeticOpCommand3() {
        assert!(!emits(check_arithmetic_op_command, "foo + opts"));
    }

    // ---- checkWrongArithmeticAssignment ----
    #[test]
    fn prop_checkWrongArit() {
        assert!(emits(check_wrong_arithmetic_assignment, "i=i+1"));
    }
    #[test]
    fn prop_checkWrongArit2() {
        assert!(emits(check_wrong_arithmetic_assignment, "n=2; i=n*2"));
    }

    // ---- checkPipePitfalls ----
    #[test]
    fn prop_checkPipePitfalls3() {
        assert!(emits(check_pipe_pitfalls, "ls | grep -v mp3"));
    }
    #[test]
    fn prop_checkPipePitfalls4() {
        assert!(!emits(check_pipe_pitfalls, "find . -print0 | xargs -0 foo"));
    }
    #[test]
    fn prop_checkPipePitfalls5() {
        assert!(!emits(check_pipe_pitfalls, "ls -N | foo"));
    }
    #[test]
    fn prop_checkPipePitfalls6() {
        assert!(emits(check_pipe_pitfalls, "find . | xargs foo"));
    }
    #[test]
    fn prop_checkPipePitfalls7() {
        assert!(!emits(
            check_pipe_pitfalls,
            "find . -printf '%s\\n' | xargs foo"
        ));
    }
    #[test]
    fn prop_checkPipePitfalls8() {
        assert!(emits(check_pipe_pitfalls, "foo | grep bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls9() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls10() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc"));
    }
    #[test]
    fn prop_checkPipePitfalls11() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep bar | wc"));
    }
    #[test]
    fn prop_checkPipePitfalls12() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc -c"));
    }
    #[test]
    fn prop_checkPipePitfalls13() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep bar | wc -c"));
    }
    #[test]
    fn prop_checkPipePitfalls14() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc -cmwL"));
    }
    #[test]
    fn prop_checkPipePitfalls15() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep bar | wc -cmwL"));
    }
    #[test]
    fn prop_checkPipePitfalls16() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -r bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls17() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -l bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls18() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -L bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls19() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -A2 bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls20() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -B999 bar | wc -l"));
    }
    #[test]
    fn prop_checkPipePitfalls21() {
        assert!(!emits(
            check_pipe_pitfalls,
            "foo | grep --after-context 999 bar | wc -l"
        ));
    }
    #[test]
    fn prop_checkPipePitfalls22() {
        assert!(!emits(
            check_pipe_pitfalls,
            "foo | grep -B 1 --after-context 999 bar | wc -l"
        ));
    }
    #[test]
    fn prop_checkPipePitfalls23() {
        assert!(!emits(
            check_pipe_pitfalls,
            "ps -o pid,args -p $(pgrep java) | grep -F net.shellcheck.Test"
        ));
    }

    // ---- checkShebangParameters ----
    #[test]
    fn prop_checkShebangParameters1() {
        assert!(tree_emits(
            check_shebang_parameters,
            "#!/usr/bin/env bash -x\necho cow"
        ));
    }
    #[test]
    fn prop_checkShebangParameters2() {
        assert!(!tree_emits(check_shebang_parameters, "#! /bin/sh  -l "));
    }
    #[test]
    fn prop_checkShebangParameters3() {
        assert!(!tree_emits(
            check_shebang_parameters,
            "#!/usr/bin/env -S bash -x\necho cow"
        ));
    }
    #[test]
    fn prop_checkShebangParameters4() {
        assert!(!tree_emits(
            check_shebang_parameters,
            "#!/usr/bin/env --split-string bash -x\necho cow"
        ));
    }

    // ---- checkForInQuoted ----
    #[test]
    fn prop_checkForInQuoted() {
        assert!(emits(
            check_for_in_quoted,
            "for f in \"$(ls)\"; do echo foo; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted2() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in \"$@\"; do echo foo; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted2a() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in *.mp3; do echo foo; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted2b() {
        assert!(emits(
            check_for_in_quoted,
            "for f in \"*.mp3\"; do echo foo; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted3() {
        assert!(emits(
            check_for_in_quoted,
            "for f in 'find /'; do true; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted4() {
        assert!(emits(check_for_in_quoted, "for f in 1,2,3; do true; done"));
    }
    #[test]
    fn prop_checkForInQuoted4a() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in foo{1,2,3}; do true; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted5() {
        assert!(emits(check_for_in_quoted, "for f in ls; do true; done"));
    }
    #[test]
    fn prop_checkForInQuoted6() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in \"${!arr}\"; do true; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted7() {
        assert!(emits(
            check_for_in_quoted,
            "for f in ls, grep, mv; do true; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted8() {
        assert!(emits(
            check_for_in_quoted,
            "for f in 'ls', 'grep', 'mv'; do true; done"
        ));
    }
    #[test]
    fn prop_checkForInQuoted9() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in 'ls,' 'grep,' 'mv'; do true; done"
        ));
    }

    // ---- checkFindExec ----
    #[test]
    fn prop_checkFindExec1() {
        assert!(emits(check_find_exec, "find / -name '*.php' -exec rm {};"));
    }
    #[test]
    fn prop_checkFindExec2() {
        assert!(emits(check_find_exec, "find / -exec touch {} && ls {} \\;"));
    }
    #[test]
    fn prop_checkFindExec3() {
        assert!(emits(
            check_find_exec,
            "find / -execdir cat {} | grep lol +"
        ));
    }
    #[test]
    fn prop_checkFindExec4() {
        assert!(!emits(
            check_find_exec,
            "find / -name '*.php' -exec foo {} +"
        ));
    }
    #[test]
    fn prop_checkFindExec5() {
        assert!(!emits(
            check_find_exec,
            "find / -execdir bash -c 'a && b' \\;"
        ));
    }
    #[test]
    fn prop_checkFindExec6() {
        assert!(emits(
            check_find_exec,
            "find / -type d -execdir rm *.jpg \\;"
        ));
    }

    // ---- checkLoopKeywordScope ----
    #[test]
    fn prop_lks_break_toplevel() {
        assert!(emits_code(check_loop_keyword_scope, "break", 2105));
    }
    #[test]
    fn prop_lks_continue_toplevel() {
        assert!(emits_code(check_loop_keyword_scope, "continue", 2105));
    }
    #[test]
    fn prop_lks_in_function() {
        assert!(emits_code(
            check_loop_keyword_scope,
            "foo() { break; }",
            2104
        ));
    }
    #[test]
    fn prop_lks_in_loop() {
        assert!(!emits(
            check_loop_keyword_scope,
            "while true; do break; done"
        ));
    }
    #[test]
    fn prop_lks_subshell_in_loop() {
        assert!(emits_code(
            check_loop_keyword_scope,
            "while true; do ( break ); done",
            2106
        ));
    }

    // ---- checkFunctionDeclarations ----
    #[test]
    fn prop_checkFunctionDeclarations1() {
        assert!(emits(
            check_function_declarations,
            "#!/bin/ksh\nfunction foo() { command foo --lol \"$@\"; }"
        ));
    }
    #[test]
    fn prop_checkFunctionDeclarations2() {
        assert!(emits(
            check_function_declarations,
            "#!/bin/dash\nfunction foo { lol; }"
        ));
    }
    #[test]
    fn prop_checkFunctionDeclarations3() {
        assert!(!emits(check_function_declarations, "foo() { echo bar; }"));
    }

    // ---- checkStderrPipe ----
    #[test]
    fn prop_checkStderrPipe1() {
        assert!(emits(check_stderr_pipe, "#!/bin/ksh\nfoo |& bar"));
    }
    #[test]
    fn prop_checkStderrPipe2() {
        assert!(!emits(check_stderr_pipe, "#!/bin/bash\nfoo |& bar"));
    }

    // ---- checkOverridingPath ----
    #[test]
    fn prop_checkOverridingPath1() {
        assert!(emits(check_overriding_path, "PATH=\"$var/$foo\""));
    }
    #[test]
    fn prop_checkOverridingPath2() {
        assert!(emits(check_overriding_path, "PATH=\"mydir\""));
    }
    #[test]
    fn prop_checkOverridingPath3() {
        assert!(emits(check_overriding_path, "PATH=/cow/foo"));
    }
    #[test]
    fn prop_checkOverridingPath4() {
        assert!(!emits(check_overriding_path, "PATH=/cow/foo/bin"));
    }
    #[test]
    fn prop_checkOverridingPath5() {
        assert!(!emits(check_overriding_path, "PATH='/bin:/sbin'"));
    }
    #[test]
    fn prop_checkOverridingPath6() {
        assert!(!emits(check_overriding_path, "PATH=\"$var/$foo\" cmd"));
    }
    #[test]
    fn prop_checkOverridingPath7() {
        assert!(!emits(check_overriding_path, "PATH=$OLDPATH"));
    }
    #[test]
    fn prop_checkOverridingPath8() {
        assert!(!emits(check_overriding_path, "PATH=$PATH:/stuff"));
    }

    // ---- checkTildeInPath ----
    #[test]
    fn prop_checkTildeInPath1() {
        assert!(emits(check_tilde_in_path, "PATH=\"$PATH:~/bin\""));
    }
    #[test]
    fn prop_checkTildeInPath2() {
        assert!(emits(check_tilde_in_path, "PATH='~foo/bin'"));
    }
    #[test]
    fn prop_checkTildeInPath3() {
        assert!(!emits(check_tilde_in_path, "PATH=~/bin"));
    }

    // ---- checkUnsupported ----
    #[test]
    fn prop_checkUnsupported3() {
        assert!(emits(
            check_unsupported,
            "#!/bin/sh\ncase foo in bar) baz ;& esac"
        ));
    }
    #[test]
    fn prop_checkUnsupported4() {
        assert!(emits(
            check_unsupported,
            "#!/bin/ksh\ncase foo in bar) baz ;;& esac"
        ));
    }
    #[test]
    fn prop_checkUnsupported5() {
        assert!(!emits(check_unsupported, "#!/bin/bash\necho \"${ ls; }\""));
    }
    #[test]
    fn prop_checkUnsupported6() {
        assert!(emits(check_unsupported, "#!/bin/ash\necho \"${ ls; }\""));
    }

    // ---- checkSuspiciousIFS ----
    #[test]
    fn prop_checkSuspiciousIFS1() {
        assert!(emits(check_suspicious_ifs, "IFS=\"\\n\""));
    }
    #[test]
    fn prop_checkSuspiciousIFS2() {
        assert!(!emits(check_suspicious_ifs, "IFS=$'\\t'"));
    }
    #[test]
    fn prop_checkSuspiciousIFS3() {
        assert!(emits(check_suspicious_ifs, "IFS=' \\t\\n'"));
    }

    // ---- checkShouldUseGrepQ ----
    #[test]
    fn prop_checkGrepQ1() {
        assert!(emits(check_should_use_grep_q, "[[ $(foo | grep bar) ]]"));
    }
    #[test]
    fn prop_checkGrepQ2() {
        assert!(emits(check_should_use_grep_q, "[ -z $(fgrep lol) ]"));
    }
    #[test]
    fn prop_checkGrepQ3() {
        assert!(emits(
            check_should_use_grep_q,
            "[ -n \"$(foo | zgrep lol)\" ]"
        ));
    }
    #[test]
    fn prop_checkGrepQ4() {
        assert!(!emits(check_should_use_grep_q, "[ -z $(grep bar | cmd) ]"));
    }
    #[test]
    fn prop_checkGrepQ5() {
        assert!(!emits(check_should_use_grep_q, "rm $(ls | grep file)"));
    }
    #[test]
    fn prop_checkGrepQ6() {
        assert!(!emits(check_should_use_grep_q, "[[ -n $(pgrep foo) ]]"));
    }

    // ---- checkCpLegacyR ----
    #[test]
    fn prop_checkCpLegacyR1() {
        assert!(emits(check_cp_legacy_r, "cp -r foo bar"));
    }
    #[test]
    fn prop_checkCpLegacyR2() {
        assert!(!emits(check_cp_legacy_r, "cp -R foo bar"));
    }

    // ---- checkLoopVariableReassignment ----
    #[test]
    fn prop_checkLoopVariableReassignment1() {
        assert!(emits(
            check_loop_variable_reassignment,
            "for i in *; do for i in *.bar; do true; done; done"
        ));
    }
    #[test]
    fn prop_checkLoopVariableReassignment2() {
        assert!(emits(
            check_loop_variable_reassignment,
            "for i in *; do for((i=0; i<3; i++)); do true; done; done"
        ));
    }
    #[test]
    fn prop_checkLoopVariableReassignment3() {
        assert!(!emits(
            check_loop_variable_reassignment,
            "for i in *; do for j in *.bar; do true; done; done"
        ));
    }
    #[test]
    fn prop_checkLoopVariableReassignment4() {
        assert!(!emits(
            check_loop_variable_reassignment,
            "for _ in *; do for _ in *.bar; do true; done; done"
        ));
    }

    // ---- checkForLoopGlobVariables ----
    #[test]
    fn prop_checkForLoopGlobVariables1() {
        assert!(emits(
            check_for_loop_glob_variables,
            "for i in $var/*.txt; do true; done"
        ));
    }
    #[test]
    fn prop_checkForLoopGlobVariables2() {
        assert!(!emits(
            check_for_loop_glob_variables,
            "for i in \"$var\"/*.txt; do true; done"
        ));
    }
    #[test]
    fn prop_checkForLoopGlobVariables3() {
        assert!(!emits(
            check_for_loop_glob_variables,
            "for i in $var; do true; done"
        ));
    }

    // ---- checkAliasUsedInSameParsingUnit ----
    #[test]
    fn prop_checkAliasUsedInSameParsingUnit1() {
        assert!(tree_emits(
            check_alias_used_in_same_parsing_unit,
            "alias x=y; x"
        ));
    }
    #[test]
    fn prop_checkAliasUsedInSameParsingUnit2() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            "alias x=y\nx"
        ));
    }
    #[test]
    fn prop_checkAliasUsedInSameParsingUnit3() {
        assert!(tree_emits(
            check_alias_used_in_same_parsing_unit,
            "{ alias x=y\nx\n}"
        ));
    }
    #[test]
    fn prop_checkAliasUsedInSameParsingUnit4() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            "alias x=y; 'x';"
        ));
    }
    #[test]
    fn prop_checkAliasUsedInSameParsingUnit5() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            ":\n{\n#shellcheck disable=SC2262\nalias x=y\nx\n}"
        ));
    }
    #[test]
    fn prop_checkAliasUsedInSameParsingUnit6() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            ":\n{\n#shellcheck disable=SC2262\nalias x=y\nalias x=z\nx\n}"
        ));
    }

    // ---- checkBlatantRecursion ----
    #[test]
    fn prop_checkBlatantRecursion1() {
        assert!(emits(check_blatant_recursion, ":(){ :|:& };:"));
    }
    #[test]
    fn prop_checkBlatantRecursion2() {
        assert!(emits(check_blatant_recursion, "f() { f; }"));
    }
    #[test]
    fn prop_checkBlatantRecursion3() {
        assert!(!emits(check_blatant_recursion, "f() { command f; }"));
    }
    #[test]
    fn prop_checkBlatantRecursion4() {
        assert!(emits(
            check_blatant_recursion,
            "cd() { cd \"$lol/$1\" || exit; }"
        ));
    }
    #[test]
    fn prop_checkBlatantRecursion5() {
        assert!(!emits(
            check_blatant_recursion,
            "cd() { [ -z \"$1\" ] || cd \"$1\"; }"
        ));
    }
    #[test]
    fn prop_checkBlatantRecursion6() {
        assert!(!emits(
            check_blatant_recursion,
            "cd() { something; cd $1; }"
        ));
    }
    #[test]
    fn prop_checkBlatantRecursion7() {
        assert!(!emits(check_blatant_recursion, "cd() { builtin cd $1; }"));
    }

    // ---- checkAssignToSelf ----
    #[test]
    fn prop_checkAssignToSelf1() {
        assert!(emits(check_assign_to_self, "x=$x"));
    }
    #[test]
    fn prop_checkAssignToSelf2() {
        assert!(emits(check_assign_to_self, "x=${x}"));
    }
    #[test]
    fn prop_checkAssignToSelf3() {
        assert!(emits(check_assign_to_self, "x=\"$x\""));
    }
    #[test]
    fn prop_checkAssignToSelf4() {
        assert!(!emits(check_assign_to_self, "x=$x mycmd"));
    }

    // ---- checkCommandWithTrailingSymbol ----
    #[test]
    fn prop_checkCommandWithTrailingSymbol1() {
        assert!(emits(check_command_with_trailing_symbol, "/"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol2() {
        assert!(emits(check_command_with_trailing_symbol, "/foo/ bar/baz"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol3() {
        assert!(emits(check_command_with_trailing_symbol, "/"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol4() {
        assert!(!emits(check_command_with_trailing_symbol, "/*"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol5() {
        assert!(!emits(check_command_with_trailing_symbol, "$foo/$bar"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol6() {
        assert!(emits(check_command_with_trailing_symbol, "foo, bar"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol7() {
        assert!(!emits(check_command_with_trailing_symbol, ". foo.sh"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol8() {
        assert!(!emits(check_command_with_trailing_symbol, ": foo"));
    }
    #[test]
    fn prop_checkCommandWithTrailingSymbol9() {
        assert!(!emits(
            check_command_with_trailing_symbol,
            "/usr/bin/python[23] file.py"
        ));
    }
    #[test]
    fn prop_sc2287_registered() {
        assert!(emits_code(check_command_with_trailing_symbol, "/", 2287));
    }

    // ---- checkBatsTestDoesNotUseNegation ----
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation1() {
        assert!(emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! true;  false; }"
        ));
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation2() {
        assert!(emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [[ -e test ]]; false; }"
        ));
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation3() {
        assert!(emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [ -e test ]; false; }"
        ));
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation4() {
        assert!(!emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { run ! true; }"
        ));
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation5() {
        assert!(!emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [[ -e test ]] || false; }"
        ));
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation6() {
        assert!(!emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [ -e test ] || false; }"
        ));
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation7() {
        assert_eq!(
            codes(
                check_bats_test_does_not_use_negation,
                "#!/usr/bin/env/bats\n@test \"name\" { ! true; }"
            ),
            vec![2314]
        );
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation8() {
        assert_eq!(
            codes(
                check_bats_test_does_not_use_negation,
                "#!/usr/bin/env/bats\n@test \"name\" { ! [[ -e test ]]; }"
            ),
            vec![2315]
        );
    }
    #[test]
    fn prop_checkBatsTestDoesNotUseNegation9() {
        assert_eq!(
            codes(
                check_bats_test_does_not_use_negation,
                "#!/usr/bin/env/bats\n@test \"name\" { ! [ -e test ]; }"
            ),
            vec![2315]
        );
    }
}
