//! Arithmetic-context checks from `ShellCheck.Analytics`.
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_word_parts;
use crate::astlib::oversimplify_concat;
use crate::cfg::get_braced_reference;
use crate::cfg::get_unquoted_literal;
use crate::interface::Shell;

pub(super) fn check_div_before_mult(params: &Parameters, t: &Token, out: &mut Out) {
    // TA_Binary _ "*" (TA_Binary id "/" _ x) y
    if let InnerToken::TA_Binary { op, lhs, rhs } = &*t.inner {
        if op == "*" {
            if let InnerToken::TA_Binary {
                op: inner_op,
                lhs: _,
                rhs: x,
            } = &*lhs.inner
            {
                if inner_op == "/" {
                    let y = rhs;
                    if !has_floating_point(params) && x != y {
                        info(
                            out,
                            lhs.id(),
                            2017,
                            "Increase precision by replacing a/b*c with a*c/b.",
                        );
                    }
                }
            }
        }
    }
}

pub(super) fn check_arithmetic_deref(params: &Parameters, t: &Token, out: &mut Out) {
    let list = match &*t.inner {
        InnerToken::TA_Expansion(l) => l,
        _ => return,
    };
    if list.len() != 1 {
        return;
    }
    let (id, op) = match &*list[0].inner {
        InnerToken::T_DollarBraced { op, .. } => (list[0].id(), op),
        _ => return,
    };
    if arith_deref_is_exception(&oversimplify_concat(op)) {
        return;
    }
    // fromMaybe noWarning . msum . map warningFor $ parents params t
    // parents = the token itself followed by its ancestors up to the root.
    let mut cur = t.clone();
    loop {
        match &*cur.inner {
            InnerToken::T_Arithmetic(_)
            | InnerToken::T_DollarArithmetic(_)
            | InnerToken::T_ForArithmetic { .. }
            | InnerToken::T_Assignment { .. } => {
                style(
                    out,
                    id,
                    2004,
                    "$/${} is unnecessary on arithmetic variables.",
                );
                return;
            }
            InnerToken::T_SimpleCommand { .. } => return,
            _ => {}
        }
        match params.parent(&cur) {
            Some(p) => cur = p.clone(),
            None => return,
        }
    }
}

pub(super) fn check_arithmetic_bad_octal(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TA_Expansion(_) = &*t.inner {
        if let Some(str) = full_literal_string(t) {
            if octal_re_match(&str) {
                err(
                    out,
                    t.id(),
                    2080,
                    "Numbers with leading 0 are considered octal.",
                );
            }
        }
    }
}

pub(super) fn check_arithmetic_op_command(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_wrong_arithmetic_assignment(params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_modified_arithmetic_in_redirection(
    params: &Parameters,
    t: &Token,
    out: &mut Out,
) {
    if params.shell == Shell::Dash || params.shell == Shell::BusyboxSh {
        return;
    }
    if let InnerToken::T_Redirecting { redirs, cmd } = &*t.inner {
        // T_SimpleCommand _ _ (_:_)
        let is_nonempty_simple = matches!(
            &*cmd.inner,
            InnerToken::T_SimpleCommand { words, .. } if !words.is_empty()
        );
        if is_nonempty_simple {
            for r in redirs {
                check_redir(r, out);
            }
        }
    }
}

pub(super) fn check_unnecessary_arithmetic_expansion_index(
    params: &Parameters,
    t: &Token,
    out: &mut Out,
) {
    // T_Assignment _ mode var [TA_Sequence _ [ TA_Expansion _ [T_DollarArithmetic id _]]] val
    if let InnerToken::T_Assignment { indices, .. } = &*t.inner {
        if indices.len() == 1 {
            if let InnerToken::TA_Sequence(seq) = &*indices[0].inner {
                if seq.len() == 1 {
                    if let InnerToken::TA_Expansion(exp) = &*seq[0].inner {
                        if exp.len() == 1 {
                            if let InnerToken::T_DollarArithmetic(_) = &*exp[0].inner {
                                let id = exp[0].id();
                                let fix = fix_with(vec![
                                    replace_start(params, id, 3, ""), // Remove "$(("
                                    replace_end(params, id, 2, ""),   // Remove "))"
                                ]);
                                style_with_fix(
                                    out,
                                    id,
                                    2321,
                                    "Array indices are already arithmetic contexts. Prefer removing the $(( and )).",
                                    fix,
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

pub(super) fn check_unnecessary_parens(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_DollarArithmetic(inner) => {
            check_leading(params, "$(( (x) )) is the same as $(( x ))", inner, out);
        }
        InnerToken::T_ForArithmetic {
            init, cond, step, ..
        } => {
            let msg = "for (((x); (y); (z))) is the same as for ((x; y; z))";
            check_leading(params, msg, init, out);
            check_leading(params, msg, cond, out);
            check_leading(params, msg, step, out);
        }
        InnerToken::T_Assignment { indices, .. } if indices.len() == 1 => {
            check_leading(params, "a[(x)] is the same as a[x]", &indices[0], out);
        }
        InnerToken::T_Arithmetic(inner) => {
            check_leading(params, "(( (x) )) is the same as (( x ))", inner, out);
        }
        InnerToken::TA_Parenthesis(seq) => {
            if let InnerToken::TA_Sequence(list) = &*seq.inner {
                if list.len() == 1 {
                    if let InnerToken::TA_Parenthesis(_) = &*list[0].inner {
                        let id = list[0].id();
                        style_with_fix(
                            out,
                            id,
                            2322,
                            "In arithmetic contexts, ((x)) is the same as (x). Prefer only one layer of parentheses.",
                            paren_fix(params, id),
                        );
                    }
                }
            }
        }
        _ => {}
    }
}

pub(super) fn check_plus_equals_number(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Assignment {
        mode: AssignmentMode::Append,
        var,
        value,
        ..
    } = &*t.inner
    {
        let id = t.id();
        (|| {
            let cfga = params.cfg_analysis.as_ref()?;
            let state = cfga.get_incoming_state(id)?;
            if !is_number(&state, value) {
                return None;
            }
            if state.variable_may_be_declared_integer(var).unwrap_or(false) {
                return None;
            }
            warn(
                out,
                id,
                2324,
                "var+=1 will append, not increment. Use (( var += 1 )), typeset -i var, or quote number to silence.",
            );
            Some(())
        })();
    }
}

fn arith_deref_is_exception(s: &str) -> bool {
    const SPECIAL: &str = "/.:#%?*@$-!+=^,";
    match s.chars().next() {
        None => true,
        Some(h) => s.chars().any(|c| SPECIAL.contains(c)) || h.is_ascii_digit(),
    }
}

/// `getGlobOrLiteralString`.
fn get_glob_or_literal_string(t: &Token) -> Option<String> {
    astlib::get_literal_string_ext(t, &|inner| match inner {
        InnerToken::T_Glob(s) => Some(s.clone()),
        _ => None,
    })
}

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

/// `getLiteralString` mirroring `getLiteralStringExt (const Nothing)`, including
/// the `TA_Expansion` / `T_ParamSubSpecialChar` cases the shared astlib helper
/// omits. (decodeEscapes on `T_DollarSingleQuoted` is not needed for our uses.)
fn full_literal_string(t: &Token) -> Option<String> {
    fn go(t: &Token, out: &mut String) -> bool {
        match &*t.inner {
            InnerToken::T_DoubleQuoted(l)
            | InnerToken::T_DollarDoubleQuoted(l)
            | InnerToken::T_NormalWord(l)
            | InnerToken::TA_Expansion(l) => {
                for p in l {
                    if !go(p, out) {
                        return false;
                    }
                }
                true
            }
            InnerToken::T_SingleQuoted(s)
            | InnerToken::T_Literal(s)
            | InnerToken::T_ParamSubSpecialChar(s)
            | InnerToken::T_DollarSingleQuoted(s) => {
                out.push_str(s);
                true
            }
            _ => false,
        }
    }
    let mut s = String::new();
    if go(t, &mut s) { Some(s) } else { None }
}

/// `getUnmodifiedParameterExpansion`.
fn get_unmodified_parameter_expansion(t: &Token) -> Option<String> {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        let str = oversimplify_concat(op);
        if get_braced_reference(&str) == str {
            Some(str)
        } else {
            None
        }
    } else {
        None
    }
}

/// `mkRegex "^0[0-7]*[8-9]"` (unanchored `matches`, i.e. `find`).
fn octal_re_match(s: &str) -> bool {
    use std::sync::OnceLock;
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    let re = RE.get_or_init(|| regex::Regex::new(r"^0[0-7]*[8-9]").unwrap());
    re.is_match(s)
}

fn check_redir(t: &Token, out: &mut Out) {
    if let InnerToken::T_FdRedirect { target, .. } = &*t.inner {
        match &*target.inner {
            InnerToken::T_IoFile { file, .. } => {
                for p in get_word_parts(file) {
                    check_arithmetic(p, out);
                }
            }
            InnerToken::T_HereString(word) => {
                for p in get_word_parts(word) {
                    check_arithmetic(p, out);
                }
            }
            InnerToken::T_HereDoc { body, .. } => {
                for p in body {
                    check_arithmetic(p, out);
                }
            }
            _ => {}
        }
    }
}

fn check_arithmetic(t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarArithmetic(x) = &*t.inner {
        check_modifying(x, out);
    }
}

fn check_modifying(t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TA_Sequence(list) => {
            for x in list {
                check_modifying(x, out);
            }
        }
        InnerToken::TA_Unary { op, .. }
            if op == "|++" || op == "++|" || op == "|--" || op == "--|" =>
        {
            warn_2257(t.id(), out);
        }
        InnerToken::TA_Assignment { .. } => warn_2257(t.id(), out),
        InnerToken::TA_Binary { lhs, rhs, .. } => {
            check_modifying(lhs, out);
            check_modifying(rhs, out);
        }
        InnerToken::TA_Trinary { cond, then, els } => {
            check_modifying(cond, out);
            check_modifying(then, out);
            check_modifying(els, out);
        }
        _ => {}
    }
}

fn warn_2257(id: Id, out: &mut Out) {
    warn(
        out,
        id,
        2257,
        "Arithmetic modifications in command redirections may be discarded. Do them separately.",
    );
}

fn check_leading(params: &Parameters, str: &str, t: &Token, out: &mut Out) {
    if let InnerToken::TA_Sequence(list) = &*t.inner {
        if list.len() == 1 {
            if let InnerToken::TA_Parenthesis(_) = &*list[0].inner {
                let id = list[0].id();
                style_with_fix(
                    out,
                    id,
                    2323,
                    &format!("{}. Prefer not wrapping in additional parentheses.", str),
                    paren_fix(params, id),
                );
            }
        }
    }
}

fn paren_fix(params: &Parameters, id: Id) -> crate::interface::Fix {
    fix_with(vec![
        replace_start(params, id, 1, ""), // Remove "("
        replace_end(params, id, 1, ""),   // Remove ")"
    ])
}

fn is_number(state: &crate::cfg_analysis::ProgramState, word: &Token) -> bool {
    let unquoted_literal = get_unquoted_literal(word);
    let is_empty = unquoted_literal.as_deref() == Some("");
    let is_unquoted_number = !is_empty
        && unquoted_literal
            .as_ref()
            .map(|s| s.chars().all(|c| c.is_ascii_digit()))
            .unwrap_or(false);
    let is_numerical_variable_name = unquoted_literal
        .as_ref()
        .and_then(|str| state.variable_may_be_assigned_integer(str))
        .unwrap_or(false);
    let is_numerical_variable_expansion = match &*word.inner {
        InnerToken::T_NormalWord(parts) if parts.len() == 1 => {
            get_unmodified_parameter_expansion(&parts[0])
                .and_then(|str| state.variable_may_be_assigned_integer(&str))
                .unwrap_or(false)
        }
        _ => false,
    };
    is_unquoted_number || is_numerical_variable_name || is_numerical_variable_expansion
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkArithmeticDeref1() {
        assert!(emits(check_arithmetic_deref, "echo $((3+$foo))"));
    }

    #[test]
    fn prop_checkArithmeticDeref2() {
        assert!(emits(check_arithmetic_deref, "cow=14; (( s+= $cow ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref3() {
        assert!(!emits(
            check_arithmetic_deref,
            "cow=1/40; (( s+= ${cow%%/*} ))"
        ));
    }

    #[test]
    fn prop_checkArithmeticDeref4() {
        assert!(!emits(check_arithmetic_deref, "(( ! $? ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref5() {
        assert!(!emits(check_arithmetic_deref, "(($1))"));
    }

    #[test]
    fn prop_checkArithmeticDeref6() {
        assert!(emits(check_arithmetic_deref, "(( a[$i] ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref7() {
        assert!(!emits(check_arithmetic_deref, "(( 10#$n ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref8() {
        assert!(!emits(check_arithmetic_deref, "let i=$i+1"));
    }

    #[test]
    fn prop_checkArithmeticDeref9() {
        assert!(!emits(check_arithmetic_deref, "(( a[foo] ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref10() {
        assert!(!emits(check_arithmetic_deref, "(( a[\\$foo] ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref11() {
        assert!(emits(check_arithmetic_deref, "a[$foo]=wee"));
    }

    #[test]
    fn prop_checkArithmeticDeref11b() {
        assert!(!emits(check_arithmetic_deref, "declare -A a; a[$foo]=wee"));
    }

    #[test]
    fn prop_checkArithmeticDeref12() {
        assert!(emits(
            check_arithmetic_deref,
            "for ((i=0; $i < 3; i)); do true; done"
        ));
    }

    #[test]
    fn prop_checkArithmeticDeref13() {
        assert!(!emits(check_arithmetic_deref, "(( $$ ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref14() {
        assert!(!emits(check_arithmetic_deref, "(( $! ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref15() {
        assert!(!emits(check_arithmetic_deref, "(( ${!var} ))"));
    }

    #[test]
    fn prop_checkArithmeticDeref16() {
        assert!(!emits(check_arithmetic_deref, "(( ${x+1} + ${x=42} ))"));
    }

    // ---- SC2219 checkLetUsage ----

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
    fn prop_checkDivBeforeMult() {
        assert!(node_emits(check_div_before_mult, "echo $((c/n*100))"));
    }

    #[test]
    fn prop_checkDivBeforeMult2() {
        assert!(!(node_emits(check_div_before_mult, "echo $((c*100/n))")));
    }

    #[test]
    fn prop_checkDivBeforeMult3() {
        assert!(!(node_emits(check_div_before_mult, "echo $((c/10*10))")));
    }

    // --- SC2080 checkArithmeticBadOctal ---

    #[test]
    fn prop_checkArithmeticBadOctal1() {
        assert!(node_emits(check_arithmetic_bad_octal, "(( 0192 ))"));
    }

    #[test]
    fn prop_checkArithmeticBadOctal2() {
        assert!(!(node_emits(check_arithmetic_bad_octal, "(( 0x192 ))")));
    }

    #[test]
    fn prop_checkArithmeticBadOctal3() {
        assert!(!(node_emits(check_arithmetic_bad_octal, "(( 1 ^ 0777 ))")));
    }

    // --- SC2257 checkModifiedArithmeticInRedirection ---

    #[test]
    fn prop_checkModifiedArithmeticInRedirection1() {
        assert!(node_emits(
            check_modified_arithmetic_in_redirection,
            "ls > $((i++))"
        ));
    }

    #[test]
    fn prop_checkModifiedArithmeticInRedirection2() {
        assert!(node_emits(
            check_modified_arithmetic_in_redirection,
            "cat < \"foo$((i++)).txt\""
        ));
    }

    #[test]
    fn prop_checkModifiedArithmeticInRedirection3() {
        assert!(
            !(node_emits(
                check_modified_arithmetic_in_redirection,
                "while true; do true; done > $((i++))"
            ))
        );
    }

    #[test]
    fn prop_checkModifiedArithmeticInRedirection4() {
        assert!(node_emits(
            check_modified_arithmetic_in_redirection,
            "cat <<< $((i++))"
        ));
    }

    #[test]
    fn prop_checkModifiedArithmeticInRedirection5() {
        assert!(node_emits(
            check_modified_arithmetic_in_redirection,
            "cat << foo\n$((i++))\nfoo\n"
        ));
    }

    #[test]
    fn prop_checkModifiedArithmeticInRedirection6() {
        assert!(
            !(node_emits(
                check_modified_arithmetic_in_redirection,
                "#!/bin/dash\nls > $((i=i+1))"
            ))
        );
    }

    #[test]
    fn prop_checkModifiedArithmeticInRedirection7() {
        assert!(
            !(node_emits(
                check_modified_arithmetic_in_redirection,
                "#!/bin/busybox sh\ncat << foo\n$((i++))\nfoo\n"
            ))
        );
    }

    // --- SC2321 checkUnnecessaryArithmeticExpansionIndex ---

    #[test]
    fn prop_checkUnnecessaryArithmeticExpansionIndex1() {
        assert!(node_emits(
            check_unnecessary_arithmetic_expansion_index,
            "a[$((1+1))]=n"
        ));
    }

    #[test]
    fn prop_checkUnnecessaryArithmeticExpansionIndex2() {
        assert!(!(node_emits(check_unnecessary_arithmetic_expansion_index, "a[1+1]=n")));
    }

    #[test]
    fn prop_checkUnnecessaryArithmeticExpansionIndex3() {
        assert!(
            !(node_emits(
                check_unnecessary_arithmetic_expansion_index,
                "a[$(echo $((1+1)))]=n"
            ))
        );
    }

    #[test]
    fn prop_checkUnnecessaryArithmeticExpansionIndex4() {
        assert!(
            !(node_emits(
                check_unnecessary_arithmetic_expansion_index,
                "declare -A a; a[$((1+1))]=val"
            ))
        );
    }

    // --- SC2322/2323 checkUnnecessaryParens ---

    #[test]
    fn prop_checkUnnecessaryParens1() {
        assert!(node_emits(check_unnecessary_parens, "echo $(( ((1+1)) ))"));
    }

    #[test]
    fn prop_checkUnnecessaryParens2() {
        assert!(node_emits(check_unnecessary_parens, "x[((1+1))+1]=1"));
    }

    #[test]
    fn prop_checkUnnecessaryParens3() {
        assert!(node_emits(check_unnecessary_parens, "x[(1+1)]=1"));
    }

    #[test]
    fn prop_checkUnnecessaryParens4() {
        assert!(node_emits(check_unnecessary_parens, "$(( (x) ))"));
    }

    #[test]
    fn prop_checkUnnecessaryParens5() {
        assert!(node_emits(check_unnecessary_parens, "(( (x) ))"));
    }

    #[test]
    fn prop_checkUnnecessaryParens6() {
        assert!(!(node_emits(check_unnecessary_parens, "x[(1+1)+1]=1")));
    }

    #[test]
    fn prop_checkUnnecessaryParens7() {
        assert!(!(node_emits(check_unnecessary_parens, "(( (1*1)+1 ))")));
    }

    #[test]
    fn prop_checkUnnecessaryParens8() {
        assert!(!(node_emits(check_unnecessary_parens, "(( (1)+1 ))")));
    }

    // --- SC2218 checkUseBeforeDefinition ---

    #[test]
    fn prop_checkPlusEqualsNumber1() {
        assert!(node_emits(check_plus_equals_number, "x+=1"));
    }

    #[test]
    fn prop_checkPlusEqualsNumber2() {
        assert!(node_emits(check_plus_equals_number, "x+=42"));
    }

    #[test]
    fn prop_checkPlusEqualsNumber3() {
        assert!(!(node_emits(check_plus_equals_number, "(( x += 1 ))")));
    }

    #[test]
    fn prop_checkPlusEqualsNumber4() {
        assert!(!(node_emits(check_plus_equals_number, "declare -i x=0; x+=1")));
    }

    #[test]
    fn prop_checkPlusEqualsNumber5() {
        assert!(!(node_emits(check_plus_equals_number, "x+='1'")));
    }

    #[test]
    fn prop_checkPlusEqualsNumber6() {
        assert!(!(node_emits(check_plus_equals_number, "n=foo; x+=n")));
    }

    #[test]
    fn prop_checkPlusEqualsNumber7() {
        assert!(node_emits(check_plus_equals_number, "n=4; x+=n"));
    }

    #[test]
    fn prop_checkPlusEqualsNumber8() {
        assert!(node_emits(check_plus_equals_number, "n=4; x+=$n"));
    }

    #[test]
    fn prop_checkPlusEqualsNumber9() {
        assert!(!(node_emits(check_plus_equals_number, "declare -ia var; var[x]+=1")));
    }
}
