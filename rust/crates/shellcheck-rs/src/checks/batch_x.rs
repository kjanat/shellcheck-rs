//! Batch X — CFG-dataflow and arithmetic-tree checks ported from
//! `ShellCheck.Analytics`.
//!
//! CFG-dataflow (uses `Parameters.cfg_analysis`, mirroring `CFGAnalysis` /
//! `CF.getIncomingState` / `CF.doesPostDominate`):
//!   * SC2218       — `checkUseBeforeDefinition`      (tree)
//!   * SC2317/2329  — `checkCommandIsUnreachable`     (node)
//!   * SC2319/2320  — `checkOverwrittenExitCode`      (node)
//!   * SC2324       — `checkPlusEqualsNumber`         (node)
//!
//! Arithmetic-tree (operate on `TA_*` nodes):
//!   * SC2017       — `checkDivBeforeMult`            (node)
//!   * SC2080       — `checkArithmeticBadOctal`       (node)
//!   * SC2257       — `checkModifiedArithmeticInRedirection` (node)
//!   * SC2321       — `checkUnnecessaryArithmeticExpansionIndex` (node)
//!   * SC2322/2323  — `checkUnnecessaryParens`        (node)
#![allow(clippy::collapsible_if)]

use crate::analyzer_lib::*;
use crate::analyzer_lib::{concat_over, is_sourced};
use crate::ast::*;
use crate::astlib::get_word_parts;
use crate::cfg::get_braced_reference;
use crate::cfg::get_unquoted_literal;
use crate::interface::Shell;
use std::collections::BTreeMap;

pub fn register(c: &mut Checker) {
    // Registration is gated by the conformance guardrail (extra == 0 per code).
    c.tree(check_use_before_definition);
    c.node(check_command_is_unreachable);
    c.node(check_overwritten_exit_code);
    c.node(check_plus_equals_number);
    c.node(check_div_before_mult);
    c.node(check_arithmetic_bad_octal);
    c.node(check_modified_arithmetic_in_redirection);
    c.node(check_unnecessary_arithmetic_expansion_index);
    c.node(check_unnecessary_parens);
}

// ===========================================================================
// Shared local helpers
// ===========================================================================

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
        let str = concat_over(op);
        if get_braced_reference(&str) == str {
            Some(str)
        } else {
            None
        }
    } else {
        None
    }
}

/// `hasFloatingPoint params`.
fn has_floating_point(params: &Parameters) -> bool {
    params.shell == Shell::Ksh
}

// ===========================================================================
// SC2017 — checkDivBeforeMult
// ===========================================================================

fn check_div_before_mult(params: &Parameters, t: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2080 — checkArithmeticBadOctal
// ===========================================================================

fn check_arithmetic_bad_octal(_params: &Parameters, t: &Token, out: &mut Out) {
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

/// `mkRegex "^0[0-7]*[8-9]"` (unanchored `matches`, i.e. `find`).
fn octal_re_match(s: &str) -> bool {
    use std::sync::OnceLock;
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    let re = RE.get_or_init(|| regex::Regex::new(r"^0[0-7]*[8-9]").unwrap());
    re.is_match(s)
}

// ===========================================================================
// SC2257 — checkModifiedArithmeticInRedirection
// ===========================================================================

fn check_modified_arithmetic_in_redirection(params: &Parameters, t: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2321 — checkUnnecessaryArithmeticExpansionIndex
// ===========================================================================

fn check_unnecessary_arithmetic_expansion_index(params: &Parameters, t: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2322 / SC2323 — checkUnnecessaryParens
// ===========================================================================

fn check_unnecessary_parens(params: &Parameters, t: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2218 — checkUseBeforeDefinition (tree)
// ===========================================================================

fn check_use_before_definition(params: &Parameters, root: &Token, out: &mut Out) {
    let cfga = match params.cfg_analysis.as_ref() {
        Some(c) => c,
        None => return,
    };

    // funcs: name -> [definition ids]
    let mut funcs: BTreeMap<String, Vec<Id>> = BTreeMap::new();
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_Function { name, .. } = &*t.inner {
            funcs.entry(name.clone()).or_default().push(t.id());
        }
    });

    // Green cut: no functions -> nothing to do.
    if funcs.is_empty() {
        return;
    }

    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            if let Some(cmd) = words.first() {
                let id = t.id();
                (|| {
                    let name = crate::astlib::get_literal_string(cmd)?;
                    let invocations = funcs.get(&name)?;
                    // Is the function definitely being defined later?
                    if !invocations.iter().any(|&c| cfga.does_post_dominate(c, id)) {
                        return None;
                    }
                    // Was one already defined, so it's actually a re-definition?
                    if invocations.iter().any(|&c| cfga.does_post_dominate(id, c)) {
                        return None;
                    }
                    err(
                        out,
                        id,
                        2218,
                        "This function is only defined later. Move the definition up.",
                    );
                    Some(())
                })();
            }
        }
    });
}

// ===========================================================================
// SC2317 / SC2329 — checkCommandIsUnreachable (node)
// ===========================================================================

fn is_unreachable(params: &Parameters, t: &Token) -> bool {
    (|| {
        let cfga = params.cfg_analysis.as_ref()?;
        let state = cfga.get_incoming_state(t.id())?;
        Some(!state.state_is_reachable())
    })()
    .unwrap_or(false)
}

fn is_unreachable_function(params: &Parameters, f: &Token) -> bool {
    if let InnerToken::T_Function { body, .. } = &*f.inner {
        is_unreachable(params, body)
    } else {
        false
    }
}

fn check_command_is_unreachable(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Pipeline { .. } => {
            (|| {
                let cfga = params.cfg_analysis.as_ref()?;
                let state = cfga.get_incoming_state(t.id())?;
                if state.state_is_reachable() {
                    return None;
                }
                if is_sourced(params, t) {
                    return None;
                }
                let path = get_path(params, t);
                if path
                    .iter()
                    .skip(1)
                    .any(|a| is_unreachable(params, a) || is_unreachable_function(params, a))
                {
                    return None;
                }
                info(
                    out,
                    t.id(),
                    2317,
                    "Command appears to be unreachable. Check usage (or ignore if invoked indirectly).",
                );
                Some(())
            })();
        }
        InnerToken::T_Function { .. } => {
            let path = get_path(params, t);
            if is_unreachable_function(params, t)
                && !path
                    .iter()
                    .skip(1)
                    .any(|a| is_unreachable_function(params, a))
                && !is_sourced(params, t)
            {
                info(
                    out,
                    t.id(),
                    2329,
                    "This function is never invoked. Check usage (or ignored if invoked indirectly).",
                );
            }
        }
        _ => {}
    }
}

// ===========================================================================
// SC2319 / SC2320 — checkOverwrittenExitCode (node)
// ===========================================================================

fn check_overwritten_exit_code(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        if crate::astlib::get_literal_string(op).as_deref() == Some("?") {
            overwritten_check(params, t, out);
        }
    }
}

fn overwritten_check(params: &Parameters, t: &Token, out: &mut Out) {
    let id = t.id();
    (|| {
        let cfga = params.cfg_analysis.as_ref()?;
        let state = cfga.get_incoming_state(id)?;
        let exit_code_ids = state.exit_codes().clone();
        if exit_code_ids.is_empty() {
            return None;
        }
        // traverse (Map.lookup) — all must be present.
        let mut exit_code_tokens: Vec<Token> = Vec::new();
        for k in exit_code_ids.iter() {
            let tok = params.id_map.get(k)?;
            exit_code_tokens.push(tok.clone());
        }

        if exit_code_tokens.iter().all(is_condition)
            && !used_unconditionally(params, t, &exit_code_ids)
        {
            warn(
                out,
                id,
                2319,
                "This $? refers to a condition, not a command. Assign to a variable to avoid it being overwritten.",
            );
        }
        if exit_code_tokens.iter().all(is_printing) {
            warn(
                out,
                id,
                2320,
                "This $? refers to echo/printf, not a previous command. Assign to variable to avoid it being overwritten.",
            );
        }
        Some(())
    })();
}

fn is_condition(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Condition { .. } => true,
        InnerToken::T_SimpleCommand { .. } => get_command_name(t).as_deref() == Some("test"),
        _ => false,
    }
}

fn used_unconditionally(
    params: &Parameters,
    t: &Token,
    test_ids: &std::collections::BTreeSet<Id>,
) -> bool {
    let cfga = match params.cfg_analysis.as_ref() {
        Some(c) => c,
        None => return false,
    };
    test_ids.iter().all(|&c| cfga.does_post_dominate(t.id(), c))
}

fn is_printing(t: &Token) -> bool {
    matches!(
        get_command_basename(t).as_deref(),
        Some("echo") | Some("printf")
    )
}

// ===========================================================================
// SC2324 — checkPlusEqualsNumber (node)
// ===========================================================================

fn check_plus_equals_number(params: &Parameters, t: &Token, out: &mut Out) {
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

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }
    fn tree_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        f(&params, &params.root, &mut out);
        !out.is_empty()
    }
    fn node_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // --- SC2017 checkDivBeforeMult ---
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
    fn prop_checkUseBeforeDefinition1() {
        assert!(tree_emits(check_use_before_definition, "f; f() { true; }"));
    }
    #[test]
    fn prop_checkUseBeforeDefinition2() {
        assert!(!(tree_emits(check_use_before_definition, "f() { true; }; f")));
    }
    #[test]
    fn prop_checkUseBeforeDefinition3() {
        assert!(
            !(tree_emits(
                check_use_before_definition,
                "if ! mycmd --version; then mycmd() { true; }; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUseBeforeDefinition4() {
        assert!(!(tree_emits(check_use_before_definition, "mycmd || mycmd() { f; }")));
    }
    #[test]
    fn prop_checkUseBeforeDefinition5() {
        assert!(tree_emits(
            check_use_before_definition,
            "false || mycmd; mycmd() { f; }"
        ));
    }
    #[test]
    fn prop_checkUseBeforeDefinition6() {
        assert!(
            !(tree_emits(
                check_use_before_definition,
                "f() { one; }; f; f() { two; }; f"
            ))
        );
    }

    // --- SC2317/2329 checkCommandIsUnreachable ---
    #[test]
    fn prop_checkCommandIsUnreachable1() {
        assert!(node_emits(
            check_command_is_unreachable,
            "foo; bar; exit; baz"
        ));
    }
    #[test]
    fn prop_checkCommandIsUnreachable2() {
        assert!(node_emits(
            check_command_is_unreachable,
            "die() { exit; }; foo; bar; die; baz"
        ));
    }
    #[test]
    fn prop_checkCommandIsUnreachable3() {
        assert!(!(node_emits(check_command_is_unreachable, "foo; bar || exit; baz")));
    }
    #[test]
    fn prop_checkCommandIsUnreachable4() {
        assert!(
            !(node_emits(
                check_command_is_unreachable,
                "f() { foo; };    # Maybe sourced"
            ))
        );
    }
    #[test]
    fn prop_checkCommandIsUnreachable5() {
        assert!(node_emits(
            check_command_is_unreachable,
            "f() { foo; }; exit  # Not sourced"
        ));
    }

    // --- SC2319/2320 checkOverwrittenExitCode ---
    #[test]
    fn prop_checkOverwrittenExitCode1() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; [ $? -eq 1 ] || [ $? -eq 2 ]"
        ));
    }
    #[test]
    fn prop_checkOverwrittenExitCode2() {
        assert!(!(node_emits(check_overwritten_exit_code, "x; [ $? -eq 1 ]")));
    }
    #[test]
    fn prop_checkOverwrittenExitCode3() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; echo \"Exit is $?\"; [ $? -eq 0 ]"
        ));
    }
    #[test]
    fn prop_checkOverwrittenExitCode4() {
        assert!(
            !(node_emits(
                check_overwritten_exit_code,
                "x; [ $? -eq 0 ] && echo Success"
            ))
        );
    }
    #[test]
    fn prop_checkOverwrittenExitCode5() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; if [ $? -eq 0 ]; then var=$?; fi"
        ));
    }
    #[test]
    fn prop_checkOverwrittenExitCode6() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; [ $? -gt 0 ] && fail=$?"
        ));
    }
    #[test]
    fn prop_checkOverwrittenExitCode7() {
        assert!(!(node_emits(check_overwritten_exit_code, "[ 1 -eq 2 ]; status=$?")));
    }
    #[test]
    fn prop_checkOverwrittenExitCode8() {
        assert!(!(node_emits(check_overwritten_exit_code, "[ 1 -eq 2 ]; exit $?")));
    }

    // --- SC2324 checkPlusEqualsNumber ---
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
