//! Ported check batch y. See rust/PORTING.md.
//!
//! Faithful ports of:
//!   * SC2070 — checkUnquotedN (Analytics.hs): `[ -n $foo ]` with an unquoted,
//!     word-splitting argument in a single-bracket test.
//!   * SC2240 — checkSourceArgs (Checks/Commands.hs): the `.`/`source` dot
//!     command given arguments under sh/dash, which do not support them.
//!
//! Helpers are private to this module (ported from ASTLib / AnalyzerLib), so
//! the module does not touch shared files that parallel agents also edit.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::cfg::oversimplify;
use crate::interface::{Code, Shell};

pub fn register(c: &mut Checker) {
    c.node(check_unquoted_n);
    c.node(check_source_args);
}

// ===========================================================================
// Shared local helpers (ported from ASTLib).
// ===========================================================================

/// The words after the command name of a `T_SimpleCommand`.
fn arguments(t: &Token) -> &[Token] {
    match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => &words[1..],
        _ => &[],
    }
}

/// `oversimplify` concatenated to a single string.
fn oversimplify_concat(t: &Token) -> String {
    oversimplify(t).concat()
}

/// `getWordParts`.
fn get_word_parts(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_NormalWord(l) => l.iter().flat_map(get_word_parts).collect(),
        InnerToken::T_DoubleQuoted(l) => l.iter().collect(),
        InnerToken::TA_Expansion(l) => l.iter().flat_map(get_word_parts).collect(),
        _ => vec![t],
    }
}

/// `isArrayExpansion`.
fn is_array_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let s = oversimplify_concat(op);
            s.starts_with('@') || (!s.starts_with('#') && s.contains("[@]"))
        }
        _ => false,
    }
}

/// `willSplit`.
fn will_split(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => true,
        T_DollarExpansion(_) => true,
        T_Backticked(_) => true,
        T_BraceExpansion(_) => true,
        T_Glob(_) => true,
        T_Extglob { .. } => true,
        T_DoubleQuoted(l) => l.iter().any(will_become_multiple_args),
        T_NormalWord(l) => l.iter().any(will_split),
        _ => false,
    }
}

/// `willBecomeMultipleArgs`.
fn will_become_multiple_args(t: &Token) -> bool {
    will_concat_in_assignment(t) || wbma_f(t)
}
fn wbma_f(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_Extglob { .. } => true,
        T_Glob(_) => true,
        T_BraceExpansion(_) => true,
        T_NormalWord(parts) => parts.iter().any(wbma_f),
        _ => false,
    }
}
fn will_concat_in_assignment(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => is_array_expansion(t),
        T_DoubleQuoted(parts) => parts.iter().any(will_concat_in_assignment),
        T_NormalWord(parts) => parts.iter().any(will_concat_in_assignment),
        _ => false,
    }
}

// ===========================================================================
// SC2070 — checkUnquotedN
// ===========================================================================
//
// checkUnquotedN _ (TC_Unary _ SingleBracket "-n" t) | willSplit t =
//     unless (any isArrayExpansion $ getWordParts t) $ -- There's SC2198 for these
//        err (getId t) 2070 "-n doesn't work with unquoted arguments. Quote or use [[ ]]."
// checkUnquotedN _ _ = return ()

fn check_unquoted_n(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Unary { typ, op, token } = &*t.inner {
        if *typ == ConditionType::SingleBracket && op == "-n" && will_split(token) {
            if !get_word_parts(token).iter().any(|p| is_array_expansion(p)) {
                err(
                    out,
                    token.id(),
                    2070,
                    "-n doesn't work with unquoted arguments. Quote or use [[ ]].",
                );
            }
        }
    }
}

// ===========================================================================
// SC2240 — checkSourceArgs
// ===========================================================================
//
// checkSourceArgs = CommandCheck (Exactly ".") f
//   where
//     f t = whenShell [Sh, Dash] $
//         case arguments t of
//             (file:arg1:_) -> warn (getId arg1) 2240 $
//                 "The dot command does not support arguments in sh/dash. Set them as variables."
//             _ -> return ()

/// Effective command token if a check registered under `Exactly target` would
/// fire on `t`, per `checkCommand`.
fn dispatch_exactly(t: &Token, target: &str) -> Option<Token> {
    let (assignments, words) = match &*t.inner {
        InnerToken::T_SimpleCommand { assignments, words } if !words.is_empty() => {
            (assignments, words)
        }
        _ => return None,
    };
    let name = astlib::get_literal_string(&words[0])?;
    if name.contains('/') {
        return None; // slash -> only Basename dispatch
    }
    if name == "builtin" && words.len() >= 2 {
        let selected = astlib::only_literal_string(&words[1]);
        if selected == target {
            return Some(Token::new(
                t.id(),
                InnerToken::T_SimpleCommand {
                    assignments: assignments.clone(),
                    words: words[1..].to_vec(),
                },
            ));
        }
        return None;
    }
    if name == target { Some(t.clone()) } else { None }
}

fn check_source_args(params: &Parameters, t: &Token, out: &mut Out) {
    let te = match dispatch_exactly(t, ".") {
        Some(x) => x,
        None => return,
    };
    // whenShell [Sh, Dash]
    if !matches!(params.shell, Shell::Sh | Shell::Dash) {
        return;
    }
    let args = arguments(&te);
    if args.len() >= 2 {
        // (file:arg1:_)
        let arg1 = &args[1];
        warn(
            out,
            arg1.id(),
            2240,
            "The dot command does not support arguments in sh/dash. Set them as variables.",
        );
    }
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

    fn produces(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params
            .root
            .visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // checkUnquotedN (SC2070)
    #[test]
    fn prop_checkUnquotedN() {
        assert!(produces(check_unquoted_n, "if [ -n $foo ]; then echo cow; fi"));
    }
    #[test]
    fn prop_checkUnquotedN2() {
        assert!(produces(check_unquoted_n, "[ -n $cow ]"));
    }
    #[test]
    fn prop_checkUnquotedN3() {
        assert!(!produces(check_unquoted_n, "[[ -n $foo ]] && echo cow"));
    }
    #[test]
    fn prop_checkUnquotedN4() {
        assert!(produces(check_unquoted_n, "[ -n $cow -o -t 1 ]"));
    }
    #[test]
    fn prop_checkUnquotedN5() {
        assert!(!produces(check_unquoted_n, "[ -n \"$@\" ]"));
    }

    // checkSourceArgs (SC2240)
    #[test]
    fn prop_checkSourceArgs1() {
        assert!(produces(check_source_args, "#!/bin/sh\n. script arg"));
    }
    #[test]
    fn prop_checkSourceArgs2() {
        assert!(!produces(check_source_args, "#!/bin/sh\n. script"));
    }
    #[test]
    fn prop_checkSourceArgs3() {
        assert!(!produces(check_source_args, "#!/bin/bash\n. script arg"));
    }
}
