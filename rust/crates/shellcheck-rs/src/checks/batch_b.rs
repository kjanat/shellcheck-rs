//! Ported check batch b. See rust/PORTING.md.
//!
//! Ported checks:
//! - SC2005  checkUuoeCmd            (Checks/Commands.hs) — useless `echo $(cmd)`
//! - SC2116  checkUuoeVar            (Analytics.hs)       — useless `cmd $(echo foo)`
//! - SC2027  checkInexplicablyUnquoted (Analytics.hs, 2027 branch only)
//! - SC2145  checkConcatenatedDollarAt (Analytics.hs)
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::assignment_is_quoting;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::is_assignment_param_to_command;
use crate::analyzer_lib::is_quote_free;
use crate::analyzer_lib::is_quote_free_context;
use crate::analyzer_lib::is_quote_free_element;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_word_parts;
use crate::astlib::is_only_redirection;
use crate::astlib::only_literal_string;
use crate::interface::Shell;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_uuoe_cmd);
    c.node(check_uuoe_var);
    c.node(check_inexplicably_unquoted_2027);
    c.node(check_concatenated_dollar_at);
}

// ---------------------------------------------------------------------------
// Shared helper predicates (ported privately; astlib.rs is owned elsewhere).
// ---------------------------------------------------------------------------

/// `tokenIsJustCommandOutput` (AnalyzerLib): a word that is entirely the output
/// of a single command substitution.
fn token_is_just_command_output(t: &Token) -> bool {
    // check: exactly one command, and it isn't only a redirection.
    fn check(cmds: &[Token]) -> bool {
        cmds.len() == 1 && !is_only_redirection(&cmds[0])
    }
    if let InnerToken::T_NormalWord(parts) = &*t.inner {
        if parts.len() == 1 {
            match &*parts[0].inner {
                InnerToken::T_DollarExpansion(cmds) => return check(cmds),
                InnerToken::T_Backticked(cmds) => return check(cmds),
                InnerToken::T_DoubleQuoted(inner) if inner.len() == 1 => match &*inner[0].inner {
                    InnerToken::T_DollarExpansion(cmds) => return check(cmds),
                    InnerToken::T_Backticked(cmds) => return check(cmds),
                    _ => {}
                },
                _ => {}
            }
        }
    }
    false
}

// ---- isQuoteFree (AnalyzerLib.isQuoteFreeNode strict=False) ----------------

// ---------------------------------------------------------------------------
// SC2005 — checkUuoeCmd
// ---------------------------------------------------------------------------

/// Effective argument list of an `echo` command per the CommandCheck dispatch:
/// the first word literal must be exactly "echo" (no slash → `Basename`
/// dispatch, which is a different check), with a `builtin echo` re-dispatch.
fn echo_arguments(words: &[Token]) -> Option<&[Token]> {
    let (cmd, rest) = words.split_first()?;
    let name = astlib::get_literal_string(cmd)?;
    if name.contains('/') {
        return None; // dispatched via Basename, not Exactly "echo"
    }
    if name == "builtin" {
        let (h, tail) = rest.split_first()?;
        if only_literal_string(h) == "echo" {
            return Some(tail);
        }
        return None;
    }
    if name == "echo" {
        return Some(rest);
    }
    None
}

fn check_uuoe_cmd(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        if let Some(args) = echo_arguments(words) {
            if args.len() == 1 && token_is_just_command_output(&args[0]) {
                style(
                    out,
                    args[0].id(),
                    2005,
                    "Useless echo? Instead of 'echo $(cmd)', just use 'cmd'.",
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2116 — checkUuoeVar
// ---------------------------------------------------------------------------

/// `couldBeOptimized`: the argument won't be re-split/globbed if inlined.
fn could_be_optimized(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Glob(_) | InnerToken::T_Extglob { .. } | InnerToken::T_BraceExpansion(_) => {
            false
        }
        InnerToken::T_NormalWord(l) | InnerToken::T_DoubleQuoted(l) => {
            l.iter().all(could_be_optimized)
        }
        _ => true,
    }
}

fn check_uuoe_var(params: &Parameters, t: &Token, out: &mut Out) {
    let (id, cmds) = match &*t.inner {
        InnerToken::T_Backticked(cmds) => (t.id(), cmds),
        InnerToken::T_DollarExpansion(cmds) => (t.id(), cmds),
        _ => return,
    };
    // check id (T_Pipeline _ _ [T_Redirecting _ _ c]) = warnForEcho id c
    if cmds.len() != 1 {
        return;
    }
    let pipeline = &cmds[0];
    let commands = match &*pipeline.inner {
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => commands,
        _ => return,
    };
    let c = match &*commands[0].inner {
        InnerToken::T_Redirecting { cmd, .. } => cmd,
        _ => return,
    };
    // checkUnqualifiedCommand "echo": first word literal (unqualified) == "echo".
    let words = match &*c.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    let cmd_name = match astlib::get_literal_string(&words[0]) {
        Some(n) => n,
        None => return,
    };
    if cmd_name != "echo" {
        return;
    }
    let vars = &words[1..];
    let (first, rest) = match vars.split_first() {
        Some(x) => x,
        None => return,
    };
    let is_covered = rest.is_empty() && token_is_just_command_output(first);
    if is_covered || only_literal_string(first).starts_with('-') {
        return;
    }
    // Conformance-safety guard: an escaped nested backtick (`echo \`cmd\``) is
    // not reassembled into a `T_Backticked` by the current parser — it leaves
    // literal backtick characters in the arguments, which defeats the
    // `is_covered` (SC2005) detection above and would over-fire here. A
    // correctly parsed command substitution never appears as a literal
    // backtick, so treat any such argument as unreliable and withhold.
    if vars.iter().any(|v| only_literal_string(v).contains('`')) {
        return;
    }
    if vars.iter().all(could_be_optimized) {
        style(
            out,
            id,
            2116,
            "Useless echo? Instead of 'cmd $(echo foo)', just use 'cmd foo'.",
        );
    }
}

// ---------------------------------------------------------------------------
// SC2027 — checkInexplicablyUnquoted (only the expansion branch)
// ---------------------------------------------------------------------------

fn check_inexplicably_unquoted_2027(params: &Parameters, t: &Token, out: &mut Out) {
    let tokens = match &*t.inner {
        InnerToken::T_NormalWord(l) => l,
        _ => return,
    };
    // mapM_ check (tails tokens): each consecutive triple starting at position i.
    for w in tokens.windows(3) {
        let a = &w[0];
        let trapped = &w[1];
        let b = &w[2];
        if matches!(&*a.inner, InnerToken::T_DoubleQuoted(_))
            && matches!(&*b.inner, InnerToken::T_DoubleQuoted(_))
        {
            match &*trapped.inner {
                InnerToken::T_DollarExpansion(_) | InnerToken::T_DollarBraced { .. } => {
                    warn(
                        out,
                        trapped.id(),
                        2027,
                        "The surrounding quotes actually unquote this. Remove or escape them.",
                    );
                }
                _ => {}
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2145 — checkConcatenatedDollarAt
// ---------------------------------------------------------------------------

fn check_concatenated_dollar_at(params: &Parameters, word: &Token, out: &mut Out) {
    if !matches!(&*word.inner, InnerToken::T_NormalWord(_)) {
        return;
    }
    let mut parts: Vec<&Token> = Vec::new();
    parts.extend(get_word_parts(word));
    // Guard: not quote-free AND more than one part.
    if is_quote_free(params, word) || parts.len() <= 1 {
        return;
    }
    if let Some(array) = parts.iter().find(|p| is_array_expansion(p)) {
        err(
            out,
            array.id(),
            2145,
            "Argument mixes string and array. Use * or separate argument.",
        );
    }
}

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
    fn collect(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Out {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out
    }
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        !collect(f, s).is_empty()
    }

    // ---- checkUuoeCmd (SC2005), mirroring Checks/Commands.hs prop tests ----
    #[test]
    fn prop_checkUuoeCmd1() {
        assert!(emits(check_uuoe_cmd, "echo $(date)"));
    }
    #[test]
    fn prop_checkUuoeCmd2() {
        assert!(emits(check_uuoe_cmd, "echo `date`"));
    }
    #[test]
    fn prop_checkUuoeCmd3() {
        assert!(emits(check_uuoe_cmd, "echo \"$(date)\""));
    }
    #[test]
    fn prop_checkUuoeCmd4() {
        assert!(emits(check_uuoe_cmd, "echo \"`date`\""));
    }
    #[test]
    fn prop_checkUuoeCmd5() {
        assert!(!emits(check_uuoe_cmd, "echo \"The time is $(date)\""));
    }
    #[test]
    fn prop_checkUuoeCmd6() {
        assert!(!emits(check_uuoe_cmd, "echo \"$(<file)\""));
    }

    // Regression guards for FIX B1: SC2005 must fire even when the `echo $(cmd)`
    // is itself nested inside a command substitution (the old command-sub
    // suppression guard was removed since inner spans are now correct).
    #[test]
    fn prop_checkUuoeCmd_nested_dollar_expansion() {
        assert!(emits(check_uuoe_cmd, "foo $(echo $(bar))"));
    }
    #[test]
    fn prop_checkUuoeCmd_nested_backtick() {
        assert!(emits(check_uuoe_cmd, "foo=`echo \\`expr 3+2\\``"));
    }
}
