//! Ported check batch b. See rust/PORTING.md.
//!
//! Ported checks:
//! - SC2005  checkUuoeCmd            (Checks/Commands.hs) — useless `echo $(cmd)`
//! - SC2116  checkUuoeVar            (Analytics.hs)       — useless `cmd $(echo foo)`
//! - SC2027  checkInexplicablyUnquoted (Analytics.hs, 2027 branch only)
//! - SC2145  checkConcatenatedDollarAt (Analytics.hs)
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
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

/// `getLiteralStringDef ""` a.k.a. `onlyLiteralString`: literal string,
/// substituting "" for any non-literal part.
fn only_literal_string(t: &Token) -> String {
    astlib::get_literal_string_ext(t, &|_| Some(String::new())).unwrap_or_default()
}

/// `isOnlyRedirection` (ASTLib).
fn is_only_redirection(t: &Token) -> bool {
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

/// `getWordParts` (ASTLib), collected as references.
fn get_word_parts<'a>(t: &'a Token, out: &mut Vec<&'a Token>) {
    match &*t.inner {
        InnerToken::T_NormalWord(l) | InnerToken::TA_Expansion(l) => {
            for x in l {
                get_word_parts(x, out);
            }
        }
        InnerToken::T_DoubleQuoted(l) => {
            for x in l {
                out.push(x);
            }
        }
        _ => out.push(t),
    }
}

/// `isArrayExpansion` (ASTLib).
fn is_array_expansion(t: &Token) -> bool {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        let string: String = astlib::oversimplify(op).concat();
        string.starts_with('@') || (!string.starts_with('#') && string.contains("[@]"))
    } else {
        false
    }
}

// ---- isQuoteFree (AnalyzerLib.isQuoteFreeNode strict=False) ----------------

/// Whether the assignment token `id`'s parent is a declaration-utility command
/// (so the assignment is passed as an argument, e.g. `export FOO=bar`).
fn is_assignment_param_to_command(params: &Parameters, id: Id) -> bool {
    let parent = match params
        .parent_map
        .get(&id)
        .and_then(|pid| params.id_map.get(pid))
    {
        Some(p) => p,
        None => return false,
    };
    if let InnerToken::T_SimpleCommand { words, .. } = &*parent.inner {
        if let Some((_, args)) = words.split_first() {
            return args.iter().any(|a| a.id() == id);
        }
    }
    false
}

fn assignment_is_quoting(params: &Parameters, id: Id) -> bool {
    let shell_parses_params_as_assignments = params.shell != Shell::Sh;
    shell_parses_params_as_assignments || !is_assignment_param_to_command(params, id)
}

/// `isQuoteFreeElement`: is this node self-quoting in itself?
fn is_quote_free_element(params: &Parameters, t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Assignment { .. } => assignment_is_quoting(params, t.id()),
        InnerToken::T_FdRedirect { .. } => true,
        _ => false,
    }
}

/// `isQuoteFreeContext` (with strict = False for the non-strict `isQuoteFree`).
fn is_quote_free_context(params: &Parameters, t: &Token) -> Option<bool> {
    use ConditionType::DoubleBracket;
    match &*t.inner {
        InnerToken::TC_Nullary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TC_Unary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TC_Binary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TA_Sequence(_) => Some(true),
        InnerToken::T_Arithmetic(_) => Some(true),
        InnerToken::T_Assignment { .. } => Some(assignment_is_quoting(params, t.id())),
        InnerToken::T_Redirecting { .. } => Some(false),
        InnerToken::T_DoubleQuoted(_) => Some(true),
        InnerToken::T_DollarDoubleQuoted(_) => Some(true),
        InnerToken::T_CaseExpression { .. } => Some(true),
        InnerToken::T_HereDoc { .. } => Some(true),
        InnerToken::T_DollarBraced { .. } => Some(true),
        // strict = False: pragmatically assume splitting is desirable here.
        InnerToken::T_ForIn { .. } => Some(true),
        InnerToken::T_SelectIn { .. } => Some(true),
        _ => None,
    }
}

/// `isQuoteFree` (non-strict).
fn is_quote_free(params: &Parameters, t: &Token) -> bool {
    if is_quote_free_element(params, t) {
        return true;
    }
    // msum over `NE.tail (getPath tree t)` = ancestors from nearest to root;
    // first `Just` wins.
    let mut cur = t;
    while let Some(p) = params.parent(cur) {
        if let Some(v) = is_quote_free_context(params, p) {
            return v;
        }
        cur = p;
    }
    false
}

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
    get_word_parts(word, &mut parts);
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
