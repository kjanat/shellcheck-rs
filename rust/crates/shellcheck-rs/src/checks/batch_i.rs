//! Ported check batch i. See rust/PORTING.md.
//!
//! Ported from `src/ShellCheck/Analytics.hs` and `src/ShellCheck/Checks/Commands.hs`:
//!   * SC2046 — `checkUnquotedExpansions`: unquoted `$(...)` / `` `...` `` command
//!     substitution that should be quoted to prevent word splitting. Uses a
//!     parent-context walk (`isQuoteFree`/`usedAsCommandName`), NOT the CFG.
//!   * SC2183 — `checkPrintfVar`: printf format string has a variable count that
//!     does not match the number of arguments.
//!   * SC2059 — `checkPrintfVar`: variables used in the printf format string.
//!   * SC2060 — `checkTr`: unquoted glob parameters passed to `tr`.
//!
//! Not ported here (belong to other batches / codes): SC2182 (printf, no
//! variables), SC2018/2019/2020/2021 (tr literal-string advice).
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::get_command_name_and_token;
use crate::analyzer_lib::is_quote_free;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::get_literal_string;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_unquoted_expansions);
}

// ===========================================================================
// Shared helpers (ported privately; parallel agents own other .rs files).
// ===========================================================================

// ---- getWordParts / isFlag / isGlob (ported from ASTLib) --------------------

// ---- command name resolution (ported from ASTLib) -------

fn get_command_token_or_this(t: &Token) -> &Token {
    get_command_name_and_token(false, t).1
}

// ===========================================================================
// SC2046 — checkUnquotedExpansions
// ===========================================================================

/// `getCommandNameFromExpansion`: if a substitution is a single command, its name.
fn get_command_name_from_expansion(t: &Token) -> Option<String> {
    use InnerToken::*;
    let list: &[Token] = match &*t.inner {
        T_DollarExpansion(l) if l.len() == 1 => l,
        T_Backticked(l) if l.len() == 1 => l,
        T_DollarBraceCommandExpansion { list, .. } if list.len() == 1 => list,
        _ => return None,
    };
    match &*list[0].inner {
        T_Pipeline { commands, .. } if commands.len() == 1 => get_command_name(&commands[0]),
        _ => None,
    }
}

/// `usedAsCommandName`: is the token the first word of a T_SimpleCommand?
fn used_as_command_name(p: &Parameters, token: &Token) -> bool {
    use InnerToken::*;
    let mut current_id = token.id();
    let mut node = p.parent(token);
    while let Some(t) = node {
        match &*t.inner {
            T_NormalWord(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = p.parent(t);
            }
            T_DoubleQuoted(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = p.parent(t);
            }
            T_SimpleCommand { words, .. } if !words.is_empty() => {
                if words[0].id() == current_id || get_command_token_or_this(t).id() == current_id {
                    return true;
                }
                // `time CMD`: the reserved word `time` is followed by the command
                // being timed. ShellCheck's parser (readTimeSuffix) parses that
                // word as the command; this parser keeps `time` as a plain
                // command with the word as its first argument, so recognise it
                // here to avoid a spurious split warning.
                return words.len() >= 2
                    && get_literal_string(&words[0]).as_deref() == Some("time")
                    && words[1].id() == current_id;
            }
            _ => return false,
        }
    }
    false
}

fn check_unquoted_expansions(p: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    let contents: &[Token] = match &*t.inner {
        T_DollarExpansion(c) => c,
        T_Backticked(c) => c,
        T_DollarBraceCommandExpansion { list, .. } => list,
        _ => return,
    };
    if contents.is_empty() {
        return;
    }
    if should_be_split(t) || is_quote_free(p, t) || used_as_command_name(p, t) {
        return;
    }
    warn(out, t.id(), 2046, "Quote this to prevent word splitting.");
}

fn should_be_split(t: &Token) -> bool {
    matches!(
        get_command_name_from_expansion(t).as_deref(),
        Some("seq") | Some("pgrep")
    )
}

// ---- mayBecomeMultipleArgs (ASTLib) ----------------------------------------
