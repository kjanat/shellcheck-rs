//! Command dispatch and helpers shared by the `commands` modules.
use crate::analyzer_lib::*;

use crate::ast::*;
use crate::astlib;
use crate::astlib::basename;
use crate::astlib::{get_literal_string, only_literal_string};

#[derive(Clone, Copy, PartialEq)]
pub(super) enum CmdKind {
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
pub(super) fn matched_words<'a>(t: &'a Token, kind: CmdKind, target: &str) -> Option<&'a [Token]> {
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
pub(super) fn word_args(words: &[Token]) -> &[Token] {
    &words[1..]
}

pub(super) fn word_flags(words: &[Token]) -> Vec<(&Token, String)> {
    get_flags_until_args(&|x| x == "--", word_args(words))
}

/// Effective command token if a check registered under `Basename target` would
/// fire on `t`, per `checkCommand`.
pub(super) fn dispatch_basename(t: &Token, target: &str) -> Option<Token> {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return None,
    };
    let name = astlib::get_literal_string(&words[0])?;
    if name.contains('/') {
        return if basename(&name) == target {
            Some(t.clone())
        } else {
            None
        };
    }
    if name == "builtin" && words.len() >= 2 {
        return None; // builtin branch: no Basename dispatch
    }
    if name == target {
        Some(t.clone())
    } else {
        None
    }
}
