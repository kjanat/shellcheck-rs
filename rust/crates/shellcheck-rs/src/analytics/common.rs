//! Helpers shared by more than one `analytics` module.
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::interface::Fix;

/// `surroundWith`.
pub(super) fn surround_with(params: &Parameters, id: Id, s: &str) -> Fix {
    fix_with(vec![
        replace_start(params, id, 0, s),
        replace_end(params, id, 0, s),
    ])
}

/// `getCommand`.
pub(super) fn get_command_local(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command_local(cmd),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        InnerToken::T_Annotation { token, .. } => get_command_local(token),
        _ => None,
    }
}
