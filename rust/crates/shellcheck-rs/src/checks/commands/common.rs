//! Command dispatch and helpers shared by the `commands` modules.
use crate::analyzer_lib::get_flags_until_args;

use crate::ast::Token;

/// `arguments`: the words after the command name.
pub(super) fn word_args(words: &[Token]) -> &[Token] {
    &words[1..]
}

pub(super) fn word_flags(words: &[Token]) -> Vec<(&Token, String)> {
    get_flags_until_args(&|x| x == "--", word_args(words))
}
