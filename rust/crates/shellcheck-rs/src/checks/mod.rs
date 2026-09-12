//! The non-Analytics checkers: `ShellCheck.Checks.Commands` and
//! `ShellCheck.Checks.ShellSupport` (`ShellCheck.Checks.ControlFlow` is an
//! empty scaffold in Haskell and has no counterpart here).
use crate::analyzer_lib::Checker;
pub mod commands;
pub mod shell_support;

pub fn register_all(c: &mut Checker) {
    commands::register(c);
    shell_support::register(c);
}
