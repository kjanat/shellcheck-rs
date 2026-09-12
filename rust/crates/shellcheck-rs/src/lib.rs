//! # shellcheck-rs (core)
//!
//! A structural Rust port of [ShellCheck](https://www.shellcheck.net). This
//! crate is the reusable, IO-free analysis core: it parses a shell script into
//! an AST, runs the analyzer/checks, and returns structured diagnostics with
//! source spans and autofixes. It is intended to be embedded directly (e.g. by
//! a language server); the CLI and text formatters live in a separate crate.
//!
//! Module layout mirrors the Haskell `ShellCheck.*` hierarchy so the port can
//! be verified module-by-module against the original.
//!
//! Pipeline (see [`checker`]):
//! 1. [`parser`] : source -> AST + id/position map + SC1xxx parse comments
//! 2. [`analyzer_lib`] + [`analytics`] / [`checks`] : AST -> `TokenComment`s
//!    (SC2xxx from `Analytics`, per-command checks from `Checks.Commands`,
//!    dialect checks from `Checks.ShellSupport`)
//! 3. [`checker`] : resolve ids to positions, filter, dedup, sort
//!
//! The three check shapes are [`analyzer_lib::Check`] (a plain function or
//! closure), `checks::commands::CommandCheck` (Haskell's `CommandCheck name f`)
//! and `checks::shell_support::ForShell` (`ForShell shells f`).

// The port deliberately keeps ShellCheck's Haskell constructor names
// (`T_Literal`, `TC_Binary`, `TA_Unary`, ...) for structural fidelity and
// cross-referencing against the original source.
#![allow(non_camel_case_types)]

pub mod ast;
pub mod interface;

pub mod analytics;
pub mod analyzer_lib;
pub mod ast_lib;
pub mod cfg;
pub mod cfg_analysis;
pub mod checker;
pub mod checks;
pub mod data;
pub mod parser;
#[cfg(test)]
mod test_support;

pub use checker::check_script;

pub use interface::{
    CheckResult, CheckSpec, Code, ColorOption, Comment, ErrorMessage, ExecutionMode, Fix,
    InsertionPoint, Position, PositionedComment, Replacement, Severity, Shell, TokenComment,
};
