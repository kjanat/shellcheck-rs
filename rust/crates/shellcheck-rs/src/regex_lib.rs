//! Port of `ShellCheck.Regex`.

use regex::Regex;

/// `mkRegex`: compile a pattern written in the source.
///
/// # Panics
///
/// When the pattern is invalid, as `mkRegex` errors.
#[must_use]
pub fn mk_regex(pattern: &str) -> Regex {
    match Regex::new(pattern) {
        Ok(re) => re,
        Err(e) => panic!("mkRegex {pattern:?}: {e}"),
    }
}
