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

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    /// Every Rust source file under `dir`.
    fn sources(dir: &Path, out: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                sources(&path, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(std::fs::read_to_string(&path).unwrap());
            }
        }
    }

    /// Every pattern the crate passes to `mk_regex` is a raw string literal
    /// that compiles, so a bad one fails the build before it can panic.
    #[test]
    fn every_static_pattern_compiles() {
        let mut files = Vec::new();
        sources(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
            &mut files,
        );
        let literal = Regex::new(r#"mk_regex\(r"([^"]*)"\)"#).unwrap();
        let mut calls = 0;
        let mut patterns = Vec::new();
        for text in &files {
            calls += text.matches("mk_regex(").count();
            patterns.extend(literal.captures_iter(text).map(|c| c[1].to_string()));
        }
        // The definition and this test's own needle are the only other uses.
        assert_eq!(
            calls,
            patterns.len() + 2,
            "a call that is not a raw literal"
        );
        assert_ne!(patterns, Vec::<String>::new());
        for pattern in &patterns {
            assert!(Regex::new(pattern).is_ok(), "{pattern:?} does not compile");
        }
    }
}
