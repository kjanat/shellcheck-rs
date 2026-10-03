//! Port of `ShellCheck.Regex`.

use regex::Regex;

/// `mkRegex`: compile a pattern written in the source, with regex-tdfa's
/// syntax and default options (see [`crate::tdfa`]).
///
/// # Panics
///
/// When the pattern is invalid, as `mkRegex` errors.
#[must_use]
pub fn mk_regex(pattern: &str) -> Regex {
    match crate::tdfa::make_regex(pattern) {
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

    /// The value of a plain string literal's body.
    fn unescape(body: &str) -> String {
        let mut out = String::new();
        let mut chars = body.chars();
        while let Some(c) = chars.next() {
            if c != '\\' {
                out.push(c);
                continue;
            }
            match chars.next() {
                Some('x') => {
                    let hex: String = chars.by_ref().take(2).collect();
                    let code = u32::from_str_radix(&hex, 16).unwrap();
                    out.push(char::from_u32(code).unwrap());
                }
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some(other) => out.push(other),
                None => {}
            }
        }
        out
    }

    /// Every pattern the crate passes to `mk_regex` is a string literal that
    /// regex-tdfa accepts, so a bad one fails the build before it can panic.
    #[test]
    fn every_static_pattern_compiles() {
        let mut files = Vec::new();
        sources(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
            &mut files,
        );
        let raw = Regex::new(r#"mk_regex\(r"([^"]*)"\)"#).unwrap();
        let plain = Regex::new(r#"mk_regex\("((?:[^"\\]|\\.)*)"\)"#).unwrap();
        let mut calls = 0;
        let mut patterns = Vec::new();
        for text in &files {
            calls += text.matches("mk_regex(").count();
            patterns.extend(raw.captures_iter(text).map(|c| c[1].to_string()));
            patterns.extend(plain.captures_iter(text).map(|c| unescape(&c[1])));
        }
        // The definition and the count above are the only other uses.
        assert_eq!(calls, patterns.len() + 2, "a call that is not a literal");
        assert_ne!(patterns, Vec::<String>::new());
        for pattern in &patterns {
            assert!(
                crate::tdfa::make_regex(pattern).is_ok(),
                "{pattern:?} does not compile"
            );
        }
    }
}
