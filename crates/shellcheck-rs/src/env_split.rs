//! Decode the static subset of GNU `env -S` argument syntax for shebangs.
//!
//! See <https://www.gnu.org/software/coreutils/manual/html_node/env-invocation.html>.
//! Environment expansion is deliberately unknown: checking a script must not
//! depend on the environment of the process running the checker.

#[derive(Clone, Copy, PartialEq, Eq)]
enum Quote {
    Unquoted,
    Single,
    Double,
}

/// Split a literal `env -S` payload, preserving empty quoted arguments.
///
/// Return `None` for dynamic expansions or malformed input. The caller must
/// retain the floor diagnostics when the interpreter arguments are unknown.
pub fn split(input: &str) -> Option<Vec<String>> {
    decode(input).ok()
}

/// The complete static arguments before any unknown or malformed argument.
///
/// A literal interpreter can still be identified when its later arguments
/// depend on the environment. Never return a partially decoded argument.
pub fn split_prefix(input: &str) -> Vec<String> {
    decode(input).unwrap_or_else(std::convert::identity)
}

fn decode(input: &str) -> Result<Vec<String>, Vec<String>> {
    let mut words = Vec::new();
    // None means the next character starts a token; Some("") is an empty token.
    let mut word: Option<String> = None;
    let mut quote = Quote::Unquoted;
    let mut chars = input.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            '\'' if quote != Quote::Double => {
                quote = if quote == Quote::Single {
                    Quote::Unquoted
                } else {
                    Quote::Single
                };
                word.get_or_insert_default();
            }
            '"' if quote != Quote::Single => {
                quote = if quote == Quote::Double {
                    Quote::Unquoted
                } else {
                    Quote::Double
                };
                word.get_or_insert_default();
            }
            ' ' | '\t' | '\n' | '\r' | '\u{b}' | '\u{c}' if quote == Quote::Unquoted => {
                if let Some(word) = word.take() {
                    words.push(word);
                }
            }
            '#' if word.is_none() => break,
            '$' if quote != Quote::Single => return Err(words),
            '\\' => {
                if quote == Quote::Single && !matches!(chars.peek(), Some('\\' | '\'')) {
                    word.get_or_insert_default().push(ch);
                    continue;
                }
                let Some(escaped) = chars.next() else {
                    return Err(words);
                };
                match escaped {
                    '_' if quote == Quote::Unquoted => {
                        if let Some(word) = word.take() {
                            words.push(word);
                        }
                    }
                    'c' if quote == Quote::Unquoted => break,
                    _ => {
                        let Some(decoded) = decode_escape(escaped) else {
                            return Err(words);
                        };
                        word.get_or_insert_default().push(decoded);
                    }
                }
            }
            _ => word.get_or_insert_default().push(ch),
        }
    }
    if quote != Quote::Unquoted {
        return Err(words);
    }
    if let Some(word) = word {
        words.push(word);
    }
    Ok(words)
}

const fn decode_escape(ch: char) -> Option<char> {
    match ch {
        '\\' | '\'' | '"' | '#' | '$' => Some(ch),
        '_' => Some(' '),
        'f' => Some('\u{c}'),
        'n' => Some('\n'),
        'r' => Some('\r'),
        't' => Some('\t'),
        'v' => Some('\u{b}'),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{split, split_prefix};

    fn assert_words(input: &str, expected: &[&str]) {
        assert_eq!(
            split(input),
            Some(expected.iter().map(|word| (*word).to_owned()).collect()),
            "{input:?}"
        );
    }

    #[test]
    fn quotes_join_segments_and_preserve_empty_arguments() {
        assert_words(
            r#"zsh '-y' "-o" sh'word'"split" '' "" a''b"#,
            &["zsh", "-y", "-o", "shwordsplit", "", "", "ab"],
        );
        assert_words(r#"'a"b' "c'd""#, &["a\"b", "c'd"]);
        assert_words(r#"zsh " a b ""#, &["zsh", " a b "]);
    }

    #[test]
    fn only_ascii_whitespace_separates_arguments() {
        assert_words(" \t\nzsh\r\u{b}\u{c}-y ", &["zsh", "-y"]);
        assert_words("a\u{a0}b", &["a\u{a0}b"]);
        assert_words("", &[]);
        assert_words(" \t\r\n", &[]);
    }

    #[test]
    fn escapes_decode_without_splitting_their_result() {
        for (escape, decoded) in [
            (r"\\", '\\'),
            (r"\'", '\''),
            (r#"\""#, '"'),
            (r"\#", '#'),
            (r"\$", '$'),
            (r"\f", '\u{c}'),
            (r"\n", '\n'),
            (r"\r", '\r'),
            (r"\t", '\t'),
            (r"\v", '\u{b}'),
        ] {
            let expected = format!("a{decoded}b");
            assert_words(&format!("a{escape}b"), &[&expected]);
            assert_words(&format!("\"a{escape}b\""), &[&expected]);
        }
    }

    #[test]
    fn single_quotes_only_decode_backslash_and_apostrophe() {
        assert_words(r"'a\'b\\c\_\c\n\$\#\q'", &["a'b\\c\\_\\c\\n\\$\\#\\q"]);
        assert_words("'${FLAGS}' '$'", &["${FLAGS}", "$"]);
    }

    #[test]
    fn underscore_escape_depends_on_quote_state() {
        assert_words(r"\_zsh\_\_-y\_", &["zsh", "-y"]);
        assert_words(r#""a\_b" ''\_"""#, &["a b", "", ""]);
        assert_words(r"'a\_b'", &[r"a\_b"]);
    }

    #[test]
    fn comments_require_a_fresh_token() {
        assert_words("zsh # '-y' ${FLAGS}", &["zsh"]);
        assert_words("# anything", &[]);
        assert_words(r##"a#b "#" '#' ''# \#"##, &["a#b", "#", "#", "#", "#"]);
        assert_words(r"zsh\_# -y", &["zsh"]);
    }

    #[test]
    fn stop_escape_discards_the_remainder_only_when_unquoted() {
        assert_words(r"zsh\c '-y' ${FLAGS}", &["zsh"]);
        assert_words(r"zsh \c '-y'", &["zsh"]);
        assert_words(r"\c", &[]);
        assert_words(r"zsh ''\c", &["zsh", ""]);
        assert_words(r"'\c'", &[r"\c"]);
        assert_eq!(split(r#""\c""#), None);
    }

    #[test]
    fn dynamic_or_invalid_payloads_are_unknown() {
        for input in [
            "zsh ${FLAGS}",
            "zsh \"${FLAGS}\"",
            "zsh $FLAGS",
            "zsh $",
            "zsh '${FLAGS}",
            "zsh \"-y",
            "zsh \\",
            r"zsh \q",
            r"zsh \ ",
        ] {
            assert_eq!(split(input), None, "{input:?}");
        }
        assert_words(r"zsh \${FLAGS}", &["zsh", "${FLAGS}"]);
    }

    #[test]
    fn a_static_prefix_never_contains_a_partial_argument() {
        for input in ["'zsh' ${FLAGS}", "'zsh' -${FLAG}", "'zsh' '\\", "'zsh' \\"] {
            assert_eq!(split_prefix(input), vec!["zsh"], "{input:?}");
            assert_eq!(split(input), None, "{input:?}");
        }
        for input in ["z${SHELL}", "'zsh", "zsh\\q"] {
            assert!(split_prefix(input).is_empty(), "{input:?}");
        }
        assert_eq!(split_prefix("'zsh' '-y'"), vec!["zsh", "-y"]);
    }
}
