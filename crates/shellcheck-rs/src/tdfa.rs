//! regex-tdfa's `makeRegex` with its default options, for a pattern built at
//! run time: `parseRegex` from `Text.Regex.TDFA.ReadRegex`, emitting the same
//! pattern in the syntax of the `regex` crate.
//!
//! The default `CompOption` is `multiline` and `newSyntax`: `^` and `$` match
//! at line breaks, `.` and a negated bracket never match a newline, and
//! `` \` ``, `\'`, `\<`, `\>`, `\b` and `\B` are anchors.

use regex::Regex;
use std::fmt::Write;

/// `makeRegex`: the pattern, or the message regex-tdfa dies with.
///
/// # Errors
///
/// When `parseRegex` rejects the pattern.
pub fn make_regex(pattern: &str) -> Result<Regex, String> {
    let mut parser = Parser {
        chars: pattern.chars().collect(),
        pos: 0,
    };
    let body = parser.regex()?;
    if let Some(c) = parser.peek() {
        return Err(format!("unexpected {c:?} at column {}", parser.pos + 1));
    }
    Regex::new(&format!("(?m){body}")).map_err(|e| e.to_string())
}

/// `decodeCharacterClass`: the characters of a `[:name:]` class, as ranges. An
/// unknown name is empty.
fn character_class(name: &str) -> &'static [(char, char)] {
    match name {
        "alnum" => &[('0', '9'), ('A', 'Z'), ('a', 'z')],
        "digit" => &[('0', '9')],
        "punct" => &[('!', '/'), (':', '@'), ('[', '`'), ('{', '~')],
        "alpha" => &[('A', 'Z'), ('a', 'z')],
        "graph" => &[('!', '~')],
        "space" => &[('\t', '\r'), (' ', ' ')],
        "blank" => &[('\t', '\t'), (' ', ' ')],
        "lower" => &[('a', 'z')],
        "upper" => &[('A', 'Z')],
        "cntrl" => &[('\0', '\u{1f}'), ('\u{7f}', '\u{7f}')],
        "print" => &[(' ', '~')],
        "xdigit" => &[('0', '9'), ('A', 'F'), ('a', 'f')],
        "word" => &[('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')],
        _ => &[],
    }
}

/// A cursor over the pattern. Every method mirrors the Parsec parser of the
/// same name, and fails without moving the cursor wherever that parser fails
/// without consuming input.
struct Parser {
    chars: Vec<char>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<char> {
        self.chars.get(self.pos + offset).copied()
    }

    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn unexpected<T>(&self) -> Result<T, String> {
        Err(self.peek().map_or_else(
            || "unexpected end of input".to_string(),
            |c| format!("unexpected {c:?} at column {}", self.pos + 1),
        ))
    }

    /// `p_regex = POr <$> sepBy1 p_branch (char '|')`.
    fn regex(&mut self) -> Result<String, String> {
        let mut out = self.branch()?;
        while self.eat('|') {
            out.push('|');
            out.push_str(&self.branch()?);
        }
        Ok(out)
    }

    /// `p_branch = PConcat <$> many1 p_piece`.
    fn branch(&mut self) -> Result<String, String> {
        let Some(first) = self.piece()? else {
            return self.unexpected();
        };
        let mut out = first;
        while let Some(piece) = self.piece()? {
            out.push_str(&piece);
        }
        Ok(out)
    }

    /// `p_piece = (p_anchor <|> p_atom) >>= p_post_atom`, or `None` when no
    /// piece starts here.
    fn piece(&mut self) -> Result<Option<String>, String> {
        let atom = match self.anchor() {
            Some(anchor) => anchor,
            None => match self.atom()? {
                Some(atom) => atom,
                None => return Ok(None),
            },
        };
        Ok(Some(atom + &self.post_atom()))
    }

    /// `p_anchor`: `^`, `$`, or the empty group `()`.
    fn anchor(&mut self) -> Option<String> {
        if self.eat('^') {
            Some("^".to_string())
        } else if self.eat('$') {
            Some("$".to_string())
        } else if self.peek() == Some('(') && self.peek_at(1) == Some(')') {
            self.pos += 2;
            Some("()".to_string())
        } else {
            None
        }
    }

    /// `p_atom = p_group <|> p_bracket <|> p_char`.
    fn atom(&mut self) -> Result<Option<String>, String> {
        if self.eat('(') {
            let inner = self.regex()?;
            if !self.eat(')') {
                return self.unexpected();
            }
            return Ok(Some(format!("({inner})")));
        }
        if self.eat('[') {
            return self.bracket().map(Some);
        }
        Ok(self.char_atom())
    }

    /// `p_post_atom`: at most one of `?`, `+`, `*` or a bound.
    fn post_atom(&mut self) -> String {
        for op in ['?', '+', '*'] {
            if self.eat(op) {
                return op.to_string();
            }
        }
        self.bound().unwrap_or_default()
    }

    /// `p_bound = try (between (char '{') (char '}') p_bound_spec)`: `{m}`,
    /// `{m,}` or `{m,n}` with `m <= n`.
    fn bound(&mut self) -> Option<String> {
        let start = self.pos;
        let spec = self.bound_spec();
        if spec.is_none() {
            self.pos = start;
        }
        spec
    }

    fn bound_spec(&mut self) -> Option<String> {
        if !self.eat('{') {
            return None;
        }
        let low = self.digits()?;
        let mut out = format!("{{{low}");
        let comma = self.pos;
        if self.eat(',') {
            match self.digits() {
                None => out.push(','),
                Some(high) if parse_count(&low) <= parse_count(&high) => {
                    let _ = write!(out, ",{high}");
                }
                // `guard (lowI <= highI)` fails inside the `try`, which leaves
                // the `,` to `char '}'`.
                Some(_) => self.pos = comma,
            }
        }
        if !self.eat('}') {
            return None;
        }
        out.push('}');
        Some(out)
    }

    /// `many1 digit`.
    fn digits(&mut self) -> Option<String> {
        let start = self.pos;
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.pos += 1;
        }
        (self.pos > start).then(|| self.chars[start..self.pos].iter().collect())
    }

    /// `p_char`: `.`, a `{` that starts no bound, `\` and any character, or
    /// any character but `^.[$()|*+?{\`.
    fn char_atom(&mut self) -> Option<String> {
        let c = self.peek()?;
        match c {
            '.' => {
                self.pos += 1;
                Some(".".to_string())
            }
            '{' if !self.peek_at(1).is_some_and(|d| d.is_ascii_digit()) => {
                self.pos += 1;
                Some(regex::escape("{"))
            }
            '\\' => {
                let escaped = self.peek_at(1)?;
                self.pos += 2;
                Some(match escaped {
                    '`' => r"\A".to_string(),
                    '\'' => r"\z".to_string(),
                    '<' => r"\b{start}".to_string(),
                    '>' => r"\b{end}".to_string(),
                    'b' => r"\b".to_string(),
                    'B' => r"\B".to_string(),
                    other => regex::escape(&other.to_string()),
                })
            }
            _ if "^.[$()|*+?{\\".contains(c) => None,
            _ => {
                self.pos += 1;
                Some(regex::escape(&c.to_string()))
            }
        }
    }

    /// `p_bracket` after its `[`: `p_set`, as a class of the `regex` crate.
    fn bracket(&mut self) -> Result<String, String> {
        let negated = self.eat('^');
        let mut ranges: Vec<(char, char)> = Vec::new();
        // `option "" (char ']' >> return "]")`, then `many1 p_set_elem`
        // unless that `]` was there.
        let initial = self.eat(']');
        if initial {
            ranges.push((']', ']'));
        }
        let mut elements = 0;
        while self.set_element(&mut ranges)? {
            elements += 1;
        }
        if (!initial && elements == 0) || !self.eat(']') {
            return self.unexpected();
        }
        let mut class = String::from(if negated { "[^" } else { "[" });
        for (start, end) in &ranges {
            let _ = write!(
                class,
                "\\x{{{:X}}}-\\x{{{:X}}}",
                u32::from(*start),
                u32::from(*end)
            );
        }
        if negated {
            class.push_str("\\n");
        } else if ranges.is_empty() {
            // A set of nothing: a class the `regex` crate accepts that no
            // character is in.
            class.push_str("a&&b");
        }
        class.push(']');
        Ok(class)
    }

    /// `p_set_elem`: the ranges of one element, or `false` where none starts.
    fn set_element(&mut self, ranges: &mut Vec<(char, char)>) -> Result<bool, String> {
        if let Some(name) = self.delimited(':') {
            ranges.extend_from_slice(character_class(&name));
            return Ok(true);
        }
        if let Some(chars) = self.delimited('=') {
            ranges.extend(chars.chars().map(|c| (c, c)));
            return Ok(true);
        }
        // `decodePatternSet` ignores collating elements.
        if self.delimited('.').is_some() {
            return Ok(true);
        }
        let Some(start) = self.peek().filter(|&c| c != ']') else {
            return Ok(false);
        };
        if self.peek_at(1) == Some('-')
            && let Some(end) = self.peek_at(2).filter(|&c| c != ']')
        {
            // `checkBracketElement`, outside the `try`: fatal.
            if start > end {
                return Err(format!(
                    "End point {end:?} of dashed character range is less than starting point {start:?}"
                ));
            }
            self.pos += 3;
            ranges.push((start, end));
            return Ok(true);
        }
        self.pos += 1;
        ranges.push((start, start));
        Ok(true)
    }

    /// `try (between (string "[x") (string "x]") (many1 (noneOf "x]")))`.
    fn delimited(&mut self, x: char) -> Option<String> {
        if self.peek() != Some('[') || self.peek_at(1) != Some(x) {
            return None;
        }
        let mut end = self.pos + 2;
        while self.chars.get(end).is_some_and(|&c| c != x && c != ']') {
            end += 1;
        }
        let body: String = self.chars[self.pos + 2..end].iter().collect();
        if body.is_empty()
            || self.chars.get(end) != Some(&x)
            || self.chars.get(end + 1) != Some(&']')
        {
            return None;
        }
        self.pos = end + 2;
        Some(body)
    }
}

/// A bound's digits as `read` would take them, saturating where an `Int`
/// would wrap.
fn parse_count(digits: &str) -> u64 {
    digits.parse().unwrap_or(u64::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matches(pattern: &str, text: &str) -> Result<bool, String> {
        Ok(make_regex(pattern)?.is_match(text))
    }

    #[test]
    fn a_bracket_takes_bracket_and_set_operators_literally() {
        assert_eq!(matches("^[a[b]$", "["), Ok(true));
        assert_eq!(matches("^[a&&b]$", "&"), Ok(true));
        assert_eq!(matches("^[a~~b]$", "~"), Ok(true));
        assert_eq!(matches("^[a-]$", "-"), Ok(true));
        assert_eq!(matches("^[]a]$", "]"), Ok(true));
        assert_eq!(matches("^[--/]$", "."), Ok(true));
    }

    #[test]
    fn a_bracket_that_regex_tdfa_rejects_is_an_error() {
        assert!(make_regex("[z-a]").is_err());
        assert!(make_regex("[a--b]").is_err());
        assert!(make_regex("[]").is_err());
        assert!(make_regex("[^]").is_err());
        assert!(make_regex("[a").is_err());
    }

    #[test]
    fn character_classes_follow_decode_character_class() {
        assert_eq!(matches("^[[:alpha:]]$", "q"), Ok(true));
        assert_eq!(matches("^[[:alpha:]]$", "\u{e9}"), Ok(false));
        assert_eq!(matches("^[[:nope:]]$", "n"), Ok(false));
        assert_eq!(matches("^[[=x=]]$", "x"), Ok(true));
        assert_eq!(matches("^[[.x.]]$", "x"), Ok(false));
        assert_eq!(matches("^[[:ascii:]]$", "a"), Ok(false));
    }

    #[test]
    fn a_negated_bracket_and_a_dot_never_match_a_newline() {
        assert_eq!(matches("^[^a]$", "\n"), Ok(false));
        assert_eq!(matches("^[^a]$", "b"), Ok(true));
        assert_eq!(matches("^.$", "\n"), Ok(false));
    }

    #[test]
    fn outside_a_bracket_the_syntax_is_posix() {
        assert_eq!(matches("^a{2}$", "aa"), Ok(true));
        assert_eq!(matches("^a{$", "a{"), Ok(true));
        assert_eq!(matches("^a}$", "a}"), Ok(true));
        assert_eq!(matches("^a]$", "a]"), Ok(true));
        assert_eq!(matches("^(a|b)?c$", "c"), Ok(true));
        assert_eq!(matches(r"^\.$", "."), Ok(true));
        assert_eq!(matches("^()a$", "a"), Ok(true));
        assert!(make_regex("a**").is_err());
        assert!(make_regex("(a").is_err());
        assert!(make_regex("a|").is_err());
    }
}
