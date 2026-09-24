//! The conformance corpus, derived directly from ShellCheck's own test suite.
//!
//! Every check in `src/ShellCheck/**/*.hs` carries `prop_` properties holding
//! the exact shell snippets its author considered decisive:
//!
//! ```haskell
//! prop_checkEchoWc3   = verify      checkEchoWc  "n=$(echo $foo | wc -c)"
//! prop_checkSudoArgs1 = verify     (checkSudoArgs "sudo") "sudo cd /root"
//! prop_checkEqualsInCommand1a = verifyCodes checkEqualsInCommand [2277] "#!/bin/bash\n0='foo'"
//! prop_checkFunctionsUsedExternally1 =
//!     verifyTree checkFunctionsUsedExternally "foo() { :; }; sudo foo"
//! ```
//!
//! Those snippets *are* the corpus: this module reads the Haskell sources and
//! extracts them, rather than depending on a generated JSON file that can drift
//! away from the sources it was generated from. The only input is the Haskell
//! tree that is already in this repository.
//!
//! The extraction is a small Haskell-string-literal lexer: the script is the
//! last string literal on the (possibly continued) property line, unescaped
//! per the Haskell report — `\n`, `\\`, `\"`, `\x41`, `\o17`, `\123`, ASCII
//! mnemonics like `\NUL`, and string gaps (`\   \`).

use std::path::Path;

/// One extracted property: an id, the helper that consumes it, and the script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// The Haskell property name, e.g. `prop_checkEchoWc3`.
    pub id: String,
    /// Source file the property came from, e.g. `Analytics.hs`.
    pub file: String,
    /// 1-based line the property is defined on, so a divergence can be
    /// annotated against the property that produced it.
    pub line: usize,
    /// The file's path as the repository spells it, e.g.
    /// `src/ShellCheck/Checks/Commands.hs`. [`Entry::file`] is only the base
    /// name (it is what an id is qualified with), which is not a path: three
    /// of the modules live under `Checks/`.
    pub path: String,
    /// `verify`, `verifyNot`, `verifyTree`, `verifyNotTree`, `verifyCodes`, or
    /// one of Parser.hs's `isOk`, `isWarning` and `isNotOk`.
    pub helper: String,
    /// The shell script under test, with Haskell escapes resolved.
    pub script: String,
}

const HELPERS: [&str; 8] = [
    "verifyNotTree",
    "verifyNot",
    "verifyTree",
    "verifyCodes",
    "verify",
    // Parser.hs states its properties with these instead, and they are the
    // only tests upstream has for the parser itself.
    "isNotOk",
    "isWarning",
    "isOk",
];

/// ASCII mnemonic escapes, longest first so `\SOH` wins over `\SO`.
const MNEMONICS: [(&str, char); 24] = [
    ("NUL", '\0'),
    ("SOH", '\u{1}'),
    ("STX", '\u{2}'),
    ("ETX", '\u{3}'),
    ("EOT", '\u{4}'),
    ("ENQ", '\u{5}'),
    ("ACK", '\u{6}'),
    ("BEL", '\u{7}'),
    ("BS", '\u{8}'),
    ("HT", '\u{9}'),
    ("LF", '\u{a}'),
    ("VT", '\u{b}'),
    ("FF", '\u{c}'),
    ("CR", '\u{d}'),
    ("SO", '\u{e}'),
    ("SI", '\u{f}'),
    ("DLE", '\u{10}'),
    ("ESC", '\u{1b}'),
    ("SP", ' '),
    ("DEL", '\u{7f}'),
    ("EM", '\u{19}'),
    ("SUB", '\u{1a}'),
    ("FS", '\u{1c}'),
    ("GS", '\u{1d}'),
];

/// Unescape one Haskell string literal body (the text between the quotes).
fn unescape(body: &str) -> String {
    let c: Vec<char> = body.chars().collect();
    let mut out = String::with_capacity(body.len());
    let mut i = 0;
    while i < c.len() {
        if c[i] != '\\' {
            out.push(c[i]);
            i += 1;
            continue;
        }
        i += 1;
        if i >= c.len() {
            break;
        }
        let e = c[i];
        // String gap: a backslash, whitespace, and a closing backslash, which
        // stands for nothing at all.
        if e.is_whitespace() {
            while i < c.len() && c[i].is_whitespace() {
                i += 1;
            }
            if i < c.len() && c[i] == '\\' {
                i += 1;
            }
            continue;
        }
        // `\&` is the empty string (used to break up numeric escapes).
        if e == '&' {
            i += 1;
            continue;
        }
        // Numeric escapes.
        if e == 'x' || e == 'o' || e.is_ascii_digit() {
            let (radix, start) = match e {
                'x' => (16, i + 1),
                'o' => (8, i + 1),
                _ => (10, i),
            };
            let mut j = start;
            while j < c.len() && c[j].is_digit(radix) {
                j += 1;
            }
            if j > start {
                let digits: String = c[start..j].iter().collect();
                if let Some(ch) = u32::from_str_radix(&digits, radix)
                    .ok()
                    .and_then(char::from_u32)
                {
                    out.push(ch);
                    i = j;
                    continue;
                }
            }
            // Not a valid numeric escape: fall through to the literal below.
        }
        // ASCII mnemonics.
        if e.is_ascii_uppercase() {
            let rest: String = c[i..].iter().collect();
            if let Some((name, ch)) = MNEMONICS
                .iter()
                .filter(|(n, _)| rest.starts_with(n))
                .max_by_key(|(n, _)| n.len())
            {
                out.push(*ch);
                i += name.len();
                continue;
            }
        }
        let simple = match e {
            'n' => Some('\n'),
            't' => Some('\t'),
            'r' => Some('\r'),
            'f' => Some('\u{c}'),
            'v' => Some('\u{b}'),
            'a' => Some('\u{7}'),
            'b' => Some('\u{8}'),
            '\\' => Some('\\'),
            '"' => Some('"'),
            '\'' => Some('\''),
            _ => None,
        };
        match simple {
            Some(ch) => out.push(ch),
            // Anything else: keep the backslash and the character, which is
            // what an unrecognized sequence means in practice.
            None => {
                out.push('\\');
                out.push(e);
            }
        }
        i += 1;
    }
    out
}

/// Every top-level string literal in `text`, as unescaped bodies, skipping
/// anything inside a `--` line comment.
fn string_literals(text: &str) -> Vec<String> {
    let c: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < c.len() {
        // A Haskell line comment runs to end of line.
        if c[i] == '-' && i + 1 < c.len() && c[i + 1] == '-' {
            while i < c.len() && c[i] != '\n' {
                i += 1;
            }
            continue;
        }
        // A character literal can hold a quote: '"' must not open a string.
        if c[i] == '\'' {
            let mut j = i + 1;
            let mut n = 0;
            while j < c.len() && c[j] != '\'' && n < 6 {
                if c[j] == '\\' {
                    j += 1;
                }
                j += 1;
                n += 1;
            }
            if j < c.len() && c[j] == '\'' && n > 0 {
                i = j + 1;
                continue;
            }
        }
        if c[i] != '"' {
            i += 1;
            continue;
        }
        let start = i + 1;
        let mut j = start;
        while j < c.len() {
            if c[j] == '\\' {
                j += 2;
                continue;
            }
            if c[j] == '"' {
                break;
            }
            j += 1;
        }
        if j >= c.len() {
            break; // unterminated
        }
        let body: String = c[start..j.min(c.len())].iter().collect();
        out.push(unescape(&body));
        i = j + 1;
    }
    out
}

/// Extract every property from one Haskell source file's text.
fn extract_text(file: &str, text: &str) -> Vec<Entry> {
    let lines: Vec<&str> = text.lines().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        if !line.starts_with("prop_") {
            i += 1;
            continue;
        }
        let defined_at = i + 1;
        // Haskell layout: a property may continue on following indented lines.
        let mut joined = line.to_string();
        let mut j = i + 1;
        while j < lines.len()
            && !lines[j].is_empty()
            && lines[j].starts_with(char::is_whitespace)
            && !lines[j].trim_start().starts_with("where")
        {
            joined.push(' ');
            joined.push_str(lines[j].trim_start());
            j += 1;
        }
        i = j;

        let Some(eq) = joined.find(" = ") else {
            continue;
        };
        let id = joined[..eq].trim().to_string();
        let body = &joined[eq + 3..];
        // The helper is the leading identifier of the body.
        let Some(helper) = HELPERS.iter().find(|h| {
            body.starts_with(**h) && !body[h.len()..].starts_with(|c: char| c.is_alphanumeric())
        }) else {
            continue;
        };
        // The script is the last string literal on the line: a parenthesised
        // target like `(checkSudoArgs "sudo")` contributes an earlier one.
        let Some(script) = string_literals(body).pop() else {
            continue;
        };
        out.push(Entry {
            id,
            file: file.to_string(),
            line: defined_at,
            // Filled in by `coverage`, which is the only caller that knows
            // where the file sits in the tree.
            path: String::new(),
            helper: (*helper).to_string(),
            script,
        });
    }
    out
}

/// One optional check, as its `CheckDescription` declares it: the `--enable`
/// name and the two example scripts upstream holds it to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionalExample {
    pub name: String,
    /// `cdPositive`: this must produce the check's diagnostic.
    pub positive: String,
    /// `cdNegative`: this must not.
    pub negative: String,
}

/// Read the optional-check catalog out of the Haskell sources.
///
/// These are the checks `--enable` turns on, and nothing else in the gate
/// reaches them: a property's script runs with the default check set, so an
/// optional check that does nothing at all agrees with the oracle on every
/// script in the corpus. Upstream holds them to `prop_verifyOptionalExamples`;
/// this extracts the same examples so the gate can.
pub fn optional_examples(src_dir: &Path) -> Result<Vec<OptionalExample>, String> {
    let mut out = Vec::new();
    for file in ["Analytics.hs", "Checks/Commands.hs"] {
        let path = src_dir.join(file);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let mut name: Option<String> = None;
        let mut positive: Option<String> = None;
        for line in text.lines() {
            let line = line.trim();
            let field = |key: &str| -> Option<String> {
                let rest = line.strip_prefix(key)?.trim_start();
                let rest = rest.strip_prefix('=')?;
                string_literals(rest).into_iter().next()
            };
            if let Some(s) = field("cdName") {
                name = Some(s);
                continue;
            }
            if let Some(s) = field("cdPositive") {
                positive = Some(s);
                continue;
            }
            // `cdNegative` closes the description: the three belong to one
            // check, and nothing is taken until all three are in hand.
            let Some(negative) = field("cdNegative") else {
                continue;
            };
            let (Some(name), Some(positive)) = (name.take(), positive.take()) else {
                continue;
            };
            out.push(OptionalExample {
                name,
                positive,
                negative,
            });
        }
    }
    out.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(out)
}

/// Every `prop_` name a Haskell source defines, whether or not it names a
/// script: a definition starts at the beginning of a line.
fn property_names(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("prop_")?;
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '\''))
                .unwrap_or(rest.len());
            Some(format!("prop_{}", &rest[..end]))
        })
        .collect()
}

/// What the corpus covers, and what it does not.
///
/// Not every `prop_` property names a shell script: many test the Fixer, the
/// Checker's IO, `ASTLib` helpers or the formatters, and there is nothing to
/// replay through a shell linter. Counting them here keeps the gap visible
/// rather than leaving "2026 properties" to be read as "all of them".
pub struct Coverage {
    /// Properties with a script, which is what the gate replays.
    pub entries: Vec<Entry>,
    /// Property names with no extractable script, by the file defining them.
    pub skipped: Vec<(String, String)>,
}

impl Coverage {
    /// One line for the gate and fuzz banners.
    pub fn summary(&self) -> String {
        let total = self.entries.len() + self.skipped.len();
        let mut by_file: std::collections::BTreeMap<&str, usize> =
            std::collections::BTreeMap::new();
        for (file, _) in &self.skipped {
            *by_file.entry(file.as_str()).or_default() += 1;
        }
        let mut worst: Vec<(&&str, &usize)> = by_file.iter().collect();
        worst.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        let where_ = worst
            .iter()
            .take(3)
            .map(|(f, n)| format!("{f} {n}"))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "corpus: {} of {total} properties have a script to replay; \
             {} have none ({where_}, ...)",
            self.entries.len(),
            self.skipped.len(),
        )
    }
}

/// Read every `prop_` property out of the Haskell tree rooted at `src_dir`
/// (normally `<repo>/src/ShellCheck`), sorted by id for a stable order.
pub fn extract(src_dir: &Path) -> Result<Vec<Entry>, String> {
    Ok(coverage(src_dir)?.entries)
}

/// As [`extract`], but also reporting the properties it could not extract.
pub fn coverage(src_dir: &Path) -> Result<Coverage, String> {
    let mut files: Vec<std::path::PathBuf> = Vec::new();
    let mut stack = vec![src_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let rd = std::fs::read_dir(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        for ent in rd {
            let ent = ent.map_err(|e| format!("{}: {e}", dir.display()))?;
            let p = ent.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|e| e == "hs") {
                files.push(p);
            }
        }
    }
    files.sort();
    let mut out = Vec::new();
    let mut skipped = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).map_err(|e| format!("{}: {e}", f.display()))?;
        let name = f
            .file_name()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default();
        // `src/ShellCheck/...` as the repository spells it, so an annotation
        // can name a file GitHub can find. `src_dir` is the tree's
        // `src/ShellCheck`, which is the prefix to restore.
        let rel = f
            .strip_prefix(src_dir)
            .map(|p| format!("src/ShellCheck/{}", p.to_string_lossy()))
            .unwrap_or_else(|_| f.to_string_lossy().into_owned());
        let mut entries = extract_text(&name, &text);
        for e in &mut entries {
            e.path = rel.clone();
        }
        // Every property the file defines, so the ones with no script to
        // replay are counted rather than passed over in silence.
        let extracted: std::collections::HashSet<&str> =
            entries.iter().map(|e| e.id.as_str()).collect();
        for prop in property_names(&text) {
            if !extracted.contains(prop.as_str()) {
                skipped.push((name.clone(), prop));
            }
        }
        out.extend(entries);
    }
    out.sort_by(|a, b| a.id.cmp(&b.id));
    // Two modules can define the same property name -- Analytics.hs and
    // Checks/Commands.hs both have `prop_checkPS13`, and there are a dozen more
    // like it. Dropping either would silently cost the gate a property, so
    // qualify both with the file they came from instead.
    let mut seen: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
    for e in &out {
        *seen.entry(e.id.as_str()).or_default() += 1;
    }
    let dupes: std::collections::HashSet<String> = seen
        .iter()
        .filter(|(_, n)| **n > 1)
        .map(|(k, _)| (*k).to_string())
        .collect();
    for e in &mut out {
        if dupes.contains(&e.id) {
            e.id = format!("{}:{}", e.file, e.id);
        }
    }
    out.sort_by(|a, b| a.id.cmp(&b.id));
    skipped.sort();
    Ok(Coverage {
        entries: out,
        skipped,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_property() {
        let e = extract_text("X.hs", r#"prop_checkFoo1 = verify checkFoo "echo $x""#);
        assert_eq!(e.len(), 1);
        assert_eq!(e[0].id, "prop_checkFoo1");
        assert_eq!(e[0].helper, "verify");
        assert_eq!(e[0].script, "echo $x");
    }

    // The line a property is defined on is what a CI annotation points at, and
    // an annotation on the wrong line is worse than none: it blames code that
    // is fine. 1-based, and counted from the property's first line even when
    // the definition continues onto following ones.
    #[test]
    fn property_line_is_where_the_definition_starts() {
        let text = "module X where\n\
                    \n\
                    prop_a = verify checkFoo \"one\"\n\
                    prop_b = verify checkFoo\n    \"two\"\n\
                    prop_c = verify checkFoo \"three\"\n";
        let e = extract_text("X.hs", text);
        let at = |id: &str| e.iter().find(|x| x.id == id).map(|x| x.line);
        assert_eq!(at("prop_a"), Some(3));
        assert_eq!(
            at("prop_b"),
            Some(4),
            "the first line, not the continuation"
        );
        assert_eq!(at("prop_c"), Some(6));
    }

    // The real tree, because the path has to exist for GitHub to resolve it,
    // and three modules live under `Checks/` rather than beside the rest.
    #[test]
    fn every_entry_carries_a_path_that_exists() {
        let Some(repo) = crate::checkout() else {
            println!(
                "skipped: no ShellCheck checkout around {}",
                env!("CARGO_MANIFEST_DIR")
            );
            return;
        };
        let src = repo.join("src/ShellCheck");
        let entries = extract(&src).expect("extract");
        let mut checked = 0;
        for e in &entries {
            assert!(
                e.path.starts_with("src/ShellCheck/"),
                "{} has path {:?}",
                e.id,
                e.path
            );
            let full = repo.join(&e.path);
            assert!(full.is_file(), "{} points at {:?}", e.id, full);
            // And the line really holds that property.
            let text = std::fs::read_to_string(&full).expect("read");
            let line = text.lines().nth(e.line - 1).unwrap_or("");
            let bare = e.id.rsplit(':').next().unwrap_or(&e.id);
            assert!(
                line.starts_with(bare),
                "{} says {}:{} but that line is {:?}",
                e.id,
                e.path,
                e.line,
                line
            );
            checked += 1;
        }
        assert!(checked > 2000, "expected the whole corpus, got {checked}");
    }

    #[test]
    fn parenthesised_target_takes_the_last_literal() {
        let e = extract_text(
            "X.hs",
            r#"prop_checkSudoArgs1 = verify (checkSudoArgs "sudo") "sudo cd /root""#,
        );
        assert_eq!(e[0].script, "sudo cd /root");
    }

    #[test]
    fn verify_codes_list_is_skipped() {
        let e = extract_text(
            "X.hs",
            r##"prop_x = verifyCodes checkEqualsInCommand [2277] "#!/bin/bash\n0='foo'""##,
        );
        assert_eq!(e[0].helper, "verifyCodes");
        assert_eq!(e[0].script, "#!/bin/bash\n0='foo'");
    }

    #[test]
    fn continuation_line_is_joined() {
        let e = extract_text(
            "X.hs",
            "prop_checkFunctionsUsedExternally1 =\n    verifyTree checkFunctionsUsedExternally \"foo() { :; }; sudo foo\"\n",
        );
        assert_eq!(e.len(), 1);
        assert_eq!(e[0].helper, "verifyTree");
        assert_eq!(e[0].script, "foo() { :; }; sudo foo");
    }

    #[test]
    fn verify_not_is_not_read_as_verify() {
        let e = extract_text("X.hs", r#"prop_x = verifyNot checkFoo "ok""#);
        assert_eq!(e[0].helper, "verifyNot");
        let e = extract_text("X.hs", r#"prop_x = verifyNotTree checkFoo "ok""#);
        assert_eq!(e[0].helper, "verifyNotTree");
    }

    #[test]
    fn escapes() {
        assert_eq!(unescape(r"a\nb"), "a\nb");
        assert_eq!(unescape(r#"say \"hi\""#), "say \"hi\"");
        assert_eq!(unescape(r"back\\slash"), r"back\slash");
        assert_eq!(unescape(r"\x41\x42"), "AB");
        assert_eq!(unescape(r"\o101"), "A");
        assert_eq!(unescape(r"\65"), "A");
        assert_eq!(unescape(r"\NUL"), "\0");
        assert_eq!(unescape(r"\ESC[0m"), "\u{1b}[0m");
        // A shell backslash-escape survives as a literal backslash pair.
        assert_eq!(unescape(r"echo \\e"), r"echo \e");
    }

    #[test]
    fn string_gap_vanishes() {
        assert_eq!(unescape("one\\   \\two"), "onetwo");
    }

    #[test]
    fn comments_do_not_yield_literals() {
        let lits = string_literals(r#"foo "keep" -- "dropped""#);
        assert_eq!(lits, vec!["keep".to_string()]);
    }

    #[test]
    fn quote_char_literal_does_not_open_a_string() {
        let lits = string_literals(r#"f '"' "real""#);
        assert_eq!(lits, vec!["real".to_string()]);
    }

    #[test]
    fn non_property_lines_are_ignored() {
        assert!(extract_text("X.hs", "checkFoo = doStuff \"not a prop\"").is_empty());
    }
}
