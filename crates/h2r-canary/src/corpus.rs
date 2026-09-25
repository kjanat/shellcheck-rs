use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

pub fn snippets(root: &Path) -> Result<BTreeSet<String>, String> {
    let mut files = Vec::new();
    haskell_files(root, &mut files)?;
    files.sort();
    let mut found = BTreeSet::new();
    for file in files {
        let text = std::fs::read_to_string(&file)
            .map_err(|error| format!("reading {}: {error}", file.display()))?;
        for (line, definition) in definitions(&text) {
            let literals = literals(&definition)
                .map_err(|error| format!("{}:{line}: {error}", file.display()))?;
            found.extend(
                literals
                    .into_iter()
                    .filter(|literal| !literal.contains('\0')),
            );
        }
    }
    Ok(found)
}

fn haskell_files(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries =
        std::fs::read_dir(dir).map_err(|error| format!("listing {}: {error}", dir.display()))?;
    for entry in entries {
        let path = entry
            .map_err(|error| format!("listing {}: {error}", dir.display()))?
            .path();
        if path.is_dir() {
            haskell_files(&path, files)?;
        } else if path.extension().is_some_and(|extension| extension == "hs") {
            files.push(path);
        }
    }
    Ok(())
}

fn definitions(text: &str) -> Vec<(usize, String)> {
    let lines: Vec<&str> = text.lines().collect();
    let mut found = Vec::new();
    let mut index = 0;
    while index < lines.len() {
        if !lines[index].starts_with("prop_") {
            index += 1;
            continue;
        }
        let start = index;
        index += 1;
        while index < lines.len() && lines[index].starts_with(char::is_whitespace) {
            index += 1;
        }
        found.push((start + 1, lines[start..index].join("\n")));
    }
    found
}

fn literals(source: &str) -> Result<Vec<String>, String> {
    let chars: Vec<char> = source.chars().collect();
    let mut found = Vec::new();
    let mut at = 0;
    while at < chars.len() {
        match chars[at] {
            '"' => {
                let (literal, next) = string(&chars, at + 1)?;
                found.push(literal);
                at = next;
            }
            '\'' if at == 0 || !identifier(chars[at - 1]) => {
                at = character(&chars, at + 1)?.unwrap_or(at + 1);
            }
            '-' if line_comment(&chars, at) => {
                while at < chars.len() && chars[at] != '\n' {
                    at += 1;
                }
            }
            '{' if chars.get(at + 1) == Some(&'-') => at = block_comment(&chars, at)?,
            _ => at += 1,
        }
    }
    Ok(found)
}

fn identifier(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

fn symbol(c: char) -> bool {
    "!#$%&*+./<=>?@\\^|-~:".contains(c)
}

fn line_comment(chars: &[char], at: usize) -> bool {
    if at > 0 && symbol(chars[at - 1]) {
        return false;
    }
    let dashes = chars[at..].iter().take_while(|&&c| c == '-').count();
    dashes >= 2 && chars.get(at + dashes).is_none_or(|&c| !symbol(c))
}

fn block_comment(chars: &[char], start: usize) -> Result<usize, String> {
    let mut depth = 0usize;
    let mut at = start;
    while at + 1 < chars.len() {
        match (chars[at], chars[at + 1]) {
            ('{', '-') => {
                depth += 1;
                at += 2;
            }
            ('-', '}') => {
                depth -= 1;
                at += 2;
                if depth == 0 {
                    return Ok(at);
                }
            }
            _ => at += 1,
        }
    }
    Err("unterminated block comment".into())
}

fn character(chars: &[char], at: usize) -> Result<Option<usize>, String> {
    let next = match chars.get(at) {
        Some('\\') => match escape(chars, at + 1)? {
            (Some(_), next) => next,
            (None, _) => return Ok(None),
        },
        Some('\'' | '\n') | None => return Ok(None),
        Some(_) => at + 1,
    };
    Ok((chars.get(next) == Some(&'\'')).then_some(next + 1))
}

fn string(chars: &[char], mut at: usize) -> Result<(String, usize), String> {
    let mut literal = String::new();
    loop {
        match chars.get(at) {
            None | Some('\n') => return Err("unterminated string literal".into()),
            Some('"') => return Ok((literal, at + 1)),
            Some('\\') => {
                let (decoded, next) = escape(chars, at + 1)?;
                literal.extend(decoded);
                at = next;
            }
            Some(&c) => {
                literal.push(c);
                at += 1;
            }
        }
    }
}

const ASCII: [(&str, u32); 34] = [
    ("NUL", 0),
    ("SOH", 1),
    ("STX", 2),
    ("ETX", 3),
    ("EOT", 4),
    ("ENQ", 5),
    ("ACK", 6),
    ("BEL", 7),
    ("BS", 8),
    ("HT", 9),
    ("LF", 10),
    ("VT", 11),
    ("FF", 12),
    ("CR", 13),
    ("SO", 14),
    ("SI", 15),
    ("DLE", 16),
    ("DC1", 17),
    ("DC2", 18),
    ("DC3", 19),
    ("DC4", 20),
    ("NAK", 21),
    ("SYN", 22),
    ("ETB", 23),
    ("CAN", 24),
    ("EM", 25),
    ("SUB", 26),
    ("ESC", 27),
    ("FS", 28),
    ("GS", 29),
    ("RS", 30),
    ("US", 31),
    ("SP", 32),
    ("DEL", 127),
];

fn escape(chars: &[char], at: usize) -> Result<(Option<char>, usize), String> {
    let scalar = |code: u32, next: usize| {
        char::from_u32(code)
            .map(|c| (Some(c), next))
            .ok_or_else(|| format!("escape \\{code} is not a Unicode scalar value"))
    };
    let Some(&first) = chars.get(at) else {
        return Err("a string ends inside an escape".into());
    };
    let simple = match first {
        'a' => Some('\x07'),
        'b' => Some('\x08'),
        'f' => Some('\x0c'),
        'n' => Some('\n'),
        'r' => Some('\r'),
        't' => Some('\t'),
        'v' => Some('\x0b'),
        '\\' | '"' | '\'' => Some(first),
        _ => None,
    };
    if let Some(c) = simple {
        return Ok((Some(c), at + 1));
    }
    match first {
        '&' => Ok((None, at + 1)),
        c if c.is_whitespace() => {
            let mut next = at;
            while chars.get(next).is_some_and(|c| c.is_whitespace()) {
                next += 1;
            }
            if chars.get(next) != Some(&'\\') {
                return Err("a string gap is not closed by a backslash".into());
            }
            Ok((None, next + 1))
        }
        '^' => match chars.get(at + 1) {
            Some(&c @ '@'..='_') => scalar(u32::from(c) - u32::from('@'), at + 2),
            _ => Err("an unknown control escape".into()),
        },
        'o' | 'x' => numeric(chars, at + 1, if first == 'o' { 8 } else { 16 })
            .and_then(|(code, next)| scalar(code, next)),
        c if c.is_ascii_digit() => {
            numeric(chars, at, 10).and_then(|(code, next)| scalar(code, next))
        }
        _ => {
            let name: String = chars[at..].iter().take(3).collect();
            ASCII
                .iter()
                .filter(|(ascii, _)| ascii.len() == 3)
                .chain(ASCII.iter().filter(|(ascii, _)| ascii.len() == 2))
                .find(|(ascii, _)| name.starts_with(ascii))
                .map_or_else(
                    || Err(format!("an unknown escape \\{first}")),
                    |(ascii, code)| scalar(*code, at + ascii.len()),
                )
        }
    }
}

fn numeric(chars: &[char], start: usize, radix: u32) -> Result<(u32, usize), String> {
    let mut code: u32 = 0;
    let mut at = start;
    while let Some(digit) = chars.get(at).and_then(|c| c.to_digit(radix)) {
        code = code
            .checked_mul(radix)
            .and_then(|code| code.checked_add(digit))
            .filter(|&code| code <= 0x10FFFF)
            .ok_or("a numeric escape exceeds the character range")?;
        at += 1;
    }
    if at == start {
        return Err("a numeric escape has no digits".into());
    }
    Ok((code, at))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_escape_form_decodes_as_haskell_reads_it() {
        let source = r#"prop_x = verify f "a\"b\\c\n\t\65\x41\o101\^A\SOH\SO\&H\DEL\1234\&5 \
            \end" 'x' '"' foo' "two""#;
        assert_eq!(
            literals(source).unwrap(),
            vec![
                "a\"b\\c\n\tAAA\u{1}\u{1}\u{e}H\u{7f}\u{4d2}5 end".to_string(),
                "two".to_string(),
            ]
        );
    }

    #[test]
    fn comments_and_operators_are_told_apart() {
        let source = "prop_x = a --> \"kept\" -- it's \"dropped\"\n  {- \"gone\" {- \"nested\" -} -} \"last\"";
        assert_eq!(literals(source).unwrap(), vec!["kept", "last"]);
    }

    #[test]
    fn a_definition_runs_until_the_next_unindented_line() {
        let text = "prop_a =\n    verify f \"x\"\n\nprop_b = verify g \"y\"\nother = \"z\"\n";
        assert_eq!(
            definitions(text),
            vec![
                (1, "prop_a =\n    verify f \"x\"".to_string()),
                (4, "prop_b = verify g \"y\"".to_string()),
            ]
        );
    }
}
