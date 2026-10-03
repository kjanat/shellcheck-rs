//! `.shellcheckrc` / `--rcfile` configuration support.
//!
//! Mirrors the discovery of the Haskell driver (`shellcheck.hs`: `getConfig`,
//! `findConfig`, `getConfigPaths`, `defaultPaths`, `readConfig`) and the rc
//! grammar of the core parser (`ShellCheck.Parser.readConfigKVs`, which is
//! `readAnnotationWithoutPrefix False` repeated between spacing and comments,
//! terminated by `eof`).
//!
//! An rc file is therefore *not* one `key=value` per line: a line may carry
//! several whitespace-separated pairs, exactly as an inline `# shellcheck`
//! annotation may, and anything that is not a pair is a configuration parse
//! failure reported as SC1134 (`readConfigFile`'s `Left` branch), which
//! discards every directive in the file.
//!
//! Directives recognised here (`readAnnotationWithoutPrefix` with
//! `sandboxed = False`):
//!
//!   * `disable=SC2086,SC1000-SC2000,all` -> `DisableComment` ranges
//!   * `enable=check-name,other` -> `EnableComment`s, appended to optional checks
//!   * `shell=bash` -> `ShellOverride`
//!   * `extended-analysis=true|false` -> `ExtendedAnalysis`
//!   * `external-sources=true|false` -> parsed, inert (source resolver not ported)
//!   * `source=...` / `source-path=...` -> parsed, inert
//!   * anything else -> SC1107, a note that rc parsing discards, and ignored
//!
//! Notes raised while parsing an rc file (SC1103, SC1107, SC1125, SC1146, ...)
//! are dropped upstream too: `readConfig` runs the sub-parser with its own
//! state and keeps only the annotations, so only the fatal SC1134 survives.

use std::cell::RefCell;

use shellcheck_rs::ast::Annotation;
use shellcheck_rs::editor_config::{
    invalid_root_lines, is_editor_config_root, is_rejection, rejected_root,
};
use shellcheck_rs::interface::{
    CheckSpec, DisableRange, RcDirectives, RcParseProblem, Shell, decode_bytes,
};

use crate::options::parse_shell;
use crate::paths::{
    combine, does_file_exist, io_error_message, normalize, take_directory, take_file_name,
    xdg_config_home,
};

/// The directives of one rc file, reduced to what the checker needs.
///
/// Upstream keeps the raw `[Annotation]` and lets the analyzer pick: all
/// `DisableComment`s and `EnableComment`s apply, while `determineShell` and
/// `getExtendedAnalysisDirective` take the FIRST `ShellOverride` /
/// `ExtendedAnalysis` in file order. This mirrors that reduction.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RcConfig {
    /// Code ranges from `disable=` directives, as endpoints.
    pub disabled: Vec<DisableRange>,
    /// Names from `enable=` directives, in order.
    pub enabled_checks: Vec<String>,
    /// The first `shell=` override, resolved through `shellForExecutable`.
    /// `None` when there was none, *or* when the first one is unrecognised: a
    /// later valid override does not get a turn.
    pub shell: Option<Shell>,
    /// The first `extended-analysis=` toggle.
    pub extended_analysis: Option<bool>,
    /// Set when the file could not be parsed; then no directive applies.
    pub parse_problem: Option<RcParseProblem>,
}

impl RcConfig {
    /// The reduction described above (`ShellCheck.AnalyzerLib.determineShell`,
    /// `ASTLib.getExtendedAnalysisDirective`, `Checker`'s
    /// `getEnableDirectives`).
    fn from_annotations(annotations: &[Annotation]) -> Self {
        let mut cfg = Self::default();
        for a in annotations {
            match a {
                Annotation::DisableComment(from, to) => cfg.disabled.push(DisableRange {
                    from: *from,
                    to: *to,
                }),
                Annotation::EnableComment(name) => cfg.enabled_checks.push(name.clone()),
                _ => {}
            }
        }
        // `headOrDefault (fromShebang s) [s | ShellOverride s <- annotations]`:
        // the first override is the candidate, valid or not.
        cfg.shell = annotations
            .iter()
            .find_map(|a| match a {
                Annotation::ShellOverride(s) => Some(s),
                _ => None,
            })
            .and_then(|s| parse_shell(s));
        // `listToMaybe [s | ExtendedAnalysis s <- list]`: first wins.
        cfg.extended_analysis = annotations.iter().find_map(|a| match a {
            Annotation::ExtendedAnalysis(b) => Some(*b),
            _ => None,
        });
        cfg
    }
}

/// Parse the contents of the rc file at `filename` (used only in the SC1134
/// message). Never fails: a parse failure becomes `parse_problem`, with every
/// directive discarded, as `readConfigFile` returns `[]` on `Left`.
#[must_use]
pub fn parse_contents(filename: &str, contents: &str) -> RcConfig {
    match read_config_kvs(contents) {
        Ok(annotations) => RcConfig::from_annotations(&annotations),
        Err(fail) => RcConfig {
            parse_problem: Some(RcParseProblem {
                filename: filename.to_string(),
                line: fail.line,
                column: fail.column,
                suggestion: fail.suggestion(),
            }),
            ..RcConfig::default()
        },
    }
}

/// Apply one rc file's directives to a spec. CLI flags win where they conflict
/// (`csShellTypeOverride` and `csExtendedAnalysis` are consulted before the
/// annotations upstream), while `disable`/`enable` always add.
pub fn merge_into(spec: &mut CheckSpec, rc: &RcConfig) {
    let directives = spec
        .rc
        .get_or_insert_with(|| Box::new(RcDirectives::default()));
    if let Some(problem) = &rc.parse_problem {
        directives.parse_problem = Some(problem.clone());
        return;
    }
    directives
        .disabled_ranges
        .extend(rc.disabled.iter().copied());
    spec.optional_checks
        .extend(rc.enabled_checks.iter().cloned());
    if spec.shell_type_override.is_none() {
        spec.shell_type_override = rc.shell;
    }
    if spec.extended_analysis.is_none() {
        spec.extended_analysis = rc.extended_analysis;
    }
}

/// A parse failure. `message` is the explicit `fail "..."` string of whichever
/// parser gave up, which is all `getStringFromParsec` shows (`Expect` /
/// `UnExpect` / `SysUnExpect` are deliberately dropped there).
#[derive(Debug, Clone, PartialEq, Eq)]
struct Fail {
    line: i64,
    column: i64,
    message: Option<String>,
}

impl Fail {
    /// `getStringFromParsec`: the message plus a period, or nothing at all.
    fn suggestion(&self) -> String {
        match &self.message {
            Some(m) => format!("{m}."),
            None => String::new(),
        }
    }
}

/// `readConfigKVs`, hand-rolled: `anySpacingOrComment`, then
/// `many (readAnnotationWithoutPrefix False <* anySpacingOrComment)`, then
/// `eof`. As in Parsec, an inner parser that fails without consuming ends the
/// `many`, while one that fails after consuming takes the whole file down.
fn read_config_kvs(contents: &str) -> Result<Vec<Annotation>, Fail> {
    let mut p = ConfigParser::new(contents);
    p.any_spacing_or_comment()?;
    let mut out = Vec::new();
    let mut parsed_any = false;
    loop {
        let start = p.idx;
        match p.read_annotation_without_prefix() {
            Ok(mut annotations) => {
                out.append(&mut annotations);
                parsed_any = true;
                // `ann <* anySpacingOrComment`: a failure here is the `many`'s.
                p.any_spacing_or_comment()?;
            }
            Err(fail) => {
                if p.idx != start {
                    return Err(fail);
                }
                break;
            }
        }
    }
    if !p.eof() {
        // `eof` failed: what is left is neither a directive, spacing, nor a
        // comment. The suggestion the oracle shows for this is the "Expected
        // whitespace" of `allspacingOrFail` while no directive has been read,
        // and nothing once one has (the `eof` failure no longer merges with it).
        return Err(Fail {
            line: p.line,
            column: p.column,
            message: if parsed_any {
                None
            } else {
                Some("Expected whitespace".to_string())
            },
        });
    }
    Ok(out)
}

/// A character cursor over an rc file, with the line and column the parsec
/// error position would report.
struct ConfigParser {
    chars: Vec<char>,
    idx: usize,
    line: i64,
    column: i64,
}

impl ConfigParser {
    fn new(contents: &str) -> Self {
        Self {
            chars: contents.chars().collect(),
            idx: 0,
            line: 1,
            column: 1,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.idx).copied()
    }

    const fn eof(&self) -> bool {
        self.idx >= self.chars.len()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.idx += 1;
        // `updatePosChar`: a tab moves to the next multiple of eight, plus one.
        match c {
            '\n' => {
                self.line += 1;
                self.column = 1;
            }
            '\t' => self.column += 8 - (self.column - 1) % 8,
            _ => self.column += 1,
        }
        Some(c)
    }

    /// Consume `c` if it is next.
    fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// A failure carrying an explicit `fail` message.
    fn fail_with<T>(&self, message: &str) -> Result<T, Fail> {
        Err(Fail {
            line: self.line,
            column: self.column,
            message: Some(message.to_string()),
        })
    }

    /// A failure with no message of its own, like Parsec's implicit errors.
    const fn fail<T>(&self) -> Result<T, Fail> {
        Err(Fail {
            line: self.line,
            column: self.column,
            message: None,
        })
    }

    /// `many linewhitespace`, returning what it matched.
    fn line_whitespace(&mut self) -> String {
        let mut out = String::new();
        while matches!(self.peek(), Some(' ' | '\t')) {
            out.push(self.bump().unwrap());
        }
        out
    }

    /// `readAnyComment`: `#` and the rest of the line.
    fn read_any_comment(&mut self) -> bool {
        if !self.eat('#') {
            return false;
        }
        while matches!(self.peek(), Some(c) if c != '\n' && c != '\r') {
            self.bump();
        }
        true
    }

    /// `anySpacingOrComment = many (void allspacingOrFail <|> void readAnyComment)`.
    ///
    /// The `<|>` only reaches `readAnyComment` if `allspacingOrFail` failed
    /// without consuming; having consumed, its failure is the whole parse's.
    fn any_spacing_or_comment(&mut self) -> Result<(), Fail> {
        loop {
            let start = self.idx;
            match self.allspacing_or_fail() {
                Ok(()) => {}
                Err(fail) => {
                    if self.idx != start {
                        return Err(fail);
                    }
                    if !self.read_any_comment() {
                        return Ok(());
                    }
                }
            }
        }
    }

    /// `allspacingOrFail`: `allspacing` that must have collected something.
    ///
    /// Emptiness is about the *string* `allspacing` returns, not about input
    /// consumed: a comment, and the trailing part of a line continuation,
    /// contribute nothing to it. So `\<newline>` at the start of a line
    /// consumes input and then fails, taking the file down with it.
    fn allspacing_or_fail(&mut self) -> Result<(), Fail> {
        if self.allspacing()?.is_empty() {
            return self.fail_with("Expected whitespace");
        }
        Ok(())
    }

    /// `allspacing`: `spacing`, then a `linefeed` and as much again, returning
    /// the spacing collected (a linefeed counts as a character).
    ///
    /// `linefeed = optional carriageReturn >> char '\n'`, so a carriage return
    /// with no linefeed after it leaves `allspacing` having consumed input and
    /// failing — which no caller can recover from.
    fn allspacing(&mut self) -> Result<String, Fail> {
        let mut out = String::new();
        loop {
            out.push_str(&self.spacing());
            if self.peek() == Some('\r') {
                self.bump();
                if !self.eat('\n') {
                    return self.fail();
                }
            } else if !self.eat('\n') {
                return Ok(out);
            }
            out.push('\n');
        }
    }

    /// `spacing`: `many (many1 linewhitespace <|> continuation)` then an
    /// optional comment, returning `concat` of the whitespace it matched. Note
    /// that a carriage return is NOT line whitespace, and that neither the
    /// comment nor a continuation's `\<newline>` is part of the result.
    fn spacing(&mut self) -> String {
        let mut out = String::new();
        loop {
            let start = self.idx;
            out.push_str(&self.line_whitespace());
            // `continuation = try (string "\\\n") >> many linewhitespace >> ..`
            if self.peek() == Some('\\') && self.chars.get(self.idx + 1) == Some(&'\n') {
                self.bump();
                self.bump();
                out.push_str(&self.line_whitespace());
                // `optional readComment` (its SC1143 is a discarded note).
                self.read_comment();
            }
            if self.idx == start {
                break;
            }
        }
        // `optional readComment`
        self.read_comment();
        out
    }

    /// `readComment`: a comment that is not a `# shellcheck` directive, which
    /// `anySpacingOrComment` picks up with `readAnyComment` instead.
    fn read_comment(&mut self) -> bool {
        if self.looks_like_annotation_prefix() {
            return false;
        }
        self.read_any_comment()
    }

    /// `readAnnotationPrefix`: `#`, line whitespace, `shellcheck`.
    fn looks_like_annotation_prefix(&self) -> bool {
        let mut i = self.idx;
        if self.chars.get(i) != Some(&'#') {
            return false;
        }
        i += 1;
        while matches!(self.chars.get(i), Some(' ' | '\t')) {
            i += 1;
        }
        self.chars[i..].starts_with(&['s', 'h', 'e', 'l', 'l', 'c', 'h', 'e', 'c', 'k'])
    }

    /// `readAnnotationWithoutPrefix False`: one or more `key=value` pairs,
    /// an optional trailing comment, then the end of the line.
    fn read_annotation_without_prefix(&mut self) -> Result<Vec<Annotation>, Fail> {
        let mut out = Vec::new();
        // `many1 readKey` counts keys, not annotations: `disable=` is a key
        // whose value parses to nothing.
        let mut keys = 0;
        loop {
            let key = self.read_key_name();
            if key.is_empty() {
                // `many1 (letter <|> char '-')` failed without consuming.
                break;
            }
            if !self.eat('=') {
                return self.fail_with("Expected '=' after directive key");
            }
            out.append(&mut self.read_value(&key)?);
            keys += 1;
            self.line_whitespace();
        }
        if keys == 0 {
            return self.fail();
        }
        self.read_any_comment();
        // `void linefeed <|> eof <|> do { SC1125; many (noneOf "\n"); .. }`,
        // where `linefeed = optional carriageReturn >> char '\n'`: a carriage
        // return that is not followed by one has consumed input, so neither
        // `eof` nor the SC1125 recovery gets a turn and the file fails. (The
        // SC1017 the return itself draws is a parse problem on the rc file,
        // which this port has no channel for.)
        if self.peek() == Some('\r') {
            self.bump();
            if !self.eat('\n') {
                return self.fail();
            }
            self.line_whitespace();
            return Ok(out);
        }
        if !self.eat('\n') && !self.eof() {
            while matches!(self.peek(), Some(c) if c != '\n') {
                self.bump();
            }
            self.eat('\n');
        }
        self.line_whitespace();
        Ok(out)
    }

    /// `many1 (letter <|> char '-')`, possibly empty (the caller decides).
    fn read_key_name(&mut self) -> String {
        let mut s = String::new();
        while matches!(self.peek(), Some(c) if c.is_ascii_alphabetic() || c == '-') {
            s.push(self.bump().unwrap());
        }
        s
    }

    /// The `case key of` in `readKey`.
    fn read_value(&mut self, key: &str) -> Result<Vec<Annotation>, Fail> {
        match key {
            "disable" => self.plain_or_quoted(Self::read_disable_elements),
            "enable" => self.plain_or_quoted(Self::read_enable_names),
            "source" => Ok(vec![Annotation::SourceOverride(self.read_word_value()?)]),
            "source-path" => Ok(vec![Annotation::SourcePath(self.read_word_value()?)]),
            // An unknown shell only draws SC1103 (a discarded note); the
            // override itself still stands.
            "shell" => Ok(vec![Annotation::ShellOverride(self.read_word_value()?)]),
            "extended-analysis" => {
                let value = self.plain_or_quoted(Self::read_letters)?;
                Ok(match value.as_str() {
                    "true" => vec![Annotation::ExtendedAnalysis(true)],
                    "false" => vec![Annotation::ExtendedAnalysis(false)],
                    // SC1146, discarded.
                    _ => Vec::new(),
                })
            }
            "external-sources" => {
                let value = self.plain_or_quoted(Self::read_letters)?;
                Ok(match value.as_str() {
                    // Not sandboxed in an rc file, so `true` is allowed here.
                    "true" => vec![Annotation::ExternalSources(true)],
                    "false" => vec![Annotation::ExternalSources(false)],
                    // SC1145, discarded.
                    _ => Vec::new(),
                })
            }
            // SC1107, discarded: `anyChar reluctantlyTill whitespace`.
            _ => {
                while matches!(self.peek(), Some(c) if !c.is_whitespace()) {
                    self.bump();
                }
                Ok(Vec::new())
            }
        }
    }

    /// `plainOrQuoted p = quoted p <|> p`: run `p` on the contents of a quoted
    /// value, or on the input directly.
    fn plain_or_quoted<T>(&mut self, p: impl Fn(&mut Self) -> Result<T, Fail>) -> Result<T, Fail> {
        let quote = match self.peek() {
            Some(q @ ('\'' | '"')) => q,
            _ => return p(self),
        };
        self.bump();
        let (line, column) = (self.line, self.column);
        let mut inner = String::new();
        while matches!(self.peek(), Some(c) if c != quote && c != '\n') {
            inner.push(self.bump().unwrap());
        }
        // `many1 $ noneOf (c:"\n")` — an empty pair of quotes fails, and the
        // opening quote is already consumed, so there is no going back to `p`.
        if inner.is_empty() {
            return self.fail();
        }
        if !self.eat(quote) {
            return self.fail_with("Missing terminating quote for directive.");
        }
        // `subParse start p str`, with `start` taken just after the opening
        // quote: the quoted text cannot span lines, so a failure inside it is
        // reported on this line, at its column from there.
        let mut sub = Self::new(&inner);
        sub.line = line;
        sub.column = column;
        p(&mut sub)
    }

    /// `many1 letter`.
    fn read_letters(&mut self) -> Result<String, Fail> {
        let mut s = String::new();
        while matches!(self.peek(), Some(c) if c.is_ascii_alphabetic()) {
            s.push(self.bump().unwrap());
        }
        if s.is_empty() {
            return self.fail();
        }
        Ok(s)
    }

    /// `quoted (many1 anyChar) <|> (many1 $ noneOf " \n")`, as used by
    /// `source`, `source-path` and `shell`.
    fn read_word_value(&mut self) -> Result<String, Fail> {
        if let Some(q @ ('\'' | '"')) = self.peek() {
            self.bump();
            let mut inner = String::new();
            while matches!(self.peek(), Some(c) if c != q && c != '\n') {
                inner.push(self.bump().unwrap());
            }
            if inner.is_empty() {
                return self.fail();
            }
            if !self.eat(q) {
                return self.fail_with("Missing terminating quote for directive.");
            }
            return Ok(inner);
        }
        let mut s = String::new();
        while matches!(self.peek(), Some(c) if c != ' ' && c != '\n') {
            s.push(self.bump().unwrap());
        }
        if s.is_empty() {
            return self.fail();
        }
        Ok(s)
    }

    /// `readElement `sepBy` char ','` for `disable=`.
    fn read_disable_elements(&mut self) -> Result<Vec<Annotation>, Fail> {
        let mut out = Vec::new();
        let start = self.idx;
        match self.read_disable_element() {
            Ok(a) => out.push(a),
            Err(fail) => {
                // `sepBy` allows none at all, but only if nothing was consumed.
                if self.idx != start {
                    return Err(fail);
                }
                return Ok(out);
            }
        }
        while self.eat(',') {
            out.push(self.read_disable_element()?);
        }
        Ok(out)
    }

    /// `readElement = readRange <|> readAll`.
    fn read_disable_element(&mut self) -> Result<Annotation, Fail> {
        let start = self.idx;
        match self.read_disable_range() {
            Ok(a) => return Ok(a),
            Err(fail) => {
                if self.idx != start {
                    return Err(fail);
                }
            }
        }
        // `readAll`: `string "all"`, which consumes what it matched but reports
        // a mismatch at the position where the string began.
        let (line, column) = (self.line, self.column);
        for expected in "all".chars() {
            if !self.eat(expected) {
                return Err(Fail {
                    line,
                    column,
                    message: None,
                });
            }
        }
        Ok(Annotation::DisableComment(0, 1_000_000))
    }

    /// `readRange`: a code, optionally `-` and another. A lone code disables
    /// itself alone (`DisableComment from (from+1)`); the endpoints are kept as
    /// they are, however far apart.
    fn read_disable_range(&mut self) -> Result<Annotation, Fail> {
        let from = self.read_disable_code()?;
        let to = if self.eat('-') {
            self.read_disable_code()?
        } else {
            from.saturating_add(1)
        };
        Ok(Annotation::DisableComment(from, to))
    }

    /// `readCode = optional (string "SC") >> many1 digit`. Parsec's `string`
    /// consumes what it matched before failing, so a lone `S` is fatal, and
    /// the failure is positioned where the string began.
    fn read_disable_code(&mut self) -> Result<i64, Fail> {
        if self.peek() == Some('S') {
            let (line, column) = (self.line, self.column);
            self.bump();
            if !self.eat('C') {
                return Err(Fail {
                    line,
                    column,
                    message: None,
                });
            }
        }
        let mut s = String::new();
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            s.push(self.bump().unwrap());
        }
        if s.is_empty() {
            return self.fail();
        }
        // Haskell reads an unbounded Integer; clamp instead of overflowing.
        Ok(s.parse::<i64>().unwrap_or(i64::MAX))
    }

    /// `readName `sepBy` char ','` for `enable=`, with
    /// `readName = many1 (letter <|> char '-')`.
    fn read_enable_names(&mut self) -> Result<Vec<Annotation>, Fail> {
        let mut out = Vec::new();
        let first = self.read_key_name();
        if first.is_empty() {
            // `sepBy` with no elements: nothing was consumed.
            return Ok(out);
        }
        out.push(Annotation::EnableComment(first));
        while self.eat(',') {
            let name = self.read_key_name();
            if name.is_empty() {
                return self.fail();
            }
            out.push(Annotation::EnableComment(name));
        }
        Ok(out)
    }
}

/// A configuration file's name and contents, as `siGetConfig` returns them.
pub type RawConfig = (String, String);

/// `siGetConfig` of `ioInterface` (`getConfig`): the `.shellcheckrc` that
/// applies to an input, merged with what its EditorConfig files say about it.
pub struct ConfigLookup {
    /// `--rcfile`, which replaces the `.shellcheckrc` search.
    rcfile: Option<String>,
    /// `getRcConfig`'s cache: the directory last searched and what was found,
    /// with `/` standing for the `--rcfile`.
    cache: RefCell<Option<(String, Option<RawConfig>)>>,
}

impl ConfigLookup {
    #[must_use]
    pub const fn new(rcfile: Option<String>) -> Self {
        Self {
            rcfile,
            cache: RefCell::new(None),
        }
    }

    /// `getConfig`, parsed: returns the name and contents of .shellcheckrc for
    /// the given file, merged with any shellcheck.* directives found in
    /// applicable EditorConfig files.
    pub fn get(&self, filename: &str) -> Option<RcConfig> {
        let rc = self.rc_config(filename);
        let ec = editor_config(filename);
        merge_configs(rc, ec).map(|(path, contents)| parse_contents(&path, &contents))
    }

    /// `getRcConfig`: an explicit `--rcfile` is read once and applied to every
    /// input; if unreadable, warn once and proceed with no config. Otherwise
    /// discover the rc config for the input by walking up from its directory
    /// to the filesystem root, then the user config dirs, and use the first
    /// candidate that exists (`findConfig`).
    ///
    /// For stdin (`-`) the current working directory is the starting point:
    /// `normalize` makes the name absolute against the CWD, as
    /// `canonicalizePath` does.
    fn rc_config(&self, filename: &str) -> Option<RawConfig> {
        let key = match self.rcfile {
            Some(_) => "/".to_string(),
            None => take_directory(&normalize(filename)),
        };
        if let Some((cached, result)) = &*self.cache.borrow()
            && *cached == key
        {
            return result.clone();
        }
        let result = match &self.rcfile {
            // We have a specified rcfile. Ignore normal rcfile resolution.
            Some(file) => {
                let result = read_config(file);
                if result.is_none() {
                    eprintln!("Warning: unable to read --rcfile {file}");
                }
                result
            }
            // `findConfig`/`readConfig` select the FIRST candidate that EXISTS
            // (doesFileExist). A nearer existing-but-unreadable file is still
            // selected: the oracle reports the read error and uses an empty
            // config, rather than silently falling through to a parent or user
            // config.
            None => config_paths(&key).iter().find_map(|p| read_config(p)),
        };
        *self.cache.borrow_mut() = Some((key, result.clone()));
        result
    }
}

/// `readConfig`: the contents of `file` if it exists. One that exists but
/// cannot be read is reported and counts as empty. The path is reported
/// verbatim in SC1134, as the oracle does.
#[must_use]
pub fn read_config(file: &str) -> Option<RawConfig> {
    if !does_file_exist(file) {
        return None;
    }
    // `readConfig` goes through `inputFile`, so an rc file is decoded exactly
    // like a script: bytes, with an ISO-8859-1 fallback for invalid UTF-8.
    let contents = match std::fs::read(file) {
        Ok(bytes) => decode_bytes(&bytes),
        Err(e) => {
            eprintln!("{file}: {}", io_error_message(file, &e));
            String::new()
        }
    };
    Some((file.to_string(), contents))
}

/// `mergeConfigs`: the `.shellcheckrc` followed by the EditorConfig
/// directives, under the `.shellcheckrc`'s name, unless the EditorConfig
/// files were rejected.
#[must_use]
pub fn merge_configs(rc: Option<RawConfig>, ec: Option<RawConfig>) -> Option<RawConfig> {
    match (rc, ec) {
        (None, ec) => ec,
        (rc, None) => rc,
        (Some(_), Some(ec)) if is_rejection(&ec.1) => Some(ec),
        (Some((rc_path, rc)), Some((_, ec))) => Some((rc_path, format!("{rc}\n{ec}"))),
    }
}

/// Looks for `.editorconfig` files in the target directory, parent directories, and `${XDG_CONFIG_HOME}/editorconfig.ini`.
/// Converts `shellcheck.*` keys in matching sections into directives, concatenating blobs under the first contributing file's name.
#[must_use]
pub fn editor_config(filename: &str) -> Option<RawConfig> {
    let global = xdg_config_home().map(|dir| combine(&dir, "editorconfig.ini"));
    editor_config_with(filename, global.as_deref())
}

/// `getEditorConfig` with the global EditorConfig file at `global`.
fn editor_config_with(filename: &str, global: Option<&str>) -> Option<RawConfig> {
    // Resolve the directory (to find .editorconfig files) but keep the leaf
    // filename as-is so that globs match the symlink name rather than the
    // resolved target.
    let dir = normalize(&take_directory(filename));
    let path = combine(&dir, take_file_name(filename));
    let mut configs = dir_editor_configs(&dir);
    configs.extend(global.and_then(read_config));
    let contributions: Vec<RawConfig> = configs
        .iter()
        .filter_map(|config| directives_for(&path, config))
        .collect();
    let (first, _) = contributions.first()?;
    Some((
        first.clone(),
        contributions
            .iter()
            .map(|(_, blob)| blob.as_str())
            .collect(),
    ))
}

/// `directivesFor`: for each EditorConfig file, report any invalid `root`
/// declaration (which takes priority) as a rejected config blob, otherwise
/// yield the matching shellcheck.* directives (invalid directives are reported
/// by `editorConfigDirectives` as a rejected blob so the .shellcheckrc parser
/// emits SC1134).
fn directives_for(path: &str, (file, contents): &RawConfig) -> Option<RawConfig> {
    let blob = match invalid_root_lines(contents).first() {
        Some(&line) => rejected_root(line),
        None => shellcheck_rs::editor_config::directives(
            contents,
            &make_relative_to(&take_directory(file), path),
        )?,
    };
    Some((file.clone(), blob))
}

/// `makeRelativeTo`: `path` below `dir`, or its file name when it is not.
fn make_relative_to(dir: &str, path: &str) -> String {
    let prefix = if dir.is_empty() || dir.ends_with('/') {
        dir.to_string()
    } else {
        format!("{dir}/")
    };
    match path.strip_prefix(&prefix) {
        Some(rest) => rest.to_string(),
        None => take_file_name(path).to_string(),
    }
}

/// `collectDirConfigs`: the `.editorconfig` files from `dir` upwards, nearest
/// first, up to the first that declares itself the root.
fn dir_editor_configs(dir: &str) -> Vec<RawConfig> {
    let mut configs = Vec::new();
    let mut dir = dir.to_string();
    loop {
        let current = read_config(&combine(&dir, ".editorconfig"));
        let is_root = current
            .as_ref()
            .is_some_and(|(_, contents)| is_editor_config_root(contents));
        configs.extend(current);
        let next = take_directory(&dir);
        if next == dir || is_root {
            return configs;
        }
        dir = next;
    }
}

/// `getConfigPaths`: get a list of candidate filenames. This includes
/// .shellcheckrc in all parent directories, plus the user's home dir and xdg
/// dir. The dot is optional for Windows and Snap users. In order:
/// `<dir>/.shellcheckrc` then `<dir>/shellcheckrc` at each level from `dir` up
/// to the root, followed by the user home and XDG config paths
/// (`defaultPaths`).
fn config_paths(dir: &str) -> Vec<String> {
    let mut paths = Vec::new();
    let mut dir = dir.to_string();
    loop {
        paths.push(combine(&dir, ".shellcheckrc"));
        paths.push(combine(&dir, "shellcheckrc"));
        let next = take_directory(&dir);
        if next == dir {
            break;
        }
        dir = next;
    }
    paths.extend(default_paths());
    paths
}

/// `defaultPaths`: the user home rc (`getAppUserDataDirectory "shellcheckrc"`,
/// i.e. `$HOME/.shellcheckrc` on Unix) and the XDG config rc
/// (`getXdgDirectory XdgConfig "shellcheckrc"`, i.e.
/// `$XDG_CONFIG_HOME/shellcheckrc` when that is absolute, or
/// `$HOME/.config/shellcheckrc`).
fn default_paths() -> Vec<String> {
    let home = std::env::var("HOME")
        .ok()
        .map(|home| combine(&home, ".shellcheckrc"));
    let xdg = xdg_config_home().map(|dir| combine(&dir, "shellcheckrc"));
    home.into_iter().chain(xdg).collect()
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;

    fn parse(contents: &str) -> RcConfig {
        parse_contents("rc", contents)
    }

    fn ranges(contents: &str) -> Vec<(i64, i64)> {
        parse(contents)
            .disabled
            .iter()
            .map(|r| (r.from, r.to))
            .collect()
    }

    /// The SC1134 message body the checker would build, or None if the file
    /// parsed.
    fn problem(contents: &str) -> Option<(i64, String)> {
        parse(contents)
            .parse_problem
            .map(|p| (p.line, p.suggestion))
    }

    #[test]
    fn an_rc_file_that_is_not_valid_utf8_still_applies() {
        // `readConfig` reads the rc file through `inputFile` like any script,
        // so a stray byte in a comment does not discard the directives.
        let path = std::env::temp_dir().join("rshellcheck-rc-decode-test");
        std::fs::write(&path, b"# comment \xff here\ndisable=SC2086\n").unwrap();
        let (name, contents) =
            read_config(&path.display().to_string()).expect("rc file should be readable");
        let config = parse_contents(&name, &contents);
        assert_eq!(
            config.disabled.iter().map(|r| r.from).collect::<Vec<_>>(),
            vec![2086]
        );
        assert!(config.parse_problem.is_none());
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn parses_single_disable() {
        assert_eq!(ranges("disable=SC1234"), vec![(1234, 1235)]);
    }

    #[test]
    fn strips_whole_line_and_trailing_comments() {
        assert_eq!(
            ranges("# a comment\ndisable=SC2148 # trailing comment\n"),
            vec![(2148, 2149)]
        );
    }

    #[test]
    fn ignores_blank_lines() {
        assert_eq!(parse("\n\n   \n\t\n"), RcConfig::default());
    }

    #[test]
    fn disable_list_splits_and_accepts_sc_prefix_or_bare() {
        assert_eq!(
            ranges("disable=SC2086,2181"),
            vec![(2086, 2087), (2181, 2182)]
        );
    }

    #[test]
    fn disable_all_is_a_range() {
        // `readAll` is `DisableComment 0 1000000`, not a separate mode.
        assert_eq!(ranges("disable=all"), vec![(0, 1_000_000)]);
    }

    #[test]
    fn disable_range_keeps_endpoints() {
        assert_eq!(ranges("disable=2086-2089"), vec![(2086, 2089)]);
        // A huge range is two numbers, not a billion of them.
        assert_eq!(
            ranges("disable=SC1000-SC1000000000"),
            vec![(1000, 1_000_000_000)]
        );
    }

    #[test]
    fn multiple_disable_lines_accumulate() {
        assert_eq!(
            ranges("disable=SC2148\ndisable=SC2086\n"),
            vec![(2148, 2149), (2086, 2087)]
        );
    }

    #[test]
    fn several_directives_on_one_line() {
        // readConfigKVs is `many readAnnotationWithoutPrefix`, and one
        // annotation is `many1 readKey`: a line may carry several pairs.
        let c = parse("disable=SC2086 shell=sh\n");
        assert_eq!(c.disabled.len(), 1);
        assert_eq!(c.disabled[0].from, 2086);
        assert_eq!(c.shell, Some(Shell::Sh));
        assert!(c.parse_problem.is_none());

        let c =
            parse("enable=require-variable-braces disable=SC1000-SC2000 extended-analysis=false");
        assert_eq!(
            c.enabled_checks,
            vec!["require-variable-braces".to_string()]
        );
        assert_eq!(c.disabled.len(), 1);
        assert_eq!(c.extended_analysis, Some(false));
    }

    #[test]
    fn enable_appends_names() {
        assert_eq!(
            parse("enable=avoid-nullary-conditions,check-extra-masked-returns").enabled_checks,
            vec![
                "avoid-nullary-conditions".to_string(),
                "check-extra-masked-returns".to_string()
            ]
        );
        // `sepBy` allows an empty list: `enable=` is not an error.
        let c = parse("enable=\n");
        assert_eq!(c.enabled_checks, [] as [std::string::String; 0]);
        assert!(c.parse_problem.is_none());
    }

    #[test]
    fn shell_valid_and_invalid() {
        assert_eq!(parse("shell=bash").shell, Some(Shell::Bash));
        assert_eq!(parse("shell=sh").shell, Some(Shell::Sh));
        // Unknown dialect: SC1103 is discarded and there is no usable override.
        assert_eq!(parse("shell=zsh").shell, None);
        // Aliases route through parse_shell (shellForExecutable).
        assert_eq!(parse("shell=ksh93").shell, Some(Shell::Ksh));
    }

    #[test]
    fn shell_keeps_first_override_even_if_unknown() {
        // determineShell takes the first ShellOverride and resolves that one, so
        // a valid override after an invalid one never applies.
        assert_eq!(parse("shell=sh\nshell=bash\n").shell, Some(Shell::Sh));
        assert_eq!(parse("shell=zsh\nshell=sh\n").shell, None);
    }

    #[test]
    fn quoted_values_are_unquoted() {
        assert_eq!(
            ranges("disable='SC2086,SC2181'"),
            vec![(2086, 2087), (2181, 2182)]
        );
        assert_eq!(parse("shell=\"bash\"").shell, Some(Shell::Bash));
        // An unterminated quote is a configuration parse failure.
        assert_eq!(
            problem("shell='bash\""),
            Some((1, "Missing terminating quote for directive..".to_string()))
        );
    }

    #[test]
    fn extended_analysis_first_wins() {
        assert_eq!(
            parse("extended-analysis=true").extended_analysis,
            Some(true)
        );
        assert_eq!(
            parse("extended-analysis=false").extended_analysis,
            Some(false)
        );
        // getExtendedAnalysisDirective is listToMaybe: the first one wins.
        assert_eq!(
            parse("extended-analysis=false\nextended-analysis=true\n").extended_analysis,
            Some(false)
        );
        // Unrecognised value draws SC1146 (discarded) and no annotation.
        assert_eq!(parse("extended-analysis=maybe").extended_analysis, None);
    }

    #[test]
    fn unknown_keys_are_ignored() {
        let c = parse("severity=error\ninclude=SC1000\nbogus=stuff\ndisable=SC2148");
        // severity/include/bogus are not rc directives -> SC1107, discarded.
        assert_eq!(
            c.disabled.iter().map(|r| r.from).collect::<Vec<_>>(),
            vec![2148]
        );
        assert_eq!(c.enabled_checks, [] as [std::string::String; 0]);
        assert!(c.parse_problem.is_none());
    }

    #[test]
    fn inert_directives_parse_without_error() {
        let c = parse("external-sources=true\nsource-path=/x\nsource=lib.sh");
        assert_eq!(c, RcConfig::default());
    }

    #[test]
    fn malformed_lines_are_a_parse_failure() {
        // A key with no '=' is the common case (SC1134, and nothing applies).
        assert_eq!(
            problem("disable SC2086"),
            Some((1, "Expected '=' after directive key.".to_string()))
        );
        // ... and it discards the directives that did parse.
        let c = parse("disable=SC2086\noops here\n");
        assert_eq!(
            c.disabled,
            [] as [shellcheck_rs::interface::DisableRange; 0]
        );
        assert_eq!(
            c.parse_problem.map(|p| (p.line, p.suggestion)),
            Some((2, "Expected '=' after directive key.".to_string()))
        );
        // Garbage that cannot even start a key fails at `eof` instead, whose
        // suggestion depends on whether a directive was read first.
        assert_eq!(
            problem("!!!\n"),
            Some((1, "Expected whitespace.".to_string()))
        );
        assert_eq!(
            problem("# c\n=x\n"),
            Some((2, "Expected whitespace.".to_string()))
        );
        assert_eq!(problem("disable=SC2086\n\n!!!\n"), Some((3, String::new())));
        // A key whose value is missing entirely fails without a message.
        assert_eq!(problem("shell=\n"), Some((1, String::new())));
        assert_eq!(problem("disable=''\n"), Some((1, String::new())));
        assert_eq!(problem("disable=SC2086,\n"), Some((1, String::new())));
        assert_eq!(problem("disable=S\n"), Some((1, String::new())));
    }

    #[test]
    fn trailing_garbage_after_a_pair_is_not_a_failure() {
        // `readAnnotationWithoutPrefix` notes SC1125 and skips the rest of the
        // line; the note is discarded for rc files, so nothing is reported.
        let c = parse("disable=SC2086 !!!\n");
        assert!(c.parse_problem.is_none());
        assert_eq!(c.disabled.len(), 1);
        // A non-numeric disable element leaves a word behind, which then looks
        // like a key without '='.
        assert_eq!(
            problem("disable=x\n"),
            Some((1, "Expected '=' after directive key.".to_string()))
        );
    }

    #[test]
    fn comments_and_continuations() {
        assert!(parse("# c\n").parse_problem.is_none());
        // A comment contributes nothing to `spacing`'s result, so a last one
        // with no newline after it fails `allspacingOrFail` having consumed it.
        assert_eq!(
            problem("# c"),
            Some((1, "Expected whitespace.".to_string()))
        );
        // An annotation-like comment is one `readComment` refuses, so it goes
        // to `readAnyComment` instead -- and then even the newline is optional.
        assert!(parse("# shellcheck disable=SC2086").parse_problem.is_none());
        assert_eq!(
            ranges("# shellcheck accepts this\ndisable=1234"),
            vec![(1234, 1235)]
        );
        // `spacing` collects no characters for a line continuation, so
        // `allspacingOrFail` fails after consuming one: the file is rejected.
        assert_eq!(
            problem("\\\ndisable=SC2086\n"),
            Some((2, "Expected whitespace.".to_string()))
        );
        // ... unless something else on the line contributed whitespace.
        assert_eq!(ranges("  \\\n  # c\ndisable=SC2086\n"), vec![(2086, 2087)]);
    }

    #[test]
    fn carriage_returns() {
        // `linefeed = optional carriageReturn >> char '\n'`: CRLF is fine
        // (SC1017 aside, which is a problem on the rc file, not on the script).
        assert_eq!(
            ranges("disable=SC2086\r\ndisable=SC2154\r\n"),
            vec![(2086, 2087), (2154, 2155)]
        );
        // A carriage return with no linefeed after it is fatal, wherever it is.
        assert_eq!(problem("disable=SC2086\rjunk\n"), Some((1, String::new())));
        assert_eq!(problem("disable=SC2086\r"), Some((1, String::new())));
        assert_eq!(problem("\rdisable=SC2086\n"), Some((1, String::new())));
    }

    #[test]
    fn merge_into_applies_directives_and_respects_cli() {
        let rc = parse("disable=SC2086 enable=foo shell=sh extended-analysis=false");
        let mut spec = CheckSpec::default();
        merge_into(&mut spec, &rc);
        let directives = spec.rc.clone().expect("rc directives");
        assert_eq!(directives.disabled_ranges.len(), 1);
        assert!(directives.disabled_ranges[0].contains(2086));
        assert!(!directives.disabled_ranges[0].contains(2087));
        assert_eq!(spec.optional_checks, vec!["foo".to_string()]);
        assert_eq!(spec.shell_type_override, Some(Shell::Sh));
        assert_eq!(spec.extended_analysis, Some(false));
        assert!(directives.parse_problem.is_none());

        // CLI flags win for shell and extended-analysis.
        let mut spec = CheckSpec {
            shell_type_override: Some(Shell::Bash),
            extended_analysis: Some(true),
            ..CheckSpec::default()
        };
        merge_into(&mut spec, &rc);
        assert_eq!(spec.shell_type_override, Some(Shell::Bash));
        assert_eq!(spec.extended_analysis, Some(true));
    }

    #[test]
    fn a_parse_failure_is_positioned_where_the_oracle_puts_it() {
        let at = |contents: &str| {
            parse(contents)
                .parse_problem
                .map(|p| (p.line, p.column, p.suggestion))
        };
        let expected =
            |line, column, suggestion: &str| Some((line, column, suggestion.to_string()));
        assert_eq!(
            at("disable SC2086"),
            expected(1, 8, "Expected '=' after directive key.")
        );
        assert_eq!(
            at("disable=SC2086\noops here\n"),
            expected(2, 5, "Expected '=' after directive key.")
        );
        // A tab advances to the next multiple of eight; the formatters untab.
        assert_eq!(
            at("\tdisable SC2086"),
            expected(1, 16, "Expected '=' after directive key.")
        );
        assert_eq!(
            at("disable='SC2086"),
            expected(1, 16, "Missing terminating quote for directive..")
        );
        // `string "SC"` reports a partial match where it began.
        assert_eq!(at("disable=S"), expected(1, 9, ""));
        assert_eq!(
            at("x\r"),
            expected(1, 2, "Expected '=' after directive key.")
        );
        assert_eq!(at("disable=SC2086\n  \"x\n"), expected(2, 3, ""));
        assert_eq!(at("\\\nx"), expected(2, 1, "Expected whitespace."));
    }

    /// `checkWithEditorConfig`: shellcheck.* directives extracted from an
    /// EditorConfig file are merged into the same "key=value" blob as
    /// .shellcheckrc. We simulate that here by feeding
    /// `editorConfigDirectives`' output through the rc parser.
    fn with_editor_config(ec: &str, name: &str) -> RcConfig {
        let blob = shellcheck_rs::editor_config::directives(ec, name).unwrap_or_default();
        parse_contents(".editorconfig", &blob)
    }

    #[test]
    fn prop_editorConfigAppliesKnownShell() {
        let c = with_editor_config("[foo]\nshellcheck.shell=bash\n", "foo");
        assert_eq!(c.shell, Some(Shell::Bash));
        assert!(c.parse_problem.is_none());
    }

    #[test]
    fn prop_editorConfigAppliesDisable() {
        let c = with_editor_config("[foo]\nshellcheck.disable=SC2086\n", "foo");
        assert_eq!(
            c.disabled,
            vec![DisableRange {
                from: 2086,
                to: 2087
            }]
        );
        assert!(c.parse_problem.is_none());
    }

    // An unknown shell can't be applied silently; it surfaces as a config
    // parse error (SC1134) rather than being dropped.
    #[test]
    fn prop_editorConfigUnknownShellIsReported() {
        let problem = with_editor_config("[foo]\nshellcheck.shell=zsh\n", "foo")
            .parse_problem
            .expect("SC1134");
        assert_eq!((problem.line, problem.column), (2, 8));
    }

    // EditorConfig has no inline comments, so a '#'-prefixed value is
    // reported as a config error (SC1134) instead of being eaten.
    #[test]
    fn prop_editorConfigCommentValueIsReported() {
        let problem = with_editor_config("[foo]\nshellcheck.disable=#abc\n", "foo")
            .parse_problem
            .expect("SC1134");
        assert_eq!(problem.line, 2);
    }

    // A directive in a section whose glob does not match the file is not
    // applied (and produces no config error).
    #[test]
    fn prop_editorConfigNonMatchingSectionIgnored() {
        assert_eq!(
            with_editor_config("[bar]\nshellcheck.disable=SC2086\n", "foo"),
            RcConfig::default()
        );
    }

    #[test]
    fn merge_configs_appends_the_editor_config_unless_it_was_rejected() {
        let rc = || Some(("/p/.shellcheckrc".to_string(), "disable=SC2086".to_string()));
        let ec = |blob: &str| Some(("/p/.editorconfig".to_string(), blob.to_string()));
        assert_eq!(merge_configs(None, None), None);
        assert_eq!(merge_configs(rc(), None), rc());
        assert_eq!(merge_configs(None, ec("shell=sh\n")), ec("shell=sh\n"));
        assert_eq!(
            merge_configs(rc(), ec("shell=sh\n")),
            Some((
                "/p/.shellcheckrc".to_string(),
                "disable=SC2086\nshell=sh\n".to_string()
            ))
        );
        let rejected = "\n\ninvalid editorconfig value\n";
        assert_eq!(merge_configs(rc(), ec(rejected)), ec(rejected));
    }

    #[test]
    fn make_relative_to_strips_whole_directories() {
        assert_eq!(make_relative_to("/a", "/a/b/c.sh"), "b/c.sh");
        assert_eq!(make_relative_to("/", "/c.sh"), "c.sh");
        assert_eq!(make_relative_to("/a/b", "/a/c.sh"), "c.sh");
        assert_eq!(make_relative_to("/ab", "/abc/d.sh"), "d.sh");
    }

    /// A directory tree under the temp dir, removed on drop.
    struct Tree(std::path::PathBuf);

    impl Tree {
        fn new(name: &str, files: &[(&str, &str)]) -> Self {
            let root =
                std::env::temp_dir().join(format!("rshellcheck-{name}-{}", std::process::id()));
            for (path, contents) in files {
                let path = root.join(path);
                std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                std::fs::write(path, contents).unwrap();
            }
            Self(std::fs::canonicalize(root).unwrap())
        }

        fn path(&self, path: &str) -> String {
            self.0.join(path).display().to_string()
        }
    }

    impl Drop for Tree {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).ok();
        }
    }

    #[test]
    fn editor_config_collects_upwards_then_the_global_file() {
        let tree = Tree::new(
            "ec-collect",
            &[
                (
                    ".editorconfig",
                    "root = true\n[*.sh]\nshellcheck.disable=SC2154\n",
                ),
                ("inner/.editorconfig", "[sub/*.sh]\nshellcheck.shell=bash\n"),
                ("inner/sub/x.sh", ""),
                ("global.ini", "[*]\nshellcheck.extended-analysis=false\n"),
            ],
        );
        let (name, blob) =
            editor_config_with(&tree.path("inner/sub/x.sh"), Some(&tree.path("global.ini")))
                .expect("contributions");
        assert_eq!(name, tree.path("inner/.editorconfig"));
        let c = parse_contents(&name, &blob);
        assert!(c.parse_problem.is_none());
        assert_eq!(c.shell, Some(Shell::Bash));
        assert_eq!(
            c.disabled,
            vec![DisableRange {
                from: 2154,
                to: 2155
            }]
        );
        assert_eq!(c.extended_analysis, Some(false));
    }

    #[test]
    fn editor_config_stops_at_the_root_and_rejects_an_invalid_root() {
        let tree = Tree::new(
            "ec-root",
            &[
                (
                    ".editorconfig",
                    "root = true\n[*.sh]\nshellcheck.disable=SC2154\n",
                ),
                (
                    "a/.editorconfig",
                    "root = true\n[*.sh]\nshellcheck.shell=sh\n",
                ),
                ("a/x.sh", ""),
                (
                    "b/.editorconfig",
                    "# c\nroot = maybe\n[*.sh]\nshellcheck.shell=sh\n",
                ),
                ("b/x.sh", ""),
            ],
        );
        let (name, blob) = editor_config_with(&tree.path("a/x.sh"), None).expect("root");
        assert_eq!(name, tree.path("a/.editorconfig"));
        let c = parse_contents(&name, &blob);
        assert_eq!(c.shell, Some(Shell::Sh));
        assert_eq!(
            c.disabled,
            [] as [shellcheck_rs::interface::DisableRange; 0]
        );

        let (name, blob) = editor_config_with(&tree.path("b/x.sh"), None).expect("rejected");
        assert_eq!(name, tree.path("b/.editorconfig"));
        assert!(!is_rejection(&blob));
        let c = parse_contents(&name, &blob);
        assert_eq!(
            c.disabled,
            [] as [shellcheck_rs::interface::DisableRange; 0]
        );
        let problem = c.parse_problem.expect("SC1134");
        assert_eq!((problem.line, problem.column), (2, 8));
    }

    #[test]
    fn editor_config_is_nothing_without_a_matching_section() {
        let tree = Tree::new(
            "ec-none",
            &[
                (
                    ".editorconfig",
                    "root = true\n[*.py]\nshellcheck.shell=sh\n",
                ),
                ("x.sh", ""),
            ],
        );
        assert_eq!(editor_config_with(&tree.path("x.sh"), None), None);
    }

    #[test]
    fn merge_into_a_broken_rc_applies_nothing() {
        let rc = parse("disable=SC2086\nnot a directive\n");
        let mut spec = CheckSpec::default();
        merge_into(&mut spec, &rc);
        let directives = spec.rc.expect("rc directives");
        assert_eq!(
            directives.disabled_ranges,
            [] as [shellcheck_rs::interface::DisableRange; 0]
        );
        assert_eq!(spec.optional_checks, [] as [std::string::String; 0]);
        let problem = directives.parse_problem.expect("SC1134 problem");
        assert_eq!(problem.filename, "rc");
        assert_eq!(problem.line, 2);
        assert_eq!(problem.suggestion, "Expected '=' after directive key.");
    }
}
