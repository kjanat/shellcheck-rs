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

use std::path::{Path, PathBuf};

use shellcheck_rs::ast::Annotation;
use shellcheck_rs::interface::{CheckSpec, DisableRange, RcDirectives, RcParseProblem, Shell};

use crate::options::parse_shell;

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
    fn from_annotations(annotations: &[Annotation]) -> RcConfig {
        let mut cfg = RcConfig::default();
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
pub fn parse_contents(filename: &str, contents: &str) -> RcConfig {
    match read_config_kvs(contents) {
        Ok(annotations) => RcConfig::from_annotations(&annotations),
        Err(fail) => RcConfig {
            parse_problem: Some(RcParseProblem {
                filename: filename.to_string(),
                line: fail.line,
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
    let directives = spec.rc.get_or_insert_with(|| Box::new(RcDirectives::default()));
    if let Some(problem) = &rc.parse_problem {
        directives.parse_problem = Some(problem.clone());
        return;
    }
    directives.disabled_ranges.extend(rc.disabled.iter().copied());
    spec.optional_checks.extend(rc.enabled_checks.iter().cloned());
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
    p.any_spacing_or_comment();
    let mut out = Vec::new();
    let mut parsed_any = false;
    loop {
        let start = p.idx;
        match p.read_annotation_without_prefix() {
            Ok(mut annotations) => {
                out.append(&mut annotations);
                parsed_any = true;
                p.any_spacing_or_comment();
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
            message: if parsed_any {
                None
            } else {
                Some("Expected whitespace".to_string())
            },
        });
    }
    Ok(out)
}

/// A character cursor over an rc file, with the line number the parsec error
/// position would report.
struct ConfigParser {
    chars: Vec<char>,
    idx: usize,
    line: i64,
}

impl ConfigParser {
    fn new(contents: &str) -> ConfigParser {
        ConfigParser {
            chars: contents.chars().collect(),
            idx: 0,
            line: 1,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.idx).copied()
    }

    fn eof(&self) -> bool {
        self.idx >= self.chars.len()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.idx += 1;
        if c == '\n' {
            self.line += 1;
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
            message: Some(message.to_string()),
        })
    }

    /// A failure with no message of its own, like Parsec's implicit errors.
    fn fail<T>(&self) -> Result<T, Fail> {
        Err(Fail {
            line: self.line,
            message: None,
        })
    }

    fn line_whitespace(&mut self) {
        while matches!(self.peek(), Some(' ' | '\t')) {
            self.bump();
        }
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
    fn any_spacing_or_comment(&mut self) {
        loop {
            let start = self.idx;
            while matches!(self.peek(), Some(' ' | '\t' | '\n' | '\r')) {
                self.bump();
            }
            if !self.read_any_comment() && self.idx == start {
                return;
            }
        }
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
        // `void linefeed <|> eof <|> do { SC1125; many (noneOf "\n"); .. }`
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
    fn plain_or_quoted<T>(
        &mut self,
        p: impl Fn(&mut Self) -> Result<T, Fail>,
    ) -> Result<T, Fail> {
        let quote = match self.peek() {
            Some(q @ ('\'' | '"')) => q,
            _ => return p(self),
        };
        self.bump();
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
        // `subParse start p str`: the quoted text cannot span lines, so a
        // failure inside it is reported on this line.
        let line = self.line;
        let mut sub = ConfigParser::new(&inner);
        sub.line = line;
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
        // `readAll`: `string "all"`, which consumes what it matched.
        for expected in "all".chars() {
            if !self.eat(expected) {
                return self.fail();
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
    /// consumes what it matched before failing, so a lone `S` is fatal.
    fn read_disable_code(&mut self) -> Result<i64, Fail> {
        if self.peek() == Some('S') {
            self.bump();
            if !self.eat('C') {
                return self.fail();
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

/// Read and parse an explicit `--rcfile`. Returns `None` if the file cannot be
/// read (the caller prints the warning), mirroring `readConfig` returning
/// `Nothing`. The path is reported verbatim in SC1134, as the oracle does.
pub fn read_config_file(path: &Path) -> Option<RcConfig> {
    let contents = std::fs::read_to_string(path).ok()?;
    Some(parse_contents(&path.display().to_string(), &contents))
}

/// Discover the applicable rc config for a single input by walking up from the
/// input's directory to the filesystem root, then the user config dirs. Uses
/// the first candidate that exists and is readable (`findConfig`).
///
/// For stdin (`-`) the current working directory is used as the starting point
/// (`getConfig` normalises `-` to the CWD via `canonicalizePath`).
pub fn discover(input_name: &str) -> Option<RcConfig> {
    let dir = starting_dir(input_name)?;
    for candidate in candidate_paths(&dir) {
        // `findConfig`/`readConfig` select the FIRST candidate that EXISTS
        // (doesFileExist). A nearer existing-but-unreadable file is still
        // selected: the oracle reports the read error and uses an empty config,
        // rather than silently falling through to a parent or user config.
        if candidate.is_file() {
            match std::fs::read_to_string(&candidate) {
                Ok(contents) => {
                    return Some(parse_contents(&candidate.display().to_string(), &contents));
                }
                Err(e) => {
                    eprintln!("{}: {}", candidate.display(), e);
                    return Some(RcConfig::default());
                }
            }
        }
    }
    None
}

/// The directory to begin the upward search from for a given input.
fn starting_dir(input_name: &str) -> Option<PathBuf> {
    if input_name == "-" {
        return std::env::current_dir().ok();
    }
    // Normalise like `canonicalizePath`, falling back to the given path if it
    // cannot be canonicalised (e.g. the file does not exist yet).
    let path = std::fs::canonicalize(input_name).unwrap_or_else(|_| PathBuf::from(input_name));
    let dir = path.parent().map(|p| p.to_path_buf());
    match dir {
        Some(d) if !d.as_os_str().is_empty() => Some(d),
        // A bare relative filename has no parent component: use the CWD.
        _ => std::env::current_dir().ok(),
    }
}

/// The ordered list of candidate rc file paths for a starting directory:
/// `<dir>/.shellcheckrc` then `<dir>/shellcheckrc` at each level from `dir` up
/// to the root, followed by the user home and XDG config paths (`defaultPaths`).
fn candidate_paths(dir: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for ancestor in dir.ancestors() {
        paths.push(ancestor.join(".shellcheckrc"));
        paths.push(ancestor.join("shellcheckrc"));
    }
    paths.extend(default_paths());
    paths
}

/// `defaultPaths`: the user home rc (`getAppUserDataDirectory "shellcheckrc"`,
/// i.e. `$HOME/.shellcheckrc` on Unix) and the XDG config rc
/// (`getXdgDirectory XdgConfig "shellcheckrc"`, i.e.
/// `$XDG_CONFIG_HOME/shellcheckrc` or `$HOME/.config/shellcheckrc`).
fn default_paths() -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let home = std::env::var_os("HOME").map(PathBuf::from);
    if let Some(home) = &home {
        paths.push(home.join(".shellcheckrc"));
    }
    if let Some(xdg) = std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from) {
        paths.push(xdg.join("shellcheckrc"));
    } else if let Some(home) = &home {
        paths.push(home.join(".config").join("shellcheckrc"));
    }
    paths
}

#[cfg(test)]
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

        let c = parse("enable=require-variable-braces disable=SC1000-SC2000 extended-analysis=false");
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
        assert!(c.enabled_checks.is_empty());
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
        assert_eq!(parse("extended-analysis=true").extended_analysis, Some(true));
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
        assert!(c.enabled_checks.is_empty());
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
        assert!(c.disabled.is_empty());
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
    fn merge_into_a_broken_rc_applies_nothing() {
        let rc = parse("disable=SC2086\nnot a directive\n");
        let mut spec = CheckSpec::default();
        merge_into(&mut spec, &rc);
        let directives = spec.rc.expect("rc directives");
        assert!(directives.disabled_ranges.is_empty());
        assert!(spec.optional_checks.is_empty());
        let problem = directives.parse_problem.expect("SC1134 problem");
        assert_eq!(problem.filename, "rc");
        assert_eq!(problem.line, 2);
        assert_eq!(problem.suggestion, "Expected '=' after directive key.");
    }
}
