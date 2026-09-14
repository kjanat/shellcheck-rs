//! Port of `ShellCheck.Interface`: the public data types shared across the
//! parse -> analyze -> format pipeline.
//!
//! Field names follow the Haskell record fields but rendered as idiomatic
//! snake_case (e.g. `posFile` -> `file`). Ordering-sensitive derives (`Ord`)
//! mirror the derived `Ord` on the Haskell side, which is used when sorting
//! messages for output.

use std::collections::BTreeMap;

pub type ErrorMessage = String;
pub type Code = i64;

/// `ShellCheck.Interface.SystemInterface`: everything the parser needs from the
/// outside world while following `source` statements.
///
/// Upstream this is a record of monadic functions supplied by the driver
/// (`shellcheck.hs`'s `ioInterface`) or by a test (`mockedSystemInterface`); the
/// port makes it a trait for the same reason -- the analysis core does no IO of
/// its own, and the caller decides what a sourced file may read.
///
/// `siGetConfig` has no counterpart here: this port reads rc files in the CLI
/// (see `shellcheck_cli::rc`) rather than from inside the parser.
pub trait SystemInterface {
    /// `siReadFile`: given what annotations say about including external files
    /// (`None` when nothing said anything) and a resolved filename from
    /// [`SystemInterface::find_source`], read it or explain why not. The
    /// explanation is what SC1091 prints after "Not following: ".
    fn read_file(&self, external_sources: Option<bool>, file: &str)
    -> Result<String, ErrorMessage>;

    /// `siFindSource`: given the script being checked, what annotations say
    /// about external files, the `source-path` annotations in effect (innermost
    /// first) and the sourced name, produce the filename to read.
    fn find_source(
        &self,
        current_script: &str,
        external_sources: Option<bool>,
        source_paths: &[String],
        name: &str,
    ) -> String;
}

/// `newSystemInterface`: reads nothing and resolves a name to itself.
#[derive(Debug, Default, Clone, Copy)]
pub struct NullSystemInterface;

impl SystemInterface for NullSystemInterface {
    fn read_file(
        &self,
        _external_sources: Option<bool>,
        _file: &str,
    ) -> Result<String, ErrorMessage> {
        Err("Not implemented".to_string())
    }

    fn find_source(
        &self,
        _current_script: &str,
        _external_sources: Option<bool>,
        _source_paths: &[String],
        name: &str,
    ) -> String {
        name.to_string()
    }
}

/// The interface [`crate::checker::check_script`] uses when the caller supplies
/// none: no file is ever read, and the refusal is worded exactly as the CLI
/// words it for a file that was not given as an input.
///
/// This is what `shellcheck` does without `-x` for a sourced file it was not
/// asked to check (`ioInterface`'s `allowable` branch), so an embedder that
/// never wires up an interface gets the same diagnostics as the default CLI
/// rather than a message about an unimplemented feature.
#[derive(Debug, Default, Clone, Copy)]
pub struct NoExternalSources;

impl SystemInterface for NoExternalSources {
    fn read_file(
        &self,
        external_sources: Option<bool>,
        file: &str,
    ) -> Result<String, ErrorMessage> {
        Err(not_an_input(external_sources, file))
    }

    fn find_source(
        &self,
        _current_script: &str,
        _external_sources: Option<bool>,
        _source_paths: &[String],
        name: &str,
    ) -> String {
        name.to_string()
    }
}

/// `ioInterface`'s two refusals for a file that is not among the inputs.
pub fn not_an_input(external_sources: Option<bool>, file: &str) -> ErrorMessage {
    if external_sources == Some(false) {
        format!(
            "{file} was not specified as input, and external files were disabled via directive."
        )
    } else {
        format!("{file} was not specified as input (see shellcheck -x).")
    }
}

/// `decodeString` (shellcheck.hs): turn the raw bytes of a script into the
/// character stream the parser sees.
///
/// Upstream opens every input with `openBinaryFile` and `hGetContents`, so each
/// byte arrives as a `Char` with that byte's value, and `decodeString` then
/// folds valid UTF-8 sequences into single characters. Anything that is not a
/// valid sequence is kept as-is, one character per byte -- which is why a file
/// with a stray `\xff` is analysed rather than rejected, and why the column of
/// everything after it is unchanged.
///
/// This is the single place where bytes become a `String` in the port; every
/// reader (main input, sourced file, rc file) goes through it, exactly as every
/// upstream reader goes through `inputFile`.
///
/// One representational difference: Haskell's `chr` accepts surrogate
/// codepoints (`\xD800`-`\xDFFF`), which a UTF-8 sequence can encode and a Rust
/// `char` cannot hold. Such a sequence becomes U+FFFD -- still exactly one
/// character, so columns continue to match; only the character's identity
/// differs, and it is a non-syntactic character either way.
pub fn decode_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let byte = bytes[i];
        if byte.is_ascii() {
            out.push(byte as char);
            i += 1;
            continue;
        }
        // `num >= 0xF8` and `num < 0xC0` are `Nothing` outright; the rest name
        // the low bits of the lead byte and how many continuation bytes follow.
        let next = match byte {
            0xF8..=0xFF => None,
            0xF0..=0xF7 => construct_codepoint(u32::from(byte & 0x07), 3, bytes, i + 1),
            0xE0..=0xEF => construct_codepoint(u32::from(byte & 0x0F), 2, bytes, i + 1),
            0xC0..=0xDF => construct_codepoint(u32::from(byte & 0x1F), 1, bytes, i + 1),
            _ => None,
        };
        match next {
            Some((codepoint, rest)) => {
                out.push(char::from_u32(codepoint).unwrap_or('\u{FFFD}'));
                i = rest;
            }
            // `c : decode rest`: the byte stands for itself, as ISO-8859-1.
            None => {
                out.push(byte as char);
                i += 1;
            }
        }
    }
    out
}

/// `construct`: accumulate `n` continuation bytes onto `x`, or fail.
fn construct_codepoint(x: u32, n: u32, bytes: &[u8], i: usize) -> Option<(u32, usize)> {
    if n == 0 {
        // `guard $ x <= 0x10FFFF`
        return if x <= 0x10FFFF { Some((x, i)) } else { None };
    }
    let byte = *bytes.get(i)?;
    if (0x80..=0xBF).contains(&byte) {
        construct_codepoint((x << 6) | u32::from(byte & 0x3F), n - 1, bytes, i + 1)
    } else {
        None
    }
}

/// `mockedSystemInterface`: a fixed list of (name, contents) pairs, with names
/// resolved to themselves. Exported for the same reason the Haskell exports it:
/// the checker's own tests source files that do not exist on disk.
#[derive(Debug, Default, Clone)]
pub struct MockSystemInterface {
    files: Vec<(String, String)>,
}

impl MockSystemInterface {
    pub fn new(files: &[(&str, &str)]) -> MockSystemInterface {
        MockSystemInterface {
            files: files
                .iter()
                .map(|(n, c)| ((*n).to_string(), (*c).to_string()))
                .collect(),
        }
    }
}

impl SystemInterface for MockSystemInterface {
    fn read_file(
        &self,
        _external_sources: Option<bool>,
        file: &str,
    ) -> Result<String, ErrorMessage> {
        match self.files.iter().find(|(n, _)| n == file) {
            Some((_, contents)) => Ok(contents.clone()),
            None => Err("File not included in mock.".to_string()),
        }
    }

    fn find_source(
        &self,
        _current_script: &str,
        _external_sources: Option<bool>,
        _source_paths: &[String],
        name: &str,
    ) -> String {
        name.to_string()
    }
}

/// `ShellCheck.Interface.Shell`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Shell {
    Ksh,
    Sh,
    Bash,
    Dash,
    BusyboxSh,
}

/// `ShellCheck.Interface.ExecutionMode`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionMode {
    Executed,
    Sourced,
}

/// `ShellCheck.Interface.Severity`.
///
/// The Haskell `deriving Ord` orders constructors in declaration order:
/// `ErrorC < WarningC < InfoC < StyleC`. That ordering is used both for
/// `csMinSeverity` comparisons (`severity <= minSeverity`) and for sorting
/// output, so the derived Rust `Ord` must match it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Severity {
    ErrorC,
    WarningC,
    InfoC,
    StyleC,
}

impl Severity {
    /// Lowercase name used by JSON/GCC formatters ("error", "warning", ...).
    pub fn as_str(self) -> &'static str {
        match self {
            Severity::ErrorC => "error",
            Severity::WarningC => "warning",
            Severity::InfoC => "info",
            Severity::StyleC => "style",
        }
    }
}

/// `ShellCheck.Interface.Position`.
///
/// 1-based line and column; columns count tabs as 8. Derived `Ord` compares
/// (file, line, column) lexicographically as in Haskell.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Position {
    pub file: String,
    pub line: i64,
    pub column: i64,
}

impl Default for Position {
    fn default() -> Self {
        // newPosition
        Position {
            file: String::new(),
            line: 1,
            column: 1,
        }
    }
}

/// `ShellCheck.Interface.Comment`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment {
    pub severity: Severity,
    pub code: Code,
    pub message: String,
}

impl Default for Comment {
    fn default() -> Self {
        // newComment
        Comment {
            severity: Severity::StyleC,
            code: 0,
            message: String::new(),
        }
    }
}

/// `ShellCheck.Interface.InsertionPoint`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InsertionPoint {
    InsertBefore,
    InsertAfter,
}

/// `ShellCheck.Interface.Replacement`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Replacement {
    pub start: Position,
    pub end: Position,
    pub string: String,
    /// Highest precedence applied first.
    pub precedence: i32,
    pub insertion_point: InsertionPoint,
}

impl Default for Replacement {
    fn default() -> Self {
        // newReplacement
        Replacement {
            start: Position::default(),
            end: Position::default(),
            string: String::new(),
            precedence: 1,
            insertion_point: InsertionPoint::InsertAfter,
        }
    }
}

/// `ShellCheck.Interface.Fix`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Fix {
    pub replacements: Vec<Replacement>,
}

/// `ShellCheck.Interface.PositionedComment`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PositionedComment {
    pub start: Position,
    pub end: Position,
    pub comment: Comment,
    pub fix: Option<Fix>,
}

/// `ShellCheck.Interface.TokenComment`: a comment attached to an AST node id,
/// resolved to a position later via the token position map.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenComment {
    pub id: crate::ast::Id,
    pub comment: Comment,
    pub fix: Option<Fix>,
}

/// `ShellCheck.Interface.ColorOption`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ColorOption {
    ColorAuto,
    ColorAlways,
    ColorNever,
}

/// A half-open range of codes `[from, to)`, as carried by
/// `Annotation.DisableComment from to`. `disable=SC2086` is the single-code
/// range `2086..2087`, `disable=SC1000-SC2000` is `1000..2000`, and
/// `disable=all` is `0..1000000`. Membership is tested, never enumerated:
/// `shouldIgnoreCode`/`contextItemDisablesCode` compare against the endpoints
/// (`code >= n && code < m`), so an enormous range costs nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DisableRange {
    pub from: Code,
    pub to: Code,
}

impl DisableRange {
    /// `disabling' (DisableComment n m) = code >= n && code < m`.
    pub fn contains(&self, code: Code) -> bool {
        code >= self.from && code < self.to
    }
}

/// A configuration file that failed to parse, as reported by SC1134.
///
/// The Haskell driver reads the rc file inside the parser
/// (`Parser.readConfigFile`), so a failure there becomes a parse problem on the
/// script being checked. This port reads rc files in the CLI, so the failure
/// travels on the spec instead and the checker emits the comment; the message
/// is assembled exactly as `errorFor` does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RcParseProblem {
    /// The rc file path, as it was used to open the file.
    pub filename: String,
    /// 1-based line of the parse failure (`sourceLine $ errorPos err`).
    pub line: i64,
    /// `getStringFromParsec`'s suggestion: the explicit `fail` message plus a
    /// period, or empty when the failure carried no message.
    pub suggestion: String,
}

/// What an rc file contributes to a check that the other `CheckSpec` fields
/// cannot express.
///
/// Upstream the rc file is read by the parser and its directives become
/// annotations on the root `T_Annotation`, so `shell`, `extended-analysis` and
/// `enable` land on the existing spec fields and only these two need a home of
/// their own.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RcDirectives {
    /// Code ranges disabled by `disable=` directives.
    ///
    /// As `DisableComment` annotations upstream, these suppress a code wherever
    /// it comes from and regardless of `csIncludedWarnings`. They are kept as
    /// endpoints, never enumerated: the range may be arbitrarily wide.
    pub disabled_ranges: Vec<DisableRange>,
    /// Set when the rc file itself could not be parsed; the checker turns it
    /// into the SC1134 comment and no rc directive takes effect.
    pub parse_problem: Option<RcParseProblem>,
}

/// `ShellCheck.Interface.CheckSpec`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckSpec {
    pub filename: String,
    pub script: String,
    pub check_sourced: bool,
    pub ignore_rc: bool,
    pub excluded_warnings: Vec<Code>,
    pub included_warnings: Option<Vec<Code>>,
    pub shell_type_override: Option<Shell>,
    pub min_severity: Severity,
    pub extended_analysis: Option<bool>,
    pub optional_checks: Vec<String>,
    /// Whatever an rc file contributed that has no `csXxx` counterpart. Boxed
    /// so that a spec without an rc file costs one pointer.
    pub rc: Option<Box<RcDirectives>>,
}

impl Default for CheckSpec {
    fn default() -> Self {
        // emptyCheckSpec
        CheckSpec {
            filename: String::new(),
            script: String::new(),
            check_sourced: false,
            ignore_rc: false,
            excluded_warnings: Vec::new(),
            included_warnings: None,
            shell_type_override: None,
            min_severity: Severity::StyleC,
            extended_analysis: None,
            optional_checks: Vec::new(),
            rc: None,
        }
    }
}

/// `ShellCheck.Interface.CheckResult`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CheckResult {
    pub filename: String,
    pub comments: Vec<PositionedComment>,
}

/// Position span map: token id -> (start, end).
pub type PositionMap = BTreeMap<crate::ast::Id, (Position, Position)>;

#[cfg(test)]
mod decode_tests {
    use super::decode_bytes;

    #[test]
    fn ascii_and_valid_utf8_decode_to_themselves() {
        assert_eq!(decode_bytes(b"echo hi\n"), "echo hi\n");
        // "caf\u{e9}" as UTF-8 is one character, not two.
        assert_eq!(decode_bytes(b"caf\xc3\xa9"), "caf\u{e9}");
        assert_eq!(
            decode_bytes("\u{FEFF}#!/bin/sh".as_bytes()),
            "\u{FEFF}#!/bin/sh"
        );
        assert_eq!(decode_bytes("\u{1F600}".as_bytes()).chars().count(), 1);
    }

    #[test]
    fn an_invalid_byte_stands_for_itself_and_shifts_nothing() {
        // `decodeString`'s ISO-8859-1 fallback: one character per stray byte,
        // so every column after it is the one the oracle reports.
        assert_eq!(decode_bytes(b"echo \xff\xfe x"), "echo \u{ff}\u{fe} x");
        assert_eq!(decode_bytes(b"echo \xff\xfe x").chars().count(), 9);
        assert_eq!(decode_bytes(b"\xff"), "\u{ff}");
        // A lead byte with a missing or bad continuation is not consumed.
        assert_eq!(decode_bytes(b"\xc3"), "\u{c3}");
        assert_eq!(decode_bytes(b"\xc3z"), "\u{c3}z");
        assert_eq!(decode_bytes(b"\xe2\x82"), "\u{e2}\u{82}");
        // `num >= 0xF8` is rejected outright, as is a continuation byte alone.
        assert_eq!(decode_bytes(b"\xf8\x80"), "\u{f8}\u{80}");
        assert_eq!(decode_bytes(b"\x80"), "\u{80}");
    }

    #[test]
    fn overlong_and_out_of_range_sequences_follow_upstream() {
        // `construct` checks only the continuation bytes and `x <= 0x10FFFF`,
        // so an overlong encoding decodes to its codepoint...
        assert_eq!(decode_bytes(b"\xc0\x80"), "\0");
        // ...and anything above the maximum fails the guard and falls back to
        // raw bytes: U+110000 is one past the last codepoint.
        assert_eq!(
            decode_bytes(b"\xf4\x90\x80\x80"),
            "\u{f4}\u{90}\u{80}\u{80}"
        );
        assert_eq!(decode_bytes(b"\xf4\x8f\xbf\xbf"), "\u{10FFFF}");
        assert_eq!(
            decode_bytes(b"\xf7\xbf\xbf\xbf"),
            "\u{f7}\u{bf}\u{bf}\u{bf}"
        );
        // A surrogate is a codepoint Haskell's `chr` accepts and Rust's `char`
        // cannot: still exactly one character, so columns are unaffected.
        assert_eq!(decode_bytes(b"\xed\xa0\x80"), "\u{FFFD}");
    }
}
