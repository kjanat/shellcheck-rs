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
