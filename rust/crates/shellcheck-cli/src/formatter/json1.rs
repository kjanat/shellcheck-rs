//! Port of `ShellCheck.Formatter.JSON1`: the `--format=json1` output.
//!
//! Emits a single `{"comments":[...]}` object over all analyzed files, matching
//! the Haskell formatter's field set. Key ordering is irrelevant to the
//! conformance harness (it compares parsed JSON), but values must match exactly.

use serde::Serialize;
use shellcheck_rs::interface::{InsertionPoint, PositionedComment};

/// The json1 document: `{"comments": [...]}`.
#[derive(Serialize)]
pub struct Output {
    /// Every comment of every checked file.
    pub comments: Vec<Comment>,
}

/// One comment, in the field order of the Haskell `toEncoding`.
#[derive(Serialize)]
pub struct Comment {
    /// The file the comment starts in.
    pub file: String,
    /// The 1-based line it starts on.
    pub line: i64,
    /// The 1-based line it ends on.
    #[serde(rename = "endLine")]
    pub end_line: i64,
    /// The 1-based column it starts at.
    pub column: i64,
    /// The 1-based column it ends at.
    #[serde(rename = "endColumn")]
    pub end_column: i64,
    /// The severity: `error`, `warning`, `info` or `style`.
    pub level: String,
    /// The SC code, without the `SC` prefix.
    pub code: i64,
    /// The message text.
    pub message: String,
    /// The suggested fix, or `null`.
    pub fix: Option<Fix>,
}

/// A fix: the replacements that make it.
#[derive(Serialize)]
pub struct Fix {
    /// The replacements, in the order the checker produced them.
    pub replacements: Vec<Replacement>,
}

/// Fields in alphabetical order to match aeson's sorted-key `object` encoding
/// of `Replacement` (which defines only `toJSON`), so json1 is byte-exact.
#[derive(Serialize)]
pub struct Replacement {
    /// The 1-based column the replaced range starts at.
    pub column: i64,
    /// The 1-based column the replaced range ends at.
    #[serde(rename = "endColumn")]
    pub end_column: i64,
    /// The 1-based line the replaced range ends on.
    #[serde(rename = "endLine")]
    pub end_line: i64,
    /// `afterEnd` or `beforeStart`.
    #[serde(rename = "insertionPoint")]
    pub insertion_point: String,
    /// The 1-based line the replaced range starts on.
    pub line: i64,
    /// The precedence that orders overlapping replacements.
    pub precedence: i32,
    /// The text that replaces the range.
    pub replacement: String,
}

/// The json form of one comment, shared with the legacy `json` formatter.
#[must_use]
pub fn to_comment(pc: &PositionedComment) -> Comment {
    Comment {
        file: pc.start.file.clone(),
        line: pc.start.line,
        end_line: pc.end.line,
        column: pc.start.column,
        end_column: pc.end.column,
        level: pc.comment.severity.as_str().to_string(),
        code: pc.comment.code,
        message: pc.comment.message.clone(),
        fix: pc.fix.as_ref().map(|f| Fix {
            replacements: f
                .replacements
                .iter()
                .map(|r| Replacement {
                    column: r.start.column,
                    end_column: r.end.column,
                    end_line: r.end.line,
                    line: r.start.line,
                    insertion_point: match r.insertion_point {
                        InsertionPoint::InsertAfter => "afterEnd".to_string(),
                        InsertionPoint::InsertBefore => "beforeStart".to_string(),
                    },
                    precedence: r.precedence,
                    replacement: r.string.clone(),
                })
                .collect(),
        }),
    }
}

/// The json1 document for `comments`.
///
/// # Errors
///
/// When `serde_json` fails to serialize the document.
pub fn render(comments: &[PositionedComment]) -> serde_json::Result<String> {
    serde_json::to_string(&Output {
        comments: comments.iter().map(to_comment).collect(),
    })
}
