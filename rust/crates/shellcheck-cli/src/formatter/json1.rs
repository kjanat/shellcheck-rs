//! Port of `ShellCheck.Formatter.JSON1`: the `--format=json1` output.
//!
//! Emits a single `{"comments":[...]}` object over all analyzed files, matching
//! the Haskell formatter's field set. Key ordering is irrelevant to the
//! conformance harness (it compares parsed JSON), but values must match exactly.

use serde::Serialize;
use shellcheck_rs::interface::{InsertionPoint, PositionedComment};

#[derive(Serialize)]
pub struct Json1Output {
    pub comments: Vec<Json1Comment>,
}

#[derive(Serialize)]
pub struct Json1Comment {
    pub file: String,
    pub line: i64,
    #[serde(rename = "endLine")]
    pub end_line: i64,
    pub column: i64,
    #[serde(rename = "endColumn")]
    pub end_column: i64,
    pub level: String,
    pub code: i64,
    pub message: String,
    pub fix: Option<Json1Fix>,
}

#[derive(Serialize)]
pub struct Json1Fix {
    pub replacements: Vec<Json1Replacement>,
}

/// Fields in alphabetical order to match aeson's sorted-key `object` encoding
/// of `Replacement` (which defines only `toJSON`), so json1 is byte-exact.
#[derive(Serialize)]
pub struct Json1Replacement {
    pub column: i64,
    #[serde(rename = "endColumn")]
    pub end_column: i64,
    #[serde(rename = "endLine")]
    pub end_line: i64,
    #[serde(rename = "insertionPoint")]
    pub insertion_point: String,
    pub line: i64,
    pub precedence: i32,
    pub replacement: String,
}

pub fn to_comment(pc: &PositionedComment) -> Json1Comment {
    Json1Comment {
        file: pc.start.file.clone(),
        line: pc.start.line,
        end_line: pc.end.line,
        column: pc.start.column,
        end_column: pc.end.column,
        level: pc.comment.severity.as_str().to_string(),
        code: pc.comment.code,
        message: pc.comment.message.clone(),
        fix: pc.fix.as_ref().map(|f| Json1Fix {
            replacements: f
                .replacements
                .iter()
                .map(|r| Json1Replacement {
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

pub fn render(comments: &[PositionedComment]) -> String {
    let out = Json1Output {
        comments: comments.iter().map(to_comment).collect(),
    };
    serde_json::to_string(&out).unwrap()
}
