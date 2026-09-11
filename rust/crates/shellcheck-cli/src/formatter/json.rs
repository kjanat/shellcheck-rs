//! Port of `ShellCheck.Formatter.JSON`: the legacy `--format=json` array form.
//!
//! Unlike `json1`, the legacy formatter does **not** untab (`makeNonVirtual`)
//! and emits a bare JSON array of comments. Comment keys follow the Haskell
//! `toEncoding` declaration order; replacement keys are alphabetical, matching
//! aeson's sorted-key encoding of a plain `object` (Replacement defines only
//! `toJSON`).

use serde::Serialize;
use shellcheck_rs::interface::{InsertionPoint, PositionedComment};

#[derive(Serialize)]
struct JsonComment {
    file: String,
    line: i64,
    #[serde(rename = "endLine")]
    end_line: i64,
    column: i64,
    #[serde(rename = "endColumn")]
    end_column: i64,
    level: String,
    code: i64,
    message: String,
    fix: Option<JsonFix>,
}

#[derive(Serialize)]
struct JsonFix {
    replacements: Vec<JsonReplacement>,
}

/// Fields in alphabetical order to match aeson's sorted-key `object` encoding.
#[derive(Serialize)]
struct JsonReplacement {
    column: i64,
    #[serde(rename = "endColumn")]
    end_column: i64,
    #[serde(rename = "endLine")]
    end_line: i64,
    #[serde(rename = "insertionPoint")]
    insertion_point: String,
    line: i64,
    precedence: i32,
    replacement: String,
}

fn to_comment(pc: &PositionedComment) -> JsonComment {
    JsonComment {
        file: pc.start.file.clone(),
        line: pc.start.line,
        end_line: pc.end.line,
        column: pc.start.column,
        end_column: pc.end.column,
        level: pc.comment.severity.as_str().to_string(),
        code: pc.comment.code,
        message: pc.comment.message.clone(),
        fix: pc.fix.as_ref().map(|f| JsonFix {
            replacements: f
                .replacements
                .iter()
                .map(|r| JsonReplacement {
                    column: r.start.column,
                    end_column: r.end.column,
                    end_line: r.end.line,
                    insertion_point: match r.insertion_point {
                        InsertionPoint::InsertAfter => "afterEnd".to_string(),
                        InsertionPoint::InsertBefore => "beforeStart".to_string(),
                    },
                    line: r.start.line,
                    precedence: r.precedence,
                    replacement: r.string.clone(),
                })
                .collect(),
        }),
    }
}

pub fn render(comments: &[PositionedComment]) -> String {
    let out: Vec<JsonComment> = comments.iter().map(to_comment).collect();
    serde_json::to_string(&out).unwrap()
}
