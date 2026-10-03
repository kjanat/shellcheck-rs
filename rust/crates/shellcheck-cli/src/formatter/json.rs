//! Legacy `--format=json` array formatter (ShellCheck.Formatter.JSON port).
//!
//! Differences from `json1`:
//! - Keeps tabs (does not untab).
//! - Emits a bare JSON array.
//!
//! Object keys match `json1` encodings:
//! - Comment keys follow Haskell declaration order.
//! - Replacement keys are sorted alphabetically (aeson standard).

use shellcheck_rs::interface::PositionedComment;

use super::json1;

/// The legacy json array for `comments`.
///
/// # Errors
///
/// When `serde_json` fails to serialize the array.
pub fn render(comments: &[PositionedComment]) -> serde_json::Result<String> {
    let out: Vec<json1::Comment> = comments.iter().map(json1::to_comment).collect();
    serde_json::to_string(&out)
}
