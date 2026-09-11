//! Port of `ShellCheck.Formatter.GCC`: `file:line:col: severity: message [SCxxxx]`.
//!
//! Comments are untabbed (`makeNonVirtual`) before formatting. Any severity
//! other than error/warning is rendered as `note`, and internal newlines in the
//! message are removed (`concat . lines`).

use shellcheck_rs::interface::{PositionedComment, Severity};

use super::fixer::make_non_virtual;

fn strip_newlines(msg: &str) -> String {
    // `concat . lines`: join the lines with nothing between them.
    super::fixer::lines(msg).concat()
}

fn format_comment(filename: &str, c: &PositionedComment) -> String {
    let severity = match c.comment.severity {
        Severity::ErrorC => "error",
        Severity::WarningC => "warning",
        _ => "note",
    };
    format!(
        "{}:{}:{}: {}: {} [SC{}]",
        filename,
        c.start.line,
        c.start.column,
        severity,
        strip_newlines(&c.comment.message),
        c.comment.code
    )
}

/// Render one file's comments (already sorted). `contents` is the file source,
/// used for tab realignment.
pub fn render_file(filename: &str, contents: &str, comments: &[PositionedComment], out: &mut String) {
    let untabbed = make_non_virtual(comments, contents);
    for c in &untabbed {
        out.push_str(&format_comment(filename, c));
        out.push('\n');
    }
}

/// GCC-style error line for a file that could not be read.
pub fn render_failure(file: &str, msg: &str) -> String {
    format!("{file}: {msg}")
}
