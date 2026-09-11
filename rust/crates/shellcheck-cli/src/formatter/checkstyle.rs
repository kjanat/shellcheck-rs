//! Port of `ShellCheck.Formatter.CheckStyle`: CheckStyle 4.3 XML output.

use shellcheck_rs::interface::{PositionedComment, Severity};

use super::fixer::make_non_virtual;

pub const HEADER: &str = "<?xml version='1.0' encoding='UTF-8'?>\n<checkstyle version='4.3'>\n";
pub const FOOTER: &str = "</checkstyle>\n";

/// `escape'`: keep ASCII letters, digits, space, `.` and `/`; everything else
/// becomes a numeric character reference.
fn escape(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        let ok = c.is_ascii_uppercase()
            || c.is_ascii_lowercase()
            || c.is_ascii_digit()
            || c == ' '
            || c == '.'
            || c == '/';
        if ok {
            out.push(c);
        } else {
            out.push_str(&format!("&#{};", c as u32));
        }
    }
    out
}

/// `attr s v = s ++ "='" ++ escape v ++ "' "` (note the trailing space).
fn attr(name: &str, value: &str) -> String {
    format!("{name}='{}' ", escape(value))
}

fn severity(sev: Severity) -> &'static str {
    match sev {
        Severity::ErrorC => "error",
        Severity::WarningC => "warning",
        _ => "info",
    }
}

fn format_comment(c: &PositionedComment) -> String {
    format!(
        "<error {}{}{}{}{}/>\n",
        attr("line", &c.start.line.to_string()),
        attr("column", &c.start.column.to_string()),
        attr("severity", severity(c.comment.severity)),
        attr("message", &c.comment.message),
        attr("source", &format!("ShellCheck.SC{}", c.comment.code)),
    )
}

/// Render one `<file>` block (with its comments, possibly empty).
pub fn render_file(filename: &str, contents: &str, comments: &[PositionedComment], out: &mut String) {
    let untabbed = make_non_virtual(comments, contents);
    out.push_str(&format!("<file {}>\n", attr("name", filename)));
    for c in &untabbed {
        out.push_str(&format_comment(c));
    }
    out.push_str("</file>\n");
}

/// A `<file>` block describing a read failure.
pub fn render_failure(file: &str, msg: &str) -> String {
    format!(
        "<file {}>\n<error {}{}{}{}{}/>\n</file>\n",
        attr("name", file),
        attr("line", "1"),
        attr("column", "1"),
        attr("severity", "error"),
        attr("message", msg),
        attr("source", "ShellCheck"),
    )
}
