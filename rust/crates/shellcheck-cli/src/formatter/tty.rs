//! Port of `ShellCheck.Formatter.TTY`: the default human-readable output.
//!
//! Reproduces the "In <file> line N:" context blocks, the caret/underline
//! arrows, the "Did you mean:" fix excerpts, and the trailing "For more
//! information:" wiki list. Coloring is gated on the resolved color mode
//! (see `super::ColorFunc`).

use shellcheck_rs::interface::{PositionedComment, Severity};

use super::ColorFunc;
use super::fixer::{apply_fix, fix_mconcat, lines as hs_lines, map_positions, unlines};

const WIKI_LINK: &str = "https://www.shellcheck.net/wiki/";

/// Codes considered "uninteresting" (generic parser errors), downranked in the
/// wiki summary.
const UNINTERESTING: &[i64] = &[1009, 1019, 1036, 1047, 1062, 1070, 1072, 1073, 1088, 1089];

/// A wiki-summary entry: (ranking, code, message). Ranking is
/// (rank_char, severity, code) to match the Haskell `Ranking`.
#[derive(Clone)]
pub struct WikiEntry {
    ranking: (char, Severity, i64),
    code: i64,
    message: String,
}

fn severity_text(sev: Severity) -> &'static str {
    match sev {
        Severity::ErrorC => "error",
        Severity::WarningC => "warning",
        Severity::InfoC => "info",
        Severity::StyleC => "style",
    }
}

fn rank_error(c: &PositionedComment) -> (char, Severity, i64) {
    let rank = if UNINTERESTING.contains(&c.comment.code) {
        'Z'
    } else {
        'A'
    };
    (rank, c.comment.severity, c.comment.code)
}

/// `makeArrow` + `cuteIndent`.
fn cute_indent(c: &PositionedComment) -> String {
    let col = c.start.column;
    let same_line = c.start.line == c.end.line;
    let delta = c.end.column - c.start.column;
    let arrow = if same_line && delta > 2 && delta < 32 {
        let mut a = String::from("^");
        for _ in 0..(delta - 2) {
            a.push('-');
        }
        a.push('^');
        a
    } else {
        "^--".to_string()
    };
    let indent: String = std::iter::repeat(' ')
        .take((col - 1).max(0) as usize)
        .collect();
    format!(
        "{indent}{arrow} SC{} ({}): {}",
        c.comment.code,
        severity_text(c.comment.severity),
        c.comment.message
    )
}

/// `sliceFile`: rebase a fix (and the excerpt lines) to the lines it spans.
fn slice_file(
    fix: &shellcheck_rs::interface::Fix,
    file_lines: &[String],
) -> (shellcheck_rs::interface::Fix, Vec<String>) {
    let mut min_line = i64::MAX;
    let mut max_line = i64::MIN;
    for r in &fix.replacements {
        for p in [&r.start, &r.end] {
            min_line = min_line.min(p.line);
            max_line = max_line.max(p.line);
        }
    }
    if fix.replacements.is_empty() {
        return (fix.clone(), Vec::new());
    }
    let lo = (min_line.max(1)) as usize;
    let hi = (max_line.max(1)) as usize;
    let excerpt: Vec<String> = (lo..=hi)
        .map(|i| file_lines.get(i - 1).cloned().unwrap_or_default())
        .collect();
    let adjusted = map_positions(fix, |p| shellcheck_rs::interface::Position {
        line: p.line - min_line + 1,
        ..p.clone()
    });
    (adjusted, excerpt)
}

/// Append the "Did you mean:" excerpt for the fixes on this line, if any.
fn show_fixed_string(
    color: &ColorFunc,
    comments: &[&PositionedComment],
    file_lines: &[String],
    out: &mut String,
) {
    let fixes: Vec<shellcheck_rs::interface::Fix> =
        comments.iter().filter_map(|c| c.fix.clone()).collect();
    if fixes.is_empty() {
        return;
    }
    let merged = fix_mconcat(&fixes);
    let (excerpt_fix, excerpt) = slice_file(&merged, file_lines);
    out.push_str(&color("message", "Did you mean:"));
    out.push('\n');
    // `putStrLn $ unlines $ applyFix ...`: unlines adds a trailing '\n', and
    // putStrLn adds one more.
    out.push_str(&unlines(&apply_fix(&excerpt_fix, &excerpt)));
    out.push('\n');
}

/// Render one file's comments (already sorted), accumulating wiki entries.
pub fn render_file(
    color: &ColorFunc,
    filename: &str,
    contents: &str,
    comments: &[PositionedComment],
    wiki: &mut Vec<WikiEntry>,
    out: &mut String,
) {
    for c in comments {
        wiki.push(WikiEntry {
            ranking: rank_error(c),
            code: c.comment.code,
            message: c.comment.message.clone(),
        });
    }

    let file_lines = hs_lines(contents);
    let line_count = file_lines.len() as i64;

    // Group consecutive comments by start line (they are already sorted).
    let mut i = 0;
    while i < comments.len() {
        let line_num = comments[i].start.line;
        let mut j = i;
        while j < comments.len() && comments[j].start.line == line_num {
            j += 1;
        }
        let group: Vec<&PositionedComment> = comments[i..j].iter().collect();

        let line = if line_num < 1 || line_num > line_count {
            String::new()
        } else {
            file_lines[(line_num - 1) as usize].clone()
        };

        out.push('\n');
        out.push_str(&color(
            "message",
            &format!("In {filename} line {line_num}:"),
        ));
        out.push('\n');
        out.push_str(&color("source", &line));
        out.push('\n');
        for c in &group {
            out.push_str(&color(severity_text(c.comment.severity), &cute_indent(c)));
            out.push('\n');
        }
        out.push('\n');
        show_fixed_string(color, &group, &file_lines, out);

        i = j;
    }
}

/// `outputWiki`: the trailing "For more information:" list. Consumes the
/// accumulated entries.
pub fn render_wiki(entries: &[WikiEntry], wiki_link_count: usize, out: &mut String) {
    // sort by ranking, then nub by ranking (keep first), then take N.
    let mut sorted = entries.to_vec();
    sorted.sort_by(|a, b| a.ranking.cmp(&b.ranking));
    let mut seen: Vec<(char, Severity, i64)> = Vec::new();
    let mut deduped: Vec<&WikiEntry> = Vec::new();
    for e in &sorted {
        if !seen.contains(&e.ranking) {
            seen.push(e.ranking);
            deduped.push(e);
        }
    }
    let issues: Vec<&WikiEntry> = deduped.into_iter().take(wiki_link_count).collect();
    if issues.is_empty() {
        return;
    }
    out.push_str("For more information:\n");
    for e in issues {
        out.push_str(&format!(
            "  {WIKI_LINK}SC{} -- {}\n",
            e.code,
            shorten(&e.message)
        ));
    }
}

fn shorten(msg: &str) -> String {
    const LIMIT: usize = 36;
    let len = msg.chars().count();
    if len < LIMIT {
        msg.to_string()
    } else {
        let head: String = msg.chars().take(LIMIT - 3).collect();
        format!("{head}...")
    }
}
