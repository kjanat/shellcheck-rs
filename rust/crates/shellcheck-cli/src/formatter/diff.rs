//! Port of `ShellCheck.Formatter.Diff`: unified-diff autofix output.
//!
//! Builds a line diff between the source and its autofixed form, groups it into
//! hunks with three lines of context (matching `groupDiff`), and renders a
//! `git`-style unified diff. A `no-newline-at-end-of-file` marker is emitted
//! when the last hunk covers a final line that lacked a trailing newline.

use shellcheck_rs::interface::{Fix, PositionedComment};

use super::fixer::{apply_fix, fix_mconcat, lines as hs_lines, unlines};

const CONTEXT: i64 = 3;

const RED: i32 = 31;
const GREEN: i32 = 32;
const CYAN: i32 = 36;
const BOLD: i32 = 1;

fn ansi(n: i32) -> String {
    format!("\x1B[{n}m")
}

/// Colorize with the given ansi code, or pass through when color is off.
fn colorize(use_color: bool, n: i32, s: &str) -> String {
    if use_color {
        format!("{}{s}{}", ansi(n), ansi(0))
    } else {
        s.to_string()
    }
}

#[derive(Clone, PartialEq, Debug)]
enum DiffElem {
    Both(String),
    First(String),
    Second(String),
}

fn is_both(d: &DiffElem) -> bool {
    matches!(d, DiffElem::Both(_))
}

/// Line diff: common lines are `Both`, deletions `First`, insertions `Second`.
/// On a tie the deletion is preferred, grouping deletions before insertions,
/// matching `Data.Algorithm.Diff.getDiff` for the whole-line replacements that
/// autofixes produce.
fn get_diff(old: &[String], new: &[String]) -> Vec<DiffElem> {
    let n = old.len();
    let m = new.len();
    let mut dp = vec![vec![0i64; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            dp[i][j] = if old[i] == new[j] {
                dp[i + 1][j + 1] + 1
            } else {
                dp[i + 1][j].max(dp[i][j + 1])
            };
        }
    }
    let mut out = Vec::new();
    let (mut i, mut j) = (0usize, 0usize);
    while i < n && j < m {
        if old[i] == new[j] {
            out.push(DiffElem::Both(old[i].clone()));
            i += 1;
            j += 1;
        } else if dp[i + 1][j] >= dp[i][j + 1] {
            out.push(DiffElem::First(old[i].clone()));
            i += 1;
        } else {
            out.push(DiffElem::Second(new[j].clone()));
            j += 1;
        }
    }
    while i < n {
        out.push(DiffElem::First(old[i].clone()));
        i += 1;
    }
    while j < m {
        out.push(DiffElem::Second(new[j].clone()));
        j += 1;
    }
    out
}

fn prepend(x: DiffElem, current: Vec<DiffElem>) -> Vec<DiffElem> {
    let mut v = Vec::with_capacity(current.len() + 1);
    v.push(x);
    v.extend(current);
    v
}

fn split_at_ctx(current: &[DiffElem], k: usize) -> (Vec<DiffElem>, Vec<DiffElem>) {
    let head: Vec<DiffElem> = current.iter().take(k).cloned().collect();
    let tail: Vec<DiffElem> = current.iter().skip(k).cloned().collect();
    (head, tail)
}

fn reversed(mut v: Vec<DiffElem>) -> Vec<DiffElem> {
    v.reverse();
    v
}

fn group_diff(diffs: &[DiffElem]) -> Vec<(bool, Vec<DiffElem>)> {
    hunt(Vec::new(), diffs)
        .into_iter()
        .filter(|(_, l)| !l.is_empty())
        .collect()
}

fn hunt(current: Vec<DiffElem>, list: &[DiffElem]) -> Vec<(bool, Vec<DiffElem>)> {
    if list.is_empty() {
        return vec![(false, reversed(current))];
    }
    if is_both(&list[0]) {
        return hunt(prepend(list[0].clone(), current), &list[1..]);
    }
    let (context, previous) = split_at_ctx(&current, CONTEXT as usize);
    let mut out = vec![(false, reversed(previous))];
    out.extend(gather(context, 0, list));
    out
}

fn gather(current: Vec<DiffElem>, n: i64, list: &[DiffElem]) -> Vec<(bool, Vec<DiffElem>)> {
    if list.is_empty() {
        let take = (n - CONTEXT).max(0) as usize;
        let (extras, patch) = split_at_ctx(&current, take);
        return vec![(true, reversed(patch)), (false, reversed(extras))];
    }
    if is_both(&list[0]) && n == CONTEXT * 2 {
        let (context, previous) = split_at_ctx(&current, CONTEXT as usize);
        let mut out = vec![(true, reversed(previous))];
        out.extend(hunt(context, list));
        return out;
    }
    if is_both(&list[0]) {
        return gather(prepend(list[0].clone(), current), n + 1, &list[1..]);
    }
    gather(prepend(list[0].clone(), current), 0, &list[1..])
}

fn count_delta(run: &[DiffElem]) -> (i64, i64) {
    let mut left = 0;
    let mut right = 0;
    for d in run {
        match d {
            DiffElem::Both(_) => {
                left += 1;
                right += 1;
            }
            DiffElem::First(_) => left += 1,
            DiffElem::Second(_) => right += 1,
        }
    }
    (left, right)
}

struct DiffRegion {
    left: (i64, i64),
    right: (i64, i64),
    diffs: Vec<DiffElem>,
}

fn find_regions(hunks: &[(bool, Vec<DiffElem>)]) -> Vec<DiffRegion> {
    let mut out = Vec::new();
    let mut left = 1i64;
    let mut right = 1i64;
    for (output, run) in hunks {
        let (dl, dr) = count_delta(run);
        if *output {
            out.push(DiffRegion { left: (left, dl), right: (right, dr), diffs: run.clone() });
        }
        left += dl;
        right += dr;
    }
    out
}

#[derive(Clone, Copy, PartialEq)]
enum Lf {
    Missing,
    Ok,
}

const NO_LF: &str = "\\ No newline at end of file";

fn format_line(use_color: bool, d: &DiffElem) -> String {
    match d {
        DiffElem::Both(x) => format!(" {x}"),
        DiffElem::First(x) => colorize(use_color, RED, &format!("-{x}")),
        DiffElem::Second(x) => colorize(use_color, GREEN, &format!("+{x}")),
    }
}

fn get_strings(use_color: bool, lf: Lf, list: &[DiffElem]) -> Vec<String> {
    match lf {
        Lf::Ok => list.iter().map(|d| format_line(use_color, d)).collect(),
        Lf::Missing => {
            if let Some(first) = list.first() {
                match first {
                    DiffElem::Both(_) | DiffElem::First(_) => {
                        let mut out = vec![NO_LF.to_string()];
                        out.extend(list.iter().map(|d| format_line(use_color, d)));
                        out
                    }
                    DiffElem::Second(_) => {
                        let mut out = vec![format_line(use_color, first)];
                        out.extend(get_strings(use_color, Lf::Missing, &list[1..]));
                        out
                    }
                }
            } else {
                Vec::new()
            }
        }
    }
}

fn tup((a, b): (i64, i64)) -> String {
    format!("{a},{b}")
}

fn format_region(use_color: bool, lf: Lf, region: &DiffRegion) -> String {
    let header = colorize(
        use_color,
        CYAN,
        &format!("@@ -{} +{} @@", tup(region.left), tup(region.right)),
    );
    let rev: Vec<DiffElem> = region.diffs.iter().rev().cloned().collect();
    let body = reversed_strings(get_strings(use_color, lf, &rev));
    let mut all = vec![header];
    all.extend(body);
    unlines(&all)
}

fn reversed_strings(mut v: Vec<String>) -> Vec<String> {
    v.reverse();
    v
}

fn normalize_path(path: &str) -> String {
    path.chars().map(|c| if c == std::path::MAIN_SEPARATOR { '/' } else { c }).collect()
}

/// `"a" </> name`: on POSIX, an absolute `name` (leading `/`) discards the
/// prefix, matching Haskell's `System.FilePath.</>`.
fn join_prefix(prefix: &str, name: &str) -> String {
    if name.starts_with('/') {
        name.to_string()
    } else {
        format!("{prefix}/{name}")
    }
}

fn format_doc(use_color: bool, name: &str, lf: Lf, regions: &[DiffRegion]) -> String {
    let mut s = String::new();
    s.push_str(&colorize(use_color, BOLD, &format!("--- {}", normalize_path(&join_prefix("a", name)))));
    s.push('\n');
    s.push_str(&colorize(use_color, BOLD, &format!("+++ {}", normalize_path(&join_prefix("b", name)))));
    s.push('\n');
    if regions.is_empty() {
        return s;
    }
    let (most, last) = regions.split_at(regions.len() - 1);
    for r in most {
        s.push_str(&format_region(use_color, Lf::Ok, r));
    }
    for r in last {
        s.push_str(&format_region(use_color, lf, r));
    }
    s
}

fn has_trailing_linefeed(s: &str) -> bool {
    s.is_empty() || s.ends_with('\n')
}

fn covers_last_line(regions: &[(bool, Vec<DiffElem>)]) -> bool {
    regions.last().map(|(o, _)| *o).unwrap_or(false)
}

/// `makeDiff` + `formatDoc`: the unified diff for one file's merged fix.
fn make_diff_string(use_color: bool, name: &str, contents: &str, fix: &Fix) -> String {
    let old = hs_lines(contents);
    let new = apply_fix(fix, &old);
    let diffs = get_diff(&old, &new);
    let hunks = group_diff(&diffs);
    let lf = if covers_last_line(&hunks) && !has_trailing_linefeed(contents) {
        Lf::Missing
    } else {
        Lf::Ok
    };
    let regions = find_regions(&hunks);
    format_doc(use_color, name, lf, &regions)
}

/// Result of rendering: the diff text and whether anything was reported.
pub struct DiffOutput {
    pub text: String,
    pub reported: bool,
}

/// Render the diff for one file's comments (already the file's own fixes).
pub fn render_file(use_color: bool, filename: &str, contents: &str, comments: &[PositionedComment]) -> DiffOutput {
    let fixes: Vec<Fix> = comments.iter().filter_map(|c| c.fix.clone()).collect();
    if fixes.is_empty() {
        return DiffOutput { text: String::new(), reported: false };
    }
    let merged = fix_mconcat(&fixes);
    if merged.replacements.is_empty() {
        return DiffOutput { text: String::new(), reported: false };
    }
    // `putStrLn $ formatDoc ...` adds a trailing newline.
    let mut text = make_diff_string(use_color, filename, contents, &merged);
    text.push('\n');
    DiffOutput { text, reported: true }
}

/// The footer warning printed to stderr when issues exist but none are fixable.
pub const NONE_FIXABLE_MSG: &str =
    "Issues were detected, but none were auto-fixable. Use another format to see them.";

pub fn color_bold_red(use_color: bool, s: &str) -> String {
    colorize(use_color, BOLD, &colorize(use_color, RED, s))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(n: i64) -> DiffElem {
        DiffElem::Both(n.to_string())
    }
    fn l(n: i64) -> DiffElem {
        DiffElem::First(n.to_string())
    }
    fn r(n: i64) -> DiffElem {
        DiffElem::Second(n.to_string())
    }

    fn keys(g: &[(bool, Vec<DiffElem>)]) -> Vec<(bool, Vec<DiffElem>)> {
        g.to_vec()
    }

    #[test]
    fn identifies_proper_context() {
        let got = group_diff(&[b(1), b(2), b(3), b(4), l(5), b(6), b(7), b(8), b(9)]);
        let want = vec![
            (false, vec![b(1)]),
            (true, vec![b(2), b(3), b(4), l(5), b(6), b(7), b(8)]),
            (false, vec![b(9)]),
        ];
        assert!(keys(&got) == want);
    }

    #[test]
    fn count_deltas_works() {
        assert_eq!(count_delta(&[b(1), l(2), r(3), r(4), b(5)]), (3, 4));
        assert_eq!(count_delta(&[]), (0, 0));
    }

    #[test]
    fn splits_into_multiple_hunks() {
        let got = group_diff(&[l(1), b(1), b(2), b(3), b(4), b(5), b(6), b(7), r(8)]);
        let want = vec![
            (true, vec![l(1), b(1), b(2), b(3)]),
            (false, vec![b(4)]),
            (true, vec![b(5), b(6), b(7), r(8)]),
        ];
        assert!(keys(&got) == want);
    }

    #[test]
    fn whole_line_replacement_groups_deletions_first() {
        let old = vec!["a".to_string(), "b".to_string()];
        let new = vec!["x".to_string(), "y".to_string()];
        let d = get_diff(&old, &new);
        assert_eq!(
            d,
            vec![
                DiffElem::First("a".to_string()),
                DiffElem::First("b".to_string()),
                DiffElem::Second("x".to_string()),
                DiffElem::Second("y".to_string()),
            ]
        );
    }
}
