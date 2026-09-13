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
///
/// The element sequence is the one a full LCS matrix with that tie-break would
/// walk out, but computed in `O(new_lines)` space by Hirschberg's divide and
/// conquer, so a large script with an autofix does not need an
/// `old_lines * new_lines` matrix.
///
/// Modelling: a diff is a monotone path through the `(old, new)` grid, where a
/// step down emits `First`, a step right emits `Second` and a diagonal step
/// emits `Both`. Because matching equal lines is always optimal, the walk takes
/// the diagonal whenever `old[i] == new[j]`; call a path obeying that rule
/// *snake-extended*. The walk is then the snake-extended path of minimal cost
/// (`First`s plus `Second`s) that prefers the downward step whenever both steps
/// are still optimal — and that path is the one whose column is smallest at
/// every row, since the only way to be further left is to take a down step the
/// walk declined, which it never does while down is optimal.
///
/// So the crossing column of the walk at row `a` is the leftmost column `j`
/// there with `cost(start -> (a, j)) + cost((a, j) -> end)` minimal, both halves
/// being single-row sweeps over the same grid. Split the problem at that cell
/// and recurse: a segment of the walk between two of its own cells is the walk
/// of that subproblem, because the tie-break is decided by local costs which
/// agree on the subrectangle.
fn get_diff(old: &[String], new: &[String]) -> Vec<DiffElem> {
    let mut out = Vec::new();
    diff_into(old, new, &mut out);
    out
}

/// Unreachable-cell cost. Kept far from `i64::MAX` so `+ 1` cannot overflow.
const INF: i64 = i64::MAX / 4;

fn add1(x: i64) -> i64 {
    if x >= INF { INF } else { x + 1 }
}

fn diff_into(old: &[String], new: &[String], out: &mut Vec<DiffElem>) {
    let n = old.len();
    let m = new.len();
    if n == 0 {
        out.extend(new.iter().cloned().map(DiffElem::Second));
        return;
    }
    if m == 0 {
        out.extend(old.iter().cloned().map(DiffElem::First));
        return;
    }
    if n == 1 {
        // A single old line: the walk inserts up to the first occurrence of it
        // and matches there; with no occurrence it deletes first, then inserts.
        let x = &old[0];
        match new.iter().position(|y| y == x) {
            Some(k) => {
                out.extend(new[..k].iter().cloned().map(DiffElem::Second));
                out.push(DiffElem::Both(x.clone()));
                out.extend(new[k + 1..].iter().cloned().map(DiffElem::Second));
            }
            None => {
                out.push(DiffElem::First(x.clone()));
                out.extend(new.iter().cloned().map(DiffElem::Second));
            }
        }
        return;
    }
    let a = n / 2; // 1 <= a <= n-1 because n >= 2
    let head = forward_costs(old, new, a);
    let tail = backward_costs(old, new, a);
    // Leftmost minimizer: the walk's own crossing column at row `a`.
    let mut b = 0usize;
    let mut best = INF;
    for j in 0..=m {
        let c = head[j].saturating_add(tail[j]);
        if c < best {
            best = c;
            b = j;
        }
    }
    diff_into(&old[..a], &new[..b], out);
    diff_into(&old[a..], &new[b..], out);
}

/// `cost((0,0) -> (a, j))` for every `j`, over the snake-extended grid.
///
/// A cell where `old[i] == new[j]` has only its diagonal exit, so a step into a
/// cell is available only when the cell it leaves is not such a match cell.
/// Requires `0 < a < old.len()` and `!new.is_empty()`.
fn forward_costs(old: &[String], new: &[String], a: usize) -> Vec<i64> {
    let m = new.len();
    let mut prev = vec![INF; m + 1];
    // Row 0: reachable by inserting, until a match cell forces the diagonal.
    prev[0] = 0;
    for j in 1..=m {
        prev[j] = if old[0] == new[j - 1] {
            INF
        } else {
            add1(prev[j - 1])
        };
    }
    let mut cur = vec![INF; m + 1];
    for i in 1..=a {
        // Column 0: only the down step from (i-1, 0), unless that cell matches.
        cur[0] = if old[i - 1] == new[0] {
            INF
        } else {
            add1(prev[0])
        };
        for j in 1..=m {
            let mut best = INF;
            // Down step from (i-1, j).
            if !(j < m && old[i - 1] == new[j]) {
                best = best.min(add1(prev[j]));
            }
            // Right step from (i, j-1). `i <= a < n`, so (i, j-1) is a real cell.
            if old[i] != new[j - 1] {
                best = best.min(add1(cur[j - 1]));
            }
            // Diagonal step from (i-1, j-1).
            if old[i - 1] == new[j - 1] {
                best = best.min(prev[j - 1]);
            }
            cur[j] = best;
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev
}

/// `cost((a, j) -> (n, m))` for every `j`, over the same snake-extended grid.
fn backward_costs(old: &[String], new: &[String], a: usize) -> Vec<i64> {
    let n = old.len();
    let m = new.len();
    // Row n: only insertions remain.
    let mut prev: Vec<i64> = (0..=m).map(|j| (m - j) as i64).collect();
    let mut cur = vec![INF; m + 1];
    for i in (a..n).rev() {
        // Column m: only the down step remains.
        cur[m] = add1(prev[m]);
        for j in (0..m).rev() {
            cur[j] = if old[i] == new[j] {
                prev[j + 1]
            } else {
                add1(prev[j]).min(add1(cur[j + 1]))
            };
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev
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
            out.push(DiffRegion {
                left: (left, dl),
                right: (right, dr),
                diffs: run.clone(),
            });
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
    path.chars()
        .map(|c| {
            if c == std::path::MAIN_SEPARATOR {
                '/'
            } else {
                c
            }
        })
        .collect()
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
    s.push_str(&colorize(
        use_color,
        BOLD,
        &format!("--- {}", normalize_path(&join_prefix("a", name))),
    ));
    s.push('\n');
    s.push_str(&colorize(
        use_color,
        BOLD,
        &format!("+++ {}", normalize_path(&join_prefix("b", name))),
    ));
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
pub fn render_file(
    use_color: bool,
    filename: &str,
    contents: &str,
    comments: &[PositionedComment],
) -> DiffOutput {
    let fixes: Vec<Fix> = comments.iter().filter_map(|c| c.fix.clone()).collect();
    if fixes.is_empty() {
        return DiffOutput {
            text: String::new(),
            reported: false,
        };
    }
    let merged = fix_mconcat(&fixes);
    if merged.replacements.is_empty() {
        return DiffOutput {
            text: String::new(),
            reported: false,
        };
    }
    // `putStrLn $ formatDoc ...` adds a trailing newline.
    let mut text = make_diff_string(use_color, filename, contents, &merged);
    text.push('\n');
    DiffOutput {
        text,
        reported: true,
    }
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

    /// The straightforward full-matrix walk the linear-space `get_diff` must
    /// reproduce element for element: LCS by dynamic programming, then a
    /// forward walk preferring `Both`, then `First` on a tie.
    fn get_diff_reference(old: &[String], new: &[String]) -> Vec<DiffElem> {
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

    fn lines_of(s: &str) -> Vec<String> {
        s.chars().map(|c| c.to_string()).collect()
    }

    /// Every string over `alphabet` of length `0..=max_len`.
    fn all_strings(alphabet: &[char], max_len: usize) -> Vec<Vec<String>> {
        let mut out = vec![Vec::new()];
        let mut frontier = vec![Vec::<String>::new()];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for s in &frontier {
                for c in alphabet {
                    let mut t = s.clone();
                    t.push(c.to_string());
                    next.push(t);
                }
            }
            out.extend(next.iter().cloned());
            frontier = next;
        }
        out
    }

    fn check_same(old: &[String], new: &[String]) {
        let want = get_diff_reference(old, new);
        let got = get_diff(old, new);
        assert_eq!(got, want, "old={old:?} new={new:?}");
    }

    #[test]
    fn matches_the_full_matrix_walk_on_every_small_pair() {
        let corpus = all_strings(&['a', 'b'], 7);
        for old in &corpus {
            for new in &corpus {
                check_same(old, new);
            }
        }
    }

    #[test]
    fn matches_the_full_matrix_walk_over_three_symbols() {
        let corpus = all_strings(&['a', 'b', 'c'], 5);
        for old in &corpus {
            for new in &corpus {
                check_same(old, new);
            }
        }
    }

    #[test]
    fn matches_the_full_matrix_walk_on_pseudorandom_larger_pairs() {
        // Deterministic xorshift so a failure is reproducible.
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for case in 0..400 {
            let alphabet = 1 + (case % 4);
            let n = (next() % 40) as usize;
            let m = (next() % 40) as usize;
            let mut make = |len: usize| -> Vec<String> {
                (0..len)
                    .map(|_| (b'a' + (next() % alphabet as u64) as u8) as char)
                    .map(|c| c.to_string())
                    .collect()
            };
            let old = make(n);
            let new = make(m);
            check_same(&old, &new);
        }
    }

    #[test]
    fn identical_inputs_are_all_both() {
        let old = lines_of("abcdef");
        let got = get_diff(&old, &old);
        assert_eq!(
            got,
            old.iter().cloned().map(DiffElem::Both).collect::<Vec<_>>()
        );
        check_same(&old, &old);
    }

    #[test]
    fn disjoint_inputs_delete_then_insert() {
        let old = lines_of("abc");
        let new = lines_of("xyz");
        assert_eq!(
            get_diff(&old, &new),
            vec![
                DiffElem::First("a".into()),
                DiffElem::First("b".into()),
                DiffElem::First("c".into()),
                DiffElem::Second("x".into()),
                DiffElem::Second("y".into()),
                DiffElem::Second("z".into()),
            ]
        );
        check_same(&old, &new);
    }

    #[test]
    fn one_sided_empty() {
        let old = lines_of("ab");
        assert_eq!(
            get_diff(&old, &[]),
            vec![DiffElem::First("a".into()), DiffElem::First("b".into())]
        );
        assert_eq!(
            get_diff(&[], &old),
            vec![DiffElem::Second("a".into()), DiffElem::Second("b".into())]
        );
        check_same(&old, &[]);
        check_same(&[], &old);
    }

    #[test]
    fn repeated_lines_match_the_earliest_row() {
        // The walk takes the diagonal as soon as the lines are equal, so the
        // surviving `a` is the first one, not the last.
        let old = lines_of("aa");
        let new = lines_of("a");
        assert_eq!(
            get_diff(&old, &new),
            vec![DiffElem::Both("a".into()), DiffElem::First("a".into())]
        );
        check_same(&old, &new);

        // The mirror case: an inserted duplicate lands after the match.
        assert_eq!(
            get_diff(&new, &old),
            vec![DiffElem::Both("a".into()), DiffElem::Second("a".into())]
        );
        check_same(&new, &old);
    }

    #[test]
    fn crossed_pair_prefers_the_deletion() {
        // Both single-line matches cost the same; the walk deletes first, so it
        // matches the second `b`, not the first `a`.
        let old = lines_of("ab");
        let new = lines_of("ba");
        assert_eq!(
            get_diff(&old, &new),
            vec![
                DiffElem::First("a".into()),
                DiffElem::Both("b".into()),
                DiffElem::Second("a".into()),
            ]
        );
        check_same(&old, &new);
    }

    #[test]
    fn moved_block() {
        let old = lines_of("abcdefgh");
        let new = lines_of("efghabcd");
        check_same(&old, &new);
    }

    #[test]
    fn duplicated_block() {
        let old = lines_of("abcd");
        let new = lines_of("abcdabcd");
        check_same(&old, &new);
        let old = lines_of("xabcdy");
        let new = lines_of("xabcdabcdy");
        check_same(&old, &new);
    }

    #[test]
    fn many_equal_lines() {
        let old = vec!["x".to_string(); 30];
        let mut new = vec!["x".to_string(); 25];
        new.push("y".to_string());
        check_same(&old, &new);
        check_same(&new, &old);
    }

    #[test]
    fn large_input_is_linear_space() {
        // A matrix for this would have been 4001 * 4001 i64 (128 MB); the real
        // 20k-line case is covered end-to-end against the oracle, and is only
        // kept out of here because the unoptimized test build is slow.
        let old: Vec<String> = (0..4_000).map(|i| format!("line {i}")).collect();
        let mut new = old.clone();
        new[2_000] = "changed".to_string();
        let got = get_diff(&old, &new);
        assert_eq!(got.len(), 4_001);
        assert_eq!(got[2_000], DiffElem::First("line 2000".to_string()));
        assert_eq!(got[2_001], DiffElem::Second("changed".to_string()));
        assert_eq!(got.iter().filter(|d| is_both(d)).count(), 3_999);
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
