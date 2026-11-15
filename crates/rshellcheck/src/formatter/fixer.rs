//! Port of `ShellCheck.Fixer`: applying `Replacement`s to source text.
//!
//! This mirrors the Haskell Fixer closely enough to drive the `diff` formatter
//! and the TTY "Did you mean:" hints:
//!
//! * `Ranged`/`overlap` and the `Fix` `Semigroup`/`mconcat` merge (discarding
//!   overlapping replacements, keeping the left side).
//! * `remove_tab_stops` realigns a range's columns from a tabstop of 8 back to
//!   the real character column (`makeNonVirtual`).
//! * `apply_fix` untabs, flattens the affected lines into a single string,
//!   applies replacements in precedence order (highest first) using a prefix-sum
//!   tree to account for earlier shifts, then splits back into lines.
//!
//! Columns and lines are 1-based, matching the Haskell `Position`.

use rshellcheck_core::interface::{
    Fix, InsertionPoint, Position, PositionedComment, Replacement, columns,
};

/// Haskell `Data.List.lines`: split on `'\n'` only (no `\r` handling), no
/// trailing empty element for a final newline, `""` -> `[]`.
#[must_use]
pub fn lines(s: &str) -> Vec<String> {
    if s.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        if c == '\n' {
            out.push(std::mem::take(&mut cur));
        } else {
            cur.push(c);
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// Haskell `unlines`: `concatMap (++ "\n")`.
#[must_use]
pub fn unlines(xs: &[String]) -> String {
    let mut s = String::new();
    for x in xs {
        s.push_str(x);
        s.push('\n');
    }
    s
}

// Ranged / overlap

/// `overlap x y = xEnd > yStart && yEnd > xStart` over `Position` order.
fn overlap(x: &Replacement, y: &Replacement) -> bool {
    x.end > y.start && y.end > x.start
}

/// `Fix`'s `Semigroup`: merge `f2` into `f1` unless any replacement overlaps,
/// in which case `f1` wins unchanged.
#[must_use]
pub fn fix_append(f1: &Fix, f2: &Fix) -> Fix {
    let conflict = f2
        .replacements
        .iter()
        .any(|r2| f1.replacements.iter().any(|r1| overlap(r2, r1)));
    if conflict {
        f1.clone()
    } else {
        let mut reps = f1.replacements.clone();
        reps.extend(f2.replacements.iter().cloned());
        Fix { replacements: reps }
    }
}

/// `mconcat`: `foldl mappend mempty` (fold left to right so `<>` discards the
/// right side on overlap).
///
/// The result equals a fold of [`fix_append`]. The accumulated fix is never
/// copied, and [`Reach`] answers each overlap test in logarithmic time.
#[must_use]
pub fn fix_mconcat(fixes: &[Fix]) -> Fix {
    let mut reach = Reach::default();
    let mut replacements = Vec::new();
    for f in fixes {
        if f.replacements.iter().any(|r| reach.overlaps(r)) {
            continue;
        }
        for r in &f.replacements {
            reach.insert(r);
        }
        replacements.extend(f.replacements.iter().cloned());
    }
    Fix { replacements }
}

/// The replacements a [`fix_mconcat`] fold has accepted, reduced to what
/// `overlap` needs. For a position `p`, it gives the furthest end among the
/// replacements that start before `p`. A new replacement overlaps an
/// accepted one exactly when that furthest end, taken at the new
/// replacement's end, lies past the new replacement's start.
///
/// The map goes from start to end, and both ascend strictly. An entry that
/// starts no earlier and ends no later than another entry can never hold
/// the furthest end, so the map drops it.
#[derive(Default)]
struct Reach(std::collections::BTreeMap<Position, Position>);

impl Reach {
    fn overlaps(&self, r: &Replacement) -> bool {
        self.0
            .range(..&r.end)
            .next_back()
            .is_some_and(|(_, end)| *end > r.start)
    }

    fn insert(&mut self, r: &Replacement) {
        let covered = self
            .0
            .range(..=&r.start)
            .next_back()
            .is_some_and(|(_, end)| *end >= r.end);
        if covered {
            return;
        }
        let dominated: Vec<Position> = self
            .0
            .range(&r.start..)
            .take_while(|(_, end)| **end <= r.end)
            .map(|(start, _)| start.clone())
            .collect();
        for start in dominated {
            self.0.remove(&start);
        }
        self.0.insert(r.start.clone(), r.end.clone());
    }
}

/// `mapPositions`: apply `f` to the start and end of every replacement.
pub fn map_positions<F: Fn(&Position) -> Position>(fix: &Fix, f: F) -> Fix {
    Fix {
        replacements: fix
            .replacements
            .iter()
            .map(|r| Replacement {
                start: f(&r.start),
                end: f(&r.end),
                ..r.clone()
            })
            .collect(),
    }
}

// Tab realignment (removeTabStops)

/// The virtual columns (tabstop 8) of a file's lines. [`TabStops::new`]
/// computes them once, and each lookup is a binary search on one line.
pub struct TabStops {
    /// For each line, the virtual column before each character and after the
    /// last one. A line without tabs holds `None`. Its virtual and real columns
    /// are equal.
    lines: Vec<Option<Vec<i64>>>,
}

impl TabStops {
    /// Scans every line of the file once.
    #[must_use]
    pub fn new(lines: &[String]) -> Self {
        let lines = lines
            .iter()
            .map(|line| {
                line.contains('\t').then(|| {
                    let mut v: i64 = 0;
                    let mut stops = Vec::with_capacity(line.len() + 1);
                    stops.push(v);
                    for ch in line.chars() {
                        if ch == '\t' {
                            v += 8 - (v % 8);
                        } else {
                            v += 1;
                        }
                        stops.push(v);
                    }
                    stops
                })
            })
            .collect();
        Self { lines }
    }

    /// `real`. Maps the virtual column `col_no` on line `line_no` to a real
    /// character column. A column on a missing line comes back unchanged. Like
    /// the Haskell recursion, the lookup stops at the first character whose
    /// virtual column reaches the target.
    fn realign_column(&self, line_no: i64, col_no: i64) -> i64 {
        let Some(line) = usize::try_from(line_no - 1)
            .ok()
            .and_then(|i| self.lines.get(i))
        else {
            return col_no;
        };
        let Some(stops) = line else {
            return col_no.max(0);
        };
        // `real _ r v target | target <= v = r` comes before the end-of-line
        // clause: a target reached by the line's last character -- a tab,
        // which jumps `v` past it -- is that character's column, not a step
        // back. Only a target beyond every stop takes `r + (target - v)`.
        let r = stops.partition_point(|&v| v < col_no);
        let last = stops.len() - 1;
        if r <= last {
            columns(r)
        } else {
            columns(last) + (col_no - stops[last])
        }
    }
}

/// `removeTabStops` for a `Replacement`.
#[must_use]
pub fn remove_tab_stops_rep(r: &Replacement, tabs: &TabStops) -> Replacement {
    let start_col = tabs.realign_column(r.start.line, r.start.column);
    let end_col = tabs.realign_column(r.end.line, r.end.column);
    Replacement {
        start: Position {
            column: start_col,
            ..r.start.clone()
        },
        end: Position {
            column: end_col,
            ..r.end.clone()
        },
        ..r.clone()
    }
}

/// `removeTabStops` for a `PositionedComment`.
#[must_use]
pub fn remove_tab_stops_comment(c: &PositionedComment, tabs: &TabStops) -> PositionedComment {
    let start_col = tabs.realign_column(c.start.line, c.start.column);
    let end_col = tabs.realign_column(c.end.line, c.end.column);
    PositionedComment {
        start: Position {
            column: start_col,
            ..c.start.clone()
        },
        end: Position {
            column: end_col,
            ..c.end.clone()
        },
        ..c.clone()
    }
}

/// `makeNonVirtual`: untab each comment's own range and its fix replacements.
#[must_use]
pub fn make_non_virtual(comments: &[PositionedComment], contents: &str) -> Vec<PositionedComment> {
    let tabs = TabStops::new(&lines(contents));
    comments
        .iter()
        .map(|c| {
            let mut nc = remove_tab_stops_comment(c, &tabs);
            nc.fix = c.fix.as_ref().map(|f| Fix {
                replacements: f
                    .replacements
                    .iter()
                    .map(|r| remove_tab_stops_rep(r, &tabs))
                    .collect(),
            });
            nc
        })
        .collect()
}

// Prefix-sum tree (PSTree)

enum PSTree {
    Leaf,
    Branch {
        pivot: i64,
        left: Box<Self>,
        right: Box<Self>,
        cumulative: i64,
    },
}

impl PSTree {
    const fn new() -> Self {
        Self::Leaf
    }

    /// Sum of values whose keys are `<= target`.
    fn prefix_sum(&self, target: i64) -> i64 {
        let mut sum = 0;
        let mut node = self;
        loop {
            match node {
                Self::Leaf => return sum,
                Self::Branch {
                    pivot,
                    left,
                    right,
                    cumulative,
                } => {
                    use std::cmp::Ordering::{Equal, Greater, Less};
                    match target.cmp(pivot) {
                        Less => node = left,
                        Greater => {
                            sum += *cumulative;
                            node = right;
                        }
                        Equal => return sum + *cumulative,
                    }
                }
            }
        }
    }

    /// Add `value` at `key` (accumulating), mirroring `addPSValue`.
    fn add(&mut self, key: i64, value: i64) {
        if value == 0 {
            return;
        }
        let mut node = self;
        loop {
            match node {
                Self::Leaf => {
                    *node = Self::Branch {
                        pivot: key,
                        left: Box::new(Self::Leaf),
                        right: Box::new(Self::Leaf),
                        cumulative: value,
                    };
                    return;
                }
                Self::Branch {
                    pivot,
                    left,
                    right,
                    cumulative,
                } => {
                    use std::cmp::Ordering::{Equal, Greater, Less};
                    match key.cmp(pivot) {
                        Less => {
                            *cumulative += value;
                            node = left;
                        }
                        Greater => node = right,
                        Equal => {
                            *cumulative += value;
                            return;
                        }
                    }
                }
            }
        }
    }
}

/// Replacements at ascending columns grow the tree into one long chain.
/// This drop takes the tree apart with a work list.
impl Drop for PSTree {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach_branches(&mut pending);
        // Each node drops here with only leaves below it. Its own `drop` then
        // finds nothing to detach.
        while let Some(mut node) = pending.pop() {
            node.detach_branches(&mut pending);
        }
    }
}

impl PSTree {
    /// Moves this node's branch children into `pending` and puts leaves in
    /// their place.
    fn detach_branches(&mut self, pending: &mut Vec<Self>) {
        if let Self::Branch { left, right, .. } = self {
            for child in [left, right] {
                if matches!(**child, Self::Branch { .. }) {
                    pending.push(std::mem::replace(&mut **child, Self::Leaf));
                }
            }
        }
    }
}

// Replacement application

/// `n` as an index into `len` items, clamped to `0..=len`.
fn clamp_index(n: i64, len: usize) -> usize {
    if n <= 0 {
        0
    } else {
        usize::try_from(n).map_or(len, |i| i.min(len))
    }
}

/// `doReplace start end o r`, with 1-based columns over the char sequence.
/// It edits `o` in place and moves only the text after the replacement.
fn do_replace(start: i64, end: i64, o: &mut Vec<char>, r: &str) {
    let si = clamp_index(start - 1, o.len());
    let ei = clamp_index(end - 1, o.len()).max(si);
    o.splice(si..ei, r.chars());
}

fn apply_replacement(rep: &Replacement, s: &mut Vec<char>, tree: &mut PSTree) {
    let old_start = rep.start.column;
    let old_end = rep.end.column;
    let new_start = old_start + tree.prefix_sum(old_start);
    let new_end = old_end + tree.prefix_sum(old_end);
    let replacer = &rep.string;
    let shift = columns(replacer.chars().count()) - (old_end - old_start);
    let insertion_point = match rep.insertion_point {
        InsertionPoint::InsertBefore => old_start,
        InsertionPoint::InsertAfter => old_end + 1,
    };
    tree.add(insertion_point, shift);
    do_replace(new_start, new_end, s, replacer);
}

/// Apply replacements in precedence order (highest precedence first).
fn apply_replacements(reps: &[Replacement], s: &str) -> String {
    // `reverse $ sortWith repPrecedence reps`: stable ascending sort, reversed.
    let mut order: Vec<&Replacement> = reps.iter().collect();
    order.sort_by_key(|r| r.precedence);
    order.reverse();
    let mut tree = PSTree::new();
    let mut cur: Vec<char> = s.chars().collect();
    for rep in order {
        apply_replacement(rep, &mut cur, &mut tree);
    }
    cur.into_iter().collect()
}

/// Flatten the affected lines into one line-1 string, shifting positions.
/// Mirrors `multiToSingleLine` for a single fix.
fn multi_to_single(fix: &Fix, lines_in: &[String]) -> (Fix, String) {
    // Prefix offsets: for a position on line L, column shift is the sum of
    // (len(line_n) + 1) for all n < L.
    let mut prefix: Vec<i64> = Vec::with_capacity(lines_in.len() + 2);
    prefix.push(0); // index 0 unused (lines are 1-based)
    prefix.push(0); // shift for line 1 is 0
    let mut acc = 0i64;
    for line in lines_in {
        acc += columns(line.chars().count()) + 1;
        prefix.push(acc);
    }
    let adjust = |pos: &Position| -> Position {
        let l = pos.line;
        let shift = if l < 1 {
            0
        } else {
            usize::try_from(l)
                .ok()
                .and_then(|i| prefix.get(i).copied())
                .unwrap_or(acc)
        };
        Position {
            file: pos.file.clone(),
            line: 1,
            column: pos.column + shift,
        }
    };
    (map_positions(fix, adjust), unlines(lines_in))
}

/// `applyFix`: apply `fix` to `file_lines` (1-based), returning the new lines.
#[must_use]
pub fn apply_fix(fix: &Fix, file_lines: &[String]) -> Vec<String> {
    let tabs = TabStops::new(file_lines);
    let untabbed = Fix {
        replacements: fix
            .replacements
            .iter()
            .map(|r| remove_tab_stops_rep(r, &tabs))
            .collect(),
    };
    let (adjusted, single) = multi_to_single(&untabbed, file_lines);
    let result = apply_replacements(&adjusted.replacements, &single);
    lines(&result)
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use rshellcheck_core::interface::{InsertionPoint, Position};

    fn pos(line: i64, col: i64) -> Position {
        Position {
            file: String::new(),
            line,
            column: col,
        }
    }

    fn t_from_start(start: i64, end: i64, repl: &str, order: i32) -> Replacement {
        Replacement {
            start: pos(1, start),
            end: pos(1, end),
            string: repl.to_string(),
            precedence: order,
            insertion_point: InsertionPoint::InsertAfter,
        }
    }
    fn t_from_end(start: i64, end: i64, repl: &str, order: i32) -> Replacement {
        Replacement {
            insertion_point: InsertionPoint::InsertBefore,
            ..t_from_start(start, end, repl, order)
        }
    }

    fn test_fixes(expected: &str, original: &str, fixes: &[Fix]) {
        let reps: Vec<Replacement> = fixes
            .iter()
            .flat_map(|f| f.replacements.iter().cloned())
            .collect();
        let actual = apply_replacements(&reps, original);
        assert_eq!(actual, expected);
    }

    fn test_fix(replacements: Vec<Replacement>) -> Fix {
        Fix { replacements }
    }

    fn assert_overlap(x: &Replacement, y: &Replacement) {
        assert!(overlap(x, y) && overlap(y, x));
    }

    fn assert_no_overlap(x: &Replacement, y: &Replacement) {
        assert!(!overlap(x, y) && !overlap(y, x));
    }

    #[test]
    fn prop_overlap_contiguous() {
        assert_no_overlap(
            &t_from_start(10, 12, "foo", 1),
            &t_from_start(12, 14, "bar", 2),
        );
    }

    #[test]
    fn prop_overlap_adjacent_zerowidth() {
        assert_no_overlap(&t_from_start(3, 3, "foo", 1), &t_from_start(3, 3, "bar", 2));
    }

    #[test]
    fn prop_overlap_enclosed() {
        assert_overlap(
            &t_from_start(3, 5, "foo", 1),
            &t_from_start(1, 10, "bar", 2),
        );
    }

    #[test]
    fn prop_overlap_partial() {
        assert_overlap(&t_from_start(1, 5, "foo", 1), &t_from_start(3, 7, "bar", 2));
    }

    fn replaced(start: i64, end: i64, o: &str, r: &str) -> String {
        let mut chars: Vec<char> = o.chars().collect();
        do_replace(start, end, &mut chars, r);
        chars.into_iter().collect()
    }

    #[test]
    fn prop_doReplace1() {
        assert_eq!(replaced(0, 0, "1234", "A"), "A1234");
    }

    #[test]
    fn prop_doReplace2() {
        assert_eq!(replaced(1, 1, "1234", "A"), "A1234");
    }

    #[test]
    fn prop_doReplace3() {
        assert_eq!(replaced(1, 2, "1234", "A"), "A234");
    }

    #[test]
    fn prop_doReplace4() {
        assert_eq!(replaced(3, 3, "1234", "A"), "12A34");
    }

    #[test]
    fn prop_doReplace5() {
        assert_eq!(replaced(4, 4, "1234", "A"), "123A4");
    }

    #[test]
    fn prop_doReplace6() {
        assert_eq!(replaced(5, 5, "1234", "A"), "1234A");
    }

    fn pstree_sums_correctly(kvs: &[(i64, i64)], targets: &[i64]) {
        let dumb: Vec<i64> = targets
            .iter()
            .map(|&target| {
                kvs.iter()
                    .filter(|(k, _)| *k <= target)
                    .map(|(_, v)| v)
                    .sum()
            })
            .collect();
        let mut tree = PSTree::new();
        for &(pos, shift) in kvs {
            tree.add(pos, shift);
        }
        let smart: Vec<i64> = targets.iter().map(|&x| tree.prefix_sum(x)).collect();
        assert_eq!(smart, dumb, "kvs {kvs:?}");
    }

    #[test]
    fn prop_pstreeSumsCorrectly() {
        let keys = -2..=2;
        let values = -1..=1;
        let pairs: Vec<(i64, i64)> = keys
            .flat_map(|k| values.clone().map(move |v| (k, v)))
            .collect();
        let targets: Vec<i64> = (-3..=3).collect();
        pstree_sums_correctly(&[], &targets);
        pstree_sums_correctly(&[(1, 1)], &[]);
        for &a in &pairs {
            pstree_sums_correctly(&[a], &targets);
            for &b in &pairs {
                pstree_sums_correctly(&[a, b], &targets);
                for &c in &pairs {
                    pstree_sums_correctly(&[a, b, c], &targets);
                }
            }
        }
        let long: Vec<(i64, i64)> = (0..200)
            .map(|i| ((i * 7) % 23 - 11, (i * 5) % 9 - 4))
            .collect();
        let long_targets: Vec<i64> = (-12..=12).collect();
        pstree_sums_correctly(&long, &long_targets);
    }

    #[test]
    fn prop_simpleFix1() {
        test_fixes(
            "hello world",
            "hell world",
            &[test_fix(vec![t_from_end(5, 5, "o", 1)])],
        );
    }

    #[test]
    fn prop_anchorsLeft() {
        test_fixes(
            "-->foobar<--",
            "--><--",
            &[test_fix(vec![
                t_from_start(4, 4, "foo", 1),
                t_from_start(4, 4, "bar", 2),
            ])],
        );
    }

    #[test]
    fn prop_anchorsRight() {
        test_fixes(
            "-->foobar<--",
            "--><--",
            &[test_fix(vec![
                t_from_end(4, 4, "bar", 1),
                t_from_end(4, 4, "foo", 2),
            ])],
        );
    }

    #[test]
    fn prop_anchorsBoth1() {
        test_fixes(
            "-->foobar<--",
            "--><--",
            &[test_fix(vec![
                t_from_start(4, 4, "bar", 2),
                t_from_end(4, 4, "foo", 1),
            ])],
        );
    }

    #[test]
    fn prop_anchorsBoth2() {
        test_fixes(
            "-->foobar<--",
            "--><--",
            &[test_fix(vec![
                t_from_end(4, 4, "foo", 2),
                t_from_start(4, 4, "bar", 1),
            ])],
        );
    }

    #[test]
    fn prop_composeFixes1() {
        test_fixes(
            "cd \"$1\" || exit",
            "cd $1",
            &[
                test_fix(vec![
                    t_from_start(4, 4, "\"", 10),
                    t_from_end(6, 6, "\"", 10),
                ]),
                test_fix(vec![t_from_end(6, 6, " || exit", 5)]),
            ],
        );
    }

    #[test]
    fn prop_composeFixes2() {
        test_fixes(
            "$(\"$1\")",
            "`$1`",
            &[
                test_fix(vec![t_from_start(1, 2, "$(", 5), t_from_end(4, 5, ")", 5)]),
                test_fix(vec![
                    t_from_start(2, 2, "\"", 10),
                    t_from_end(4, 4, "\"", 10),
                ]),
            ],
        );
    }

    #[test]
    fn prop_composeFixes3() {
        test_fixes(
            "(x)[x]",
            "xx",
            &[test_fix(vec![
                t_from_start(1, 1, "(", 4),
                t_from_end(2, 2, ")", 3),
                t_from_start(2, 2, "[", 2),
                t_from_end(3, 3, "]", 1),
            ])],
        );
    }

    #[test]
    fn prop_composeFixes4() {
        test_fixes(
            "(x)[x]",
            "xx",
            &[test_fix(vec![
                t_from_start(1, 1, "(", 4),
                t_from_start(2, 2, "[", 3),
                t_from_end(2, 2, ")", 2),
                t_from_end(3, 3, "]", 1),
            ])],
        );
    }

    #[test]
    fn prop_composeFixes5() {
        test_fixes(
            "\"$(x)\"",
            "`x`",
            &[test_fix(vec![
                t_from_start(1, 2, "$(", 2),
                t_from_end(3, 4, ")", 2),
                t_from_start(1, 1, "\"", 1),
                t_from_end(4, 4, "\"", 1),
            ])],
        );
    }

    #[test]
    fn hs_lines_semantics() {
        assert_eq!(lines(""), Vec::<String>::new());
        assert_eq!(lines("a\nb"), vec!["a", "b"]);
        assert_eq!(lines("a\nb\n"), vec!["a", "b"]);
        assert_eq!(lines("\n"), vec![""]);
        assert_eq!(lines("a\n\nb"), vec!["a", "", "b"]);
    }

    fn real_col(line: &str, target: i64) -> i64 {
        TabStops::new(&[line.to_string()]).realign_column(1, target)
    }

    #[test]
    fn a_column_on_a_trailing_tab_is_that_tab() {
        // `real`'s `target <= v` guard comes before its end-of-line clause: a
        // tab as the last character jumps the virtual column past the target,
        // and the answer is the tab's own column, not `r + (target - v)`.
        assert_eq!(real_col("o{1..$n}\t", 9), 9);
        assert_eq!(real_col("o{1..$n}\t", 8), 8);
        assert_eq!(real_col("ab", 5), 5);
    }

    #[test]
    fn tab_stops_match_the_haskell_recursion() {
        // `real` from `ShellCheck.Fixer`, transcribed clause by clause.
        fn real(line: &[char], r: i64, v: i64, target: i64) -> i64 {
            if target <= v {
                return r;
            }
            match line.split_first() {
                None => r + (target - v),
                Some(('\t', rest)) => real(rest, r + 1, v + 8 - (v % 8), target),
                Some((_, rest)) => real(rest, r + 1, v + 1, target),
            }
        }
        for line in [
            "",
            "ab",
            "\t",
            "\tx",
            "a\tb\t\tc",
            "1234567\t",
            "\t\t",
            "x\t",
        ] {
            let chars: Vec<char> = line.chars().collect();
            for target in -3..40 {
                assert_eq!(
                    real_col(line, target),
                    real(&chars, 0, 0, target),
                    "{line:?} at {target}"
                );
            }
        }
        let tabs = TabStops::new(&["\tx".to_string()]);
        assert_eq!(tabs.realign_column(0, 9), 9);
        assert_eq!(tabs.realign_column(2, 9), 9);
    }

    #[test]
    fn a_long_chain_of_shifts_builds_and_drops() {
        let sums = std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut tree = PSTree::new();
                for key in 1..=10_000 {
                    tree.add(key, 1);
                }
                (tree.prefix_sum(10_000), tree.prefix_sum(0))
            })
            .and_then(|h| h.join().map_err(|_| std::io::Error::other("panicked")));
        assert_eq!(sums.ok(), Some((10_000, 0)));
    }

    #[test]
    fn fix_mconcat_equals_folding_fix_append() {
        let mut seed: u64 = 0x2545_F491_4F6C_DD1D;
        let mut next = |bound: i64| {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            i64::try_from(seed >> 33).unwrap_or(0) % bound
        };
        for _ in 0..500 {
            let fixes: Vec<Fix> = (0..=next(12))
                .map(|_| {
                    test_fix(
                        (0..=next(3))
                            .map(|_| {
                                let line = 1 + next(3);
                                let start = 1 + next(12);
                                let end = start + next(4);
                                Replacement {
                                    start: pos(line, start),
                                    end: pos(line + next(2), end),
                                    ..t_from_start(0, 0, "x", 1)
                                }
                            })
                            .collect(),
                    )
                })
                .collect();
            let folded = fixes
                .iter()
                .fold(Fix::default(), |acc, f| fix_append(&acc, f));
            assert_eq!(fix_mconcat(&fixes), folded, "{fixes:?}");
        }
    }

    #[test]
    fn apply_fix_multiline_untabs() {
        // A tab before the target column: virtual column 9 -> real column 2.
        let file = vec!["\tx".to_string()];
        let fix = Fix {
            replacements: vec![Replacement {
                start: pos(1, 9),
                end: pos(1, 10),
                string: "y".to_string(),
                precedence: 1,
                insertion_point: InsertionPoint::InsertBefore,
            }],
        };
        assert_eq!(apply_fix(&fix, &file), vec!["\ty".to_string()]);
    }
}
