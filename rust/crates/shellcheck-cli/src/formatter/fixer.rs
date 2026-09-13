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

use shellcheck_rs::interface::{Fix, InsertionPoint, Position, PositionedComment, Replacement};

/// Haskell `Data.List.lines`: split on `'\n'` only (no `\r` handling), no
/// trailing empty element for a final newline, `""` -> `[]`.
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
pub fn unlines(xs: &[String]) -> String {
    let mut s = String::new();
    for x in xs {
        s.push_str(x);
        s.push('\n');
    }
    s
}

// --- Ranged / overlap -------------------------------------------------------

/// `overlap x y = xEnd > yStart && yEnd > xStart` over `Position` order.
fn overlap(x: &Replacement, y: &Replacement) -> bool {
    x.end > y.start && y.end > x.start
}

/// `Fix`'s `Semigroup`: merge `f2` into `f1` unless any replacement overlaps,
/// in which case `f1` wins unchanged.
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
pub fn fix_mconcat(fixes: &[Fix]) -> Fix {
    let mut acc = Fix::default();
    for f in fixes {
        acc = fix_append(&acc, f);
    }
    acc
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

// --- Tab realignment (removeTabStops) ---------------------------------------

/// `real`: map a virtual column (tabstop 8) to a real character column on
/// `line`. Mirrors the Haskell recursion exactly.
fn real_col(line: &str, target: i64) -> i64 {
    let mut r: i64 = 0;
    let mut v: i64 = 0;
    for ch in line.chars() {
        if target <= v {
            return r;
        }
        if ch == '\t' {
            v += 8 - (v % 8);
        } else {
            v += 1;
        }
        r += 1;
    }
    // `real _ r v target | target <= v = r` comes before the end-of-line
    // clause: a target reached by the line's last character -- a tab, which
    // jumps `v` past it -- is that character's column, not a step back.
    if target <= v {
        return r;
    }
    r + (target - v)
}

fn realign_column(lines: &[String], line_no: i64, col_no: i64) -> i64 {
    if line_no > 0 && line_no <= lines.len() as i64 {
        real_col(&lines[(line_no - 1) as usize], col_no)
    } else {
        col_no
    }
}

/// `removeTabStops` for a `Replacement`.
pub fn remove_tab_stops_rep(r: &Replacement, lines: &[String]) -> Replacement {
    let start_col = realign_column(lines, r.start.line, r.start.column);
    let end_col = realign_column(lines, r.end.line, r.end.column);
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
pub fn remove_tab_stops_comment(c: &PositionedComment, lines: &[String]) -> PositionedComment {
    let start_col = realign_column(lines, c.start.line, c.start.column);
    let end_col = realign_column(lines, c.end.line, c.end.column);
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
pub fn make_non_virtual(comments: &[PositionedComment], contents: &str) -> Vec<PositionedComment> {
    let arr = lines(contents);
    comments
        .iter()
        .map(|c| {
            let mut nc = remove_tab_stops_comment(c, &arr);
            nc.fix = c.fix.as_ref().map(|f| Fix {
                replacements: f
                    .replacements
                    .iter()
                    .map(|r| remove_tab_stops_rep(r, &arr))
                    .collect(),
            });
            nc
        })
        .collect()
}

// --- Prefix-sum tree (PSTree) -----------------------------------------------

enum PSTree {
    Leaf,
    Branch {
        pivot: i64,
        left: Box<PSTree>,
        right: Box<PSTree>,
        cumulative: i64,
    },
}

impl PSTree {
    fn new() -> Self {
        PSTree::Leaf
    }

    /// Sum of values whose keys are `<= target`.
    fn prefix_sum(&self, target: i64) -> i64 {
        let mut sum = 0;
        let mut node = self;
        loop {
            match node {
                PSTree::Leaf => return sum,
                PSTree::Branch {
                    pivot,
                    left,
                    right,
                    cumulative,
                } => {
                    use std::cmp::Ordering::*;
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
        match self {
            PSTree::Leaf => {
                *self = PSTree::Branch {
                    pivot: key,
                    left: Box::new(PSTree::Leaf),
                    right: Box::new(PSTree::Leaf),
                    cumulative: value,
                };
            }
            PSTree::Branch {
                pivot,
                left,
                right,
                cumulative,
            } => {
                use std::cmp::Ordering::*;
                match key.cmp(pivot) {
                    Less => {
                        left.add(key, value);
                        *cumulative += value;
                    }
                    Greater => right.add(key, value),
                    Equal => *cumulative += value,
                }
            }
        }
    }
}

// --- Replacement application ------------------------------------------------

/// `doReplace start end o r` (1-based columns over the char sequence).
fn do_replace(start: i64, end: i64, o: &str, r: &str) -> String {
    let chars: Vec<char> = o.chars().collect();
    let si = ((start - 1).max(0) as usize).min(chars.len());
    let ei = ((end - 1).max(0) as usize).min(chars.len());
    let ei = ei.max(si);
    let mut out = String::new();
    out.extend(chars[..si].iter());
    out.push_str(r);
    out.extend(chars[ei..].iter());
    out
}

fn apply_replacement(rep: &Replacement, s: String, tree: &mut PSTree) -> String {
    let old_start = rep.start.column;
    let old_end = rep.end.column;
    let new_start = old_start + tree.prefix_sum(old_start);
    let new_end = old_end + tree.prefix_sum(old_end);
    let replacer = &rep.string;
    let shift = replacer.chars().count() as i64 - (old_end - old_start);
    let insertion_point = match rep.insertion_point {
        InsertionPoint::InsertBefore => old_start,
        InsertionPoint::InsertAfter => old_end + 1,
    };
    tree.add(insertion_point, shift);
    do_replace(new_start, new_end, &s, replacer)
}

/// Apply replacements in precedence order (highest precedence first).
fn apply_replacements(reps: &[Replacement], s: String) -> String {
    // `reverse $ sortWith repPrecedence reps`: stable ascending sort, reversed.
    let mut order: Vec<&Replacement> = reps.iter().collect();
    order.sort_by_key(|r| r.precedence);
    order.reverse();
    let mut tree = PSTree::new();
    let mut cur = s;
    for rep in order {
        cur = apply_replacement(rep, cur, &mut tree);
    }
    cur
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
        acc += line.chars().count() as i64 + 1;
        prefix.push(acc);
    }
    let adjust = |pos: &Position| -> Position {
        let l = pos.line;
        let shift = if l >= 1 && (l as usize) < prefix.len() {
            prefix[l as usize]
        } else if l >= prefix.len() as i64 {
            *prefix.last().unwrap()
        } else {
            0
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
pub fn apply_fix(fix: &Fix, file_lines: &[String]) -> Vec<String> {
    let untabbed = Fix {
        replacements: fix
            .replacements
            .iter()
            .map(|r| remove_tab_stops_rep(r, file_lines))
            .collect(),
    };
    let (adjusted, single) = multi_to_single(&untabbed, file_lines);
    let result = apply_replacements(&adjusted.replacements, single);
    lines(&result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use shellcheck_rs::interface::{InsertionPoint, Position};

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
        let actual = apply_replacements(&reps, original.to_string());
        assert_eq!(actual, expected);
    }

    #[test]
    fn do_replace_cases() {
        assert_eq!(do_replace(0, 0, "1234", "A"), "A1234");
        assert_eq!(do_replace(1, 1, "1234", "A"), "A1234");
        assert_eq!(do_replace(1, 2, "1234", "A"), "A234");
        assert_eq!(do_replace(3, 3, "1234", "A"), "12A34");
        assert_eq!(do_replace(4, 4, "1234", "A"), "123A4");
        assert_eq!(do_replace(5, 5, "1234", "A"), "1234A");
    }

    #[test]
    fn simple_fix() {
        test_fixes(
            "hello world",
            "hell world",
            &[Fix {
                replacements: vec![t_from_end(5, 5, "o", 1)],
            }],
        );
    }

    #[test]
    fn anchors_left() {
        test_fixes(
            "-->foobar<--",
            "--><--",
            &[Fix {
                replacements: vec![t_from_start(4, 4, "foo", 1), t_from_start(4, 4, "bar", 2)],
            }],
        );
    }

    #[test]
    fn anchors_right() {
        test_fixes(
            "-->foobar<--",
            "--><--",
            &[Fix {
                replacements: vec![t_from_end(4, 4, "bar", 1), t_from_end(4, 4, "foo", 2)],
            }],
        );
    }

    #[test]
    fn compose_fixes1() {
        test_fixes(
            "cd \"$1\" || exit",
            "cd $1",
            &[
                Fix {
                    replacements: vec![t_from_start(4, 4, "\"", 10), t_from_end(6, 6, "\"", 10)],
                },
                Fix {
                    replacements: vec![t_from_end(6, 6, " || exit", 5)],
                },
            ],
        );
    }

    #[test]
    fn compose_fixes3() {
        test_fixes(
            "(x)[x]",
            "xx",
            &[Fix {
                replacements: vec![
                    t_from_start(1, 1, "(", 4),
                    t_from_end(2, 2, ")", 3),
                    t_from_start(2, 2, "[", 2),
                    t_from_end(3, 3, "]", 1),
                ],
            }],
        );
    }

    #[test]
    fn compose_fixes5() {
        test_fixes(
            "\"$(x)\"",
            "`x`",
            &[Fix {
                replacements: vec![
                    t_from_start(1, 2, "$(", 2),
                    t_from_end(3, 4, ")", 2),
                    t_from_start(1, 1, "\"", 1),
                    t_from_end(4, 4, "\"", 1),
                ],
            }],
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
