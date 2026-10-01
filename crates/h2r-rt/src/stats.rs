//! Allocation census counters (the `stats` cargo feature; WP13).
//!
//! Every counter is a plain `Cell<u64>` in a thread-local array, so counting
//! is a load, an add and a store, and a unit test sees only its own thread.
//! The program runs on a thread of its own (`on_program_stack`), which
//! [`flush`]es its counts into process-wide totals when it ends; [`report`]
//! renders those totals plus the calling thread's own, and `on_program_stack`
//! prints it to stderr once the program thread has been joined.
//!
//! This module is compiled only with the feature, and is pasted into the
//! generated crates (see `runtime_source` in `h2r-lower`) the same way as
//! `cell.rs`, so it names nothing outside itself.

use std::cell::Cell;
use std::fmt::Write;
use std::sync::Mutex;

/// `writeln!` to a `String`, which cannot fail.
macro_rules! put {
    ($out:expr, $($arg:tt)*) => {
        writeln!($out, $($arg)*).expect("writing to a String")
    };
}

/// The kinds of cell a `Shared<T>` can be, by what `T` is.
pub const KINDS: usize = 5;
const KIND_NAMES: [&str; KINDS] = ["Int", "Data", "Closure", "Field", "other"];

/// Which kind of cell `T` makes. Matches on the type's name so that the one
/// definition serves both the crate and its pasted copy (a different path).
pub fn kind<T>() -> usize {
    let name = std::any::type_name::<T>();
    if name == "i64" {
        0
    } else if name.ends_with("Node") {
        1
    } else if name.ends_with("ClosureCode") {
        2
    } else if name.ends_with("Field") {
        3
    } else {
        4
    }
}

// Layout of the counter array: families first, then single counters.
/// `delayN`, by N (0..=16).
pub const DELAY: usize = 0;
/// `stepN`, by N (0..=16).
pub const STEP: usize = DELAY + 17;
/// `Data::ready`, by arity: 0, 1, 2, 3, more.
pub const READY: usize = STEP + 17;
/// Lazy cells made by `Shared::step` (every thunk: `delayN`, `apply_later`,
/// `defer`, ...), by kind.
pub const CREATED: usize = READY + 5;
/// Cells made by `Shared::pending` (to be filled), by kind.
pub const PENDING: usize = CREATED + KINDS;
/// Already-evaluated cells (`Shared::ready`, `ready_with`), by kind.
pub const EVALUATED: usize = PENDING + KINDS;
/// First force (`force_slow`) of a cell nobody else holds, by kind.
pub const FORCED_UNIQUE: usize = EVALUATED + KINDS;
/// First force (`force_slow`) of a cell with strong count above one, by kind.
pub const FORCED_SHARED: usize = FORCED_UNIQUE + KINDS;
/// A cell entered by `chase` while only the chase held it (moved through, not
/// memoised), by kind.
pub const CHASED_UNIQUE: usize = FORCED_SHARED + KINDS;
/// A cell entered by `chase` that others hold too (memoised), by kind.
pub const CHASED_SHARED: usize = CHASED_UNIQUE + KINDS;
/// A cell freed while still holding its `Once` code: a thunk nobody forced.
pub const DROPPED_UNFORCED: usize = CHASED_SHARED + KINDS;
/// A cell freed while still holding `Pending` code: never filled.
pub const DROPPED_PENDING: usize = DROPPED_UNFORCED + KINDS;
/// The value of an evaluated cell taken out of it (unique owner), by kind.
pub const MOVED_UNIQUE: usize = DROPPED_PENDING + KINDS;
/// The value of an evaluated cell cloned out of it (other owners), by kind.
pub const COPIED: usize = MOVED_UNIQUE + KINDS;
/// `Int/Data/Closure/Field::defer_to` calls (what `delayN` calls), by kind.
pub const DEFER_TO: usize = COPIED + KINDS;
const SINGLES: usize = DEFER_TO + KINDS;

pub const APPLY_LATER: usize = SINGLES;
pub const APPLY_STEP: usize = SINGLES + 1;
pub const BIND: usize = SINGLES + 2;
pub const BIND_ENTERING: usize = SINGLES + 3;
/// `Closure::ready` and `Closure::entering`: a boxed Rust closure as code.
pub const BOXED: usize = SINGLES + 4;
pub const PARTIAL: usize = SINGLES + 5;
pub const APPLY: usize = SINGLES + 6;
pub const APPLY_GENERAL: usize = SINGLES + 7;
pub const APPLY_OVER: usize = SINGLES + 8;
/// `Field::data` on a field that is still a thunk (`deferred_data`).
pub const DEFERRED_DATA: usize = SINGLES + 9;
const COUNTERS: usize = SINGLES + 10;

thread_local! {
    static LOCAL: [Cell<u64>; COUNTERS] = const { [const { Cell::new(0) }; COUNTERS] };
}

static TOTAL: Mutex<[u64; COUNTERS]> = Mutex::new([0; COUNTERS]);

/// Add one to counter `index`.
#[inline]
pub fn bump(index: usize) {
    // No destructor, so the thread-local is always accessible.
    LOCAL.with(|local| local[index].set(local[index].get() + 1));
}

/// Add one to the counter of `family` for cells of type `T`.
#[inline]
pub fn bump_kind<T>(family: usize) {
    bump(family + kind::<T>());
}

/// The calling thread's own counts.
pub fn snapshot() -> Vec<u64> {
    LOCAL.with(|local| local.iter().map(Cell::get).collect())
}

/// A counter of the calling thread.
pub fn get(index: usize) -> u64 {
    LOCAL.with(|local| local[index].get())
}

/// Move the calling thread's counts into the process-wide totals.
pub fn flush() {
    let mut total = TOTAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    LOCAL.with(|local| {
        for (sum, count) in total.iter_mut().zip(local) {
            *sum += count.replace(0);
        }
    });
}

fn totals() -> Vec<u64> {
    let total = TOTAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let local = snapshot();
    total.iter().zip(local).map(|(a, b)| a + b).collect()
}

/// Print [`report`] to stderr.
pub fn print_report() {
    eprint!("{}", report());
}

/// The census as a table: process-wide totals plus the calling thread's own.
pub fn report() -> String {
    render(&totals())
}

fn row(out: &mut String, label: &str, count: u64) {
    put!(out, "  {label:<34}{count:>14}");
}

fn render(c: &[u64]) -> String {
    let mut out = String::from("h2r-rt allocation census (feature `stats`)\n");
    let sum = |from: usize, len: usize| c[from..from + len].iter().sum::<u64>();

    out.push_str("\nthunks (cells made by Shared::step) by what they hold\n");
    for (k, name) in KIND_NAMES.iter().enumerate() {
        row(&mut out, name, c[CREATED + k]);
    }
    row(&mut out, "total", sum(CREATED, KINDS));

    out.push_str("\nfate of those thunks\n");
    put!(
        out,
        "  {:<10}{:>12}{:>12}{:>12}{:>12}{:>12}{:>12}{:>9}",
        "kind",
        "created",
        "forced",
        "forced shr",
        "chased",
        "chased shr",
        "unforced",
        "unf %"
    );
    for (k, name) in KIND_NAMES.iter().enumerate() {
        let created = c[CREATED + k];
        let unforced = c[DROPPED_UNFORCED + k];
        let share = if created == 0 {
            0.0
        } else {
            unforced as f64 * 100.0 / created as f64
        };
        put!(
            out,
            "  {name:<10}{created:>12}{:>12}{:>12}{:>12}{:>12}{unforced:>12}{share:>8.1}%",
            c[FORCED_UNIQUE + k],
            c[FORCED_SHARED + k],
            c[CHASED_UNIQUE + k],
            c[CHASED_SHARED + k],
        );
    }
    put!(
        out,
        "  {:<10}{:>12}{:>12}{:>12}{:>12}{:>12}{:>12}",
        "total",
        sum(CREATED, KINDS),
        sum(FORCED_UNIQUE, KINDS),
        sum(FORCED_SHARED, KINDS),
        sum(CHASED_UNIQUE, KINDS),
        sum(CHASED_SHARED, KINDS),
        sum(DROPPED_UNFORCED, KINDS),
    );
    out.push_str(
        "  forced: first force_slow of a cell held once / by several owners;\n  chased: entered by chase (held once: moved through, never memoised / shared: memoised);\n  unforced: freed still holding its code. forced and chased include forced pending cells.\n",
    );

    out.push_str("\nvalues taken out of evaluated cells\n");
    for (k, name) in KIND_NAMES.iter().enumerate() {
        put!(
            out,
            "  {name:<10}moved out unique {:>12}   cloned {:>12}",
            c[MOVED_UNIQUE + k],
            c[COPIED + k]
        );
    }

    out.push_str("\ncells with no code to run\n");
    for (k, name) in KIND_NAMES.iter().enumerate() {
        put!(
            out,
            "  {name:<10}evaluated (ready) {:>12}   pending {:>12}   pending dropped unfilled {:>10}",
            c[EVALUATED + k],
            c[PENDING + k],
            c[DROPPED_PENDING + k]
        );
    }

    out.push_str("\ndelayN by number of captured arguments (stepN in the second column)\n");
    for n in 0..=16 {
        if c[DELAY + n] != 0 || c[STEP + n] != 0 {
            put!(
                out,
                "  delay{n:<8}{:>14}   step{n:<8}{:>14}",
                c[DELAY + n],
                c[STEP + n]
            );
        }
    }
    row(&mut out, "delayN total", sum(DELAY, 17));
    row(&mut out, "stepN total", sum(STEP, 17));
    for (k, name) in KIND_NAMES.iter().enumerate().take(4) {
        row(&mut out, &format!("{name}::defer_to"), c[DEFER_TO + k]);
    }

    out.push_str("\nData::ready by arity\n");
    for (label, index) in ["0", "1", "2", "3", "4+"].iter().zip(0..) {
        row(&mut out, &format!("arity {label}"), c[READY + index]);
    }
    row(&mut out, "total", sum(READY, 5));

    out.push_str("\ncalls\n");
    row(&mut out, "apply_later", c[APPLY_LATER]);
    row(&mut out, "apply_step", c[APPLY_STEP]);
    row(&mut out, "Closure::bind", c[BIND]);
    row(&mut out, "Closure::bind_entering", c[BIND_ENTERING]);
    row(&mut out, "Closure::ready/entering (boxed)", c[BOXED]);
    row(&mut out, "partial applications", c[PARTIAL]);
    row(&mut out, "Closure::apply", c[APPLY]);
    row(&mut out, "  apply_general", c[APPLY_GENERAL]);
    row(&mut out, "  apply_over", c[APPLY_OVER]);
    row(&mut out, "Field::data of a thunk", c[DEFERRED_DATA]);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_kind_of_a_cell_follows_its_type() {
        assert_eq!(kind::<i64>(), 0);
        assert_eq!(kind::<super::super::Node>(), 1);
        assert_eq!(kind::<super::super::ClosureCode>(), 2);
        assert_eq!(kind::<super::super::Field>(), 3);
        assert_eq!(kind::<u8>(), 4);
        assert!(report().contains("allocation census"));
    }
}
