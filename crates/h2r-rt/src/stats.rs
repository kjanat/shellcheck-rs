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

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::fmt::Write;
use std::sync::{Mutex, OnceLock};

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

// Per-site attribution (WP17a). A thunk is made at one emitted site; the
// emitter numbers the sites densely and passes the number to `delayN_at` /
// `apply_later_at`, which leave it in `CURRENT_SITE` for the one
// `Shared::step` they cause to read, and the cell keeps it in its header. The
// fate of the cell (forced, chased, freed unforced) is then counted against
// the site, not only against the cell's kind.

/// The site of a thunk that no emitted site made: the runtime's own (`map_list`
/// and friends), `defer`, and the `defer_to` of a block with too many captures.
pub const NO_SITE: u32 = u32::MAX;

/// What the emitter knows about one thunk-creating site, written into the
/// entry crate as `static SITES: &[SiteInfo]`, indexed by site id, and handed
/// to [`install_sites`] at program start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SiteInfo {
    /// The generated crate that holds the site (`-` for a single-file program).
    pub krate: &'static str,
    /// The Haskell binder the function was lowered from.
    pub function: &'static str,
    /// The instance number (`f_<instance>`, `b_<instance>_<block>` in the source).
    pub instance: u32,
    /// The NIR block the site is in.
    pub block: u32,
    /// Where it is written: `DelayBlock` instruction, `f_` wrapper, looping tail ..
    pub kind: &'static str,
    /// Which rule and Core form it came from.
    pub origin: &'static str,
    /// What first uses a `DelayBlock` thunk (empty for the other kinds).
    pub used_by: &'static str,
    /// How many values the thunk captures.
    pub captured: u32,
}

static SITE_TABLE: OnceLock<&'static [SiteInfo]> = OnceLock::new();

/// Install the emitter's site table. The first call wins; later ones (every
/// entry function of a typed API installs it) are ignored.
pub fn install_sites(sites: &'static [SiteInfo]) {
    SITE_TABLE.get_or_init(|| sites);
}

/// The counters kept per site.
pub const SITE_CREATED: usize = 0;
pub const SITE_FORCED_UNIQUE: usize = 1;
pub const SITE_FORCED_SHARED: usize = 2;
pub const SITE_CHASED_UNIQUE: usize = 3;
pub const SITE_CHASED_SHARED: usize = 4;
pub const SITE_UNFORCED: usize = 5;
const SITE_FIELDS: usize = 6;

type SiteCounts = [u64; SITE_FIELDS];

thread_local! {
    static CURRENT_SITE: Cell<u32> = const { Cell::new(NO_SITE) };
    // Slot 0 is `NO_SITE`; site `n` is slot `n + 1`. A thread that is being
    // torn down no longer has it (`try_with`): a cell freed that late is not
    // counted.
    static SITE_LOCAL: RefCell<Vec<SiteCounts>> = const { RefCell::new(Vec::new()) };
}

static SITE_TOTAL: Mutex<Vec<SiteCounts>> = Mutex::new(Vec::new());

fn slot(site: u32) -> usize {
    if site == NO_SITE {
        0
    } else {
        site as usize + 1
    }
}

/// Name the site of the next thunk this thread makes.
#[inline]
pub fn set_site(site: u32) {
    CURRENT_SITE
        .try_with(|current| current.set(site))
        .unwrap_or_default();
}

/// The site the next thunk is made at, which is then spent.
#[inline]
pub fn take_site() -> u32 {
    CURRENT_SITE
        .try_with(|current| current.replace(NO_SITE))
        .unwrap_or(NO_SITE)
}

/// Add one to counter `field` of `site` (one of the `SITE_*` constants).
#[inline]
pub fn bump_site(site: u32, field: usize) {
    SITE_LOCAL
        .try_with(|local| {
            let mut local = local.borrow_mut();
            let slot = slot(site);
            if local.len() <= slot {
                local.resize(slot + 1, [0; SITE_FIELDS]);
            }
            local[slot][field] += 1;
        })
        .unwrap_or_default();
}

/// A counter of `site` on the calling thread.
pub fn site_get(site: u32, field: usize) -> u64 {
    SITE_LOCAL.with(|local| {
        local
            .borrow()
            .get(slot(site))
            .map_or(0, |counts| counts[field])
    })
}

fn merge(into: &mut Vec<SiteCounts>, from: &[SiteCounts]) {
    if into.len() < from.len() {
        into.resize(from.len(), [0; SITE_FIELDS]);
    }
    for (sum, counts) in into.iter_mut().zip(from) {
        for (a, b) in sum.iter_mut().zip(counts) {
            *a += b;
        }
    }
}

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
    let mut sites = SITE_TOTAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    SITE_LOCAL.with(|local| merge(&mut sites, &local.take()));
}

/// Per-site counts, process-wide plus the calling thread's own: index 0 is
/// the thunks no site made, index `n + 1` is site `n`.
fn site_totals() -> Vec<SiteCounts> {
    let mut sites = SITE_TOTAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone();
    SITE_LOCAL.with(|local| merge(&mut sites, &local.borrow()));
    sites
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
    render(&totals(), &site_totals())
}

fn row(out: &mut String, label: &str, count: u64) {
    put!(out, "  {label:<34}{count:>14}");
}

fn render(c: &[u64], sites: &[SiteCounts]) -> String {
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
    render_sites(&mut out, sites, SITE_TABLE.get().copied().unwrap_or(&[]));
    out
}

/// One site's row: id, counts, and what the table says about it.
struct SiteRow<'a> {
    id: Option<usize>,
    counts: SiteCounts,
    info: Option<&'a SiteInfo>,
}

fn percent(part: u64, whole: u64) -> f64 {
    if whole == 0 {
        0.0
    } else {
        part as f64 * 100.0 / whole as f64
    }
}

fn site_heading(out: &mut String, first: &str) {
    put!(
        out,
        "  {first:>7}{:>11}{:>11}{:>11}{:>11}{:>11}{:>11}{:>8}  where",
        "created",
        "forced",
        "forced shr",
        "chased",
        "chased shr",
        "unforced",
        "unf %"
    );
}

fn site_counts_line(out: &mut String, label: &str, counts: &SiteCounts) {
    let [
        created,
        forced,
        forced_shared,
        chased,
        chased_shared,
        unforced,
    ] = *counts;
    write!(
        out,
        "  {label:>7}{created:>11}{forced:>11}{forced_shared:>11}{chased:>11}{chased_shared:>11}{unforced:>11}{:>7.1}%  ",
        percent(unforced, created)
    )
    .expect("writing to a String");
}

fn site_top(out: &mut String, title: &str, rows: &mut [SiteRow<'_>], by: usize) {
    const TOP: usize = 40;
    rows.sort_by(|a, b| {
        b.counts[by]
            .cmp(&a.counts[by])
            .then_with(|| b.counts[SITE_CREATED].cmp(&a.counts[SITE_CREATED]))
            .then_with(|| a.id.cmp(&b.id))
    });
    put!(out, "\n{title}");
    site_heading(out, "site");
    for row in rows.iter().take(TOP).filter(|row| row.counts[by] != 0) {
        let label = row.id.map_or("none".to_string(), |id| id.to_string());
        site_counts_line(out, &label, &row.counts);
        match row.info {
            Some(info) => put!(
                out,
                "{} {}#{} b{} | {} / {} | used by: {} | {} captured",
                info.krate,
                info.function,
                info.instance,
                info.block,
                info.kind,
                info.origin,
                if info.used_by.is_empty() {
                    "-"
                } else {
                    info.used_by
                },
                info.captured
            ),
            None if row.id.is_some() => put!(out, "(no site table installed, or id outside it)"),
            None => put!(out, "(thunks no emitted site made)"),
        }
    }
}

fn site_rollup<'a>(
    out: &mut String,
    title: &str,
    rows: &[SiteRow<'a>],
    key: impl Fn(&'a SiteInfo) -> String,
) {
    let mut groups: BTreeMap<String, (u64, SiteCounts)> = BTreeMap::new();
    for row in rows {
        let name = row.info.map_or_else(|| "(unattributed)".to_string(), &key);
        let (sites, counts) = groups.entry(name).or_default();
        *sites += u64::from(row.id.is_some());
        for (sum, count) in counts.iter_mut().zip(row.counts) {
            *sum += count;
        }
    }
    let mut groups: Vec<_> = groups
        .into_iter()
        .filter(|(_, (sites, counts))| *sites != 0 || counts.iter().any(|&count| count != 0))
        .collect();
    groups.sort_by(|a, b| {
        b.1.1[SITE_UNFORCED]
            .cmp(&a.1.1[SITE_UNFORCED])
            .then_with(|| a.0.cmp(&b.0))
    });
    put!(out, "\n{title}");
    site_heading(out, "sites");
    let mut total: SiteCounts = [0; SITE_FIELDS];
    let mut all_sites = 0;
    for (name, (sites, counts)) in &groups {
        site_counts_line(out, &sites.to_string(), counts);
        put!(out, "{name}");
        all_sites += sites;
        for (sum, count) in total.iter_mut().zip(counts) {
            *sum += count;
        }
    }
    site_counts_line(out, &all_sites.to_string(), &total);
    put!(out, "total");
}

/// The per-site tables: the top 40 sites by unforced and by created count,
/// and roll-ups by where the site is written, by origin and by use.
fn render_sites(out: &mut String, counts: &[SiteCounts], table: &'static [SiteInfo]) {
    out.push_str("\nthunks by emitter site (WP17a)\n");
    put!(
        out,
        "  {} sites in the installed table, {} with a thunk made",
        table.len(),
        counts
            .iter()
            .skip(1)
            .filter(|c| c[SITE_CREATED] != 0)
            .count()
    );
    let mut rows: Vec<SiteRow<'_>> = (0..counts.len().max(table.len() + 1))
        .map(|slot| SiteRow {
            id: slot.checked_sub(1),
            counts: counts.get(slot).copied().unwrap_or([0; SITE_FIELDS]),
            info: slot.checked_sub(1).and_then(|id| table.get(id)),
        })
        .collect();
    site_top(
        out,
        "top 40 sites by thunks freed unforced",
        &mut rows,
        SITE_UNFORCED,
    );
    site_top(
        out,
        "top 40 sites by thunks created",
        &mut rows,
        SITE_CREATED,
    );
    site_rollup(out, "by where written", &rows, |info| info.kind.to_string());
    site_rollup(
        out,
        "by origin: where written / rule / Core form",
        &rows,
        |info| format!("{} / {}", info.kind, info.origin),
    );
    site_rollup(
        out,
        "by what uses a DelayBlock thunk first",
        &rows,
        |info| {
            if info.used_by.is_empty() {
                format!("({})", info.kind)
            } else {
                info.used_by.to_string()
            }
        },
    );
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
