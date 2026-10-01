//! A static census of the allocations the emitter writes (WP13).
//!
//! With `H2R_CENSUS=1` in the environment at emit time, [`Guard::from_env`]
//! turns collection on and prints to stderr, when the emission ends, how many
//! delayed-thunk sites (`delayed()`: a `DelayBlock` instruction, the `f_`
//! wrapper of a lifted result, a looping tail arm) were written, from which
//! rule and Core form, with how many captured arguments, and how many
//! `HData::ready` sites there are by arity. The counts are of *sites*, not of
//! what runs: the runtime's `stats` feature counts executions, and the two
//! together say which site makes the thunks that nobody forces.
//!
//! Collection lives in a thread-local so the emitter's functions take no extra
//! parameter; when it is off every hook is one thread-local read.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::Write;

use h2r_core_ir::Expr;

use crate::emit::operands;

/// `writeln!` to a `String`, which cannot fail.
macro_rules! put {
    ($out:expr, $($arg:tt)*) => {
        writeln!($out, $($arg)*).expect("writing to a String")
    };
}
use crate::nir::{Block, Exit, Operation, Source, World};

/// Where in the emitter a delayed thunk is written, and what it came from.
/// Built by the constructors below; empty (and free) when no census is on.
#[derive(Debug, Default)]
pub(crate) struct Site {
    kind: &'static str,
    origin: String,
    used_by: Option<&'static str>,
}

impl Site {
    /// A `DelayBlock` instruction: the rule and Core form it came from, and
    /// what the block does with its result.
    pub(crate) fn instruction(world: &World<'_>, block: &Block, position: usize) -> Site {
        if !active() {
            return Site::default();
        }
        let instruction = &block.instructions[position];
        let source = match instruction.origin.source {
            Source::Expr(expr) => world
                .at(instruction.origin.module)
                .map_or("expression", |module| core_form(module, expr)),
            Source::Binder(_) => "binder",
        };
        Site {
            kind: "DelayBlock instruction",
            origin: format!("{:?} / {source}", instruction.origin.rule),
            used_by: Some(use_of(block, position)),
        }
    }

    /// The `f_` function of a lifted result: a thunk of the whole body.
    pub(crate) fn wrapper(caf: bool) -> Site {
        if !active() {
            return Site::default();
        }
        Site {
            kind: if caf {
                "f_ wrapper (no parameters: cached CAF)"
            } else {
                "f_ wrapper (lifted result)"
            },
            origin: "function entry".into(),
            used_by: None,
        }
    }

    /// A transfer into a block that loops back to this one, from the
    /// instruction that ended it (a tail call or a tail `case` arm).
    pub(crate) fn tail(kind: &'static str, instruction: &crate::nir::Instruction) -> Site {
        if !active() {
            return Site::default();
        }
        Site {
            kind,
            origin: format!("{:?}", instruction.origin.rule),
            used_by: None,
        }
    }

    /// A transfer by `Exit::Jump` or `Exit::IntSwitch` into a looping block.
    pub(crate) fn jump() -> Site {
        if !active() {
            return Site::default();
        }
        Site {
            kind: "looping tail jump",
            origin: "block exit (Jump / IntSwitch)".into(),
            used_by: None,
        }
    }
}

fn core_form(module: &h2r_core_ir::Module, expr: h2r_core_ir::ExprId) -> &'static str {
    match module.expr(expr) {
        Expr::Var { .. } => "Var",
        Expr::Lit(_) => "Lit",
        Expr::App { .. } => {
            let mut head = expr;
            while let Expr::App { fun, .. } = module.expr(head) {
                head = *fun;
            }
            match module.expr(head) {
                Expr::Var {
                    is_global: true, ..
                } => "App (call of a global)",
                Expr::Var { .. } => "App (call of a local)",
                _ => "App (other head)",
            }
        }
        Expr::Lam { .. } => "Lam",
        Expr::Let { .. } => "Let",
        Expr::Case { .. } => "Case",
        Expr::Cast { .. } => "Cast",
        Expr::Tick(_) => "Tick",
        Expr::Type { .. } | Expr::Coercion => "Type",
    }
}

/// What the first later use of a delayed value is.
fn use_of(block: &Block, position: usize) -> &'static str {
    let id = block.instructions[position].result.id;
    for later in &block.instructions[position + 1..] {
        if !operands(&later.operation)
            .iter()
            .any(|(used, _)| *used == id)
        {
            continue;
        }
        return match &later.operation {
            Operation::CallTop { .. } => "argument of a top-level call",
            Operation::CallLocal { .. } => "argument of a local call",
            Operation::Apply { .. } => "argument of an unknown call",
            Operation::Construct { .. } => "field of a constructor",
            Operation::MakeClosure { .. } | Operation::LocalScope { .. } => {
                "captured by a closure or local scope"
            }
            Operation::DelayBlock { .. } => "captured by another delay",
            Operation::EvaluateBlock { .. } => "captured by an evaluated block",
            Operation::MatchData { .. } => "captured by a case",
            Operation::Force(_) | Operation::Move(_) => "forced or moved at once",
            Operation::AppendList { .. }
            | Operation::UnpackString(_)
            | Operation::ListPredicate(_)
            | Operation::ListFunction(_)
            | Operation::CompareStrings(_)
            | Operation::RaiseCallStackError(_)
            | Operation::RaiseError { .. }
            | Operation::Machine { .. }
            | Operation::PointerEquality { .. }
            | Operation::FillCell { .. }
            | Operation::DataToTag { .. } => "lazy argument of an external or primitive",
            _ => "other operation",
        };
    }
    match &block.terminator.exit {
        Exit::Return(v) if *v == id => "returned",
        Exit::Jump { args, .. } | Exit::IntSwitch { args, .. } if args.contains(&id) => {
            "argument of a jump"
        }
        _ => "unused",
    }
}

#[derive(Default)]
struct Tally {
    sites: u64,
    captured: u64,
}

impl Tally {
    fn add(&mut self, captured: usize) {
        self.sites += 1;
        self.captured += captured as u64;
    }
}

#[derive(Default)]
struct Census {
    delays: u64,
    by_kind: BTreeMap<&'static str, Tally>,
    by_origin: BTreeMap<String, Tally>,
    by_use: BTreeMap<&'static str, Tally>,
    by_captures: BTreeMap<usize, u64>,
    ready: BTreeMap<(&'static str, usize), u64>,
}

thread_local! {
    static CENSUS: RefCell<Option<Census>> = const { RefCell::new(None) };
}

fn active() -> bool {
    CENSUS.with(|census| census.borrow().is_some())
}

/// Count one `delayed()` site capturing `captured` values.
pub(crate) fn delay(site: &Site, captured: usize) {
    CENSUS.with(|census| {
        let mut census = census.borrow_mut();
        let Some(census) = census.as_mut() else {
            return;
        };
        census.delays += 1;
        census.by_kind.entry(site.kind).or_default().add(captured);
        census
            .by_origin
            .entry(format!("{} / {}", site.kind, site.origin))
            .or_default()
            .add(captured);
        if let Some(used_by) = site.used_by {
            census.by_use.entry(used_by).or_default().add(captured);
        }
        *census.by_captures.entry(captured).or_default() += 1;
    });
}

/// Count one `HData::ready(..)` the emitter writes, with `arity` fields.
pub(crate) fn ready(origin: &'static str, arity: usize) {
    CENSUS.with(|census| {
        if let Some(census) = census.borrow_mut().as_mut() {
            *census.ready.entry((origin, arity)).or_default() += 1;
        }
    });
}

/// Collection for the length of one emission. Only the guard that turned
/// collection on takes the census and, if it came from the environment,
/// prints it; one inside another does nothing.
pub(crate) struct Guard {
    owner: bool,
    print: bool,
}

impl Guard {
    /// On when `H2R_CENSUS` is set and not `0` or empty; prints to stderr.
    pub(crate) fn from_env() -> Guard {
        let wanted =
            std::env::var("H2R_CENSUS").is_ok_and(|value| !value.is_empty() && value != "0");
        Guard::start(wanted, true)
    }

    /// On regardless of the environment; the report is read with [`Guard::report`].
    #[cfg(test)]
    pub(crate) fn collecting() -> Guard {
        Guard::start(true, false)
    }

    fn start(wanted: bool, print: bool) -> Guard {
        let owner = wanted
            && CENSUS.with(|census| {
                let mut census = census.borrow_mut();
                let free = census.is_none();
                if free {
                    *census = Some(Census::default());
                }
                free
            });
        Guard { owner, print }
    }

    /// The tables so far.
    #[cfg(test)]
    pub(crate) fn report(&self) -> String {
        CENSUS.with(|census| census.borrow().as_ref().map(render).unwrap_or_default())
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        if self.owner {
            let census = CENSUS.with(|census| census.borrow_mut().take());
            if let (true, Some(census)) = (self.print, census) {
                eprint!("{}", render(&census));
            }
        }
    }
}

fn table<K: std::fmt::Display>(
    out: &mut String,
    title: &str,
    rows: impl Iterator<Item = (K, u64, u64)>,
) {
    let mut rows: Vec<(String, u64, u64)> = rows
        .map(|(key, sites, captured)| (key.to_string(), sites, captured))
        .collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let (sites, captured) = rows
        .iter()
        .fold((0, 0), |(s, c), row| (s + row.1, c + row.2));
    put!(out, "\n{title}");
    put!(
        out,
        "  {:>8}  {:>9}  {:>6}  what",
        "sites",
        "captured",
        "avg"
    );
    for (key, count, captures) in &rows {
        let average = *captures as f64 / (*count).max(1) as f64;
        put!(out, "  {count:>8}  {captures:>9}  {average:>6.2}  {key}");
    }
    let average = captured as f64 / sites.max(1) as f64;
    put!(out, "  {sites:>8}  {captured:>9}  {average:>6.2}  total");
}

fn render(census: &Census) -> String {
    let mut out = String::from("h2r-lower emitter census (H2R_CENSUS)\n");
    let tally = |map: &BTreeMap<&'static str, Tally>| {
        map.iter()
            .map(|(key, tally)| (*key, tally.sites, tally.captured))
            .collect::<Vec<_>>()
    };
    table(
        &mut out,
        "delayed() sites by where they are written",
        tally(&census.by_kind).into_iter(),
    );
    table(
        &mut out,
        "delayed() sites by origin: site / rule / Core form",
        census
            .by_origin
            .iter()
            .map(|(key, tally)| (key.as_str(), tally.sites, tally.captured)),
    );
    table(
        &mut out,
        "DelayBlock instructions by what uses the thunk first",
        tally(&census.by_use).into_iter(),
    );
    put!(out, "\ndelayed() sites by number of captured arguments");
    for (captured, sites) in &census.by_captures {
        put!(out, "  {captured:>3} captured: {sites:>8} sites");
    }
    put!(out, "\nHData::ready sites by arity");
    let mut by_arity: BTreeMap<usize, u64> = BTreeMap::new();
    for ((_, arity), sites) in &census.ready {
        *by_arity.entry(*arity).or_default() += sites;
    }
    for (arity, sites) in &by_arity {
        put!(out, "  arity {arity:>2}: {sites:>8} sites");
    }
    put!(
        out,
        "  {:>9}: {:>8} sites",
        "total",
        by_arity.values().sum::<u64>()
    );
    put!(out, "\nHData::ready sites by origin and arity");
    for ((origin, arity), sites) in &census.ready {
        put!(out, "  {origin:<28} arity {arity:>2}: {sites:>8} sites");
    }
    out
}
