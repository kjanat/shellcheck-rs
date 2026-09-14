//! The residual-laziness census.
//!
//! For every local binding left after GHC's optimiser, decide *why* it still
//! exists and what it would have to become in Rust. The principle: emit
//! deferred evaluation only where the optimised Core still demonstrates
//! conditional evaluation that Rust control flow cannot trivially preserve.
//!
//! Two sources of evidence are combined and cross-checked:
//!
//! * GHC's own analysis — the binder's demand (strict / absent / used once)
//!   and occurrence info — which is sound and accounts for what callees do.
//! * A syntactic occurrence analysis of our own: where every use of the
//!   binder sits relative to the `let`, whether uses are in mutually
//!   exclusive case alternatives, whether any is captured by a lambda that
//!   may be entered more than once, and what each use *position* demands.
//!
//! The last point matters: sinking `let x = e in f x` to `f e` removes the
//! thunk only if `f` is strict in that argument. Otherwise the thunk moves
//! into the argument and the census must not count it as gone.

use std::collections::HashMap;

use h2r_core_ir::{Binder, BinderKind, Edge, Expr, ExprId, Module, Pair};
use serde::Serialize;

use crate::shape::{
    ArgShape, Position, RhsKind, arg_shape, is_dictionary_head, position, value_args,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Class {
    /// RHS is a lambda: a closure, not a thunk.
    Function,
    /// GHC join point: control flow, never a value.
    JoinPoint,
    /// Never used.
    Dead,
    /// RHS is a variable or literal: a rename.
    Alias,
    /// RHS is already a value (constructor, partial application).
    Value,
    /// Definitely demanded, evaluated at most once: an owned Rust value.
    StrictValue,
    /// Definitely demanded, used many times: a Rust value that is shared.
    StrictShared,
    /// Conditionally demanded, evaluated at most once.
    LazyOnce,
    /// Conditionally demanded, possibly evaluated from several places.
    LazyShared,
    /// Non-function member of a recursive group: knot-tying.
    RecursiveValue,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum DemandClass {
    /// Demanded on every path (GHC: strict).
    Must,
    /// Conditionally demanded.
    May,
    /// Never demanded (GHC: absent).
    Never,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Multiplicity {
    Once,
    Many,
    Unknown,
}

/// Where a conditionally-demanded binding could be moved to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum Sink {
    /// Single use: the RHS can be placed at the use site.
    Inline {
        at: ExprId,
        position: Position,
    },
    /// Uses are in mutually exclusive alternatives of this case: the `let`
    /// can be duplicated into each branch.
    Branches {
        case: ExprId,
        leaves: u32,
        all_eager: bool,
    },
    /// Several uses on the same path, not all of them demanded.
    Shared,
    /// A use is captured by a lambda that may be entered more than once.
    UnderLambda {
        lam: ExprId,
    },
    NotApplicable,
}

/// What would have to be emitted for a potential thunk site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Fate {
    NotAThunk,
    /// Sinks to a position that evaluates it: the thunk disappears.
    SinkEager,
    /// Sinks, but into a lazy argument position: the thunk moves, it does
    /// not vanish. Whether it survives is now the callee's question.
    SinkLazyPosition,
    /// Needs memoisation (`Lazy<T>`): shared on a path or captured.
    Memo,
    Recursive,
    Unknown,
}

/// Where a binder came from, judged by GHC's naming conventions. Heuristic,
/// but it separates compiler-introduced bindings from user code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Origin {
    /// `$d…`: a type-class dictionary; erased by specialisation.
    Dictionary,
    /// `lvl…`: full-laziness float-out — GHC hoisted work out of a lambda
    /// to share it. Sinking it back is semantically valid.
    FloatOut,
    /// `ds…`: desugarer-introduced, typically a lazy pattern binding.
    Desugar,
    /// `eta…`: eta-expansion artifact (monadic state plumbing).
    Eta,
    /// `$w…` / `$s…`: worker-wrapper or specialisation.
    WorkerOrSpec,
    /// `$j…`: join point.
    Join,
    User,
}

impl Origin {
    pub fn of(occ: &str) -> Origin {
        fn numbered(s: &str, prefix: &str) -> bool {
            s.strip_prefix(prefix)
                .is_some_and(|r| r.chars().all(|c| c.is_ascii_digit()))
        }
        if occ.starts_with("$d") {
            Origin::Dictionary
        } else if numbered(occ, "lvl") {
            Origin::FloatOut
        } else if numbered(occ, "ds") {
            Origin::Desugar
        } else if numbered(occ, "eta") {
            Origin::Eta
        } else if occ.starts_with("$w") || occ.starts_with("$s") {
            Origin::WorkerOrSpec
        } else if occ.starts_with("$j") {
            Origin::Join
        } else {
            Origin::User
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct BindingReport {
    pub module: String,
    pub occ: String,
    pub origin: Origin,
    pub unique: String,
    pub let_node: ExprId,
    pub rhs: ExprId,
    pub class: Class,
    pub rhs_kind: RhsKind,
    pub demand: DemandClass,
    pub demand_pretty: String,
    pub multiplicity: Multiplicity,
    /// GHC's usage cardinality for the binder, for cross-checking.
    pub ghc_used_once: Option<bool>,
    /// Our syntactic verdict, before combining with GHC's.
    pub syntactic_once: Option<bool>,
    pub recursive: bool,
    pub whnf: bool,
    pub cheap: bool,
    pub ok_for_spec: bool,
    pub trivial: bool,
    pub occurrences: usize,
    pub sink: Sink,
    pub fate: Fate,
    pub reasons: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TopClass {
    Function,
    Value,
    Alias,
    /// A string literal (`unpackCString# "..."#`): static data, not a thunk.
    StringLiteral,
    /// A pattern-match-failure or `error` CAF: a panic at the use site.
    Bottom,
    /// A genuine top-level thunk: evaluated once on first use.
    Caf,
}

#[derive(Debug, Clone, Serialize)]
pub struct TopReport {
    pub module: String,
    pub occ: String,
    pub class: TopClass,
    pub rhs_kind: RhsKind,
    pub cheap: bool,
    pub ok_for_spec: bool,
}

/// A non-trivial argument: something CorePrep would have to let-bind, i.e.
/// an allocation the `let` census cannot see.
#[derive(Debug, Clone, Serialize)]
pub struct ArgSite {
    pub module: String,
    pub app: ExprId,
    pub arg: ExprId,
    pub shape: ArgShape,
    pub position: Position,
    pub dictionary: bool,
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct Agreement {
    pub both_once: usize,
    pub ghc_once_syntax_many: usize,
    pub ghc_many_syntax_once: usize,
    pub both_many: usize,
}

#[derive(Debug, Default, Serialize)]
pub struct Census {
    pub bindings: Vec<BindingReport>,
    pub top: Vec<TopReport>,
    pub args: Vec<ArgSite>,
    pub agreement: Agreement,
}

impl Census {
    pub fn of_modules<'a>(modules: impl IntoIterator<Item = &'a Module>) -> Census {
        let mut census = Census::default();
        for m in modules {
            census.add_module(m);
        }
        census
    }

    pub fn add_module(&mut self, m: &Module) {
        let occs = occurrence_map(m);

        for bind in &m.top {
            for pair in &bind.pairs {
                self.top.push(top_report(m, pair));
            }
        }

        for id in 0..m.exprs.len() as ExprId {
            match m.expr(id) {
                Expr::Let { bind, .. } => {
                    for pair in &bind.pairs {
                        let r = classify(m, id, pair, bind.recursive, &occs);
                        let candidate = matches!(
                            r.class,
                            Class::StrictValue
                                | Class::StrictShared
                                | Class::LazyOnce
                                | Class::LazyShared
                        );
                        match (r.ghc_used_once, r.syntactic_once) {
                            _ if !candidate => {}
                            (Some(true), Some(true)) => self.agreement.both_once += 1,
                            (Some(true), Some(false)) => self.agreement.ghc_once_syntax_many += 1,
                            (Some(false), Some(true)) => self.agreement.ghc_many_syntax_once += 1,
                            (Some(false), Some(false)) => self.agreement.both_many += 1,
                            _ => {}
                        }
                        self.bindings.push(r);
                    }
                }
                Expr::App { .. } if is_spine_root(m, id) => {
                    self.arg_sites(m, id);
                }
                _ => {}
            }
        }
    }

    fn arg_sites(&mut self, m: &Module, root: ExprId) {
        let (head, args) = m.spine(root);
        let _ = head;
        for arg in value_args(m, &args) {
            let shape = arg_shape(m, arg);
            if shape == ArgShape::Trivial {
                continue;
            }
            let dictionary = {
                let (ahead, _) = m.spine(arg);
                is_dictionary_head(m, ahead)
            };
            self.args.push(ArgSite {
                module: m.name.clone(),
                app: root,
                arg,
                shape,
                position: position(m, arg),
                dictionary,
            });
        }
    }
}

/// Every `Var` occurrence in the module, by unique. Uniques are unique per
/// compilation, so no scoping is needed: every occurrence of a let-bound
/// unique is within that let.
fn occurrence_map(m: &Module) -> HashMap<&str, Vec<ExprId>> {
    let mut map: HashMap<&str, Vec<ExprId>> = HashMap::new();
    for (i, e) in m.exprs.iter().enumerate() {
        if let Expr::Var { unique, .. } = e {
            map.entry(unique.as_str()).or_default().push(i as ExprId);
        }
    }
    map
}

fn is_spine_root(m: &Module, id: ExprId) -> bool {
    match m.parent[id as usize] {
        Some(p) => !(m.edge[id as usize] == Edge::AppFun && matches!(m.expr(p), Expr::App { .. })),
        None => true,
    }
}

fn top_report(m: &Module, pair: &Pair) -> TopReport {
    let rhs_kind = RhsKind::of(m, pair.rhs);
    let class = if pair.trivial {
        TopClass::Alias
    } else if rhs_kind == RhsKind::Lambda {
        TopClass::Function
    } else if pair.whnf {
        TopClass::Value
    } else {
        let (head, _) = m.spine(pair.rhs);
        match m.expr(head) {
            Expr::Var { occ, .. }
                if matches!(
                    occ.as_str(),
                    "unpackCString#" | "unpackCStringUtf8#" | "unpackAppendCString#"
                ) =>
            {
                TopClass::StringLiteral
            }
            Expr::Var { .. } if m.id_info(head).is_some_and(|i| i.dmd_sig.diverges) => {
                TopClass::Bottom
            }
            _ => TopClass::Caf,
        }
    };
    TopReport {
        module: m.name.clone(),
        occ: m.binder(pair.binder).occ.clone(),
        class,
        rhs_kind,
        cheap: pair.cheap,
        ok_for_spec: pair.ok_for_spec,
    }
}

//------------------------------------------------------------------------------
// Occurrence paths
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AltStep {
    case: ExprId,
    alt: u32,
}

#[derive(Debug)]
struct OccPath {
    at: ExprId,
    /// Case alternatives entered between the `let` and the use, root first.
    alts: Vec<AltStep>,
    /// The outermost lambda between the `let` and the use that may be
    /// entered more than once.
    lambda: Option<ExprId>,
    /// The use is inside the recursive group's own right-hand sides.
    in_rhs: bool,
}

fn occ_path(m: &Module, let_node: ExprId, at: ExprId) -> OccPath {
    let mut alts = Vec::new();
    let mut lambda = None;
    let mut in_rhs = false;
    let mut child = at;
    while let Some(parent) = m.parent[child as usize] {
        let edge = m.edge[child as usize];
        if parent == let_node {
            in_rhs = matches!(edge, Edge::LetRhs { .. });
            break;
        }
        match (m.expr(parent), edge) {
            (Expr::Case { .. }, Edge::CaseAlt { alt }) => alts.push(AltStep { case: parent, alt }),
            (Expr::Lam { binder, .. }, Edge::LamBody) => {
                if !transparent_lambda(m, parent, m.binder(*binder)) {
                    lambda = Some(parent);
                }
            }
            _ => {}
        }
        child = parent;
    }
    alts.reverse();
    OccPath {
        at,
        alts,
        lambda,
        in_rhs,
    }
}

/// A lambda that does not create a many-entry closure: a type lambda, a
/// one-shot lambda, or the parameter lambda of a non-recursive join point.
fn transparent_lambda(m: &Module, lam: ExprId, binder: &Binder) -> bool {
    if binder.kind == BinderKind::Tyvar || binder.one_shot == Some(true) {
        return true;
    }
    // Walk up through the lambda chain to see what binds it.
    let mut cur = lam;
    loop {
        let Some(p) = m.parent[cur as usize] else {
            return false;
        };
        match m.edge[cur as usize] {
            Edge::LamBody if matches!(m.expr(p), Expr::Lam { .. }) => cur = p,
            Edge::Cast | Edge::Tick => cur = p,
            Edge::LetRhs { pair } => {
                return match m.expr(p) {
                    // A recursive join point is a loop: its body may run
                    // many times, so only non-recursive ones are transparent.
                    Expr::Let { bind, .. } => {
                        !bind.recursive
                            && m.binder(bind.pairs[pair as usize].binder).is_join_point
                                == Some(true)
                    }
                    _ => false,
                };
            }
            _ => return false,
        }
    }
}

/// If every pair of uses lies in mutually exclusive case alternatives,
/// return the outermost case at which they diverge.
fn exclusive_split(paths: &[OccPath]) -> Option<ExprId> {
    let mut top: Option<ExprId> = None;
    let mut work: Vec<(Vec<usize>, usize)> = vec![((0..paths.len()).collect(), 0)];
    while let Some((group, depth)) = work.pop() {
        if group.len() <= 1 {
            continue;
        }
        let mut case: Option<ExprId> = None;
        let mut by_alt: HashMap<u32, Vec<usize>> = HashMap::new();
        for &i in &group {
            let Some(step) = paths[i].alts.get(depth) else {
                // This use is in the region shared by the others.
                return None;
            };
            match case {
                None => case = Some(step.case),
                // Two different cases at the same depth are both evaluated.
                Some(c) if c != step.case => return None,
                _ => {}
            }
            by_alt.entry(step.alt).or_default().push(i);
        }
        if by_alt.len() > 1 && top.is_none() {
            top = case;
        }
        for (_, sub) in by_alt {
            work.push((sub, depth + 1));
        }
    }
    top
}

//------------------------------------------------------------------------------
// Classification
//------------------------------------------------------------------------------

fn classify(
    m: &Module,
    let_node: ExprId,
    pair: &Pair,
    recursive: bool,
    occs: &HashMap<&str, Vec<ExprId>>,
) -> BindingReport {
    let b = m.binder(pair.binder);
    let rhs_kind = RhsKind::of(m, pair.rhs);
    let mut reasons = Vec::new();

    let paths: Vec<OccPath> = occs
        .get(b.unique.as_str())
        .map(|v| v.iter().map(|&at| occ_path(m, let_node, at)).collect())
        .unwrap_or_default();
    // Uses inside the group's own RHSs are recursion, not consumption.
    let uses: Vec<&OccPath> = paths.iter().filter(|p| !p.in_rhs).collect();
    let self_recursive = paths.iter().any(|p| p.in_rhs);

    let demand = match &b.demand {
        Some(d) if d.absent => DemandClass::Never,
        Some(d) if d.strict => DemandClass::Must,
        Some(_) => DemandClass::May,
        None => DemandClass::Unknown,
    };
    let ghc_used_once = b.demand.as_ref().map(|d| d.used_once);

    let lambda = uses.iter().find_map(|p| p.lambda);
    let split = if uses.len() > 1 {
        exclusive_split(&paths)
    } else {
        None
    };
    let positions: Vec<Position> = uses.iter().map(|p| position(m, p.at)).collect();
    // A use in a lazy argument position hands the *thunk* to the callee,
    // which may force it any number of times; only GHC's cardinality
    // analysis can say more.
    let escapes = positions.iter().any(|p| p.escapes());
    let syntactic_once = if uses.is_empty() {
        None
    } else {
        Some(lambda.is_none() && !escapes && (uses.len() == 1 || split.is_some()))
    };
    let multiplicity = match (ghc_used_once, syntactic_once) {
        (Some(true), _) | (_, Some(true)) => Multiplicity::Once,
        (Some(false), Some(false)) => Multiplicity::Many,
        (Some(false), None) => Multiplicity::Many,
        _ => Multiplicity::Unknown,
    };

    let class = if b.is_join_point == Some(true) {
        reasons.push("GHC join point".into());
        Class::JoinPoint
    } else if uses.is_empty() && !self_recursive
        || matches!(b.occ_info, Some(h2r_core_ir::OccInfo::Dead))
        || demand == DemandClass::Never
    {
        reasons.push("never used".into());
        Class::Dead
    } else if rhs_kind == RhsKind::Lambda {
        reasons.push("RHS is a lambda".into());
        Class::Function
    } else if recursive && self_recursive {
        reasons.push("non-function in a recursive group, refers to itself".into());
        Class::RecursiveValue
    } else if pair.trivial {
        reasons.push("RHS is trivial".into());
        Class::Alias
    } else if pair.whnf {
        reasons.push(format!("RHS is already a value ({rhs_kind:?})"));
        Class::Value
    } else {
        match demand {
            DemandClass::Must => {
                reasons.push(format!(
                    "strictly demanded ({})",
                    b.demand.as_ref().map(|d| d.pretty.as_str()).unwrap_or("")
                ));
                if multiplicity == Multiplicity::Many {
                    reasons.push("used more than once".into());
                    Class::StrictShared
                } else {
                    Class::StrictValue
                }
            }
            DemandClass::May => {
                reasons.push(format!(
                    "not strictly demanded ({})",
                    b.demand.as_ref().map(|d| d.pretty.as_str()).unwrap_or("")
                ));
                if multiplicity == Multiplicity::Many {
                    reasons.push("may be evaluated from several places".into());
                    Class::LazyShared
                } else {
                    Class::LazyOnce
                }
            }
            DemandClass::Never => unreachable!(),
            DemandClass::Unknown => {
                reasons.push("no demand information".into());
                Class::Unknown
            }
        }
    };

    let (sink, fate) = match class {
        Class::LazyOnce | Class::LazyShared => {
            if let Some(lam) = lambda
                && ghc_used_once != Some(true)
            {
                reasons.push(format!(
                    "captured by a lambda that may be entered many times (node {lam})"
                ));
                (Sink::UnderLambda { lam }, Fate::Memo)
            } else if uses.len() == 1 {
                let at = uses[0].at;
                let pos = positions[0];
                let fate = if !pos.escapes() {
                    reasons.push(format!(
                        "single use at node {at} in an evaluating position ({pos:?})"
                    ));
                    Fate::SinkEager
                } else {
                    reasons.push(format!(
                        "single use at node {at}, but in a lazy position ({pos:?})"
                    ));
                    Fate::SinkLazyPosition
                };
                (Sink::Inline { at, position: pos }, fate)
            } else if let Some(case) = split {
                let all_eager = positions.iter().all(|p| !p.escapes());
                reasons.push(format!(
                    "{} uses in mutually exclusive branches of case node {case}",
                    uses.len()
                ));
                let fate = if all_eager {
                    Fate::SinkEager
                } else {
                    reasons.push("some branch uses it in a lazy position".into());
                    Fate::SinkLazyPosition
                };
                (
                    Sink::Branches {
                        case,
                        leaves: uses.len() as u32,
                        all_eager,
                    },
                    fate,
                )
            } else {
                reasons.push(format!(
                    "{} uses that are not mutually exclusive",
                    uses.len()
                ));
                (Sink::Shared, Fate::Memo)
            }
        }
        Class::RecursiveValue => (Sink::NotApplicable, Fate::Recursive),
        Class::Unknown => (Sink::NotApplicable, Fate::Unknown),
        _ => (Sink::NotApplicable, Fate::NotAThunk),
    };

    if pair.ok_for_spec && matches!(fate, Fate::Memo | Fate::SinkLazyPosition) {
        reasons.push("RHS is ok-for-speculation: could simply be evaluated eagerly".into());
    } else if pair.cheap && matches!(fate, Fate::Memo | Fate::SinkLazyPosition) {
        reasons.push("GHC considers the RHS cheap (but not speculatable)".into());
    }

    BindingReport {
        module: m.name.clone(),
        occ: b.occ.clone(),
        origin: Origin::of(&b.occ),
        unique: b.unique.clone(),
        let_node,
        rhs: pair.rhs,
        class,
        rhs_kind,
        demand,
        demand_pretty: b
            .demand
            .as_ref()
            .map(|d| d.pretty.clone())
            .unwrap_or_default(),
        multiplicity,
        ghc_used_once,
        syntactic_once,
        recursive,
        whnf: pair.whnf,
        cheap: pair.cheap,
        ok_for_spec: pair.ok_for_spec,
        trivial: pair.trivial,
        occurrences: uses.len(),
        sink,
        fate,
        reasons,
    }
}
