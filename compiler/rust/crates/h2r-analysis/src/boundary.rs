//! Can every proven scalar view be applied *at the same time*?
//!
//! [`crate::scalar`] proves each removable flow's view is complete: every
//! consumer of *that* tuple is placed, and every call site it proved is
//! accounted for. It says nothing about the other values that arrive at the
//! same place. A formal parameter, and a function's result, is a
//! **representation boundary**: one slot, one representation, shared by
//! everything that reaches it.
//!
//! Suppose parameter `p` of a local function `f` receives removable tuple A
//! at one call, removable tuple B at another, and at a third call an
//! expression that is not a removable tuple at all — a variable of tuple
//! type from an opaque source, the result of an imported call, a parameter
//! of the enclosing function. A and B each have a perfect def-use proof and
//! the two proofs are individually consistent, but `p` cannot be *both* two
//! scalars and one boxed tuple. Splitting it requires the third producer to
//! take part in the same representation change, or requires `f` to be
//! cloned and specialised. The same holds for a return: a function that
//! returns a removable tuple on one branch and something of unknown
//! representation on another cannot have its result split.
//!
//! [`crate::tuples`] guards the *callee* ([`crate::tuples::R_CALLEE_NOT_SPLITTABLE`],
//! [`crate::tuples::R_CLOSURE_INTO_PARAM`]): the function must be local,
//! not exported, and never used as a value, so that every call site is
//! visible and rewritable. That is strictly weaker than proving that every
//! *producer* of the boundary agrees on one representation, and both
//! [`crate::tuples`] and [`crate::verify`] follow the selected tuple *into*
//! the parameter — neither ever looks at what else arrives there. So the
//! assumption is shared rather than challenged, which is exactly the kind
//! of thing a second proof object is for.
//!
//! # How a boundary is enumerated
//!
//! Independently of the flow walk, and from the IR's own identity:
//!
//! * **A parameter** `(f, i)`. Every occurrence of `f`'s binder
//!   ([`h2r_core_ir::Module::occurrences`]) is taken to its spine root
//!   ([`h2r_core_ir::Module::spine_root`]); an occurrence that is not the
//!   head of a spine, or is the head of a spine that supplies fewer value
//!   arguments than `f` has manifest parameters, is `f` used *as a value* —
//!   a PAP, an argument, something stored — and the parameter cannot be
//!   split at all. Every remaining occurrence is a call site, and the value
//!   argument at index `i` is a producer.
//! * **A return** of `f`. The manifest lambda chain of `f`'s right-hand
//!   side is stripped, and every syntactic return point of the body is
//!   enumerated iteratively: every leaf of the `case`/`let` tree.
//!
//! A producer expression is then classified by what it *is*, looking
//! through casts, ticks, `let` bodies, `case` alternatives and local
//! aliases (a variable bound to a right-hand side is that right-hand side),
//! and following a tail call to a local function into *its* return points.
//! A call to an import, a lambda-bound parameter, a field bound by a match,
//! an imported value: each is named, and each requests the tuple
//! representation.
//!
//! # The verdict
//!
//! [`BoundaryVerdict::UniformSplit`] only when every producer requests
//! `Scalars(k)` for the same `k` *and* the boundary has no other use.
//! [`BoundaryVerdict::CloneRequired`] when the producers disagree but the
//! function is local, not exported and never used as a value, so a
//! specialised clone could carry the split representation.
//! [`BoundaryVerdict::Preserve`] when a proven real value reaches it.
//! [`BoundaryVerdict::Unresolved`] otherwise, with the reason.
//!
//! A removable flow that crosses a boundary that is not `UniformSplit` is
//! **downgraded** ([`settle`]): to [`crate::tuples::TupleFate::RemovableWithClone`]
//! when a clone would do — which the milestone's accounting counts as
//! *unsupported*, because no cloning decision exists yet — and to
//! [`crate::tuples::TupleFate::Unresolved`] otherwise. The downgrade is a
//! fixpoint: a flow that stops being removable stops requesting scalars at
//! every other boundary it produces into, which can make a second boundary
//! non-uniform. It only ever removes flows from the removable set, so it
//! settles.

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{BindSite, BinderId, BinderKind, Expr, ExprId, Module, Ref};
use serde::Serialize;

use crate::scope::Scope;
use crate::shape::value_args;
use crate::tuples::{TupleFate, TupleFlow, TupleUse, Tuples};

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------

/// **Boundary.** A removable flow crosses a representation boundary: a
/// formal parameter of a local function, or a local function's result.
/// Evidence: lexical binder identity (1) over the flow's own consumers.
pub const B0_BOUNDARY: &str = "B0-BOUNDARY";

/// **Producers.** Every value that reaches a boundary, enumerated from the
/// IR's occurrences of the function binder (for a parameter) or from the
/// syntactic return points of its body (for a return) — never from the flow
/// walk. Evidence: lexical binder identity (1) and structural shape (2).
pub const B1_PRODUCERS: &str = "B1-PRODUCERS";

/// **Verdict.** Every producer requests the same `Scalars(k)` and nothing
/// else uses the function as a value, so the boundary can be split.
/// Evidence: def-use dataflow (3) over the producers.
pub const B2_UNIFORM: &str = "B2-UNIFORM";

/// **Downgrade.** A removable flow crosses a boundary that is not uniform,
/// so its own perfect def-use proof is not enough: it is moved out of the
/// normalised population here.
pub const B3_DOWNGRADE: &str = "B3-DOWNGRADE";

//------------------------------------------------------------------------------
// Reasons
//------------------------------------------------------------------------------

pub const B_FUNCTION_EXPORTED: &str = "function-is-exported";
pub const B_FUNCTION_IS_A_VALUE: &str = "function-used-as-a-value";
pub const B_CALL_UNDERSAT: &str = "call-site-is-a-partial-application";
pub const B_NO_CALL_SITES: &str = "function-has-no-visible-call-site";
pub const B_NO_PARAMS: &str = "function-has-no-manifest-parameters";
pub const B_INDEX_PAST_PARAMS: &str = "index-past-the-callee-parameters";
pub const B_NO_PRODUCERS: &str = "no-producer-reaches-the-boundary";
pub const B_PRODUCERS_DISAGREE: &str = "producers-request-different-representations";
pub const B_PRESERVE_REACHES: &str = "a-preserved-tuple-reaches-the-boundary";
pub const B_BUDGET: &str = "producer-walk-exceeded-the-budget";

/// Nodes one producer enumeration may visit before it is abandoned. No
/// boundary on any dump comes near it; it exists so that a pathological
/// module degrades into an honest `Unresolved`.
const PRODUCER_BUDGET: usize = 50_000;

/// How many times the downgrade fixpoint may go round before it is a bug.
const ROUNDS: usize = 64;

//------------------------------------------------------------------------------
// The objects
//------------------------------------------------------------------------------

/// A place where one representation has to serve every value that arrives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Boundary {
    Parameter { function: BinderId, index: u32 },
    Return { function: BinderId },
}

impl Boundary {
    pub fn function(self) -> BinderId {
        match self {
            Boundary::Parameter { function, .. } | Boundary::Return { function } => function,
        }
    }

    pub fn kind(self) -> &'static str {
        match self {
            Boundary::Parameter { .. } => "parameter",
            Boundary::Return { .. } => "return",
        }
    }

    /// How the boundary is named in a report and in a flow's reason detail.
    pub fn render(self, m: &Module) -> String {
        let f = self.function();
        let occ = format!("{}#{f}", m.binder(f).occ);
        match self {
            Boundary::Parameter { index, .. } => format!("parameter {index} of {occ}"),
            Boundary::Return { .. } => format!("return of {occ}"),
        }
    }
}

/// What a value asks the boundary to be.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Representation {
    /// The producer is a removable tuple: it wants `k` separate values.
    Scalars(u32),
    /// The producer is a tuple that stays, or something whose
    /// representation this module does not get to choose.
    Tuple,
}

/// What one producer of a boundary is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ProducerKind {
    /// A saturated tuple construction whose flow is (still) removable.
    Removable {
        construction: ExprId,
        arity: u32,
    },
    /// A saturated tuple construction whose flow is not removable.
    NonRemovable {
        construction: ExprId,
        fate: TupleFate,
    },
    /// A lambda-bound parameter of some enclosing function.
    Parameter {
        binder: BinderId,
    },
    /// A binder bound by a pattern match.
    MatchField {
        binder: BinderId,
    },
    /// The binder a `case` keeps for the whole scrutinee.
    CaseBinder {
        binder: BinderId,
    },
    /// An imported value.
    ImportedValue,
    /// The result of a call this module cannot see into.
    ImportedCall,
    /// A call to something local the walk would not follow: unsaturated,
    /// over-applied, or a head that is not a manifest lambda chain.
    LocalCallUnresolved,
    /// A constructor application that is not a tuple construction in the
    /// population.
    Constructed,
    /// A lambda: a function value, never a tuple.
    Lambda,
    Literal,
    /// Anything the classifier has no name for.
    Other,
}

impl ProducerKind {
    pub fn name(self) -> &'static str {
        match self {
            ProducerKind::Removable { .. } => "removable construction",
            ProducerKind::NonRemovable { .. } => "construction that stays",
            ProducerKind::Parameter { .. } => "parameter of the enclosing function",
            ProducerKind::MatchField { .. } => "field bound by a match",
            ProducerKind::CaseBinder { .. } => "case binder",
            ProducerKind::ImportedValue => "imported value",
            ProducerKind::ImportedCall => "result of an imported call",
            ProducerKind::LocalCallUnresolved => "result of an unfollowable local call",
            ProducerKind::Constructed => "constructor application",
            ProducerKind::Lambda => "lambda",
            ProducerKind::Literal => "literal",
            ProducerKind::Other => "unclassified",
        }
    }
}

/// One value that reaches a boundary.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct Producer {
    /// The node the value is, after casts and ticks.
    pub at: ExprId,
    /// The call site it arrives at, for a parameter boundary.
    pub call: Option<ExprId>,
    pub kind: ProducerKind,
    pub representation: Representation,
}

/// A use of the boundary's function that is not a rewritable call site.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct OtherUse {
    pub why: &'static str,
    pub at: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum BoundaryVerdict {
    /// Every producer wants the same `k` scalars and nothing else uses the
    /// function as a value: the boundary can be split.
    UniformSplit { arity: u32 },
    /// The producers disagree, but the function is local, not exported and
    /// never used as a value: a specialised clone could carry the split.
    CloneRequired,
    /// A proven real value reaches the boundary; it keeps the tuple.
    Preserve,
    /// Anything else.
    Unresolved,
}

impl BoundaryVerdict {
    pub fn name(self) -> &'static str {
        match self {
            BoundaryVerdict::UniformSplit { .. } => "UniformSplit",
            BoundaryVerdict::CloneRequired => "CloneRequired",
            BoundaryVerdict::Preserve => "Preserve",
            BoundaryVerdict::Unresolved => "Unresolved",
        }
    }

    /// A boundary a removable flow may cross without losing its fate.
    pub fn ok(self) -> bool {
        matches!(self, BoundaryVerdict::UniformSplit { .. })
    }
}

/// One representation boundary, everything that reaches it, and the verdict.
#[derive(Debug, Clone, Serialize)]
pub struct BoundaryReport {
    pub module: String,
    pub boundary: Boundary,
    /// How the boundary reads in a report.
    pub name: String,
    /// Does a boxed tuple cross it, an unboxed one, or both?
    pub boxed: bool,
    pub unboxed: bool,
    pub producers: Vec<Producer>,
    /// The occurrences of the parameter, or the call sites of the function
    /// whose result is split.
    pub consumers: Vec<ExprId>,
    /// One entry per producer, in the same order.
    pub requested: Vec<Representation>,
    /// Uses of the function that are not rewritable call sites.
    pub other_uses: Vec<OtherUse>,
    pub verdict: BoundaryVerdict,
    /// Why the verdict is not `UniformSplit`.
    pub reason: Option<&'static str>,
    /// The producer walk ran out of budget, so the enumeration is partial.
    pub over_budget: bool,
}

impl BoundaryReport {
    /// The distinct arities the producers ask for.
    pub fn arities(&self) -> Vec<u32> {
        let mut v: Vec<u32> = self
            .requested
            .iter()
            .filter_map(|r| match r {
                Representation::Scalars(k) => Some(*k),
                Representation::Tuple => None,
            })
            .collect();
        v.sort_unstable();
        v.dedup();
        v
    }
}

/// Every boundary the removable flows of one module cross.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Boundaries {
    pub module: String,
    pub reports: Vec<BoundaryReport>,
    /// Construction node -> the boundaries that flow crosses, as indices
    /// into [`Boundaries::reports`].
    pub crossed: BTreeMap<ExprId, Vec<usize>>,
}

impl Boundaries {
    pub fn verdict(&self, i: usize) -> BoundaryVerdict {
        self.reports[i].verdict
    }
}

/// One removable flow that lost its fate because a boundary it crosses is
/// not uniform.
#[derive(Debug, Clone, Serialize)]
pub struct Downgrade {
    pub module: String,
    pub construction: ExprId,
    pub boxed: bool,
    /// The binder whose parameter or return the boundary is.
    pub function: BinderId,
    pub from: TupleFate,
    pub to: TupleFate,
    /// The boundary that did it, rendered.
    pub boundary: String,
    pub verdict: BoundaryVerdict,
    /// The boundary's reason, carried onto the flow.
    pub reason: &'static str,
}

//------------------------------------------------------------------------------
// Crossing
//------------------------------------------------------------------------------

/// Value parameters of the manifest lambda chain at `rhs`, in order.
/// Written out here rather than shared with [`crate::tuples`], so that a
/// mistake about what a callee's parameters are cannot be common to both.
fn params_of(m: &Module, rhs: ExprId) -> Vec<BinderId> {
    let mut out = Vec::new();
    let mut cur = m.strip(rhs);
    while let Expr::Lam { binder, body } = m.expr(cur) {
        if m.binder(*binder).kind != BinderKind::Tyvar {
            out.push(*binder);
        }
        cur = m.strip(*body);
    }
    out
}

/// The boundaries one flow crosses, including the ones it inherits by
/// being copied into, or nested inside, another removable construction.
///
/// Iterative over flows: a re-tupling ([`TupleUse::Retupled`]) and a
/// tuple-in-tuple ([`TupleUse::NestedIn`]) both make the inner tuple's
/// fields travel wherever the outer box travels, so the outer's boundaries
/// are the inner's too.
fn crossed_by(t: &Tuples<'_>, flow: &TupleFlow, removable: &HashSet<ExprId>) -> Vec<Boundary> {
    let mut out: Vec<Boundary> = Vec::new();
    let mut seen_flows: HashSet<ExprId> = HashSet::from([flow.construction]);
    let mut seen: HashSet<Boundary> = HashSet::new();
    let mut work: Vec<&TupleFlow> = vec![flow];
    while let Some(f) = work.pop() {
        for u in &f.consumers {
            match *u {
                TupleUse::PassedTo { callee, param, .. } => {
                    let b = Boundary::Parameter {
                        function: callee,
                        index: param,
                    };
                    if seen.insert(b) {
                        out.push(b);
                    }
                }
                TupleUse::Returned { function } => {
                    let b = Boundary::Return { function };
                    if seen.insert(b) {
                        out.push(b);
                    }
                }
                TupleUse::Retupled { outer } | TupleUse::NestedIn { outer, .. } => {
                    if !removable.contains(&outer) || !seen_flows.insert(outer) {
                        continue;
                    }
                    if let Some(o) = t.flow_at(outer) {
                        work.push(o);
                    }
                }
                _ => {}
            }
        }
    }
    out
}

//------------------------------------------------------------------------------
// Producers
//------------------------------------------------------------------------------

/// Case binder -> the scrutinee it is another name for. A `case` keeps the
/// whole scrutinee under a second name, so a return point that *is* that
/// binder produces whatever the scrutinee produced.
pub fn case_binders(m: &Module) -> HashMap<BinderId, ExprId> {
    let mut out = HashMap::new();
    for e in &m.exprs {
        if let Expr::Case { scrut, binder, .. } = e {
            out.insert(*binder, *scrut);
        }
    }
    out
}

struct Producers<'m> {
    t: &'m Tuples<'m>,
    scope: Scope<'m>,
    removable: &'m HashSet<ExprId>,
    aliases: &'m HashMap<BinderId, ExprId>,
    out: Vec<Producer>,
    /// Local functions whose return points are already being enumerated: a
    /// recursive tail call adds nothing new, and must not loop.
    following: HashSet<BinderId>,
    budget: usize,
    over: bool,
}

impl<'m> Producers<'m> {
    fn new(
        t: &'m Tuples<'m>,
        removable: &'m HashSet<ExprId>,
        aliases: &'m HashMap<BinderId, ExprId>,
    ) -> Producers<'m> {
        Producers {
            t,
            scope: Scope::new(t.module),
            removable,
            aliases,
            out: Vec::new(),
            following: HashSet::new(),
            budget: PRODUCER_BUDGET,
            over: false,
        }
    }

    fn push(&mut self, at: ExprId, call: Option<ExprId>, kind: ProducerKind) {
        let representation = match kind {
            ProducerKind::Removable { arity, .. } => Representation::Scalars(arity),
            _ => Representation::Tuple,
        };
        self.out.push(Producer {
            at,
            call,
            kind,
            representation,
        });
    }

    /// Enumerate every value the expression at `root` can be, looking
    /// through the constructs that do not change a value's representation.
    fn expand(&mut self, root: ExprId, call: Option<ExprId>) {
        let m = self.t.module;
        let mut work = vec![root];
        let mut seen: HashSet<ExprId> = HashSet::new();
        while let Some(raw) = work.pop() {
            if self.budget == 0 {
                self.over = true;
                return;
            }
            self.budget -= 1;
            let id = m.strip(raw);
            if !seen.insert(id) {
                continue;
            }
            match m.expr(id) {
                // Neither a `case` nor a `let` is a value of its own: the
                // value is whatever each alternative, or the body, is.
                Expr::Case { alts, .. } => work.extend(alts.iter().map(|a| a.rhs)),
                Expr::Let { body, .. } => work.push(*body),
                Expr::Lam { .. } => self.push(id, call, ProducerKind::Lambda),
                Expr::Lit(_) => self.push(id, call, ProducerKind::Literal),
                Expr::Type { .. } | Expr::Coercion => {}
                Expr::Cast(_) | Expr::Tick(_) => unreachable!("stripped above"),
                Expr::Var { .. } => match m.reference(id) {
                    Some(Ref::Global) => self.push(id, call, ProducerKind::ImportedValue),
                    Some(Ref::Local(b)) => {
                        let bi = m.binding(b);
                        match bi.site {
                            // An alias: the binder *is* its right-hand
                            // side, so the producer is whatever that is.
                            BindSite::Top | BindSite::Let => match bi.rhs {
                                Some(rhs) => work.push(rhs),
                                None => self.push(id, call, ProducerKind::Other),
                            },
                            BindSite::Lam => {
                                self.push(id, call, ProducerKind::Parameter { binder: b })
                            }
                            BindSite::AltBinder => {
                                self.push(id, call, ProducerKind::MatchField { binder: b })
                            }
                            // Another name for the scrutinee, not a value of
                            // its own: the producer is whatever the
                            // scrutinee produced.
                            BindSite::CaseBinder => match self.aliases.get(&b) {
                                Some(scrut) => work.push(*scrut),
                                None => self.push(id, call, ProducerKind::CaseBinder { binder: b }),
                            },
                        }
                    }
                    None => self.push(id, call, ProducerKind::Other),
                },
                Expr::App { .. } => self.application(id, call, &mut work),
            }
        }
    }

    /// An application spine in a producer position: a tuple construction, a
    /// tail call into a local function (followed), or a call this module
    /// cannot see into.
    fn application(&mut self, id: ExprId, call: Option<ExprId>, work: &mut Vec<ExprId>) {
        let m = self.t.module;
        if let Some(f) = self.t.flow_at(id) {
            let kind = if self.removable.contains(&id) {
                ProducerKind::Removable {
                    construction: id,
                    arity: f.arity,
                }
            } else {
                ProducerKind::NonRemovable {
                    construction: id,
                    fate: f.fate,
                }
            };
            self.push(id, call, kind);
            return;
        }
        let (head, args) = m.spine(id);
        if self.scope.head_sig(head).and_then(|s| s.data_con).is_some() {
            self.push(id, call, ProducerKind::Constructed);
            return;
        }
        let Some(bi) = m.binding_of(head) else {
            self.push(id, call, ProducerKind::ImportedCall);
            return;
        };
        let Some(rhs) = bi
            .rhs
            .filter(|_| matches!(bi.site, BindSite::Let | BindSite::Top))
        else {
            self.push(id, call, ProducerKind::LocalCallUnresolved);
            return;
        };
        let vargs = value_args(&self.scope, &args);
        if vargs.is_empty() {
            self.push(id, call, ProducerKind::LocalCallUnresolved);
            return;
        }
        // A tail call to a local function: the values it can return are
        // values this boundary receives, so its own return points are
        // enumerated the same way a return boundary's are. A call back into
        // a function whose returns are already being enumerated contributes
        // nothing new — by induction it returns what the other leaves
        // return — so it is skipped rather than looped on.
        if !self.following.insert(bi.binder) {
            return;
        }
        let leaves = return_points(m, rhs);
        if leaves.is_empty() || !leaves.iter().any(|(_, d)| *d == vargs.len()) {
            self.push(id, call, ProducerKind::LocalCallUnresolved);
            return;
        }
        for (leaf, depth) in leaves {
            // Only the leaves reached with exactly this call's arguments are
            // this call's result; a leaf deeper in is a function this call
            // returns, and one shallower is not reached at all.
            if depth == vargs.len() {
                work.push(leaf);
            } else {
                self.push(leaf, call, ProducerKind::LocalCallUnresolved);
            }
        }
    }
}

/// Uses of a function binder, split into rewritable call sites and
/// everything else. Every occurrence has to be the head of an application
/// spine; an occurrence that is not — a PAP, an argument, a stored value —
/// is the function used *as a value*, and no slot of it can be rewritten.
/// `need` is the number of value arguments a call site has to supply.
fn call_sites(
    m: &Module,
    scope: &Scope<'_>,
    f: BinderId,
    need: usize,
) -> (Vec<(ExprId, Vec<ExprId>)>, Vec<OtherUse>) {
    let mut calls = Vec::new();
    let mut other = Vec::new();
    for occ in m.occurrences(f) {
        let root = m.spine_root(*occ);
        if root == *occ {
            other.push(OtherUse {
                why: B_FUNCTION_IS_A_VALUE,
                at: *occ,
            });
            continue;
        }
        let (head, args) = m.spine(root);
        if m.strip(head) != m.strip(*occ) {
            other.push(OtherUse {
                why: B_FUNCTION_IS_A_VALUE,
                at: *occ,
            });
            continue;
        }
        let vargs = value_args(scope, &args);
        if vargs.len() < need {
            other.push(OtherUse {
                why: B_CALL_UNDERSAT,
                at: root,
            });
            continue;
        }
        calls.push((root, vargs));
    }
    (calls, other)
}

/// Every syntactic return point of `rhs`, with the number of value
/// arguments that had to be supplied to reach it.
///
/// GHC does not always leave a function's lambdas at the head of its
/// right-hand side: `f = case c of A -> \s -> e1; B -> \s -> e2` is an
/// ordinary shape after case-of-case, and its return points are `e1` and
/// `e2`, both at depth 1. So the chain is peeled *through* the `case`/`let`
/// tree rather than off the front, iteratively, and the depth each leaf was
/// reached at is carried out with it: leaves at different depths are not
/// one result and the caller refuses them rather than picking one.
fn return_points(m: &Module, rhs: ExprId) -> Vec<(ExprId, usize)> {
    let mut leaves = Vec::new();
    let mut work = vec![(rhs, 0usize)];
    let mut seen: HashSet<(ExprId, usize)> = HashSet::new();
    while let Some((raw, depth)) = work.pop() {
        let id = m.strip(raw);
        if !seen.insert((id, depth)) {
            continue;
        }
        match m.expr(id) {
            Expr::Lam { binder, body } => {
                let value = usize::from(m.binder(*binder).kind != BinderKind::Tyvar);
                work.push((*body, depth + value));
            }
            Expr::Case { alts, .. } => work.extend(alts.iter().map(|a| (a.rhs, depth))),
            Expr::Let { body, .. } => work.push((*body, depth)),
            _ => leaves.push((id, depth)),
        }
    }
    leaves
}

/// Enumerate one boundary: its producers, its consumers, and the verdict.
fn report(
    t: &Tuples<'_>,
    b: Boundary,
    removable: &HashSet<ExprId>,
    aliases: &HashMap<BinderId, ExprId>,
) -> BoundaryReport {
    let m = t.module;
    let scope = Scope::new(m);
    let f = b.function();
    let mut other_uses: Vec<OtherUse> = Vec::new();
    let mut producers: Vec<Producer> = Vec::new();
    let mut consumers: Vec<ExprId> = Vec::new();
    let mut over_budget = false;

    if m.binder(f).exported == Some(true) {
        other_uses.push(OtherUse {
            why: B_FUNCTION_EXPORTED,
            at: m.binding(f).rhs.unwrap_or(0),
        });
    }
    let params = m
        .binding(f)
        .rhs
        .map(|rhs| params_of(m, rhs))
        .unwrap_or_default();
    let rhs = m.binding(f).rhs;

    match (rhs, b) {
        (None, _) => other_uses.push(OtherUse {
            why: B_NO_PARAMS,
            at: 0,
        }),
        // A parameter: the manifest lambda chain names it, and every call
        // site has to supply at least the whole chain for the argument at
        // `index` to be the one that lands on it.
        (Some(rhs), Boundary::Parameter { index, .. }) => {
            if params.is_empty() || index as usize >= params.len() {
                other_uses.push(OtherUse {
                    why: if params.is_empty() {
                        B_NO_PARAMS
                    } else {
                        B_INDEX_PAST_PARAMS
                    },
                    at: rhs,
                });
            } else {
                let (calls, mut other) = call_sites(m, &scope, f, params.len());
                other_uses.append(&mut other);
                let mut walk = Producers::new(t, removable, aliases);
                walk.following.insert(f);
                for (root, vargs) in &calls {
                    walk.expand(vargs[index as usize], Some(*root));
                }
                over_budget = walk.over;
                producers = walk.out;
                consumers.extend(m.occurrences(params[index as usize]).iter().copied());
            }
        }
        // A return: how many arguments a call supplies is what says which
        // lambdas belong to this function, so it is read off the call sites
        // rather than off the syntax. Call sites that disagree are not one
        // boundary and are refused.
        (Some(rhs), Boundary::Return { .. }) => {
            let (calls, mut other) = call_sites(m, &scope, f, 1);
            other_uses.append(&mut other);
            let leaves = return_points(m, rhs);
            // The result lives at the deepest leaf. A leaf reached with
            // fewer arguments has, by the type of the position it sits in,
            // to be a *function* of the remaining ones — a tuple is never a
            // function — so it is a producer this walk cannot see into
            // rather than a value of the boundary.
            let depth = leaves.iter().map(|(_, d)| *d).max().unwrap_or(0);
            if calls.is_empty() {
                other_uses.push(OtherUse {
                    why: B_NO_CALL_SITES,
                    at: rhs,
                });
            } else if depth == 0 {
                other_uses.push(OtherUse {
                    why: B_NO_PARAMS,
                    at: rhs,
                });
            } else {
                let mut walk = Producers::new(t, removable, aliases);
                walk.following.insert(f);
                for (leaf, d) in &leaves {
                    if *d == depth {
                        walk.expand(*leaf, None);
                    } else {
                        walk.push(*leaf, None, ProducerKind::LocalCallUnresolved);
                    }
                }
                over_budget = walk.over;
                producers = walk.out;
                consumers.extend(calls.iter().map(|(root, _)| *root));
            }
        }
    }

    let requested: Vec<Representation> = producers.iter().map(|p| p.representation).collect();
    let (verdict, reason) = judge(b, &producers, &requested, &other_uses, over_budget);

    BoundaryReport {
        module: m.name.clone(),
        boundary: b,
        name: b.render(m),
        boxed: false,
        unboxed: false,
        producers,
        consumers,
        requested,
        other_uses,
        verdict,
        reason,
        over_budget,
    }
}

/// The verdict, from what reaches the boundary and what else uses the
/// function. Separate from the enumeration so that it can be re-taken when
/// a parameter this boundary produces from turns out to be splittable.
fn judge(
    b: Boundary,
    producers: &[Producer],
    requested: &[Representation],
    other_uses: &[OtherUse],
    over_budget: bool,
) -> (BoundaryVerdict, Option<&'static str>) {
    let uniform = match requested.first() {
        Some(Representation::Scalars(k))
            if requested.iter().all(|r| *r == Representation::Scalars(*k)) =>
        {
            Some(*k)
        }
        _ => None,
    };
    let preserved = producers.iter().any(|p| {
        matches!(
            p.kind,
            ProducerKind::NonRemovable {
                fate: TupleFate::Preserve,
                ..
            }
        )
    });
    if over_budget {
        (BoundaryVerdict::Unresolved, Some(B_BUDGET))
    } else if let (true, Some(k)) = (other_uses.is_empty(), uniform) {
        (BoundaryVerdict::UniformSplit { arity: k }, None)
    } else if preserved {
        (BoundaryVerdict::Preserve, Some(B_PRESERVE_REACHES))
    } else if let Some(u) = other_uses.first() {
        (BoundaryVerdict::Unresolved, Some(u.why))
    } else if producers.is_empty() {
        (BoundaryVerdict::Unresolved, Some(B_NO_PRODUCERS))
    } else if matches!(b, Boundary::Parameter { .. }) {
        // A *parameter* with mixed producers can be specialised: a clone of
        // the callee takes the scalars, the call sites that have a real
        // tuple keep calling the original. Local, not exported and every
        // use a rewritable call site is exactly what makes that possible.
        (BoundaryVerdict::CloneRequired, Some(B_PRODUCERS_DISAGREE))
    } else {
        // A *return* cannot be specialised the same way: every return point
        // is inside one body and they all have to agree, so there is no
        // clone that splits some of them and not the others.
        (BoundaryVerdict::Unresolved, Some(B_PRODUCERS_DISAGREE))
    }
}

//------------------------------------------------------------------------------
// The analysis
//------------------------------------------------------------------------------

/// Enumerate and judge one boundary on its own, whether or not a removable
/// flow crosses it. The entry point a test or an audit uses to ask the
/// question directly; [`analyse`] is the same thing over the boundaries the
/// census' removable flows actually cross.
pub fn examine(t: &Tuples<'_>, b: Boundary, removable: &HashSet<ExprId>) -> BoundaryReport {
    report(t, b, removable, &case_binders(t.module))
}

/// Every boundary the flows in `crossers` cross, with the verdict on each.
///
/// `crossers` says whose boundaries are enumerated; `removable` says which
/// producers still ask for scalars. They are the same set during the
/// fixpoint, and differ only in the final report, which keeps the
/// boundaries of the flows that were downgraded so that the reason a flow
/// lost its fate is still printable.
pub fn analyse(
    t: &Tuples<'_>,
    crossers: &HashSet<ExprId>,
    removable: &HashSet<ExprId>,
) -> Boundaries {
    let mut out = Boundaries {
        module: t.module.name.clone(),
        ..Default::default()
    };
    let aliases = case_binders(t.module);
    let mut index: HashMap<Boundary, usize> = HashMap::new();
    for f in &t.flows {
        if !crossers.contains(&f.construction) {
            continue;
        }
        let mut mine = Vec::new();
        for b in crossed_by(t, f, removable) {
            let i = match index.get(&b) {
                Some(i) => *i,
                None => {
                    let i = out.reports.len();
                    out.reports.push(report(t, b, removable, &aliases));
                    index.insert(b, i);
                    i
                }
            };
            if f.boxed {
                out.reports[i].boxed = true;
            } else {
                out.reports[i].unboxed = true;
            }
            if !mine.contains(&i) {
                mine.push(i);
            }
        }
        if !mine.is_empty() {
            out.crossed.insert(f.construction, mine);
        }
    }
    upgrade_parameters(t.module, &mut out);
    out
}

/// A function that returns one of its own parameters returns whatever that
/// parameter is. So once a *parameter* boundary is a uniform split, every
/// producer that is that parameter asks for the same scalars, which can
/// make a *return* boundary uniform in turn.
///
/// Run as a fixpoint that only ever *adds* splittable parameters, starting
/// from none: a cycle of functions that pass each other's parameters around
/// cannot bootstrap itself into being splittable, it simply stays a tuple.
/// The same discipline as the tuple-in-tuple fixpoint in [`crate::tuples`].
fn upgrade_parameters(m: &Module, out: &mut Boundaries) {
    let mut split: HashMap<BinderId, u32> = HashMap::new();
    for _ in 0..ROUNDS {
        let mut next = split.clone();
        for r in &out.reports {
            if let (
                BoundaryVerdict::UniformSplit { arity },
                Boundary::Parameter { function, index },
            ) = (r.verdict, r.boundary)
                && let Some(rhs) = m.binding(function).rhs
                && let Some(p) = params_of(m, rhs).get(index as usize)
            {
                next.insert(*p, arity);
            }
        }
        if next.len() == split.len() {
            return;
        }
        split = next;
        for r in out.reports.iter_mut() {
            for (p, req) in r.producers.iter_mut().zip(r.requested.iter_mut()) {
                if let ProducerKind::Parameter { binder } = p.kind
                    && let Some(k) = split.get(&binder)
                {
                    p.representation = Representation::Scalars(*k);
                    *req = p.representation;
                }
            }
            let (v, why) = judge(
                r.boundary,
                &r.producers,
                &r.requested,
                &r.other_uses,
                r.over_budget,
            );
            r.verdict = v;
            r.reason = why;
        }
    }
}

/// Run the boundary check to a fixpoint and report the flows that lose
/// their fate.
///
/// Starts from the flows [`crate::tuples`] proved removable, enumerates the
/// boundaries they cross, and removes from the removable set every flow
/// that crosses one that is not [`BoundaryVerdict::UniformSplit`]. Removing
/// a flow can only ever make another boundary *less* uniform (it stops
/// requesting scalars there), so the set shrinks monotonically and the loop
/// settles; `rounds` records how many it took.
pub struct Settled {
    pub boundaries: Boundaries,
    pub downgrades: Vec<Downgrade>,
    pub rounds: usize,
}

pub fn settle(t: &Tuples<'_>) -> Settled {
    let mut removable: HashSet<ExprId> = t
        .flows
        .iter()
        .filter(|f| matches!(f.fate, TupleFate::ScalarReplace | TupleFate::WorkerReturn))
        .map(|f| f.construction)
        .collect();
    let initial = removable.clone();
    let mut down: BTreeMap<ExprId, Downgrade> = BTreeMap::new();
    let mut rounds = 0;
    loop {
        let b = analyse(t, &removable, &removable);
        let mut fresh: Vec<Downgrade> = Vec::new();
        for f in &t.flows {
            if !removable.contains(&f.construction) {
                continue;
            }
            let Some(crossed) = b.crossed.get(&f.construction) else {
                continue;
            };
            // The worst verdict wins: one boundary that cannot be split is
            // enough, and a clone is only offered when every failure is one.
            let mut worst: Option<&BoundaryReport> = None;
            for i in crossed {
                let r = &b.reports[*i];
                if r.verdict.ok() {
                    continue;
                }
                let better = match worst {
                    None => true,
                    Some(w) => {
                        w.verdict == BoundaryVerdict::CloneRequired
                            && r.verdict != BoundaryVerdict::CloneRequired
                    }
                };
                if better {
                    worst = Some(r);
                }
            }
            let Some(r) = worst else { continue };
            let to = match r.verdict {
                BoundaryVerdict::CloneRequired => TupleFate::RemovableWithClone,
                _ => TupleFate::Unresolved,
            };
            fresh.push(Downgrade {
                module: f.module.clone(),
                construction: f.construction,
                boxed: f.boxed,
                function: r.boundary.function(),
                from: f.fate,
                to,
                boundary: r.name.clone(),
                verdict: r.verdict,
                reason: r.reason.unwrap_or(B_PRODUCERS_DISAGREE),
            });
        }
        rounds += 1;
        if fresh.is_empty() {
            break;
        }
        for d in fresh {
            removable.remove(&d.construction);
            down.insert(d.construction, d);
        }
        assert!(
            rounds < ROUNDS,
            "the boundary downgrade fixpoint did not settle in {ROUNDS} rounds"
        );
    }
    // The reported boundary object keeps the boundaries of the downgraded
    // flows too — otherwise the reason a flow lost its fate would not be
    // printable — and every verdict in it is the one the final removable
    // set implies. A flow downgraded in an early round is re-judged against
    // it, so the verdict on the flow and the verdict on the boundary can
    // never disagree in the report.
    let boundaries = analyse(t, &initial, &removable);
    let mut downgrades: Vec<Downgrade> = Vec::new();
    for f in &t.flows {
        if !down.contains_key(&f.construction) {
            continue;
        }
        let Some(crossed) = boundaries.crossed.get(&f.construction) else {
            downgrades.push(down[&f.construction].clone());
            continue;
        };
        let worst = crossed
            .iter()
            .map(|i| &boundaries.reports[*i])
            .filter(|r| !r.verdict.ok())
            .min_by_key(|r| u8::from(r.verdict == BoundaryVerdict::CloneRequired));
        match worst {
            Some(r) => downgrades.push(Downgrade {
                module: f.module.clone(),
                construction: f.construction,
                boxed: f.boxed,
                function: r.boundary.function(),
                from: f.fate,
                to: match r.verdict {
                    BoundaryVerdict::CloneRequired => TupleFate::RemovableWithClone,
                    _ => TupleFate::Unresolved,
                },
                boundary: r.name.clone(),
                verdict: r.verdict,
                reason: r.reason.unwrap_or(B_PRODUCERS_DISAGREE),
            }),
            None => downgrades.push(down[&f.construction].clone()),
        }
    }
    Settled {
        boundaries,
        downgrades,
        rounds,
    }
}

//------------------------------------------------------------------------------
// Report shapes
//------------------------------------------------------------------------------

/// Boundaries by verdict, split by the representation of the tuples that
/// cross them: `(verdict, kind, boxed, unboxed, both)`.
#[derive(Debug, Clone, Serialize)]
pub struct VerdictRow {
    pub verdict: &'static str,
    pub kind: &'static str,
    pub boxed: usize,
    pub unboxed: usize,
    pub both: usize,
    pub total: usize,
}

pub fn verdict_rows(all: &[Boundaries]) -> Vec<VerdictRow> {
    let mut by: BTreeMap<(&'static str, &'static str), [usize; 3]> = BTreeMap::new();
    for b in all {
        for r in &b.reports {
            let e = by
                .entry((r.verdict.name(), r.boundary.kind()))
                .or_insert([0; 3]);
            match (r.boxed, r.unboxed) {
                (true, true) => e[2] += 1,
                (true, false) => e[0] += 1,
                _ => e[1] += 1,
            }
        }
    }
    by.into_iter()
        .map(|((verdict, kind), c)| VerdictRow {
            verdict,
            kind,
            boxed: c[0],
            unboxed: c[1],
            both: c[2],
            total: c[0] + c[1] + c[2],
        })
        .collect()
}
