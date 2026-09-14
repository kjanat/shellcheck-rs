//! A second, independent check of every tuple the census calls removable.
//!
//! [`crate::tuples`] proves a fate by following the value forward through a
//! worklist over locations-with-debt. This module answers the *same*
//! question a different way and shares no code with it beyond the IR: it
//! enumerates, for one construction, every alias the tuple can be reached
//! under — the binder it is let-bound to, the case binder of every match,
//! the parameter of every known local callee it is handed to, the call
//! sites of every function that returns it — and requires that **every
//! occurrence of every alias** is one of three things:
//!
//! * a scrutiny (`case t of (a, b) -> …`), including the lazy selection
//!   that returns one field;
//! * a further alias (bound again, passed into a local callee's parameter,
//!   returned and consumed at a call site);
//! * nothing else at all.
//!
//! and that the whole chain is **closed within the module**: no alias is an
//! exported binding, no function whose return is rewritten is exported or
//! escapes as a value, and no use is an argument of anything this module
//! cannot see into.
//!
//! It is deliberately blunt. It has one verdict — removable or not — it
//! does not rank reasons, and where the census distinguishes "a real value"
//! from "cannot follow" it simply refuses. Refusing more than the census is
//! only a coverage loss and is reported as such; the failure this exists to
//! catch is the census calling *removable* something this walk can refuse.
//!
//! Two deliberate strengthenings over the census' own rules, both about
//! whether the rewrite is *possible* rather than about where the value
//! goes. Removing a tuple that is passed into a local callee means
//! splitting that callee's parameter, and removing one that is returned
//! means rewriting that function's returns; both need every call site of
//! the callee to be visible and rewritable. So a callee that is exported,
//! or that escapes as a value anywhere in the module (handed to `map`,
//! stored in a constructor), is refused here.
//!
//! **This module does not use [`crate::flow`], and must not.** The generic
//! aggregate walk *is* the census' walk with the tuple-specific rules lifted
//! out; re-deriving a verdict with it would only re-run the analysis being
//! checked. The only thing this module shares with the census is the IR.

use std::collections::{HashMap, HashSet};

use h2r_core_ir::{AltCon, BindSite, BinderId, BinderKind, Edge, Expr, ExprId, Module};
use serde::Serialize;

/// Why the verifier will not call a construction removable.
#[derive(Debug, Clone, Serialize)]
pub struct Rejection {
    pub why: &'static str,
    pub at: ExprId,
    pub detail: String,
}

pub const V_EXPORTED: &str = "alias-is-an-exported-binding";
pub const V_APPLIED: &str = "tuple-applied-as-a-function";
pub const V_ALTS: &str = "case-is-not-one-full-tuple-alternative";
pub const V_STORED: &str = "stored-in-a-constructor-field";
pub const V_OPAQUE: &str = "argument-of-a-call-this-module-cannot-see-into";
pub const V_CALLEE_ESCAPES: &str = "callee-escapes-so-its-parameter-cannot-be-split";
pub const V_CLOSURE_INTO_PARAM: &str = "closure-returning-the-tuple-is-passed-into-a-parameter";
pub const V_CALLEE_EXPORTED: &str = "callee-is-exported-so-its-parameter-cannot-be-split";
pub const V_PAST_PARAMS: &str = "argument-lands-past-the-callee-parameters";
pub const V_OVERSAT: &str = "call-applies-past-the-return";
pub const V_NOT_AN_ARG: &str = "use-is-not-a-value-argument-of-its-spine";
pub const V_NO_BINDING: &str = "value-has-no-enclosing-binding";
pub const V_SCRUT_CLOSURE: &str = "closure-returning-the-tuple-is-scrutinised";
pub const V_OUTER_NOT_REMOVABLE: &str = "stored-in-a-tuple-field-that-is-not-removable";
pub const V_NESTING: &str = "tuple-nesting-too-deep";
pub const V_BUDGET: &str = "walk-exceeded-the-budget";

/// What the walk enumerated, when it succeeds.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Proof {
    /// Binders the whole tuple is reachable under.
    pub aliases: Vec<BinderId>,
    /// Binders that return the tuple after *n* more arguments.
    pub producers: Vec<(BinderId, u32)>,
    /// Every `case` that takes the tuple apart, with the field binders.
    pub scrutinies: Vec<(ExprId, Vec<BinderId>)>,
    /// Scrutinies whose alternative returns exactly one field binder.
    pub selections: usize,
    /// Occurrences examined.
    pub occurrences: usize,
    pub locations: usize,
    /// The walk used a hop supplied by another proof object.
    pub used_hop: bool,
}

const BUDGET: usize = 200_000;
const MAX_NESTING: u32 = 8;

/// One saturated tuple construction, found independently of
/// [`crate::tuples`].
#[derive(Debug, Clone, Copy)]
pub struct Construction {
    pub root: ExprId,
    pub boxed: bool,
    pub arity: u32,
}

pub struct Verifier<'m> {
    m: &'m Module,
    /// Spine root -> construction, for every saturated tuple construction.
    cons: HashMap<ExprId, Construction>,
    /// Binders whose every occurrence is the head of a call supplying at
    /// least their manifest arity: they never escape as a value.
    never_escapes: HashMap<BinderId, bool>,
    /// Extra hops the walk cannot derive on its own, supplied by the
    /// caller: `(spine root, value-argument index) -> parameter binder`.
    /// Used for the continuation calls the Parsec proof object resolves, so
    /// that *that* hop is an input and everything after it is still checked
    /// here.
    hops: HashMap<(ExprId, usize), Vec<BinderId>>,
}

/// Is this stable name ghc-prim's boxed or unboxed tuple constructor, and
/// of what arity? Written out here rather than shared, so that a mistake in
/// selecting the population cannot be common to both sides.
fn tuple_arity(name: &str, boxed_out: &mut bool) -> Option<u32> {
    let rest = name.strip_prefix('$')?;
    let (unit, rest) = rest.split_once('$')?;
    let (module, occ) = rest.split_once('$')?;
    if unit != "ghc-prim" {
        return None;
    }
    let commas = if module == "GHC.Prim" {
        *boxed_out = false;
        occ.strip_prefix("(#")?.strip_suffix("#)")?
    } else if module.starts_with("GHC.Tuple") {
        *boxed_out = true;
        occ.strip_prefix('(')?.strip_suffix(')')?
    } else {
        return None;
    };
    if commas.is_empty() || !commas.bytes().all(|c| c == b',') {
        return None;
    }
    Some(commas.len() as u32 + 1)
}

impl<'m> Verifier<'m> {
    pub fn new(m: &'m Module) -> Verifier<'m> {
        let mut v = Verifier {
            m,
            cons: HashMap::new(),
            never_escapes: HashMap::new(),
            hops: HashMap::new(),
        };
        v.find_constructions();
        v
    }

    /// Add the hops a separate proof object establishes (see
    /// [`Verifier::hops`]).
    pub fn with_hops(mut self, hops: HashMap<(ExprId, usize), Vec<BinderId>>) -> Verifier<'m> {
        self.hops = hops;
        self
    }

    pub fn constructions(&self) -> impl Iterator<Item = &Construction> {
        self.cons.values()
    }

    pub fn construction_at(&self, root: ExprId) -> Option<Construction> {
        self.cons.get(&root).copied()
    }

    /// Value arguments of a spine: everything that is not a type or a
    /// coercion.
    fn vargs(&self, args: &[ExprId]) -> Vec<ExprId> {
        args.iter()
            .copied()
            .filter(|a| {
                !matches!(
                    self.m.expr(self.m.strip(*a)),
                    Expr::Type { .. } | Expr::Coercion
                )
            })
            .collect()
    }

    /// The data constructor at the head of a spine, if the head is one.
    fn head_data_con(&self, head: ExprId) -> Option<&'m h2r_core_ir::DataConInfo> {
        let Expr::Var { name, .. } = self.m.expr(head) else {
            return None;
        };
        if self.m.resolve(head).is_some() {
            return None; // bound here: locals are never constructors
        }
        self.m.ids.get(name)?.data_con.as_ref()
    }

    fn find_constructions(&mut self) {
        let m = self.m;
        for id in 0..m.exprs.len() as ExprId {
            if !matches!(m.expr(id), Expr::App { .. }) || m.spine_root(id) != id {
                continue;
            }
            let (head, args) = m.spine(id);
            let Some(dc) = self.head_data_con(head) else {
                continue;
            };
            let mut boxed = true;
            let Some(arity) = tuple_arity(&dc.name, &mut boxed) else {
                continue;
            };
            if arity != dc.rep_arity || dc.strict_fields.iter().any(|s| *s) {
                continue;
            }
            if self.vargs(&args).len() != arity as usize {
                continue;
            }
            self.cons.insert(
                id,
                Construction {
                    root: id,
                    boxed,
                    arity,
                },
            );
        }
    }

    /// The manifest value parameters of a binder's right-hand side.
    fn params_of(&self, b: BinderId) -> Vec<BinderId> {
        let m = self.m;
        let Some(rhs) = m.binding(b).rhs else {
            return Vec::new();
        };
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

    /// Is every occurrence of `b` the head of a spine that supplies at
    /// least `n` value arguments? If not, `b` is a value somewhere and its
    /// parameters and returns cannot be rewritten.
    fn never_escapes(&mut self, b: BinderId, n: usize) -> bool {
        if let Some(v) = self.never_escapes.get(&b) {
            return *v;
        }
        let m = self.m;
        let mut ok = true;
        for occ in m.occurrences(b) {
            let root = m.spine_root(*occ);
            if root == *occ {
                ok = false; // a bare occurrence: the function itself is the value
                break;
            }
            let (head, args) = m.spine(root);
            if m.strip(head) != m.strip(*occ) || self.vargs(&args).len() < n {
                ok = false;
                break;
            }
        }
        self.never_escapes.insert(b, ok);
        ok
    }

    /// Can the construction rooted at `root` be removed? The whole check.
    pub fn verify(&mut self, root: ExprId) -> Result<Proof, Rejection> {
        let mut visiting = HashSet::new();
        self.walk(root, &mut visiting, 0)
    }

    fn walk(
        &mut self,
        root: ExprId,
        visiting: &mut HashSet<ExprId>,
        depth: u32,
    ) -> Result<Proof, Rejection> {
        let Some(con) = self.cons.get(&root).copied() else {
            return Err(Rejection {
                why: V_OUTER_NOT_REMOVABLE,
                at: root,
                detail: "not a saturated tuple construction".into(),
            });
        };
        if depth > MAX_NESTING || !visiting.insert(root) {
            return Err(Rejection {
                why: V_NESTING,
                at: root,
                detail: format!("depth {depth}"),
            });
        }
        let out = self.walk_inner(root, con, visiting, depth);
        visiting.remove(&root);
        out
    }

    fn walk_inner(
        &mut self,
        root: ExprId,
        con: Construction,
        visiting: &mut HashSet<ExprId>,
        depth: u32,
    ) -> Result<Proof, Rejection> {
        let m = self.m;
        let mut p = Proof::default();
        let mut work: Vec<(ExprId, u32)> = vec![(root, 0)];
        let mut seen: HashSet<(ExprId, u32)> = HashSet::from([(root, 0)]);
        let mut bound: HashSet<(BinderId, u32)> = HashSet::new();
        while let Some((start, start_owed)) = work.pop() {
            p.locations += 1;
            if p.locations > BUDGET {
                return Err(Rejection {
                    why: V_BUDGET,
                    at: root,
                    detail: String::new(),
                });
            }
            // Climb out of every construct whose own value is this value,
            // counting the lambdas crossed: after `owed` more arguments the
            // thing bound here produces the tuple.
            let mut n = start;
            let mut owed = start_owed;
            let landed = loop {
                match (m.parent[n as usize], m.edge[n as usize]) {
                    (None, Edge::Top { pair }) => {
                        let b = m
                            .top
                            .iter()
                            .flat_map(|x| x.pairs.iter())
                            .nth(pair as usize)
                            .map(|x| x.binder);
                        match b {
                            Some(b) => break Landing::Bind(b, owed),
                            None => break Landing::Reject(V_NO_BINDING, n, String::new()),
                        }
                    }
                    (None, _) => break Landing::Reject(V_NO_BINDING, n, String::new()),
                    (Some(parent), edge) => match edge {
                        Edge::Cast | Edge::Tick | Edge::LetBody | Edge::CaseAlt { .. } => {
                            n = parent
                        }
                        Edge::LamBody => {
                            let Expr::Lam { binder, .. } = m.expr(parent) else {
                                break Landing::Reject(V_NO_BINDING, parent, String::new());
                            };
                            if m.binder(*binder).kind != BinderKind::Tyvar {
                                owed += 1;
                            }
                            n = parent;
                        }
                        Edge::LetRhs { pair } => {
                            let Expr::Let { bind, .. } = m.expr(parent) else {
                                break Landing::Reject(V_NO_BINDING, parent, String::new());
                            };
                            break Landing::Bind(bind.pairs[pair as usize].binder, owed);
                        }
                        Edge::Top { .. } => break Landing::Reject(V_NO_BINDING, n, String::new()),
                        Edge::CaseScrut => break Landing::Scrutiny(parent, owed),
                        Edge::AppArg => break Landing::Argument(parent, n, owed),
                        Edge::AppFun => break Landing::Applied(n, owed),
                    },
                }
            };
            match landed {
                Landing::Reject(why, at, detail) => return Err(Rejection { why, at, detail }),
                Landing::Bind(b, owed) => {
                    if m.binding(b).site == BindSite::Top && m.binder(b).exported == Some(true) {
                        return Err(Rejection {
                            why: V_EXPORTED,
                            at: start,
                            detail: m.binder(b).occ.clone(),
                        });
                    }
                    if bound.insert((b, owed)) {
                        if owed == 0 {
                            p.aliases.push(b);
                        } else {
                            p.producers.push((b, owed));
                        }
                        for occ in m.occurrences(b) {
                            p.occurrences += 1;
                            if seen.insert((*occ, owed)) {
                                work.push((*occ, owed));
                            }
                        }
                    }
                }
                Landing::Scrutiny(case, owed) => {
                    if owed > 0 {
                        return Err(Rejection {
                            why: V_SCRUT_CLOSURE,
                            at: case,
                            detail: String::new(),
                        });
                    }
                    let Expr::Case { binder, alts, .. } = m.expr(case) else {
                        return Err(Rejection {
                            why: V_ALTS,
                            at: case,
                            detail: String::new(),
                        });
                    };
                    // Forcing the whole tuple reads no field and is a
                    // no-op on a constructor application.
                    if alts.len() == 1
                        && matches!(alts[0].con, AltCon::Default)
                        && alts[0].binders.is_empty()
                    {
                        for occ in m.occurrences(*binder) {
                            p.occurrences += 1;
                            if seen.insert((*occ, 0)) {
                                work.push((*occ, 0));
                            }
                        }
                        continue;
                    }
                    let one = alts.first().filter(|a| {
                        alts.len() == 1
                            && matches!(a.con, AltCon::DataAlt { .. })
                            && a.binders.len() == con.arity as usize
                    });
                    let Some(alt) = one else {
                        return Err(Rejection {
                            why: V_ALTS,
                            at: case,
                            detail: format!("{} alternative(s)", alts.len()),
                        });
                    };
                    // The case binder is the whole tuple under another name.
                    for occ in m.occurrences(*binder) {
                        p.occurrences += 1;
                        if seen.insert((*occ, 0)) {
                            work.push((*occ, 0));
                        }
                    }
                    if m.resolve(m.strip(alt.rhs))
                        .is_some_and(|r| alt.binders.contains(&r))
                    {
                        p.selections += 1;
                    }
                    p.scrutinies.push((case, alt.binders.clone()));
                }
                Landing::Applied(at, owed) => {
                    if owed == 0 {
                        return Err(Rejection {
                            why: V_APPLIED,
                            at,
                            detail: String::new(),
                        });
                    }
                    let root2 = m.spine_root(at);
                    let (_, args) = m.spine(root2);
                    let k = self.vargs(&args).len() as u32;
                    if k > owed {
                        return Err(Rejection {
                            why: V_OVERSAT,
                            at: root2,
                            detail: format!("{k} of {owed}"),
                        });
                    }
                    if seen.insert((root2, owed - k)) {
                        work.push((root2, owed - k));
                    }
                }
                Landing::Argument(app, v, owed) => {
                    let root2 = m.spine_root(app);
                    let (head, args) = m.spine(root2);
                    let vargs = self.vargs(&args);
                    let Some(idx) = vargs.iter().position(|a| *a == v) else {
                        return Err(Rejection {
                            why: V_NOT_AN_ARG,
                            at: root2,
                            detail: String::new(),
                        });
                    };
                    let occ = match m.expr(head) {
                        Expr::Var { occ, .. } => occ.clone(),
                        _ => String::new(),
                    };
                    // A field of another tuple: the inner tuple survives
                    // only as long as the outer does, so it is removable
                    // exactly when the outer is, and then its consumers are
                    // the outer's field consumers.
                    if owed == 0 && self.cons.contains_key(&root2) {
                        let inner = self.walk(root2, visiting, depth + 1)?;
                        for (_, binders) in &inner.scrutinies {
                            let Some(fb) = binders.get(idx) else { continue };
                            for o in m.occurrences(*fb) {
                                p.occurrences += 1;
                                if seen.insert((*o, 0)) {
                                    work.push((*o, 0));
                                }
                            }
                        }
                        p.locations += inner.locations;
                        p.used_hop |= inner.used_hop;
                        continue;
                    }
                    if self.head_data_con(head).is_some() {
                        return Err(Rejection {
                            why: V_STORED,
                            at: root2,
                            detail: occ,
                        });
                    }
                    // A hop another proof object establishes.
                    if let Some(params) = self.hops.get(&(root2, idx)) {
                        let params = params.clone();
                        p.used_hop = true;
                        for pb in params {
                            for o in m.occurrences(pb) {
                                p.occurrences += 1;
                                if seen.insert((*o, owed)) {
                                    work.push((*o, owed));
                                }
                            }
                        }
                        continue;
                    }
                    // A call to a function bound here to a lambda chain.
                    let Some(hb) = m.resolve(m.strip(head)) else {
                        return Err(Rejection {
                            why: V_OPAQUE,
                            at: root2,
                            detail: occ,
                        });
                    };
                    if !matches!(m.binding(hb).site, BindSite::Let | BindSite::Top) {
                        return Err(Rejection {
                            why: V_OPAQUE,
                            at: root2,
                            detail: occ,
                        });
                    }
                    let params = self.params_of(hb);
                    if params.is_empty() {
                        return Err(Rejection {
                            why: V_OPAQUE,
                            at: root2,
                            detail: occ,
                        });
                    }
                    if m.binder(hb).exported == Some(true) {
                        return Err(Rejection {
                            why: V_CALLEE_EXPORTED,
                            at: root2,
                            detail: occ,
                        });
                    }
                    if !self.never_escapes(hb, params.len()) {
                        return Err(Rejection {
                            why: V_CALLEE_ESCAPES,
                            at: root2,
                            detail: occ,
                        });
                    }
                    if owed > 0 {
                        // The *closure* that returns the tuple is handed to
                        // a parameter. Rewriting its result representation
                        // changes that parameter's type, so every other
                        // closure that reaches the parameter would have to
                        // be rewritten too — and those are not checked here.
                        return Err(Rejection {
                            why: V_CLOSURE_INTO_PARAM,
                            at: root2,
                            detail: occ,
                        });
                    }
                    if vargs.len() < params.len() || idx >= params.len() {
                        return Err(Rejection {
                            why: V_PAST_PARAMS,
                            at: root2,
                            detail: occ,
                        });
                    }
                    for o in m.occurrences(params[idx]) {
                        p.occurrences += 1;
                        if seen.insert((*o, owed)) {
                            work.push((*o, owed));
                        }
                    }
                }
            }
        }
        Ok(p)
    }
}

enum Landing {
    Bind(BinderId, u32),
    Scrutiny(ExprId, u32),
    Applied(ExprId, u32),
    Argument(ExprId, ExprId, u32),
    Reject(&'static str, ExprId, String),
}

//------------------------------------------------------------------------------
// Cross-check
//------------------------------------------------------------------------------

/// A construction the census calls removable that this walk refuses.
#[derive(Debug, Clone, Serialize)]
pub struct Disagreement {
    pub module: String,
    pub construction: ExprId,
    pub rejection: Rejection,
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct CrossCheck {
    /// Removable verdicts examined.
    pub checked: usize,
    /// …of which this walk also proves removable.
    pub agreed: usize,
    pub disagreements: Vec<Disagreement>,
    /// Constructions this walk would accept that the census does not call
    /// removable. Coverage left on the table, never a failure.
    pub census_stricter: usize,
    /// Constructions one side found in the population and the other did
    /// not: the two selections must agree exactly.
    pub only_here: Vec<ExprId>,
    pub only_there: Vec<ExprId>,
    /// Removable verdicts that needed a hop from another proof object.
    pub via_hops: usize,
    /// Every construction this walk re-derived as removable, by module and
    /// spine root. The milestone's accounting counts a construction as
    /// *normalised* only if it is in here: removable-but-unverified is
    /// unsupported, never normalised.
    pub verified: Vec<(String, ExprId)>,
}

/// Check one module: `population` is every construction the census found,
/// `removable` the subset it calls `ScalarReplace`/`WorkerReturn`/
/// `StateThread`, and `hops` the extra edges another proof object
/// establishes (see [`Verifier::hops`]).
pub fn cross_check(
    m: &Module,
    population: &HashSet<ExprId>,
    removable: &HashSet<ExprId>,
    hops: HashMap<(ExprId, usize), Vec<BinderId>>,
    out: &mut CrossCheck,
) {
    let mut v = Verifier::new(m).with_hops(hops);
    let mine: HashSet<ExprId> = v.cons.keys().copied().collect();
    out.only_here
        .extend(mine.difference(population).copied().collect::<Vec<_>>());
    out.only_there
        .extend(population.difference(&mine).copied().collect::<Vec<_>>());
    let mut roots: Vec<ExprId> = mine.iter().copied().collect();
    roots.sort_unstable();
    for root in roots {
        let verdict = v.verify(root);
        if removable.contains(&root) {
            out.checked += 1;
            match verdict {
                Ok(p) => {
                    out.agreed += 1;
                    out.via_hops += usize::from(p.used_hop);
                    out.verified.push((m.name.clone(), root));
                }
                Err(rejection) => out.disagreements.push(Disagreement {
                    module: m.name.clone(),
                    construction: root,
                    rejection,
                }),
            }
        } else if verdict.is_ok() {
            out.census_stricter += 1;
        }
    }
}
