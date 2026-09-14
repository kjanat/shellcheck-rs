//! A second, independent check of every *representation* verdict the three
//! M2.3 censuses publish in the direction where being wrong is a miscompile.
//!
//! [`crate::fields`], [`crate::lists`] and [`crate::text`] all derive their
//! verdicts by following a value forward with the generic aggregate walk
//! ([`crate::flow`]) and then joining facts over the consumers it found.
//! This module answers the same questions a different way and **shares no
//! code with any of them beyond the IR**: its own population selection, its
//! own constructor test, its own climb-and-enumerate walk. In particular it
//! does not use [`crate::flow`], and must not — the generic walk *is* the
//! censuses' walk, so re-deriving a verdict with it would only re-run the
//! analysis being checked.
//!
//! It is deliberately blunt: one verdict per claim, accept or refuse, no
//! ranking of reasons. Refusing more than a census does is a coverage loss
//! and is reported as such; the failure this exists to catch is a census
//! claiming one of the *unsafe* verdicts —
//!
//! | claim | what a wrong one costs |
//! |---|---|
//! | [`crate::fields::FieldRep::Direct`] | a field's evaluation is moved to the construction: a moved divergence |
//! | [`crate::fields::FieldRep::Dead`] | a field that is read is dropped |
//! | [`crate::lists::Recommendation::VecCandidate`] / `IteratorCandidate` | a spine that is shared or re-entered is turned into a one-shot iterator |
//! | [`crate::text::Advisory::StrongStringCandidate`] | a value whose characters are observed is turned into an opaque string |
//!
//! — where this walk can refuse it.
//!
//! # The two semantic dependencies, stated
//!
//! Two things are *asserted* rather than derived anywhere in this compiler,
//! and re-deriving them here would mean inventing a second, unchecked
//! assertion rather than checking the first:
//!
//! Since M2.3g the table is consulted on **four** axes, each re-derived
//! into a fact of its own here: the argument's spine demand, whether a tail
//! of it survives beside the call ([`axioms::Axiom::aliases_spine`], which
//! an element alias deliberately does not satisfy), whether the call
//! replays it, and whether the elements are *forced* or merely *exposed*.
//! Consulting a corrected table is still consulting it: these walks check
//! that the entry is applied to the right argument of a saturated call to
//! an import, not that the entry is true.
//!
//! * the **library demand-semantics table** ([`crate::lists::axioms`]) and
//!   the **text-head table** ([`crate::text::TEXT_HEADS`]). This module
//!   consults *the same* tables. What it re-derives itself is everything
//!   around them: that the head really is an import, its stable name, which
//!   value argument of the call the value lands in, how many value
//!   arguments the call supplies, and hence which entry row applies.
//! * **M1's** [`Class::RecursiveValue`](crate::laziness::Class). The
//!   milestones read it rather than re-deriving it, and so does this.
//!
//! Everything else — aliasing, reachability, scrutiny, storage, escape,
//! traversal counting — is re-derived from the arena here.

use std::collections::{HashMap, HashSet};

use h2r_core_ir::{
    AltCon, BindSite, BinderId, BinderKind, DataConInfo, Edge, Expr, ExprId, Module,
};
use serde::Serialize;

use crate::laziness::{Census, Class};
use crate::lists::axioms::{self, Alias, ArgSpine};

/// Mark a location as reached with `via_tail`, and say whether it must be
/// walked: a location seen only as tail-derived is walked again when it is
/// reached without a tail alias.
fn mark(seen: &mut HashMap<(ExprId, u32), bool>, key: (ExprId, u32), via_tail: bool) -> bool {
    match seen.get_mut(&key) {
        None => {
            seen.insert(key, via_tail);
            true
        }
        Some(prev) if *prev && !via_tail => {
            *prev = false;
            true
        }
        Some(_) => false,
    }
}

/// GHC's stable names for the list constructors, written out here rather
/// than imported, so that a mistake in selecting the population cannot be
/// common to both sides.
const CONS: &str = "$ghc-prim$GHC.Types$:";
const NIL: &str = "$ghc-prim$GHC.Types$[]";

const BUDGET: usize = 400_000;

//------------------------------------------------------------------------------
// What is claimed, and what comes back
//------------------------------------------------------------------------------

/// One census verdict to re-derive. `at` is the census' own node: a
/// construction for a field claim, a producer for a list or text claim.
#[derive(Debug, Clone, Serialize)]
pub struct Claim {
    pub module: String,
    pub kind: ClaimKind,
    pub at: ExprId,
    pub field: u32,
    /// The rule the census says proved it, for the `Direct` claims.
    pub rule: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ClaimKind {
    FieldDirect,
    FieldDead,
    FieldRecursive,
    ListKnot,
    ListVec,
    ListIterator,
    TextStrong,
}

impl ClaimKind {
    pub fn name(self) -> &'static str {
        match self {
            ClaimKind::FieldDirect => "field Direct",
            ClaimKind::FieldDead => "field Dead",
            ClaimKind::FieldRecursive => "field Recursive",
            ClaimKind::ListKnot => "list RecursiveKnot",
            ClaimKind::ListVec => "list VecCandidate",
            ClaimKind::ListIterator => "list IteratorCandidate",
            ClaimKind::TextStrong => "text StrongStringCandidate",
        }
    }
}

/// Why this walk will not re-derive a claim.
#[derive(Debug, Clone, Serialize)]
pub struct Refusal {
    pub why: &'static str,
    pub at: ExprId,
    pub detail: String,
}

// Refusal reasons. `W_` ones are this walk being blunter than the census
// and cost coverage only; `X_` ones are claims a census must not make.
pub const X_NOT_A_CONSTRUCTION: &str = "not-a-saturated-construction-of-the-claimed-shape";
pub const X_FIELD_NOT_STRICT: &str = "R1-claimed-but-the-field-is-not-strict";
pub const X_FIELD_NOT_A_VALUE: &str = "R2-claimed-but-the-field-expression-is-not-a-value";
pub const X_NO_RULE: &str = "Direct-with-no-rule-this-walk-can-re-derive";
/// The census proved the timing with `R3-SAME-FRONTIER`, which is a
/// statement about *its own* walk — that it crossed no return, no unknown
/// call, no lambda and no conditional between the construction and every
/// scrutiny. Re-deriving that here would be writing the same walk a second
/// time rather than checking it, so this walk declines: a coverage
/// refusal, not a claim. What it does instead is count the `R3` verdicts
/// and report the count, because the milestone's own assertion is that on
/// `-O1` there are none (GHC's case-of-known-constructor has already
/// eliminated every construction scrutinised in the frame that built it).
pub const W_NO_R3_RULE: &str = "R3-SAME-FRONTIER-is-the-census-own-walk-and-is-not-re-derived-here";
pub const X_DEAD_FIELD_READ: &str = "Dead-but-an-alternative-binder-for-the-field-is-used";
pub const X_DEAD_FIELD_STRICT: &str = "Dead-but-the-field-is-strict";
pub const X_DEAD_ESCAPES: &str = "Dead-but-the-value-escapes-the-walk";
pub const X_NOT_M1_RECURSIVE: &str = "M1-does-not-call-this-binding-a-recursive-value";
pub const X_SHARED_TAIL: &str = "a-tail-of-this-spine-survives-in-a-second-place";
pub const X_MULTI_PASS: &str = "more-than-one-independent-entry-into-the-spine";
pub const X_STORED: &str = "the-spine-is-stored-returned-or-captured";
pub const X_NOT_STREAMING: &str = "a-spine-consumer-is-not-streaming";
/// A consumer retains the spine and walks it again from the front, so one
/// pass over it is not enough (M2.3g).
pub const X_REPLAYED: &str = "a-consumer-replays-this-spine";
pub const X_NO_SPINE_DEMAND: &str = "no-reachable-consumer-demands-the-spine";
pub const X_NOT_WHOLE: &str = "Vec-claimed-but-no-consumer-demands-the-whole-spine";
pub const X_KNOT: &str = "M1-calls-this-binding-a-recursive-value";
pub const X_CHAR_OBSERVED: &str = "an-individual-character-is-observed";
/// …and the weaker half of it, split out at M2.3g: an element reaches a
/// predicate or a class method, which need not force it. Still a refusal —
/// the character has to exist as a value — but a different fact.
pub const X_CHAR_EXPOSED: &str = "an-individual-character-is-exposed-to-a-callback";
pub const X_PREFIX_CONSUMER: &str = "a-prefix-consumer";
pub const X_NOT_TEXT_ONLY: &str = "a-consumer-is-not-a-text-head";

pub const W_ESCAPES: &str = "the-value-leaves-what-this-walk-follows";
pub const W_OPAQUE_CALL: &str = "argument-of-a-call-this-walk-cannot-see-into";
pub const W_NO_AXIOM: &str = "no-axiom-for-this-imported-head";
pub const W_APPLIED: &str = "the-value-is-applied-as-a-function";
pub const W_NO_BINDING: &str = "the-value-has-no-enclosing-binding";
pub const W_EXPORTED: &str = "an-alias-is-an-exported-binding";
pub const W_ALTS: &str = "a-case-selects-no-alternative-this-value-could-take";
pub const W_BUDGET: &str = "the-walk-exceeded-its-budget";
pub const W_UNSUPPORTED: &str = "this-walk-has-no-rule-for-the-claim";
/// This walk counts every consumer reached across an `L7-CONSED-AS-TAIL`
/// hop as an independent entry into the spine, because from here the cells
/// of the longer spine *are* these cells. Where the longer spines are
/// alternatives of one `case` — a `go` whose result is consed at five
/// different branches — that is one entry at run time and several here.
/// Refusing on it is a coverage loss, not a claim about the census.
pub const W_ENTRIES_VIA_TAIL_HOP: &str = "entries-counted-across-a-consed-as-tail-hop";
/// `Whole` for a `go`-loop is M2.3c's `L4-LOOP-WHOLE`, which turns on where
/// the recursive call *stands* (evaluating position vs. a constructor field
/// vs. under a `case`). Re-deriving that here would mean writing the
/// loop-position analysis a second time rather than checking it, so this
/// walk establishes every other fact a `VecCandidate` rests on — no shared
/// tail, no value knot, a spine that is demanded, storage or re-entry — and
/// leaves the `Whole` fact to the census.
pub const W_LOOP_WHOLE: &str = "the-Whole-spine-of-a-loop-is-not-re-derivable-here";

/// What the walk enumerated when it accepts a claim.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Proof {
    pub aliases: usize,
    pub occurrences: usize,
    pub scrutinies: usize,
    pub imported_consumers: usize,
    pub locations: usize,
    /// For an `R2` field claim: the field expression is a value **only**
    /// because it is a string literal, which is accepted on
    /// `okForSpeculation` grounds and not because it is in WHNF.
    pub r2_string_literal_only: bool,
}

/// A claim this walk refuses.
#[derive(Debug, Clone, Serialize)]
pub struct Disagreement {
    pub claim: Claim,
    pub refusal: Refusal,
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct RepCrossCheck {
    pub checked: usize,
    pub agreed: usize,
    pub by_kind: Vec<(ClaimKind, usize, usize)>,
    pub disagreements: Vec<Disagreement>,
    /// `Direct`/`R2` verdicts whose only evidence is the string-literal
    /// case.
    pub r2_string_literal_only: usize,
    pub r2_total: usize,
    pub r1_total: usize,
    pub r3_total: usize,
}

/// Is this refusal a claim about the census (a verdict it must not make),
/// or this walk declining to re-derive something (a coverage loss)?
pub fn is_coverage_refusal(why: &str) -> bool {
    matches!(
        why,
        W_ESCAPES
            | W_OPAQUE_CALL
            | W_NO_AXIOM
            | W_APPLIED
            | W_NO_BINDING
            | W_EXPORTED
            | W_ALTS
            | W_BUDGET
            | W_UNSUPPORTED
            | W_NO_R3_RULE
            | W_ENTRIES_VIA_TAIL_HOP
            | W_LOOP_WHOLE
    )
}

impl RepCrossCheck {
    /// Refusals that say the census claimed something this walk can show is
    /// wrong, as opposed to this walk being blunter than it.
    pub fn real_disagreements(&self) -> usize {
        self.disagreements
            .iter()
            .filter(|d| !is_coverage_refusal(d.refusal.why))
            .count()
    }

    /// Refusals that are only this walk declining to re-derive a fact.
    pub fn coverage_refusals(&self) -> usize {
        self.disagreements.len() - self.real_disagreements()
    }
}

//------------------------------------------------------------------------------
// The walk
//------------------------------------------------------------------------------

/// What the value is known to be, which is what makes alternative selection
/// constructor-relative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Known<'a> {
    /// A saturated construction of this data constructor.
    Con(&'a str),
    /// A list whose head constructor is not known (an imported call's
    /// result): a `case` on it may take either alternative.
    List,
}

/// One place the value was observed.
#[derive(Debug, Clone)]
enum Obs {
    /// A `case` that selects an alternative of the known constructor.
    Alt {
        case: ExprId,
        binders: Vec<BinderId>,
        /// Reached through another consumer's tail alias: the same
        /// traversal continued, not a new entry into the spine.
        via_tail: bool,
    },
    /// A `case` that observes the value and binds no field of it.
    Whnf { case: ExprId, via_tail: bool },
    /// A value argument of a saturated call to an imported head.
    Imported {
        call: ExprId,
        name: String,
        idx: usize,
        n: usize,
        via_tail: bool,
    },
    /// A field of a data constructor that is not a list cell.
    Stored { at: ExprId, con: String },
    /// The tail argument of a list cell: the spine continues there, and
    /// this walk continues with it.
    ConsedAsTail {},
}

#[derive(Debug, Default)]
struct Walk {
    obs: Vec<Obs>,
    /// The walk continued across an `L7`-shaped hop: the value became the
    /// tail of a longer spine and the longer spine's consumers were taken
    /// as consumers of this one.
    via_l7: bool,
    escapes: Vec<(&'static str, ExprId, String)>,
    returned: bool,
    crossed_lambda: bool,
    aliases: Vec<BinderId>,
    /// `(:)`-alternative head binders, and whether each is used.
    heads: Vec<(BinderId, bool)>,
    occurrences: usize,
    locations: usize,
    over_budget: bool,
}

pub struct RepVerifier<'m> {
    m: &'m Module,
    /// Binding right-hand sides M1 calls recursive *values*.
    m1_recursive: HashSet<ExprId>,
    never_escapes: HashMap<BinderId, bool>,
}

enum Landing {
    Bind(BinderId, u32),
    Scrutiny(ExprId, u32),
    Applied(ExprId, u32),
    Argument(ExprId, ExprId, u32),
    Reject(&'static str, ExprId),
}

impl<'m> RepVerifier<'m> {
    pub fn new(m: &'m Module, census: &Census) -> RepVerifier<'m> {
        RepVerifier {
            m,
            m1_recursive: census
                .bindings
                .iter()
                .filter(|b| b.module == m.name && b.class == Class::RecursiveValue)
                .map(|b| b.rhs)
                .collect(),
            never_escapes: HashMap::new(),
        }
    }

    //--------------------------------------------------------------------------
    // Structural primitives, re-derived here
    //--------------------------------------------------------------------------

    fn vargs(&self, args: &[ExprId]) -> Vec<ExprId> {
        args.iter()
            .copied()
            .filter(|a| {
                !matches!(
                    self.m.expr(self.m.strip(*a)),
                    Expr::Type(_) | Expr::Coercion
                )
            })
            .collect()
    }

    /// The data constructor at the head of a spine, if the head is an
    /// imported id with a `DataConInfo`.
    fn head_data_con(&self, head: ExprId) -> Option<&'m DataConInfo> {
        let Expr::Var { unique, .. } = self.m.expr(head) else {
            return None;
        };
        if self.m.resolve(head).is_some() {
            return None;
        }
        self.m.ids.get(unique)?.data_con.as_ref()
    }

    /// The stable name of the head of a spine, if the head is an import.
    fn imported_name(&self, head: ExprId) -> Option<&'m str> {
        let Expr::Var { name, .. } = self.m.expr(head) else {
            return None;
        };
        if self.m.resolve(head).is_some() {
            return None;
        }
        Some(name)
    }

    /// The saturated construction rooted at `root`, if there is one.
    fn construction_at(&self, root: ExprId) -> Option<(&'m DataConInfo, Vec<ExprId>)> {
        let m = self.m;
        if m.spine_root(root) != root {
            return None;
        }
        // A nullary constructor is its own spine root and is not an `App`.
        if let Expr::Var { .. } = m.expr(root) {
            let dc = self.head_data_con(root)?;
            return (dc.rep_arity == 0).then(|| (dc, Vec::new()));
        }
        if !matches!(m.expr(root), Expr::App { .. }) {
            return None;
        }
        let (head, args) = m.spine(root);
        let dc = self.head_data_con(head)?;
        let vargs = self.vargs(&args);
        if vargs.len() != dc.rep_arity as usize {
            return None;
        }
        Some((dc, vargs))
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

    /// Is every occurrence of `b` the head of a spine supplying at least
    /// `n` value arguments? If not, `b` is a value somewhere.
    fn never_escapes(&mut self, b: BinderId, n: usize) -> bool {
        if let Some(v) = self.never_escapes.get(&b) {
            return *v;
        }
        let m = self.m;
        let mut ok = true;
        for occ in m.occurrences(b) {
            let root = m.spine_root(*occ);
            if root == *occ {
                ok = false;
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

    /// Is `node` inside the subtree rooted at `root`?
    fn within(&self, node: ExprId, root: ExprId) -> bool {
        node == root || self.m.ancestors(node).any(|a| a == root)
    }

    /// Is the field expression already a value, so that evaluating it where
    /// the constructor is built moves no work and can introduce no new
    /// divergence? Returns `(is_value, only_because_it_is_a_string_literal)`.
    ///
    /// A **string literal** — `unpackCString# "…"#` — is accepted, and it
    /// is the one clause that does *not* argue from WHNF: the expression is
    /// an unsaturated-looking call that GHC's `exprIsHNF` rejects. It is
    /// accepted because it is total, terminating and cheap, so evaluating
    /// it eagerly can neither diverge nor error — `okForSpeculation`
    /// reasoning, not WHNF reasoning. Every verdict that rests on this
    /// clause alone is counted separately and reported.
    fn field_is_value(&self, id: ExprId) -> (bool, bool) {
        let m = self.m;
        let inner = m.strip(id);
        match m.expr(inner) {
            // A literal, a lambda, or a variable: no allocation, nothing to
            // move. A variable occurrence is a pointer to a binding that
            // already exists; forcing the slot eagerly cannot move work
            // that this expression does, because it does none.
            Expr::Lit(_) | Expr::Lam { .. } | Expr::Var { .. } => (true, false),
            Expr::App { .. } => {
                let (head, args) = m.spine(inner);
                let vargs = self.vargs(&args);
                // A string literal.
                if let Some(name) = self.imported_name(head)
                    && is_string_literal_head(name)
                    && vargs.len() == 1
                    && matches!(m.expr(m.strip(vargs[0])), Expr::Lit(_))
                {
                    return (true, true);
                }
                // A saturated constructor application, or a partial
                // application of anything: both are values.
                if let Some(dc) = self.head_data_con(head) {
                    return (vargs.len() <= dc.rep_arity as usize, false);
                }
                let arity = m
                    .resolve(m.strip(head))
                    .map(|b| self.params_of(b).len())
                    .or_else(|| {
                        let Expr::Var { unique, .. } = m.expr(head) else {
                            return None;
                        };
                        m.ids.get(unique).map(|i| i.arity as usize)
                    });
                match arity {
                    Some(a) if vargs.len() < a => (true, false),
                    _ => (false, false),
                }
            }
            _ => (false, false),
        }
    }

    //--------------------------------------------------------------------------
    // The one walk
    //--------------------------------------------------------------------------

    /// Enumerate every occurrence of the value produced at `root`, through
    /// every alias, and record what each one does with it.
    fn walk(&mut self, root: ExprId, known: Known<'_>) -> Walk {
        let m = self.m;
        let mut w = Walk::default();
        let mut work: Vec<(ExprId, u32, bool)> = vec![(root, 0, false)];
        // A location reached both through a tail alias and *not* through
        // one is an independent entry into the spine: the non-tail arrival
        // wins, so a location already seen as tail-derived is re-walked
        // when it turns up again without one.
        let mut seen: HashMap<(ExprId, u32), bool> = HashMap::from([((root, 0), false)]);
        let mut bound: HashSet<(BinderId, u32)> = HashSet::new();
        while let Some((start, start_owed, via_tail)) = work.pop() {
            w.locations += 1;
            if w.locations > BUDGET {
                w.over_budget = true;
                w.escapes.push((W_BUDGET, root, String::new()));
                return w;
            }
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
                            None => break Landing::Reject(W_NO_BINDING, n),
                        }
                    }
                    (None, _) => break Landing::Reject(W_NO_BINDING, n),
                    (Some(parent), edge) => match edge {
                        Edge::Cast | Edge::Tick | Edge::LetBody | Edge::CaseAlt { .. } => {
                            n = parent
                        }
                        Edge::LamBody => {
                            let Expr::Lam { binder, .. } = m.expr(parent) else {
                                break Landing::Reject(W_NO_BINDING, parent);
                            };
                            if m.binder(*binder).kind != BinderKind::Tyvar {
                                owed += 1;
                                w.crossed_lambda = true;
                            }
                            n = parent;
                        }
                        Edge::LetRhs { pair } => {
                            let Expr::Let { bind, .. } = m.expr(parent) else {
                                break Landing::Reject(W_NO_BINDING, parent);
                            };
                            break Landing::Bind(bind.pairs[pair as usize].binder, owed);
                        }
                        Edge::Top { .. } => break Landing::Reject(W_NO_BINDING, n),
                        Edge::CaseScrut => break Landing::Scrutiny(parent, owed),
                        Edge::AppArg => break Landing::Argument(parent, n, owed),
                        Edge::AppFun => break Landing::Applied(n, owed),
                    },
                }
            };
            match landed {
                Landing::Reject(why, at) => w.escapes.push((why, at, String::new())),
                Landing::Bind(b, owed) => {
                    if m.binding(b).site == BindSite::Top && m.binder(b).exported == Some(true) {
                        w.escapes.push((W_EXPORTED, start, m.binder(b).occ.clone()));
                        continue;
                    }
                    if owed > 0 {
                        w.returned = true;
                    }
                    if bound.insert((b, owed)) {
                        if owed == 0 {
                            w.aliases.push(b);
                        }
                        for occ in m.occurrences(b) {
                            w.occurrences += 1;
                            if mark(&mut seen, (*occ, owed), via_tail) {
                                work.push((*occ, owed, via_tail));
                            }
                        }
                    }
                }
                Landing::Scrutiny(case, owed) => {
                    if owed > 0 {
                        w.escapes
                            .push((W_ESCAPES, case, "a closure is scrutinised".into()));
                        continue;
                    }
                    let Expr::Case { binder, alts, .. } = m.expr(case) else {
                        w.escapes.push((W_ALTS, case, String::new()));
                        continue;
                    };
                    // Constructor-relative selection: only the alternative
                    // this value can take is reachable, and the case
                    // binder's occurrences *inside the others* are not.
                    let picked: Vec<usize> = match known {
                        Known::Con(name) => alts
                            .iter()
                            .position(
                                |a| matches!(&a.con, AltCon::DataAlt { name: n, .. } if n == name),
                            )
                            .map(|i| vec![i])
                            .unwrap_or_else(|| {
                                alts.iter()
                                    .position(|a| matches!(a.con, AltCon::Default))
                                    .map(|i| vec![i])
                                    .unwrap_or_default()
                            }),
                        Known::List => {
                            let mut v: Vec<usize> = alts
                                .iter()
                                .enumerate()
                                .filter(|(_, a)| {
                                    matches!(&a.con, AltCon::DataAlt { name, .. }
                                             if name == CONS || name == NIL)
                                })
                                .map(|(i, _)| i)
                                .collect();
                            if v.is_empty() {
                                v = alts
                                    .iter()
                                    .position(|a| matches!(a.con, AltCon::Default))
                                    .map(|i| vec![i])
                                    .unwrap_or_default();
                            }
                            v
                        }
                    };
                    if picked.is_empty() {
                        w.escapes
                            .push((W_ALTS, case, format!("{} alternative(s)", alts.len())));
                        continue;
                    }
                    for i in picked {
                        let alt = &alts[i];
                        let cons = matches!(&alt.con, AltCon::DataAlt { name, .. } if name == CONS);
                        if alt.binders.is_empty() {
                            w.obs.push(Obs::Whnf { case, via_tail });
                        } else {
                            w.obs.push(Obs::Alt {
                                case,
                                binders: alt.binders.clone(),
                                via_tail,
                            });
                        }
                        if cons && alt.binders.len() == 2 {
                            // The head binder is an element; record whether
                            // it is used at all.
                            let hb = alt.binders[0];
                            w.heads.push((hb, !m.occurrences(hb).is_empty()));
                            // The tail binder *is* the rest of this spine.
                            for occ in m.occurrences(alt.binders[1]) {
                                w.occurrences += 1;
                                if mark(&mut seen, (*occ, 0), true) {
                                    work.push((*occ, 0, true));
                                }
                            }
                        }
                        // The case binder is the whole value under another
                        // name — but only where it is reachable.
                        for occ in m.occurrences(*binder) {
                            if !self.within(*occ, alt.rhs) {
                                continue;
                            }
                            w.occurrences += 1;
                            if mark(&mut seen, (*occ, 0), via_tail) {
                                work.push((*occ, 0, via_tail));
                            }
                        }
                    }
                }
                Landing::Applied(at, owed) => {
                    if owed == 0 {
                        w.escapes.push((W_APPLIED, at, String::new()));
                        continue;
                    }
                    let root2 = m.spine_root(at);
                    let (_, args) = m.spine(root2);
                    let k = self.vargs(&args).len() as u32;
                    if k > owed {
                        w.escapes.push((W_ESCAPES, root2, "over-applied".into()));
                        continue;
                    }
                    if mark(&mut seen, (root2, owed - k), via_tail) {
                        work.push((root2, owed - k, via_tail));
                    }
                }
                Landing::Argument(app, v, owed) => {
                    let root2 = m.spine_root(app);
                    let (head, args) = m.spine(root2);
                    let vargs = self.vargs(&args);
                    let Some(idx) = vargs.iter().position(|a| *a == v) else {
                        w.escapes
                            .push((W_ESCAPES, root2, "not a value argument".into()));
                        continue;
                    };
                    if owed > 0 {
                        w.escapes
                            .push((W_ESCAPES, root2, "a closure is handed out".into()));
                        continue;
                    }
                    if let Some(dc) = self.head_data_con(head) {
                        if dc.name == CONS && idx == 1 && vargs.len() == 2 {
                            // `L7`-shaped: the value becomes the tail of a
                            // longer spine. Its cells are that spine's
                            // cells, so the walk continues at the cell —
                            // whatever demands the outer spine demands this
                            // one, which is the conservative reading.
                            w.obs.push(Obs::ConsedAsTail {});
                            w.via_l7 = true;
                            if mark(&mut seen, (root2, 0), via_tail) {
                                work.push((root2, 0, via_tail));
                            }
                        } else {
                            w.obs.push(Obs::Stored {
                                at: root2,
                                con: dc.name.clone(),
                            });
                        }
                        continue;
                    }
                    if let Some(name) = self.imported_name(head) {
                        w.obs.push(Obs::Imported {
                            call: root2,
                            name: name.to_string(),
                            idx,
                            n: vargs.len(),
                            via_tail,
                        });
                        continue;
                    }
                    // A call to a function bound in this module.
                    let Some(hb) = m.resolve(m.strip(head)) else {
                        w.escapes.push((W_OPAQUE_CALL, root2, String::new()));
                        continue;
                    };
                    if !matches!(m.binding(hb).site, BindSite::Let | BindSite::Top) {
                        w.escapes.push((W_OPAQUE_CALL, root2, String::new()));
                        continue;
                    }
                    let params = self.params_of(hb);
                    if params.is_empty()
                        || idx >= params.len()
                        || vargs.len() < params.len()
                        || m.binder(hb).exported == Some(true)
                        || !self.never_escapes(hb, params.len())
                    {
                        w.escapes
                            .push((W_OPAQUE_CALL, root2, m.binder(hb).occ.clone()));
                        continue;
                    }
                    for o in m.occurrences(params[idx]) {
                        w.occurrences += 1;
                        if mark(&mut seen, (*o, 0), via_tail) {
                            work.push((*o, 0, via_tail));
                        }
                    }
                }
            }
        }
        w
    }

    //--------------------------------------------------------------------------
    // The claims
    //--------------------------------------------------------------------------

    /// The binding group a node's right-hand side belongs to, and whether
    /// it is recursive.
    fn enclosing_group(&self, node: ExprId) -> Option<(HashSet<BinderId>, bool, ExprId)> {
        let m = self.m;
        let mut cur = node;
        loop {
            match m.edge[cur as usize] {
                Edge::LetRhs { .. } => {
                    let parent = m.parent[cur as usize]?;
                    let Expr::Let { bind, .. } = m.expr(parent) else {
                        return None;
                    };
                    return Some((
                        bind.pairs.iter().map(|p| p.binder).collect(),
                        bind.recursive,
                        cur,
                    ));
                }
                Edge::Top { pair } => {
                    let mut group = HashSet::new();
                    let mut rec = false;
                    let mut i = 0usize;
                    for bind in &m.top {
                        let k = bind.pairs.len();
                        if (i..i + k).contains(&(pair as usize)) {
                            group.extend(bind.pairs.iter().map(|p| p.binder));
                            rec = bind.recursive;
                        }
                        i += k;
                    }
                    return Some((group, rec, cur));
                }
                Edge::Cast | Edge::Tick => cur = m.parent[cur as usize]?,
                _ => return None,
            }
        }
    }

    /// Does M1 call the binding this node is the right-hand side of a
    /// recursive *value*, and does the value refer back into its own group?
    fn is_m1_knot(&self, node: ExprId, roots: &[ExprId]) -> bool {
        let m = self.m;
        let Some((group, rec, rhs)) = self.enclosing_group(node) else {
            return false;
        };
        if !rec {
            return false;
        }
        if !(self.m1_recursive.contains(&rhs) || matches!(m.edge[rhs as usize], Edge::Top { .. })) {
            return false;
        }
        roots.iter().any(|r| {
            m.preorder(*r)
                .any(|n| m.resolve(n).is_some_and(|b| group.contains(&b)))
        })
    }

    /// Re-derive one claim.
    pub fn check(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        match c.kind {
            ClaimKind::FieldDirect => self.check_direct(c),
            ClaimKind::FieldDead => self.check_dead(c),
            ClaimKind::FieldRecursive => self.check_field_recursive(c),
            ClaimKind::ListKnot => self.check_list_knot(c),
            ClaimKind::ListVec | ClaimKind::ListIterator => self.check_candidate(c),
            ClaimKind::TextStrong => self.check_strong_string(c),
        }
    }

    fn check_direct(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        let Some((dc, vargs)) = self.construction_at(c.at) else {
            return Err(Refusal {
                why: X_NOT_A_CONSTRUCTION,
                at: c.at,
                detail: String::new(),
            });
        };
        let i = c.field as usize;
        let mut p = Proof::default();
        // R1: GHC already made the field strict.
        if dc.strict_fields.get(i).copied().unwrap_or(false) {
            if c.rule == crate::fields::R2_FIELD_IS_VALUE {
                // Not a disagreement: a strict field is also Direct. The
                // census prefers R1, so this cannot happen; check anyway.
            }
            return Ok(p);
        }
        if c.rule == crate::fields::R1_STRICT_FIELD {
            return Err(Refusal {
                why: X_FIELD_NOT_STRICT,
                at: c.at,
                detail: format!("{} field {i}", dc.name),
            });
        }
        // R2: the field expression is already a value.
        let Some(field) = vargs.get(i).copied() else {
            return Err(Refusal {
                why: X_NOT_A_CONSTRUCTION,
                at: c.at,
                detail: format!("no field {i}"),
            });
        };
        let (is_value, string_only) = self.field_is_value(field);
        if is_value {
            p.r2_string_literal_only = string_only;
            return Ok(p);
        }
        // R3 is the only rule left, and this walk has no way to re-derive
        // "the same evaluation frontier" that is not the census' own walk.
        // It must find none.
        Err(Refusal {
            why: match c.rule {
                crate::fields::R2_FIELD_IS_VALUE => X_FIELD_NOT_A_VALUE,
                crate::fields::R3_SAME_FRONTIER => W_NO_R3_RULE,
                _ => X_NO_RULE,
            },
            at: field,
            detail: c.rule.to_string(),
        })
    }

    fn check_dead(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        let Some((dc, _)) = self.construction_at(c.at) else {
            return Err(Refusal {
                why: X_NOT_A_CONSTRUCTION,
                at: c.at,
                detail: String::new(),
            });
        };
        let i = c.field as usize;
        if dc.strict_fields.get(i).copied().unwrap_or(false) {
            return Err(Refusal {
                why: X_DEAD_FIELD_STRICT,
                at: c.at,
                detail: format!("{} field {i}", dc.name),
            });
        }
        let name = dc.name.clone();
        let w = self.walk(c.at, Known::Con(&name));
        if let Some((why, at, detail)) = w.escapes.first().cloned() {
            return Err(Refusal {
                why: if why == W_BUDGET {
                    W_BUDGET
                } else {
                    X_DEAD_ESCAPES
                },
                at,
                detail: format!("{why} {detail}"),
            });
        }
        for o in &w.obs {
            if let Obs::Alt { case, binders, .. } = o
                && let Some(b) = binders.get(i)
                && !self.m.occurrences(*b).is_empty()
            {
                return Err(Refusal {
                    why: X_DEAD_FIELD_READ,
                    at: *case,
                    detail: self.m.binder(*b).occ.clone(),
                });
            }
        }
        if self.is_m1_knot(c.at, &[c.at]) {
            return Err(Refusal {
                why: X_KNOT,
                at: c.at,
                detail: String::new(),
            });
        }
        Ok(Proof {
            aliases: w.aliases.len(),
            occurrences: w.occurrences,
            scrutinies: w.obs.len(),
            locations: w.locations,
            ..Proof::default()
        })
    }

    fn check_field_recursive(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        let Some((_, vargs)) = self.construction_at(c.at) else {
            return Err(Refusal {
                why: X_NOT_A_CONSTRUCTION,
                at: c.at,
                detail: String::new(),
            });
        };
        let Some(field) = vargs.get(c.field as usize).copied() else {
            return Err(Refusal {
                why: X_NOT_A_CONSTRUCTION,
                at: c.at,
                detail: String::new(),
            });
        };
        if self.is_m1_knot(c.at, &[field]) {
            Ok(Proof::default())
        } else {
            Err(Refusal {
                why: X_NOT_M1_RECURSIVE,
                at: c.at,
                detail: String::new(),
            })
        }
    }

    fn check_list_knot(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        // Every cell of the chain the producer builds is a root to look for
        // a back-reference in, which is what the census does too — the
        // *fact* being checked is M1's, the cells are re-derived here.
        let roots = self.cells_of(c.at);
        if self.is_m1_knot(c.at, &roots) {
            Ok(Proof::default())
        } else {
            Err(Refusal {
                why: X_NOT_M1_RECURSIVE,
                at: c.at,
                detail: String::new(),
            })
        }
    }

    /// What a list producer node is known to be. A `[]` can only ever
    /// select a `[]` alternative, so every `(:)` alternative of a `case` on
    /// it — and every occurrence of the case binder inside one — is
    /// unreachable for it. A cons chain's *own* cell is a `(:)`, but its
    /// tail alias need not be, so a cons flow is followed with both
    /// alternatives live: strictly more conservative than the census, which
    /// can only make this walk refuse more.
    fn known_of(&self, producer: ExprId) -> Result<Known<'static>, Refusal> {
        match self.construction_at(producer) {
            Some((dc, _)) if dc.name == NIL => Ok(Known::Con(NIL)),
            Some((dc, _)) if dc.name == CONS => Ok(Known::List),
            Some((dc, _)) => Err(Refusal {
                why: X_NOT_A_CONSTRUCTION,
                at: producer,
                detail: dc.name.clone(),
            }),
            None => Ok(Known::List),
        }
    }

    /// The cons cells one producer node builds, outermost first.
    fn cells_of(&self, root: ExprId) -> Vec<ExprId> {
        let m = self.m;
        let mut out = Vec::new();
        let mut cur = root;
        while let Some((dc, vargs)) = self.construction_at(cur) {
            if dc.name != CONS || vargs.len() != 2 {
                break;
            }
            out.push(cur);
            cur = m.spine_root(m.strip(vargs[1]));
        }
        if out.is_empty() { vec![root] } else { out }
    }

    /// `VecCandidate` and `IteratorCandidate`: re-derive the facts they
    /// rest on.
    fn check_candidate(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        let known = self.known_of(c.at)?;
        let w = self.walk(c.at, known);
        if let Some((why, at, detail)) = w.escapes.first().cloned() {
            return Err(Refusal { why, at, detail });
        }
        let f = self.facts(&w)?;
        if !f.shared_tails.is_empty() {
            return Err(Refusal {
                why: X_SHARED_TAIL,
                at: f.shared_tails[0],
                detail: String::new(),
            });
        }
        if self.is_m1_knot(c.at, &self.cells_of(c.at)) {
            return Err(Refusal {
                why: X_KNOT,
                at: c.at,
                detail: String::new(),
            });
        }
        if f.spine_consumers.is_empty() {
            return Err(Refusal {
                why: X_NO_SPINE_DEMAND,
                at: c.at,
                detail: String::new(),
            });
        }
        match c.kind {
            ClaimKind::ListIterator => {
                // Nothing may outlive the one pass: not a constructor
                // field, not a return, not a capture.
                if let Some(at) = f.stored {
                    return Err(Refusal {
                        why: X_STORED,
                        at,
                        detail: f.stored_in.clone().unwrap_or_default(),
                    });
                }
                if w.returned {
                    return Err(Refusal {
                        why: X_STORED,
                        at: c.at,
                        detail: "the spine crosses a return".into(),
                    });
                }
                if f.traversals > 1 {
                    return Err(Refusal {
                        why: if w.via_l7 {
                            W_ENTRIES_VIA_TAIL_HOP
                        } else {
                            X_MULTI_PASS
                        },
                        at: f.spine_consumers[0],
                        detail: format!("{} entries", f.traversals),
                    });
                }
                if let Some(at) = f.not_streaming {
                    return Err(Refusal {
                        why: X_NOT_STREAMING,
                        at,
                        detail: String::new(),
                    });
                }
                if let Some(at) = f.replayed.first() {
                    return Err(Refusal {
                        why: X_REPLAYED,
                        at: *at,
                        detail: String::new(),
                    });
                }
            }
            ClaimKind::ListVec if !f.whole => {
                return Err(Refusal {
                    why: if w.via_l7 || f.structural {
                        W_LOOP_WHOLE
                    } else {
                        X_NOT_WHOLE
                    },
                    at: c.at,
                    detail: String::new(),
                });
            }
            _ => {}
        }
        Ok(Proof {
            aliases: w.aliases.len(),
            occurrences: w.occurrences,
            scrutinies: f.spine_consumers.len(),
            imported_consumers: f.imported,
            locations: w.locations,
            ..Proof::default()
        })
    }

    /// `StrongStringCandidate`.
    fn check_strong_string(&mut self, c: &Claim) -> Result<Proof, Refusal> {
        let known = self.known_of(c.at)?;
        let w = self.walk(c.at, known);
        if let Some((why, at, detail)) = w.escapes.first().cloned() {
            return Err(Refusal { why, at, detail });
        }
        let f = self.facts(&w)?;
        if !f.shared_tails.is_empty() {
            return Err(Refusal {
                why: X_SHARED_TAIL,
                at: f.shared_tails[0],
                detail: String::new(),
            });
        }
        if let Some(at) = f.prefix_consumer {
            return Err(Refusal {
                why: X_PREFIX_CONSUMER,
                at,
                detail: String::new(),
            });
        }
        // **M2.3g.** Forcing and exposure are re-derived separately, and
        // the refusal says which of the two it saw. Either disqualifies the
        // claim; only one of them is a proof that anything is evaluated.
        if let Some(at) = f.head_forced {
            return Err(Refusal {
                why: X_CHAR_OBSERVED,
                at,
                detail: String::new(),
            });
        }
        if let Some(at) = f.head_exposed.or(f.char_observed) {
            return Err(Refusal {
                why: X_CHAR_EXPOSED,
                at,
                detail: String::new(),
            });
        }
        if let Some(at) = f.not_text_only {
            return Err(Refusal {
                why: X_NOT_TEXT_ONLY,
                at,
                detail: String::new(),
            });
        }
        if self.is_m1_knot(c.at, &self.cells_of(c.at)) {
            return Err(Refusal {
                why: X_KNOT,
                at: c.at,
                detail: String::new(),
            });
        }
        Ok(Proof {
            aliases: w.aliases.len(),
            occurrences: w.occurrences,
            imported_consumers: f.imported,
            locations: w.locations,
            ..Proof::default()
        })
    }

    /// The spine facts, re-derived from one walk's observations.
    fn facts(&self, w: &Walk) -> Result<SpineFacts, Refusal> {
        let mut f = SpineFacts::default();
        for o in &w.obs {
            match o {
                Obs::Alt { case, via_tail, .. } => {
                    // A structural `case` on the cells: a spine consumer,
                    // and not a text-shaped one.
                    f.push_consumer(*case, *via_tail);
                    f.structural = true;
                    f.not_text_only.get_or_insert(*case);
                }
                Obs::Whnf { case, via_tail } => {
                    f.push_consumer(*case, *via_tail);
                    f.prefix_consumer.get_or_insert(*case);
                }
                Obs::Stored { at, con } => {
                    // Storage is a fact about lifetime, not about what is
                    // demanded: a stored value has no consumer here at all,
                    // which is neither a text-shaped consumer nor a
                    // non-text one. It is what an `Iterator` claim turns
                    // on and what a `StrongString` claim does not.
                    f.stored.get_or_insert(*at);
                    f.stored_in.get_or_insert_with(|| con.clone());
                }
                // Followed in the walk itself; nothing to record here.
                Obs::ConsedAsTail { .. } => {}
                Obs::Imported {
                    call,
                    name,
                    idx,
                    n,
                    via_tail,
                } => {
                    f.imported += 1;
                    let Some(ax) = axioms::axiom(name) else {
                        // The text table can still speak for a head the
                        // axiom table has no entry for.
                        match crate::text::text_head(name) {
                            Some(th) => {
                                if th.char_exposing || th.position_semantics {
                                    f.char_observed.get_or_insert(*call);
                                }
                                f.push_consumer(*call, *via_tail);
                                continue;
                            }
                            None => {
                                return Err(Refusal {
                                    why: W_NO_AXIOM,
                                    at: *call,
                                    detail: name.clone(),
                                });
                            }
                        }
                    };
                    if *n < ax.min_args {
                        return Err(Refusal {
                            why: W_OPAQUE_CALL,
                            at: *call,
                            detail: format!("{name}: {n} of {} value arguments", ax.min_args),
                        });
                    }
                    // Re-derive which argument of *this* call the value is,
                    // end-indexed, and read the row for it.
                    let spine = ax.spine_of(*idx, *n);
                    // The *result* of this call keeps a tail of this
                    // spine alive beside it.
                    // **M2.3g.** A tail of this spine surviving beside the
                    // call is the aliasing axis, and it is asked
                    // independently of whether the call node is a list:
                    // `span` returns a pair whose second component is a
                    // suffix of this argument. An element alias
                    // (`head :: [[a]] -> [a]`) is deliberately not a tail.
                    if !matches!(ax.alias, Alias::NoAlias) && ax.aliases_spine(*idx, *n) {
                        f.shared_tails.push(*call);
                    }
                    // …and whether the call walks this spine a second time
                    // from the front, which a one-pass iterator cannot do.
                    if ax.replays_arg(*idx, *n) {
                        f.replayed.push(*call);
                    }
                    match spine {
                        None => {
                            return Err(Refusal {
                                why: W_NO_AXIOM,
                                at: *call,
                                detail: format!("{name}: argument {idx} of {n} is not a list"),
                            });
                        }
                        Some(ArgSpine::NoDemand) => {}
                        Some(s) => {
                            f.push_consumer(*call, *via_tail);
                            if s == ArgSpine::Whole {
                                f.whole = true;
                            }
                            if matches!(
                                s,
                                ArgSpine::PrefixFromArg(_) | ArgSpine::PrefixDataDependent
                            ) {
                                f.prefix_consumer.get_or_insert(*call);
                            }
                            if !ax.streaming {
                                f.not_streaming.get_or_insert(*call);
                            }
                        }
                    }
                    // **M2.3g.** Proven forcing and mere exposure to a
                    // callback are re-derived as two facts. Either is
                    // enough to disqualify a `StrongString` claim — the
                    // element has to exist as a value — but the refusal
                    // now says which one it was.
                    if ax.head != crate::lists::HeadDemand::None {
                        f.head_forced.get_or_insert(*call);
                        f.char_observed.get_or_insert(*call);
                    }
                    if ax.exposure != axioms::HeadExposure::NotExposed {
                        f.head_exposed.get_or_insert(*call);
                        f.char_observed.get_or_insert(*call);
                    }
                    if crate::text::text_head(name).is_none() {
                        f.not_text_only.get_or_insert(*call);
                    } else if crate::text::text_head(name)
                        .is_some_and(|th| th.char_exposing || th.position_semantics)
                    {
                        f.char_observed.get_or_insert(*call);
                    }
                }
            }
        }
        for (b, used) in &w.heads {
            if *used {
                // A `(:)` alternative that binds and uses the element
                // exposes it; whether it *forces* it is L3's question and
                // this walk does not answer it (M2.3g).
                f.head_exposed
                    .get_or_insert_with(|| self.m.occurrences(*b)[0]);
                f.char_observed
                    .get_or_insert_with(|| self.m.occurrences(*b)[0]);
            }
        }
        f.entries.sort_unstable();
        f.entries.dedup();
        f.traversals = if f.entries.is_empty() && !f.spine_consumers.is_empty() {
            1
        } else {
            f.entries.len()
        };
        Ok(f)
    }
}

#[derive(Debug, Default)]
struct SpineFacts {
    spine_consumers: Vec<ExprId>,
    /// Spine consumers *not* reached through another consumer's tail
    /// alias: each is an independent entry into the spine.
    entries: Vec<ExprId>,
    shared_tails: Vec<ExprId>,
    /// Consumers that retain the spine and walk it again (M2.3g).
    replayed: Vec<ExprId>,
    stored: Option<ExprId>,
    stored_in: Option<String>,
    prefix_consumer: Option<ExprId>,
    char_observed: Option<ExprId>,
    /// An element is **provably forced** (M2.3g).
    head_forced: Option<ExprId>,
    /// An element is handed to a callback that need not force it (M2.3g).
    head_exposed: Option<ExprId>,
    not_streaming: Option<ExprId>,
    not_text_only: Option<ExprId>,
    imported: usize,
    traversals: usize,
    whole: bool,
    /// A `case` in this module takes the cells apart. How far such a loop
    /// walks is `L4`/`L5`/`L17`'s question, and this walk does not answer
    /// it (see [`W_LOOP_WHOLE`]).
    structural: bool,
}

impl SpineFacts {
    fn push_consumer(&mut self, at: ExprId, via_tail: bool) {
        self.spine_consumers.push(at);
        if !via_tail {
            self.entries.push(at);
        }
    }
}

/// The `unpackCString#` family: a static string literal unpacked into
/// `[Char]`. Written out here rather than shared.
fn is_string_literal_head(name: &str) -> bool {
    matches!(
        name,
        "$ghc-prim$GHC.CString$unpackCString#"
            | "$ghc-prim$GHC.CString$unpackCStringUtf8#"
            | "$ghc-prim$GHC.CString$unpackNBytes#"
    )
}

//------------------------------------------------------------------------------
// Cross-check
//------------------------------------------------------------------------------

/// Re-derive every claim in `claims` for one module.
pub fn cross_check(m: &Module, census: &Census, claims: &[Claim], out: &mut RepCrossCheck) {
    let mut v = RepVerifier::new(m, census);
    let mut per_kind: HashMap<ClaimKind, (usize, usize)> = HashMap::new();
    for c in claims {
        out.checked += 1;
        let e = per_kind.entry(c.kind).or_default();
        e.0 += 1;
        if c.kind == ClaimKind::FieldDirect {
            match c.rule {
                crate::fields::R1_STRICT_FIELD => out.r1_total += 1,
                crate::fields::R2_FIELD_IS_VALUE => out.r2_total += 1,
                _ => out.r3_total += 1,
            }
        }
        match v.check(c) {
            Ok(p) => {
                out.agreed += 1;
                e.1 += 1;
                if p.r2_string_literal_only {
                    out.r2_string_literal_only += 1;
                }
            }
            Err(refusal) => out.disagreements.push(Disagreement {
                claim: c.clone(),
                refusal,
            }),
        }
    }
    for (k, (n, ok)) in per_kind {
        match out.by_kind.iter_mut().find(|(kk, _, _)| *kk == k) {
            Some(row) => {
                row.1 += n;
                row.2 += ok;
            }
            None => out.by_kind.push((k, n, ok)),
        }
    }
    out.by_kind.sort();
}
