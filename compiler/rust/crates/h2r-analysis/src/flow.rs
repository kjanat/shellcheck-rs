//! The def-use walk that follows one **aggregate value** from the place it
//! is built to every place it is used.
//!
//! This is the machinery M2.2 developed for tuples, with the tuple-specific
//! rules lifted out. What is left is generic over any *saturated
//! data-constructor application* — a program ADT (`Just x`, `T_Literal id
//! s`), a list cell, a boxed or unboxed tuple — because none of the rules
//! below read a constructor's name to decide anything. The population is
//! selected by the client; the constructor is identified through
//! [`Scope::head_sig`]'s [`DataConInfo`], never by name.
//!
//! # What the walk is
//!
//! An explicit worklist over **value locations**, never a recursion over
//! Core. A location is a node *plus the number of value arguments still
//! owed* before the aggregate appears: 0 means the node's value *is* the
//! aggregate, `k` means it is a function that returns the aggregate after
//! `k` more arguments. That debt is what lets the walk leave a function —
//! ascending past a lambda raises it, a call site that pays it exactly is a
//! location of the aggregate again — and it is why the walk is
//! interprocedural from the start. It terminates on a visited set keyed by
//! the `(node, debt)` pair, and it is bounded by [`LOCATION_BUDGET`] so a
//! pathological module degrades into an honest unresolved verdict instead
//! of a hang.
//!
//! Following a value into a callee's parameter or out of a function to its
//! call sites is a **may** analysis: the walk takes the union over every
//! call site it can see, and refuses (rather than guesses) as soon as one
//! of them is outside the module.
//!
//! # The rules
//!
//! The rule ids are the ones the tuple census established, and they keep
//! their spelling here because they name the *shape* the rule recognises,
//! not the constructor it was first written for:
//!
//! | Rule | What it recognises |
//! |---|---|
//! | [`T1_LET_BOUND`] | the construction is a `let`/top-level right-hand side; its uses are that binder's occurrences |
//! | [`T2_SCRUTINISED`] | a use is a `case` that takes the value apart; the alternative's field binders are exposed on the [`Scrutiny`] |
//! | [`T5_PASSED_LOCAL`] | a use is argument *i* of a saturated call to a known local callee |
//! | [`T6_RETURNED`] | the value is a local function's return value |
//! | [`T7_CALL_RESULT`] | …and a call site paying the debt exactly is a location again |
//! | [`T8_CASE_BINDER_ALIAS`] | the case binder aliases the whole value |
//! | [`T9_STORED`] | a use is a field of another constructor application |
//! | [`T10_OPAQUE_CALL`] | a use is an argument of a call this module cannot see into |
//! | [`T11_ESCAPE`] | anything else, with a machine-readable reason |
//! | [`T14_FORCED`] | a use forces the value whole without reading a field |
//! | [`T15_WHNF_ALT`] | a use is a `case` whose alternative for this constructor binds no field of it |
//!
//! # What a client adds
//!
//! A [`Client`] (a) selects its own population and calls [`walk`] once per
//! construction, (b) adds use kinds of its own through
//! [`Client::Use`]`: From<`[`FlowUse`]`>`, and (c) decides fates from the
//! uses the walk accumulated. Four hooks let it intercept the places where
//! a client-specific rule belongs: [`Client::on_binding`],
//! [`Client::on_alt`], [`Client::on_whnf`], [`Client::on_stored`] and
//! [`Client::on_call_arg`]. [`crate::tuples`] uses four of them (for
//! re-tupling, lazy selection, nested tuples and Parsec continuation hops)
//! and [`crate::fields`] two; a client with no extra rules implements none.
//!
//! Evidence hierarchy, strongest first (the same one [`crate::parsec`]
//! uses): 1 lexical binder identity, 2 structural shape, 3 def-use
//! dataflow, 4 GHC type compatibility, 5 textual type comparison, 6 names.
//!
//! # Sum types: which alternative is the scrutiny
//!
//! A `case` on the value is classified against the construction's own
//! [`DataConInfo`]: the alternative whose data constructor *is* this one —
//! matched on GHC's stable name, with the constructor tag corroborating —
//! is the scrutiny, and its binders are the fields ([`T2_SCRUTINISED`]).
//! For a product type that is the only alternative there is; for a sum type
//! a `case` with one alternative per constructor is the normal shape, and
//! only one of them can be taken by a value of this constructor.
//!
//! When no alternative names this constructor, the alternative a value of
//! it selects is the `DEFAULT` one, which binds no field: the case observes
//! the constructor to WHNF and reads nothing ([`T15_WHNF_ALT`]). A `case`
//! with only a `DEFAULT` alternative — `seq`, a force — is the same
//! observation under its own rule ([`T14_FORCED`]), kept separate because
//! it is the shape the tuple census established.
//!
//! Two things fall through to an escape with [`R_ALTS`]: an alternative
//! that names this constructor but does not bind its `repArity` fields (an
//! unboxed or existential field layout), and a `case` with neither a
//! matching alternative nor a `DEFAULT` (nothing it could select).
//!
//! [`Client::on_alt`] is offered the matching alternative and
//! [`Client::on_whnf`] the WHNF observation, so a client over a sum type
//! can rescue either before the generic rule fires.

use std::collections::HashSet;

use h2r_core_ir::{
    Alt, AltCon, BindSite, BinderId, BinderKind, DataConInfo, Edge, Expr, ExprId, Module,
};
use serde::Serialize;

use crate::callee::split_stable_name;
use crate::scope::Scope;
use crate::shape::value_args;

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------

/// The construction is the right-hand side of a `let` or top-level binding:
/// the value's uses are the resolved occurrences of that binder.
/// Evidence: lexical binder identity (1).
pub const T1_LET_BOUND: &str = "T1-LET-BOUND";
/// A use is the scrutinee of a `case` whose single alternative is a data
/// alternative binding the value's fields: the aggregate is taken apart
/// here and the box does not survive the match. The alternative's field
/// binders are recorded on the [`Scrutiny`], so a client can see which
/// fields a scrutiny binds. Evidence: structural shape (2).
pub const T2_SCRUTINISED: &str = "T2-SCRUTINISED";
/// A use is value argument *i* of a **saturated** call to a binder bound in
/// this module to a manifest lambda chain: the value flows on to the
/// occurrences of that chain's *i*-th value parameter. Evidence: lexical
/// identity of the callee (1) over structural shape of the call (2).
pub const T5_PASSED_LOCAL: &str = "T5-PASSED-LOCAL";
/// The value is the body of the innermost lambda of the manifest chain
/// bound to a local binder `f`: it is `f`'s return value, and the flow
/// continues at every call site of `f` in this module. Evidence: structural
/// shape (2) over lexical identity (1).
pub const T6_RETURNED: &str = "T6-RETURNED";
/// …and at a call site supplying exactly the chain's parameters, the call's
/// spine root is a value location of the same aggregate. Evidence:
/// dataflow (3) over 1 and 2.
pub const T7_CALL_RESULT: &str = "T7-CALL-RESULT";
/// The case binder of a scrutiny is an alias of the whole value; its own
/// occurrences are followed as value locations, so a match that also keeps
/// the boxed value cannot be mistaken for one that consumes it.
/// Evidence: lexical binder identity (1).
pub const T8_CASE_BINDER_ALIAS: &str = "T8-CASE-BINDER-ALIAS";
/// A use is a value argument of a saturated data-constructor application:
/// the value is stored in a field and outlives every scrutiny of it. A
/// proven real value. Evidence: structural shape (2) over `DataConInfo` (4).
pub const T9_STORED: &str = "T9-STORED";
/// A use is an argument of a call this module cannot see into: an import, a
/// class-op dispatch, a partial application, or an unknown higher-order
/// callee. What the callee does with the value is outside the module, so
/// the box has to exist — except when even the callee is unknown, which is
/// unresolved rather than proven. Evidence: lexical identity (1), signature
/// lookup (4).
pub const T10_OPAQUE_CALL: &str = "T10-OPAQUE-CALL";
/// A use is the scrutinee of a `case` with a single `DEFAULT` alternative
/// binding nothing: the value is *forced* and no field is read. Forcing a
/// constructor application is a no-op, so this neither keeps the box alive
/// nor reads it — it is recorded as a consumer that reads no field.
/// Evidence: structural shape (2).
pub const T14_FORCED: &str = "T14-FORCED";
/// A use is a `case` on the value whose alternatives contain none for this
/// constructor, so the alternative a value of it selects is the `DEFAULT`
/// one — or one that does name it but binds nothing. Either way the case
/// observes the value to WHNF and reads no field. Which alternative a value
/// of this constructor selects is decided by the construction's own
/// [`DataConInfo`] against the alternatives' data constructors, matched on
/// GHC's stable name with the tag corroborating. Evidence: structural shape
/// (2) over the constructor's identity (4).
pub const T15_WHNF_ALT: &str = "T15-WHNF-ALT";
/// Any other use: the value applied as a function, bound to an exported
/// binder, returned from an exported function, or reached through a closure
/// whose call sites are not visible. Recorded with a machine-readable
/// reason; never guessed. Evidence: structural shape (2).
pub const T11_ESCAPE: &str = "T11-ESCAPE";

// Reasons. `preserve` reasons name what holds the value; the others name
// what the rules could not follow. Two of the strings below still say
// "tuple" where the rule is about any aggregate ([`R_APPLIED`], [`R_ALTS`],
// and the `R_CLOSURE_INTO_PARAM` text): they are wire values that the
// milestone's residual tables and the regression gate are keyed on, so they
// are left exactly as M2.2 established them rather than renamed here.
pub const R_STORED_CON: &str = "stored-in-constructor-field";
pub const R_IMPORTED_LAZY: &str = "passed-to-imported-lazy-parameter";
pub const R_IMPORTED_STRICT: &str = "passed-to-imported-strict-parameter";
pub const R_CLASS_OP: &str = "passed-through-class-op-dispatch";
pub const R_IN_PAP: &str = "held-in-a-partial-application";
pub const R_HIGHER_ORDER: &str = "callee-is-an-unknown-higher-order-value";
pub const R_EXPORTED_RETURN: &str = "returned-from-an-exported-function";
pub const R_EXPORTED_BINDING: &str = "bound-to-an-exported-binding";
pub const R_CALL_OVERSAT: &str = "call-site-applies-past-the-return";
pub const R_NESTED_CLOSURE: &str = "returned-from-a-closure-with-no-visible-binding";
pub const R_CLOSURE_ARG: &str = "returned-from-a-closure-passed-to-a-local-value-callee";
pub const R_CLOSURE_STORED: &str = "returned-from-a-closure-stored-in-a-constructor";
pub const R_APPLIED: &str = "tuple-applied-as-a-function";
pub const R_ALTS: &str = "case-is-not-one-tuple-alternative";
pub const R_PAST_PARAMS: &str = "argument-lands-past-the-callee-parameters";
pub const R_TOO_LARGE: &str = "flow-exceeded-the-location-budget";
// Refined residuals, so the next milestone can pick each one up without
// re-analysing. The constructor and callee names in the detail are
// diagnostics; the *split* is by what kind of thing holds the closure.
pub const R_CLOSURE_CONSED: &str = "returned-from-a-closure-consed-onto-a-list";
pub const R_CLOSURE_ARG_IMPORTED: &str = "returned-from-a-closure-passed-to-an-imported-call";
pub const R_CLOSURE_ARG_CLASS_OP: &str = "returned-from-a-closure-passed-to-a-class-op";
pub const R_CLOSURE_ARG_UNKNOWN: &str =
    "returned-from-a-closure-passed-to-an-unknown-higher-order-callee";
pub const R_EXPORTED_WRAPPER_RETURN: &str = "returned-from-an-exported-wrapper-of-a-local-worker";
/// The *closure* that returns the value is handed to a known local callee's
/// parameter. Rewriting the aggregate away changes that parameter's type,
/// so every other closure reaching the parameter would have to be rewritten
/// too — and this flow does not see them. Refused rather than guessed.
pub const R_CLOSURE_INTO_PARAM: &str = "closure-returning-the-tuple-is-passed-into-a-parameter";
/// The value is handed to a local callee whose parameter cannot be split:
/// the callee is exported, or it is used somewhere as a value, so not every
/// call site of it is visible and rewritable.
pub const R_CALLEE_NOT_SPLITTABLE: &str = "callee-parameter-cannot-be-split";

/// Locations one flow may visit before it is abandoned as too large. No
/// flow on the `-O1` dump comes anywhere near it; it exists so a
/// pathological module degrades into an honest unresolved verdict instead
/// of a hang.
pub const LOCATION_BUDGET: usize = 20_000;

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

/// Why a verdict holds: a rule id, the nodes it read, and the binder whose
/// identity it rests on.
#[derive(Debug, Clone, Serialize)]
pub struct Evidence {
    pub rule: &'static str,
    pub nodes: Vec<ExprId>,
    pub binder: Option<BinderId>,
    pub note: String,
}

/// How a `case` came to observe the value without reading a field of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum WhnfHow {
    /// `case v of _ { DEFAULT -> … }`: a `seq` or a force ([`T14_FORCED`]).
    Forced,
    /// The case has alternatives, none of them for this constructor, so a
    /// value of it selects the `DEFAULT` one ([`T15_WHNF_ALT`]).
    DefaultAlt,
    /// The alternative for this constructor binds no binder at all — a
    /// nullary constructor, or a match that discards the fields.
    NoFields,
}

impl WhnfHow {
    pub fn name(self) -> &'static str {
        match self {
            WhnfHow::Forced => "forced-whole",
            WhnfHow::DefaultAlt => "default-alternative",
            WhnfHow::NoFields => "alternative-binds-no-field",
        }
    }
}

/// A use the generic rules produce. A client's own use type is built from
/// these plus whatever kinds its extra rules add.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowUse {
    /// `case v of C a b -> …`: taken apart here ([`T2_SCRUTINISED`]).
    Scrutinised {
        case: ExprId,
        all_fields_bound: bool,
    },
    /// Forced whole, without reading a field ([`T14_FORCED`]).
    Forced { case: ExprId },
    /// Observed to WHNF by a `case` whose alternative for this constructor
    /// binds no field of it ([`T15_WHNF_ALT`]).
    Whnf { case: ExprId, how: WhnfHow },
    /// Value argument `param` of a saturated call to a known local callee;
    /// the flow continues at that parameter's occurrences
    /// ([`T5_PASSED_LOCAL`]).
    PassedTo {
        call: ExprId,
        callee: BinderId,
        param: u32,
    },
    /// Returned from `function`; the flow continues at its call sites
    /// ([`T6_RETURNED`]).
    Returned { function: BinderId },
    /// Stored in a data constructor's field ([`T9_STORED`]).
    StoredIn { con: ExprId },
    /// Argument of a call this module cannot see into ([`T10_OPAQUE_CALL`]).
    PassedToUnknown { call: ExprId, why: &'static str },
    /// Anything else the rules do not accept ([`T11_ESCAPE`]).
    Escapes { at: ExprId, why: &'static str },
}

/// What the walk needs of a client's use type: where the use is, so an
/// escape can be recorded against the node it happened at.
pub trait Consumer: Copy {
    fn at(self) -> ExprId;
}

impl Consumer for FlowUse {
    fn at(self) -> ExprId {
        match self {
            FlowUse::Scrutinised { case, .. }
            | FlowUse::Forced { case }
            | FlowUse::Whnf { case, .. } => case,
            FlowUse::PassedTo { call, .. } | FlowUse::PassedToUnknown { call, .. } => call,
            FlowUse::StoredIn { con } => con,
            FlowUse::Escapes { at, .. } => at,
            FlowUse::Returned { .. } => 0,
        }
    }
}

/// One `case` the walk accepted as a read of the aggregate's fields, with
/// the alternative's **field binders** exposed: which binder each field
/// lands in, in field order. Recorded for every accepted alternative,
/// whether the generic rule ([`T2_SCRUTINISED`]) or a client rule classified
/// it, so a client can follow individual fields without re-deriving the alt.
#[derive(Debug, Clone)]
pub struct Scrutiny {
    pub case: ExprId,
    /// The location that was scrutinised.
    pub at: ExprId,
    /// The alternative's binders, in field order.
    pub field_binders: Vec<BinderId>,
    /// The alternative's right-hand side: the region in which those
    /// binders' occurrences are reached.
    pub rhs: ExprId,
}

/// The state one construction's walk accumulates.
pub struct Walk<U: Consumer> {
    work: Vec<(ExprId, u32)>,
    seen: HashSet<(ExprId, u32)>,
    pub consumers: Vec<U>,
    pub evidence: Vec<Evidence>,
    /// Escapes, as (is this a proven real value?, reason, detail, node).
    pub escapes: Vec<(bool, &'static str, String, ExprId)>,
    /// The value crossed a *return*: it is the result of a function whose
    /// call sites had to be followed. Passing it into a known callee's
    /// parameter is not that — the box still never outlives its scrutinies
    /// — so only a return sets this.
    pub returned: bool,
    /// Local binders the flow already crossed a *return* of, innermost
    /// first: what makes an exported return a wrapper of a local worker.
    pub returned_from: Vec<BinderId>,
    /// Every accepted scrutiny, with its field binders.
    pub scrutinies: Vec<Scrutiny>,
    /// The binder the construction itself is bound to, when it is a `let`
    /// or top-level right-hand side.
    pub bound: Option<BinderId>,
    /// Value locations visited: the size of the def-use proof.
    pub locations: usize,
    pub over_budget: bool,
    /// Alternatives a value of this construction cannot select, skipped at
    /// the `case`es the flow reached: the reachability the constructor
    /// buys over a shape-only walk.
    pub unreachable_alts: usize,
    /// Occurrences of a case binder that alias this value but sit in an
    /// alternative it cannot select, so they are not followed.
    pub alias_occurrences_unreachable: usize,
}

impl<U: Consumer> Walk<U> {
    /// Enqueue a value location: `id`'s value is the aggregate once `owed`
    /// more value arguments are supplied.
    pub fn push(&mut self, id: ExprId, owed: u32) {
        if self.seen.insert((id, owed)) {
            self.work.push((id, owed));
        }
    }

    pub fn use_(&mut self, u: U) {
        self.consumers.push(u);
    }

    /// The value leaves what this walk can follow. `preserve` says whether
    /// *where* it went proves it is a real value (a constructor field, a
    /// callee outside the module) as opposed to merely being unfollowable.
    /// Records the consumer and the escape together, so the consumer list is
    /// never missing a use.
    pub fn escape(&mut self, u: U, preserve: bool, why: &'static str, detail: String) {
        let at = u.at();
        self.consumers.push(u);
        self.escapes.push((preserve, why, detail, at));
    }
}

impl<U: Consumer + From<FlowUse>> Walk<U> {
    /// An escape with no more specific use kind ([`T11_ESCAPE`]).
    pub fn escape_at(&mut self, at: ExprId, preserve: bool, why: &'static str, detail: String) {
        self.evidence.push(Evidence {
            rule: T11_ESCAPE,
            nodes: vec![at],
            binder: None,
            note: if detail.is_empty() {
                why.to_string()
            } else {
                format!("{why} ({detail})")
            },
        });
        self.escape(FlowUse::Escapes { at, why }.into(), preserve, why, detail);
    }
}

//------------------------------------------------------------------------------
// What one walk needs to know about its module
//------------------------------------------------------------------------------

/// The module-level facts the walk reads, plus which construction it is
/// following. Borrowed, so a client keeps owning its `Scope`.
pub struct Ctx<'a, 'm> {
    pub m: &'m Module,
    pub scope: &'a Scope<'m>,
    /// Top-level binder of every flattened top-level pair, by pair index.
    pub top_pairs: &'a [BinderId],
    /// The spine root of the construction the walk starts from.
    pub start: ExprId,
    /// How many fields that construction has: the number of binders a
    /// `case` alternative must bind to count as a read of it.
    pub arity: u32,
    /// The construction's data constructor, when the client identified one
    /// (it always did, for a saturated construction). It is what decides
    /// *which* alternative of a `case` a value of this construction
    /// selects; `None` falls back to the single-alternative rule.
    pub con: Option<&'m DataConInfo>,
}

impl Ctx<'_, '_> {
    /// Is every occurrence of `b` the head of a spine that supplies at
    /// least `n` value arguments? If not, `b` is somewhere a *value*, and a
    /// call site of it exists that rewriting its parameters would miss.
    pub fn never_escapes(&self, b: BinderId, n: usize) -> bool {
        let m = self.m;
        m.occurrences(b).iter().all(|occ| {
            let root = m.spine_root(*occ);
            if root == *occ {
                return false;
            }
            let (head, args) = m.spine(root);
            m.strip(head) == m.strip(*occ) && value_args(self.scope, &args).len() >= n
        })
    }
}

//------------------------------------------------------------------------------
// The client's extension points
//------------------------------------------------------------------------------

/// A client of the walk: its use type, and the four places a rule of its
/// own can intercept. Every hook has a default that does nothing, so a
/// client with no extra rules implements only [`Client::Use`].
pub trait Client {
    /// The client's use kind. Everything the generic rules produce is a
    /// [`FlowUse`]; the client may add kinds of its own and push them from
    /// a hook.
    type Use: Consumer + From<FlowUse>;

    /// A location of the value was found to be bound to `b` — with no debt
    /// the binder *is* the value ([`T1_LET_BOUND`]), with a debt it is a
    /// function returning it ([`T6_RETURNED`]). Called after the exported
    /// check accepted the binder and before its occurrences are followed.
    fn on_binding(
        &mut self,
        _w: &mut Walk<Self::Use>,
        _cx: &Ctx<'_, '_>,
        _b: BinderId,
        _v: ExprId,
        _owed: u32,
    ) {
    }

    /// A `case` on the value whose alternative matches the construction.
    /// Return `true` to claim it: the generic [`T2_SCRUTINISED`] rule is
    /// then not applied. The [`Scrutiny`] is already recorded either way.
    fn on_alt(
        &mut self,
        _w: &mut Walk<Self::Use>,
        _cx: &Ctx<'_, '_>,
        _case: ExprId,
        _v: ExprId,
        _alt: &Alt,
    ) -> bool {
        false
    }

    /// A `case` on the value that observes it to WHNF and binds no field of
    /// this constructor ([`T15_WHNF_ALT`]) — the alternative a value of it
    /// selects is a `DEFAULT`, or names it but binds nothing. `alt` is that
    /// alternative when there is one. Return `true` to claim it before the
    /// generic rule records it.
    fn on_whnf(
        &mut self,
        _w: &mut Walk<Self::Use>,
        _cx: &Ctx<'_, '_>,
        _case: ExprId,
        _v: ExprId,
        _how: WhnfHow,
        _alt: Option<&Alt>,
    ) -> bool {
        false
    }

    /// The value (no debt) is value argument `idx` of a saturated
    /// application of the data constructor `dc`. Return the `preserve`
    /// reason for the generic [`T9_STORED`] rule, or `None` if the client
    /// recorded the use itself.
    #[allow(clippy::too_many_arguments)]
    fn on_stored(
        &mut self,
        _w: &mut Walk<Self::Use>,
        _cx: &Ctx<'_, '_>,
        _root: ExprId,
        _idx: usize,
        _dc: &DataConInfo,
        _occ: &str,
    ) -> Option<&'static str> {
        Some(R_STORED_CON)
    }

    /// The value is value argument `idx` of a spine whose head is not a
    /// data constructor. Return `true` to claim it, before the
    /// known-local-call rule ([`T5_PASSED_LOCAL`]) and the opaque-call rule
    /// ([`T10_OPAQUE_CALL`]) are tried.
    #[allow(clippy::too_many_arguments)]
    fn on_call_arg(
        &mut self,
        _w: &mut Walk<Self::Use>,
        _cx: &Ctx<'_, '_>,
        _root: ExprId,
        _idx: usize,
        _head: ExprId,
        _occ: &str,
        _owed: u32,
    ) -> bool {
        false
    }
}

//------------------------------------------------------------------------------
// The walk
//------------------------------------------------------------------------------

/// Follow one construction from [`Ctx::start`] until every use is
/// classified or the budget runs out.
pub fn walk<C: Client>(cx: &Ctx<'_, '_>, client: &mut C) -> Walk<C::Use> {
    let start = cx.start;
    let mut w = Walk {
        work: vec![(start, 0)],
        seen: HashSet::from([(start, 0)]),
        consumers: Vec::new(),
        evidence: Vec::new(),
        escapes: Vec::new(),
        returned: false,
        returned_from: Vec::new(),
        scrutinies: Vec::new(),
        bound: None,
        locations: 0,
        over_budget: false,
        unreachable_alts: 0,
        alias_occurrences_unreachable: 0,
    };
    while let Some((v, owed)) = w.work.pop() {
        w.locations += 1;
        if w.locations > LOCATION_BUDGET {
            w.over_budget = true;
            break;
        }
        step(cx, client, &mut w, v, owed);
    }
    w
}

/// Classify one value location: what does the context do with the value
/// there — the aggregate itself when `owed` is 0, otherwise a function that
/// returns it after `owed` more arguments?
fn step<C: Client>(cx: &Ctx<'_, '_>, client: &mut C, w: &mut Walk<C::Use>, v: ExprId, owed: u32) {
    let m = cx.m;
    let Some(parent) = m.parent[v as usize] else {
        // A top-level right-hand side.
        let Edge::Top { pair } = m.edge[v as usize] else {
            w.escape_at(v, false, R_NESTED_CLOSURE, String::new());
            return;
        };
        let b = cx.top_pairs[pair as usize];
        follow_binding(cx, client, w, b, v, owed, BindSite::Top);
        return;
    };
    match m.edge[v as usize] {
        // A cast or tick is the same value.
        Edge::Cast | Edge::Tick => w.push(parent, owed),
        // The value of the `let`/`case` is this value: keep ascending.
        Edge::LetBody | Edge::CaseAlt { .. } => w.push(parent, owed),
        // Ascending past a lambda: the value here is a function that
        // returns the aggregate once one more argument is supplied
        // ([`T6_RETURNED`]).
        Edge::LamBody => {
            let Expr::Lam { binder, .. } = m.expr(parent) else {
                return;
            };
            let value_param = m.binder(*binder).kind != BinderKind::Tyvar;
            w.push(parent, owed + u32::from(value_param));
        }
        Edge::LetRhs { pair } => {
            let Expr::Let { bind, .. } = m.expr(parent) else {
                return;
            };
            let b = bind.pairs[pair as usize].binder;
            follow_binding(cx, client, w, b, v, owed, BindSite::Let);
        }
        Edge::CaseScrut if owed == 0 => scrutiny(cx, client, w, parent, v),
        Edge::AppArg => argument(cx, client, w, parent, v, owed),
        // A closure that still owes arguments is applied here: the spine
        // that applies it pays part or all of the debt ([`T7_CALL_RESULT`]).
        Edge::AppFun if owed > 0 => applied(cx, w, v, owed),
        // An aggregate applied as a function is impossible; a closure
        // scrutinised or handed to a callee is not followed.
        Edge::AppFun => w.escape_at(parent, false, R_APPLIED, String::new()),
        Edge::CaseScrut => w.escape_at(parent, false, R_NESTED_CLOSURE, String::new()),
        Edge::Top { .. } => {}
    }
}

/// A value location bound to `b`. With no debt the binder *is* the value
/// and its occurrences are value locations ([`T1_LET_BOUND`]); with a debt
/// it is a function returning it, and its occurrences are call sites to
/// follow ([`T6_RETURNED`]). Either way the flow is bounded by the binder's
/// resolved occurrences — unless the binder is exported, when there are
/// call sites this module cannot see.
fn follow_binding<C: Client>(
    cx: &Ctx<'_, '_>,
    client: &mut C,
    w: &mut Walk<C::Use>,
    b: BinderId,
    v: ExprId,
    owed: u32,
    site: BindSite,
) {
    let m = cx.m;
    if owed == 0 && (v == cx.start || m.strip(v) == cx.start) {
        w.bound = Some(b);
    }
    if owed > 0 {
        w.use_(FlowUse::Returned { function: b }.into());
    }
    if site == BindSite::Top && m.binder(b).exported == Some(true) {
        let worker = w.returned_from.iter().rev().find(|x| **x != b).copied();
        let (why, detail) = match (owed, worker) {
            (0, _) => (R_EXPORTED_BINDING, m.binder(b).occ.clone()),
            // The value already crossed a *local* function's return before
            // reaching this exported one: the exported binder is a wrapper
            // around that worker, and resolving it needs the worker's
            // callers, not the exported function's.
            (_, Some(k)) => (
                R_EXPORTED_WRAPPER_RETURN,
                format!("{} of {}", m.binder(b).occ, m.binder(k).occ),
            ),
            _ => (R_EXPORTED_RETURN, m.binder(b).occ.clone()),
        };
        w.escape_at(v, false, why, detail);
        return;
    }
    if owed > 0 {
        w.returned = true;
        w.returned_from.push(b);
    }
    client.on_binding(w, cx, b, v, owed);
    w.evidence.push(Evidence {
        rule: if owed > 0 { T6_RETURNED } else { T1_LET_BOUND },
        nodes: vec![v],
        binder: Some(b),
        note: format!(
            "{} {} with {} occurrence(s)",
            if owed > 0 {
                format!("returned from (after {owed} more argument(s))")
            } else {
                "bound to".to_string()
            },
            m.binder(b).occ,
            m.occurrences(b).len()
        ),
    });
    for occ in m.occurrences(b) {
        w.push(*occ, owed);
    }
}

/// The closure at `v` (owing `owed` arguments before it returns the
/// aggregate) is in the head position of an application spine.
fn applied<U: Consumer + From<FlowUse>>(cx: &Ctx<'_, '_>, w: &mut Walk<U>, v: ExprId, owed: u32) {
    let m = cx.m;
    let root = m.spine_root(v);
    let (_, args) = m.spine(root);
    let n = value_args(cx.scope, &args).len() as u32;
    match n.cmp(&owed) {
        std::cmp::Ordering::Equal => {
            w.evidence.push(Evidence {
                rule: T7_CALL_RESULT,
                nodes: vec![root],
                binder: None,
                note: format!("{n} argument(s) supplied: the call result is the tuple"),
            });
            w.push(root, 0);
        }
        // Still a function: a partial application, which is a value holding
        // the aggregate's eventual producer. Keep following it.
        std::cmp::Ordering::Less => w.push(root, owed - n),
        std::cmp::Ordering::Greater => {
            w.escape_at(root, false, R_CALL_OVERSAT, format!("{n} of {owed}"))
        }
    }
}

/// `case v of …` ([`T2_SCRUTINISED`] / [`T8_CASE_BINDER_ALIAS`] /
/// [`T14_FORCED`] / [`T15_WHNF_ALT`]).
///
/// Which alternative this *value* selects is decided by the construction's
/// own constructor, the way GHC decides it: the alternative whose data
/// constructor has the same stable name (the tag corroborates) is the one
/// taken, and every other alternative is **unreachable for this value**.
/// When no alternative names it, a `DEFAULT` is what it selects; when there
/// is not even one, nothing here can be selected and the flow escapes
/// rather than being called unobserved.
///
/// Reachability applies to the case *binder* too. It is in scope in every
/// alternative, but only the selected one runs, so only its occurrences of
/// the binder are value locations of this aggregate; an occurrence under
/// another constructor's alternative cannot be reached by this value and is
/// counted, not followed ([`Walk::alias_occurrences_unreachable`]).
fn scrutiny<C: Client>(
    cx: &Ctx<'_, '_>,
    client: &mut C,
    w: &mut Walk<C::Use>,
    case: ExprId,
    v: ExprId,
) {
    let m = cx.m;
    let Expr::Case { binder, alts, .. } = m.expr(case) else {
        return;
    };
    // Forcing the whole value without reading a field: a no-op on a
    // constructor application, and no field is read ([`T14_FORCED`]).
    if alts.len() == 1 && matches!(alts[0].con, AltCon::Default) && alts[0].binders.is_empty() {
        alias_binder(cx, w, case, *binder, Some(0));
        if client.on_whnf(w, cx, case, v, WhnfHow::Forced, Some(&alts[0])) {
            return;
        }
        w.use_(FlowUse::Forced { case }.into());
        w.evidence.push(Evidence {
            rule: T14_FORCED,
            nodes: vec![case, v],
            binder: None,
            note: "forced whole; no field read".into(),
        });
        return;
    }
    // The alternative this constructor selects. Identity first: the
    // alternative whose data constructor is this one. Failing that — no
    // `DataConInfo` to compare against — a *single* data alternative
    // binding exactly the construction's fields is the only one a value
    // reaching this case can take, which is the rule the tuple census
    // established and is still structurally exact.
    let by_con = cx.con.and_then(|dc| {
        alts.iter().position(|a| match &a.con {
            AltCon::DataAlt { name, tag, .. } => *name == dc.name && *tag == dc.tag,
            _ => false,
        })
    });
    let arity = cx.con.map(|dc| dc.rep_arity).unwrap_or(cx.arity) as usize;
    let single = (alts.len() == 1
        && matches!(alts[0].con, AltCon::DataAlt { .. })
        && alts[0].binders.len() == arity)
        .then_some(0usize);
    let default = alts.iter().position(|a| matches!(a.con, AltCon::Default));
    let Some(sel) = by_con.or(single).or(default) else {
        // Nothing this value could select: conservatively unresolved, never
        // "the construction was not observed here".
        alias_binder(cx, w, case, *binder, None);
        w.escape_at(
            case,
            false,
            R_ALTS,
            format!("{} alternative(s)", alts.len()),
        );
        return;
    };
    w.unreachable_alts += alts.len() - 1;
    alias_binder(cx, w, case, *binder, Some(sel));
    let alt = &alts[sel];
    let reads_fields = by_con.or(single) == Some(sel) && !alt.binders.is_empty();
    if !reads_fields {
        // The selected alternative binds no field of this constructor: the
        // case observes the value to WHNF and reads nothing.
        let how = if matches!(alt.con, AltCon::Default) {
            WhnfHow::DefaultAlt
        } else {
            WhnfHow::NoFields
        };
        if client.on_whnf(w, cx, case, v, how, Some(alt)) {
            return;
        }
        w.use_(FlowUse::Whnf { case, how }.into());
        w.evidence.push(Evidence {
            rule: T15_WHNF_ALT,
            nodes: vec![case, v],
            binder: None,
            note: format!(
                "{} of {} alternative(s); no field of this constructor is bound",
                how.name(),
                alts.len()
            ),
        });
        return;
    }
    if alt.binders.len() != arity {
        // This constructor's alternative, but it does not bind its
        // representation fields: a layout the field rules cannot index.
        w.escape_at(
            case,
            false,
            R_ALTS,
            format!("{} binder(s) for {arity} field(s)", alt.binders.len()),
        );
        return;
    }
    // Expose which binder each field lands in, for clients that follow
    // fields rather than the whole value.
    w.scrutinies.push(Scrutiny {
        case,
        at: v,
        field_binders: alt.binders.clone(),
        rhs: alt.rhs,
    });
    if client.on_alt(w, cx, case, v, alt) {
        return;
    }
    w.use_(
        FlowUse::Scrutinised {
            case,
            all_fields_bound: !alt.binders.is_empty(),
        }
        .into(),
    );
    w.evidence.push(Evidence {
        rule: T2_SCRUTINISED,
        nodes: vec![case, v],
        binder: None,
        note: format!("{} field binder(s) bound", alt.binders.len()),
    });
}

/// The case binder is an alias of the whole value ([`T8_CASE_BINDER_ALIAS`]),
/// but only in the alternative this value selects: it is in scope in all of
/// them and only one of them runs. Occurrences elsewhere are unreachable for
/// this value and are counted instead of followed. `sel` is the selected
/// alternative, or `None` when nothing is selectable.
fn alias_binder<U: Consumer>(
    cx: &Ctx<'_, '_>,
    w: &mut Walk<U>,
    case: ExprId,
    binder: BinderId,
    sel: Option<usize>,
) {
    let m = cx.m;
    let occs = m.occurrences(binder);
    if occs.is_empty() {
        return;
    }
    let (reachable, unreachable): (Vec<ExprId>, Vec<ExprId>) = occs
        .iter()
        .copied()
        .partition(|o| sel.is_some() && alt_of(m, case, *o) == sel);
    w.alias_occurrences_unreachable += unreachable.len();
    if reachable.is_empty() {
        return;
    }
    w.evidence.push(Evidence {
        rule: T8_CASE_BINDER_ALIAS,
        nodes: vec![case],
        binder: Some(binder),
        note: format!(
            "case binder {} aliases the tuple ({} occurrence(s))",
            m.binder(binder).occ,
            occs.len()
        ),
    });
    for occ in reachable {
        w.push(occ, 0);
    }
}

/// Which alternative of `case` the node `at` sits in, by climbing the
/// parent links to the `case` itself. `None` if it is not under one (the
/// scrutinee, or not under this case at all).
fn alt_of(m: &Module, case: ExprId, at: ExprId) -> Option<usize> {
    let mut cur = at;
    while let Some(p) = m.parent[cur as usize] {
        if p == case {
            return match m.edge[cur as usize] {
                Edge::CaseAlt { alt } => Some(alt as usize),
                _ => None,
            };
        }
        cur = p;
    }
    None
}

/// The value at `v` — the aggregate when `owed` is 0, otherwise a closure
/// that returns it — is a value argument of the spine `app` sits in.
fn argument<C: Client>(
    cx: &Ctx<'_, '_>,
    client: &mut C,
    w: &mut Walk<C::Use>,
    app: ExprId,
    v: ExprId,
    owed: u32,
) {
    let m = cx.m;
    let root = m.spine_root(app);
    let (head, args) = m.spine(root);
    let vargs = value_args(cx.scope, &args);
    let Some(idx) = vargs.iter().position(|a| *a == v) else {
        return; // a type argument: not a value flow
    };
    let occ = match m.expr(head) {
        Expr::Var { occ, .. } => occ.clone(),
        _ => String::new(),
    };
    let sig = cx.scope.head_sig(head);

    // Stored in a constructor field. With no debt that is the aggregate
    // itself: a real allocation holds it, which is the strongest `preserve`
    // evidence there is. With a debt it is the *closure* that is stored, and
    // whoever pulls it back out and calls it is not visible from here.
    if let Some(dc) = sig.and_then(|s| s.data_con) {
        if vargs.len() < dc.rep_arity as usize {
            w.escape(
                FlowUse::PassedToUnknown {
                    call: root,
                    why: R_IN_PAP,
                }
                .into(),
                owed == 0,
                R_IN_PAP,
                occ,
            );
            return;
        }
        if owed > 0 {
            // The *closure* is stored. Split by what holds it, so the
            // residual says which whole-program fact would resolve it.
            let why = if is_list_cons(&dc.name) {
                R_CLOSURE_CONSED
            } else {
                R_CLOSURE_STORED
            };
            w.escape_at(root, false, why, occ);
            return;
        }
        let Some(why) = client.on_stored(w, cx, root, idx, dc, &occ) else {
            return;
        };
        w.evidence.push(Evidence {
            rule: T9_STORED,
            nodes: vec![root],
            binder: None,
            note: format!("field {idx} of {occ}"),
        });
        w.escape(FlowUse::StoredIn { con: root }.into(), true, why, occ);
        return;
    }

    if client.on_call_arg(w, cx, root, idx, head, &occ, owed) {
        return;
    }

    // A call to something bound in this module to a manifest lambda chain:
    // the argument lands on a parameter whose occurrences are the next value
    // locations — with the same debt it arrived with.
    if let Some(bi) = m.binding_of(head)
        && matches!(bi.site, BindSite::Let | BindSite::Top)
        && let Some(rhs) = bi.rhs
    {
        let params = manifest_params(m, rhs);
        if !params.is_empty() {
            if vargs.len() < params.len() {
                w.escape(
                    FlowUse::PassedToUnknown {
                        call: root,
                        why: R_IN_PAP,
                    }
                    .into(),
                    owed == 0,
                    R_IN_PAP,
                    occ,
                );
                return;
            }
            if idx >= params.len() {
                w.escape(
                    FlowUse::PassedToUnknown {
                        call: root,
                        why: R_PAST_PARAMS,
                    }
                    .into(),
                    false,
                    R_PAST_PARAMS,
                    occ,
                );
                return;
            }
            if owed > 0 {
                // A *closure* that returns the aggregate, handed to a
                // parameter. Removing the aggregate changes that parameter's
                // representation, and the other closures that reach it are
                // not in this flow.
                w.escape_at(root, false, R_CLOSURE_INTO_PARAM, occ);
                return;
            }
            // Splitting the parameter rewrites every call site of the
            // callee, so they all have to be visible and be calls.
            if m.binder(bi.binder).exported == Some(true)
                || !cx.never_escapes(bi.binder, params.len())
            {
                w.escape_at(root, false, R_CALLEE_NOT_SPLITTABLE, occ);
                return;
            }
            let p = params[idx];
            w.use_(
                FlowUse::PassedTo {
                    call: root,
                    callee: bi.binder,
                    param: idx as u32,
                }
                .into(),
            );
            w.evidence.push(Evidence {
                rule: T5_PASSED_LOCAL,
                nodes: vec![root],
                binder: Some(p),
                note: format!(
                    "argument {idx} of the saturated call to {}; follows parameter {} (debt {owed})",
                    occ,
                    m.binder(p).occ
                ),
            });
            for o in m.occurrences(p) {
                w.push(*o, owed);
            }
            return;
        }
    }

    // Everything else: the callee is opaque ([`T10_OPAQUE_CALL`]). A value
    // handed to code outside the module has to exist; a *closure* handed out
    // says nothing about the aggregate it will return, so that is unresolved
    // rather than proven.
    if owed > 0 {
        let why = match sig {
            Some(s) if s.is_class_op => R_CLOSURE_ARG_CLASS_OP,
            Some(s) if s.sig_arity() > 0 && m.binding_of(head).is_none() => R_CLOSURE_ARG_IMPORTED,
            _ if m.binding_of(head).is_some() => R_CLOSURE_ARG,
            _ => R_CLOSURE_ARG_UNKNOWN,
        };
        w.escape_at(root, false, why, occ);
        return;
    }
    let (preserve, why) = match sig {
        Some(s) if s.is_class_op => (true, R_CLASS_OP),
        Some(s) if s.sig_arity() > 0 && m.binding_of(head).is_none() => match s.dmd_args.get(idx) {
            Some(d) if d.strict => (true, R_IMPORTED_STRICT),
            _ => (true, R_IMPORTED_LAZY),
        },
        _ => (false, R_HIGHER_ORDER),
    };
    w.evidence.push(Evidence {
        rule: T10_OPAQUE_CALL,
        nodes: vec![root],
        binder: None,
        note: format!("argument {idx} of {occ}: {why}"),
    });
    w.escape(
        FlowUse::PassedToUnknown { call: root, why }.into(),
        preserve,
        why,
        occ,
    );
}

//------------------------------------------------------------------------------
// Shared helpers
//------------------------------------------------------------------------------

/// Is this stable name the list cons constructor? A diagnostic split of the
/// residual only: no fate depends on it.
pub fn is_list_cons(name: &str) -> bool {
    matches!(
        split_stable_name(name),
        Some(("ghc-prim", "GHC.Types", ":"))
    )
}

/// Value parameters of the manifest lambda chain at `rhs`, in order.
pub fn manifest_params(m: &Module, rhs: ExprId) -> Vec<BinderId> {
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

/// The saturated data-constructor application rooted at `id`, if that is
/// what it is: the constructor, its `repArity` value arguments in field
/// order, and the head node. Identified through the head's
/// [`DataConInfo`](h2r_core_ir::DataConInfo) — never by name — so it is the
/// one population predicate every aggregate client can share.
pub fn saturated_con<'m>(
    scope: &Scope<'m>,
    id: ExprId,
) -> Option<(&'m DataConInfo, ExprId, Vec<ExprId>)> {
    let m = scope.m;
    if !matches!(m.expr(id), Expr::App { .. }) || m.spine_root(id) != id {
        return None;
    }
    let (head, args) = m.spine(id);
    let dc = scope.head_sig(head)?.data_con?;
    let vargs = value_args(scope, &args);
    if vargs.len() != dc.rep_arity as usize {
        return None;
    }
    Some((dc, head, vargs))
}
