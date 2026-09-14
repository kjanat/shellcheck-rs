//! Structural recognition of Parsec's CPS representation in optimised Core.
//!
//! `Text.Parsec.Prim` represents a parser as
//!
//! ```text
//! newtype ParsecT s u m a = ParsecT { unParser :: forall b.
//!       State s u
//!    -> (a -> State s u -> ParseError -> m b)   -- consumed ok    (cok)
//!    -> (ParseError -> m b)                     -- consumed error (cerr)
//!    -> (a -> State s u -> ParseError -> m b)   -- empty ok       (eok)
//!    -> (ParseError -> m b)                     -- empty error    (eerr)
//!    -> m b }
//! ```
//!
//! By the time the simplifier is done the newtype is gone, every combinator
//! is inlined, and what is left is raw CPS: lambdas that bind a state and
//! four continuations, and calls that apply them. The census attributes
//! those sites to Parsec *by name* (`cok`, `cerr`, `eok`, `eerr`, `eta`),
//! which is only a diagnostic: GHC names every eta-expanded parameter
//! `eta`, renames unused ones `ds`, and a `cok`-named binder is not
//! evidence of anything. This module proves the roles instead, from
//!
//! * the binder **types** the plugin dumps (`State s u`, `ParseError`,
//!   `a -> State s u -> ParseError -> r`), which survive optimisation, and
//! * the **dataflow**: every use of a candidate role binder must be a
//!   continuation call, a propagation into a continuation slot of a
//!   recognised parser call, a state scrutinee, or an eta-reduced form of
//!   one of those. Anything else rejects the whole region.
//!
//! Nothing here reads an occurrence name. Names are carried in the proof
//! object as labels only.
//!
//! # What the dump actually looks like
//!
//! The layout is *discovered*, not assumed. On the `-O1` dump of
//! ShellCheck the five Parsec parameters always appear in Parsec's own
//! order — state, cok, cerr, eok, eerr — as a contiguous run at the end of
//! a lambda chain, optionally preceded by the parser's own arguments and
//! optionally followed by **two** trailing parameters of type
//! `Environment m` and `SystemState`: ShellCheck's parser monad is
//! `ParsecT String UserState (SCBase m)` with
//! `SCBase m = ReaderT (Environment m) (StateT SystemState m)`, and those
//! two newtypes erase to two extra function arguments on `m b`.
//!
//! Worker/wrapper drops *absent* continuations, so a run may be shorter
//! than four and any subset of the four slots may be missing. The run is
//! therefore matched as a **subsequence** of the four-slot template; when
//! more than one embedding fits, the role is a proven finite set rather
//! than a single slot.
//!
//! # Scoping
//!
//! Uniques are **not** unique in an optimised dump: inlining duplicates a
//! term without freshening its binders (`ShellCheck.Parser` has 41,874
//! binders over 8,257 distinct uniques). Every occurrence is therefore
//! resolved to its innermost enclosing binder by [`crate::scope::Scope`],
//! the same resolution the census uses; no pass here keys anything by
//! unique.

use std::collections::{BTreeMap, HashMap};

use h2r_core_ir::{AltCon, Binder, BinderId, BinderKind, Edge, Expr, ExprId, Module};
use serde::Serialize;

use crate::callee::{Family, ParsecTarget};
use crate::laziness::Census;
use crate::scope::Scope;
use crate::shape::{ArgShape, value_args};

//------------------------------------------------------------------------------
// Types, as GHC pretty-prints them
//------------------------------------------------------------------------------

/// Split a pretty-printed type on its top-level `->`.
pub fn split_arrows(ty: &str) -> Vec<&str> {
    let b = ty.as_bytes();
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    let mut i = 0usize;
    while i < b.len() {
        match b[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b'-' if depth == 0 && i + 1 < b.len() && b[i + 1] == b'>' => {
                parts.push(ty[start..i].trim());
                i += 2;
                start = i;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    parts.push(ty[start..].trim());
    parts
}

/// Drop redundant outer parentheses.
pub fn strip_parens(ty: &str) -> &str {
    let mut t = ty.trim();
    while t.starts_with('(') && t.ends_with(')') {
        let b = t.as_bytes();
        let mut depth = 0i32;
        let mut balanced = true;
        for (i, c) in b.iter().enumerate() {
            match c {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 && i + 1 < b.len() {
                        balanced = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if !balanced {
            break;
        }
        t = t[1..t.len() - 1].trim();
    }
    t
}

/// Drop a leading `forall ….` quantifier.
fn strip_forall(ty: &str) -> &str {
    let t = strip_parens(ty);
    match t.strip_prefix("forall ") {
        Some(rest) => match rest.find(". ") {
            Some(i) => rest[i + 2..].trim(),
            None => t,
        },
        None => t,
    }
}

/// Canonical form of a pretty-printed type, with type *variables* renamed in
/// order of first appearance.
///
/// GHC's pretty-printer disambiguates type variables inside each `SDoc`
/// independently, so the same Core type variable is printed `b` on one
/// binder and `b1` on the next. Comparing type strings verbatim across
/// binders therefore reports differences that are not there.
///
/// This is level 5 of the evidence hierarchy and the weakest thing here: it
/// is a *textual* comparison and two genuinely different type variables can
/// normalise alike. It is therefore only ever used to **refuse** — a region
/// whose continuations disagree about their result type is not a region —
/// and never as the support for a verdict. Every proof rests on the layout
/// (2) and the dataflow rules; if this function wrongly equated two
/// variables, the only effect would be that a chain the stricter comparison
/// would have skipped still has to survive every use rule to be proven.
pub fn alpha_normalise(ty: &str) -> String {
    let mut out = String::with_capacity(ty.len());
    let mut names: Vec<&str> = Vec::new();
    let b = ty.as_bytes();
    let mut i = 0usize;
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'\'') {
                i += 1;
            }
            let word = &ty[start..i];
            if word.starts_with(|ch: char| ch.is_ascii_lowercase() || ch == '_') {
                let idx = match names.iter().position(|w| *w == word) {
                    Some(k) => k,
                    None => {
                        names.push(word);
                        names.len() - 1
                    }
                };
                out.push_str(&format!("t{idx}"));
            } else {
                out.push_str(word);
            }
            continue;
        }
        out.push(c as char);
        i += 1;
    }
    out
}

/// `State s u`: Parsec's parser state.
pub fn is_state_ty(ty: &str) -> bool {
    let t = strip_forall(ty);
    t == "State" || t.starts_with("State ")
}

/// `ParseError`: the error *value*, not a continuation.
pub fn is_parse_error_ty(ty: &str) -> bool {
    strip_forall(ty) == "ParseError"
}

/// Which of ParsecT's two continuation shapes a type has, and how many
/// arguments it still needs.
///
/// * `a -> State s u -> ParseError -> r` — an ok continuation, arity 3.
/// * `State s u -> ParseError -> r` — an ok continuation whose value has
///   already been supplied (GHC builds these as partial applications),
///   arity 2.
/// * `ParseError -> r` — an error continuation, arity 1. Note that an ok
///   continuation with two arguments already supplied has the same shape;
///   the type cannot tell them apart, so this is only ever used for the
///   arity arithmetic and for the coarse ok/err distinction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ContShape {
    pub kind: ContKind,
    /// Value arguments still owed before the continuation runs.
    pub arity: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ContKind {
    Ok,
    Err,
}

pub fn cont_shape_of_arrows(a: &[&str]) -> Option<ContShape> {
    if a.len() >= 4 && is_state_ty(a[1]) && is_parse_error_ty(a[2]) {
        return Some(ContShape {
            kind: ContKind::Ok,
            arity: 3,
        });
    }
    if a.len() >= 3 && is_state_ty(a[0]) && is_parse_error_ty(a[1]) {
        return Some(ContShape {
            kind: ContKind::Ok,
            arity: 2,
        });
    }
    if a.len() >= 2 && is_parse_error_ty(a[0]) {
        return Some(ContShape {
            kind: ContKind::Err,
            arity: 1,
        });
    }
    None
}

pub fn cont_shape_of_ty(ty: &str) -> Option<ContShape> {
    cont_shape_of_arrows(&split_arrows(ty))
}

/// What a *value* of this type is, as far as the recogniser cares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TyKind {
    /// `State s u`.
    State,
    /// `ParseError`.
    ErrorValue,
    /// A full ok continuation (`a -> State s u -> ParseError -> r`).
    OkCont,
    /// A full error continuation (`ParseError -> r`).
    ErrCont,
    /// Anything else with a known type.
    Other,
}

pub fn ty_kind(ty: &str) -> TyKind {
    let a = split_arrows(ty);
    if a.len() == 1 {
        if is_state_ty(ty) {
            return TyKind::State;
        }
        if is_parse_error_ty(ty) {
            return TyKind::ErrorValue;
        }
        return TyKind::Other;
    }
    match cont_shape_of_arrows(&a) {
        Some(ContShape {
            kind: ContKind::Ok,
            arity: 3,
        }) => TyKind::OkCont,
        Some(ContShape {
            kind: ContKind::Err,
            arity: 1,
        }) => TyKind::ErrCont,
        _ => TyKind::Other,
    }
}

//------------------------------------------------------------------------------
// The four-slot template
//------------------------------------------------------------------------------

/// ParsecT's continuation slots, in the order the representation lists them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Slot {
    Cok,
    Cerr,
    Eok,
    Eerr,
}

pub const TEMPLATE: [ContKind; 4] = [ContKind::Ok, ContKind::Err, ContKind::Ok, ContKind::Err];

pub const SLOTS: [Slot; 4] = [Slot::Cok, Slot::Cerr, Slot::Eok, Slot::Eerr];

impl Slot {
    pub fn kind(self) -> ContKind {
        match self {
            Slot::Cok | Slot::Eok => ContKind::Ok,
            Slot::Cerr | Slot::Eerr => ContKind::Err,
        }
    }
    pub fn edge(self) -> EdgeKind {
        match self {
            Slot::Cok => EdgeKind::ConsumedOk,
            Slot::Cerr => EdgeKind::ConsumedErr,
            Slot::Eok => EdgeKind::EmptyOk,
            Slot::Eerr => EdgeKind::EmptyErr,
        }
    }
}

/// A proven set of slots a continuation may occupy. A singleton is an exact
/// role; anything larger is a proven finite set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SlotSet(pub u8);

impl Serialize for SlotSet {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_seq(self.iter())
    }
}

impl SlotSet {
    pub fn empty() -> SlotSet {
        SlotSet(0)
    }
    pub fn single(i: usize) -> SlotSet {
        SlotSet(1 << i)
    }
    pub fn insert(&mut self, i: usize) {
        self.0 |= 1 << i;
    }
    pub fn contains(self, i: usize) -> bool {
        self.0 & (1 << i) != 0
    }
    pub fn len(self) -> usize {
        self.0.count_ones() as usize
    }
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
    pub fn iter(self) -> impl Iterator<Item = Slot> {
        (0..4usize)
            .filter(move |i| self.contains(*i))
            .map(|i| SLOTS[i])
    }
    pub fn exact(self) -> Option<Slot> {
        if self.len() == 1 {
            self.iter().next()
        } else {
            None
        }
    }
    /// The ok/err distinction, when every candidate slot agrees.
    pub fn kind(self) -> Option<ContKind> {
        let mut k = None;
        for s in self.iter() {
            match k {
                None => k = Some(s.kind()),
                Some(x) if x != s.kind() => return None,
                _ => {}
            }
        }
        k
    }
}

/// A run element as seen at a binding site or a call site: a continuation of
/// a known kind, or a value whose type we cannot read (a computation, or a
/// lambda whose shape is not decidable) that may fill any slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RunItem {
    Cont(ContKind),
    Wild,
}

/// Every way `run` embeds, in order, into the four-slot template.
/// Enumerated over the 16 subsets of the template — no recursion.
fn embeddings(run: &[RunItem]) -> Vec<[usize; 4]> {
    let mut out = Vec::new();
    if run.is_empty() || run.len() > 4 {
        return out;
    }
    for mask in 0u8..16 {
        if (mask.count_ones() as usize) != run.len() {
            continue;
        }
        let mut idx = [0usize; 4];
        let mut n = 0;
        let mut ok = true;
        for (slot, tmpl) in TEMPLATE.iter().enumerate() {
            if mask & (1 << slot) == 0 {
                continue;
            }
            match run[n] {
                RunItem::Cont(k) if k != *tmpl => {
                    ok = false;
                    break;
                }
                _ => {}
            }
            idx[n] = slot;
            n += 1;
        }
        if ok {
            out.push(idx);
        }
    }
    out
}

/// Per-run-element slot sets, from every embedding that fits.
fn slot_sets(run: &[RunItem]) -> Option<Vec<SlotSet>> {
    let embs = embeddings(run);
    if embs.is_empty() {
        return None;
    }
    let mut sets = vec![SlotSet::empty(); run.len()];
    for e in &embs {
        for (i, set) in sets.iter_mut().enumerate() {
            set.insert(e[i]);
        }
    }
    Some(sets)
}

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum EdgeKind {
    ConsumedOk,
    ConsumedErr,
    EmptyOk,
    EmptyErr,
    CallParser,
}

/// Why a verdict holds: which rule fired, on which nodes, for which binder.
#[derive(Debug, Clone, Serialize)]
pub struct Provenance {
    pub source_nodes: Vec<ExprId>,
    /// The binder whose role this edge is evidence for. `None` for a
    /// [`EdgeKind::CallParser`] edge, which is a property of the call.
    pub binder: Option<BinderId>,
    pub binder_unique: String,
    /// Recognition rule id; see the `R*` constants in this module.
    pub rule: &'static str,
    pub proven: bool,
    /// The binder's occurrence name. A label for humans — never evidence.
    pub label: String,
}

/// What an edge records. Role **identity** and role **forwarding** are
/// different facts and are never conflated: handing a continuation to a
/// parser call in some slot chooses a target for one path, it does not
/// change what that continuation *is*. The inlined `<?>` passes its own
/// `cok` into the `eok` slot of the parser it labels; `cok` stays `cok`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum EdgeFact {
    /// A role binder is invoked here: control goes to the role it is, so
    /// source and destination are the same thing.
    Invoke,
    /// A role binder is passed, unchanged, into a continuation slot of a
    /// recognised parser call. `source_role` is what it is, `destination`
    /// is the slot it fills; the two may differ.
    Forward,
    /// The call is a parser being run. No single role binder is its
    /// subject, so it has no source role.
    RunParser,
}

#[derive(Debug, Clone, Serialize)]
pub struct ParserEdge {
    /// Which of the two facts this edge is.
    pub fact: EdgeFact,
    /// The intrinsic role of the binder this edge is about: what it *is*,
    /// never rewritten by anything that forwards it. Empty for
    /// [`EdgeFact::RunParser`].
    pub source_role: SlotSet,
    /// Where this edge sends control: the invoked role for
    /// [`EdgeFact::Invoke`], the filled slot for [`EdgeFact::Forward`].
    pub destination: SlotSet,
    /// `destination` as edge kinds; the first when it is a singleton.
    pub kind: EdgeKind,
    pub candidates: Vec<EdgeKind>,
    /// Spine root of the call.
    pub at: ExprId,
    pub region: usize,
    pub provenance: Provenance,
}

impl ParserEdge {
    pub fn exact(&self) -> bool {
        self.candidates.len() == 1
    }

    /// A forwarding edge whose destination slot is not the source's own
    /// role: the continuation is being reused for a different path.
    pub fn reroutes(&self) -> bool {
        self.fact == EdgeFact::Forward && self.source_role != self.destination
    }
}

/// A use that the rules do not accept, and therefore rejects the region.
#[derive(Debug, Clone, Serialize)]
pub struct Reject {
    /// Machine-readable reason; see the `REJ_*` constants.
    pub reason: &'static str,
    /// Extra detail (arities, slot names) for the reason.
    pub detail: String,
    pub at: ExprId,
    pub binder_unique: String,
    pub label: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct Evidence {
    pub rule: &'static str,
    pub node: ExprId,
    pub note: String,
}

/// A continuation parameter of a region, with the slots it may occupy.
#[derive(Debug, Clone, Serialize)]
pub struct ContParam {
    pub binder: BinderId,
    pub slots: SlotSet,
    pub arity: usize,
    pub label: String,
    pub ty: String,
}

/// A lambda whose parameters carry ParsecT's CPS representation.
#[derive(Debug, Clone, Serialize)]
pub struct ParserRegion {
    pub module: String,
    /// The lambda chain head.
    pub entry: ExprId,
    /// Every `Id` parameter of the chain, in order. A saturated call to
    /// this region lines its value arguments up with these one to one.
    pub params: Vec<BinderId>,
    /// `params[run.0..run.1]` are the continuation parameters.
    pub run: (usize, usize),
    /// When `state` is `None` because worker/wrapper unboxed `State s u`:
    /// the three parameters that carry its representation fields, in field
    /// order (`params[run.0-3..run.0]`).
    pub unboxed_state: Option<[BinderId; 3]>,
    /// The state parameter. `None` when worker/wrapper unboxed it or it is
    /// bound by an enclosing lambda.
    pub state: Option<BinderId>,
    pub cok: Option<BinderId>,
    pub cerr: Option<BinderId>,
    pub eok: Option<BinderId>,
    pub eerr: Option<BinderId>,
    /// Every continuation parameter, in argument order.
    pub conts: Vec<ContParam>,
    /// Trailing transformer parameters (`Environment m`, `SystemState`).
    pub extra: Vec<BinderId>,
    /// The wrapper region whose call resolved an ambiguous embedding
    /// ([`R9_WRAPPER_MAP`]), when one did.
    pub wrapper: Option<usize>,
    /// Let-bound continuation values inside the region, promoted by
    /// [`R8_DERIVED_CONT`] and proved by the same rules.
    pub derived: Vec<BinderId>,
    pub edges: Vec<ParserEdge>,
    pub rejects: Vec<Reject>,
    pub evidence: Vec<Evidence>,
    pub proven: bool,
}

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------
//
// Evidence hierarchy, strongest first. Every rule below says which level it
// rests on, and no rule rests on a weaker level than it claims.
//
//  1. **Lexical binder identity** — which binder an occurrence resolves to
//     ([`h2r_core_ir::Module::resolve`]). Exact, and the foundation of
//     everything else here.
//  2. **Structural function / application shape** — a lambda chain's
//     parameters, a spine's arguments, a case's alternatives. Exact.
//  3. **Worker/wrapper dataflow** — a wrapper is an eta-expansion of its
//     worker, so roles transfer across the call ([`R9_WRAPPER_MAP`]).
//     Exact given 1 and 2.
//  4. **GHC type compatibility** — the [`TyKind`] of a printed type:
//     `State s u`, `ParseError`, the two continuation shapes. Sound as a
//     classifier of these five cases.
//  5. **Alpha-normalised textual type comparison** ([`alpha_normalise`]) —
//     candidate generation and corroboration only. It can equate two
//     genuinely distinct type variables, so it is only ever used to
//     *refuse* a region, never as the support for a verdict.
//  6. **Binder names** — diagnostics only. Nothing in this module reads
//     one. (`State` in [`Analysis::index_state_fields`] is a data
//     constructor, which is part of the type's identity and is never
//     renamed, and the field types are checked anyway.)

/// A lambda chain's parameter types carry ParsecT's `State s u`, cok, cerr,
/// eok, eerr suffix; dropped (absent) continuations are allowed, so the run
/// is matched as a subsequence of the four-slot template.
/// Evidence: structural shape (2) over the binder types (4).
pub const R1_LAYOUT: &str = "R1-LAYOUT";
/// Every continuation of a region agrees on the state type and on the
/// result type, and the ok continuations really take `State s u` then
/// `ParseError`. Evidence: type compatibility (4) plus alpha-normalised
/// comparison (5) — a *filter* on [`R1_LAYOUT`], able only to refuse.
pub const R1_TYPE_AGREE: &str = "R1-TYPE-AGREE";
/// A call whose arguments are a `State s u` followed by a run of
/// continuation-shaped arguments embedding into the template, plus at most
/// two trailing transformer arguments: a parser being run.
/// Evidence: structural shape (2) over argument types (4).
pub const R2_PARSER_CALL: &str = "R2-PARSER-CALL";
/// The same, with the state argument absent because worker/wrapper unboxed
/// `State` into its representation fields. The absence has to be
/// *explained*; the three variants below say how, and one of them always
/// stands in for this id on an actual edge.
pub const R2_UNBOXED_STATE: &str = "R2-UNBOXED-STATE";
/// …the fields come from a `case … of State f0 f1 f2` at this call site.
pub const R2_UNBOXED_DESTRUCTURED: &str = "R2-UNBOXED-STATE/destructured";
/// …the callee is itself a recognised worker whose parameters are the fields.
pub const R2_UNBOXED_WORKER: &str = "R2-UNBOXED-STATE/worker-layout";
/// …the enclosing worker's own unboxed state is forwarded unchanged.
pub const R2_UNBOXED_FORWARDED: &str = "R2-UNBOXED-STATE/forwarded";
/// A continuation applied to exactly its arity: (value, state, error) for
/// an ok continuation, (error) for an error continuation. The head's own
/// type fixes what each argument slot means, and every argument whose type
/// is readable is checked against it
/// ([`Analysis::cont_call_arg_types`]).
/// Evidence: lexical identity (1) of the head, structural shape (2),
/// corroborated by type compatibility (4).
pub const R3_CONT_CALL: &str = "R3-CONT-CALL";
/// …applied to its arity plus the two trailing transformer arguments that
/// `ReaderT (Environment m) (StateT SystemState m)` erases to.
pub const R3_CONT_CALL_TRAILING: &str = "R3-CONT-CALL-TRAILING";
/// …applied to fewer arguments, the shortfall being supplied by
/// eta-reduction: the enclosing continuation position owes exactly the
/// missing arguments.
pub const R3_CONT_CALL_ETA: &str = "R3-CONT-CALL-ETA";
/// A continuation value returned into a continuation position that owes
/// exactly the arguments it still needs.
pub const R3_CONT_RETURNED: &str = "R3-CONT-RETURNED";
/// A continuation passed unchanged into a continuation slot of a recognised
/// parser call, of the same kind. The slot need not match its own role:
/// `try`-like combinators pass cok into the eok slot — which is why this is
/// a [`EdgeFact::Forward`] edge carrying both the source's own role and the
/// destination slot, and never rewrites the source's role. The ok/err kind
/// check is enforced on every propagation.
/// Evidence: lexical identity (1) of the forwarded binder, structural shape
/// (2) of the receiving call.
pub const R4_PROP_CONT: &str = "R4-PROP-CONT";
/// The state passed in the state slot of a continuation call.
pub const R5_STATE_IN_CONT_CALL: &str = "R5-STATE-IN-CONT-CALL";
/// The state passed in the state slot of a recognised parser call.
pub const R6_STATE_IN_PARSER_CALL: &str = "R6-STATE-IN-PARSER-CALL";
/// The state scrutinised (`case s of State …`).
pub const R7_STATE_SCRUTINISED: &str = "R7-STATE-SCRUTINISED";
/// A let-bound binder of continuation type inside a region: a derived
/// continuation, proved by the same use rules as a parameter.
/// Evidence: lexical identity (1) plus type compatibility (4); its role is
/// only ever the kind-restricted pair of slots, never a single slot.
pub const R8_DERIVED_CONT: &str = "R8-DERIVED-CONT";

/// An ambiguous embedding resolved from the worker/wrapper pair: the
/// wrapper's full-arity chain fixes the slots, and its body is one
/// saturated call forwarding them into the worker's parameters.
pub const R9_WRAPPER_MAP: &str = "R9-WRAPPER-MAP";

pub const REJ_STATE_APPLIED: &str = "state-applied";
pub const REJ_STATE_SLOT: &str = "state-in-non-state-slot";
pub const REJ_CONT_ARITY: &str = "cont-wrong-arity";
pub const REJ_CONT_ARG_TY: &str = "cont-argument-type-mismatch";
pub const REJ_CONT_SCRUTINISED: &str = "cont-scrutinised";
pub const REJ_CONT_SLOT: &str = "cont-in-non-cont-slot";
pub const REJ_CONT_KIND: &str = "cont-kind-mismatch";
pub const REJ_MIXED_KIND: &str = "role-kind-not-decided";
pub const REJ_UNRECOGNISED_CALL: &str = "arg-of-unrecognised-call";
pub const REJ_ESCAPE: &str = "escape";
pub const REJ_CON_FIELD: &str = "stored-in-constructor-field";

//------------------------------------------------------------------------------
// Analysis
//------------------------------------------------------------------------------

/// A lambda chain that binds continuation-typed parameters but does not
/// become a region. Recorded so that nothing disappears silently.
#[derive(Debug, Clone, Serialize)]
pub struct SkippedChain {
    pub entry: ExprId,
    /// `no-template-embedding`, `lone-continuation-without-state`,
    /// `type-disagreement`.
    pub reason: &'static str,
    pub detail: String,
}

/// An edge about to be recorded: the two facts, and where.
#[derive(Debug, Clone, Copy)]
struct EdgeSpec {
    fact: EdgeFact,
    source_role: SlotSet,
    destination: SlotSet,
    at: ExprId,
}

#[derive(Debug, Clone, Copy)]
struct RoleInfo {
    region: usize,
    /// `None` for the state parameter.
    cont: Option<(SlotSet, usize)>,
}

/// What a call site is, once its head is known.
#[derive(Debug, Clone)]
enum CallShape {
    /// Head is a (candidate) continuation: slot 0 is the value, 1 the
    /// state, 2 the error for an ok continuation; slot 0 the error for an
    /// error continuation.
    Cont {
        kind: ContKind,
        arity: usize,
        n: usize,
    },
    /// Head is anything else, but the argument list carries the template.
    Parser {
        state: Option<usize>,
        slots: Vec<(usize, SlotSet)>,
        rule: &'static str,
    },
}

pub struct Analysis<'m> {
    pub module: &'m Module,
    pub regions: Vec<ParserRegion>,
    /// Chains with continuation-typed parameters that did not form a region.
    pub skipped: Vec<SkippedChain>,
    /// Binding structure and scoped occurrence resolution, shared with the
    /// census so the two can never disagree about what a `Var` refers to.
    scope: Scope<'m>,
    role: HashMap<BinderId, RoleInfo>,
    /// The binder a region's lambda chain is bound to, inverted.
    region_of_binder: HashMap<BinderId, usize>,
    /// Binders that are representation fields of a scrutinised `State s u`:
    /// `binder -> (case node, alt, field index)`.
    state_fields: HashMap<BinderId, (ExprId, u32, usize)>,
    /// Lambda chain head -> region index.
    region_at: HashMap<ExprId, usize>,
    /// Spine root -> (region, edge) for every edge recorded at that root.
    edge_index: HashMap<ExprId, Vec<(usize, usize)>>,
}

impl<'m> Analysis<'m> {
    pub fn of_module(m: &'m Module) -> Analysis<'m> {
        let scope = Scope::new(m);
        let mut a = Analysis {
            module: m,
            regions: Vec::new(),
            skipped: Vec::new(),
            scope,
            role: HashMap::new(),
            region_of_binder: HashMap::new(),
            state_fields: HashMap::new(),
            region_at: HashMap::new(),
            edge_index: HashMap::new(),
        };
        a.index_state_fields();
        a.find_regions();
        a.wrapper_map();
        a.promote_derived();
        a.prove();
        a.find_parser_calls();
        a.index_edges();
        a
    }

    /// Every recognised parser call inside a region becomes a `CallParser`
    /// edge of the innermost region that contains it. One pass over the
    /// spine roots of the module.
    fn find_parser_calls(&mut self) {
        let m = self.module;
        let mut found: Vec<(usize, ExprId, &'static str)> = Vec::new();
        for id in 0..m.exprs.len() as ExprId {
            if !matches!(m.expr(id), Expr::App { .. }) || self.module.spine_root(id) != id {
                continue;
            }
            let Some(CallShape::Parser { rule, .. }) = self.call_shape(id) else {
                continue;
            };
            let Some(ri) = self.enclosing_region(id) else {
                continue;
            };
            found.push((ri, id, rule));
        }
        for (ri, at, rule) in found {
            self.regions[ri].edges.push(ParserEdge {
                fact: EdgeFact::RunParser,
                source_role: SlotSet::empty(),
                destination: SlotSet::empty(),
                kind: EdgeKind::CallParser,
                candidates: vec![EdgeKind::CallParser],
                at,
                region: ri,
                provenance: Provenance {
                    source_nodes: vec![at],
                    binder: None,
                    binder_unique: String::new(),
                    rule,
                    proven: true,
                    label: String::new(),
                },
            });
        }
    }

    fn index_edges(&mut self) {
        let mut idx: HashMap<ExprId, Vec<(usize, usize)>> = HashMap::new();
        for (ri, r) in self.regions.iter().enumerate() {
            for (ei, e) in r.edges.iter().enumerate() {
                idx.entry(e.at).or_default().push((ri, ei));
            }
        }
        self.edge_index = idx;
    }

    pub fn binder(&self, b: BinderId) -> &'m Binder {
        self.module.binder(b)
    }

    //--------------------------------------------------------------------------
    // Shape helpers
    //--------------------------------------------------------------------------

    /// The Id parameters of the lambda chain at `id`, and its body.
    fn chain(&self, id: ExprId) -> (Vec<BinderId>, ExprId) {
        let m = self.module;
        let mut params = Vec::new();
        let mut cur = id;
        while let Expr::Lam { binder, body } = m.expr(cur) {
            if m.binder(*binder).kind == BinderKind::Id {
                params.push(*binder);
            }
            cur = *body;
        }
        (params, cur)
    }

    fn is_chain_head(&self, id: ExprId) -> bool {
        let m = self.module;
        match m.parent[id as usize] {
            Some(p) => {
                !(m.edge[id as usize] == Edge::LamBody && matches!(m.expr(p), Expr::Lam { .. }))
            }
            None => true,
        }
    }

    /// The type of an expression, when it can be read off a binder.
    fn expr_ty(&self, e: ExprId) -> Option<&'m str> {
        let m = self.module;
        let i = m.strip(e);
        match m.expr(i) {
            Expr::Var { .. } => self.scope.resolve(i).map(|b| self.binder(b).ty.as_str()),
            _ => None,
        }
    }

    /// What a value in an argument position is, as far as the template
    /// matcher cares. A lambda is read from its parameter types, falling
    /// back to its parameters plus the type of its body when the body is a
    /// variable (GHC eta-reduces continuations down to `\x -> k`).
    fn arg_item(&self, e: ExprId) -> (Option<TyKind>, RunItem) {
        let m = self.module;
        let i = m.strip(e);
        let kind = match m.expr(i) {
            Expr::Var { .. } => self.scope.resolve(i).map(|b| ty_kind(&self.binder(b).ty)),
            Expr::Lam { .. } => {
                let (params, body) = self.chain(i);
                let tys: Vec<&str> = params.iter().map(|b| self.binder(*b).ty.as_str()).collect();
                if tys.len() >= 3 && is_state_ty(tys[1]) && is_parse_error_ty(tys[2]) {
                    Some(TyKind::OkCont)
                } else if !tys.is_empty() && is_parse_error_ty(tys[0]) {
                    Some(TyKind::ErrCont)
                } else {
                    // GHC eta-reduces continuations down to `\x -> k`; the
                    // lambda's type is then its parameters plus the type of
                    // the variable it returns.
                    self.expr_ty(body).map(|bt| {
                        let mut arrows = tys.clone();
                        arrows.extend(split_arrows(bt));
                        match cont_shape_of_arrows(&arrows) {
                            Some(ContShape {
                                kind: ContKind::Ok,
                                arity: 3,
                            }) => TyKind::OkCont,
                            Some(ContShape {
                                kind: ContKind::Err,
                                arity: 1,
                            }) => TyKind::ErrCont,
                            _ => TyKind::Other,
                        }
                    })
                }
            }
            _ => None,
        };
        let item = match kind {
            Some(TyKind::OkCont) => RunItem::Cont(ContKind::Ok),
            Some(TyKind::ErrCont) => RunItem::Cont(ContKind::Err),
            // A value of known, non-continuation type can never fill a slot;
            // only a value whose type cannot be read is a wildcard.
            Some(_) => RunItem::Wild,
            None => RunItem::Wild,
        };
        (kind, item)
    }

    /// The binder a lambda chain (or any expression) is bound to, looking
    /// through the casts the simplifier leaves between a binding and its
    /// right-hand side. Evidence level: lexical binder identity.
    fn bound_to(&self, id: ExprId) -> Option<BinderId> {
        let m = self.module;
        let mut cur = id;
        loop {
            let p = m.parent[cur as usize];
            match m.edge[cur as usize] {
                Edge::Cast | Edge::Tick => cur = p?,
                Edge::LetRhs { pair } => {
                    let Expr::Let { bind, .. } = m.expr(p?) else {
                        return None;
                    };
                    return Some(bind.pairs[pair as usize].binder);
                }
                Edge::Top { pair } => {
                    return m
                        .top
                        .iter()
                        .flat_map(|b| b.pairs.iter())
                        .nth(pair as usize)
                        .map(|x| x.binder);
                }
                _ => return None,
            }
        }
    }

    /// Index the binders that carry the representation fields of a
    /// destructured `State s u`.
    ///
    /// Evidence level: structural shape plus GHC type compatibility. The
    /// alternative's constructor is `State` — a *data constructor* name,
    /// which is part of the type's identity and is not renamed by the
    /// simplifier, unlike a binder name — its field count is Parsec's
    /// three, its middle field is a `SourcePos`, and the scrutinee is
    /// something of `State` type.
    fn index_state_fields(&mut self) {
        let m = self.module;
        let mut found = Vec::new();
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Case { scrut, alts, .. } = m.expr(id) else {
                continue;
            };
            // The scrutinee is something of `State s u` type.
            if !self.expr_ty(*scrut).is_some_and(is_state_ty) {
                continue;
            }
            for (ai, alt) in alts.iter().enumerate() {
                let AltCon::DataAlt { occ, .. } = &alt.con else {
                    continue;
                };
                // Three fields, the middle one a `SourcePos`: Parsec's
                // `State`. The constructor's name corroborates it.
                if alt.binders.len() != 3
                    || strip_parens(&m.binder(alt.binders[1]).ty) != "SourcePos"
                    || occ != "State"
                {
                    continue;
                }
                for (fi, b) in alt.binders.iter().enumerate() {
                    found.push((*b, (id, ai as u32, fi)));
                }
            }
        }
        self.state_fields = found.into_iter().collect();
    }

    /// The three parameters before a continuation run that carry an unboxed
    /// `State s u`: any input type, a `SourcePos`, any user-state type.
    /// Evidence level: GHC type compatibility on the binder types.
    fn unboxed_state_params(&self, params: &[BinderId], start: usize) -> Option<[BinderId; 3]> {
        if start < 3 {
            return None;
        }
        let f = [params[start - 3], params[start - 2], params[start - 1]];
        if strip_parens(&self.binder(f[1]).ty) != "SourcePos" {
            return None;
        }
        Some(f)
    }

    //--------------------------------------------------------------------------
    // R1: region discovery
    //--------------------------------------------------------------------------

    fn find_regions(&mut self) {
        let m = self.module;
        for id in 0..m.exprs.len() as ExprId {
            if !matches!(m.expr(id), Expr::Lam { .. }) || !self.is_chain_head(id) {
                continue;
            }
            let (params, _) = self.chain(id);
            if params.is_empty() {
                continue;
            }
            let kinds: Vec<TyKind> = params
                .iter()
                .map(|b| ty_kind(&self.binder(*b).ty))
                .collect();
            // The last maximal run of continuation-typed parameters that
            // embeds into the template.
            let mut best: Option<(Option<usize>, usize, usize, Vec<SlotSet>)> = None;
            let mut i = 0usize;
            while i < kinds.len() {
                if !matches!(kinds[i], TyKind::OkCont | TyKind::ErrCont) {
                    i += 1;
                    continue;
                }
                let start = i;
                let mut run = Vec::new();
                while i < kinds.len() && matches!(kinds[i], TyKind::OkCont | TyKind::ErrCont) {
                    run.push(RunItem::Cont(match kinds[i] {
                        TyKind::OkCont => ContKind::Ok,
                        _ => ContKind::Err,
                    }));
                    i += 1;
                }
                if let Some(sets) = slot_sets(&run) {
                    let state = if start > 0 && kinds[start - 1] == TyKind::State {
                        Some(start - 1)
                    } else {
                        None
                    };
                    // Without a state parameter to anchor it, a single
                    // continuation is too weak to call a region.
                    if state.is_some() || run.len() >= 2 {
                        best = Some((state, start, i, sets));
                    }
                }
            }
            let Some((state_idx, start, end, sets)) = best else {
                if kinds
                    .iter()
                    .any(|k| matches!(k, TyKind::OkCont | TyKind::ErrCont))
                {
                    let lone = kinds
                        .iter()
                        .filter(|k| matches!(k, TyKind::OkCont | TyKind::ErrCont))
                        .count()
                        == 1;
                    self.skipped.push(SkippedChain {
                        entry: id,
                        reason: if lone {
                            "lone-continuation-without-state"
                        } else {
                            "no-template-embedding"
                        },
                        detail: format!("{kinds:?}"),
                    });
                }
                continue;
            };
            // R1-TYPE-AGREE.
            let state_ty = state_idx.map(|si| self.binder(params[si]).ty.as_str());
            let mut result_tys: Vec<String> = Vec::new();
            let mut agree = true;
            for b in &params[start..end] {
                let ty = self.binder(*b).ty.as_str();
                let a = split_arrows(ty);
                match ty_kind(ty) {
                    TyKind::OkCont => {
                        if !is_parse_error_ty(a[2])
                            || state_ty.is_some_and(|s| {
                                alpha_normalise(strip_parens(a[1]))
                                    != alpha_normalise(strip_parens(s))
                            })
                        {
                            agree = false;
                        }
                        result_tys.push(alpha_normalise(&a[3..].join("->")));
                    }
                    _ => result_tys.push(alpha_normalise(&a[1..].join("->"))),
                }
            }
            result_tys.sort();
            result_tys.dedup();
            if !agree || result_tys.len() != 1 {
                self.skipped.push(SkippedChain {
                    entry: id,
                    reason: "type-disagreement",
                    detail: format!(
                        "state {state_ty:?}, {} distinct result type(s): {result_tys:?}",
                        result_tys.len()
                    ),
                });
                continue;
            }

            let ri = self.regions.len();
            let mut conts = Vec::new();
            let mut slot_binder = [None; 4];
            for (k, b) in params[start..end].iter().enumerate() {
                let bd = self.binder(*b);
                let arity = cont_shape_of_ty(&bd.ty).map(|c| c.arity).unwrap_or(0);
                if let Some(s) = sets[k].exact() {
                    slot_binder[s as usize] = Some(*b);
                }
                conts.push(ContParam {
                    binder: *b,
                    slots: sets[k],
                    arity,
                    label: bd.occ.clone(),
                    ty: bd.ty.clone(),
                });
                self.role.insert(
                    *b,
                    RoleInfo {
                        region: ri,
                        cont: Some((sets[k], arity)),
                    },
                );
            }
            if let Some(si) = state_idx {
                self.role.insert(
                    params[si],
                    RoleInfo {
                        region: ri,
                        cont: None,
                    },
                );
            }
            let mut evidence = vec![Evidence {
                rule: R1_LAYOUT,
                node: id,
                note: format!(
                    "parameters [{}] carry {}{} continuation slot(s) {}",
                    params
                        .iter()
                        .map(|b| format!("{}::{}", self.binder(*b).occ, self.binder(*b).ty))
                        .collect::<Vec<_>>()
                        .join(", "),
                    if state_idx.is_some() { "state + " } else { "" },
                    end - start,
                    conts
                        .iter()
                        .map(|c| format!("{:?}", c.slots.iter().collect::<Vec<_>>()))
                        .collect::<Vec<_>>()
                        .join(" ")
                ),
            }];
            evidence.push(Evidence {
                rule: R1_TYPE_AGREE,
                node: id,
                note: format!(
                    "one result type {:?}, state type {:?}",
                    result_tys.first(),
                    state_ty
                ),
            });
            self.region_at.insert(id, ri);
            if let Some(b) = self.bound_to(id) {
                self.region_of_binder.insert(b, ri);
            }
            let unboxed_state = if state_idx.is_none() {
                self.unboxed_state_params(&params, start)
            } else {
                None
            };
            self.regions.push(ParserRegion {
                module: m.name.clone(),
                entry: id,
                params: params.clone(),
                run: (start, end),
                unboxed_state,
                state: state_idx.map(|si| params[si]),
                cok: slot_binder[0],
                cerr: slot_binder[1],
                eok: slot_binder[2],
                eerr: slot_binder[3],
                conts,
                extra: params[end..].to_vec(),
                wrapper: None,
                derived: Vec::new(),
                edges: Vec::new(),
                rejects: Vec::new(),
                evidence,
                proven: false,
            });
        }
    }

    //--------------------------------------------------------------------------
    // R9: worker/wrapper role transfer
    //--------------------------------------------------------------------------

    /// R9-WRAPPER-MAP. A region whose continuation run embeds into the
    /// four-slot template in more than one way has a proven *finite* role
    /// set, not an exact role. When that region is the **worker** of a
    /// worker/wrapper pair that is also in the dump, the ambiguity is
    /// resolvable: a wrapper is an eta-expansion of its worker with the
    /// absent arguments dropped, so the wrapper's slot for each argument it
    /// forwards *is* the worker's role for the parameter that receives it.
    ///
    /// Evidence level: structural application shape (the wrapper's body is
    /// exactly one saturated call to the worker) on top of lexical binder
    /// identity (each forwarded argument is one of the wrapper's own
    /// parameters), and the wrapper's own roles come from `R1-LAYOUT` on a
    /// chain that carries all four slots and is therefore unambiguous.
    /// Nothing here reads a name, and the mapping is only accepted if it is
    /// one of the embeddings the worker's own layout already allowed.
    ///
    /// This is role *identity* transfer, not role forwarding: it is sound
    /// only because the wrapper does nothing but pass its parameters on. A
    /// combinator that forwards a continuation into a differently-named
    /// slot (`<?>` passing `cok` into the `eok` slot) is a
    /// [`R4_PROP_CONT`] edge and never changes anybody's role.
    fn wrapper_map(&mut self) {
        let m = self.module;
        let mut resolved: Vec<(usize, Vec<Slot>, ExprId, usize)> = Vec::new();
        for ki in 0..self.regions.len() {
            let k = &self.regions[ki];
            if !k.conts.iter().any(|c| c.slots.len() > 1) {
                continue;
            }
            let Some(kb) = self.bound_to(k.entry) else {
                continue;
            };
            let mut agreed: Option<Vec<Slot>> = None;
            let mut witness = None;
            let mut conflict = false;
            for &u in m.occurrences(kb) {
                let Some((map, wi)) = self.wrapper_call_map(ki, u) else {
                    continue;
                };
                match &agreed {
                    None => {
                        agreed = Some(map);
                        witness = Some((u, wi));
                    }
                    Some(prev) if *prev == map => {}
                    Some(_) => conflict = true,
                }
            }
            if conflict {
                continue;
            }
            if let (Some(map), Some((at, wi))) = (agreed, witness) {
                resolved.push((ki, map, at, wi));
            }
        }
        for (ki, map, at, wi) in resolved {
            let (start, _) = self.regions[ki].run;
            let mut slot_binder = [None; 4];
            for (j, slot) in map.iter().enumerate() {
                let c = &mut self.regions[ki].conts[j];
                c.slots = SlotSet::single(*slot as usize);
                slot_binder[*slot as usize] = Some(c.binder);
                let arity = c.arity;
                let binder = c.binder;
                self.role.insert(
                    binder,
                    RoleInfo {
                        region: ki,
                        cont: Some((SlotSet::single(*slot as usize), arity)),
                    },
                );
            }
            let r = &mut self.regions[ki];
            r.cok = slot_binder[0].or(r.cok);
            r.cerr = slot_binder[1].or(r.cerr);
            r.eok = slot_binder[2].or(r.eok);
            r.eerr = slot_binder[3].or(r.eerr);
            r.wrapper = Some(wi);
            r.evidence.push(Evidence {
                rule: R9_WRAPPER_MAP,
                node: at,
                note: format!(
                    "wrapper region {wi} forwards its own slots {:?} into parameters {}..{}                      of this worker at node {at}",
                    map,
                    start,
                    start + map.len()
                ),
            });
        }
    }

    /// If the occurrence `u` is a wrapper's whole-body call to region `ki`,
    /// the slot each of `ki`'s continuation parameters gets from it, and
    /// the wrapper's region index.
    fn wrapper_call_map(&self, ki: usize, u: ExprId) -> Option<(Vec<Slot>, usize)> {
        let m = self.module;
        let k = &self.regions[ki];
        let root = m.spine_root(u);
        let (head, args) = m.spine(root);
        // The occurrence has to be the head of the call, not an argument.
        if m.strip(head) != u {
            return None;
        }
        let wi = self.enclosing_region(root)?;
        let w = &self.regions[wi];
        // The wrapper's own chain must carry all four slots (so its own
        // embedding is unambiguous) and a state.
        let (wcok, wcerr, weok, weerr) = (w.cok?, w.cerr?, w.eok?, w.eerr?);
        let wstate = w.state?;
        // Its body must be exactly this call: a wrapper does nothing else.
        let mut body = w.entry;
        while let Expr::Lam { body: b, .. } = m.expr(body) {
            body = *b;
        }
        if m.strip(body) != root {
            return None;
        }
        // The call must be saturated: one value argument per parameter.
        let vargs = value_args(&self.scope, &args);
        if vargs.len() != k.params.len() {
            return None;
        }
        // The worker's state, if it kept one, comes from the wrapper's.
        let (start, end) = k.run;
        if let Some(_ks) = k.state {
            let si = k.params.iter().position(|b| Some(*b) == k.state)?;
            if m.resolve(m.strip(vargs[si])) != Some(wstate) {
                return None;
            }
        }
        let slot_of = |b: BinderId| -> Option<Slot> {
            if b == wcok {
                Some(Slot::Cok)
            } else if b == wcerr {
                Some(Slot::Cerr)
            } else if b == weok {
                Some(Slot::Eok)
            } else if b == weerr {
                Some(Slot::Eerr)
            } else {
                None
            }
        };
        let mut map = Vec::new();
        let mut last: Option<usize> = None;
        for (j, arg) in vargs.iter().enumerate().take(end).skip(start) {
            let b = m.resolve(m.strip(*arg))?;
            let slot = slot_of(b)?;
            // Order-preserving, injective, and consistent with the
            // embeddings this worker's own layout already allowed.
            if last.is_some_and(|l| l >= slot as usize) {
                return None;
            }
            if !k.conts[j - start].slots.contains(slot as usize) {
                return None;
            }
            last = Some(slot as usize);
            map.push(slot);
        }
        if map.len() != end - start {
            return None;
        }
        Some((map, wi))
    }

    /// R8: a let-bound value of continuation type inside a region is a
    /// derived continuation and has to satisfy the same use rules.
    fn promote_derived(&mut self) {
        let m = self.module;
        let mut promote: Vec<(BinderId, usize, ContShape)> = Vec::new();
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Let { bind, .. } = m.expr(id) else {
                continue;
            };
            let Some(ri) = self.enclosing_region(id) else {
                continue;
            };
            for p in &bind.pairs {
                if self.role.contains_key(&p.binder) {
                    continue;
                }
                let Some(shape) = cont_shape_of_ty(&m.binder(p.binder).ty) else {
                    continue;
                };
                promote.push((p.binder, ri, shape));
            }
        }
        for (b, ri, shape) in promote {
            let slots = match shape.kind {
                ContKind::Ok => SlotSet(0b0101),
                ContKind::Err => SlotSet(0b1010),
            };
            self.role.insert(
                b,
                RoleInfo {
                    region: ri,
                    cont: Some((slots, shape.arity)),
                },
            );
            let r = &mut self.regions[ri];
            r.derived.push(b);
            r.evidence.push(Evidence {
                rule: R8_DERIVED_CONT,
                node: r.entry,
                note: format!(
                    "let-bound {} :: {} is a {:?} continuation owing {} argument(s)",
                    m.binder(b).occ,
                    m.binder(b).ty,
                    shape.kind,
                    shape.arity
                ),
            });
        }
    }

    pub fn enclosing_region_of(&self, id: ExprId) -> Option<usize> {
        self.enclosing_region(id)
    }

    fn enclosing_region(&self, id: ExprId) -> Option<usize> {
        if let Some(ri) = self.region_at.get(&id) {
            return Some(*ri);
        }
        self.module
            .ancestors(id)
            .find_map(|a| self.region_at.get(&a).copied())
    }

    //--------------------------------------------------------------------------
    // R2: call recognition
    //--------------------------------------------------------------------------

    /// Narrow a parser call's slots with the callee's own proven roles.
    ///
    /// The slots a call's argument run gets from [`slot_sets`] are derived
    /// from the argument *types*, which cannot always tell the consumed
    /// pair from the empty pair. When the callee is a region in this module
    /// whose parameters already have exact roles — because its chain
    /// carries all four slots, or because [`R9_WRAPPER_MAP`] resolved it —
    /// the callee is the authority on what its own parameters are.
    /// Evidence level: worker/wrapper dataflow over lexical identity. A
    /// narrowing is only taken when it agrees with the embedding.
    fn narrow_by_callee(&self, head: ExprId, vargs: &[ExprId], slots: &mut [(usize, SlotSet)]) {
        let Some(b) = self.module.resolve(head) else {
            return;
        };
        let Some(&ri) = self.region_of_binder.get(&b) else {
            return;
        };
        let r = &self.regions[ri];
        if r.params.len() != vargs.len() {
            return;
        }
        for (i, set) in slots.iter_mut() {
            let Some(c) = r.conts.get(i.wrapping_sub(r.run.0)) else {
                continue;
            };
            if r.params.get(*i) != Some(&c.binder) {
                continue;
            }
            if let Some(slot) = c.slots.exact()
                && set.contains(slot as usize)
            {
                *set = SlotSet::single(slot as usize);
            }
        }
    }

    /// Classify the call rooted at `root`.
    fn call_shape(&self, root: ExprId) -> Option<CallShape> {
        let m = self.module;
        let (head, args) = m.spine(root);
        let vargs = value_args(&self.scope, &args);
        // A call to a (candidate) continuation.
        let hi = m.strip(head);
        if matches!(m.expr(hi), Expr::Var { .. })
            && let Some(b) = self.scope.resolve(hi)
            && let Some(info) = self.role.get(&b)
            && let Some((slots, arity)) = info.cont
            && let Some(kind) = slots.kind()
        {
            return Some(CallShape::Cont {
                kind,
                arity,
                n: vargs.len(),
            });
        }
        // A data constructor is never a parser: storing a continuation in a
        // field is an escape, however Parsec-shaped the field types look.
        if self
            .scope
            .head_sig(hi)
            .is_some_and(|sig| sig.data_con.is_some())
        {
            return None;
        }
        // A parser being run.
        let items: Vec<(Option<TyKind>, RunItem)> =
            vargs.iter().map(|a| self.arg_item(*a)).collect();
        let is_cont = |i: usize| matches!(items[i].0, Some(TyKind::OkCont) | Some(TyKind::ErrCont));
        let mut best: Option<CallShape> = None;
        let mut i = 0usize;
        while i < items.len() {
            if items[i].0 != Some(TyKind::State) {
                i += 1;
                continue;
            }
            let start = i + 1;
            let mut end = start;
            while end < items.len() && (is_cont(end) || items[end].1 == RunItem::Wild) {
                end += 1;
            }
            // A trailing wildcard is not evidence of a slot.
            while end > start && !is_cont(end - 1) {
                end -= 1;
            }
            let run: Vec<RunItem> = (start..end).map(|k| items[k].1).collect();
            if !run.is_empty()
                && run.iter().any(|r| matches!(r, RunItem::Cont(_)))
                && items.len() - end <= 2
                && let Some(sets) = slot_sets(&run)
            {
                let mut slots: Vec<(usize, SlotSet)> =
                    (start..end).map(|k| (k, sets[k - start])).collect();
                self.narrow_by_callee(hi, &vargs, &mut slots);
                best = Some(CallShape::Parser {
                    state: Some(i),
                    slots,
                    rule: R2_PARSER_CALL,
                });
            }
            i = end.max(i + 1);
        }
        if best.is_some() {
            return best;
        }
        // Worker/wrapper unboxed the state into its representation fields.
        // A run of continuation-shaped arguments is *not* on its own
        // evidence of a parser call — an ordinary higher-order function can
        // take two of them — so the missing state has to be explained.
        let mut end = items.len();
        while end > 0 {
            let mut start = end;
            while start > 0 && is_cont(start - 1) {
                start -= 1;
            }
            let run: Vec<RunItem> = (start..end).map(|k| items[k].1).collect();
            if run.len() >= 2
                && items.len() - end <= 2
                && let Some(rule) = self.unboxed_state_explained(root, hi, &vargs, start)
                && let Some(sets) = slot_sets(&run)
            {
                let mut slots: Vec<(usize, SlotSet)> =
                    (start..end).map(|k| (k, sets[k - start])).collect();
                self.narrow_by_callee(hi, &vargs, &mut slots);
                return Some(CallShape::Parser {
                    state: None,
                    slots,
                    rule,
                });
            }
            end -= 1;
        }
        None
    }

    /// [`R2_UNBOXED_STATE`]'s side condition: the absent `State s u`
    /// argument is *explained*, not merely missing. One of
    ///
    /// * **(a)** the three arguments standing where the state would be are
    ///   the representation fields, in field order, of one and the same
    ///   `case … of State f0 f1 f2` alternative — the state was
    ///   destructured at this very call, by code that is itself inside a
    ///   recognised region (evidence: lexical binder identity, then
    ///   structural shape); or
    /// * **(b)** the callee is a local worker that is itself a recognised
    ///   region whose own parameter list is (state fields, continuation
    ///   run) in exactly this order, and the call saturates it (evidence:
    ///   lexical binder identity, then the callee's own `R1-LAYOUT`); or
    /// * **(c)** the three arguments are the state-field parameters of the
    ///   enclosing region, which is itself a worker whose `State` was
    ///   unboxed — the provenance is the same one level up (evidence:
    ///   lexical binder identity, then the enclosing region's `R1-LAYOUT`).
    ///
    /// Without one of these the call is not recognised as a parser call at
    /// all, and every continuation handed to it rejects its region.
    fn unboxed_state_explained(
        &self,
        root: ExprId,
        head: ExprId,
        vargs: &[ExprId],
        start: usize,
    ) -> Option<&'static str> {
        let m = self.module;
        // (a) destructured right here.
        if start >= 3 {
            let f: Vec<Option<(ExprId, u32, usize)>> = (start - 3..start)
                .map(|i| {
                    m.resolve(m.strip(vargs[i]))
                        .and_then(|b| self.state_fields.get(&b).copied())
                })
                .collect();
            if let [Some(a), Some(b), Some(c)] = f[..]
                && (a.0, a.1, a.2) == (b.0, b.1, 0)
                && (b.0, b.1, b.2) == (c.0, c.1, 1)
                && c.2 == 2
            {
                return Some(R2_UNBOXED_DESTRUCTURED);
            }
        }
        // (b) the callee's own layout says those parameters are the fields.
        if let Some(b) = m.resolve(head)
            && let Some(&wi) = self.region_of_binder.get(&b)
        {
            let w = &self.regions[wi];
            if w.unboxed_state.is_some() && w.run.0 == start && w.params.len() == vargs.len() {
                return Some(R2_UNBOXED_WORKER);
            }
        }
        // (c) forwarded from the enclosing worker's own unboxed state.
        if start >= 3
            && let Some(ei) = self.enclosing_region(root)
            && let Some(f) = self.regions[ei].unboxed_state
        {
            let got: Vec<Option<BinderId>> = (start - 3..start)
                .map(|i| m.resolve(m.strip(vargs[i])))
                .collect();
            if got == [Some(f[0]), Some(f[1]), Some(f[2])] {
                return Some(R2_UNBOXED_FORWARDED);
            }
        }
        None
    }

    /// What continuation does this position want, if any?
    fn cont_position(&self, node: ExprId) -> Option<ContShape> {
        let m = self.module;
        let mut cur = node;
        let mut parent = m.parent[cur as usize];
        while let Some(p) = parent {
            if matches!(m.edge[cur as usize], Edge::Cast | Edge::Tick) {
                cur = p;
                parent = m.parent[cur as usize];
            } else {
                break;
            }
        }
        let p = parent?;
        match m.edge[cur as usize] {
            Edge::AppArg => {
                let root = self.module.spine_root(p);
                let (_, args) = m.spine(root);
                let vargs = value_args(&self.scope, &args);
                let idx = vargs.iter().position(|a| *a == cur)?;
                match self.call_shape(root)? {
                    CallShape::Parser { slots, .. } => {
                        let set = slots.iter().find(|(i, _)| *i == idx)?.1;
                        let kind = set.kind()?;
                        Some(ContShape {
                            kind,
                            arity: if kind == ContKind::Ok { 3 } else { 1 },
                        })
                    }
                    CallShape::Cont { .. } => None,
                }
            }
            Edge::LetRhs { pair } => {
                let Expr::Let { bind, .. } = m.expr(p) else {
                    return None;
                };
                cont_shape_of_ty(&m.binder(bind.pairs[pair as usize].binder).ty)
            }
            _ => None,
        }
    }

    /// How many arguments the enclosing continuation position still owes at
    /// `node`, after the lambdas between here and there have taken theirs.
    fn owed_at(&self, node: ExprId) -> Option<usize> {
        let m = self.module;
        let mut cur = node;
        let mut params = 0usize;
        loop {
            let p = m.parent[cur as usize]?;
            if m.edge[cur as usize] == Edge::LamBody
                && let Expr::Lam { binder, .. } = m.expr(p)
            {
                if m.binder(*binder).kind == BinderKind::Id {
                    params += 1;
                }
                cur = p;
                continue;
            }
            if let Some(shape) = self.cont_position(cur) {
                return shape.arity.checked_sub(params);
            }
            match m.edge[cur as usize] {
                Edge::Cast | Edge::Tick | Edge::LetBody | Edge::CaseAlt { .. } => cur = p,
                _ => return None,
            }
        }
    }

    /// Do the arguments of a continuation call agree with the continuation
    /// type's own argument types?
    ///
    /// [`R3_CONT_CALL`] is otherwise an arity check: the head's type fixes
    /// what each slot *means* — an ok continuation takes a value, then a
    /// `State s u`, then a `ParseError` — so applying it to exactly its
    /// arity already pins the arguments down. This checks the claim wherever
    /// the dump lets it be checked: every argument whose own type is
    /// readable must have the same [`TyKind`] as the corresponding argument
    /// of the head's type. Evidence level: GHC type compatibility, used
    /// here to *refute*, never as the sole support for a verdict.
    fn cont_call_arg_types(&self, head_ty: &str, vargs: &[ExprId], arity: usize) -> Option<String> {
        let parts = split_arrows(head_ty);
        for (j, arg) in vargs.iter().enumerate().take(arity.min(parts.len())) {
            let Some(actual) = self.expr_ty(*arg) else {
                continue;
            };
            let (want, got) = (ty_kind(parts[j]), ty_kind(actual));
            if want != got {
                return Some(format!(
                    "argument {j} is {got:?} ({actual}), the continuation type wants                      {want:?} ({})",
                    parts[j]
                ));
            }
        }
        None
    }

    //--------------------------------------------------------------------------
    // The proof
    //--------------------------------------------------------------------------

    fn prove(&mut self) {
        let m = self.module;
        let roles: Vec<(BinderId, RoleInfo)> = self.role.iter().map(|(k, v)| (*k, *v)).collect();
        for (b, info) in roles {
            let uses: Vec<ExprId> = self.scope.occurrences(b).to_vec();
            for use_at in uses {
                let (kind, prov) = self.classify_use(b, info, use_at);
                let r = &mut self.regions[info.region];
                match kind {
                    Ok(edge) => match edge {
                        Some(spec) => r.edges.push(ParserEdge {
                            fact: spec.fact,
                            source_role: spec.source_role,
                            destination: spec.destination,
                            kind: spec.destination.iter().next().expect("non-empty").edge(),
                            candidates: spec.destination.iter().map(|s| s.edge()).collect(),
                            at: spec.at,
                            region: info.region,
                            provenance: prov,
                        }),
                        None => r.evidence.push(Evidence {
                            rule: prov.rule,
                            node: prov.source_nodes[0],
                            note: format!("{} ok", prov.label),
                        }),
                    },
                    Err((reason, detail)) => r.rejects.push(Reject {
                        reason,
                        detail,
                        at: prov.source_nodes[0],
                        binder_unique: prov.binder_unique,
                        label: prov.label,
                    }),
                }
            }
        }
        for r in &mut self.regions {
            r.proven = r.rejects.is_empty();
        }
        let _ = m;
    }

    #[allow(clippy::type_complexity)]
    fn classify_use(
        &self,
        b: BinderId,
        info: RoleInfo,
        use_at: ExprId,
    ) -> (Result<Option<EdgeSpec>, (&'static str, String)>, Provenance) {
        let m = self.module;
        let bd = self.binder(b);
        let mut prov = Provenance {
            source_nodes: vec![use_at],
            binder: Some(b),
            binder_unique: bd.unique.clone(),
            rule: R1_LAYOUT,
            proven: true,
            label: bd.occ.clone(),
        };
        // Look through casts on the way up.
        let mut cur = use_at;
        while let Some(p) = m.parent[cur as usize] {
            if matches!(m.edge[cur as usize], Edge::Cast | Edge::Tick) {
                cur = p;
            } else {
                break;
            }
        }
        let Some(_parent) = m.parent[cur as usize] else {
            return (Err((REJ_ESCAPE, "module root".into())), prov);
        };
        let edge = m.edge[cur as usize];
        match edge {
            Edge::AppFun => {
                let root = self.module.spine_root(cur);
                prov.source_nodes = vec![root];
                let (_, args) = m.spine(root);
                let n = value_args(&self.scope, &args).len();
                let Some((slots, arity)) = info.cont else {
                    return (
                        Err((
                            REJ_STATE_APPLIED,
                            format!("state applied to {n} argument(s)"),
                        )),
                        prov,
                    );
                };
                let Some(kind) = slots.kind() else {
                    return (Err((REJ_MIXED_KIND, "ok/err not decided".into())), prov);
                };
                let rule = if n == arity {
                    Some(R3_CONT_CALL)
                } else if n == arity + 2 {
                    Some(R3_CONT_CALL_TRAILING)
                } else if n < arity
                    && let Some(owed) = self.owed_at(root)
                    && owed + n == arity
                {
                    Some(R3_CONT_CALL_ETA)
                } else {
                    None
                };
                if let Some(rule) = rule {
                    let vargs = value_args(&self.scope, &args);
                    if let Some(why) = self.cont_call_arg_types(&bd.ty, &vargs, arity) {
                        return (Err((REJ_CONT_ARG_TY, why)), prov);
                    }
                    prov.rule = rule;
                    // Invoking a continuation goes to the role it *is*.
                    return (
                        Ok(Some(EdgeSpec {
                            fact: EdgeFact::Invoke,
                            source_role: slots,
                            destination: slots,
                            at: root,
                        })),
                        prov,
                    );
                }
                let _ = kind;
                (
                    Err((
                        REJ_CONT_ARITY,
                        format!("applied to {n} argument(s), needs {arity}"),
                    )),
                    prov,
                )
            }
            Edge::AppArg => {
                let parent = m.parent[cur as usize].expect("checked");
                let root = self.module.spine_root(parent);
                prov.source_nodes = vec![root];
                let (_, args) = m.spine(root);
                let vargs = value_args(&self.scope, &args);
                let Some(idx) = vargs.iter().position(|a| *a == cur) else {
                    return (Err((REJ_ESCAPE, "type argument".into())), prov);
                };
                match self.call_shape(root) {
                    Some(CallShape::Cont { kind, arity, n }) => {
                        // (value, state, error) for ok, (error) for err;
                        // an eta-reduced call has no readable layout.
                        if n != arity && n != arity + 2 {
                            return (
                                Err((
                                    REJ_UNRECOGNISED_CALL,
                                    format!("continuation call with {n} of {arity} arguments"),
                                )),
                                prov,
                            );
                        }
                        let state_slot = kind == ContKind::Ok && idx == 1;
                        if info.cont.is_none() && state_slot {
                            prov.rule = R5_STATE_IN_CONT_CALL;
                            return (Ok(None), prov);
                        }
                        let what = if info.cont.is_none() {
                            "state"
                        } else {
                            "continuation"
                        };
                        (
                            Err((
                                if info.cont.is_none() {
                                    REJ_STATE_SLOT
                                } else {
                                    REJ_CONT_SLOT
                                },
                                format!("{what} in argument {idx} of a {kind:?} continuation call"),
                            )),
                            prov,
                        )
                    }
                    Some(CallShape::Parser { state, slots, rule }) => {
                        if info.cont.is_none() {
                            return if state == Some(idx) {
                                prov.rule = R6_STATE_IN_PARSER_CALL;
                                (Ok(None), prov)
                            } else {
                                (
                                    Err((
                                        REJ_STATE_SLOT,
                                        format!(
                                            "state in argument {idx} of a parser call ({rule})"
                                        ),
                                    )),
                                    prov,
                                )
                            };
                        }
                        let (slots_here, _) = info.cont.expect("checked");
                        let Some(target) = slots.iter().find(|(i, _)| *i == idx).map(|(_, s)| *s)
                        else {
                            return (
                                Err((
                                    REJ_CONT_SLOT,
                                    format!("continuation in argument {idx}, not a slot ({rule})"),
                                )),
                                prov,
                            );
                        };
                        // The kind check is what makes forwarding sound:
                        // an ok continuation may fill either ok slot and an
                        // error continuation either error slot, but never
                        // the other kind. It is enforced on *every*
                        // propagation, and the binder's own role
                        // (`source_role`) is untouched by the forwarding.
                        match (target.kind(), slots_here.kind()) {
                            (Some(a), Some(b2)) if a == b2 => {
                                prov.rule = R4_PROP_CONT;
                                prov.source_nodes.push(root);
                                (
                                    Ok(Some(EdgeSpec {
                                        fact: EdgeFact::Forward,
                                        source_role: slots_here,
                                        destination: target,
                                        at: root,
                                    })),
                                    prov,
                                )
                            }
                            (Some(a), Some(b2)) => (
                                Err((
                                    REJ_CONT_KIND,
                                    format!("{b2:?} continuation in a {a:?} slot"),
                                )),
                                prov,
                            ),
                            _ => (Err((REJ_MIXED_KIND, "slot kind not decided".into())), prov),
                        }
                    }
                    None => {
                        let (head, _) = m.spine(root);
                        let con = self
                            .scope
                            .head_sig(m.strip(head))
                            .and_then(|sig| sig.data_con)
                            .is_some();
                        (
                            Err(if con {
                                (
                                    REJ_CON_FIELD,
                                    format!("stored in field {idx} of a data constructor"),
                                )
                            } else {
                                (
                                    REJ_UNRECOGNISED_CALL,
                                    format!("argument {idx} of a call that is not a parser call"),
                                )
                            }),
                            prov,
                        )
                    }
                }
            }
            Edge::CaseScrut => {
                if info.cont.is_none() {
                    prov.rule = R7_STATE_SCRUTINISED;
                    (Ok(None), prov)
                } else {
                    (
                        Err((REJ_CONT_SCRUTINISED, "continuation scrutinised".into())),
                        prov,
                    )
                }
            }
            _ => {
                // A continuation value returned into a position that owes
                // exactly the arguments it still needs.
                if let Some((_, arity)) = info.cont
                    && let Some(owed) = self.owed_at(cur)
                    && owed == arity
                {
                    prov.rule = R3_CONT_RETURNED;
                    return (Ok(None), prov);
                }
                (Err((REJ_ESCAPE, format!("used at a {edge:?} edge"))), prov)
            }
        }
    }

    //--------------------------------------------------------------------------
    // Queries
    //--------------------------------------------------------------------------

    /// The continuation-call edge recorded at `root` for the head binder
    /// `b`, if any. Propagation and `CallParser` edges sit at the same root
    /// and are deliberately not returned: they say what the *arguments* of
    /// the call are, not what the call itself invokes.
    pub fn cont_edge_at(&self, root: ExprId, b: BinderId) -> Option<(&ParserRegion, &ParserEdge)> {
        for (ri, ei) in self.edge_index.get(&root)? {
            let r = &self.regions[*ri];
            let e = &r.edges[*ei];
            if e.provenance.binder == Some(b)
                && matches!(
                    e.provenance.rule,
                    R3_CONT_CALL | R3_CONT_CALL_TRAILING | R3_CONT_CALL_ETA
                )
            {
                return Some((r, e));
            }
        }
        None
    }

    /// Every edge recorded at a spine root.
    pub fn edges_at(&self, root: ExprId) -> Vec<(&ParserRegion, &ParserEdge)> {
        self.edge_index
            .get(&root)
            .map(|v| {
                v.iter()
                    .map(|(ri, ei)| (&self.regions[*ri], &self.regions[*ri].edges[*ei]))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Is this binder a (candidate) Parsec role binder?
    pub fn role_of(&self, b: BinderId) -> Option<usize> {
        self.role.get(&b).map(|r| r.region)
    }

    pub fn resolved_head(&self, root: ExprId) -> Option<BinderId> {
        let m = self.module;
        let (head, _) = m.spine(root);
        let hi = m.strip(head);
        self.scope.resolve(hi)
    }

    /// The spine root a census argument site belongs to. The same
    /// [`h2r_core_ir::Module::spine_root`] the census uses: there is one
    /// notion of an application root in the compiler.
    pub fn site_root(&self, app: ExprId) -> ExprId {
        self.module.spine_root(app)
    }
}

//------------------------------------------------------------------------------
// Accounting
//------------------------------------------------------------------------------

/// Where an argument site of the census' Parsec-shaped unresolved
/// population ends up. Exactly one bucket per site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Bucket {
    /// The head is a proven continuation (or a proven parser parameter) with
    /// a single role, and this call is a well-formed edge.
    ExactRole,
    /// The head is proven to be one of a known finite set of roles.
    FiniteRoleSet,
    /// The head is a Parsec role binder of a recognised region, but the
    /// region is rejected or this call is not a well-formed edge.
    RegionRecognisedTargetUnresolved,
    /// Not Parsec: the head is not a role binder at all.
    RejectedNonParsec,
}

#[derive(Debug, Clone, Serialize)]
pub struct SiteVerdict {
    pub module: String,
    pub app: ExprId,
    pub arg: ExprId,
    pub root: ExprId,
    pub bucket: Bucket,
    /// The rule that proved the edge, when there is one.
    pub rule: Option<&'static str>,
    /// Machine-readable reason, when the site is not proven.
    pub reason: Option<&'static str>,
    pub detail: String,
    pub head_label: String,
    pub head_ty: String,
    pub region: Option<usize>,
    pub edge: Option<EdgeKind>,
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct Accounting {
    pub population: usize,
    pub exact: usize,
    pub finite: usize,
    pub region_unresolved: usize,
    pub rejected: usize,
    /// Sites the recogniser proves as edges that the census did *not* put
    /// in the Parsec-shaped unresolved population. Reported separately;
    /// never folded into the population.
    pub outside_exact: usize,
    pub outside_finite: usize,
    pub reasons: BTreeMap<String, usize>,
    pub verdicts: Vec<SiteVerdict>,
}

impl Accounting {
    pub fn check(&self) {
        assert_eq!(
            self.exact + self.finite + self.region_unresolved + self.rejected,
            self.population,
            "every site must land in exactly one bucket"
        );
    }
}

/// Is this census site part of the Parsec-shaped unresolved population?
pub fn in_population(a: &crate::laziness::ArgSite) -> bool {
    a.shape == ArgShape::Computation
        && a.position.escapes()
        && matches!(
            a.callee.family,
            Family::ParsecContinuation | Family::EtaParam
        )
}

/// Classify every census argument site against the recognisers.
/// The recogniser's verdict for one census argument site: which bucket it
/// lands in, why, and what evidence produced it. The single place the
/// question is answered — [`integrate`] writes it onto the site and
/// [`account`] tallies it, so the tiers and the accounting can never
/// disagree.
pub struct Verdict {
    pub bucket: Bucket,
    pub target: Option<ParsecTarget>,
    pub rule: Option<&'static str>,
    pub reason: Option<&'static str>,
    pub detail: String,
    pub region: Option<usize>,
    pub edge: Option<EdgeKind>,
    pub head: Option<BinderId>,
    pub root: ExprId,
}

pub fn verdict(a: &Analysis<'_>, site: &crate::laziness::ArgSite) -> Verdict {
    let root = a.site_root(site.app);
    let head = a.resolved_head(root);
    let mut v = Verdict {
        bucket: Bucket::RejectedNonParsec,
        target: None,
        rule: None,
        reason: None,
        detail: String::new(),
        region: None,
        edge: None,
        head,
        root,
    };
    match head.and_then(|b| a.cont_edge_at(root, b)) {
        Some((r, e)) if r.proven => {
            v.bucket = if e.exact() {
                Bucket::ExactRole
            } else {
                Bucket::FiniteRoleSet
            };
            v.target = Some(if e.exact() {
                ParsecTarget::Role(e.kind)
            } else {
                ParsecTarget::RoleSet
            });
            v.rule = Some(e.provenance.rule);
            v.region = Some(e.region);
            v.edge = Some(e.kind);
        }
        Some((_, e)) => {
            v.bucket = Bucket::RegionRecognisedTargetUnresolved;
            v.target = Some(ParsecTarget::RegionUnresolved("region-rejected"));
            v.reason = Some("region-rejected");
            v.region = Some(e.region);
        }
        None => match head.and_then(|b| a.role_of(b)) {
            Some(ri) => {
                let why = if a.regions[ri].proven {
                    "call-is-not-an-edge"
                } else {
                    "region-rejected"
                };
                v.bucket = Bucket::RegionRecognisedTargetUnresolved;
                v.target = Some(ParsecTarget::RegionUnresolved(why));
                v.reason = Some(why);
                v.region = Some(ri);
            }
            None => {
                v.reason = Some("head-is-not-a-parsec-role-binder");
                v.detail = match head {
                    Some(b) => format!("head :: {}", a.binder(b).ty),
                    None => "head is not a local binder".to_string(),
                };
            }
        },
    }
    v
}

/// Write what the recogniser proved onto every census argument site, so the
/// census' target tier reflects it. The resolution and family axes are left
/// exactly as they were: this is a third, orthogonal fact.
pub fn integrate(census: &mut Census, analyses: &[Analysis<'_>]) {
    let by_module: HashMap<&str, &Analysis> = analyses
        .iter()
        .map(|a| (a.module.name.as_str(), a))
        .collect();
    for site in &mut census.args {
        let Some(a) = by_module.get(site.module.as_str()) else {
            continue;
        };
        site.callee.parsec = verdict(a, site).target;
    }
}

pub fn account(census: &Census, analyses: &[Analysis<'_>]) -> Accounting {
    let by_module: HashMap<&str, &Analysis> = analyses
        .iter()
        .map(|a| (a.module.name.as_str(), a))
        .collect();
    let mut acct = Accounting::default();
    for site in &census.args {
        let pop = in_population(site);
        let Some(a) = by_module.get(site.module.as_str()) else {
            if pop {
                acct.population += 1;
                acct.rejected += 1;
                *acct
                    .reasons
                    .entry("module-not-analysed".into())
                    .or_default() += 1;
            }
            continue;
        };
        let Verdict {
            bucket,
            rule,
            reason,
            detail,
            region,
            edge,
            head,
            root,
            ..
        } = verdict(a, site);
        if !pop {
            match bucket {
                Bucket::ExactRole => acct.outside_exact += 1,
                Bucket::FiniteRoleSet => acct.outside_finite += 1,
                _ => {}
            }
            continue;
        }
        acct.population += 1;
        match bucket {
            Bucket::ExactRole => acct.exact += 1,
            Bucket::FiniteRoleSet => acct.finite += 1,
            Bucket::RegionRecognisedTargetUnresolved => acct.region_unresolved += 1,
            Bucket::RejectedNonParsec => acct.rejected += 1,
        }
        if let Some(r) = reason {
            let key = if detail.is_empty() {
                r.to_string()
            } else {
                format!("{r}: {detail}")
            };
            *acct.reasons.entry(key).or_default() += 1;
        }
        acct.verdicts.push(SiteVerdict {
            module: site.module.clone(),
            app: site.app,
            arg: site.arg,
            root,
            bucket,
            rule,
            reason,
            detail,
            head_label: head.map(|b| a.binder(b).occ.clone()).unwrap_or_default(),
            head_ty: head.map(|b| a.binder(b).ty.clone()).unwrap_or_default(),
            region,
            edge,
        });
    }
    acct.check();
    acct
}

//------------------------------------------------------------------------------
// Tests
//------------------------------------------------------------------------------

#[cfg(test)]
mod test {
    use super::*;
    use h2r_core_ir::raw;
    use serde_json::{Value, json};

    const ST: &str = "State String UserState";
    const OK: &str = "Token -> State String UserState -> ParseError -> SCBase m b";
    const EK: &str = "ParseError -> SCBase m b";

    fn dmd() -> Value {
        json!({"strict": false, "absent": false, "usedOnce": false, "pretty": "L"})
    }

    /// A binder with a real type; `occ` is a *label*, never evidence.
    fn b(occ: &str, ty: &str) -> Value {
        json!({
            "kind": "id", "name": occ, "occ": occ, "unique": occ, "type": ty,
            "arity": 0, "callArity": 0, "exported": false,
            "dmdSig": {"args": [], "diverges": false, "pretty": ""},
            "cprSig": "", "demand": dmd(),
            "occInfo": {"kind": "many", "tailCalled": false}, "oneShot": false,
            "details": "", "hasUnfolding": false, "isJoinPoint": false, "isDataCon": false
        })
    }

    fn v(occ: &str) -> Value {
        json!({"node": "Var", "name": occ, "occ": occ, "unique": occ, "isGlobal": false})
    }

    fn g(occ: &str) -> Value {
        json!({"node": "Var", "name": occ, "occ": occ, "unique": occ, "isGlobal": true})
    }

    fn ap(f: Value, args: Vec<Value>) -> Value {
        let mut e = f;
        for a in args {
            e = json!({"node": "App", "fun": e, "arg": a});
        }
        e
    }

    fn lam(params: Vec<Value>, body: Value) -> Value {
        let mut e = body;
        for p in params.into_iter().rev() {
            e = json!({"node": "Lam", "binder": p, "body": e});
        }
        e
    }

    fn case_of(scrut: Value, con: &str, binders: Vec<Value>, rhs: Value) -> Value {
        json!({
            "node": "Case", "scrut": scrut, "binder": b("wild", "T"), "type": "R",
            "alts": [{"con": {"kind": "DataAlt", "name": con, "occ": con, "tag": 1},
                      "binders": binders, "rhs": rhs}]
        })
    }

    fn case_alts(scrut: Value, rhss: Vec<Value>) -> Value {
        let alts: Vec<Value> = rhss
            .into_iter()
            .enumerate()
            .map(|(i, rhs)| {
                json!({"con": {"kind": "DataAlt", "name": format!("C{i}"), "occ": format!("C{i}"),
                               "tag": i as u32 + 1},
                       "binders": [], "rhs": rhs})
            })
            .collect();
        json!({"node": "Case", "scrut": scrut, "binder": b("wild", "T"), "type": "R", "alts": alts})
    }

    fn module(body: Value, ids: Value) -> h2r_core_ir::Module {
        let m = json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": ids,
            "binds": [{"rec": false, "pairs": [{
                "binder": b("top", "T"), "rhs": body,
                "whnf": true, "trivial": false, "cheap": false, "okForSpec": false
            }]}]
        });
        h2r_core_ir::Module::from_raw(serde_json::from_value(m).unwrap()).unwrap()
    }

    fn con(occ: &str, arity: u32) -> Value {
        json!({
            "name": occ, "occ": occ, "arity": arity,
            "dmdSig": {"args": [], "diverges": false, "pretty": ""},
            "isJoinPoint": false,
            "dataCon": {"name": occ, "repArity": arity, "tag": 1,
                        "strictFields": vec![false; arity as usize]}
        })
    }

    fn kinds(a: &Analysis) -> Vec<EdgeKind> {
        let mut k: Vec<EdgeKind> = a
            .regions
            .iter()
            .flat_map(|r| r.edges.iter().map(|e| e.kind))
            .collect();
        k.sort();
        k.dedup();
        k
    }

    fn rules(a: &Analysis) -> Vec<&'static str> {
        let mut k: Vec<&'static str> = a
            .regions
            .iter()
            .flat_map(|r| r.edges.iter().map(|e| e.provenance.rule))
            .collect();
        k.sort();
        k.dedup();
        k
    }

    /// `\s1 cok cerr eok eerr -> case s1 of State … -> case p of { … }` with
    /// one alternative per edge kind.
    #[test]
    fn minimal_region_proves_all_five_edge_kinds() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            case_of(
                v("s1"),
                "State",
                vec![
                    b("pos", "SourcePos"),
                    b("inp", "String"),
                    b("u", "UserState"),
                ],
                case_alts(
                    g("scrut"),
                    vec![
                        ap(v("cok"), vec![g("x"), v("s1"), g("e")]),
                        ap(v("cerr"), vec![g("e")]),
                        ap(v("eok"), vec![g("x"), v("s1"), g("e")]),
                        ap(v("eerr"), vec![g("e")]),
                        ap(
                            g("p"),
                            vec![v("s1"), v("cok"), v("cerr"), v("eok"), v("eerr")],
                        ),
                    ],
                ),
            ),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        assert_eq!(a.regions.len(), 1);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        assert!(r.state.is_some() && r.cok.is_some() && r.cerr.is_some());
        assert!(r.eok.is_some() && r.eerr.is_some());
        assert_eq!(
            kinds(&a),
            vec![
                EdgeKind::ConsumedOk,
                EdgeKind::ConsumedErr,
                EdgeKind::EmptyOk,
                EdgeKind::EmptyErr,
                EdgeKind::CallParser
            ]
        );
        // The state flows into a continuation slot, a parser slot and a case.
        let ev: Vec<&'static str> = r.evidence.iter().map(|e| e.rule).collect();
        assert!(ev.contains(&R5_STATE_IN_CONT_CALL));
        assert!(ev.contains(&R6_STATE_IN_PARSER_CALL));
        assert!(ev.contains(&R7_STATE_SCRUTINISED));
    }

    /// The inlined `<?>` / label combinator: the region's own cok and cerr go
    /// straight through, its eok and eerr are replaced by fresh lambdas that
    /// call them.
    #[test]
    fn label_combinator_wraps_the_empty_continuations() {
        let wrapped_ok = lam(
            vec![b("x1", "Token"), b("s3", ST), b("err1", "ParseError")],
            ap(v("cok"), vec![v("x1"), v("s3"), g("merge")]),
        );
        let wrapped_err = lam(
            vec![b("err2", "ParseError")],
            ap(v("cerr"), vec![g("merge")]),
        );
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(
                g("poly_k"),
                vec![v("s1"), v("cok"), v("cerr"), wrapped_ok, wrapped_err],
            ),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        // cok is propagated into the cok slot *and* called inside the fresh
        // eok lambda; both are edges, and the call is a ConsumedOk.
        let cok = r.cok.unwrap();
        let for_cok: Vec<(&'static str, EdgeKind)> = r
            .edges
            .iter()
            .filter(|e| e.provenance.binder == Some(cok))
            .map(|e| (e.provenance.rule, e.kind))
            .collect();
        assert!(for_cok.contains(&(R4_PROP_CONT, EdgeKind::ConsumedOk)));
        assert!(for_cok.contains(&(R3_CONT_CALL, EdgeKind::ConsumedOk)));
        // eok and eerr are not passed anywhere: the wrappers replaced them.
        assert!(
            r.edges
                .iter()
                .all(|e| e.provenance.binder != Some(r.eok.unwrap()))
        );
        assert!(rules(&a).contains(&R2_PARSER_CALL));
    }

    /// Every binder named `eta`, and a binder named `cok` that is not a
    /// continuation at all. The roles come out right either way.
    #[test]
    fn names_are_not_evidence() {
        let region = lam(
            vec![
                b("cok", "[Char]"), // a String named `cok`
                b("eta", ST),
                b("eta1", OK),
                b("eta2", EK),
                b("eta3", OK),
                b("eta4", EK),
            ],
            ap(v("eta1"), vec![g("x"), v("eta"), g("e")]),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        // The `eta`-named parameters got the roles; the `cok`-named one did not.
        assert_eq!(a.module.binder(r.cok.unwrap()).occ, "eta1");
        assert_eq!(a.module.binder(r.state.unwrap()).occ, "eta");
        let string_cok = r.conts.iter().find(|c| c.ty == "[Char]");
        assert!(string_cok.is_none());
        assert_eq!(r.edges[0].kind, EdgeKind::ConsumedOk);
        assert!(r.edges[0].exact());
    }

    /// Worker/wrapper drops absent continuations, so a run can be shorter
    /// than four. Two continuations that could be either the consumed or the
    /// empty pair are a proven finite role set, not an exact role.
    #[test]
    fn dropped_continuations_give_a_finite_role_set() {
        let region = lam(
            vec![b("s1", ST), b("ok", OK), b("err", EK)],
            ap(v("ok"), vec![g("x"), v("s1"), g("e")]),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        assert_eq!(r.conts[0].slots.len(), 2);
        assert_eq!(r.conts[1].slots.len(), 2);
        assert_eq!(r.cok, None, "no slot is proven exactly");
        let e = &r.edges[0];
        assert!(!e.exact());
        assert_eq!(e.candidates, vec![EdgeKind::ConsumedOk, EdgeKind::EmptyOk]);
    }

    /// A continuation stored in a data constructor field escapes: the
    /// recogniser cannot see what will eventually call it, so the region is
    /// rejected rather than guessed at.
    #[test]
    fn continuation_stored_in_a_constructor_rejects() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(g("MkT"), vec![v("cok"), v("cerr")]),
        );
        let m = module(region, json!({"MkT": con("MkT", 2)}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(!r.proven);
        assert!(r.rejects.iter().all(|j| j.reason == REJ_CON_FIELD));
        assert_eq!(r.rejects.len(), 2);
    }

    /// The state handed to a continuation in the *value* slot is not the
    /// state flowing where a state may flow.
    #[test]
    fn state_in_the_wrong_slot_rejects() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(v("cok"), vec![v("s1"), g("s2"), g("e")]),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(!r.proven);
        // Two independent rules see it: the state is in a value slot, and
        // the call's argument types contradict cok's own type.
        let state_slot = r
            .rejects
            .iter()
            .find(|j| j.reason == REJ_STATE_SLOT)
            .expect("the state reject");
        assert!(state_slot.detail.contains("argument 0"));
        assert!(r.rejects.iter().any(|j| j.reason == REJ_CONT_ARG_TY));
        assert_eq!(r.rejects.len(), 2);
    }

    /// Continuations propagate through a parser call nested inside a fresh
    /// continuation passed to another parser call.
    #[test]
    fn propagation_through_a_nested_parser_call() {
        let inner = lam(
            vec![b("x", "Token"), b("s2", ST), b("err", "ParseError")],
            ap(
                g("q"),
                vec![v("s2"), v("cok"), v("cerr"), v("eok"), v("eerr")],
            ),
        );
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(g("p"), vec![v("s1"), v("cok"), v("cerr"), inner, v("eerr")]),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        let props = r
            .edges
            .iter()
            .filter(|e| e.provenance.rule == R4_PROP_CONT)
            .count();
        // three at the outer call (cok, cerr, eerr) and four at the inner one
        assert_eq!(props, 7);
        let calls = r
            .edges
            .iter()
            .filter(|e| e.kind == EdgeKind::CallParser)
            .count();
        assert_eq!(calls, 2);
    }

    /// GHC eta-reduces a continuation wrapper down to `\x -> k v`: the
    /// lambda binds one of the three arguments and the call supplies one,
    /// the caller supplies the other two.
    #[test]
    fn eta_reduced_continuation_call_is_still_an_edge() {
        let wrapper = lam(vec![b("x", "Token")], ap(v("cok"), vec![g("wrap")]));
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(
                g("p"),
                vec![v("s1"), wrapper, v("cerr"), v("eok"), v("eerr")],
            ),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        assert!(
            r.edges
                .iter()
                .any(|e| e.provenance.rule == R3_CONT_CALL_ETA && e.kind == EdgeKind::ConsumedOk)
        );
    }

    /// Uniques are reused across inlined copies; every occurrence must
    /// resolve to the binder that actually binds it.
    #[test]
    fn shadowed_uniques_resolve_to_the_innermost_binder() {
        // Two sibling regions whose binders share every unique.
        let one = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(v("cok"), vec![g("x"), v("s1"), g("e")]),
        );
        let two = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(v("cerr"), vec![g("e")]),
        );
        let m = module(ap(g("pair"), vec![one, two]), json!({}));
        let a = Analysis::of_module(&m);
        assert_eq!(a.regions.len(), 2);
        assert!(a.regions.iter().all(|r| r.proven));
        assert!(a.regions.iter().all(|r| r.edges.len() == 1));
        let mut ks: Vec<EdgeKind> = a.regions.iter().map(|r| r.edges[0].kind).collect();
        ks.sort();
        assert_eq!(ks, vec![EdgeKind::ConsumedOk, EdgeKind::ConsumedErr]);
        // Each edge is attributed to its *own* region's binder, even though
        // the two regions' binders share every unique.
        for r in &a.regions {
            let e = &r.edges[0];
            let own = match e.kind {
                EdgeKind::ConsumedOk => r.cok,
                _ => r.cerr,
            };
            assert_eq!(e.provenance.binder, own);
        }
        let cok0 = a.module.binder(a.regions[0].cok.unwrap());
        let cok1 = a.module.binder(a.regions[1].cok.unwrap());
        assert_eq!(cok0.unique, cok1.unique);
        assert_ne!(a.regions[0].cok, a.regions[1].cok);
    }

    /// A lambda chain whose parameter types disagree about the result type
    /// is not a region at all, and says so.
    #[test]
    fn type_disagreement_is_recorded_not_silently_dropped() {
        let region = lam(
            vec![
                b("s1", ST),
                b(
                    "cok",
                    "Token -> State String UserState -> ParseError -> IO b",
                ),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            g("body"),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        assert!(a.regions.is_empty());
        assert_eq!(a.skipped.len(), 1);
        assert_eq!(a.skipped[0].reason, "type-disagreement");
    }

    /// The accounting partitions the census population; nothing vanishes.
    #[test]
    fn accounting_partitions_the_population() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(
                v("cok"),
                vec![g("x"), v("s1"), ap(g("mergeError"), vec![g("a"), g("b")])],
            ),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let census = Census::of_modules([&m]);
        let acct = account(&census, std::slice::from_ref(&a));
        acct.check();
        assert_eq!(acct.population, 1, "the mergeError argument");
        assert_eq!(acct.exact, 1);
        assert_eq!(acct.verdicts[0].bucket, Bucket::ExactRole);
        assert_eq!(acct.verdicts[0].edge, Some(EdgeKind::ConsumedOk));
    }

    //--------------------------------------------------------------------------
    // Adversarial: what must *not* be recognised
    //--------------------------------------------------------------------------

    /// An ordinary higher-order function that happens to take two
    /// continuation-shaped arguments is not a parser call. Nothing explains
    /// a missing `State s u` here, so [`R2_UNBOXED_STATE`] must not fire —
    /// and because the region hands its own continuations to a call the
    /// rules do not recognise, the region rejects rather than guessing.
    #[test]
    fn two_continuation_arguments_alone_are_not_a_parser_call() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            // `withBoth` takes an ok- and an err-shaped callback and no
            // state: shape alone would have matched the template.
            ap(g("withBoth"), vec![g("n"), v("cok"), v("cerr")]),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(!r.proven, "a bare continuation run is not evidence");
        assert!(r.rejects.iter().all(|j| j.reason == REJ_UNRECOGNISED_CALL));
        assert_eq!(r.rejects.len(), 2);
        assert!(!rules(&a).contains(&R2_UNBOXED_DESTRUCTURED));
    }

    /// The same call *is* a parser call once the missing state is
    /// explained: the three representation fields of a destructured
    /// `State s u` stand where the state would be.
    #[test]
    fn a_destructured_state_explains_the_missing_state_argument() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            case_of(
                v("s1"),
                "State",
                vec![
                    b("ww", "String"),
                    b("ww1", "SourcePos"),
                    b("ww2", "UserState"),
                ],
                ap(
                    g("$wsatisfy"),
                    vec![g("p"), v("ww"), v("ww1"), v("ww2"), v("cok"), v("cerr")],
                ),
            ),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        assert!(rules(&a).contains(&R2_UNBOXED_DESTRUCTURED));
        // …and the middle field really has to be a SourcePos.
        let bad = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            case_of(
                v("s1"),
                "State",
                vec![b("ww", "String"), b("ww1", "Int"), b("ww2", "UserState")],
                ap(
                    g("$wsatisfy"),
                    vec![g("p"), v("ww"), v("ww1"), v("ww2"), v("cok"), v("cerr")],
                ),
            ),
        );
        let m = module(bad, json!({}));
        let a = Analysis::of_module(&m);
        assert!(!a.regions[0].proven);
    }

    /// A worker whose own parameters are the representation fields is a
    /// recognised region, and a saturated call to it is a parser call by
    /// the worker's own layout.
    #[test]
    fn a_workers_own_layout_explains_the_missing_state_argument() {
        let worker = lam(
            vec![
                b("ww", "String"),
                b("ww1", "SourcePos"),
                b("ww2", "UserState"),
                b("wcok", OK),
                b("wcerr", EK),
            ],
            ap(v("wcok"), vec![g("x"), g("s9"), g("e")]),
        );
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(
                v("$wf"),
                vec![g("i"), g("pos"), g("u"), v("cok"), v("cerr")],
            ),
        );
        // let $wf = worker in region: the call is headed by the worker, so
        // its own layout says the first three arguments are State's fields.
        let body = json!({"node": "Let", "bind": {"rec": false, "pairs": [{
            "binder": b("$wf", "String -> SourcePos -> UserState -> R"),
            "rhs": worker, "whnf": true, "trivial": false, "cheap": false, "okForSpec": false
        }]}, "body": region});
        let m = module(body, json!({}));
        let a = Analysis::of_module(&m);
        let outer = a
            .regions
            .iter()
            .find(|r| r.state.is_some())
            .expect("the caller region");
        assert!(outer.proven, "rejects: {:?}", outer.rejects);
        assert!(rules(&a).contains(&R2_UNBOXED_WORKER));
    }

    /// Forwarding never rewrites a role. The inlined `<?>` hands its own
    /// `cok` to the `eok` slot; the edge records the destination slot *and*
    /// the source's untouched role, and `cok` stays `cok` everywhere else.
    #[test]
    fn forwarding_records_both_facts_and_changes_no_role() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            ap(
                g("p"),
                vec![v("s1"), v("cok"), v("cerr"), v("cok"), v("eerr")],
            ),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(r.proven, "rejects: {:?}", r.rejects);
        let cok = r.cok.unwrap();
        let fwd: Vec<&ParserEdge> = r
            .edges
            .iter()
            .filter(|e| e.provenance.binder == Some(cok))
            .collect();
        assert_eq!(fwd.len(), 2, "cok is forwarded into two slots");
        for e in &fwd {
            assert_eq!(e.fact, EdgeFact::Forward);
            assert_eq!(e.source_role, SlotSet::single(Slot::Cok as usize));
        }
        let mut dests: Vec<EdgeKind> = fwd.iter().map(|e| e.kind).collect();
        dests.sort();
        assert_eq!(dests, vec![EdgeKind::ConsumedOk, EdgeKind::EmptyOk]);
        assert_eq!(fwd.iter().filter(|e| e.reroutes()).count(), 1);
        // The role itself is untouched: cok is still exactly slot Cok.
        assert_eq!(
            r.conts
                .iter()
                .find(|c| c.binder == cok)
                .unwrap()
                .slots
                .exact(),
            Some(Slot::Cok)
        );
    }

    /// The ok/err check on a propagation is not optional.
    ///
    /// It can only bite where the slot and the forwarded value are decided
    /// by different means: here `k` is a let-bound ok continuation whose
    /// value argument GHC has already supplied, so its printed type is
    /// `State s u -> ParseError -> r` — a shape the argument-run matcher
    /// cannot classify, which leaves the slot to be fixed by the *other*
    /// arguments. They put `k` in the `cerr` slot, and `k` is an ok
    /// continuation, so the region rejects instead of guessing.
    #[test]
    fn forwarding_into_a_slot_of_the_other_kind_rejects() {
        let partial = "State String UserState -> ParseError -> SCBase m b";
        let body = json!({"node": "Let", "bind": {"rec": false, "pairs": [{
            "binder": b("k", partial),
            "rhs": ap(v("cok"), vec![g("x")]),
            "whnf": true, "trivial": false, "cheap": false, "okForSpec": false
        }]}, "body": ap(g("p"), vec![v("s1"), v("cok"), v("k"), v("eok"), v("eerr")])});
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            body,
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert_eq!(r.derived.len(), 1, "k is promoted by R8");
        assert!(!r.proven);
        assert!(
            r.rejects.iter().any(|j| j.reason == REJ_CONT_KIND),
            "rejects: {:?}",
            r.rejects
        );
    }

    /// A continuation applied to its arity, but with an argument whose own
    /// type contradicts the continuation's type, is not an edge.
    #[test]
    fn a_continuation_call_with_a_contradicting_argument_type_rejects() {
        let region = lam(
            vec![
                b("s1", ST),
                b("cok", OK),
                b("cerr", EK),
                b("eok", OK),
                b("eerr", EK),
            ],
            // `cerr` wants a ParseError; it is given the state.
            ap(v("cerr"), vec![v("s1")]),
        );
        let m = module(region, json!({}));
        let a = Analysis::of_module(&m);
        let r = &a.regions[0];
        assert!(!r.proven);
        assert!(r.rejects.iter().any(|j| j.reason == REJ_CONT_ARG_TY));
    }

    /// R9: a worker whose run embeds into the template in two ways, and the
    /// wrapper that calls it. The wrapper's chain carries all four slots, so
    /// its own embedding is unambiguous; its body is one saturated call
    /// forwarding its parameters, which fixes the worker's roles.
    #[test]
    fn a_wrapper_resolves_the_workers_ambiguous_embedding() {
        // $wf s ok err — ok/err could be {cok,cerr} or {eok,eerr} …
        let worker = lam(
            vec![b("s2", ST), b("ok", OK), b("err", EK)],
            ap(v("ok"), vec![g("x"), v("s2"), g("e")]),
        );
        // … but the wrapper passes its *empty* pair.
        let wrapper = lam(
            vec![
                b("s1", ST),
                b("wcok", OK),
                b("wcerr", EK),
                b("weok", OK),
                b("weerr", EK),
            ],
            ap(v("$wf"), vec![v("s1"), v("weok"), v("weerr")]),
        );
        let body = json!({"node": "Let", "bind": {"rec": false, "pairs": [{
            "binder": b("$wf", "T"), "rhs": worker,
            "whnf": true, "trivial": false, "cheap": false, "okForSpec": false
        }]}, "body": wrapper});
        let m = module(body, json!({}));
        let a = Analysis::of_module(&m);
        let w = a.regions.iter().find(|r| r.params.len() == 3).unwrap();
        assert_eq!(w.conts.len(), 2);
        assert_eq!(w.conts[0].slots.exact(), Some(Slot::Eok));
        assert_eq!(w.conts[1].slots.exact(), Some(Slot::Eerr));
        assert!(w.wrapper.is_some());
        assert!(
            w.evidence.iter().any(|e| e.rule == R9_WRAPPER_MAP),
            "the mapping must record where it came from"
        );
        // The call inside the worker is now an exact EmptyOk edge.
        let e = w.edges.iter().find(|e| e.fact == EdgeFact::Invoke).unwrap();
        assert!(e.exact());
        assert_eq!(e.kind, EdgeKind::EmptyOk);
    }

    /// …and a caller that is not a wrapper (it does more than forward)
    /// resolves nothing: the role stays a proven finite set.
    #[test]
    fn a_caller_that_is_not_a_wrapper_resolves_nothing() {
        let worker = lam(
            vec![b("s2", ST), b("ok", OK), b("err", EK)],
            ap(v("ok"), vec![g("x"), v("s2"), g("e")]),
        );
        let caller = lam(
            vec![
                b("s1", ST),
                b("wcok", OK),
                b("wcerr", EK),
                b("weok", OK),
                b("weerr", EK),
            ],
            // The call is inside a case: the region does more than forward.
            case_alts(
                g("scrut"),
                vec![
                    ap(v("$wf"), vec![v("s1"), v("weok"), v("weerr")]),
                    ap(v("wcok"), vec![g("x"), v("s1"), g("e")]),
                ],
            ),
        );
        let body = json!({"node": "Let", "bind": {"rec": false, "pairs": [{
            "binder": b("$wf", "T"), "rhs": worker,
            "whnf": true, "trivial": false, "cheap": false, "okForSpec": false
        }]}, "body": caller});
        let m = module(body, json!({}));
        let a = Analysis::of_module(&m);
        let w = a.regions.iter().find(|r| r.params.len() == 3).unwrap();
        assert_eq!(w.conts[0].slots.len(), 2);
        assert!(w.wrapper.is_none());
    }

    #[test]
    fn type_helpers() {
        assert!(is_state_ty("State [Char] UserState"));
        assert!(!is_state_ty("StateT s Identity b"));
        assert!(is_parse_error_ty("ParseError"));
        assert_eq!(ty_kind(OK), TyKind::OkCont);
        assert_eq!(ty_kind(EK), TyKind::ErrCont);
        assert_eq!(ty_kind(ST), TyKind::State);
        assert_eq!(
            cont_shape_of_ty("State String UserState -> ParseError -> SCBase m b"),
            Some(ContShape {
                kind: ContKind::Ok,
                arity: 2
            })
        );
        // Printed type-variable names differ per binder; compare modulo them.
        assert_eq!(alpha_normalise("m b1"), alpha_normalise("m b"));
        assert_ne!(alpha_normalise("m b"), alpha_normalise("SCBase m b"));
        assert_eq!(split_arrows("(a -> b) -> c").len(), 2);
    }
}
