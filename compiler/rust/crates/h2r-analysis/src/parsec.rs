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
//! resolved to its innermost enclosing binder by an explicit-stack walk
//! ([`Analysis::resolve_scopes`]); no pass here keys anything by unique.

use std::collections::{BTreeMap, HashMap};

use h2r_core_ir::{Binder, BinderId, BinderKind, Edge, Expr, ExprId, Module};
use serde::Serialize;

use crate::callee::Family;
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
/// binders therefore reports differences that are not there. This is a
/// corroborating check on top of the layout and dataflow proof, not a type
/// checker: two genuinely different variables can normalise alike.
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

#[derive(Debug, Clone, Serialize)]
pub struct ParserEdge {
    /// The role this call plays. When the role is a proven finite set this
    /// is the first candidate; `candidates` carries the whole set.
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

/// A lambda chain's parameter types carry ParsecT's `State s u`, cok, cerr,
/// eok, eerr suffix; dropped (absent) continuations are allowed, so the run
/// is matched as a subsequence of the four-slot template.
pub const R1_LAYOUT: &str = "R1-LAYOUT";
/// Every continuation of a region agrees on the state type and on the
/// result type, and the ok continuations really take `State s u` then
/// `ParseError`.
pub const R1_TYPE_AGREE: &str = "R1-TYPE-AGREE";
/// A call whose arguments are a `State s u` followed by a run of
/// continuation-shaped arguments embedding into the template, plus at most
/// two trailing transformer arguments: a parser being run.
pub const R2_PARSER_CALL: &str = "R2-PARSER-CALL";
/// The same, with the state argument absent because worker/wrapper unboxed
/// `State` into its fields.
pub const R2_UNBOXED_STATE: &str = "R2-UNBOXED-STATE";
/// A continuation applied to exactly its arity: (value, state, error) for
/// an ok continuation, (error) for an error continuation.
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
/// `try`-like combinators pass cok into the eok slot.
pub const R4_PROP_CONT: &str = "R4-PROP-CONT";
/// The state passed in the state slot of a continuation call.
pub const R5_STATE_IN_CONT_CALL: &str = "R5-STATE-IN-CONT-CALL";
/// The state passed in the state slot of a recognised parser call.
pub const R6_STATE_IN_PARSER_CALL: &str = "R6-STATE-IN-PARSER-CALL";
/// The state scrutinised (`case s of State …`).
pub const R7_STATE_SCRUTINISED: &str = "R7-STATE-SCRUTINISED";
/// A let-bound binder of continuation type inside a region: a derived
/// continuation, proved by the same use rules as a parameter.
pub const R8_DERIVED_CONT: &str = "R8-DERIVED-CONT";

pub const REJ_STATE_APPLIED: &str = "state-applied";
pub const REJ_STATE_SLOT: &str = "state-in-non-state-slot";
pub const REJ_CONT_ARITY: &str = "cont-wrong-arity";
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
    scope: Scope<'m>,
    /// Innermost enclosing binder of every `Var` occurrence.
    resolved: Vec<Option<BinderId>>,
    uses: HashMap<BinderId, Vec<ExprId>>,
    role: HashMap<BinderId, RoleInfo>,
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
            resolved: vec![None; m.exprs.len()],
            uses: HashMap::new(),
            role: HashMap::new(),
            region_at: HashMap::new(),
            edge_index: HashMap::new(),
        };
        a.resolve_scopes();
        a.find_regions();
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
            if !matches!(m.expr(id), Expr::App { .. }) || self.spine_root(id) != id {
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
    // Scoped resolution
    //--------------------------------------------------------------------------

    /// Resolve every local `Var` to the binder that actually binds it.
    ///
    /// Iterative: an explicit stack of enter/bind/unbind operations, so the
    /// Core is never recursed over.
    fn resolve_scopes(&mut self) {
        enum Op<'a> {
            Enter(ExprId),
            Bind(BinderId),
            Unbind(&'a str),
        }
        let m = self.module;
        let mut env: HashMap<&str, Vec<BinderId>> = HashMap::new();
        let mut stack: Vec<Op> = Vec::new();
        for bind in &m.top {
            for p in &bind.pairs {
                env.entry(m.binder(p.binder).unique.as_str())
                    .or_default()
                    .push(p.binder);
            }
        }
        for bind in m.top.iter().rev() {
            for p in bind.pairs.iter().rev() {
                stack.push(Op::Enter(p.rhs));
            }
        }
        while let Some(op) = stack.pop() {
            let id = match op {
                Op::Bind(b) => {
                    env.entry(m.binder(b).unique.as_str()).or_default().push(b);
                    continue;
                }
                Op::Unbind(u) => {
                    if let Some(v) = env.get_mut(u) {
                        v.pop();
                    }
                    continue;
                }
                Op::Enter(id) => id,
            };
            match m.expr(id) {
                Expr::Var {
                    unique, is_global, ..
                } => {
                    if !*is_global && let Some(b) = env.get(unique.as_str()).and_then(|v| v.last())
                    {
                        self.resolved[id as usize] = Some(*b);
                        self.uses.entry(*b).or_default().push(id);
                    }
                }
                Expr::App { fun, arg } => {
                    stack.push(Op::Enter(*arg));
                    stack.push(Op::Enter(*fun));
                }
                Expr::Lam { binder, body } => {
                    stack.push(Op::Unbind(m.binder(*binder).unique.as_str()));
                    stack.push(Op::Enter(*body));
                    stack.push(Op::Bind(*binder));
                }
                Expr::Let { bind, body } => {
                    for p in &bind.pairs {
                        stack.push(Op::Unbind(m.binder(p.binder).unique.as_str()));
                    }
                    stack.push(Op::Enter(*body));
                    if bind.recursive {
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Enter(p.rhs));
                        }
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Bind(p.binder));
                        }
                    } else {
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Bind(p.binder));
                        }
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Enter(p.rhs));
                        }
                    }
                }
                Expr::Case {
                    scrut,
                    binder,
                    alts,
                    ..
                } => {
                    stack.push(Op::Unbind(m.binder(*binder).unique.as_str()));
                    for alt in alts.iter().rev() {
                        for b in &alt.binders {
                            stack.push(Op::Unbind(m.binder(*b).unique.as_str()));
                        }
                        stack.push(Op::Enter(alt.rhs));
                        for b in alt.binders.iter().rev() {
                            stack.push(Op::Bind(*b));
                        }
                    }
                    stack.push(Op::Bind(*binder));
                    stack.push(Op::Enter(*scrut));
                }
                Expr::Cast(e) | Expr::Tick(e) => stack.push(Op::Enter(*e)),
                Expr::Lit(_) | Expr::Type(_) | Expr::Coercion => {}
            }
        }
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

    /// The root of the application spine `id` belongs to, looking through
    /// the casts the simplifier leaves inside spines.
    fn spine_root(&self, id: ExprId) -> ExprId {
        let m = self.module;
        let mut root = id;
        while let Some(p) = m.parent[root as usize] {
            let through = match m.edge[root as usize] {
                Edge::AppFun => matches!(m.expr(p), Expr::App { .. }),
                Edge::Cast | Edge::Tick => {
                    matches!(m.expr(p), Expr::App { .. } | Expr::Cast(_) | Expr::Tick(_))
                }
                _ => false,
            };
            if through { root = p } else { break }
        }
        root
    }

    /// The type of an expression, when it can be read off a binder.
    fn expr_ty(&self, e: ExprId) -> Option<&'m str> {
        let m = self.module;
        let i = m.strip(e);
        match m.expr(i) {
            Expr::Var { .. } => self.resolved[i as usize].map(|b| self.binder(b).ty.as_str()),
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
            Expr::Var { .. } => self.resolved[i as usize].map(|b| ty_kind(&self.binder(b).ty)),
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
            self.regions.push(ParserRegion {
                module: m.name.clone(),
                entry: id,
                state: state_idx.map(|si| params[si]),
                cok: slot_binder[0],
                cerr: slot_binder[1],
                eok: slot_binder[2],
                eerr: slot_binder[3],
                conts,
                extra: params[end..].to_vec(),
                derived: Vec::new(),
                edges: Vec::new(),
                rejects: Vec::new(),
                evidence,
                proven: false,
            });
        }
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

    /// Classify the call rooted at `root`.
    fn call_shape(&self, root: ExprId) -> Option<CallShape> {
        let m = self.module;
        let (head, args) = m.spine(root);
        let vargs = value_args(&self.scope, &args);
        // A call to a (candidate) continuation.
        let hi = m.strip(head);
        if matches!(m.expr(hi), Expr::Var { .. })
            && let Some(b) = self.resolved[hi as usize]
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
                best = Some(CallShape::Parser {
                    state: Some(i),
                    slots: (start..end).map(|k| (k, sets[k - start])).collect(),
                    rule: R2_PARSER_CALL,
                });
            }
            i = end.max(i + 1);
        }
        if best.is_some() {
            return best;
        }
        // Worker/wrapper unboxed the state: anchor on the continuation run.
        let mut end = items.len();
        while end > 0 {
            let mut start = end;
            while start > 0 && is_cont(start - 1) {
                start -= 1;
            }
            let run: Vec<RunItem> = (start..end).map(|k| items[k].1).collect();
            if run.len() >= 2
                && items.len() - end <= 2
                && let Some(sets) = slot_sets(&run)
            {
                return Some(CallShape::Parser {
                    state: None,
                    slots: (start..end).map(|k| (k, sets[k - start])).collect(),
                    rule: R2_UNBOXED_STATE,
                });
            }
            end -= 1;
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
                let root = self.spine_root(p);
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

    //--------------------------------------------------------------------------
    // The proof
    //--------------------------------------------------------------------------

    fn prove(&mut self) {
        let m = self.module;
        let roles: Vec<(BinderId, RoleInfo)> = self.role.iter().map(|(k, v)| (*k, *v)).collect();
        for (b, info) in roles {
            let uses = self.uses.get(&b).cloned().unwrap_or_default();
            for use_at in uses {
                let (kind, prov) = self.classify_use(b, info, use_at);
                let r = &mut self.regions[info.region];
                match kind {
                    Ok(edge) => match edge {
                        Some((kind, candidates, at)) => r.edges.push(ParserEdge {
                            kind,
                            candidates,
                            at,
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
    ) -> (
        Result<Option<(EdgeKind, Vec<EdgeKind>, ExprId)>, (&'static str, String)>,
        Provenance,
    ) {
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
                let root = self.spine_root(cur);
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
                let cands: Vec<EdgeKind> = slots.iter().map(|s| s.edge()).collect();
                let first = cands[0];
                if n == arity {
                    prov.rule = R3_CONT_CALL;
                    return (Ok(Some((first, cands, root))), prov);
                }
                if n == arity + 2 {
                    prov.rule = R3_CONT_CALL_TRAILING;
                    return (Ok(Some((first, cands, root))), prov);
                }
                if n < arity
                    && let Some(owed) = self.owed_at(root)
                    && owed + n == arity
                {
                    prov.rule = R3_CONT_CALL_ETA;
                    return (Ok(Some((first, cands, root))), prov);
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
                let root = self.spine_root(parent);
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
                        match (target.kind(), slots_here.kind()) {
                            (Some(a), Some(b2)) if a == b2 => {
                                prov.rule = R4_PROP_CONT;
                                let cands: Vec<EdgeKind> =
                                    target.iter().map(|s| s.edge()).collect();
                                prov.source_nodes.push(root);
                                let first = cands[0];
                                (Ok(Some((first, cands, root))), prov)
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
        self.resolved[hi as usize]
    }

    /// The spine root a census argument site belongs to, looking through
    /// the casts the census' own `spine_root` stops at.
    pub fn site_root(&self, app: ExprId) -> ExprId {
        self.spine_root(app)
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
        let root = a.site_root(site.app);
        let head = a.resolved_head(root);
        let edge = head.and_then(|b| a.cont_edge_at(root, b));
        let (bucket, rule, reason, detail, region, edge) = match edge {
            Some((r, e)) if r.proven => {
                let b = if e.exact() {
                    Bucket::ExactRole
                } else {
                    Bucket::FiniteRoleSet
                };
                (
                    b,
                    Some(e.provenance.rule),
                    None,
                    String::new(),
                    Some(e.region),
                    Some(e.kind),
                )
            }
            Some((_, e)) => (
                Bucket::RegionRecognisedTargetUnresolved,
                None,
                Some("region-rejected"),
                String::new(),
                Some(e.region),
                None,
            ),
            None => match head.and_then(|b| a.role_of(b)) {
                Some(ri) => (
                    Bucket::RegionRecognisedTargetUnresolved,
                    None,
                    if a.regions[ri].proven {
                        Some("call-is-not-an-edge")
                    } else {
                        Some("region-rejected")
                    },
                    String::new(),
                    Some(ri),
                    None,
                ),
                None => {
                    let detail = match head {
                        Some(b) => format!("head :: {}", a.binder(b).ty),
                        None => "head is not a local binder".to_string(),
                    };
                    (
                        Bucket::RejectedNonParsec,
                        None,
                        Some("head-is-not-a-parsec-role-binder"),
                        detail,
                        None,
                        None,
                    )
                }
            },
        };
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
        assert_eq!(r.rejects.len(), 1);
        assert_eq!(r.rejects[0].reason, REJ_STATE_SLOT);
        assert!(r.rejects[0].detail.contains("argument 0"));
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
