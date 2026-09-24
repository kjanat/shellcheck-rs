//! What is *evaluated* when a constructor field is read?
//!
//! M2.2 asked which tuple allocations are plumbing. This asks a narrower
//! and strictly different question about every **other** saturated data
//! constructor — the program's own (`T_Literal`, `Parameters`,
//! `TokenComment`) and the libraries' (`Just`, `Left`, `Bin`, `State`,
//! `ParseError`): for each *field* of each construction, what does the
//! optimised Core prove about **when** the field's expression is evaluated?
//!
//! It answers evaluation only. Whether the box survives, who owns it, and
//! what a Rust representation would be are not decided here and are not
//! implied by anything below.
//!
//! # The three facts, and only then a verdict
//!
//! Every (construction, field) records three *orthogonal* facts before any
//! rep is derived, and the rep is a function of them and nothing else:
//!
//! | Fact | Values | Source |
//! |---|---|---|
//! | [`FieldDemand`] | `Always` / `Conditional` / `Never` / `Unknown` | the def-use walk's reachable observations |
//! | [`ConStrictness`] | `StrictField` / `LazyField` | GHC's `DataConInfo::strict_fields` |
//! | [`ValueRecursion`] | `RecursiveKnot` / `Acyclic` | M1's [`Class::RecursiveValue`](crate::laziness::Class) |
//!
//! # Observations, and what is reachable
//!
//! The value is followed with the [generic aggregate walk](crate::flow) —
//! through aliases, case binders, returns with argument debt,
//! known-local-call parameters, call results, storage and escapes — and
//! every place it is *observed* is recorded:
//!
//! * [`ObsKind::WhnfOnly`] — a `case` that observes the constructor and
//!   binds no field of it: a `seq`, a `DEFAULT` alternative, or an
//!   alternative that names it but binds nothing;
//! * [`ObsKind::FieldDemanded`] — an alternative binds field *i* and the
//!   binder is then used, strictly ([`D3_DEMAND_GHC`], [`D4_DEMAND_POSITION`])
//!   or lazily ([`D5_DEMAND_LAZY`]);
//! * [`ObsKind::FieldBoundUnused`] — bound by the pattern, never used;
//! * [`ObsKind::Escape`] — the value left what the walk can follow.
//!
//! Reachability is constructor-relative and is [`crate::flow`]'s job: at a
//! `case` on a value known to be `C`, only `C`'s alternative (or, failing
//! that, the `DEFAULT`) can run, so the other alternatives — and the case
//! binder's occurrences inside them — contribute nothing. A `case` with
//! neither is conservatively an escape, never "not an observation".
//!
//! # Why `Direct` is narrow
//!
//! `Direct` claims that evaluating the field where the constructor is built
//! is equivalent to leaving it where GHC put it: **timing**, not eventual
//! demand. `Foo (error "boom") \`seq\` 42` must stay `42`, and a
//! construction that crosses a return can sit while other work happens
//! before anything reads it, so "something forces it eventually" is not
//! enough. Only three things establish it, each with its own rule id:
//!
//! * [`R1_STRICT_FIELD`] — GHC already made the field strict, so it is
//!   forced at construction. GHC's own evidence (4).
//! * [`R2_FIELD_IS_VALUE`] — the field expression is already a value (a
//!   literal, a lambda, a saturated construction, a partial application, a
//!   string literal, or a variable bound to something GHC marks `whnf` /
//!   `okForSpec`): there is no evaluation to move. Structural (2).
//! * [`R3_SAME_FRONTIER`] — every observation is a scrutiny that strictly
//!   demands the field and sits at the *same evaluation frontier* as the
//!   construction: no return, no unknown call, no lambda and no conditional
//!   between the two. Structural (2) over def-use (3).
//!
//! Everything else that is demanded at all is [`FieldRep::Deferred`]. A
//! false `Direct` is a miscompile; a false `Deferred` is lost coverage.
//!
//! Evidence hierarchy, strongest first: 1 lexical binder identity, 2
//! structural shape, 3 def-use dataflow, 4 GHC type compatibility, 5
//! textual type comparison, 6 names.

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{BinderId, DataConInfo, Edge, Expr, ExprId, Module, Pair};
use serde::Serialize;

use crate::callee::{Family, split_stable_name};
use crate::flow::{
    self, Client, Consumer, Ctx, Evidence, FlowUse, R_TOO_LARGE, WhnfHow, is_list_cons,
    saturated_con,
};
use crate::laziness::{Census, Class};
use crate::scope::Scope;
use crate::shape::{ArgShape, Position, arg_shape, position};
use crate::tuples::tuple_con;

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------

/// **Population.** A saturated application of a data constructor that is
/// neither a tuple (M2.2's population) nor the list cons (M2.3c's): the
/// spine root is an `App`, the head's [`DataConInfo`] is known, and the
/// spine supplies exactly `repArity` value arguments. Identified through
/// the `DataConInfo`, never by name; the name only splits the report into
/// the program's own constructors and the libraries'. Evidence: structural
/// saturation (2) over the constructor's `DataConInfo` (4).
pub const D0_FIELD_CON: &str = "D0-FIELD-CON";
/// An observation of the construction that binds no field of it: a `seq`,
/// a `DEFAULT` alternative, or an alternative naming it that binds nothing.
/// The constructor reaches WHNF here and nothing is read. Evidence:
/// structural shape (2).
pub const D1_WHNF_ONLY: &str = "D1-WHNF-ONLY";
/// A `case` alternative for this constructor binds field *i* in a binder:
/// what happens to that binder is what happens to the field. Evidence:
/// lexical binder identity (1).
pub const D2_FIELD_BOUND: &str = "D2-FIELD-BOUND";
/// …and GHC's demand on that alternative's binder is strict: the
/// alternative's right-hand side evaluates the field whenever it runs.
/// Evidence: GHC's own demand analysis (4).
pub const D3_DEMAND_GHC: &str = "D3-DEMAND-GHC";
/// …or the binder occurs in a position that is evaluated whenever the
/// alternative is: a scrutinee, an application head, or a strict argument,
/// with only evaluating edges between it and the alternative's right-hand
/// side. Evidence: structural shape (2).
pub const D4_DEMAND_POSITION: &str = "D4-DEMAND-POSITION";
/// …or the binder is used but nothing proves it is evaluated: it is passed
/// on, stored, captured or returned. Evidence: def-use (3).
pub const D5_DEMAND_LAZY: &str = "D5-DEMAND-LAZY";
/// The alternative binds field *i* and the binder has no occurrence: the
/// field is read by nothing on this path. Evidence: lexical identity (1).
pub const D6_FIELD_UNUSED: &str = "D6-FIELD-UNUSED";
/// The value left what the walk can follow, with the walk's own
/// machine-readable reason: an import, a class-op, an exported binding, an
/// unknown higher-order callee, a constructor field this analysis does not
/// follow through. Nothing can be proven about the fields past it.
/// Evidence: structural shape (2).
pub const D7_ESCAPE: &str = "D7-ESCAPE";
/// The value is a field of *another* construction in this population: the
/// flow continues at that field's binders wherever the outer construction
/// is scrutinised, and inherits the outer's escapes. Evidence: structural
/// shape (2) over the outer's own def-use proof (3).
pub const D8_NESTED: &str = "D8-NESTED";
/// The construction is the right-hand side of a binding M1 classifies as
/// [`Class::RecursiveValue`] — a non-function member of a recursive group
/// that refers to itself — and field *i* is the one that carries the
/// reference. M1's definition is read, not re-derived. Evidence: lexical
/// binder identity (1).
pub const D9_RECURSIVE_KNOT: &str = "D9-RECURSIVE-KNOT";

/// **Direct**, by GHC's own field strictness: a strict field is forced when
/// the constructor is built, so there is no evaluation left to move.
/// Evidence: GHC (4).
pub const R1_STRICT_FIELD: &str = "R1-STRICT-FIELD";
/// **Direct**, because the field expression is already a value: a literal,
/// a lambda, a saturated construction, a partial application, a string
/// literal, or a variable bound to something GHC marks `whnf` or
/// `okForSpec`. Evidence: structural shape (2).
pub const R2_FIELD_IS_VALUE: &str = "R2-FIELD-IS-VALUE";
/// **Direct**, because every observation is a scrutiny that strictly
/// demands the field and stands at the same evaluation frontier as the
/// construction: the walk crossed no return and no unknown call, and
/// between the construction and each scrutiny there is no lambda, no
/// conditional and no thunk boundary. Evidence: structural shape (2) over
/// def-use (3).
pub const R3_SAME_FRONTIER: &str = "R3-SAME-FRONTIER";
/// **Deferred**: the field is demanded somewhere, but not on every
/// observation, or only lazily, or the timing cannot be shown to be
/// preserved. Carries a machine-readable reason.
pub const R4_DEFERRED: &str = "R4-DEFERRED";
/// **Dead**: the field is demanded by nothing reachable, it is lazy, and it
/// is not part of a knot — so there is no evaluation obligation at all.
pub const R5_DEAD: &str = "R5-DEAD";
/// **Recursive**: the field carries a value knot.
pub const R6_RECURSIVE: &str = "R6-RECURSIVE";
/// **Unknown**: the construction escapes, so what is demanded of the field
/// is outside what this module proves. Carries the escape's reason.
pub const R7_UNKNOWN: &str = "R7-UNKNOWN";

// Reasons. `Deferred` reasons say what is missing from a `Direct` proof;
// `Unknown` reasons are the walk's own escape reasons.
pub const R_WHNF_WITHOUT_FIELD: &str = "observed-at-whnf-without-demanding-the-field";
pub const R_SOME_PATHS_ONLY: &str = "demanded-on-some-observations-only";
pub const R_LAZY_ONLY: &str = "demanded-only-lazily";
pub const R_BOUND_UNUSED_SOMEWHERE: &str = "bound-and-unused-on-some-observation";
pub const R_TIMING_NOT_PRESERVED: &str = "demanded-on-every-path-but-not-at-the-same-frontier";
/// The construction this one is stored in escapes, so the field reads that
/// reach it through the outer box are not all visible.
pub const R_OUTER_ESCAPES: &str = "the-construction-holding-it-escapes";
/// …and the holder is one of the program's own constructors. Split out so
/// that M2.3f can tell a residue it can still close (the holder is in this
/// population and in this program) from one it cannot.
pub const R_OUTER_ESCAPES_PROGRAM: &str = "the-program-construction-holding-it-escapes";
/// …and the holder is a library constructor.
pub const R_OUTER_ESCAPES_LIBRARY: &str = "the-library-construction-holding-it-escapes";
/// Stored in a **list cell**: M2.3c's population, and its flows say what
/// happens to it.
pub const R_STORED_IN_LIST_CELL: &str = "stored-in-a-list-cell";
/// Stored in a **tuple** field: M2.2's population.
pub const R_STORED_IN_TUPLE: &str = "stored-in-a-tuple-field";
/// Stored in a constructor that is not in any of the three populations —
/// an unsaturated or over-applied constructor application.
pub const R_STORED_IN_OTHER: &str = "stored-in-a-construction-outside-every-population";

/// How many rounds the nesting fixpoint may take before it is a bug.
const NESTING_ROUNDS: usize = 32;

//------------------------------------------------------------------------------
// The three facts
//------------------------------------------------------------------------------

/// What the reachable observations demand of one field. Fact 1 of 3: it
/// says nothing about *when*.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum FieldDemand {
    /// Every observation of the construction demands the field strictly.
    Always,
    /// Some observation demands it; not every one of them, or not strictly.
    Conditional,
    /// No reachable observation demands it.
    Never,
    /// The construction escapes: what is demanded is not visible here.
    Unknown,
}

/// GHC's own field strictness. Fact 2 of 3.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ConStrictness {
    /// `DataConInfo::strict_fields[i]` is false.
    LazyField,
    /// …is true: the field is forced when the constructor is built.
    StrictField,
}

/// Whether the field carries a value knot, in M1's sense. Fact 3 of 3.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ValueRecursion {
    Acyclic,
    /// The construction is the right-hand side of a binding M1 calls
    /// [`Class::RecursiveValue`], and this field refers back to the group.
    RecursiveKnot,
}

/// The derived representation of one field. Never assigned directly: it is
/// a function of the three facts above and of the timing proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum FieldRep {
    Dead,
    Direct,
    Deferred,
    Recursive,
    Unknown,
}

impl FieldRep {
    pub fn name(self) -> &'static str {
        match self {
            FieldRep::Dead => "Dead",
            FieldRep::Direct => "Direct",
            FieldRep::Deferred => "Deferred",
            FieldRep::Recursive => "Recursive",
            FieldRep::Unknown => "Unknown",
        }
    }

    /// Rank for aggregating one DataCon field over its constructions: the
    /// weakest claim wins, and `Dead` yields to any real demand.
    fn rank(self) -> u8 {
        match self {
            FieldRep::Dead => 0,
            FieldRep::Direct => 1,
            FieldRep::Deferred => 2,
            FieldRep::Recursive => 3,
            FieldRep::Unknown => 4,
        }
    }

    pub fn join(self, other: FieldRep) -> FieldRep {
        if other.rank() > self.rank() {
            other
        } else {
            self
        }
    }
}

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ObsKind {
    /// The constructor reached WHNF and no field of it was bound.
    WhnfOnly,
    /// An alternative bound the field and the binder is used.
    FieldDemanded,
    /// An alternative bound the field and the binder has no occurrence.
    FieldBoundUnused,
    /// The value left what the walk follows.
    Escape,
}

/// How a field binder is used on one observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum DemandHow {
    /// GHC's demand on the alternative's binder is strict ([`D3_DEMAND_GHC`]).
    StrictByGhc,
    /// The binder is evaluated whenever the alternative runs, by position
    /// ([`D4_DEMAND_POSITION`]).
    StrictByPosition,
    /// Used, but nothing proves it is evaluated ([`D5_DEMAND_LAZY`]).
    Lazy,
}

impl DemandHow {
    pub fn strict(self) -> bool {
        !matches!(self, DemandHow::Lazy)
    }

    pub fn rule(self) -> &'static str {
        match self {
            DemandHow::StrictByGhc => D3_DEMAND_GHC,
            DemandHow::StrictByPosition => D4_DEMAND_POSITION,
            DemandHow::Lazy => D5_DEMAND_LAZY,
        }
    }
}

/// One place the construction is observed. A `FieldDemanded` /
/// `FieldBoundUnused` observation is recorded once per field of the
/// alternative; a `WhnfOnly` or `Escape` once per site.
#[derive(Debug, Clone, Serialize)]
pub struct Observation {
    pub kind: ObsKind,
    /// The `case` or escape site.
    pub at: ExprId,
    /// Which field, for the per-field kinds.
    pub field: Option<u32>,
    /// The alternative's binder that field landed in, for the per-field
    /// kinds: where a value stored in this field can be followed to.
    pub binder: Option<BinderId>,
    pub how: Option<DemandHow>,
    /// For `WhnfOnly`, how the case came to read nothing.
    pub whnf: Option<WhnfHow>,
    /// For `Escape`, the walk's own reason.
    pub why: Option<&'static str>,
    pub detail: String,
    pub rule: &'static str,
}

/// One field of one construction: the three facts, then the rep.
#[derive(Debug, Clone, Serialize)]
pub struct FieldVerdict {
    pub index: u32,
    pub demand: FieldDemand,
    pub strictness: ConStrictness,
    pub recursion: ValueRecursion,
    /// The construction forces the field on reaching WHNF even though
    /// nothing demands it: a strict field nobody reads. Reported on its own
    /// row rather than as `Dead`.
    pub force_on_whnf: bool,
    pub rep: FieldRep,
    pub rule: &'static str,
    /// For a [`FieldRep::Direct`] verdict: **every** route that proves the
    /// timing, not only the one the derivation happened to reach first.
    /// [`FieldVerdict::rule`] is the first of them; this is what makes the
    /// overlap between the three rules visible (M2.3f's route-set
    /// histogram). Empty for every other rep.
    pub routes: Vec<&'static str>,
    pub reason: Option<&'static str>,
    pub detail: String,
    pub evidence: Vec<Evidence>,
}

impl FieldVerdict {
    /// The route set as one histogram key: `R1`, `R2`, `R1+R2`, …
    pub fn route_key(&self) -> String {
        if self.routes.is_empty() {
            return "none".to_string();
        }
        self.routes
            .iter()
            .map(|r| match *r {
                R1_STRICT_FIELD => "R1",
                R2_FIELD_IS_VALUE => "R2",
                R3_SAME_FRONTIER => "R3",
                other => other,
            })
            .collect::<Vec<_>>()
            .join("+")
    }

    pub fn reason_key(&self) -> Option<String> {
        let r = self.reason?;
        Some(if self.detail.is_empty() {
            r.to_string()
        } else {
            format!("{r} ({})", self.detail)
        })
    }
}

/// One saturated non-tuple, non-list construction and everything proven
/// about its fields.
#[derive(Debug, Clone, Serialize)]
pub struct FieldFlow {
    pub module: String,
    /// Spine root of the constructor application.
    pub construction: ExprId,
    /// GHC's stable name of the constructor; a diagnostic and the key the
    /// per-DataCon aggregation groups on.
    pub con: String,
    pub occ: String,
    /// Defined in ShellCheck itself, as opposed to a library.
    pub program: bool,
    pub arity: u32,
    /// The value arguments, in field order.
    pub fields: Vec<ExprId>,
    pub strict_fields: Vec<bool>,
    pub bound: Option<BinderId>,
    pub observations: Vec<Observation>,
    /// Escapes, as (reason, detail, node).
    pub escapes: Vec<(&'static str, String, ExprId)>,
    pub verdicts: Vec<FieldVerdict>,
    pub returned: bool,
    pub locations: usize,
    pub over_budget: bool,
    pub unreachable_alts: usize,
    pub alias_occurrences_unreachable: usize,
    pub evidence: Vec<Evidence>,
}

impl FieldFlow {
    /// Was the construction observed anywhere at all?
    pub fn observed(&self) -> bool {
        self.observations.iter().any(|o| o.kind != ObsKind::Escape)
    }

    pub fn escaped(&self) -> bool {
        !self.escapes.is_empty() || self.over_budget
    }
}

//------------------------------------------------------------------------------
// The client
//------------------------------------------------------------------------------

/// Where a construction's *i*-th field can be followed to when the value is
/// stored in it.
#[derive(Debug, Clone, Default)]
struct NestedTarget {
    seeds: Vec<ExprId>,
    /// The holder's own flow escapes, so the reads that reach this value
    /// through it are not all visible.
    escaped: bool,
}

type Nested = HashMap<(ExprId, usize), NestedTarget>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FieldUse {
    Flow(FlowUse),
    /// A field of another construction whose own flow this one continues
    /// through ([`D8_NESTED`]).
    NestedIn {
        outer: ExprId,
    },
}

impl Consumer for FieldUse {
    fn at(self) -> ExprId {
        match self {
            FieldUse::Flow(u) => u.at(),
            FieldUse::NestedIn { outer } => outer,
        }
    }
}

impl From<FlowUse> for FieldUse {
    fn from(u: FlowUse) -> FieldUse {
        FieldUse::Flow(u)
    }
}

struct FieldClient<'a> {
    /// Constructions in the population, so a store into one of them can be
    /// recognised as a hop rather than an escape.
    population: &'a HashSet<ExprId>,
    nested: &'a Nested,
    /// Is this value stored in a field of another construction in the
    /// population? Then re-running it once that construction's own flow is
    /// known can resolve the hop, and the fixpoint has to come back to it.
    nests: bool,
}

impl Client for FieldClient<'_> {
    type Use = FieldUse;

    /// A field of another construction in the population: the reads of that
    /// construction's *i*-th field binder are reads of this value
    /// ([`D8_NESTED`]). The holder's escapes come with it — if the outer box
    /// is handed out, so is this value.
    fn on_stored(
        &mut self,
        w: &mut flow::Walk<FieldUse>,
        _cx: &Ctx<'_, '_>,
        root: ExprId,
        idx: usize,
        dc: &DataConInfo,
        occ: &str,
    ) -> Option<&'static str> {
        if !self.population.contains(&root) {
            // Which population owns the holder decides who can close this
            // residue, so say it here rather than leaving one reason for
            // all of them.
            return Some(if is_list_cons(&dc.name) {
                R_STORED_IN_LIST_CELL
            } else if tuple_con(&dc.name, dc.rep_arity).is_some() {
                R_STORED_IN_TUPLE
            } else {
                R_STORED_IN_OTHER
            });
        }
        self.nests = true;
        let Some(t) = self.nested.get(&(root, idx)) else {
            return Some(flow::R_STORED_CON);
        };
        w.use_(FieldUse::NestedIn { outer: root });
        w.evidence.push(Evidence {
            rule: D8_NESTED,
            nodes: vec![root],
            binder: None,
            note: format!(
                "field {idx} of {occ}: {} use(s) of that field follow",
                t.seeds.len()
            ),
        });
        if t.escaped {
            let why = if is_program_con(&dc.name) {
                R_OUTER_ESCAPES_PROGRAM
            } else {
                R_OUTER_ESCAPES_LIBRARY
            };
            w.escape_at(root, false, why, occ.to_string());
        }
        for seed in &t.seeds {
            w.push(*seed, 0);
        }
        None
    }
}

//------------------------------------------------------------------------------
// The analysis
//------------------------------------------------------------------------------

pub struct Fields<'m> {
    pub module: &'m Module,
    pub flows: Vec<FieldFlow>,
    scope: Scope<'m>,
    index: HashMap<ExprId, usize>,
    population: HashSet<ExprId>,
    top_pairs: Vec<BinderId>,
    /// Flattened top-level pair index -> whether its group is recursive.
    top_rec: Vec<bool>,
    /// Bindings M1 classifies as `RecursiveValue`, by right-hand-side node.
    m1_recursive: HashSet<ExprId>,
    pub nesting_rounds: usize,
}

impl<'m> Fields<'m> {
    /// Census one module. `census` is M1's, read only for its
    /// [`Class::RecursiveValue`] verdicts — the knot definition is M1's and
    /// is not re-derived here.
    pub fn of_module(m: &'m Module, census: &Census) -> Fields<'m> {
        let m1_recursive: HashSet<ExprId> = census
            .bindings
            .iter()
            .filter(|b| b.module == m.name && b.class == Class::RecursiveValue)
            .map(|b| b.rhs)
            .collect();
        let mut top_rec = Vec::new();
        for bind in &m.top {
            for _ in &bind.pairs {
                top_rec.push(bind.recursive);
            }
        }
        let mut f = Fields {
            module: m,
            flows: Vec::new(),
            scope: Scope::new(m),
            index: HashMap::new(),
            population: HashSet::new(),
            top_pairs: m
                .top
                .iter()
                .flat_map(|b| b.pairs.iter())
                .map(|p| p.binder)
                .collect(),
            top_rec,
            m1_recursive,
            nesting_rounds: 0,
        };
        f.find_constructions();
        f.resolve_flows();
        f
    }

    pub fn flow_at(&self, node: ExprId) -> Option<&FieldFlow> {
        self.index.get(&node).map(|i| &self.flows[*i])
    }

    /// Every saturated construction that is neither a tuple nor a list cell
    /// ([`D0_FIELD_CON`]).
    fn find_constructions(&mut self) {
        let m = self.module;
        for id in 0..m.exprs.len() as ExprId {
            let Some((dc, head, vargs)) = saturated_con(&self.scope, id) else {
                continue;
            };
            if tuple_con(&dc.name, dc.rep_arity).is_some() || is_list_cons(&dc.name) {
                continue;
            }
            if dc.rep_arity == 0 {
                continue;
            }
            let occ = match m.expr(head) {
                Expr::Var { occ, .. } => occ.clone(),
                _ => String::new(),
            };
            // GHC reports strictness per *source* field; when the
            // representation has a different number of fields there is no
            // per-field verdict to read and every field is treated as lazy.
            let strict_fields = if dc.strict_fields.len() == dc.rep_arity as usize {
                dc.strict_fields.clone()
            } else {
                vec![false; dc.rep_arity as usize]
            };
            self.index.insert(id, self.flows.len());
            self.population.insert(id);
            self.flows.push(FieldFlow {
                module: m.name.clone(),
                construction: id,
                con: dc.name.clone(),
                occ: occ.clone(),
                program: is_program_con(&dc.name),
                arity: dc.rep_arity,
                fields: vargs,
                strict_fields,
                bound: None,
                observations: Vec::new(),
                escapes: Vec::new(),
                verdicts: Vec::new(),
                returned: false,
                locations: 0,
                over_budget: false,
                unreachable_alts: 0,
                alias_occurrences_unreachable: 0,
                evidence: vec![Evidence {
                    rule: D0_FIELD_CON,
                    nodes: vec![id, head],
                    binder: None,
                    note: format!(
                        "{} of repArity {} ({}), {} strict field(s)",
                        occ,
                        dc.rep_arity,
                        dc.name,
                        dc.strict_fields.iter().filter(|s| **s).count()
                    ),
                }],
            });
        }
    }

    /// Resolve every flow, then iterate the ones that hop through another
    /// construction's field until the nesting settles. Starts pessimistic —
    /// nothing is followed through a field — and only ever *adds* hops, so
    /// a cycle cannot bootstrap itself into being followed.
    fn resolve_flows(&mut self) {
        let n = self.flows.len();
        let empty: Nested = Nested::new();
        let mut nests = vec![false; n];
        for (i, h) in nests.iter_mut().enumerate() {
            *h = self.run_flow(i, &empty);
        }
        let mut rounds = 0;
        loop {
            let nested = self.nested_targets();
            let before: Vec<Vec<FieldRep>> = self
                .flows
                .iter()
                .map(|f| f.verdicts.iter().map(|v| v.rep).collect())
                .collect();
            let again: Vec<usize> = (0..n).filter(|i| nests[*i]).collect();
            for i in again {
                nests[i] = self.run_flow(i, &nested);
            }
            rounds += 1;
            let after: Vec<Vec<FieldRep>> = self
                .flows
                .iter()
                .map(|f| f.verdicts.iter().map(|v| v.rep).collect())
                .collect();
            if before == after {
                break;
            }
            assert!(
                rounds < NESTING_ROUNDS,
                "field nesting did not settle in {NESTING_ROUNDS} rounds"
            );
        }
        self.nesting_rounds = rounds;
    }

    /// Where a construction's *i*-th field is read, for a **different**
    /// population: the occurrences of the field binder at every alternative
    /// that binds it, and whether the holder's own flow escaped. This is
    /// [`D8_NESTED`]'s map, published so that M2.3c can mirror the rule for
    /// a list stored in a constructor field — the case this census
    /// deliberately stops at. Nothing here reads it; no verdict changes.
    pub fn field_reads(&self) -> HashMap<(ExprId, usize), (Vec<ExprId>, bool)> {
        self.nested_targets()
            .into_iter()
            .map(|(k, t)| (k, (t.seeds, t.escaped)))
            .collect()
    }

    /// Where a construction's *i*-th field goes: the occurrences of the
    /// field binder at every alternative that binds it.
    fn nested_targets(&self) -> Nested {
        let m = self.module;
        let mut out: Nested = Nested::new();
        for f in &self.flows {
            for idx in 0..f.arity as usize {
                let mut seeds = Vec::new();
                for o in &f.observations {
                    if o.field != Some(idx as u32) {
                        continue;
                    }
                    if let Some(b) = o.binder {
                        seeds.extend(m.occurrences(b).iter().copied());
                    }
                }
                out.insert(
                    (f.construction, idx),
                    NestedTarget {
                        seeds,
                        escaped: f.escaped(),
                    },
                );
            }
        }
        out
    }

    fn run_flow(&mut self, i: usize, nested: &Nested) -> bool {
        let construction = self.flows[i].construction;
        let cx = Ctx {
            m: self.module,
            scope: &self.scope,
            top_pairs: &self.top_pairs,
            start: construction,
            arity: self.flows[i].arity,
            con: saturated_con(&self.scope, construction).map(|(dc, _, _)| dc),
        };
        let mut client = FieldClient {
            population: &self.population,
            nested,
            nests: false,
        };
        let w = flow::walk(&cx, &mut client);
        let nests = client.nests;
        let (observations, mut evidence) = self.observations(&w);
        let escapes: Vec<(&'static str, String, ExprId)> = w
            .escapes
            .iter()
            .map(|(_, why, detail, at)| (*why, detail.clone(), *at))
            .collect();
        let f = &mut self.flows[i];
        f.bound = w.bound;
        f.returned = w.returned;
        f.locations = w.locations;
        f.over_budget = w.over_budget;
        f.unreachable_alts = w.unreachable_alts;
        f.alias_occurrences_unreachable = w.alias_occurrences_unreachable;
        f.observations = observations;
        f.escapes = escapes;
        f.evidence.truncate(1);
        f.evidence.extend(w.evidence.iter().cloned());
        f.evidence.append(&mut evidence);
        let verdicts = self.decide(i, &w);
        self.flows[i].verdicts = verdicts;
        nests
    }

    /// Turn the walk's accepted scrutinies, WHNF observations and escapes
    /// into per-field observations.
    fn observations(&self, w: &flow::Walk<FieldUse>) -> (Vec<Observation>, Vec<Evidence>) {
        let m = self.module;
        let mut obs = Vec::new();
        let mut ev = Vec::new();
        for s in &w.scrutinies {
            for (idx, b) in s.field_binders.iter().enumerate() {
                let occs = m.occurrences(*b);
                if occs.is_empty() {
                    obs.push(Observation {
                        kind: ObsKind::FieldBoundUnused,
                        at: s.case,
                        field: Some(idx as u32),
                        binder: Some(*b),
                        how: None,
                        whnf: None,
                        why: None,
                        detail: m.binder(*b).occ.clone(),
                        rule: D6_FIELD_UNUSED,
                    });
                    continue;
                }
                let how = self.demand_of(*b, s.rhs);
                obs.push(Observation {
                    kind: ObsKind::FieldDemanded,
                    at: s.case,
                    field: Some(idx as u32),
                    binder: Some(*b),
                    how: Some(how),
                    whnf: None,
                    why: None,
                    detail: m.binder(*b).occ.clone(),
                    rule: how.rule(),
                });
            }
            ev.push(Evidence {
                rule: D2_FIELD_BOUND,
                nodes: vec![s.case, s.at],
                binder: None,
                note: format!("{} field binder(s) bound", s.field_binders.len()),
            });
        }
        for u in &w.consumers {
            let (case, how) = match u {
                FieldUse::Flow(FlowUse::Forced { case }) => (*case, WhnfHow::Forced),
                FieldUse::Flow(FlowUse::Whnf { case, how }) => (*case, *how),
                _ => continue,
            };
            obs.push(Observation {
                kind: ObsKind::WhnfOnly,
                at: case,
                field: None,
                binder: None,
                how: None,
                whnf: Some(how),
                why: None,
                detail: how.name().to_string(),
                rule: D1_WHNF_ONLY,
            });
        }
        for (_, why, detail, at) in &w.escapes {
            obs.push(Observation {
                kind: ObsKind::Escape,
                at: *at,
                field: None,
                binder: None,
                how: None,
                whnf: None,
                why: Some(why),
                detail: detail.clone(),
                rule: D7_ESCAPE,
            });
        }
        if w.over_budget {
            obs.push(Observation {
                kind: ObsKind::Escape,
                at: w.consumers.first().map(|u| u.at()).unwrap_or(0),
                field: None,
                binder: None,
                how: None,
                whnf: None,
                why: Some(R_TOO_LARGE),
                detail: String::new(),
                rule: D7_ESCAPE,
            });
        }
        (obs, ev)
    }

    /// How the alternative's binder `b` is used inside the alternative's
    /// right-hand side `rhs`.
    fn demand_of(&self, b: BinderId, rhs: ExprId) -> DemandHow {
        let m = self.module;
        if m.binder(b)
            .demand
            .as_ref()
            .is_some_and(|d| d.strict && !d.absent)
        {
            return DemandHow::StrictByGhc;
        }
        if m.occurrences(b)
            .iter()
            .any(|o| evaluated_within(&self.scope, *o, rhs))
        {
            return DemandHow::StrictByPosition;
        }
        DemandHow::Lazy
    }

    //--------------------------------------------------------------------------
    // The three facts, and the rep derived from them
    //--------------------------------------------------------------------------

    fn decide(&self, i: usize, w: &flow::Walk<FieldUse>) -> Vec<FieldVerdict> {
        let f = &self.flows[i];
        let escaped = f.escaped();
        let first_escape = f.escapes.first().cloned();
        let recursive = self.recursion(f);
        (0..f.arity)
            .map(|idx| {
                let strictness = if f.strict_fields[idx as usize] {
                    ConStrictness::StrictField
                } else {
                    ConStrictness::LazyField
                };
                let recursion = if recursive.contains(&idx) {
                    ValueRecursion::RecursiveKnot
                } else {
                    ValueRecursion::Acyclic
                };
                let (demand, why) = self.demand(f, idx, escaped);
                let mut evidence = Vec::new();
                let force_on_whnf =
                    demand == FieldDemand::Never && strictness == ConStrictness::StrictField;
                let (rep, rule, reason, detail) = if recursion == ValueRecursion::RecursiveKnot {
                    evidence.push(Evidence {
                        rule: D9_RECURSIVE_KNOT,
                        nodes: vec![f.construction, f.fields[idx as usize]],
                        binder: f.bound,
                        note: "M1 calls this binding a recursive value; the field refers back"
                            .into(),
                    });
                    (FieldRep::Recursive, R6_RECURSIVE, None, String::new())
                } else if strictness == ConStrictness::StrictField {
                    evidence.push(Evidence {
                        rule: R1_STRICT_FIELD,
                        nodes: vec![f.construction],
                        binder: None,
                        note: "GHC makes the field strict: it is forced at construction".into(),
                    });
                    (FieldRep::Direct, R1_STRICT_FIELD, None, String::new())
                } else if demand == FieldDemand::Unknown {
                    let (r, d) = first_escape
                        .clone()
                        .map(|(why, detail, _)| (why, detail))
                        .unwrap_or((R_TOO_LARGE, String::new()));
                    evidence.push(Evidence {
                        rule: D7_ESCAPE,
                        nodes: vec![first_escape.as_ref().map(|e| e.2).unwrap_or(f.construction)],
                        binder: None,
                        note: r.to_string(),
                    });
                    (FieldRep::Unknown, R7_UNKNOWN, Some(r), d)
                } else if demand == FieldDemand::Never {
                    (FieldRep::Dead, R5_DEAD, None, String::new())
                } else if demand == FieldDemand::Always {
                    match self.timing(f, idx, w) {
                        Some((rule, note)) => {
                            evidence.push(Evidence {
                                rule,
                                nodes: vec![f.construction, f.fields[idx as usize]],
                                binder: None,
                                note,
                            });
                            (FieldRep::Direct, rule, None, String::new())
                        }
                        None => (
                            FieldRep::Deferred,
                            R4_DEFERRED,
                            Some(R_TIMING_NOT_PRESERVED),
                            String::new(),
                        ),
                    }
                } else {
                    (
                        FieldRep::Deferred,
                        R4_DEFERRED,
                        Some(why.unwrap_or(R_SOME_PATHS_ONLY)),
                        String::new(),
                    )
                };
                let routes = if rep == FieldRep::Direct {
                    self.routes(f, idx, w)
                } else {
                    Vec::new()
                };
                debug_assert!(
                    rep != FieldRep::Direct || routes.contains(&rule),
                    "the rule that proved Direct must be one of the routes"
                );
                FieldVerdict {
                    index: idx,
                    demand,
                    strictness,
                    recursion,
                    force_on_whnf,
                    rep,
                    rule,
                    routes,
                    reason,
                    detail,
                    evidence,
                }
            })
            .collect()
    }

    /// Fact 1: what the reachable observations demand of field `idx`, and
    /// what is missing from `Always` when it is not.
    fn demand(
        &self,
        f: &FieldFlow,
        idx: u32,
        escaped: bool,
    ) -> (FieldDemand, Option<&'static str>) {
        if escaped {
            return (FieldDemand::Unknown, None);
        }
        let mut sites = 0usize;
        let mut strict = 0usize;
        let mut lazy = 0usize;
        let mut unused = 0usize;
        let mut whnf = 0usize;
        for o in &f.observations {
            match o.kind {
                ObsKind::WhnfOnly => {
                    sites += 1;
                    whnf += 1;
                }
                ObsKind::FieldDemanded if o.field == Some(idx) => {
                    sites += 1;
                    if o.how.is_some_and(|h| h.strict()) {
                        strict += 1;
                    } else {
                        lazy += 1;
                    }
                }
                ObsKind::FieldBoundUnused if o.field == Some(idx) => {
                    sites += 1;
                    unused += 1;
                }
                _ => {}
            }
        }
        if strict + lazy == 0 {
            return (FieldDemand::Never, None);
        }
        if strict == sites {
            return (FieldDemand::Always, None);
        }
        let why = if whnf > 0 {
            R_WHNF_WITHOUT_FIELD
        } else if unused > 0 {
            R_BOUND_UNUSED_SOMEWHERE
        } else if strict == 0 {
            R_LAZY_ONLY
        } else {
            R_SOME_PATHS_ONLY
        };
        (FieldDemand::Conditional, Some(why))
    }

    /// Fact 3: which fields carry a value knot. M1 decides whether the
    /// *binding* is a recursive value ([`Class::RecursiveValue`]); this only
    /// says which field the reference goes through.
    fn recursion(&self, f: &FieldFlow) -> HashSet<u32> {
        let m = self.module;
        let mut out = HashSet::new();
        // The binding this construction is the right-hand side of.
        let Some((group, is_rec, rhs)) = self.enclosing_group(f.construction) else {
            return out;
        };
        if !is_rec {
            return out;
        }
        // M1's verdict where M1 has one (let-bound); at top level M1 reports
        // no class, and the group's own recursion flag is what there is.
        let knot =
            self.m1_recursive.contains(&rhs) || matches!(m.edge[rhs as usize], Edge::Top { .. });
        if !knot {
            return out;
        }
        for (idx, field) in f.fields.iter().enumerate() {
            let refers = m
                .preorder(*field)
                .any(|n| m.resolve(n).is_some_and(|b| group.contains(&b)));
            if refers {
                out.insert(idx as u32);
            }
        }
        out
    }

    /// The binder group whose right-hand side this node is, if it is one:
    /// the group's binders, whether the group is recursive, and the
    /// right-hand-side node M1 keys its report on.
    fn enclosing_group(&self, at: ExprId) -> Option<(HashSet<BinderId>, bool, ExprId)> {
        let m = self.module;
        // Casts and ticks around a right-hand side do not break it.
        let mut cur = at;
        loop {
            match m.edge[cur as usize] {
                Edge::Cast | Edge::Tick => cur = m.parent[cur as usize]?,
                Edge::LetRhs { pair } => {
                    let parent = m.parent[cur as usize]?;
                    let Expr::Let { bind, .. } = m.expr(parent) else {
                        return None;
                    };
                    let _ = pair;
                    return Some((
                        bind.pairs.iter().map(|p| p.binder).collect(),
                        bind.recursive,
                        cur,
                    ));
                }
                Edge::Top { pair } => {
                    let rec = self.top_rec.get(pair as usize).copied().unwrap_or(false);
                    // Every pair of the same top-level group.
                    let mut group = HashSet::new();
                    let mut i = 0usize;
                    for bind in &m.top {
                        let n = bind.pairs.len();
                        if (i..i + n).contains(&(pair as usize)) {
                            group.extend(bind.pairs.iter().map(|p| p.binder));
                        }
                        i += n;
                    }
                    return Some((group, rec, cur));
                }
                _ => return None,
            }
        }
    }

    /// Is evaluating field `idx` where the constructor is built equivalent
    /// to leaving it where GHC put it? Returns the rule that proves it.
    fn timing(
        &self,
        f: &FieldFlow,
        idx: u32,
        w: &flow::Walk<FieldUse>,
    ) -> Option<(&'static str, String)> {
        // (b) There is no evaluation to move.
        if field_is_value(&self.scope, f.fields[idx as usize]) {
            return Some((
                R2_FIELD_IS_VALUE,
                format!(
                    "the field expression is already a value ({:?})",
                    arg_shape(&self.scope, f.fields[idx as usize])
                ),
            ));
        }
        self.r3_frontier(f, idx, w)
    }

    /// (c) The force sits at the same evaluation frontier as the
    /// construction: nothing may run in between. Split out of
    /// [`Fields::timing`] so that the route-set histogram can ask each rule
    /// separately instead of only seeing the first one that fired.
    fn r3_frontier(
        &self,
        f: &FieldFlow,
        idx: u32,
        w: &flow::Walk<FieldUse>,
    ) -> Option<(&'static str, String)> {
        if f.returned || f.escaped() {
            return None;
        }
        if w.consumers.iter().any(|u| {
            matches!(
                u,
                FieldUse::Flow(FlowUse::PassedTo { .. })
                    | FieldUse::Flow(FlowUse::PassedToUnknown { .. })
                    | FieldUse::NestedIn { .. }
            )
        }) {
            return None;
        }
        let scrutinies: Vec<ExprId> = f
            .observations
            .iter()
            .filter(|o| o.kind == ObsKind::FieldDemanded && o.field == Some(idx))
            .map(|o| o.at)
            .collect();
        if scrutinies.is_empty() {
            return None;
        }
        if !scrutinies
            .iter()
            .all(|c| same_frontier(&self.scope, f.construction, *c))
        {
            return None;
        }
        Some((
            R3_SAME_FRONTIER,
            format!(
                "{} scrutin(y/ies) at the construction's own evaluation frontier",
                scrutinies.len()
            ),
        ))
    }

    /// Every route that proves a `Direct` timing for this field, in rule
    /// order. The derivation stops at the first one; this asks all three,
    /// so that the overlap between them is visible rather than hidden by
    /// the order they are tried in.
    fn routes(&self, f: &FieldFlow, idx: u32, w: &flow::Walk<FieldUse>) -> Vec<&'static str> {
        let mut out = Vec::new();
        if f.strict_fields[idx as usize] {
            out.push(R1_STRICT_FIELD);
        }
        if field_is_value(&self.scope, f.fields[idx as usize]) {
            out.push(R2_FIELD_IS_VALUE);
        }
        if self.r3_frontier(f, idx, w).is_some() {
            out.push(R3_SAME_FRONTIER);
        }
        out
    }
}

//------------------------------------------------------------------------------
// Shared predicates
//------------------------------------------------------------------------------

/// Is this constructor defined in ShellCheck itself? The same test the M2
/// census' family attribution uses, and a *diagnostic* split only: no
/// verdict depends on it.
pub fn is_program_con(name: &str) -> bool {
    match split_stable_name(name) {
        Some((unit, module, _)) => {
            unit == "main" || module.starts_with("ShellCheck") || module == "Main"
        }
        None => false,
    }
}

/// Does the parent of `child` evaluate it whenever the parent itself is
/// evaluated?
pub(crate) fn evaluates(s: &Scope, child: ExprId) -> bool {
    match s.m.edge[child as usize] {
        Edge::CaseScrut | Edge::AppFun | Edge::Cast | Edge::Tick | Edge::LetBody => true,
        // Only if the callee is strict in that argument.
        Edge::AppArg => position(s, child) == Position::StrictArg,
        _ => false,
    }
}

/// Is `at` evaluated whenever `root` is — with only evaluating edges in
/// between? An occurrence that *is* `root` is not: returning a binder does
/// not force it.
pub(crate) fn evaluated_within(s: &Scope, at: ExprId, root: ExprId) -> bool {
    let m = s.m;
    let mut cur = at;
    if cur == root {
        return false;
    }
    loop {
        if !evaluates(s, cur) {
            return false;
        }
        let Some(p) = m.parent[cur as usize] else {
            return false;
        };
        if p == root {
            return true;
        }
        cur = p;
    }
}

/// Does the `case` at `at` run at the same evaluation frontier as the
/// construction — no lambda, no conditional, no thunk and no call in
/// between? Both nodes are related through their nearest common ancestor:
/// the construction's own path up to it may not cross a lambda, and the
/// case's path up to it must be all evaluating edges.
fn same_frontier(s: &Scope, construction: ExprId, at: ExprId) -> bool {
    let m = s.m;
    let mut chain: Vec<ExprId> = vec![construction];
    chain.extend(m.ancestors(construction));
    let pos: HashMap<ExprId, usize> = chain.iter().enumerate().map(|(i, n)| (*n, i)).collect();
    let mut cur = at;
    loop {
        if let Some(i) = pos.get(&cur) {
            return chain[..*i]
                .iter()
                .all(|n| m.edge[*n as usize] != Edge::LamBody);
        }
        if !evaluates(s, cur) {
            return false;
        }
        let Some(p) = m.parent[cur as usize] else {
            return false;
        };
        cur = p;
    }
}

/// Is the field expression already a value, so that evaluating it moves no
/// work and cannot introduce divergence? Syntactic values count, as does a
/// nullary data constructor; a bare variable counts only when GHC's own
/// flags say its binding is one.
fn field_is_value(s: &Scope, id: ExprId) -> bool {
    let m = s.m;
    let inner = m.strip(id);
    if matches!(m.expr(inner), Expr::Lit(_)) {
        return true;
    }
    match arg_shape(s, id) {
        ArgShape::Closure | ArgShape::ConApp | ArgShape::PartialApp | ArgShape::StringLiteral => {
            true
        }
        ArgShape::Trivial => {
            // A nullary data constructor is a value on its own.
            if s.head_sig(inner)
                .and_then(|x| x.data_con)
                .is_some_and(|dc| dc.rep_arity == 0)
            {
                return true;
            }
            match m.resolve(inner).map(|b| m.binding(b)) {
                Some(bi) => bi
                    .rhs
                    .and_then(|rhs| pair_flags(m, rhs))
                    .is_some_and(|p| p.whnf || p.ok_for_spec),
                None => false,
            }
        }
        ArgShape::Computation => false,
    }
}

/// GHC's flags for the binding pair whose right-hand side is `rhs`.
fn pair_flags(m: &Module, rhs: ExprId) -> Option<&Pair> {
    match m.edge[rhs as usize] {
        Edge::LetRhs { pair } => {
            let parent = m.parent[rhs as usize]?;
            let Expr::Let { bind, .. } = m.expr(parent) else {
                return None;
            };
            bind.pairs.get(pair as usize)
        }
        Edge::Top { pair } => {
            let mut i = 0usize;
            for bind in &m.top {
                if (pair as usize) < i + bind.pairs.len() {
                    return bind.pairs.get(pair as usize - i);
                }
                i += bind.pairs.len();
            }
            None
        }
        _ => None,
    }
}

/// Is this census argument site one of the M2 baseline's constructor-field
/// argument sites — the 1,996 attributed to the constructor-field strategy?
/// The same predicate the census' own report uses, narrowed to the three
/// constructor families. Returns whether the site belongs to M2.3c (the
/// list cons) rather than here.
pub fn in_population(a: &crate::laziness::ArgSite) -> Option<bool> {
    if a.shape != ArgShape::Computation || !a.position.escapes() {
        return None;
    }
    match a.callee.family {
        Family::ListCons => Some(true),
        Family::ProgramDataCon | Family::LibraryDataCon => Some(false),
        _ => None,
    }
}

//------------------------------------------------------------------------------
// Accounting
//------------------------------------------------------------------------------

/// One of the M2 census' constructor-field argument sites, and the
/// (construction, field) it belongs to.
#[derive(Debug, Clone, Serialize)]
pub struct SiteMap {
    pub module: String,
    pub app: ExprId,
    pub arg: ExprId,
    /// The list cons: M2.3c's population, not mapped here.
    pub list_cons: bool,
    pub program: bool,
    /// Index into [`FieldCensus::flows`], when the site maps onto one.
    pub flow: Option<usize>,
    pub field: Option<u32>,
    pub rep: Option<FieldRep>,
    /// Why it maps onto no construction.
    pub reason: Option<&'static str>,
}

/// One cell of the three-fact matrix, before any rep is derived.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct FactCell {
    pub demand: FieldDemand,
    pub strictness: ConStrictness,
    pub recursion: ValueRecursion,
    pub n: usize,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct RepCell {
    pub program: bool,
    pub ghc_strict: bool,
    pub rep: FieldRep,
    pub n: usize,
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct FieldAccounting {
    pub constructions: usize,
    pub constructions_program: usize,
    pub constructions_library: usize,
    /// `constructions = observed + unobserved + escaped_before_observation`.
    pub observed: usize,
    pub unobserved: usize,
    pub escaped_before_observation: usize,
    pub fields_total: usize,
    pub by_rep: Vec<(FieldRep, usize)>,
    pub by_class: Vec<RepCell>,
    /// The three orthogonal facts, before the rep is derived from them.
    pub facts: Vec<FactCell>,
    /// Strict fields nothing demands: demand `Never` with a forcing
    /// obligation at WHNF, which is why they are not `Dead`.
    pub strict_unused: usize,
    /// Direct verdicts by the rule that proved the timing.
    pub direct_by_rule: Vec<(&'static str, usize)>,
    /// Direct verdicts by the **set** of rules that prove it, so that the
    /// overlap between R1, R2 and R3 is visible: `R1`, `R2`, `R1+R2`, …
    /// Printed unconditionally, including the combinations that are zero.
    pub direct_by_routes: Vec<(String, usize)>,
    pub sites: Vec<SiteMap>,
    pub sites_mapped: usize,
    pub sites_deferred_to_m23c: usize,
    pub sites_unmapped: usize,
    /// Reachability the constructor bought over a shape-only walk.
    pub unreachable_alts: usize,
    pub alias_occurrences_unreachable: usize,
    pub observations_by_kind: Vec<(&'static str, usize)>,
    pub rules: Vec<(&'static str, usize)>,
}

impl FieldAccounting {
    pub fn count(&self, rep: FieldRep) -> usize {
        self.by_rep
            .iter()
            .find(|(r, _)| *r == rep)
            .map(|(_, n)| *n)
            .unwrap_or(0)
    }

    /// Every field is in exactly one rep bucket, every construction in
    /// exactly one observation bucket, and every census site is mapped,
    /// deferred to M2.3c, or carries a reason.
    pub fn check(&self) {
        let by_rep: usize = self.by_rep.iter().map(|(_, n)| n).sum();
        assert_eq!(
            by_rep, self.fields_total,
            "every field must land in exactly one rep"
        );
        let by_class: usize = self.by_class.iter().map(|c| c.n).sum();
        assert_eq!(
            by_class, self.fields_total,
            "the program/library x strict/lazy split must cover every field"
        );
        let facts: usize = self.facts.iter().map(|c| c.n).sum();
        assert_eq!(
            facts, self.fields_total,
            "the three-fact matrix must cover every field"
        );
        assert_eq!(
            self.observed + self.unobserved + self.escaped_before_observation,
            self.constructions,
            "every construction is observed, unobserved, or escaped before observation"
        );
        assert_eq!(
            self.constructions_program + self.constructions_library,
            self.constructions,
            "every construction is the program's or a library's"
        );
        assert_eq!(
            self.sites_mapped + self.sites_deferred_to_m23c + self.sites_unmapped,
            self.sites.len(),
            "every census constructor-field site is mapped, deferred or explained"
        );
        for s in &self.sites {
            assert!(
                s.list_cons || (s.flow.is_some() ^ s.reason.is_some()),
                "site {} in {} must map onto exactly one construction or carry a reason",
                s.app,
                s.module
            );
        }
        let direct: usize = self.direct_by_rule.iter().map(|(_, n)| n).sum();
        assert_eq!(
            direct,
            self.count(FieldRep::Direct),
            "every Direct verdict must name the rule that proved its timing"
        );
        let routed: usize = self.direct_by_routes.iter().map(|(_, n)| n).sum();
        assert_eq!(
            routed,
            self.count(FieldRep::Direct),
            "every Direct verdict must land in exactly one route-set bucket"
        );
    }
}

/// One DataCon's field, aggregated over every construction of it.
#[derive(Debug, Clone, Serialize)]
pub struct ConFieldRow {
    pub con: String,
    pub occ: String,
    pub program: bool,
    pub index: u32,
    pub ghc_strict: bool,
    pub constructions: usize,
    pub rep: FieldRep,
    pub by_rep: Vec<(FieldRep, usize)>,
}

/// The whole population over a set of modules.
pub struct FieldCensus<'m> {
    pub per_module: Vec<Fields<'m>>,
    pub flows: Vec<FieldFlow>,
    pub accounting: FieldAccounting,
    /// Per (DataCon, field index), aggregated over constructions.
    pub con_fields: Vec<ConFieldRow>,
}

impl<'m> FieldCensus<'m> {
    pub fn of_modules(modules: &'m [&'m Module], census: &Census) -> FieldCensus<'m> {
        let per_module: Vec<Fields<'m>> = modules
            .iter()
            .map(|m| Fields::of_module(m, census))
            .collect();
        let mut flows: Vec<FieldFlow> = Vec::new();
        let mut index: HashMap<(&str, ExprId), usize> = HashMap::new();
        for t in &per_module {
            for f in &t.flows {
                index.insert((t.module.name.as_str(), f.construction), flows.len());
                flows.push(f.clone());
            }
        }
        let mut acct = FieldAccounting::default();
        let mut by_rep: BTreeMap<FieldRep, usize> = BTreeMap::new();
        let mut by_class: BTreeMap<(bool, bool, FieldRep), usize> = BTreeMap::new();
        let mut facts: BTreeMap<(FieldDemand, ConStrictness, ValueRecursion), usize> =
            BTreeMap::new();
        let mut obs_kind: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut rules: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut direct_by_rule: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut direct_by_routes: BTreeMap<String, usize> = BTreeMap::new();
        // (con, index) -> rows
        let mut con_fields: BTreeMap<(String, u32), ConFieldRow> = BTreeMap::new();
        for f in &flows {
            acct.constructions += 1;
            if f.program {
                acct.constructions_program += 1;
            } else {
                acct.constructions_library += 1;
            }
            if f.observed() {
                acct.observed += 1;
            } else if f.escaped() {
                acct.escaped_before_observation += 1;
            } else {
                acct.unobserved += 1;
            }
            acct.unreachable_alts += f.unreachable_alts;
            acct.alias_occurrences_unreachable += f.alias_occurrences_unreachable;
            for o in &f.observations {
                *obs_kind
                    .entry(match o.kind {
                        ObsKind::WhnfOnly => "WhnfOnly",
                        ObsKind::FieldDemanded => "FieldDemanded",
                        ObsKind::FieldBoundUnused => "FieldBoundUnused",
                        ObsKind::Escape => "Escape",
                    })
                    .or_default() += 1;
                *rules.entry(o.rule).or_default() += 1;
            }
            for e in &f.evidence {
                *rules.entry(e.rule).or_default() += 1;
            }
            for v in &f.verdicts {
                acct.fields_total += 1;
                *by_rep.entry(v.rep).or_default() += 1;
                *by_class
                    .entry((f.program, v.strictness == ConStrictness::StrictField, v.rep))
                    .or_default() += 1;
                *facts
                    .entry((v.demand, v.strictness, v.recursion))
                    .or_default() += 1;
                if v.force_on_whnf {
                    acct.strict_unused += 1;
                }
                if v.rep == FieldRep::Direct {
                    *direct_by_rule.entry(v.rule).or_default() += 1;
                    *direct_by_routes.entry(v.route_key()).or_default() += 1;
                }
                *rules.entry(v.rule).or_default() += 1;
                let row = con_fields
                    .entry((f.con.clone(), v.index))
                    .or_insert_with(|| ConFieldRow {
                        con: f.con.clone(),
                        occ: f.occ.clone(),
                        program: f.program,
                        index: v.index,
                        ghc_strict: v.strictness == ConStrictness::StrictField,
                        constructions: 0,
                        rep: FieldRep::Dead,
                        by_rep: Vec::new(),
                    });
                row.constructions += 1;
                row.rep = row.rep.join(v.rep);
                match row.by_rep.iter_mut().find(|(r, _)| *r == v.rep) {
                    Some(e) => e.1 += 1,
                    None => row.by_rep.push((v.rep, 1)),
                }
            }
        }
        acct.by_rep = by_rep.into_iter().collect();
        acct.by_class = by_class
            .into_iter()
            .map(|((program, ghc_strict, rep), n)| RepCell {
                program,
                ghc_strict,
                rep,
                n,
            })
            .collect();
        acct.facts = facts
            .into_iter()
            .map(|((demand, strictness, recursion), n)| FactCell {
                demand,
                strictness,
                recursion,
                n,
            })
            .collect();
        acct.observations_by_kind = obs_kind.into_iter().collect();
        acct.rules = rules.into_iter().collect();
        acct.rules.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        acct.direct_by_rule = direct_by_rule.into_iter().collect();
        // The histogram is printed unconditionally, including the
        // combinations that are zero here: the overlap between the three
        // rules is the point, and an absent row hides a zero.
        for key in ["R1", "R2", "R3", "R1+R2", "R1+R3", "R2+R3", "R1+R2+R3"] {
            direct_by_routes.entry(key.to_string()).or_insert(0);
        }
        acct.direct_by_routes = direct_by_routes.into_iter().collect();

        // The M2 census' constructor-field argument sites.
        let known: HashSet<&str> = modules.iter().map(|m| m.name.as_str()).collect();
        for site in &census.args {
            let Some(list_cons) = in_population(site) else {
                continue;
            };
            if !known.contains(site.module.as_str()) {
                continue;
            }
            if list_cons {
                acct.sites_deferred_to_m23c += 1;
                acct.sites.push(SiteMap {
                    module: site.module.clone(),
                    app: site.app,
                    arg: site.arg,
                    list_cons: true,
                    program: false,
                    flow: None,
                    field: None,
                    rep: None,
                    reason: Some("deferred-to-m2.3c-list-cons"),
                });
                continue;
            }
            // The census records argument sites at spine roots, and a
            // construction *is* a spine root.
            let flow = index.get(&(site.module.as_str(), site.app)).copied();
            let field = flow.and_then(|i| {
                flows[i]
                    .fields
                    .iter()
                    .position(|a| *a == site.arg)
                    .map(|k| k as u32)
            });
            let (flow, reason) = match (flow, field) {
                (Some(i), Some(_)) => (Some(i), None),
                (Some(_), None) => (None, Some("argument-is-not-a-field-of-the-construction")),
                (None, _) => (None, Some("construction-not-in-the-population")),
            };
            if flow.is_some() {
                acct.sites_mapped += 1;
            } else {
                acct.sites_unmapped += 1;
            }
            acct.sites.push(SiteMap {
                module: site.module.clone(),
                app: site.app,
                arg: site.arg,
                list_cons: false,
                program: flow.map(|i| flows[i].program).unwrap_or(false),
                flow,
                field,
                rep: flow
                    .zip(field)
                    .and_then(|(i, k)| flows[i].verdicts.get(k as usize).map(|v| v.rep)),
                reason,
            });
        }
        acct.check();
        let mut con_fields: Vec<ConFieldRow> = con_fields.into_values().collect();
        for r in con_fields.iter_mut() {
            r.by_rep.sort_by_key(|(rep, _)| rep.rank());
        }
        con_fields.sort_by(|a, b| {
            b.constructions
                .cmp(&a.constructions)
                .then(a.con.cmp(&b.con))
                .then(a.index.cmp(&b.index))
        });
        FieldCensus {
            per_module,
            flows,
            accounting: acct,
            con_fields,
        }
    }
}
