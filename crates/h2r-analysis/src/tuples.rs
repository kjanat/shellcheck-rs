//! Which tuple allocations are representation plumbing, and which are real
//! program values?
//!
//! After inlining, mtl's `StateT`/`RWST`/`Writer` steps are not newtypes any
//! more: a step *is* a function returning a tuple, and a `>>=` between two
//! steps *is* a tuple construction followed by a tuple pattern match.
//! Worker/wrapper does the same thing with unboxed tuples — a CPR worker
//! returns `(# a, s #)` and every caller immediately takes it apart. Neither
//! of those tuples needs to exist in Rust: the fields can be passed as
//! separate values (scalar replacement).
//!
//! `(a, b)` is not *intrinsically* transformer noise, though — ShellCheck
//! stores pairs in `Map`s, in constructor fields and in its own return
//! types, and those are real values. The constructor name cannot tell the
//! two apart, so nothing here decides a fate from a name: the population is
//! *selected* by the constructor (level 6 evidence, diagnostics only) and
//! every verdict about it is proved by def-use over the resolved
//! occurrences.
//!
//! # What is censused
//!
//! Every **saturated tuple construction** — boxed and unboxed counted
//! separately — wherever it appears: a `let` right-hand side, a case
//! alternative, a function's return value, an argument of another call. The
//! M2 census only sees the *argument* sites of a tuple constructor (1,321 of
//! them attributed to tuples), which is a fraction of the population and
//! never the whole construction; those sites are mapped onto this
//! population one-to-one and reported on their own.
//!
//! # How a fate is proved
//!
//! Each construction gets a [`TupleFlow`]: the value is followed from the
//! construction through every place it can reach — the binder it is bound
//! to, the parameters of known local callees, the call sites of the function
//! that returns it — until every use is classified. The walk is an explicit
//! worklist over *value locations* (nodes whose value is this tuple), never
//! a recursion over Core, and it terminates on a visited set.
//!
//! Interprocedural from the start, because the shapes that dominate are:
//! a lazy-RWS step builds its result tuple out of lazy selectors over the
//! inner step's tuple and **returns** it (so the consumer is whoever calls
//! the enclosing lambda), and a CPR worker returns `(# _, _ #)` that each
//! call site scrutinises. A tuple returned from an *exported* function has
//! callers this module cannot see; that is recorded as unresolved, never
//! guessed.
//!
//! Evidence hierarchy, strongest first (the same one [`crate::parsec`]
//! uses): 1 lexical binder identity, 2 structural shape, 3 def-use
//! dataflow, 4 GHC type compatibility, 5 textual type comparison, 6 names.
//! Every rule below states the level it rests on.

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{AltCon, BindSite, BinderId, Expr, ExprId, Module};
use serde::Serialize;

use crate::callee::{Family, split_stable_name};
use crate::flow::{self, Client, Consumer, Ctx, FlowUse, manifest_params};
use crate::laziness::Census;
use crate::scope::Scope;
use crate::shape::value_args;

/// The generic aggregate walk's rule ids, reasons and proof object, which
/// this client uses unchanged. They are defined in [`crate::flow`] because
/// every saturated constructor flow shares them, and re-exported here
/// because this is where they were first established.
pub use crate::flow::{
    Evidence, LOCATION_BUDGET, R_ALTS, R_APPLIED, R_CALL_OVERSAT, R_CALLEE_NOT_SPLITTABLE,
    R_CLASS_OP, R_CLOSURE_ARG, R_CLOSURE_ARG_CLASS_OP, R_CLOSURE_ARG_IMPORTED,
    R_CLOSURE_ARG_UNKNOWN, R_CLOSURE_CONSED, R_CLOSURE_INTO_PARAM, R_CLOSURE_STORED,
    R_EXPORTED_BINDING, R_EXPORTED_RETURN, R_EXPORTED_WRAPPER_RETURN, R_HIGHER_ORDER,
    R_IMPORTED_LAZY, R_IMPORTED_STRICT, R_IN_PAP, R_NESTED_CLOSURE, R_PAST_PARAMS, R_STORED_CON,
    R_TOO_LARGE, T1_LET_BOUND, T2_SCRUTINISED, T5_PASSED_LOCAL, T6_RETURNED, T7_CALL_RESULT,
    T8_CASE_BINDER_ALIAS, T9_STORED, T10_OPAQUE_CALL, T11_ESCAPE, T14_FORCED,
};

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------

/// **Population.** The head of an application spine is a data constructor
/// whose defining module and occurrence name are GHC's boxed (`GHC.Tuple*`,
/// `(,)`, `(,,)`, …) or unboxed (`GHC.Prim`, `(#,#)`, `(#,,#)`, …) tuple of
/// arity ≥ 1, its `repArity` agrees with the name's comma count and all its
/// fields are lazy, and the spine supplies exactly `repArity` value
/// arguments. Evidence: structural saturation (2) over the constructor's
/// `DataConInfo` (4); the *name* selects the population (6) and proves
/// nothing about the fate.
pub const T0_TUPLE_CON: &str = "T0-TUPLE-CON";
/// …and that alternative's right-hand side is exactly its *i*-th binder: a
/// field selection, which is how GHC desugars a lazy pattern `~(a, b)` into
/// one selector thunk per field. Evidence: lexical identity of the returned
/// binder (1) over structural shape (2).
pub const T3_SELECTED: &str = "T3-SELECTED";
/// A construction every one of whose fields is a [`T3_SELECTED`] projection
/// — field *i* at position *i* — of one and the same binder: a field-wise
/// copy of that tuple, not a new value. Requires all *n* scrutinees to
/// resolve to the same binder; two textually equal expressions are not
/// evidence. Evidence: lexical binder identity (1) over structural shape (2).
pub const T4_RETUPLE: &str = "T4-RETUPLE";
/// A use is a value argument of a saturated construction of *another*
/// tuple whose own fate is proven removable: the inner tuple is a field of
/// a box that will not exist, so it survives exactly as long as that box's
/// fields do, and its consumers are the uses of the outer's *i*-th field
/// binder at every scrutiny of the outer — transitively. When the outer is
/// not proven removable the inner is [`T9_STORED`] as before.
/// Evidence: structural shape (2) over the outer's own def-use proof (3).
pub const T12_NESTED: &str = "T12-NESTED";
/// A use is the value argument of a continuation call the Parsec proof
/// object ([`crate::parsec`]) proves, *and* that proof resolves the
/// continuation to lambdas inside this module: the flow continues at their
/// value parameters. Nothing here re-derives the continuation's target —
/// the region graph is read, not recomputed. Evidence: the Parsec proof's
/// own level (1 over 2) for the hop, def-use (3) after it.
pub const T13_PARSEC_CONT: &str = "T13-PARSEC-CONT";
/// Every consumer reads fields, and the flow never left the function the
/// tuple was built in: the allocation can be replaced by its fields.
/// Evidence: def-use over resolved occurrences (3).
pub const F1_SCALAR_REPLACE: &str = "F1-SCALAR-REPLACE";
/// The flow crosses a function boundary and **every** consumer reads the
/// tuple's fields — by scrutiny, by lazy selection, or by field-wise
/// re-tupling: a multi-value return. Whether any consumer is a lazy
/// selection is recorded as a fact on the flow and not as a fate of its
/// own: both shapes are removed the same way, and no structural rule
/// distinguishes "a state being threaded" from "a worker's result".
/// Evidence: def-use (3).
pub const F2_WORKER_RETURN: &str = "F2-WORKER-RETURN";
/// A proven real value: stored in a constructor field, held in a partial
/// application, or handed to a function outside this module. Evidence:
/// whichever `T9`/`T10` use proved it.
/// **Fate.** Removable by its own def-use proof, but it crosses a
/// representation boundary that [`crate::boundary`] cannot split uniformly
/// and that only a specialised clone of the callee could carry. The proof
/// stands; the rewrite needs a decision this milestone does not make, so
/// the construction is counted as *unsupported*, never as normalised.
pub const F3_REMOVABLE_WITH_CLONE: &str = "F3-REMOVABLE-WITH-CLONE";

pub const F4_PRESERVE: &str = "F4-PRESERVE";
/// A use the rules cannot classify. Carries the reason.
pub const F5_UNRESOLVED: &str = "F5-UNRESOLVED";

// Reasons specific to this client; the ones every aggregate flow shares
// live in [`crate::flow`] and are re-exported above. `Preserve` reasons
// name what holds the tuple; `Unresolved` reasons name what the rules could
// not follow.
pub const R_STORED_TUPLE: &str = "stored-in-a-tuple-field";
pub const R_FUNCTION_ESCAPES: &str = "returning-function-escapes-as-a-value";
pub const R_CALL_UNDERSAT: &str = "call-site-is-a-partial-application";
/// The tuple is the value argument of a proven Parsec continuation call
/// whose target the region graph does not resolve. The detail names the
/// edge.
pub const R_PARSEC_CONT: &str = "parsec-continuation-target-not-in-the-region-graph";
/// Not a reason a *flow* ever carries: the bucket a construction the census
/// calls removable and the [independent verifier](crate::verify) does not
/// re-derive lands in. The milestone counts it as **unsupported**, never as
/// normalised — a removable verdict with only one proof behind it is not a
/// removal this milestone will make.
pub const R_UNVERIFIED: &str = "removable-but-not-independently-verified";

/// A removable flow crosses a representation boundary that is not a
/// uniform split and cannot be cloned into one ([`crate::boundary`]).
pub const R_BOUNDARY_NOT_UNIFORM: &str = "boundary-not-uniform";

/// …and one that a specialised clone of the callee could carry.
pub const R_BOUNDARY_NEEDS_CLONE: &str = "boundary-needs-a-specialised-clone";

/// How many times the nesting fixpoint ([`Tuples::resolve_flows`]) may go
/// round before it is a bug. On every dump it settles in 2.
const NESTING_ROUNDS: usize = 32;

/// Where a removable outer tuple's *i*-th field can be followed to.
#[derive(Debug, Clone)]
struct NestedTarget {
    /// Occurrences of the field binder at each of the outer's scrutinies.
    seeds: Vec<ExprId>,
    /// The outer crossed a return, so this field does too.
    returned: bool,
}

/// `(outer construction, field index) -> where that field goes`.
type Nested = HashMap<(ExprId, usize), NestedTarget>;

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

/// One consumer of a tuple value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum TupleUse {
    /// `case t of (a, b) -> …`: taken apart here.
    Scrutinised {
        case: ExprId,
        all_fields_bound: bool,
    },
    /// `case t of (a, b) -> a`: one field selected (a lazy selector thunk).
    Selected { case: ExprId, field: u32 },
    /// Value argument `param` of a saturated call to a known local callee;
    /// the flow continues at that parameter's occurrences.
    PassedTo {
        call: ExprId,
        callee: BinderId,
        param: u32,
    },
    /// Returned from `function`; the flow continues at its call sites.
    Returned { function: BinderId },
    /// Consumed by a construction that copies it field by field.
    Retupled { outer: ExprId },
    /// Stored in a data constructor's field: a real allocation holds it.
    StoredIn { con: ExprId },
    /// A field of another tuple that is itself proven removable: the flow
    /// continues at that field's binders ([`T12_NESTED`]).
    NestedIn { outer: ExprId, field: u32 },
    /// Forced whole, without reading a field ([`T14_FORCED`]).
    Forced { case: ExprId },
    /// Argument of a call this module cannot see into.
    PassedToUnknown { call: ExprId, why: &'static str },
    /// Anything else the rules do not accept.
    Escapes { at: ExprId, why: &'static str },
}

impl TupleUse {
    /// Does this use only read the tuple's fields?
    pub fn reads_fields(self) -> bool {
        matches!(
            self,
            TupleUse::Scrutinised { .. } | TupleUse::Selected { .. } | TupleUse::Retupled { .. }
        )
    }

    pub fn kind(self) -> &'static str {
        match self {
            TupleUse::Scrutinised { .. } => "Scrutinised",
            TupleUse::Selected { .. } => "Selected",
            TupleUse::PassedTo { .. } => "PassedTo",
            TupleUse::Returned { .. } => "Returned",
            TupleUse::Retupled { .. } => "Retupled",
            TupleUse::StoredIn { .. } => "StoredIn",
            TupleUse::NestedIn { .. } => "NestedIn",
            TupleUse::Forced { .. } => "Forced",
            TupleUse::PassedToUnknown { .. } => "PassedToUnknown",
            TupleUse::Escapes { .. } => "Escapes",
        }
    }

    pub fn at(self) -> ExprId {
        match self {
            TupleUse::Scrutinised { case, .. }
            | TupleUse::Selected { case, .. }
            | TupleUse::Forced { case } => case,
            TupleUse::PassedTo { call, .. } | TupleUse::PassedToUnknown { call, .. } => call,
            TupleUse::Retupled { outer } => outer,
            TupleUse::StoredIn { con } | TupleUse::NestedIn { outer: con, .. } => con,
            TupleUse::Escapes { at, .. } => at,
            TupleUse::Returned { .. } => 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TupleFate {
    /// Every consumer reads fields, in the function that built it.
    ScalarReplace,
    /// It crosses a return and every consumer reads its fields: a
    /// multi-value return. Whether the fields are read together (a
    /// scrutiny) or one at a time (a lazy selection) is recorded as a fact
    /// on the flow, not as a separate fate — see [`TupleFlow::selected`].
    WorkerReturn,
    /// Removable by its own def-use proof, but a representation boundary it
    /// crosses carries values that do not agree on one representation, and
    /// only a specialised clone of the callee could split it
    /// ([`crate::boundary`]). Counted as *unsupported* until a cloning
    /// decision exists.
    RemovableWithClone,
    /// A proven real value.
    Preserve,
    /// A use the rules cannot classify.
    Unresolved,
}

impl TupleFate {
    pub fn rule(self) -> &'static str {
        match self {
            TupleFate::ScalarReplace => F1_SCALAR_REPLACE,
            TupleFate::WorkerReturn => F2_WORKER_RETURN,
            TupleFate::RemovableWithClone => F3_REMOVABLE_WITH_CLONE,
            TupleFate::Preserve => F4_PRESERVE,
            TupleFate::Unresolved => F5_UNRESOLVED,
        }
    }
}

/// One saturated tuple construction and everything proven about it.
#[derive(Debug, Clone, Serialize)]
pub struct TupleFlow {
    pub module: String,
    /// Spine root of the constructor application.
    pub construction: ExprId,
    pub boxed: bool,
    pub arity: u32,
    /// The value arguments, in field order.
    pub fields: Vec<ExprId>,
    /// The binder the construction is bound to, when it is a `let` or
    /// top-level right-hand side.
    pub bound: Option<BinderId>,
    /// When [`T4_RETUPLE`] proves this construction is a field-wise copy:
    /// the binder it copies.
    pub copy_of: Option<BinderId>,
    pub consumers: Vec<TupleUse>,
    /// At least one consumer reads a field on its own — a lazy selector
    /// ([`T3_SELECTED`]) or a field-wise copy ([`T4_RETUPLE`]) — as opposed
    /// to taking the whole tuple apart at once. A fact about how the
    /// fields are demanded, kept as evidence; it decides no fate.
    pub selected: bool,
    /// The flow left the function the tuple was built in through a return.
    pub returned: bool,
    /// Constructions this one is a field of, with the field index
    /// ([`T12_NESTED`]); non-empty whether or not the outer turned out to
    /// be removable.
    pub nested_in: Vec<(ExprId, u32)>,
    pub fate: TupleFate,
    pub evidence: Vec<Evidence>,
    /// Machine-readable reason, for `Preserve` and `Unresolved`.
    pub reason: Option<&'static str>,
    /// Extra detail for the reason (the callee's name, a node id).
    pub detail: String,
    /// Value locations visited: the size of the def-use proof.
    pub locations: usize,
}

impl TupleFlow {
    /// The reason as it is counted in the report: reason plus detail.
    pub fn reason_key(&self) -> Option<String> {
        let r = self.reason?;
        Some(if self.detail.is_empty() {
            r.to_string()
        } else {
            format!("{r} ({})", self.detail)
        })
    }
}

//------------------------------------------------------------------------------
// Population
//------------------------------------------------------------------------------

/// A tuple constructor, as identified by [`T0_TUPLE_CON`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TupleCon {
    pub boxed: bool,
    pub arity: u32,
}

/// Is this data constructor a boxed or unboxed tuple of arity ≥ 1?
///
/// The stable name (`$ghc-prim$GHC.Tuple.Prim$(,)`) gives the defining unit
/// and module as well as the occurrence, so the test is not a bare string
/// match on user-visible text: it is ghc-prim's own tuple constructor or
/// nothing. `rep_arity` is then required to agree with the name's comma
/// count, which is what the rest of the analysis indexes fields by.
pub fn tuple_con(name: &str, rep_arity: u32) -> Option<TupleCon> {
    let (unit, module, occ) = split_stable_name(name)?;
    if unit != "ghc-prim" {
        return None;
    }
    let unboxed = occ.strip_prefix("(#").and_then(|o| o.strip_suffix("#)"));
    let (boxed, inner) = match unboxed {
        Some(i) if module == "GHC.Prim" => (false, i),
        Some(_) => return None,
        None => {
            let i = occ.strip_prefix('(').and_then(|o| o.strip_suffix(')'))?;
            if !module.starts_with("GHC.Tuple") {
                return None;
            }
            (true, i)
        }
    };
    if inner.is_empty() || !inner.bytes().all(|c| c == b',') {
        return None;
    }
    let arity = inner.len() as u32 + 1;
    if arity != rep_arity {
        return None;
    }
    Some(TupleCon { boxed, arity })
}

/// Constructor applications that carry a tuple constructor but are not a
/// saturated construction, so that nothing disappears silently.
#[derive(Debug, Clone, Serialize)]
pub struct SkippedCon {
    pub module: String,
    pub at: ExprId,
    /// `partial-application`, `over-applied`.
    pub reason: &'static str,
    pub occ: String,
}

//------------------------------------------------------------------------------
// The analysis
//------------------------------------------------------------------------------

pub struct Tuples<'m> {
    pub module: &'m Module,
    pub flows: Vec<TupleFlow>,
    pub skipped: Vec<SkippedCon>,
    scope: Scope<'m>,
    /// Spine root of a construction -> index into `flows`.
    index: HashMap<ExprId, usize>,
    /// Binder -> the constructions that are field-wise copies of it.
    copies: HashMap<BinderId, Vec<ExprId>>,
    /// Top-level binder of every flattened top-level pair, by pair index.
    top_pairs: Vec<BinderId>,
    /// Hops this module's own rules cannot derive, taken from another proof
    /// object: `(spine root, value-argument index) -> the parameter(s) the
    /// value lands on`. Filled in by the Parsec coupling
    /// ([`T12_PARSEC_CONT`]); empty when no Parsec proof is supplied.
    pub hops: HashMap<(ExprId, usize), Vec<BinderId>>,
    /// Proven Parsec continuation calls whose target the region graph does
    /// not close over: `(spine root, value-argument index) -> the edge`.
    pub parsec_unresolved: HashMap<(ExprId, usize), String>,
    /// Rounds the nesting fixpoint took.
    pub nesting_rounds: usize,
}

/// The tuple census as a client of the [generic aggregate walk](crate::flow).
///
/// Everything generic — the worklist over value locations, the argument
/// debt that lets the walk leave a function, the may-analysis union over
/// call sites, the location budget — is [`crate::flow`]'s. What this adds is
/// the four rules that are about *tuples* specifically: re-tupling
/// ([`T4_RETUPLE`]), lazy field selection ([`T3_SELECTED`]), nesting inside
/// another removable tuple ([`T12_NESTED`]) and the Parsec continuation hop
/// ([`T13_PARSEC_CONT`]).
struct TupleClient<'a, 'm> {
    t: &'a Tuples<'m>,
    /// Where a removable outer tuple's fields go, from the previous round
    /// of the nesting fixpoint.
    nested: &'a Nested,
    /// Constructions this tuple is a field of, with the field index —
    /// recorded whether or not the outer turned out to be removable.
    nested_in: Vec<(ExprId, u32)>,
}

impl Consumer for TupleUse {
    fn at(self) -> ExprId {
        TupleUse::at(self)
    }
}

impl From<FlowUse> for TupleUse {
    fn from(u: FlowUse) -> TupleUse {
        match u {
            FlowUse::Scrutinised {
                case,
                all_fields_bound,
            } => TupleUse::Scrutinised {
                case,
                all_fields_bound,
            },
            FlowUse::Forced { case } | FlowUse::Whnf { case, .. } => TupleUse::Forced { case },
            FlowUse::PassedTo {
                call,
                callee,
                param,
            } => TupleUse::PassedTo {
                call,
                callee,
                param,
            },
            FlowUse::Returned { function } => TupleUse::Returned { function },
            FlowUse::StoredIn { con } => TupleUse::StoredIn { con },
            FlowUse::PassedToUnknown { call, why } => TupleUse::PassedToUnknown { call, why },
            FlowUse::Escapes { at, why } => TupleUse::Escapes { at, why },
        }
    }
}

impl Client for TupleClient<'_, '_> {
    type Use = TupleUse;

    /// A construction that copies this binder field by field is a consumer
    /// of it: it reads every field and allocates its own box, whose fate is
    /// decided on its own ([`T4_RETUPLE`]).
    fn on_binding(
        &mut self,
        w: &mut flow::Walk<TupleUse>,
        _cx: &Ctx<'_, '_>,
        b: BinderId,
        _v: ExprId,
        owed: u32,
    ) {
        if owed > 0 {
            return;
        }
        for outer in self.t.copies.get(&b).into_iter().flatten() {
            w.use_(TupleUse::Retupled { outer: *outer });
            w.evidence.push(Evidence {
                rule: T4_RETUPLE,
                nodes: vec![*outer],
                binder: Some(b),
                note: "copied field by field into this construction".into(),
            });
        }
    }

    /// A field selection: the alternative returns one of its own binders,
    /// which is how GHC desugars a lazy pattern into one selector thunk per
    /// field ([`T3_SELECTED`]).
    fn on_alt(
        &mut self,
        w: &mut flow::Walk<TupleUse>,
        cx: &Ctx<'_, '_>,
        case: ExprId,
        v: ExprId,
        alt: &h2r_core_ir::Alt,
    ) -> bool {
        let m = cx.m;
        let Some(i) = m
            .resolve(m.strip(alt.rhs))
            .and_then(|r| alt.binders.iter().position(|x| *x == r))
        else {
            return false;
        };
        w.use_(TupleUse::Selected {
            case,
            field: i as u32,
        });
        w.evidence.push(Evidence {
            rule: T3_SELECTED,
            nodes: vec![case, v],
            binder: Some(alt.binders[i]),
            note: format!("field {i} selected"),
        });
        true
    }

    /// A field of another tuple: if that tuple is itself proven removable
    /// the box holding this one will not exist, so the flow continues at the
    /// outer's field binders ([`T12_NESTED`]). Otherwise this is an ordinary
    /// [`T9_STORED`], with the reason split by whether the holder is a tuple.
    fn on_stored(
        &mut self,
        w: &mut flow::Walk<TupleUse>,
        _cx: &Ctx<'_, '_>,
        root: ExprId,
        idx: usize,
        dc: &h2r_core_ir::DataConInfo,
        _occ: &str,
    ) -> Option<&'static str> {
        let tuple_field = tuple_con(&dc.name, dc.rep_arity).is_some();
        if tuple_field && self.t.index.contains_key(&root) {
            self.nested_in.push((root, idx as u32));
            if let Some(t) = self.nested.get(&(root, idx)) {
                w.use_(TupleUse::NestedIn {
                    outer: root,
                    field: idx as u32,
                });
                w.evidence.push(Evidence {
                    rule: T12_NESTED,
                    nodes: vec![root],
                    binder: None,
                    note: format!(
                        "field {idx} of a removable tuple: {} use(s) of that field follow",
                        t.seeds.len()
                    ),
                });
                w.returned |= t.returned;
                for seed in &t.seeds {
                    w.push(*seed, 0);
                }
                return None;
            }
        }
        Some(if tuple_field {
            R_STORED_TUPLE
        } else {
            R_STORED_CON
        })
    }

    /// A continuation the Parsec proof object resolves: the tuple is the
    /// continuation's value argument, so it lands on the value parameter of
    /// every lambda that continuation can be ([`T13_PARSEC_CONT`]).
    fn on_call_arg(
        &mut self,
        w: &mut flow::Walk<TupleUse>,
        cx: &Ctx<'_, '_>,
        root: ExprId,
        idx: usize,
        head: ExprId,
        occ: &str,
        owed: u32,
    ) -> bool {
        if owed != 0 {
            return false;
        }
        let m = cx.m;
        if let Some(params) = self.t.hops.get(&(root, idx))
            && let Some(b) = m.resolve(m.strip(head))
        {
            w.use_(TupleUse::PassedTo {
                call: root,
                callee: b,
                param: idx as u32,
            });
            w.evidence.push(Evidence {
                rule: T13_PARSEC_CONT,
                nodes: vec![root],
                binder: Some(b),
                note: format!(
                    "the Parsec proof resolves {occ} to {} continuation lambda(s)",
                    params.len()
                ),
            });
            for p in params {
                for o in m.occurrences(*p) {
                    w.push(*o, 0);
                }
            }
            return true;
        }
        if let Some(detail) = self.t.parsec_unresolved.get(&(root, idx)) {
            w.escape_at(root, false, R_PARSEC_CONT, detail.clone());
            return true;
        }
        false
    }
}

impl<'m> Tuples<'m> {
    pub fn of_module(m: &'m Module) -> Tuples<'m> {
        Tuples::of_module_with(m, None)
    }

    /// …reading the Parsec proof object's resolved continuation targets as
    /// well, when one is supplied ([`T13_PARSEC_CONT`]).
    pub fn of_module_with(m: &'m Module, parsec: Option<&ParsecHops>) -> Tuples<'m> {
        let mut t = Tuples {
            module: m,
            flows: Vec::new(),
            skipped: Vec::new(),
            scope: Scope::new(m),
            index: HashMap::new(),
            copies: HashMap::new(),
            top_pairs: m
                .top
                .iter()
                .flat_map(|b| b.pairs.iter())
                .map(|p| p.binder)
                .collect(),
            hops: HashMap::new(),
            parsec_unresolved: HashMap::new(),
            nesting_rounds: 0,
        };
        if let Some(p) = parsec {
            t.hops = p.hops.clone();
            t.parsec_unresolved = p.unresolved.clone();
        }
        t.find_constructions();
        t.find_retuplings();
        t.resolve_flows();
        t
    }

    /// Run the [representation boundary](crate::boundary) check over this
    /// module's flows and apply its downgrades, in place.
    ///
    /// Part of the census ([`TupleCensus::of_modules_with`] calls it) rather
    /// than a report, for the same reason the independent verifier is: a
    /// flow whose boundary cannot be split is not one this milestone
    /// removes, so the fate has to say so wherever the fate is read.
    pub fn settle_boundaries(&mut self) -> crate::boundary::Settled {
        let settled = crate::boundary::settle(self);
        for d in &settled.downgrades {
            let Some(i) = self
                .flows
                .iter()
                .position(|f| f.construction == d.construction)
            else {
                continue;
            };
            let f = &mut self.flows[i];
            f.fate = d.to;
            f.reason = Some(match d.to {
                TupleFate::RemovableWithClone => R_BOUNDARY_NEEDS_CLONE,
                _ => R_BOUNDARY_NOT_UNIFORM,
            });
            f.detail = d.boundary.clone();
            f.evidence.push(Evidence {
                rule: crate::boundary::B3_DOWNGRADE,
                nodes: vec![f.construction],
                binder: Some(d.function),
                note: format!(
                    "{} is {} ({}): the def-use proof stands, the rewrite does not",
                    d.boundary,
                    d.verdict.name(),
                    d.reason
                ),
            });
        }
        settled
    }

    pub fn binder(&self, b: BinderId) -> &'m h2r_core_ir::Binder {
        self.module.binder(b)
    }

    /// The flow of the construction rooted at `node`, if that node is one.
    /// A construction is a spine root, so this is also the answer to "is
    /// this application a tuple construction?".
    pub fn flow_at(&self, node: ExprId) -> Option<&TupleFlow> {
        self.index.get(&node).map(|i| &self.flows[*i])
    }

    /// Every saturated tuple construction in the module ([`T0_TUPLE_CON`]).
    fn find_constructions(&mut self) {
        let m = self.module;
        for id in 0..m.exprs.len() as ExprId {
            if !matches!(m.expr(id), Expr::App { .. }) || m.spine_root(id) != id {
                continue;
            }
            let (head, args) = m.spine(id);
            let Some(sig) = self.scope.head_sig(head) else {
                continue;
            };
            let Some(dc) = sig.data_con else { continue };
            let Some(con) = tuple_con(&dc.name, dc.rep_arity) else {
                continue;
            };
            // A tuple's fields are all lazy; a strict one would be a
            // different constructor and a different question.
            if dc.strict_fields.iter().any(|s| *s) {
                continue;
            }
            let vargs = value_args(&self.scope, &args);
            let occ = match m.expr(head) {
                Expr::Var { occ, .. } => occ.clone(),
                _ => String::new(),
            };
            match vargs.len().cmp(&(con.arity as usize)) {
                std::cmp::Ordering::Less => {
                    self.skipped.push(SkippedCon {
                        module: m.name.clone(),
                        at: id,
                        reason: "partial-application",
                        occ,
                    });
                    continue;
                }
                std::cmp::Ordering::Greater => {
                    self.skipped.push(SkippedCon {
                        module: m.name.clone(),
                        at: id,
                        reason: "over-applied",
                        occ,
                    });
                    continue;
                }
                std::cmp::Ordering::Equal => {}
            }
            self.index.insert(id, self.flows.len());
            self.flows.push(TupleFlow {
                module: m.name.clone(),
                construction: id,
                boxed: con.boxed,
                arity: con.arity,
                fields: vargs,
                bound: None,
                copy_of: None,
                consumers: Vec::new(),
                selected: false,
                returned: false,
                nested_in: Vec::new(),
                fate: TupleFate::Unresolved,
                evidence: vec![Evidence {
                    rule: T0_TUPLE_CON,
                    nodes: vec![id, head],
                    binder: None,
                    note: format!(
                        "{} tuple of arity {} ({}), {} value argument(s)",
                        if con.boxed { "boxed" } else { "unboxed" },
                        con.arity,
                        dc.name,
                        con.arity
                    ),
                }],
                reason: None,
                detail: String::new(),
                locations: 0,
            });
        }
    }

    /// Is `e` a selection of field `i` of binder `b` ([`T3_SELECTED`])?
    /// Returns the binder scrutinised and the field index.
    fn selection_of(&self, e: ExprId, arity: u32) -> Option<(BinderId, u32, ExprId)> {
        let m = self.module;
        let node = m.strip(e);
        let Expr::Case { scrut, alts, .. } = m.expr(node) else {
            return None;
        };
        if alts.len() != 1 {
            return None;
        }
        let alt = &alts[0];
        if !matches!(alt.con, AltCon::DataAlt { .. }) || alt.binders.len() != arity as usize {
            return None;
        }
        // The scrutinee must be a variable: only lexical identity can prove
        // that two selections read the *same* tuple.
        let b = m.resolve(m.strip(*scrut))?;
        let ret = m.resolve(m.strip(alt.rhs))?;
        let field = alt.binders.iter().position(|x| *x == ret)? as u32;
        Some((b, field, node))
    }

    /// Constructions that are field-wise copies of one tuple ([`T4_RETUPLE`]).
    fn find_retuplings(&mut self) {
        let mut found: Vec<(usize, BinderId, Vec<ExprId>)> = Vec::new();
        for (i, f) in self.flows.iter().enumerate() {
            let mut of: Option<BinderId> = None;
            let mut nodes = Vec::new();
            let mut ok = true;
            for (k, field) in f.fields.iter().enumerate() {
                match self.selection_of(*field, f.arity) {
                    Some((b, idx, case)) if idx as usize == k && *of.get_or_insert(b) == b => {
                        nodes.push(case);
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok && let Some(b) = of {
                found.push((i, b, nodes));
            }
        }
        for (i, b, nodes) in found {
            let f = &mut self.flows[i];
            f.copy_of = Some(b);
            f.evidence.push(Evidence {
                rule: T4_RETUPLE,
                nodes,
                binder: Some(b),
                note: format!(
                    "every field is the matching projection of {} — a field-wise copy",
                    self.module.binder(b).occ
                ),
            });
            self.copies.entry(b).or_default().push(f.construction);
        }
    }

    //--------------------------------------------------------------------------
    // Def-use walk
    //--------------------------------------------------------------------------

    /// Resolve every flow, and then iterate the ones that are a field of
    /// another tuple until the nesting settles.
    ///
    /// A tuple stored in a *tuple* field is not, in itself, evidence of a
    /// real allocation: if the outer box is proven removable then the field
    /// is just a value, and the inner tuple's consumers are the uses of the
    /// outer's *i*-th field binder at each of the outer's scrutinies. That
    /// is a fixpoint, because the outer may be nested in something else
    /// again. It starts from the pessimistic assignment — every nested
    /// tuple `Preserve` — and only ever *adds* resolved nestings, so a
    /// knot-tied cycle cannot bootstrap itself into being removable.
    fn resolve_flows(&mut self) {
        let n = self.flows.len();
        let empty: Nested = Nested::new();
        let mut nested_any = vec![false; n];
        for (i, any) in nested_any.iter_mut().enumerate() {
            *any = self.run_flow(i, &empty);
        }
        let mut rounds = 0;
        loop {
            let nested = self.nested_targets();
            let before: Vec<TupleFate> = self.flows.iter().map(|f| f.fate).collect();
            let again: Vec<usize> = nested_any
                .iter()
                .enumerate()
                .filter(|(_, any)| **any)
                .map(|(i, _)| i)
                .collect();
            for i in again {
                nested_any[i] = self.run_flow(i, &nested);
            }
            rounds += 1;
            if self.flows.iter().map(|f| f.fate).eq(before.iter().copied()) {
                break;
            }
            assert!(
                rounds < NESTING_ROUNDS,
                "tuple nesting did not settle in {NESTING_ROUNDS} rounds"
            );
        }
        self.nesting_rounds = rounds;
    }

    /// Where a removable outer tuple's *i*-th field can be followed to:
    /// the occurrences of the field binder at every scrutiny of the outer.
    fn nested_targets(&self) -> Nested {
        let m = self.module;
        let mut out: Nested = Nested::new();
        for f in &self.flows {
            if !matches!(f.fate, TupleFate::ScalarReplace | TupleFate::WorkerReturn) {
                continue;
            }
            for idx in 0..f.arity as usize {
                let mut seeds = Vec::new();
                for u in &f.consumers {
                    let case = match u {
                        TupleUse::Scrutinised { case, .. } | TupleUse::Selected { case, .. } => {
                            *case
                        }
                        _ => continue,
                    };
                    let Expr::Case { alts, .. } = m.expr(case) else {
                        continue;
                    };
                    let Some(alt) = alts.first() else { continue };
                    let Some(b) = alt.binders.get(idx) else {
                        continue;
                    };
                    seeds.extend(m.occurrences(*b).iter().copied());
                }
                out.insert(
                    (f.construction, idx),
                    NestedTarget {
                        seeds,
                        returned: f.returned,
                    },
                );
            }
        }
        out
    }

    /// Run one construction's def-use walk from scratch. Returns whether
    /// the flow is a field of another tuple, i.e. whether re-running it can
    /// change anything.
    fn run_flow(&mut self, i: usize, nested: &Nested) -> bool {
        let cx = Ctx {
            m: self.module,
            scope: &self.scope,
            top_pairs: &self.top_pairs,
            start: self.flows[i].construction,
            arity: self.flows[i].arity,
            // The construction's own constructor, which is what decides
            // which alternative of a `case` a value of it selects. A tuple
            // type has one constructor, so this only ever confirms what the
            // single-alternative rule already said.
            con: flow::saturated_con(&self.scope, self.flows[i].construction).map(|(dc, _, _)| dc),
        };
        let mut client = TupleClient {
            t: self,
            nested,
            nested_in: Vec::new(),
        };
        let w = flow::walk(&cx, &mut client);
        let nested_in = client.nested_in;
        let (fate, reason, detail) = decide(&w);
        let base = self.flows[i]
            .evidence
            .iter()
            .position(|e| e.rule != T0_TUPLE_CON && e.rule != T4_RETUPLE)
            .unwrap_or(self.flows[i].evidence.len());
        let f = &mut self.flows[i];
        f.evidence.truncate(base);
        f.bound = w.bound;
        f.locations = w.locations;
        f.selected = w
            .consumers
            .iter()
            .any(|u| matches!(u, TupleUse::Selected { .. } | TupleUse::Retupled { .. }));
        f.returned = w.returned;
        f.nested_in = nested_in;
        f.consumers = w.consumers;
        f.evidence.extend(w.evidence);
        f.fate = fate;
        f.reason = reason;
        f.detail = detail;
        f.evidence.push(Evidence {
            rule: fate.rule(),
            nodes: vec![f.construction],
            binder: None,
            note: format!(
                "{} consumer(s) over {} value location(s){}{}",
                f.consumers.len(),
                f.locations,
                if w.returned {
                    ", crossing a return"
                } else {
                    ""
                },
                if f.selected {
                    ", at least one field read on its own"
                } else {
                    ""
                }
            ),
        });
        !f.nested_in.is_empty()
    }
}

/// The fate, from the accumulated uses. Precedence, so that every
/// construction lands in exactly one bucket:
///
/// 1. a proven real value wins over everything — it *is* an allocation;
/// 2. then anything the rules could not follow;
/// 3. then the three plumbing fates, by whether the tuple crossed a return
///    and by how its fields are read.
fn decide(w: &flow::Walk<TupleUse>) -> (TupleFate, Option<&'static str>, String) {
    if w.over_budget {
        return (TupleFate::Unresolved, Some(R_TOO_LARGE), String::new());
    }
    if let Some((_, why, detail, _)) = w.escapes.iter().find(|e| e.0) {
        return (TupleFate::Preserve, Some(why), detail.clone());
    }
    if let Some((_, why, detail, _)) = w.escapes.first() {
        return (TupleFate::Unresolved, Some(why), detail.clone());
    }
    // What is left are the uses that read fields and the hops that got to
    // them (`Returned`, `PassedTo`), which are not themselves consumers.
    let reads: Vec<TupleUse> = w
        .consumers
        .iter()
        .copied()
        .filter(|u| u.reads_fields())
        .collect();
    if reads.is_empty() || !w.returned {
        // Nothing reads the tuple (it is dead), or it never outlives the
        // call it was built in — including where it was handed to a known
        // callee, whose parameter becomes the fields.
        return (TupleFate::ScalarReplace, None, String::new());
    }
    (TupleFate::WorkerReturn, None, String::new())
}

/// Is this census argument site one of the tuple-attributed lazy/unknown
/// computations of the M2 baseline — the 1,321 the milestone has to account
/// for? The same predicate the census' own report uses, narrowed to the two
/// tuple families.
pub fn in_population(a: &crate::laziness::ArgSite) -> Option<bool> {
    if a.shape != crate::shape::ArgShape::Computation || !a.position.escapes() {
        return None;
    }
    match a.callee.family {
        Family::Tuple => Some(true),
        Family::UnboxedTuple => Some(false),
        _ => None,
    }
}

//------------------------------------------------------------------------------
// Accounting
//------------------------------------------------------------------------------

/// One of the census' tuple-attributed lazy argument sites, and the
/// construction it belongs to.
#[derive(Debug, Clone, Serialize)]
pub struct SiteMap {
    pub module: String,
    /// The census' spine root and argument node.
    pub app: ExprId,
    pub arg: ExprId,
    pub boxed: bool,
    /// Index into [`TupleCensus::flows`], when the site maps onto one.
    pub flow: Option<usize>,
    pub fate: Option<TupleFate>,
    /// Why it maps onto no construction.
    pub reason: Option<&'static str>,
}

/// How many constructions of one representation got one fate.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct FateCount {
    pub boxed: bool,
    pub fate: TupleFate,
    pub n: usize,
}

/// The milestone's accounting for one representation:
/// `before = normalised + preserved + unsupported`.
///
/// *normalised* is a construction this milestone removes — removable **and**
/// re-derived by the independent verifier. *preserved* is a proven real
/// value. *unsupported* is everything else: `Unresolved`, plus any
/// construction the census calls removable that the verifier does not
/// confirm ([`R_UNVERIFIED`]). The three are disjoint and sum to the
/// population by construction, and [`Accounting::check`] asserts it.
#[derive(Debug, Clone, Copy, Default, Serialize)]
pub struct Bucket {
    pub boxed: bool,
    pub before: usize,
    pub normalised: usize,
    pub preserved: usize,
    pub unsupported: usize,
}

impl Bucket {
    fn add(&mut self, fate: TupleFate, verified: bool) {
        self.before += 1;
        match fate {
            TupleFate::ScalarReplace | TupleFate::WorkerReturn if verified => self.normalised += 1,
            TupleFate::Preserve => self.preserved += 1,
            _ => self.unsupported += 1,
        }
    }
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct Accounting {
    /// Constructions by representation and fate; one entry per pair that
    /// occurs.
    pub by_fate: Vec<FateCount>,
    pub constructions_boxed: usize,
    pub constructions_unboxed: usize,
    /// Census argument sites attributed to a tuple constructor.
    pub sites: Vec<SiteMap>,
    pub sites_mapped: usize,
    pub sites_unmapped: usize,
    /// `before = normalised + preserved + unsupported`, boxed then unboxed.
    pub milestone: Vec<Bucket>,
    /// The same for the census' tuple-attributed argument sites.
    pub site_milestone: Vec<Bucket>,
    /// Constructions the census calls removable that the independent
    /// verifier does not re-derive: counted as unsupported.
    pub removable_unverified: usize,
    /// Constructions whose def-use proof stands but whose representation
    /// boundary only a specialised clone could split: counted as
    /// unsupported ([`TupleFate::RemovableWithClone`]).
    pub removable_with_clone: usize,
    /// The unsupported residual, itemised by the *kind* of thing holding
    /// the value — the flow's own reason, plus [`R_UNVERIFIED`]. Sums to
    /// the unsupported total over both representations.
    pub residual: Vec<(String, usize)>,
}

impl Accounting {
    /// Constructions of one representation with one fate.
    pub fn count(&self, boxed: bool, fate: TupleFate) -> usize {
        self.by_fate
            .iter()
            .find(|c| c.boxed == boxed && c.fate == fate)
            .map(|c| c.n)
            .unwrap_or(0)
    }

    /// The milestone bucket for one representation.
    pub fn bucket(&self, boxed: bool) -> Bucket {
        self.milestone
            .iter()
            .find(|b| b.boxed == boxed)
            .copied()
            .unwrap_or_default()
    }

    /// The same over the census' argument sites.
    pub fn site_bucket(&self, boxed: bool) -> Bucket {
        self.site_milestone
            .iter()
            .find(|b| b.boxed == boxed)
            .copied()
            .unwrap_or_default()
    }

    /// Every construction is in exactly one fate bucket, and every census
    /// site either maps onto exactly one construction or carries a reason.
    pub fn check(&self) {
        let boxed: usize = self.by_fate.iter().filter(|c| c.boxed).map(|c| c.n).sum();
        let unboxed: usize = self.by_fate.iter().filter(|c| !c.boxed).map(|c| c.n).sum();
        assert_eq!(
            boxed, self.constructions_boxed,
            "every boxed construction must land in exactly one fate"
        );
        assert_eq!(
            unboxed, self.constructions_unboxed,
            "every unboxed construction must land in exactly one fate"
        );
        assert_eq!(
            self.sites_mapped + self.sites_unmapped,
            self.sites.len(),
            "every census tuple site is mapped or explained"
        );
        for s in &self.sites {
            assert!(
                s.flow.is_some() ^ s.reason.is_some(),
                "site {} in {} must map onto exactly one construction or carry a reason",
                s.app,
                s.module
            );
        }
        // The milestone's own accounting: nothing is counted twice and
        // nothing falls between the buckets.
        for (what, buckets, total) in [
            (
                "constructions",
                &self.milestone,
                self.constructions_boxed + self.constructions_unboxed,
            ),
            ("census sites", &self.site_milestone, self.sites_mapped),
        ] {
            let mut sum = 0;
            for b in buckets.iter() {
                assert_eq!(
                    b.before,
                    b.normalised + b.preserved + b.unsupported,
                    "{what}: before must be normalised + preserved + unsupported \
                     for the {} representation",
                    if b.boxed { "boxed" } else { "unboxed" }
                );
                sum += b.before;
            }
            assert_eq!(sum, total, "{what}: the buckets must cover the population");
        }
        let unsupported: usize = self.milestone.iter().map(|b| b.unsupported).sum();
        let itemised: usize = self.residual.iter().map(|(_, n)| n).sum();
        assert_eq!(
            itemised, unsupported,
            "the itemised residual must sum to the unsupported total"
        );
    }
}

/// The whole population over a set of modules, with the census' argument
/// sites mapped onto it.
pub struct TupleCensus<'m> {
    pub per_module: Vec<Tuples<'m>>,
    /// Every flow, in module order; the index the [`SiteMap`]s refer to.
    pub flows: Vec<TupleFlow>,
    pub accounting: Accounting,
    /// The [independent verifier](crate::verify)'s re-derivation of every
    /// removable verdict. Run here rather than behind a flag, because the
    /// milestone's accounting counts only *verified* removals as
    /// normalised, so the verdict is part of the census, not a report.
    pub cross: crate::verify::CrossCheck,
    /// `(module, construction)` of every verdict the verifier re-derived.
    pub verified: HashSet<(String, ExprId)>,
    /// The [representation boundaries](crate::boundary) the removable flows
    /// cross, one entry per module in the same order as `per_module`.
    pub boundaries: Vec<crate::boundary::Boundaries>,
    /// Flows that lost their fate because a boundary they cross is not a
    /// uniform split.
    pub downgrades: Vec<crate::boundary::Downgrade>,
    /// Rounds the boundary downgrade fixpoint took, over all modules.
    pub boundary_rounds: usize,
}

impl TupleCensus<'_> {
    /// Did the independent verifier re-derive this flow's removable
    /// verdict? False for everything that is not removable.
    pub fn is_verified(&self, f: &TupleFlow) -> bool {
        self.verified.contains(&(f.module.clone(), f.construction))
    }

    /// Constructions this milestone removes: removable *and* verified.
    pub fn is_normalised(&self, f: &TupleFlow) -> bool {
        matches!(f.fate, TupleFate::ScalarReplace | TupleFate::WorkerReturn) && self.is_verified(f)
    }
}

impl<'m> TupleCensus<'m> {
    pub fn of_modules(modules: &'m [&'m Module], census: &Census) -> TupleCensus<'m> {
        TupleCensus::of_modules_with(modules, census, &[])
    }

    /// …with the Parsec proof object's hops, one entry per module in the
    /// same order (or an empty slice for none).
    pub fn of_modules_with(
        modules: &'m [&'m Module],
        census: &Census,
        parsec: &[ParsecHops],
    ) -> TupleCensus<'m> {
        let mut per_module: Vec<Tuples<'m>> = modules
            .iter()
            .enumerate()
            .map(|(i, m)| Tuples::of_module_with(m, parsec.get(i)))
            .collect();
        // M2.2.1: a flow's own def-use proof is not enough if the
        // representation boundary it crosses carries other values too.
        // Every removable flow whose scalar view crosses a parameter or a
        // return has that boundary enumerated independently, and loses its
        // fate here if the boundary is not a uniform split.
        let mut boundaries: Vec<crate::boundary::Boundaries> = Vec::new();
        let mut downgrades: Vec<crate::boundary::Downgrade> = Vec::new();
        let mut boundary_rounds = 0;
        for t in per_module.iter_mut() {
            let settled = t.settle_boundaries();
            boundary_rounds = boundary_rounds.max(settled.rounds);
            downgrades.extend(settled.downgrades.iter().cloned());
            boundaries.push(settled.boundaries);
        }
        let per_module = per_module;
        let mut flows: Vec<TupleFlow> = Vec::new();
        // module -> construction node -> flow index
        let mut index: HashMap<(&str, ExprId), usize> = HashMap::new();
        for t in &per_module {
            for f in &t.flows {
                index.insert((t.module.name.as_str(), f.construction), flows.len());
                flows.push(f.clone());
            }
        }
        let mut acct = Accounting::default();
        let mut by_fate: BTreeMap<(bool, TupleFate), usize> = BTreeMap::new();
        for f in &flows {
            if f.boxed {
                acct.constructions_boxed += 1;
            } else {
                acct.constructions_unboxed += 1;
            }
            *by_fate.entry((f.boxed, f.fate)).or_default() += 1;
        }
        acct.by_fate = by_fate
            .into_iter()
            .map(|((boxed, fate), n)| FateCount { boxed, fate, n })
            .collect();
        // The independent re-derivation, module by module. Its verdict is
        // what separates *normalised* from *unsupported* below.
        let mut cross = crate::verify::CrossCheck::default();
        for (t, m) in per_module.iter().zip(modules.iter()) {
            let population: HashSet<ExprId> = t.flows.iter().map(|f| f.construction).collect();
            let removable: HashSet<ExprId> = t
                .flows
                .iter()
                .filter(|f| matches!(f.fate, TupleFate::ScalarReplace | TupleFate::WorkerReturn))
                .map(|f| f.construction)
                .collect();
            crate::verify::cross_check(m, &population, &removable, t.hops.clone(), &mut cross);
        }
        let verified: HashSet<(String, ExprId)> = cross.verified.iter().cloned().collect();

        let known: HashSet<&str> = modules.iter().map(|m| m.name.as_str()).collect();
        for site in &census.args {
            let Some(boxed) = in_population(site) else {
                continue;
            };
            if !known.contains(site.module.as_str()) {
                continue;
            }
            // The census records argument sites at spine roots, and a
            // construction *is* a spine root, so the site maps onto the
            // construction at its own `app` node or onto nothing.
            let flow = index.get(&(site.module.as_str(), site.app)).copied();
            let reason = match flow {
                Some(_) => None,
                None => Some(unmapped_reason(&per_module, site)),
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
                boxed,
                flow,
                fate: flow.map(|i| flows[i].fate),
                reason,
            });
        }
        // `before = normalised + preserved + unsupported`, per
        // representation, for the population and for the census' sites.
        let is_verified = |f: &TupleFlow| verified.contains(&(f.module.clone(), f.construction));
        let mut milestone = [
            Bucket {
                boxed: true,
                ..Default::default()
            },
            Bucket {
                boxed: false,
                ..Default::default()
            },
        ];
        let mut site_milestone = milestone;
        let mut residual: BTreeMap<String, usize> = BTreeMap::new();
        for f in &flows {
            let ok = is_verified(f);
            milestone[usize::from(!f.boxed)].add(f.fate, ok);
            match (f.fate, ok) {
                (TupleFate::ScalarReplace | TupleFate::WorkerReturn, false) => {
                    acct.removable_unverified += 1;
                    *residual.entry(R_UNVERIFIED.to_string()).or_default() += 1;
                }
                // Proven removable, but the boundary it crosses would have
                // to be cloned: unsupported until that decision exists.
                (TupleFate::RemovableWithClone, _) => {
                    acct.removable_with_clone += 1;
                    *residual
                        .entry(R_BOUNDARY_NEEDS_CLONE.to_string())
                        .or_default() += 1;
                }
                (TupleFate::Unresolved, _) => {
                    // By the *kind* of holder, not by its name: the
                    // constructor and callee names are diagnostics, and the
                    // split is what says which milestone picks each class up.
                    let key = f.reason.unwrap_or("unresolved-with-no-reason");
                    *residual.entry(key.to_string()).or_default() += 1;
                }
                _ => {}
            }
        }
        for s in &acct.sites {
            let Some(i) = s.flow else { continue };
            site_milestone[usize::from(!s.boxed)].add(flows[i].fate, is_verified(&flows[i]));
        }
        acct.milestone = milestone.to_vec();
        acct.site_milestone = site_milestone.to_vec();
        acct.residual = residual.into_iter().collect();
        acct.residual
            .sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        acct.check();
        TupleCensus {
            per_module,
            flows,
            accounting: acct,
            cross,
            verified,
            boundaries,
            downgrades,
            boundary_rounds,
        }
    }
}

/// Why a census site attributed to a tuple constructor is not a saturated
/// construction.
fn unmapped_reason(per_module: &[Tuples<'_>], site: &crate::laziness::ArgSite) -> &'static str {
    for t in per_module {
        if t.module.name != site.module {
            continue;
        }
        if let Some(sk) = t.skipped.iter().find(|s| s.at == site.app) {
            return sk.reason;
        }
    }
    "construction-not-in-the-population"
}

//------------------------------------------------------------------------------
// Coupling the two proof objects
//------------------------------------------------------------------------------
//
// A tuple handed to a Parsec continuation is not "passed to an unknown
// higher-order value" as far as the *other* proof object is concerned:
// [`crate::parsec`] proves what that continuation is and which edge of the
// recovered graph the call is. What it does not always give is where the
// continuation's own value comes from, and that is what following the
// tuple needs. So this reads the proof object — regions, their continuation
// parameters, and the binder each region's chain is bound to — and resolves
// the *value* of the continuation only when the region graph closes over
// it: every call of the region is a saturated call to a visible binder, and
// what fills the slot at each is a manifest lambda (directly, or through
// another continuation parameter, followed the same way). Nothing here
// re-derives a role, a slot or an edge.

/// What the Parsec proof object contributes to a tuple flow.
#[derive(Debug, Default, Clone)]
pub struct ParsecHops {
    /// `(spine root, value-argument index) -> the value parameter(s) of the
    /// lambdas that continuation can be.
    pub hops: HashMap<(ExprId, usize), Vec<BinderId>>,
    /// `spine root -> (value-argument index, the edge, why it is not
    /// resolved)` for a proven continuation call whose target the region
    /// graph does not close over.
    pub unresolved: HashMap<(ExprId, usize), String>,
}

/// Read the Parsec proof object for every continuation call that carries a
/// value argument.
pub fn parsec_hops(a: &crate::parsec::Analysis<'_>) -> ParsecHops {
    use crate::parsec::{ContKind, EdgeFact};

    let mut out = ParsecHops::default();
    // Which region each continuation *parameter* belongs to, and its arity,
    // straight out of the proof object.
    let mut cont_param: HashMap<BinderId, (usize, usize, usize)> = HashMap::new();
    for (ri, r) in a.regions.iter().enumerate() {
        if !r.proven {
            continue;
        }
        for c in &r.conts {
            let Some(pos) = r.params.iter().position(|p| *p == c.binder) else {
                continue;
            };
            cont_param.insert(c.binder, (ri, pos, c.arity));
        }
    }
    for r in a.regions.iter().filter(|r| r.proven) {
        for e in &r.edges {
            if e.fact != EdgeFact::Invoke {
                continue;
            }
            let Some(b) = e.provenance.binder else {
                continue;
            };
            // Only an "ok" continuation of the three-argument shape carries
            // a value; the proof object says which this is.
            let Some((ri, _, arity)) = cont_param.get(&b).copied() else {
                continue;
            };
            if e.source_role.kind() != Some(ContKind::Ok) || arity != 3 {
                continue;
            }
            let key = (e.at, 0usize);
            match resolve_cont(a, &cont_param, b) {
                Ok(params) if !params.is_empty() => {
                    out.hops.insert(key, params);
                }
                Ok(_) => {
                    out.unresolved.insert(
                        key,
                        format!("{} of region {ri} has no call site", e.provenance.label),
                    );
                }
                Err(why) => {
                    out.unresolved
                        .insert(key, format!("{} of region {ri}: {why}", e.provenance.label));
                }
            }
        }
    }
    out
}

/// The value parameters of every lambda that can be bound to the
/// continuation parameter `b`, following the region graph.
fn resolve_cont(
    a: &crate::parsec::Analysis<'_>,
    cont_param: &HashMap<BinderId, (usize, usize, usize)>,
    b: BinderId,
) -> Result<Vec<BinderId>, &'static str> {
    let m: &Module = a.module;
    let mut out: Vec<BinderId> = Vec::new();
    let mut work = vec![b];
    let mut seen: HashSet<BinderId> = HashSet::from([b]);
    while let Some(cb) = work.pop() {
        // The continuation values that reach `cb`.
        let values: Vec<ExprId> = if let Some((ri, pos, _)) = cont_param.get(&cb).copied() {
            let r = &a.regions[ri];
            let Some(p) = a.region_binder(ri) else {
                return Err("the region's chain is not bound to a binder");
            };
            if m.binder(p).exported == Some(true) {
                return Err("the region's parser is exported");
            }
            let mut vs = Vec::new();
            for occ in m.occurrences(p) {
                let root = m.spine_root(*occ);
                if root == *occ {
                    return Err("the region's parser is used as a value");
                }
                let (head, args) = m.spine(root);
                if m.strip(head) != m.strip(*occ) {
                    return Err("the region's parser is not the head of its spine");
                }
                let vargs: Vec<ExprId> = args
                    .iter()
                    .copied()
                    .filter(|x| !matches!(m.expr(m.strip(*x)), Expr::Type { .. } | Expr::Coercion))
                    .collect();
                if vargs.len() != r.params.len() {
                    return Err("a call of the region is not saturated exactly");
                }
                vs.push(vargs[pos]);
            }
            vs
        } else {
            // A let-bound continuation: its right-hand side is its value.
            match m.binding(cb).rhs {
                Some(rhs) => vec![rhs],
                None => return Err("the continuation is not a region parameter or a binding"),
            }
        };
        for v in values {
            let i = m.strip(v);
            match m.expr(i) {
                Expr::Lam { .. } => match manifest_params(m, i).first() {
                    // The value is the ok continuation's first argument.
                    // Corroborated against the parameter's own type, so an
                    // eta-reduced lambda that starts with the state cannot
                    // be mistaken for one that starts with the value.
                    Some(p) if !crate::parsec::is_state_ty(&m.binder(*p).ty_pretty) => out.push(*p),
                    Some(_) => return Err("the continuation lambda starts with the state"),
                    None => return Err("the continuation lambda has no value parameter"),
                },
                Expr::Var { .. } => match m.resolve(i) {
                    Some(b2) if seen.insert(b2) => work.push(b2),
                    Some(_) => {}
                    None => return Err("the continuation is an import"),
                },
                _ => return Err("the continuation is a computed value"),
            }
        }
    }
    Ok(out)
}

//------------------------------------------------------------------------------
// The audited shapes, counted in a real dump
//------------------------------------------------------------------------------

/// One shape the stage-2 audit built a regression test for, and how often
/// it actually occurs. Reported so that a hand-built test is never the only
/// evidence that a rule was exercised.
#[derive(Debug, Clone, Serialize)]
pub struct Pattern {
    pub name: &'static str,
    pub n: usize,
    /// A representative, for `h2r show`.
    pub module: String,
    pub at: ExprId,
    /// Fates of the constructions matching it.
    pub fates: BTreeMap<String, usize>,
}

/// Does `b` occur inside its own right-hand side?
fn is_recursive(m: &Module, b: BinderId) -> bool {
    let Some(rhs) = m.binding(b).rhs else {
        return false;
    };
    m.occurrences(b)
        .iter()
        .any(|occ| *occ == rhs || m.ancestors(*occ).any(|a| a == rhs))
}

/// Facts about one module that a shape predicate needs and a single flow
/// does not carry.
struct PatternCtx {
    /// Cases that take an *unboxed* tuple apart, from those flows' own
    /// consumer lists.
    unboxed_scrutinies: HashSet<ExprId>,
}

/// Count every audited shape over a set of modules.
pub fn patterns(per_module: &[Tuples<'_>]) -> Vec<Pattern> {
    let ctxs: Vec<PatternCtx> = per_module
        .iter()
        .map(|t| PatternCtx {
            unboxed_scrutinies: t
                .flows
                .iter()
                .filter(|f| !f.boxed)
                .flat_map(|f| f.consumers.iter())
                .filter_map(|u| match u {
                    TupleUse::Scrutinised { case, .. } | TupleUse::Selected { case, .. } => {
                        Some(*case)
                    }
                    _ => None,
                })
                .collect(),
        })
        .collect();
    type Pred = fn(&PatternCtx, &Tuples<'_>, &TupleFlow) -> bool;
    let rows: &[(&'static str, Pred)] = &[
        ("1 two names for one tuple, one escaping", |_, _, f| {
            aliases(f) > 1 && !removable(f.fate)
        }),
        ("1 re-bound under a second let binder", |_, _, f| {
            lets(f) > 1
        }),
        ("2 two or more field reads", |_, _, f| {
            f.consumers.iter().filter(|u| u.reads_fields()).count() > 1
        }),
        ("2 read and then stored", |_, _, f| {
            f.consumers.iter().any(|u| u.reads_fields())
                && f.consumers
                    .iter()
                    .any(|u| matches!(u, TupleUse::StoredIn { .. }))
        }),
        ("3 returned from a recursive function", |_, t, f| {
            f.consumers.iter().any(|u| match u {
                TupleUse::Returned { function } => is_recursive(t.module, *function),
                _ => false,
            })
        }),
        ("3 threaded into a recursive callee", |_, t, f| {
            f.consumers.iter().any(|u| match u {
                TupleUse::PassedTo { callee, .. } => is_recursive(t.module, *callee),
                _ => false,
            })
        }),
        ("4 a field of another tuple, outer removable", |_, _, f| {
            f.consumers
                .iter()
                .any(|u| matches!(u, TupleUse::NestedIn { .. }))
        }),
        ("4 a field of another tuple, outer not", |_, _, f| {
            !f.nested_in.is_empty()
                && !f
                    .consumers
                    .iter()
                    .any(|u| matches!(u, TupleUse::NestedIn { .. }))
        }),
        ("5 an unboxed return re-boxed by its caller", |c, t, f| {
            f.boxed && f.fields.iter().all(|x| is_unboxed_field(c, t, *x))
        }),
        ("5 unboxed into a local callee's parameters", |_, _, f| {
            f.consumers
                .iter()
                .any(|u| matches!(u, TupleUse::PassedTo { .. }))
                && f.consumers
                    .iter()
                    .any(|u| matches!(u, TupleUse::Scrutinised { .. }))
        }),
        ("5 returned from an exported wrapper", |_, _, f| {
            f.reason == Some(R_EXPORTED_WRAPPER_RETURN)
        }),
        (
            "6 returned from a closure, call sites visible",
            |_, t, f| {
                removable(f.fate)
                    && f.consumers.iter().any(|u| match u {
                        TupleUse::Returned { function } => {
                            t.module.binding(*function).site == BindSite::Let
                        }
                        _ => false,
                    })
            },
        ),
        ("6 returned from a closure that is stored", |_, _, f| {
            matches!(f.reason, Some(R_CLOSURE_STORED) | Some(R_CLOSURE_CONSED))
        }),
        ("7 the callee is a computed closure", |_, _, f| {
            f.reason == Some(R_HIGHER_ORDER) || f.reason == Some(R_CLOSURE_ARG)
        }),
        ("7 a parameter reached from two call sites", |_, t, f| {
            f.consumers.iter().any(|u| match u {
                TupleUse::PassedTo { callee, .. } => t.module.occurrences(*callee).len() > 1,
                _ => false,
            })
        }),
        ("8 forced whole, no field read", |_, _, f| {
            f.consumers
                .iter()
                .any(|u| matches!(u, TupleUse::Forced { .. }))
        }),
        ("8 stored in a strict constructor field", |_, t, f| {
            f.consumers.iter().any(|u| match u {
                TupleUse::StoredIn { con } => in_strict_field(t, *con),
                _ => false,
            })
        }),
        ("8 a case that is not one tuple alternative", |_, _, f| {
            f.reason == Some(R_ALTS)
        }),
    ];
    let mut out = Vec::new();
    for (name, pred) in rows {
        let mut p = Pattern {
            name,
            n: 0,
            module: String::new(),
            at: 0,
            fates: BTreeMap::new(),
        };
        for (t, c) in per_module.iter().zip(&ctxs) {
            for f in &t.flows {
                if !pred(c, t, f) {
                    continue;
                }
                p.n += 1;
                *p.fates.entry(format!("{:?}", f.fate)).or_default() += 1;
                if p.module.is_empty() {
                    p.module = t.module.name.clone();
                    p.at = f.construction;
                }
            }
        }
        out.push(p);
    }
    out
}

fn removable(f: TupleFate) -> bool {
    matches!(f, TupleFate::ScalarReplace | TupleFate::WorkerReturn)
}

/// Alias binders the flow was reachable under: every `let`/top-level
/// binding plus every case binder that aliases the whole tuple.
fn aliases(f: &TupleFlow) -> usize {
    f.evidence
        .iter()
        .filter(|e| e.rule == T1_LET_BOUND || e.rule == T8_CASE_BINDER_ALIAS)
        .count()
}

fn lets(f: &TupleFlow) -> usize {
    f.evidence.iter().filter(|e| e.rule == T1_LET_BOUND).count()
}

/// Is this field of a boxed construction a binder bound by a match on an
/// *unboxed* tuple — i.e. is the construction re-boxing a worker's result?
fn is_unboxed_field(c: &PatternCtx, t: &Tuples<'_>, field: ExprId) -> bool {
    let m = t.module;
    let Some(b) = m.resolve(m.strip(field)) else {
        return false;
    };
    if m.binding(b).site != BindSite::AltBinder {
        return false;
    }
    // The field is inside the alternative that binds it, so the case is on
    // the path up from here.
    for a in m.ancestors(field) {
        let Expr::Case { alts, .. } = m.expr(a) else {
            continue;
        };
        if !alts.iter().any(|x| x.binders.contains(&b)) {
            continue;
        }
        return c.unboxed_scrutinies.contains(&a);
    }
    false
}

fn in_strict_field(t: &Tuples<'_>, con: ExprId) -> bool {
    let m = t.module;
    let (head, _) = m.spine(con);
    t.scope
        .head_sig(head)
        .and_then(|s| s.data_con)
        .is_some_and(|dc| dc.strict_fields.iter().any(|x| *x))
}
