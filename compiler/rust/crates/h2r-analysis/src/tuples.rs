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

use h2r_core_ir::{AltCon, BindSite, BinderId, BinderKind, Edge, Expr, ExprId, Module};
use serde::Serialize;

use crate::callee::{Family, split_stable_name};
use crate::laziness::Census;
use crate::scope::Scope;
use crate::shape::value_args;

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
/// The construction is the right-hand side of a `let` or top-level binding:
/// the tuple's uses are the resolved occurrences of that binder.
/// Evidence: lexical binder identity (1).
pub const T1_LET_BOUND: &str = "T1-LET-BOUND";
/// A use is the scrutinee of a `case` whose single alternative is a data
/// alternative binding the tuple's fields: the tuple is taken apart here and
/// the box does not survive the match. Evidence: structural shape (2).
pub const T2_SCRUTINISED: &str = "T2-SCRUTINISED";
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
/// A use is value argument *i* of a **saturated** call to a binder bound in
/// this module to a manifest lambda chain: the tuple flows on to the
/// occurrences of that chain's *i*-th value parameter. Evidence: lexical
/// identity of the callee (1) over structural shape of the call (2).
pub const T5_PASSED_LOCAL: &str = "T5-PASSED-LOCAL";
/// The value is the body of the innermost lambda of the manifest chain bound
/// to a local binder `f`: it is `f`'s return value, and the flow continues at
/// every call site of `f` in this module. Evidence: structural shape (2) over
/// lexical identity (1).
pub const T6_RETURNED: &str = "T6-RETURNED";
/// …and at a call site supplying exactly the chain's parameters, the call's
/// spine root is a value location of the same tuple. Evidence: dataflow (3)
/// over 1 and 2.
pub const T7_CALL_RESULT: &str = "T7-CALL-RESULT";
/// The case binder of a scrutiny is an alias of the whole tuple; its own
/// occurrences are followed as value locations, so a match that also keeps
/// the boxed value cannot be mistaken for one that consumes it.
/// Evidence: lexical binder identity (1).
pub const T8_CASE_BINDER_ALIAS: &str = "T8-CASE-BINDER-ALIAS";
/// A use is a value argument of a saturated data-constructor application:
/// the tuple is stored in a field and outlives every scrutiny of it. A
/// proven real value. Evidence: structural shape (2) over `DataConInfo` (4).
pub const T9_STORED: &str = "T9-STORED";
/// A use is an argument of a call this module cannot see into: an import, a
/// class-op dispatch, a partial application, or an unknown higher-order
/// callee. What the callee does with the tuple is outside the module, so the
/// box has to exist — except when even the callee is unknown, which is
/// unresolved rather than proven. Evidence: lexical identity (1), signature
/// lookup (4).
pub const T10_OPAQUE_CALL: &str = "T10-OPAQUE-CALL";
/// Any other use: the tuple applied as a function, bound to an exported
/// binder, returned from an exported function, or reached through a closure
/// whose call sites are not visible. Recorded with a machine-readable
/// reason; never guessed. Evidence: structural shape (2).
pub const T11_ESCAPE: &str = "T11-ESCAPE";

/// Every consumer reads fields, and the flow never left the function the
/// tuple was built in: the allocation can be replaced by its fields.
/// Evidence: def-use over resolved occurrences (3).
pub const F1_SCALAR_REPLACE: &str = "F1-SCALAR-REPLACE";
/// The flow crosses a function boundary and **every** consumer scrutinises
/// the tuple immediately: a worker/CPR return, which becomes a multi-value
/// return. Evidence: def-use (3).
pub const F2_WORKER_RETURN: &str = "F2-WORKER-RETURN";
/// The flow crosses a function boundary and every consumer reads fields, at
/// least one of them by lazy selection or by field-wise re-tupling: a
/// transformer step's state/result triple handed to the next step.
/// Evidence: def-use (3).
pub const F3_STATE_THREAD: &str = "F3-STATE-THREAD";
/// A proven real value: stored in a constructor field, held in a partial
/// application, or handed to a function outside this module. Evidence:
/// whichever `T9`/`T10` use proved it.
pub const F4_PRESERVE: &str = "F4-PRESERVE";
/// A use the rules cannot classify. Carries the reason.
pub const F5_UNRESOLVED: &str = "F5-UNRESOLVED";

// Reasons. `Preserve` reasons name what holds the tuple; `Unresolved`
// reasons name what the rules could not follow.
pub const R_STORED_CON: &str = "stored-in-constructor-field";
pub const R_STORED_TUPLE: &str = "stored-in-a-tuple-field";
pub const R_IMPORTED_LAZY: &str = "passed-to-imported-lazy-parameter";
pub const R_IMPORTED_STRICT: &str = "passed-to-imported-strict-parameter";
pub const R_CLASS_OP: &str = "passed-through-class-op-dispatch";
pub const R_IN_PAP: &str = "held-in-a-partial-application";
pub const R_HIGHER_ORDER: &str = "callee-is-an-unknown-higher-order-value";
pub const R_EXPORTED_RETURN: &str = "returned-from-an-exported-function";
pub const R_EXPORTED_BINDING: &str = "bound-to-an-exported-binding";
pub const R_FUNCTION_ESCAPES: &str = "returning-function-escapes-as-a-value";
pub const R_CALL_UNDERSAT: &str = "call-site-is-a-partial-application";
pub const R_CALL_OVERSAT: &str = "call-site-applies-past-the-return";
pub const R_NESTED_CLOSURE: &str = "returned-from-a-closure-with-no-visible-binding";
pub const R_CLOSURE_ARG: &str = "returned-from-a-closure-passed-to-a-call";
pub const R_CLOSURE_STORED: &str = "returned-from-a-closure-stored-in-a-constructor";
pub const R_APPLIED: &str = "tuple-applied-as-a-function";
pub const R_ALTS: &str = "case-is-not-one-tuple-alternative";
pub const R_PAST_PARAMS: &str = "argument-lands-past-the-callee-parameters";
pub const R_TOO_LARGE: &str = "flow-exceeded-the-location-budget";

/// Locations one flow may visit before it is abandoned as too large. No
/// flow on the `-O1` dump comes anywhere near it; it exists so a pathological
/// module degrades into an honest `Unresolved` instead of a hang.
const LOCATION_BUDGET: usize = 20_000;

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
            TupleUse::PassedToUnknown { .. } => "PassedToUnknown",
            TupleUse::Escapes { .. } => "Escapes",
        }
    }

    pub fn at(self) -> ExprId {
        match self {
            TupleUse::Scrutinised { case, .. } | TupleUse::Selected { case, .. } => case,
            TupleUse::PassedTo { call, .. } | TupleUse::PassedToUnknown { call, .. } => call,
            TupleUse::Retupled { outer } => outer,
            TupleUse::StoredIn { con } => con,
            TupleUse::Escapes { at, .. } => at,
            TupleUse::Returned { .. } => 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TupleFate {
    /// Every consumer reads fields, in the function that built it.
    ScalarReplace,
    /// Flows through transformer-step positions and never escapes.
    StateThread,
    /// Returned from a function whose every call site scrutinises it.
    WorkerReturn,
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
            TupleFate::StateThread => F3_STATE_THREAD,
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
}

/// A location the tuple value reaches, and the accumulated verdict about it.
///
/// A location is a node **plus the number of value arguments still owed**
/// before the tuple appears: 0 means the node's value *is* the tuple, `k`
/// means it is a function that returns the tuple after `k` more arguments.
/// That is what lets the walk leave a function: ascending past a lambda
/// raises the debt, and a call site that pays it exactly is a location of
/// the tuple again. Keyed on the pair, since the same node can be reached
/// with different debts.
struct Walk {
    work: Vec<(ExprId, u32)>,
    seen: HashSet<(ExprId, u32)>,
    consumers: Vec<TupleUse>,
    evidence: Vec<Evidence>,
    /// Escapes, as (is this a proven real value?, reason, detail, node).
    escapes: Vec<(bool, &'static str, String, ExprId)>,
    /// The tuple crossed a *return*: it is the result of a function whose
    /// call sites had to be followed. Passing it into a known callee's
    /// parameter is not that — the box still never outlives its scrutinies
    /// — so only a return sets this.
    returned: bool,
    locations: usize,
    over_budget: bool,
}

impl Walk {
    fn push(&mut self, id: ExprId, owed: u32) {
        if self.seen.insert((id, owed)) {
            self.work.push((id, owed));
        }
    }

    fn use_(&mut self, u: TupleUse) {
        self.consumers.push(u);
    }

    /// The tuple leaves what this analysis can follow. `preserve` says
    /// whether *where* it went proves it is a real value (a constructor
    /// field, a callee outside the module) as opposed to merely being
    /// unfollowable. Records the consumer and the escape together, so the
    /// consumer list is never missing a use.
    fn escape(&mut self, u: TupleUse, preserve: bool, why: &'static str, detail: String) {
        let at = u.at();
        self.consumers.push(u);
        self.escapes.push((preserve, why, detail, at));
    }

    /// An escape with no more specific use kind ([`T11_ESCAPE`]).
    fn escape_at(&mut self, at: ExprId, preserve: bool, why: &'static str, detail: String) {
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
        self.escape(TupleUse::Escapes { at, why }, preserve, why, detail);
    }
}

impl<'m> Tuples<'m> {
    pub fn of_module(m: &'m Module) -> Tuples<'m> {
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
        };
        t.find_constructions();
        t.find_retuplings();
        t.resolve_flows();
        t
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

    fn resolve_flows(&mut self) {
        for i in 0..self.flows.len() {
            let start = self.flows[i].construction;
            let mut w = Walk {
                work: vec![(start, 0)],
                seen: HashSet::from([(start, 0)]),
                consumers: Vec::new(),
                evidence: Vec::new(),
                escapes: Vec::new(),
                returned: false,
                locations: 0,
                over_budget: false,
            };
            let mut bound = None;
            while let Some((v, owed)) = w.work.pop() {
                w.locations += 1;
                if w.locations > LOCATION_BUDGET {
                    w.over_budget = true;
                    break;
                }
                self.step(&mut w, v, owed, start, &mut bound);
            }
            let (fate, reason, detail) = decide(&w);
            let f = &mut self.flows[i];
            f.bound = bound;
            f.locations = w.locations;
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
                    "{} consumer(s) over {} value location(s){}",
                    f.consumers.len(),
                    f.locations,
                    if w.returned {
                        ", crossing a return"
                    } else {
                        ""
                    }
                ),
            });
        }
    }

    /// Classify one value location: what does the context do with the value
    /// there — the tuple itself when `owed` is 0, otherwise a function that
    /// returns it after `owed` more arguments?
    fn step(
        &self,
        w: &mut Walk,
        v: ExprId,
        owed: u32,
        start: ExprId,
        bound: &mut Option<BinderId>,
    ) {
        let m = self.module;
        let Some(parent) = m.parent[v as usize] else {
            // A top-level right-hand side.
            let Edge::Top { pair } = m.edge[v as usize] else {
                w.escape_at(v, false, R_NESTED_CLOSURE, String::new());
                return;
            };
            let b = self.top_pairs[pair as usize];
            self.follow_binding(w, b, v, owed, start, bound, BindSite::Top);
            return;
        };
        match m.edge[v as usize] {
            // A cast or tick is the same value.
            Edge::Cast | Edge::Tick => w.push(parent, owed),
            // The value of the `let`/`case` is this value: keep ascending.
            Edge::LetBody | Edge::CaseAlt { .. } => w.push(parent, owed),
            // Ascending past a lambda: the value here is a function that
            // returns the tuple once one more argument is supplied
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
                self.follow_binding(w, b, v, owed, start, bound, BindSite::Let);
            }
            Edge::CaseScrut if owed == 0 => self.scrutiny(w, parent, v),
            Edge::AppArg => self.argument(w, parent, v, owed),
            // A closure that still owes arguments is applied here: the
            // spine that applies it pays part or all of the debt
            // ([`T7_CALL_RESULT`]).
            Edge::AppFun if owed > 0 => self.applied(w, v, owed),
            // A tuple applied as a function is impossible; a closure
            // scrutinised or handed to a callee is not followed.
            Edge::AppFun => w.escape_at(parent, false, R_APPLIED, String::new()),
            Edge::CaseScrut => w.escape_at(parent, false, R_NESTED_CLOSURE, String::new()),
            Edge::Top { .. } => {}
        }
    }

    /// A value location bound to `b`. With no debt the binder *is* the
    /// tuple and its occurrences are tuple locations ([`T1_LET_BOUND`]);
    /// with a debt it is a function returning it, and its occurrences are
    /// call sites to follow ([`T6_RETURNED`]). Either way the flow is
    /// bounded by the binder's resolved occurrences — unless the binder is
    /// exported, when there are call sites this module cannot see.
    #[allow(clippy::too_many_arguments)]
    fn follow_binding(
        &self,
        w: &mut Walk,
        b: BinderId,
        v: ExprId,
        owed: u32,
        start: ExprId,
        bound: &mut Option<BinderId>,
        site: BindSite,
    ) {
        let m = self.module;
        if owed == 0 && (v == start || m.strip(v) == start) {
            *bound = Some(b);
        }
        if owed > 0 {
            w.use_(TupleUse::Returned { function: b });
        }
        if site == BindSite::Top && m.binder(b).exported == Some(true) {
            let why = if owed > 0 {
                R_EXPORTED_RETURN
            } else {
                R_EXPORTED_BINDING
            };
            w.escape_at(v, false, why, m.binder(b).occ.clone());
            return;
        }
        if owed > 0 {
            w.returned = true;
        }
        // A construction that copies this binder field by field is a
        // consumer of it: it reads every field and allocates its own box,
        // whose fate is decided on its own ([`T4_RETUPLE`]).
        if owed == 0 {
            for outer in self.copies.get(&b).into_iter().flatten() {
                w.use_(TupleUse::Retupled { outer: *outer });
                w.evidence.push(Evidence {
                    rule: T4_RETUPLE,
                    nodes: vec![*outer],
                    binder: Some(b),
                    note: "copied field by field into this construction".into(),
                });
            }
        }
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
    /// tuple) is in the head position of an application spine.
    fn applied(&self, w: &mut Walk, v: ExprId, owed: u32) {
        let m = self.module;
        let root = m.spine_root(v);
        let (_, args) = m.spine(root);
        let n = value_args(&self.scope, &args).len() as u32;
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
            // Still a function: a partial application, which is a value
            // holding the tuple's eventual producer. Keep following it.
            std::cmp::Ordering::Less => w.push(root, owed - n),
            std::cmp::Ordering::Greater => {
                w.escape_at(root, false, R_CALL_OVERSAT, format!("{n} of {owed}"))
            }
        }
    }

    /// `case t of …` ([`T2_SCRUTINISED`] / [`T3_SELECTED`]).
    fn scrutiny(&self, w: &mut Walk, case: ExprId, v: ExprId) {
        let m = self.module;
        let Expr::Case {
            binder, alts, ty, ..
        } = m.expr(case)
        else {
            return;
        };
        let _ = ty;
        // The case binder is an alias of the whole tuple: follow it too, so
        // a match that also keeps the box is not mistaken for one that
        // consumes it ([`T8_CASE_BINDER_ALIAS`]).
        if !m.occurrences(*binder).is_empty() {
            w.evidence.push(Evidence {
                rule: T8_CASE_BINDER_ALIAS,
                nodes: vec![case],
                binder: Some(*binder),
                note: format!(
                    "case binder {} aliases the tuple ({} occurrence(s))",
                    m.binder(*binder).occ,
                    m.occurrences(*binder).len()
                ),
            });
            for occ in m.occurrences(*binder) {
                w.push(*occ, 0);
            }
        }
        // A value of tuple type has exactly one constructor, so a `case` on
        // it that is not one data alternative is either forcing-only (a
        // `DEFAULT` alternative) or an empty case on a diverging scrutinee.
        // Neither reads a field; neither is what the scalar-replacement
        // rules are about, so it is reported rather than assumed benign.
        let Some(alt) = alts
            .first()
            .filter(|a| alts.len() == 1 && matches!(a.con, AltCon::DataAlt { .. }))
        else {
            w.escape_at(
                case,
                false,
                R_ALTS,
                format!("{} alternative(s)", alts.len()),
            );
            return;
        };
        // A field selection: the alternative returns one of its own binders.
        let projected = m
            .resolve(m.strip(alt.rhs))
            .and_then(|r| alt.binders.iter().position(|x| *x == r));
        match projected {
            Some(i) => {
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
            }
            None => {
                w.use_(TupleUse::Scrutinised {
                    case,
                    all_fields_bound: !alt.binders.is_empty(),
                });
                w.evidence.push(Evidence {
                    rule: T2_SCRUTINISED,
                    nodes: vec![case, v],
                    binder: None,
                    note: format!("{} field binder(s) bound", alt.binders.len()),
                });
            }
        }
    }

    /// The value at `v` — the tuple when `owed` is 0, otherwise a closure
    /// that returns it — is a value argument of the spine `app` sits in.
    fn argument(&self, w: &mut Walk, app: ExprId, v: ExprId, owed: u32) {
        let m = self.module;
        let root = m.spine_root(app);
        let (head, args) = m.spine(root);
        let vargs = value_args(&self.scope, &args);
        let Some(idx) = vargs.iter().position(|a| *a == v) else {
            return; // a type argument: not a value flow
        };
        let occ = match m.expr(head) {
            Expr::Var { occ, .. } => occ.clone(),
            _ => String::new(),
        };
        let sig = self.scope.head_sig(head);

        // Stored in a constructor field. With no debt that is the tuple
        // itself: a real allocation holds it, which is the strongest
        // `Preserve` evidence there is. With a debt it is the *closure*
        // that is stored, and whoever pulls it back out and calls it is not
        // visible from here.
        if let Some(dc) = sig.and_then(|s| s.data_con) {
            if vargs.len() < dc.rep_arity as usize {
                w.escape(
                    TupleUse::PassedToUnknown {
                        call: root,
                        why: R_IN_PAP,
                    },
                    owed == 0,
                    R_IN_PAP,
                    occ,
                );
                return;
            }
            if owed > 0 {
                w.escape_at(root, false, R_CLOSURE_STORED, occ);
                return;
            }
            let tuple_field = tuple_con(&dc.name, dc.rep_arity).is_some();
            w.evidence.push(Evidence {
                rule: T9_STORED,
                nodes: vec![root],
                binder: None,
                note: format!("field {idx} of {occ}"),
            });
            w.escape(
                TupleUse::StoredIn { con: root },
                true,
                if tuple_field {
                    R_STORED_TUPLE
                } else {
                    R_STORED_CON
                },
                occ,
            );
            return;
        }

        // A call to something bound in this module to a manifest lambda
        // chain: the argument lands on a parameter whose occurrences are
        // the next value locations — with the same debt it arrived with.
        if let Some(bi) = m.binding_of(head)
            && matches!(bi.site, BindSite::Let | BindSite::Top)
            && let Some(rhs) = bi.rhs
        {
            let params = manifest_params(m, rhs);
            if !params.is_empty() {
                if vargs.len() < params.len() {
                    w.escape(
                        TupleUse::PassedToUnknown {
                            call: root,
                            why: R_IN_PAP,
                        },
                        owed == 0,
                        R_IN_PAP,
                        occ,
                    );
                    return;
                }
                if idx >= params.len() {
                    w.escape(
                        TupleUse::PassedToUnknown {
                            call: root,
                            why: R_PAST_PARAMS,
                        },
                        false,
                        R_PAST_PARAMS,
                        occ,
                    );
                    return;
                }
                let p = params[idx];
                w.use_(TupleUse::PassedTo {
                    call: root,
                    callee: bi.binder,
                    param: idx as u32,
                });
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

        // Everything else: the callee is opaque ([`T10_OPAQUE_CALL`]). A
        // tuple handed to code outside the module has to exist; a *closure*
        // handed out says nothing about the tuple it will return, so that
        // is unresolved rather than proven.
        if owed > 0 {
            w.escape_at(root, false, R_CLOSURE_ARG, occ);
            return;
        }
        let (preserve, why) = match sig {
            Some(s) if s.is_class_op => (true, R_CLASS_OP),
            Some(s) if s.sig_arity() > 0 && m.binding_of(head).is_none() => {
                match s.dmd_args.get(idx) {
                    Some(d) if d.strict => (true, R_IMPORTED_STRICT),
                    _ => (true, R_IMPORTED_LAZY),
                }
            }
            _ => (false, R_HIGHER_ORDER),
        };
        w.evidence.push(Evidence {
            rule: T10_OPAQUE_CALL,
            nodes: vec![root],
            binder: None,
            note: format!("argument {idx} of {occ}: {why}"),
        });
        w.escape(
            TupleUse::PassedToUnknown { call: root, why },
            preserve,
            why,
            occ,
        );
    }
}

/// Value parameters of the manifest lambda chain at `rhs`, in order.
fn manifest_params(m: &Module, rhs: ExprId) -> Vec<BinderId> {
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

/// The fate, from the accumulated uses. Precedence, so that every
/// construction lands in exactly one bucket:
///
/// 1. a proven real value wins over everything — it *is* an allocation;
/// 2. then anything the rules could not follow;
/// 3. then the three plumbing fates, by whether the tuple crossed a return
///    and by how its fields are read.
fn decide(w: &Walk) -> (TupleFate, Option<&'static str>, String) {
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
    if reads
        .iter()
        .all(|u| matches!(u, TupleUse::Scrutinised { .. }))
    {
        return (TupleFate::WorkerReturn, None, String::new());
    }
    (TupleFate::StateThread, None, String::new())
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
    }
}

/// The whole population over a set of modules, with the census' argument
/// sites mapped onto it.
pub struct TupleCensus<'m> {
    pub per_module: Vec<Tuples<'m>>,
    /// Every flow, in module order; the index the [`SiteMap`]s refer to.
    pub flows: Vec<TupleFlow>,
    pub accounting: Accounting,
}

impl<'m> TupleCensus<'m> {
    pub fn of_modules(modules: &'m [&'m Module], census: &Census) -> TupleCensus<'m> {
        let per_module: Vec<Tuples<'m>> = modules.iter().map(|m| Tuples::of_module(m)).collect();
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
        acct.check();
        TupleCensus {
            per_module,
            flows,
            accounting: acct,
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
