//! Higher-order representation agreement: what reaches every
//! function-valued slot in the closed world, and whether one representation
//! can serve it.
//!
//! # The question
//!
//! [`crate::boundary`] asked it of tuples: a formal parameter is **one
//! slot, one representation**, shared by everything that arrives there, so
//! a per-flow proof that *this* tuple can be split says nothing until every
//! other producer of the slot agrees. The same is true, and harder, of
//! closures. A `Rust` closure is a struct of its captured environment plus
//! a code pointer; two closures of different arity, or capturing different
//! things, are different types. A slot that receives both is either
//! `dyn Fn` — a run-time closure that survives — or a cloned callee, one
//! clone per representation.
//!
//! This is therefore **not** a patch for the 67 tuple flows M2.2.1 refused
//! as `closure-returning-the-tuple-is-passed-into-a-parameter`. It is the
//! general boundary analysis those 67 were waiting for, and the tuple
//! residuals are read back out of it at the end as *feedback*, without
//! reclassifying anything ([`Feedback`]).
//!
//! # The population
//!
//! Three kinds of function-valued boundary, each decided by the structured
//! type and never by a name ([`H1_FUNCTION_TYPED`]):
//!
//! * a **parameter** whose binder type is a `FunTy`, or a `ForAllTy` over
//!   one — every value lambda binder in every module;
//! * a **constructor field** at which some pattern match in the closed
//!   world binds a function-typed binder: closures are *stored*;
//! * a **return** whose type, after the function's manifest value
//!   parameters are dropped, is still a `FunTy`: closures are *returned*.
//!
//! # Producers
//!
//! Enumerated independently of any flow walk, exactly as
//! [`crate::boundary`] and [`crate::dictflow`] do it: from the IR's own
//! occurrences, whole-program by stable name, under
//! [`H0_CLOSED_WORLD`] — every call site of a parameter's function in
//! every module, every saturated application of a field's constructor,
//! every syntactic return point of a return's body
//! ([`H2_PRODUCERS`]). A function used as a value, or one nothing in the
//! closed world names, makes the set unenumerable exactly as it does
//! there.
//!
//! A producer that is itself a function-valued boundary — the parameter of
//! a parameter, the result of a known call — contributes *that* boundary's
//! set, in a monovariant worklist fixpoint with the budget discipline of
//! [`crate::dictflow`] ([`H3_PROPAGATE`]).
//!
//! # Two facts, not one
//!
//! **AN ENUMERATED PRODUCER SET IS NOT ONE REPRESENTATION.** As in M2.4c,
//! where a known method target was not a removable dictionary, the
//! enumeration question and the representation question are recorded
//! separately on every boundary ([`Boundary::enumerated`],
//! [`Boundary::classes`]) and only then crossed into a verdict
//! ([`H11_SEPARATE`]). A boundary can have a perfectly enumerated set of
//! nine producers and still need nine representations.
//!
//! The **shape class** ([`H4_SHAPE_CLASS`]) is what decides agreement, and
//! it is deliberately conservative: two producers can share one
//! representation only when they have the same arity *and* the same
//! ordered list of captured-variable types, compared up to
//! alpha-equivalence of the structured type. A producer whose environment
//! the closed world cannot see — a closure read back out of a constructor
//! field, a closure returned by a call into a library — is
//! [`Shape::Opaque`] and never equal to anything, including another
//! `Opaque`.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use h2r_core_ir::{AltCon, BindSite, BinderId, BinderKind, Edge, Expr, ExprId, Module, Ty};
use serde::Serialize;

use crate::callee::split_stable_name;
use crate::scope::Scope;
use crate::shape::value_args;

//------------------------------------------------------------------------------
// Rules
//------------------------------------------------------------------------------

/// **The closed world.** The modules of the dump are the whole program and
/// `Main.main` is its only root, so every call site of every function,
/// every application of every constructor and every use of every closure
/// is in the dump. The same assumption [`crate::dictflow::W0_CLOSED_WORLD`]
/// states, restated here because everything below rests on it. Evidence: a
/// stated assumption about the build (5).
pub const H0_CLOSED_WORLD: &str = "H0-CLOSED-WORLD";
/// **Function-valued.** A boundary is function-valued when its structured
/// type is a `FunTy`, or a `ForAllTy` over one. Never a name, never a
/// rendering. Evidence: GHC type identity (4).
pub const H1_FUNCTION_TYPED: &str = "H1-FUNCTION-TYPED";
/// **Producers.** The producers of a boundary are enumerated from the IR's
/// occurrences over the whole closed world — every call site of the
/// parameter's function, every saturated application of the field's
/// constructor, every syntactic return point of the return's body — and
/// never from a flow walk. Evidence: def-use over stable global identity
/// (3).
pub const H2_PRODUCERS: &str = "H2-PRODUCERS";
/// **Propagation.** A producer that is itself a function-valued boundary
/// contributes that boundary's producer set; the result is a monovariant
/// worklist fixpoint over all boundaries at once. Evidence: def-use
/// dataflow (3).
pub const H3_PROPAGATE: &str = "H3-PROPAGATE";
/// **The shape class.** Two closures can share one representation only
/// when they take the same number of arguments and capture the same
/// ordered list of types, compared up to alpha-equivalence of the
/// structured type. A producer whose environment is not visible is
/// `Opaque` and equal to nothing. Evidence: structural shape (2) over GHC
/// type identity (4).
pub const H4_SHAPE_CLASS: &str = "H4-SHAPE-CLASS";
/// **Exact.** Exactly one producer reaches the boundary and it is a known
/// lambda, partial application or function. Evidence: def-use (3).
pub const H5_EXACT: &str = "H5-EXACT";
/// **Uniform.** Every producer is known and they all fall in one shape
/// class, so one representation serves the slot. Evidence: def-use (3)
/// over [`H4_SHAPE_CLASS`].
pub const H6_UNIFORM: &str = "H6-UNIFORM";
/// **Clone.** Producers in different shape classes at a *parameter* of a
/// local function that is not exported and is never used as a value: one
/// specialised clone per shape class serves them. The clones are counted,
/// never made. Evidence: def-use (3).
pub const H7_CLONE: &str = "H7-CLONE";
/// **Preserve.** A genuine run-time closure reaches the boundary — read
/// back out of a constructor field, or returned by a call the dump cannot
/// see — or the boundary's representation is shared with something the
/// rewrite does not own, because its function is exported or used as a
/// value. The holder is named. Evidence: def-use (3).
pub const H8_PRESERVE: &str = "H8-PRESERVE";
/// **Taint.** A producer the closed world cannot account for makes the set
/// `Top` and the boundary `Unresolved`; nothing is guessed. Evidence:
/// def-use (3).
pub const H9_TAINT: &str = "H9-TAINT";
/// **Budget.** A walk or a fixpoint over a stated budget is `Unresolved`,
/// never a guess. Evidence: structural (2).
pub const H10_BUDGET: &str = "H10-BUDGET";
/// **The two questions are separate.** An enumerated producer set is not
/// one representation: [`Boundary::enumerated`] and [`Boundary::classes`]
/// are recorded from different facts and only then crossed into a verdict.
/// Evidence: a stated property of the proof object (5).
pub const H11_SEPARATE: &str = "H11-SEPARATE";
/// **Uses.** What is done with a boundary — called with *n* arguments,
/// passed on, stored, returned, forced — is read from the occurrences of
/// its binders, following local aliases. Evidence: def-use (3).
pub const H12_USES: &str = "H12-USES";
/// **Landing.** Where a residual closure flow of M2.2.1 lands is the
/// function-typed parameter (or constructor field) of the callee it is
/// handed to, chosen by the *callee's own binder types* and not by the
/// argument expression. Where several function-typed slots of one callee
/// qualify, the worst of their verdicts is reported. Evidence: GHC type
/// identity (4) over structural shape (2).
pub const H13_LANDING: &str = "H13-LANDING";

/// Every rule, with its meaning and evidence level.
pub const RULES: &[(&str, u8, &str)] = &[
    (
        H0_CLOSED_WORLD,
        5,
        "the dump is the whole program and Main.main is its only root (assumption)",
    ),
    (
        H1_FUNCTION_TYPED,
        4,
        "a boundary is function-valued when its structured type is a FunTy (or a ForAll over one)",
    ),
    (
        H2_PRODUCERS,
        3,
        "producers are enumerated from the IR's occurrences over the whole closed world",
    ),
    (
        H3_PROPAGATE,
        3,
        "a producer that is a boundary contributes that boundary's set; a monovariant fixpoint",
    ),
    (
        H4_SHAPE_CLASS,
        2,
        "one representation needs the same arity and the same captured types, up to alpha-eq",
    ),
    (H5_EXACT, 3, "exactly one known producer reaches the slot"),
    (
        H6_UNIFORM,
        3,
        "every producer is known and they all fall in one shape class",
    ),
    (
        H7_CLONE,
        3,
        "disagreeing producers at a local never-a-value parameter cost one clone per shape class",
    ),
    (
        H8_PRESERVE,
        3,
        "a run-time closure reaches the slot, or the slot is shared outside the rewrite",
    ),
    (
        H9_TAINT,
        3,
        "an unaccountable producer taints the set and the boundary is Unresolved",
    ),
    (
        H10_BUDGET,
        2,
        "a walk over budget is Unresolved, never a guess",
    ),
    (
        H11_SEPARATE,
        5,
        "an enumerated producer set is NOT one representation: separate facts",
    ),
    (
        H12_USES,
        3,
        "uses are read from the occurrences of the boundary's binders, through aliases",
    ),
    (
        H13_LANDING,
        4,
        "a residual closure flow lands on the callee's function-typed slots, by binder type",
    ),
];

// Taint / unresolved reasons.
pub const T_USED_AS_A_VALUE: &str = "function-used-as-a-value";
pub const T_PARTIAL_CALL: &str = "call-site-is-a-partial-application";
pub const T_UNREACHABLE: &str = "function-is-unreachable-in-the-closed-world";
pub const T_ANON_LAMBDA: &str = "parameter-of-an-anonymous-lambda";
pub const T_NO_PRODUCER: &str = "no-producer-reaches-the-boundary";
pub const T_HIGHER_ORDER: &str = "closure-from-an-untracked-higher-order-parameter";
pub const T_NOT_A_FUNCTION: &str = "expression-is-not-a-closure";
pub const T_OVER_APPLIED: &str = "call-applies-past-the-callee-parameters";
pub const T_UNKNOWN_CALL: &str = "closure-returned-by-a-call-the-dump-cannot-see";
pub const T_UNTRACKED_RETURN: &str = "closure-returned-by-a-function-with-no-return-boundary";
pub const T_NO_CON_APPS: &str = "constructor-is-never-applied-in-the-closed-world";
pub const B_ROUNDS: &str = "fixpoint-exceeded-the-round-budget";
pub const B_SET: &str = "closure-set-exceeded-the-budget";
pub const B_EVAL: &str = "evaluation-exceeded-the-step-budget";

// Preserve holders.
pub const P_FIELD_READ: &str = "a-closure-read-back-from-a-constructor-field";
pub const P_IMPORTED: &str = "a-closure-returned-by-an-imported-call";
pub const P_EXPORTED: &str = "the-boundary-is-exported-so-its-representation-is-shared";
pub const P_VALUED: &str = "the-boundary-belongs-to-a-function-used-as-a-value";

/// Fixpoint rounds before every unstable boundary is forced to `Top`.
pub const ROUND_BUDGET: usize = 40;
/// Producers in one abstract set before it collapses to `Top`.
pub const SET_CAP: usize = 32;
/// Expression steps in one evaluation.
pub const EVAL_BUDGET: usize = 4000;

//------------------------------------------------------------------------------
// The abstract domain
//------------------------------------------------------------------------------

/// What a function-valued expression can be: a finite set of closure
/// producer identities, or `Top` with the reason it could not be bounded.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ClosureSet {
    Top(String),
    Set(BTreeSet<String>),
}

impl ClosureSet {
    pub fn empty() -> ClosureSet {
        ClosureSet::Set(BTreeSet::new())
    }
    pub fn one(key: &str) -> ClosureSet {
        ClosureSet::Set([key.to_string()].into_iter().collect())
    }
    pub fn is_top(&self) -> bool {
        matches!(self, ClosureSet::Top(_))
    }
    pub fn reason(&self) -> Option<&str> {
        match self {
            ClosureSet::Top(r) => Some(r),
            _ => None,
        }
    }
    pub fn keys(&self) -> &BTreeSet<String> {
        match self {
            ClosureSet::Set(s) => s,
            ClosureSet::Top(_) => EMPTY.get_or_init(BTreeSet::new),
        }
    }
    /// Monotone join. Two `Top`s keep the lexicographically smaller reason,
    /// so a round's result never depends on visit order.
    pub fn join(&mut self, other: &ClosureSet) {
        let joined = match (&*self, other) {
            (ClosureSet::Top(a), ClosureSet::Top(b)) => ClosureSet::Top(a.min(b).clone()),
            (ClosureSet::Top(a), _) => ClosureSet::Top(a.clone()),
            (_, ClosureSet::Top(b)) => ClosureSet::Top(b.clone()),
            (ClosureSet::Set(a), ClosureSet::Set(b)) => {
                let u: BTreeSet<String> = a.union(b).cloned().collect();
                if u.len() > SET_CAP {
                    ClosureSet::Top(B_SET.into())
                } else {
                    ClosureSet::Set(u)
                }
            }
        };
        *self = joined;
    }
}

static EMPTY: std::sync::OnceLock<BTreeSet<String>> = std::sync::OnceLock::new();

//------------------------------------------------------------------------------
// Types, canonically
//------------------------------------------------------------------------------

/// Is this a function type — a `FunTy`, or a `ForAllTy` over one?
/// ([`H1_FUNCTION_TYPED`].)
pub fn is_fun_ty(t: &Ty) -> bool {
    let mut cur = t;
    loop {
        match cur {
            Ty::ForAll { body, .. } => cur = body,
            Ty::Fun { .. } => return true,
            _ => return false,
        }
    }
}

/// The result type after `n` value arrows are dropped, looking through
/// `forall`s. `None` when the type has fewer than `n` arrows — the binder's
/// type and its manifest lambda chain disagree, which is not something to
/// guess about.
pub fn result_after(t: &Ty, n: usize) -> Option<&Ty> {
    let mut cur = t;
    let mut left = n;
    loop {
        match cur {
            Ty::ForAll { body, .. } => cur = body,
            Ty::Fun { res, .. } if left > 0 => {
                left -= 1;
                cur = res;
            }
            _ => return if left == 0 { Some(cur) } else { None },
        }
    }
}

/// A canonical key for a structured type: two types have the same key
/// exactly when they are alpha-equivalent. `forall`-bound variables are
/// replaced by their binding depth, so the key carries no variable name;
/// free variables keep their unique, which is sound because a type's free
/// variables are all bound in the same enclosing term (the same argument
/// [`Ty::alpha_eq`] rests on).
///
/// Iterative, over an explicit stack: a signature can be long.
pub fn ty_key(t: &Ty) -> String {
    enum Step<'a> {
        Ty(&'a Ty, usize),
        Text(&'static str),
        Pop,
    }
    let mut out = String::new();
    let mut bound: Vec<&str> = Vec::new();
    let mut work = vec![Step::Ty(t, 0)];
    while let Some(step) = work.pop() {
        match step {
            Step::Text(s) => out.push_str(s),
            Step::Pop => {
                bound.pop();
            }
            Step::Ty(t, depth) => {
                bound.truncate(depth);
                match t {
                    Ty::Var(v) => {
                        match bound.iter().rposition(|b| *b == v.unique) {
                            // A bound variable is named by how far up it
                            // was bound, so two alpha-variants agree.
                            Some(i) => out.push_str(&format!("b{}", bound.len() - 1 - i)),
                            None => out.push_str(&format!("f{}", v.unique)),
                        }
                    }
                    Ty::Con { tycon, args } => {
                        out.push_str(&format!("C({}", tycon.name));
                        work.push(Step::Text(")"));
                        for a in args.iter().rev() {
                            work.push(Step::Ty(a, depth));
                            work.push(Step::Text(","));
                        }
                    }
                    Ty::App { fun, arg } => {
                        out.push_str("A(");
                        work.push(Step::Text(")"));
                        work.push(Step::Ty(arg, depth));
                        work.push(Step::Text(","));
                        work.push(Step::Ty(fun, depth));
                    }
                    Ty::Fun { mult, arg, res } => {
                        out.push_str("F(");
                        work.push(Step::Text(")"));
                        work.push(Step::Ty(res, depth));
                        work.push(Step::Text(","));
                        work.push(Step::Ty(arg, depth));
                        work.push(Step::Text(","));
                        work.push(Step::Ty(mult, depth));
                    }
                    Ty::ForAll { binder, body } => {
                        out.push_str("V(");
                        bound.push(binder.unique.as_str());
                        work.push(Step::Pop);
                        work.push(Step::Text(")"));
                        work.push(Step::Ty(body, depth + 1));
                    }
                    Ty::Lit { kind, text } => out.push_str(&format!("L({kind},{text})")),
                    Ty::Opaque { pretty } => out.push_str(&format!("O({pretty})")),
                }
            }
        }
    }
    out
}

//------------------------------------------------------------------------------
// Producers
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum ProducerKind {
    /// A manifest lambda, with its captured variables.
    Lambda,
    /// A partial application of a function whose arity is known.
    PartialApplication,
    /// A function defined in the dump, used as a value with no arguments.
    KnownFunction,
    /// An imported id of function type, used as a value: a static function
    /// with no environment.
    ImportedFunction,
    /// A closure read back out of a constructor field.
    FieldRead,
    /// A closure returned by a call the dump cannot see into.
    ImportedCall,
}

impl ProducerKind {
    pub fn name(self) -> &'static str {
        match self {
            ProducerKind::Lambda => "lambda",
            ProducerKind::PartialApplication => "partial application",
            ProducerKind::KnownFunction => "known function as a value",
            ProducerKind::ImportedFunction => "imported function as a value",
            ProducerKind::FieldRead => "closure read from a constructor field",
            ProducerKind::ImportedCall => "closure from an imported call",
        }
    }
}

/// The representation a producer needs ([`H4_SHAPE_CLASS`]).
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Shape {
    /// `arity` arguments, capturing these types in this order.
    Known { arity: usize, captures: Vec<String> },
    /// The environment is not visible: equal to nothing, not even itself.
    Opaque(String),
}

impl Shape {
    /// The class key. Two producers share a representation exactly when
    /// their class keys are equal and neither is opaque.
    pub fn class(&self) -> String {
        match self {
            Shape::Known { arity, captures } => {
                format!("arity={arity};captures=[{}]", captures.join("|"))
            }
            Shape::Opaque(r) => format!("opaque:{r}"),
        }
    }
    pub fn is_opaque(&self) -> bool {
        matches!(self, Shape::Opaque(_))
    }
    /// The class as a report prints it: the arity and the number of
    /// captures, with the capture types elided.
    pub fn short(&self) -> String {
        match self {
            Shape::Known { arity, captures } => {
                format!("arity {arity}, {} capture(s)", captures.len())
            }
            Shape::Opaque(_) => "opaque".to_string(),
        }
    }
}

/// One closure producer in the closed world.
#[derive(Debug, Clone, Serialize)]
pub struct Producer {
    /// `Module#node` for a closure built in the dump, the stable name for
    /// an imported function used as a value, `field:<con>#<i>` for a
    /// closure read back out of a constructor field. **Not** a binder
    /// name: an internal top-level name is not unique (M2.4c).
    pub key: String,
    pub module: String,
    pub node: ExprId,
    pub kind: ProducerKind,
    pub shape: Shape,
    /// The binder the producer is bound to, for the report only.
    pub occ: String,
}

//------------------------------------------------------------------------------
// Boundaries
//------------------------------------------------------------------------------

/// One function-valued slot, and the identity of the fixpoint node.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Slot {
    /// A value lambda binder of function type.
    Param { mi: usize, binder: BinderId },
    /// Field `index` of the constructor with this stable name.
    Field { con: String, index: usize },
    /// What a function returns after its manifest value parameters.
    Return { mi: usize, binder: BinderId },
}

impl Slot {
    pub fn kind(&self) -> &'static str {
        match self {
            Slot::Param { .. } => "param",
            Slot::Field { .. } => "field",
            Slot::Return { .. } => "return",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum UseKind {
    /// Called with `n` value arguments, and `n` is the boundary's arity.
    CalledSaturated,
    /// Called with fewer arguments than the boundary's arity.
    CalledUnder,
    /// Called with more.
    CalledOver,
    /// Called, but the boundary has no single known arity to compare with.
    CalledArityUnknown,
    /// Handed on as an argument of another call.
    PassedOn,
    /// Stored in a constructor field.
    Stored,
    /// It is a return point of the enclosing function.
    Returned,
    /// Scrutinised, or otherwise forced without being applied.
    ForcedOnly,
    /// Anything else.
    Other,
}

impl UseKind {
    pub fn name(self) -> &'static str {
        match self {
            UseKind::CalledSaturated => "called, saturated",
            UseKind::CalledUnder => "called, under-applied",
            UseKind::CalledOver => "called, over-applied",
            UseKind::CalledArityUnknown => "called, arity not agreed",
            UseKind::PassedOn => "passed on to another slot",
            UseKind::Stored => "stored in a constructor",
            UseKind::Returned => "returned",
            UseKind::ForcedOnly => "forced only",
            UseKind::Other => "other",
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize)]
pub struct Use {
    pub kind: UseKind,
    pub at: ExprId,
    /// Value arguments supplied, for a call.
    pub args: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Verdict {
    /// One producer, and it is a known lambda, PAP or function.
    ExactClosure,
    /// Every producer is known and they all share one representation.
    UniformRepresentation,
    /// Every producer is known; they need `n` representations, and one
    /// clone of the callee per representation would serve them. Counted,
    /// never made.
    CloneRequired(usize),
    /// Every producer is known, they disagree, and no clone is available.
    FiniteClosureSet(usize),
    /// A genuine run-time closure reaches it, or the slot is shared
    /// outside the rewrite. The holder is named.
    Preserve(String),
    Unresolved(String),
}

impl Verdict {
    pub fn label(&self) -> &'static str {
        match self {
            Verdict::ExactClosure => "ExactClosure",
            Verdict::UniformRepresentation => "UniformRepresentation",
            Verdict::CloneRequired(_) => "CloneRequired",
            Verdict::FiniteClosureSet(_) => "FiniteClosureSet",
            Verdict::Preserve(_) => "Preserve",
            Verdict::Unresolved(_) => "Unresolved",
        }
    }
    pub fn col(&self) -> usize {
        match self {
            Verdict::ExactClosure => 0,
            Verdict::UniformRepresentation => 1,
            Verdict::CloneRequired(_) => 2,
            Verdict::FiniteClosureSet(_) => 3,
            Verdict::Preserve(_) => 4,
            Verdict::Unresolved(_) => 5,
        }
    }
    /// How bad it is, for picking the worst of several: lower is better.
    pub fn severity(&self) -> usize {
        match self {
            Verdict::ExactClosure => 0,
            Verdict::UniformRepresentation => 1,
            Verdict::CloneRequired(_) => 2,
            Verdict::FiniteClosureSet(_) => 3,
            Verdict::Preserve(_) => 4,
            Verdict::Unresolved(_) => 5,
        }
    }
    /// Does one representation serve the slot?
    pub fn one_representation(&self) -> bool {
        matches!(self, Verdict::ExactClosure | Verdict::UniformRepresentation)
    }
}

pub const VERDICTS: [&str; 6] = [
    "ExactClosure",
    "UniformRepresentation",
    "CloneRequired",
    "FiniteClosureSet",
    "Preserve",
    "Unresolved",
];

/// One function-valued boundary, everything that reaches it, everything
/// done with it, and the verdict.
#[derive(Debug, Clone, Serialize)]
pub struct Boundary {
    pub slot: Slot,
    pub kind: &'static str,
    pub module: String,
    /// How the boundary reads in a report.
    pub name: String,
    /// The node the boundary sits at: the lambda for a parameter, the
    /// right-hand side for a return, 0 for a field.
    pub node: ExprId,
    /// The binder, when the boundary has one (parameter, return).
    #[serde(skip)]
    pub binder: Option<BinderId>,
    pub exported: bool,
    /// The function the boundary belongs to, for the report.
    pub owner: String,
    /// **Fact one**, recorded on its own: every producer is accounted for.
    pub enumerated: bool,
    /// **Fact two**, recorded on its own: how many representations the
    /// producers need. `0` when the set is not enumerated.
    pub classes: usize,
    /// The producer set the fixpoint settled on.
    pub set: ClosureSet,
    /// The producers, resolved.
    pub producers: Vec<Producer>,
    /// Where the producer set was read from: the module, the value node
    /// (the argument at a call site, the field argument at a constructor
    /// application, a return point) and the site it sits in. Kept so an
    /// audit can go from a call site back to the slot it feeds.
    pub sources: Vec<(String, ExprId, ExprId)>,
    pub uses: Vec<Use>,
    /// The single arity every producer agrees on, when there is one.
    pub arity: Option<usize>,
    pub verdict: Verdict,
}

impl Boundary {
    /// The distinct shape classes of the producers, sorted.
    pub fn class_keys(&self) -> Vec<String> {
        let mut v: Vec<String> = self.producers.iter().map(|p| p.shape.class()).collect();
        v.sort();
        v.dedup();
        v
    }
}

//------------------------------------------------------------------------------
// The program
//------------------------------------------------------------------------------

/// The closed world, indexed for whole-program questions. Built
/// independently of [`crate::boundary`] and [`crate::dictflow`]: the
/// producer sets here are enumerated from the IR's own occurrences.
pub struct Program<'m> {
    pub modules: Vec<&'m Module>,
    scopes: Vec<Scope<'m>>,
    /// Stable name → the top-level binding that defines it.
    tops: HashMap<String, (usize, BinderId, ExprId)>,
    /// Stable name → every *global* `Var` occurrence of it, anywhere.
    gvars: HashMap<String, Vec<(usize, ExprId)>>,
    lam_of: Vec<HashMap<BinderId, ExprId>>,
    top_of_rhs: Vec<HashMap<ExprId, BinderId>>,
    case_scrut: Vec<HashMap<BinderId, ExprId>>,
    /// An alt binder → the constructor and field index it is bound at.
    alt_field: Vec<HashMap<BinderId, (String, usize)>>,
    /// Constructor stable name → every saturated application of it.
    con_apps: HashMap<String, Vec<(usize, ExprId)>>,
    /// Producers discovered while evaluating, by key. Filled during the
    /// fixpoint (evaluation is `&self`), read once it has settled.
    found: RefCell<BTreeMap<String, (usize, ExprId, ProducerKind)>>,
}

impl<'m> Program<'m> {
    pub fn new(modules: impl IntoIterator<Item = &'m Module>) -> Program<'m> {
        let modules: Vec<&Module> = modules.into_iter().collect();
        let n = modules.len();
        let scopes: Vec<Scope> = modules.iter().map(|m| Scope::new(m)).collect();
        let mut p = Program {
            modules,
            scopes,
            tops: HashMap::new(),
            gvars: HashMap::new(),
            lam_of: vec![HashMap::new(); n],
            top_of_rhs: vec![HashMap::new(); n],
            case_scrut: vec![HashMap::new(); n],
            alt_field: vec![HashMap::new(); n],
            con_apps: HashMap::new(),
            found: RefCell::new(BTreeMap::new()),
        };
        p.index();
        p
    }

    pub fn m(&self, mi: usize) -> &'m Module {
        self.modules[mi]
    }
    fn s(&self, mi: usize) -> &Scope<'m> {
        &self.scopes[mi]
    }

    fn index(&mut self) {
        for mi in 0..self.modules.len() {
            let m = self.m(mi);
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    if is_external_name(&b.name) {
                        self.tops
                            .entry(b.name.clone())
                            .or_insert((mi, pair.binder, pair.rhs));
                    }
                    self.top_of_rhs[mi].insert(pair.rhs, pair.binder);
                }
            }
            for id in 0..m.exprs.len() as ExprId {
                match m.expr(id) {
                    Expr::Lam { binder, .. } => {
                        self.lam_of[mi].insert(*binder, id);
                    }
                    Expr::Var {
                        name, is_global, ..
                    } => {
                        if *is_global && m.resolve(id).is_none() {
                            self.gvars.entry(name.clone()).or_default().push((mi, id));
                        }
                    }
                    Expr::Case {
                        scrut,
                        binder,
                        alts,
                        ..
                    } => {
                        self.case_scrut[mi].insert(*binder, *scrut);
                        for alt in alts {
                            let AltCon::DataAlt { name, .. } = &alt.con else {
                                continue;
                            };
                            for (i, &bid) in alt.binders.iter().enumerate() {
                                if m.binder(bid).kind == BinderKind::Tyvar {
                                    continue;
                                }
                                self.alt_field[mi].insert(bid, (name.clone(), i));
                            }
                        }
                    }
                    _ => {}
                }
            }
            // Saturated constructor applications, by stable name.
            for id in 0..m.exprs.len() as ExprId {
                let is_app = matches!(m.expr(id), Expr::App { .. });
                if (!is_app && !matches!(m.expr(id), Expr::Var { .. })) || m.spine_root(id) != id {
                    continue;
                }
                let (head, args) = m.spine(id);
                let Some(dc) = self.s(mi).head_sig(head).and_then(|x| x.data_con) else {
                    continue;
                };
                if value_args(self.s(mi), &args).len() < dc.rep_arity as usize {
                    continue;
                }
                self.con_apps
                    .entry(dc.name.clone())
                    .or_default()
                    .push((mi, id));
            }
        }
    }

    /// Value parameters of the manifest lambda chain at `rhs`, in order.
    pub fn lam_params(&self, mi: usize, rhs: ExprId) -> Vec<BinderId> {
        let m = self.m(mi);
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

    /// Every occurrence of a top-level binding, in every module of the
    /// closed world ([`H2_PRODUCERS`]): the local ones through the module's
    /// own binder, the rest by stable name.
    fn all_occurrences(&self, mi: usize, b: BinderId) -> Vec<(usize, ExprId)> {
        let m = self.m(mi);
        let mut out: Vec<(usize, ExprId)> = m.occurrences(b).iter().map(|&o| (mi, o)).collect();
        if m.binding(b).site == BindSite::Top
            && is_external_name(&m.binder(b).name)
            && let Some(g) = self.gvars.get(&m.binder(b).name)
        {
            out.extend(g.iter().copied());
        }
        out
    }

    fn note(&self, key: &str, mi: usize, node: ExprId, kind: ProducerKind) {
        self.found
            .borrow_mut()
            .entry(key.to_string())
            .or_insert((mi, node, kind));
    }
}

/// Is this an *external* name — one another module could refer to, and one
/// that is unique in the program? The same test M2.4c states: GHC gives a
/// top-level binder it has not externalised an internal name, and those are
/// not unique.
pub(crate) fn is_external_name(name: &str) -> bool {
    crate::dictflow::is_external_name(name)
}

//------------------------------------------------------------------------------
// Collecting the boundaries
//------------------------------------------------------------------------------

/// Where the values that reach a boundary come from, enumerated once.
#[derive(Debug, Clone, Default)]
struct Sources {
    /// A source the closed world cannot account for.
    top: Option<String>,
    /// Expressions to evaluate, with the site they were read from:
    /// (module, value node, call / construction / return-point node).
    exprs: Vec<(usize, ExprId, ExprId)>,
}

/// The named function a lambda binder belongs to, and the binder's index
/// among that function's manifest value parameters. Written out here rather
/// than shared with [`crate::dictflow`], so a mistake about what a
/// function's parameters are cannot be common to both.
fn owner_of(p: &Program, mi: usize, b: BinderId) -> (Option<BinderId>, usize) {
    let m = p.m(mi);
    let Some(&lam) = p.lam_of[mi].get(&b) else {
        return (None, 0);
    };
    let mut idx = 0usize;
    let mut cur = lam;
    loop {
        let Some(parent) = m.parent[cur as usize] else {
            return (p.top_of_rhs[mi].get(&cur).copied(), idx);
        };
        match m.edge[cur as usize] {
            Edge::LamBody if matches!(m.expr(parent), Expr::Lam { .. }) => {
                if let Expr::Lam { binder, .. } = m.expr(parent)
                    && m.binder(*binder).kind != BinderKind::Tyvar
                {
                    idx += 1;
                }
                cur = parent;
            }
            Edge::Cast | Edge::Tick => cur = parent,
            Edge::LetRhs { pair } => {
                return match m.expr(parent) {
                    Expr::Let { bind, .. } => (Some(bind.pairs[pair as usize].binder), idx),
                    _ => (None, idx),
                };
            }
            Edge::Top { .. } => return (p.top_of_rhs[mi].get(&cur).copied(), idx),
            _ => return (None, idx),
        }
    }
}

/// Every syntactic return point of `rhs`, with the number of value
/// arguments that had to be supplied to reach it. The same peeling
/// [`crate::boundary::analyse`] does: GHC does not always leave a
/// function's lambdas at the head of its right-hand side.
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

/// A boundary before the fixpoint has run: the slot, the sources, and the
/// facts read off the IR.
struct Raw {
    slot: Slot,
    module: String,
    name: String,
    node: ExprId,
    binder: Option<BinderId>,
    exported: bool,
    owner: String,
    /// The function's own uses are not rewritable call sites.
    valued: bool,
    sources: Sources,
}

/// Every function-valued parameter in the closed world ([`H1_FUNCTION_TYPED`]).
fn collect_params(p: &Program) -> Vec<Raw> {
    let mut out = Vec::new();
    for mi in 0..p.modules.len() {
        let m = p.m(mi);
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Lam { binder, .. } = m.expr(id) else {
                continue;
            };
            let b = *binder;
            if m.binder(b).kind == BinderKind::Tyvar || !is_fun_ty(m.binder_ty(b)) {
                continue;
            }
            let (owner, index) = owner_of(p, mi, b);
            let (owner_name, exported, valued) = match owner {
                Some(f) => (
                    m.binder(f).occ.clone(),
                    m.binding(f).site == BindSite::Top && m.binder(f).exported == Some(true),
                    used_as_a_value(p, mi, f),
                ),
                None => (String::new(), false, true),
            };
            out.push(Raw {
                slot: Slot::Param { mi, binder: b },
                module: m.name.clone(),
                name: format!(
                    "parameter {index} ({}) of {owner_name}#{}",
                    m.binder(b).occ,
                    owner.map(|f| f.to_string()).unwrap_or_else(|| "?".into())
                ),
                node: id,
                binder: Some(b),
                exported,
                owner: owner_name,
                valued,
                sources: param_sources(p, mi, owner, index),
            });
        }
    }
    out
}

/// Is any occurrence of this top-level or let-bound function something
/// other than the head of a saturated call? Then no slot of it can be
/// rewritten without seeing that use too.
fn used_as_a_value(p: &Program, mi: usize, f: BinderId) -> bool {
    let m = p.m(mi);
    let Some(rhs) = m.binding(f).rhs else {
        return true;
    };
    let need = p.lam_params(mi, rhs).len();
    if need == 0 {
        return true;
    }
    for (omi, o) in p.all_occurrences(mi, f) {
        let om = p.m(omi);
        let root = om.spine_root(o);
        if root == o || om.strip(om.spine(root).0) != om.strip(o) {
            return true;
        }
        if value_args(p.s(omi), &om.spine(root).1).len() < need {
            return true;
        }
    }
    false
}

/// Enumerate, over the whole closed world, what produces the `index`th
/// value argument of `owner` ([`H2_PRODUCERS`]).
fn param_sources(p: &Program, mi: usize, owner: Option<BinderId>, index: usize) -> Sources {
    let mut out = Sources::default();
    let Some(f) = owner else {
        out.top = Some(T_ANON_LAMBDA.into());
        return out;
    };
    let m = p.m(mi);
    let need = m
        .binding(f)
        .rhs
        .map(|rhs| p.lam_params(mi, rhs).len())
        .unwrap_or(0);
    let occs = p.all_occurrences(mi, f);
    if occs.is_empty() {
        out.top = Some(T_UNREACHABLE.into());
        return out;
    }
    for (omi, o) in occs {
        let om = p.m(omi);
        let root = om.spine_root(o);
        if root == o {
            out.top = Some(T_USED_AS_A_VALUE.into());
            return out;
        }
        let (head, args) = om.spine(root);
        if om.strip(head) != om.strip(o) {
            out.top = Some(T_USED_AS_A_VALUE.into());
            return out;
        }
        let vargs = value_args(p.s(omi), &args);
        if vargs.len() < need {
            out.top = Some(T_PARTIAL_CALL.into());
            return out;
        }
        match vargs.get(index) {
            Some(&a) => out.exprs.push((omi, a, root)),
            None => out.top = Some(T_PARTIAL_CALL.into()),
        }
    }
    out
}

/// Every constructor field at which some pattern match in the closed world
/// binds a function-typed binder ([`H1_FUNCTION_TYPED`]).
fn collect_fields(p: &Program) -> Vec<Raw> {
    // (con, index) -> the binders bound there.
    let mut fields: BTreeMap<(String, usize), Vec<(usize, BinderId)>> = BTreeMap::new();
    for mi in 0..p.modules.len() {
        let m = p.m(mi);
        for (b, (con, i)) in &p.alt_field[mi] {
            if is_fun_ty(m.binder_ty(*b)) {
                fields.entry((con.clone(), *i)).or_default().push((mi, *b));
            }
        }
    }
    let mut out = Vec::new();
    for ((con, index), binders) in fields {
        let mut sources = Sources::default();
        match p.con_apps.get(&con) {
            None => sources.top = Some(T_NO_CON_APPS.into()),
            Some(apps) => {
                for &(ami, root) in apps {
                    let am = p.m(ami);
                    let (_, args) = am.spine(root);
                    let vargs = value_args(p.s(ami), &args);
                    match vargs.get(index) {
                        Some(&a) => sources.exprs.push((ami, a, root)),
                        None => sources.top = Some(T_PARTIAL_CALL.into()),
                    }
                }
            }
        }
        let occ = split_stable_name(&con)
            .map(|(_, _, o)| o.to_string())
            .unwrap_or_else(|| con.clone());
        let module = split_stable_name(&con)
            .map(|(_, md, _)| md.to_string())
            .unwrap_or_default();
        let mut binders_sorted = binders;
        binders_sorted.sort();
        out.push(Raw {
            slot: Slot::Field {
                con: con.clone(),
                index,
            },
            module,
            name: format!("field {index} of {occ}"),
            node: 0,
            binder: binders_sorted.first().map(|(_, b)| *b),
            // A constructor's fields are shared by every module that can
            // build or match it; the rewrite never owns the slot alone.
            exported: true,
            owner: occ,
            valued: false,
            sources,
        });
        // The reader binders are recorded on the boundary as its uses,
        // below, through `field_readers`.
    }
    out
}

/// The binders every function-typed field of a constructor is read into.
fn field_readers(p: &Program, con: &str, index: usize) -> Vec<(usize, BinderId)> {
    let mut out = Vec::new();
    for mi in 0..p.modules.len() {
        for (b, (c, i)) in &p.alt_field[mi] {
            if c == con && *i == index {
                out.push((mi, *b));
            }
        }
    }
    out.sort();
    out
}

/// Every function whose result, after its manifest value parameters, is
/// still of function type ([`H1_FUNCTION_TYPED`]).
fn collect_returns(p: &Program) -> Vec<Raw> {
    let mut out = Vec::new();
    for mi in 0..p.modules.len() {
        let m = p.m(mi);
        for b in 0..m.binders.len() as BinderId {
            let bi = m.binding(b);
            if !matches!(bi.site, BindSite::Top | BindSite::Let) {
                continue;
            }
            let Some(rhs) = bi.rhs else { continue };
            if m.binder(b).kind == BinderKind::Tyvar {
                continue;
            }
            let params = p.lam_params(mi, rhs);
            if params.is_empty() {
                continue;
            }
            let Some(res) = result_after(m.binder_ty(b), params.len()) else {
                continue;
            };
            if !is_fun_ty(res) {
                continue;
            }
            let leaves = return_points(m, rhs);
            let depth = leaves.iter().map(|(_, d)| *d).max().unwrap_or(0);
            let mut sources = Sources::default();
            for (leaf, d) in &leaves {
                if *d == depth {
                    sources.exprs.push((mi, *leaf, *leaf));
                }
            }
            if depth != params.len() {
                // The lambdas the type says belong to this function and the
                // ones the body has do not line up; refuse rather than pick.
                sources.top = Some(T_NOT_A_FUNCTION.into());
            }
            out.push(Raw {
                slot: Slot::Return { mi, binder: b },
                module: m.name.clone(),
                name: format!("return of {}#{b}", m.binder(b).occ),
                node: rhs,
                binder: Some(b),
                exported: bi.site == BindSite::Top && m.binder(b).exported == Some(true),
                owner: m.binder(b).occ.clone(),
                valued: used_as_a_value(p, mi, b),
                sources,
            });
        }
    }
    out
}

//------------------------------------------------------------------------------
// Evaluating a function-valued expression
//------------------------------------------------------------------------------

type State = HashMap<Slot, ClosureSet>;

/// What closures the expression at `node` can be, under the current state.
/// A worklist over the expression graph: every successor is pushed, never
/// recursed into.
fn eval(p: &Program, st: &State, mi: usize, node: ExprId) -> ClosureSet {
    let mut acc = ClosureSet::empty();
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work = vec![(mi, node)];
    let mut steps = 0usize;
    while let Some((mi, node)) = work.pop() {
        steps += 1;
        if steps > EVAL_BUDGET {
            return ClosureSet::Top(B_EVAL.into());
        }
        if !seen.insert((mi, node)) {
            continue;
        }
        let m = p.m(mi);
        let s = p.s(mi);
        let inner = m.strip(node);
        let (head, args) = m.spine(inner);
        let vargs = value_args(s, &args);

        match m.expr(head) {
            Expr::Case { alts, .. } if vargs.is_empty() => {
                work.extend(alts.iter().map(|a| (mi, a.rhs)));
                continue;
            }
            Expr::Let { body, .. } if vargs.is_empty() => {
                work.push((mi, *body));
                continue;
            }
            // A manifest lambda: the closure is this node.
            Expr::Lam { .. } if vargs.is_empty() => {
                let key = format!("{}#{head}", m.name);
                p.note(&key, mi, head, ProducerKind::Lambda);
                acc.join(&ClosureSet::one(&key));
                continue;
            }
            Expr::Var { .. } => {}
            _ => {
                acc.join(&ClosureSet::Top(T_NOT_A_FUNCTION.into()));
                continue;
            }
        }

        // A local variable at the head.
        if let Some(b) = m.resolve(head) {
            let bi = m.binding(b);
            match bi.site {
                BindSite::Lam => {
                    // A higher-order parameter: its own boundary's set,
                    // when the parameter is one ([`H3_PROPAGATE`]).
                    if !vargs.is_empty() {
                        acc.join(&ClosureSet::Top(T_HIGHER_ORDER.into()));
                    } else {
                        match st.get(&Slot::Param { mi, binder: b }) {
                            Some(v) => acc.join(v),
                            None => acc.join(&ClosureSet::Top(T_HIGHER_ORDER.into())),
                        }
                    }
                }
                BindSite::Let | BindSite::Top => match bi.rhs {
                    Some(rhs) => apply(p, st, mi, mi, b, rhs, inner, &vargs, &mut acc, &mut work),
                    None => acc.join(&ClosureSet::Top(T_NOT_A_FUNCTION.into())),
                },
                BindSite::CaseBinder => match p.case_scrut[mi].get(&b) {
                    Some(&scrut) if vargs.is_empty() => work.push((mi, scrut)),
                    _ => acc.join(&ClosureSet::Top(T_NOT_A_FUNCTION.into())),
                },
                // A closure read back out of a constructor field: a genuine
                // run-time closure, identified by the field it came from.
                BindSite::AltBinder => match p.alt_field[mi].get(&b) {
                    Some((con, i)) => {
                        let key = format!("field:{con}#{i}");
                        p.note(&key, mi, head, ProducerKind::FieldRead);
                        acc.join(&ClosureSet::one(&key));
                    }
                    None => acc.join(&ClosureSet::Top(T_NOT_A_FUNCTION.into())),
                },
            }
            continue;
        }

        // A global.
        let Expr::Var { name, .. } = m.expr(head) else {
            unreachable!("head is a Var here")
        };
        if let Some(&(wi, wb, rhs)) = p.tops.get(name) {
            apply(p, st, mi, wi, wb, rhs, inner, &vargs, &mut acc, &mut work);
            continue;
        }
        let sig = s.head_sig(head);
        if sig.and_then(|x| x.data_con).is_some() {
            // A constructor is not a closure; a partially applied one is,
            // but the dump never leaves one behind here.
            acc.join(&ClosureSet::Top(T_NOT_A_FUNCTION.into()));
            continue;
        }
        let arity = sig.map(|x| x.arity as usize).unwrap_or(0);
        if vargs.is_empty() && arity > 0 {
            // An imported function used as a value: a static function with
            // no environment.
            p.note(name, mi, head, ProducerKind::ImportedFunction);
            acc.join(&ClosureSet::one(name));
        } else if vargs.is_empty() {
            acc.join(&ClosureSet::Top(T_UNKNOWN_CALL.into()));
        } else if vargs.len() < arity {
            let key = format!("{}#{inner}", m.name);
            p.note(&key, mi, inner, ProducerKind::PartialApplication);
            acc.join(&ClosureSet::one(&key));
        } else {
            // A closure returned by a call into a library.
            let key = format!("{}#{inner}", m.name);
            p.note(&key, mi, inner, ProducerKind::ImportedCall);
            acc.join(&ClosureSet::one(&key));
        }
    }
    acc
}

/// A spine whose head is a function bound in the dump, applied to
/// `vargs.len()` value arguments.
#[allow(clippy::too_many_arguments)]
fn apply(
    p: &Program,
    st: &State,
    cmi: usize,
    fmi: usize,
    fb: BinderId,
    rhs: ExprId,
    inner: ExprId,
    vargs: &[ExprId],
    acc: &mut ClosureSet,
    work: &mut Vec<(usize, ExprId)>,
) {
    let fm = p.m(fmi);
    let params = p.lam_params(fmi, rhs);
    let n = vargs.len();
    if params.is_empty() {
        // An alias: the binder *is* its right-hand side.
        if n == 0 {
            work.push((fmi, rhs));
        } else {
            acc.join(&ClosureSet::Top(T_NOT_A_FUNCTION.into()));
        }
        return;
    }
    if n == 0 {
        // The function used as a value: the closure is its lambda.
        let lam = fm.strip(rhs);
        let key = format!("{}#{lam}", fm.name);
        p.note(&key, fmi, lam, ProducerKind::KnownFunction);
        acc.join(&ClosureSet::one(&key));
    } else if n < params.len() {
        // A partial application: a closure over the arguments supplied. It
        // lives in the module the *call* is in, not the callee's.
        let key = format!("{}#{inner}", p.m(cmi).name);
        p.note(&key, cmi, inner, ProducerKind::PartialApplication);
        acc.join(&ClosureSet::one(&key));
    } else if n == params.len() {
        // Saturated: the closure is whatever the body returns.
        match st.get(&Slot::Return {
            mi: fmi,
            binder: fb,
        }) {
            Some(v) => acc.join(v),
            None => acc.join(&ClosureSet::Top(T_UNTRACKED_RETURN.into())),
        }
    } else {
        acc.join(&ClosureSet::Top(T_OVER_APPLIED.into()));
    }
}

//------------------------------------------------------------------------------
// Producers, resolved
//------------------------------------------------------------------------------

/// The local binders a lambda's body reads that the lambda does not bind:
/// its captured environment. Iterative over the subtree.
fn captures(m: &Module, lam: ExprId) -> Vec<BinderId> {
    let mut bound: HashSet<BinderId> = HashSet::new();
    let mut free: BTreeSet<BinderId> = BTreeSet::new();
    for id in m.preorder(lam) {
        match m.expr(id) {
            Expr::Lam { binder, .. } => {
                bound.insert(*binder);
            }
            Expr::Let { bind, .. } => {
                for pr in &bind.pairs {
                    bound.insert(pr.binder);
                }
            }
            Expr::Case { binder, alts, .. } => {
                bound.insert(*binder);
                for a in alts {
                    bound.extend(a.binders.iter().copied());
                }
            }
            _ => {}
        }
    }
    for id in m.preorder(lam) {
        if let Some(b) = m.resolve(id)
            && !bound.contains(&b)
            && m.binding(b).site != BindSite::Top
            && m.binder(b).kind != BinderKind::Tyvar
        {
            free.insert(b);
        }
    }
    free.into_iter().collect()
}

/// The shape of a producer: its arity and the types it captures
/// ([`H4_SHAPE_CLASS`]).
fn shape_of(p: &Program, mi: usize, node: ExprId, kind: ProducerKind, key: &str) -> Shape {
    let m = p.m(mi);
    match kind {
        ProducerKind::FieldRead => Shape::Opaque(P_FIELD_READ.into()),
        ProducerKind::ImportedCall => Shape::Opaque(P_IMPORTED.into()),
        ProducerKind::ImportedFunction => Shape::Known {
            arity: p
                .s(mi)
                .head_sig(node)
                .map(|x| x.arity as usize)
                .unwrap_or(0),
            captures: Vec::new(),
        },
        ProducerKind::Lambda | ProducerKind::KnownFunction => {
            let arity = p.lam_params(mi, node).len();
            let caps = captures(m, node);
            Shape::Known {
                arity,
                captures: caps.iter().map(|b| ty_key(m.binder_ty(*b))).collect(),
            }
        }
        ProducerKind::PartialApplication => {
            let (head, args) = m.spine(node);
            let vargs = value_args(p.s(mi), &args);
            let arity = head_arity(p, mi, head).saturating_sub(vargs.len());
            let captures = vargs
                .iter()
                .map(|&a| arg_ty_key(p, mi, a))
                .collect::<Vec<_>>();
            let _ = key;
            Shape::Known { arity, captures }
        }
    }
}

/// How many value arguments the head of a spine takes before it does work.
fn head_arity(p: &Program, mi: usize, head: ExprId) -> usize {
    let m = p.m(mi);
    if let Some(b) = m.resolve(head)
        && let Some(rhs) = m.binding(b).rhs
    {
        let n = p.lam_params(mi, rhs).len();
        if n > 0 {
            return n;
        }
    }
    if let Expr::Var { name, .. } = m.expr(head)
        && let Some(&(wi, _, rhs)) = p.tops.get(name)
    {
        let n = p.lam_params(wi, rhs).len();
        if n > 0 {
            return n;
        }
    }
    p.s(mi)
        .head_sig(head)
        .map(|x| x.arity as usize)
        .unwrap_or(0)
}

/// The type key of an argument expression. Only a variable carries a type
/// here — binders do, expressions do not — so anything else gets a key
/// unique to its node, which can never match another producer's. Refusing
/// to merge is the conservative direction.
fn arg_ty_key(p: &Program, mi: usize, a: ExprId) -> String {
    let m = p.m(mi);
    let inner = m.strip(a);
    match m.resolve(inner) {
        Some(b) => ty_key(m.binder_ty(b)),
        None => format!("?{}#{inner}", m.name),
    }
}

//------------------------------------------------------------------------------
// Uses
//------------------------------------------------------------------------------

/// What is done with the closure at this occurrence ([`H12_USES`]).
fn classify_use(p: &Program, mi: usize, occ: ExprId, work: &mut Vec<(usize, ExprId)>) -> Use {
    let m = p.m(mi);
    let s = p.s(mi);
    // Is the occurrence itself the head of an application?
    let root = m.spine_root(occ);
    if root != occ {
        let (head, args) = m.spine(root);
        if m.strip(head) == m.strip(occ) {
            return Use {
                kind: UseKind::CalledArityUnknown,
                at: root,
                args: value_args(s, &args).len(),
            };
        }
    }
    let mut cur = occ;
    while let Some(parent) = m.parent[cur as usize] {
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => cur = parent,
            Edge::CaseScrut => {
                return Use {
                    kind: UseKind::ForcedOnly,
                    at: parent,
                    args: 0,
                };
            }
            Edge::AppArg => {
                let root = m.spine_root(parent);
                let (head, _) = m.spine(root);
                let stored = s.head_sig(head).and_then(|x| x.data_con).is_some();
                return Use {
                    kind: if stored {
                        UseKind::Stored
                    } else {
                        UseKind::PassedOn
                    },
                    at: root,
                    args: 0,
                };
            }
            Edge::LetRhs { pair } => {
                let Expr::Let { bind, .. } = m.expr(parent) else {
                    return Use {
                        kind: UseKind::Other,
                        at: parent,
                        args: 0,
                    };
                };
                let b = bind.pairs[pair as usize].binder;
                for &o in m.occurrences(b) {
                    work.push((mi, o));
                }
                return Use {
                    kind: UseKind::Other,
                    at: parent,
                    args: 0,
                };
            }
            Edge::LamBody | Edge::LetBody | Edge::CaseAlt { .. } => {
                return Use {
                    kind: UseKind::Returned,
                    at: cur,
                    args: 0,
                };
            }
            Edge::Top { .. } => {
                return Use {
                    kind: UseKind::Returned,
                    at: cur,
                    args: 0,
                };
            }
            _ => {
                return Use {
                    kind: UseKind::Other,
                    at: parent,
                    args: 0,
                };
            }
        }
    }
    Use {
        kind: UseKind::Returned,
        at: cur,
        args: 0,
    }
}

/// Every use of a boundary, from its binders' occurrences.
fn uses_of(p: &Program, r: &Raw) -> Vec<Use> {
    let mut occs: Vec<(usize, ExprId)> = Vec::new();
    match &r.slot {
        Slot::Param { mi, binder } => {
            occs.extend(p.m(*mi).occurrences(*binder).iter().map(|&o| (*mi, o)));
        }
        Slot::Field { con, index } => {
            for (fmi, b) in field_readers(p, con, *index) {
                occs.extend(p.m(fmi).occurrences(b).iter().map(|&o| (fmi, o)));
            }
        }
        Slot::Return { mi, binder } => {
            // The closure a call produces is the call node itself.
            let m = p.m(*mi);
            let need = m
                .binding(*binder)
                .rhs
                .map(|rhs| p.lam_params(*mi, rhs).len())
                .unwrap_or(0);
            for (omi, o) in p.all_occurrences(*mi, *binder) {
                let om = p.m(omi);
                let root = om.spine_root(o);
                if root == o || om.strip(om.spine(root).0) != om.strip(o) {
                    continue;
                }
                if value_args(p.s(omi), &om.spine(root).1).len() == need {
                    occs.push((omi, root));
                }
            }
        }
    }
    let mut out = Vec::new();
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work = occs;
    let mut steps = 0usize;
    while let Some((mi, o)) = work.pop() {
        steps += 1;
        if steps > EVAL_BUDGET {
            break;
        }
        if !seen.insert((mi, o)) {
            continue;
        }
        out.push(classify_use(p, mi, o, &mut work));
    }
    out
}

//------------------------------------------------------------------------------
// The analysis
//------------------------------------------------------------------------------

#[derive(Debug, Default, Serialize)]
pub struct Accounting {
    pub boundaries: usize,
    pub rounds: usize,
    pub round_budget_hit: bool,
    /// Boundaries whose producer set the fixpoint bounded: **fact one**,
    /// on its own.
    pub enumerated: usize,
    /// Of the enumerated, those that need exactly one representation:
    /// **fact two**, on its own.
    pub one_representation: usize,
    /// kind → verdict counts, in [`VERDICTS`] order.
    pub by_kind: BTreeMap<&'static str, [usize; 6]>,
    pub verdicts: [usize; 6],
    /// Enumeration × representation, the two facts crossed.
    pub matrix: [[usize; 2]; 2],
    pub producers: usize,
    pub by_producer_kind: BTreeMap<&'static str, usize>,
    pub by_use_kind: BTreeMap<&'static str, usize>,
    /// Shape class → how many boundaries have a producer in it.
    pub shape_classes: BTreeMap<String, usize>,
    /// The same, by the printable `(arity, captures)` summary.
    pub shape_shapes: BTreeMap<String, usize>,
    pub distinct_shape_classes: usize,
    pub clones: usize,
    pub reasons: BTreeMap<String, usize>,
}

impl Accounting {
    /// boundaries = the six verdicts; the per-kind rows sum to the same;
    /// and the 2×2 of the two separate facts sums to the population.
    pub fn check(&self) -> Result<(), String> {
        if self.verdicts.iter().sum::<usize>() != self.boundaries {
            return Err(format!(
                "boundaries {} != {:?}",
                self.boundaries, self.verdicts
            ));
        }
        let mut per = [0usize; 6];
        for row in self.by_kind.values() {
            for (i, n) in row.iter().enumerate() {
                per[i] += n;
            }
        }
        if per != self.verdicts {
            return Err(format!("by-kind {per:?} != verdicts {:?}", self.verdicts));
        }
        let m: usize = self.matrix.iter().flatten().sum();
        if m != self.boundaries {
            return Err(format!("matrix {m} != boundaries {}", self.boundaries));
        }
        if self.matrix[1][0] + self.matrix[1][1] != self.enumerated {
            return Err("matrix enumerated row disagrees with the count".into());
        }
        Ok(())
    }
}

/// The whole-program higher-order representation analysis.
pub struct Higher {
    pub boundaries: Vec<Boundary>,
    /// The settled producer set of every slot, for the ad-hoc questions
    /// the feedback asks about expressions that are not boundaries.
    #[allow(clippy::type_complexity)]
    pub state: HashMap<Slot, ClosureSet>,
    pub rounds: usize,
    pub round_budget_hit: bool,
    /// Every producer the analysis resolved, by key.
    pub producers: BTreeMap<String, Producer>,
}

impl Higher {
    pub fn of_modules<'a>(modules: impl IntoIterator<Item = &'a Module>) -> Higher {
        let p = Program::new(modules);
        Self::of_program(&p)
    }

    pub fn of_program(p: &Program) -> Higher {
        let mut raws: Vec<Raw> = collect_params(p);
        raws.extend(collect_fields(p));
        raws.extend(collect_returns(p));
        let mut state: State = raws
            .iter()
            .map(|r| (r.slot.clone(), ClosureSet::empty()))
            .collect();

        let mut rounds = 0usize;
        let mut hit = false;
        loop {
            rounds += 1;
            let mut changed = false;
            let mut next = state.clone();
            for r in &raws {
                let mut acc = ClosureSet::empty();
                if let Some(t) = &r.sources.top {
                    acc.join(&ClosureSet::Top(t.clone()));
                }
                for &(smi, node, _) in &r.sources.exprs {
                    let v = eval(p, &state, smi, node);
                    acc.join(&v);
                }
                let slot = next.get_mut(&r.slot).unwrap();
                if *slot != acc {
                    *slot = acc;
                    changed = true;
                }
            }
            state = next;
            if !changed {
                break;
            }
            if rounds >= ROUND_BUDGET {
                hit = true;
                for v in state.values_mut() {
                    if !v.is_top() {
                        v.join(&ClosureSet::Top(B_ROUNDS.into()));
                    }
                }
                break;
            }
        }

        // The producers the walk found, resolved once the sets are settled.
        let found = p.found.borrow().clone();
        let mut producers: BTreeMap<String, Producer> = BTreeMap::new();
        for (key, (mi, node, kind)) in &found {
            let m = p.m(*mi);
            producers.insert(
                key.clone(),
                Producer {
                    key: key.clone(),
                    module: m.name.clone(),
                    node: *node,
                    kind: *kind,
                    shape: shape_of(p, *mi, *node, *kind, key),
                    occ: match m.expr(m.strip(*node)) {
                        Expr::Var { occ, .. } => occ.clone(),
                        _ => String::new(),
                    },
                },
            );
        }

        let mut boundaries = Vec::new();
        for r in &raws {
            let set = state[&r.slot].clone();
            let uses = uses_of(p, r);
            let mut ps: Vec<Producer> = set
                .keys()
                .iter()
                .filter_map(|k| producers.get(k).cloned())
                .collect();
            ps.sort_by(|a, b| a.key.cmp(&b.key));
            let enumerated = !set.is_top() && !set.keys().is_empty();
            let mut classes: Vec<String> = ps.iter().map(|x| x.shape.class()).collect();
            classes.sort();
            classes.dedup();
            let n_classes = if enumerated { classes.len() } else { 0 };
            let arity = one_arity(&ps);
            let verdict = judge(r, &set, &ps, n_classes);
            let uses = retime(uses, arity);
            boundaries.push(Boundary {
                kind: r.slot.kind(),
                slot: r.slot.clone(),
                module: r.module.clone(),
                name: r.name.clone(),
                node: r.node,
                binder: r.binder,
                exported: r.exported,
                owner: r.owner.clone(),
                enumerated,
                classes: n_classes,
                set,
                producers: ps,
                sources: r
                    .sources
                    .exprs
                    .iter()
                    .map(|&(smi, n, at)| (p.m(smi).name.clone(), n, at))
                    .collect(),
                uses,
                arity,
                verdict,
            });
        }

        Higher {
            boundaries,
            state,
            rounds,
            round_budget_hit: hit,
            producers,
        }
    }

    /// The verdict of the boundary a binder names: its parameter boundary
    /// if the binder is a lambda-bound parameter, its return boundary if it
    /// is a function. **The API [M2.4e](crate::parsec) calls** to ask what
    /// a continuation slot's representation is.
    pub fn verdict_for(&self, module: &str, binder: BinderId) -> Option<&Boundary> {
        self.boundaries
            .iter()
            .find(|b| b.module == module && b.binder == Some(binder))
    }

    /// Every boundary of one module.
    pub fn in_module<'a>(&'a self, module: &'a str) -> impl Iterator<Item = &'a Boundary> {
        self.boundaries.iter().filter(move |b| b.module == module)
    }

    pub fn accounting(&self) -> Accounting {
        let mut a = Accounting {
            boundaries: self.boundaries.len(),
            rounds: self.rounds,
            round_budget_hit: self.round_budget_hit,
            ..Default::default()
        };
        let mut classes: BTreeSet<String> = BTreeSet::new();
        for b in &self.boundaries {
            a.verdicts[b.verdict.col()] += 1;
            a.by_kind.entry(b.kind).or_insert([0; 6])[b.verdict.col()] += 1;
            if b.enumerated {
                a.enumerated += 1;
            }
            let one = b.enumerated && b.classes == 1;
            if one {
                a.one_representation += 1;
            }
            a.matrix[usize::from(b.enumerated)][usize::from(one)] += 1;
            for k in b.class_keys() {
                classes.insert(k.clone());
                *a.shape_classes.entry(k).or_default() += 1;
            }
            let mut shorts: Vec<String> = b.producers.iter().map(|x| x.shape.short()).collect();
            shorts.sort();
            shorts.dedup();
            for k in shorts {
                *a.shape_shapes.entry(k).or_default() += 1;
            }
            for u in &b.uses {
                *a.by_use_kind.entry(u.kind.name()).or_default() += 1;
            }
            if let Verdict::CloneRequired(n) = &b.verdict {
                a.clones += n;
            }
            match &b.verdict {
                Verdict::Preserve(r) | Verdict::Unresolved(r) => {
                    *a.reasons.entry(reason_head(r)).or_default() += 1;
                }
                _ => {}
            }
        }
        a.distinct_shape_classes = classes.len();
        a.producers = self.producers.len();
        for x in self.producers.values() {
            *a.by_producer_kind.entry(x.kind.name()).or_default() += 1;
        }
        a
    }
}

/// The one arity every producer agrees on, when there is one.
fn one_arity(ps: &[Producer]) -> Option<usize> {
    let mut it = ps.iter().filter_map(|x| match &x.shape {
        Shape::Known { arity, .. } => Some(*arity),
        Shape::Opaque(_) => None,
    });
    let first = it.next()?;
    if it.all(|a| a == first) && ps.iter().all(|x| !x.shape.is_opaque()) {
        Some(first)
    } else {
        None
    }
}

/// Re-classify the call uses now that the boundary's arity is known.
fn retime(uses: Vec<Use>, arity: Option<usize>) -> Vec<Use> {
    uses.into_iter()
        .map(|mut u| {
            if u.kind == UseKind::CalledArityUnknown
                && let Some(a) = arity
            {
                u.kind = match u.args.cmp(&a) {
                    std::cmp::Ordering::Equal => UseKind::CalledSaturated,
                    std::cmp::Ordering::Less => UseKind::CalledUnder,
                    std::cmp::Ordering::Greater => UseKind::CalledOver,
                };
            }
            u
        })
        .collect()
}

/// The verdict, from the two facts kept apart ([`H11_SEPARATE`]).
fn judge(r: &Raw, set: &ClosureSet, ps: &[Producer], classes: usize) -> Verdict {
    if let ClosureSet::Top(t) = set {
        return Verdict::Unresolved(t.clone());
    }
    if ps.is_empty() {
        return Verdict::Unresolved(T_NO_PRODUCER.into());
    }
    // A producer whose environment the closed world cannot see is a genuine
    // run-time closure ([`H8_PRESERVE`]).
    if let Some(o) = ps.iter().find(|x| x.shape.is_opaque()) {
        let holder = match &o.shape {
            Shape::Opaque(why) => why.clone(),
            _ => unreachable!(),
        };
        return Verdict::Preserve(format!("{holder} ({} node {})", o.module, o.node));
    }
    if ps.len() == 1 {
        return Verdict::ExactClosure;
    }
    if classes <= 1 {
        return Verdict::UniformRepresentation;
    }
    // The producers disagree. Only a *parameter* of a local function that
    // is not exported and never used as a value can be cloned: every call
    // site of it is visible and rewritable ([`H7_CLONE`]).
    if matches!(r.slot, Slot::Param { .. }) && !r.exported && !r.valued {
        return Verdict::CloneRequired(classes);
    }
    if r.exported {
        return Verdict::Preserve(format!("{P_EXPORTED} ({} {})", r.module, r.owner));
    }
    if r.valued {
        return Verdict::Preserve(format!("{P_VALUED} ({} {})", r.module, r.owner));
    }
    Verdict::FiniteClosureSet(ps.len())
}

/// The kind of a reason, for grouping: everything before a `;` and before a
/// parenthesised witness, which names a node and so is never the group.
pub fn reason_head(r: &str) -> String {
    let r = r.split(';').next().unwrap_or(r);
    r.split(" (").next().unwrap_or(r).trim().to_string()
}

//------------------------------------------------------------------------------
// Feeding the proof back into the residues
//------------------------------------------------------------------------------

/// Where one residual flow or census site lands, and what the boundary
/// analysis says about it. **Nothing here reclassifies anything**: every
/// verdict M2.2.1 and M2.1 recorded stands exactly as it was, and this is
/// an additional column beside it.
#[derive(Debug, Clone, Serialize)]
pub struct Landing {
    pub module: String,
    /// The node the residual was recorded at.
    pub node: ExprId,
    /// The residual's own reason or resolution, unchanged.
    pub residual: String,
    /// The boundary it lands on, when the closed world has one.
    pub boundary: Option<String>,
    pub verdict: String,
    /// Would one representation serve the slot?
    pub one_representation: bool,
    /// Why there is no boundary, when there is none.
    pub why: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct Section {
    pub label: String,
    pub landings: Vec<Landing>,
    /// verdict → count.
    pub by_verdict: BTreeMap<String, usize>,
    /// How many **could** be reclassified by a later pass: the landing slot
    /// needs one representation. Reported, never acted on.
    pub could_reclassify: usize,
}

impl Section {
    fn build(label: &str, landings: Vec<Landing>) -> Section {
        let mut by_verdict: BTreeMap<String, usize> = BTreeMap::new();
        let mut could = 0usize;
        for l in &landings {
            *by_verdict.entry(l.verdict.clone()).or_default() += 1;
            if l.one_representation {
                could += 1;
            }
        }
        Section {
            label: label.to_string(),
            landings,
            by_verdict,
            could_reclassify: could,
        }
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct Feedback {
    /// (a) the 67 `closure-returning-the-tuple-is-passed-into-a-parameter`.
    pub into_param: Section,
    /// (b) the closure paths of the tuple residual: imported call, list
    /// cons, program constructor.
    pub closure_paths: Vec<Section>,
    /// (c) the census' higher-order-parameter and computed-closure sites.
    pub census: Vec<Section>,
}

/// The worst verdict among a callee's function-typed slots
/// ([`H13_LANDING`]).
fn worst<'a>(h: &'a Higher, slots: &[Slot]) -> Option<&'a Boundary> {
    h.boundaries
        .iter()
        .filter(|b| slots.contains(&b.slot))
        .max_by_key(|b| b.verdict.severity())
}

impl Higher {
    /// The function-typed parameter slots of the callee at the head of the
    /// spine rooted at `root`, chosen by the callee's own binder types.
    fn callee_param_slots(
        &self,
        p: &Program,
        mi: usize,
        root: ExprId,
    ) -> (Vec<Slot>, Option<String>) {
        let m = p.m(mi);
        let (head, _) = m.spine(root);
        let (cmi, cb) = match m.resolve(head) {
            Some(b) => (mi, b),
            None => match m.expr(head) {
                Expr::Var { name, .. } => match p.tops.get(name) {
                    Some(&(wi, b, _)) => (wi, b),
                    None => {
                        return (
                            Vec::new(),
                            Some("the callee is outside the closed world".into()),
                        );
                    }
                },
                _ => return (Vec::new(), Some("the callee is not a variable".into())),
            },
        };
        let cm = p.m(cmi);
        let Some(rhs) = cm.binding(cb).rhs else {
            return (
                Vec::new(),
                Some("the callee has no body in the dump".into()),
            );
        };
        let slots: Vec<Slot> = p
            .lam_params(cmi, rhs)
            .into_iter()
            .filter(|b| is_fun_ty(cm.binder_ty(*b)))
            .map(|b| Slot::Param { mi: cmi, binder: b })
            .collect();
        if slots.is_empty() {
            return (
                slots,
                Some("the callee has no function-typed parameter".into()),
            );
        }
        (slots, None)
    }

    /// The function-typed field slots of the constructor at the head of the
    /// spine rooted at `root`.
    fn con_field_slots(&self, p: &Program, mi: usize, root: ExprId) -> (Vec<Slot>, Option<String>) {
        let m = p.m(mi);
        let (head, _) = m.spine(root);
        let Some(dc) = p.s(mi).head_sig(head).and_then(|x| x.data_con) else {
            return (Vec::new(), Some("the head is not a constructor".into()));
        };
        let slots: Vec<Slot> = self
            .boundaries
            .iter()
            .filter_map(|b| match &b.slot {
                Slot::Field { con, .. } if *con == dc.name => Some(b.slot.clone()),
                _ => None,
            })
            .collect();
        if slots.is_empty() {
            return (
                slots,
                Some("no function-typed field of this constructor is ever read back".into()),
            );
        }
        (slots, None)
    }

    fn landing(
        &self,
        p: &Program,
        mi: usize,
        node: ExprId,
        residual: &str,
        slots: Vec<Slot>,
        why: Option<String>,
    ) -> Landing {
        let m = p.m(mi);
        match worst(self, &slots) {
            Some(b) => Landing {
                module: m.name.clone(),
                node,
                residual: residual.to_string(),
                boundary: Some(b.name.clone()),
                verdict: b.verdict.label().to_string(),
                one_representation: b.verdict.one_representation(),
                why: None,
            },
            None => Landing {
                module: m.name.clone(),
                node,
                residual: residual.to_string(),
                boundary: None,
                verdict: "NoBoundary".to_string(),
                one_representation: false,
                why: why.or_else(|| Some("the slot is not in the closed world".into())),
            },
        }
    }
}

/// One residual the feedback reads: a module index, a node, and the reason
/// it was recorded under. Built by the caller from the tuple census and the
/// argument census, so this module depends on neither.
#[derive(Debug, Clone)]
pub struct Residual {
    pub mi: usize,
    pub node: ExprId,
    pub reason: String,
    pub via: Via,
}

/// How the residual reaches a boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Via {
    /// The node is a call; the closure lands on the callee's function-typed
    /// parameters.
    CalleeParam,
    /// The node is a constructor application; the closure lands in one of
    /// its function-typed fields.
    ConField,
    /// The node is a call into a library: there is no slot in the dump.
    Imported,
    /// The node is a spine whose *head* is the closure: its boundary is the
    /// head's own.
    Head,
}

impl Higher {
    /// Build one feedback section from a list of residuals.
    pub fn section(&self, p: &Program, label: &str, residuals: &[Residual]) -> Section {
        let mut out = Vec::new();
        for r in residuals {
            let l = match r.via {
                Via::CalleeParam => {
                    let (slots, why) = self.callee_param_slots(p, r.mi, r.node);
                    self.landing(p, r.mi, r.node, &r.reason, slots, why)
                }
                Via::ConField => {
                    let (slots, why) = self.con_field_slots(p, r.mi, r.node);
                    self.landing(p, r.mi, r.node, &r.reason, slots, why)
                }
                Via::Imported => Landing {
                    module: p.m(r.mi).name.clone(),
                    node: r.node,
                    residual: r.reason.clone(),
                    boundary: None,
                    verdict: "NoBoundary".to_string(),
                    one_representation: false,
                    why: Some(
                        "the receiving parameter belongs to an imported function: it is not a \
                         slot of the closed world, and H0 does not make it one"
                            .into(),
                    ),
                },
                Via::Head => self.head_landing(p, r),
            };
            out.push(l);
        }
        Section::build(label, out)
    }
}

impl Higher {
    /// The verdict of an arbitrary function-valued expression, judged with
    /// the same rules as a boundary but with no slot to clone: what the
    /// feedback asks about a head the analysis does not register as a
    /// boundary (a `case`- or `let`-computed closure).
    pub fn expression_verdict(&self, p: &Program, mi: usize, node: ExprId) -> Verdict {
        let set = eval(p, &self.state, mi, node);
        if let ClosureSet::Top(t) = &set {
            return Verdict::Unresolved(t.clone());
        }
        let ps: Vec<&Producer> = set
            .keys()
            .iter()
            .filter_map(|k| self.producers.get(k))
            .collect();
        if ps.is_empty() {
            return Verdict::Unresolved(T_NO_PRODUCER.into());
        }
        if let Some(o) = ps.iter().find(|x| x.shape.is_opaque()) {
            let holder = match &o.shape {
                Shape::Opaque(why) => why.clone(),
                _ => unreachable!(),
            };
            return Verdict::Preserve(format!("{holder} ({} node {})", o.module, o.node));
        }
        if ps.len() == 1 {
            return Verdict::ExactClosure;
        }
        let mut classes: Vec<String> = ps.iter().map(|x| x.shape.class()).collect();
        classes.sort();
        classes.dedup();
        if classes.len() == 1 {
            Verdict::UniformRepresentation
        } else {
            Verdict::FiniteClosureSet(ps.len())
        }
    }

    /// A residual whose *head* is the closure: its boundary is the head's
    /// own parameter or return slot where the analysis registers one, and
    /// otherwise the expression it is bound to, judged directly.
    fn head_landing(&self, p: &Program, r: &Residual) -> Landing {
        let m = p.m(r.mi);
        let (head, _) = m.spine(r.node);
        let head = m.strip(head);
        let here = |v: Verdict, name: Option<String>, why: Option<String>| Landing {
            module: m.name.clone(),
            node: r.node,
            residual: r.reason.clone(),
            one_representation: v.one_representation(),
            verdict: v.label().to_string(),
            boundary: name,
            why,
        };
        let Some(b) = m.resolve(head) else {
            return Landing {
                module: m.name.clone(),
                node: r.node,
                residual: r.reason.clone(),
                boundary: None,
                verdict: "NoBoundary".into(),
                one_representation: false,
                why: Some("the head is an import, not a slot of the closed world".into()),
            };
        };
        let bi = m.binding(b);
        let slot = match bi.site {
            BindSite::Lam => Slot::Param {
                mi: r.mi,
                binder: b,
            },
            BindSite::Let | BindSite::Top => Slot::Return {
                mi: r.mi,
                binder: b,
            },
            _ => Slot::Param {
                mi: r.mi,
                binder: b,
            },
        };
        if let Some(bd) = self.boundaries.iter().find(|x| x.slot == slot) {
            return here(bd.verdict.clone(), Some(bd.name.clone()), None);
        }
        // Not a registered boundary. A let- or top-bound head is an
        // expression this analysis can still judge; a lambda-bound one is
        // a parameter whose *type* is not a FunTy (H1) — a type variable
        // instantiated out of sight — and there is nothing to judge.
        match bi.rhs {
            Some(rhs) => {
                let v = self.expression_verdict(p, r.mi, rhs);
                here(
                    v,
                    Some(format!("the expression bound to {}#{b}", m.binder(b).occ)),
                    None,
                )
            }
            None => Landing {
                module: m.name.clone(),
                node: r.node,
                residual: r.reason.clone(),
                boundary: None,
                verdict: "NoBoundary".into(),
                one_representation: false,
                why: Some(format!(
                    "the head {}#{b} is not function-typed (H1-FUNCTION-TYPED): its type is \
                     instantiated out of sight, so there is no slot to agree about",
                    m.binder(b).occ
                )),
            },
        }
    }
}
