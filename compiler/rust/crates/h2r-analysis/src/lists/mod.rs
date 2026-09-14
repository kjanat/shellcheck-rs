//! When, and how much, of a list's **spine** is demanded — by whom, how
//! often, and does anything alias its tail?
//!
//! This is M2.3c. It is deliberately *not* the question "is this
//! syntactically a Haskell list, and can I call it a `Vec`". `foldl'`
//! consumes every cell of a spine and is still a streaming consumer;
//! "the whole spine is eventually consumed" does not imply that the whole
//! spine ever exists at once. So nothing here starts from `[]`/`(:)` and
//! ends at a Rust type. It records **facts** about flows, each with a rule
//! id and the nodes it read, and derives an *advisory* recommendation from
//! them at the very end, clearly separated.
//!
//! Text (`[Char]`) is M2.3d's question and is decided nowhere below. Each
//! flow does record the list type and the element type **as GHC rendered
//! them on the binder** (corroboration-level evidence, never a verdict), so
//! that M2.3d can select the `[Char]` flows out of these facts instead of
//! re-deriving them.
//!
//! # The population: flows, not cells
//!
//! A flow starts at a **producer** ([`ProducerKind`]):
//!
//! * [`ProducerKind::ConsChain`] — a saturated `(:)`, identified through
//!   its [`DataConInfo`] and never by name. A cons whose tail argument is
//!   itself a cons or a nil construction is a **cell of the same flow**,
//!   not a flow of its own, so `1 : 2 : 3 : []` is one flow of four cells
//!   ([`L0_CONS`], [`L1_CHAIN`]).
//! * [`ProducerKind::Nil`] — a `[]`, likewise by `DataConInfo`, and
//!   likewise only when it is not already the tail of a cons in the
//!   population ([`L0_NIL`]).
//! * [`ProducerKind::ImportedCall`] — a saturated call to an imported
//!   function the [axiom table](axioms) says returns a list, with the
//!   entry saying *how* it is produced: incrementally (`map`), whole
//!   before the first cell (`reverse`, `sortBy`), or as a suffix of its
//!   own input (`drop`) ([`L0_IMPORTED`]).
//! * [`ProducerKind::LocalCall`] — a saturated call to a local function
//!   that returns a list producer, in the cases where the producer's own
//!   flow could not reach this call site (the return left the module)
//!   ([`L0_LOCAL`]). Everywhere else a local call *is* reached, as the
//!   walk's own `T6-RETURNED`/`T7-CALL-RESULT` pair, and is a location of
//!   the producer's flow rather than a new one — which is what keeps the
//!   population disjoint.
//!
//! # Following a spine
//!
//! The [generic aggregate walk](crate::flow) does the following, with
//! constructor-relative alternative selection: at `case xs of { [] -> …;
//! (y:ys) -> … }` a cons flow selects the `(:)` alternative and a nil flow
//! the `[]` one, and the other is unreachable for that flow. Two
//! list-specific rules are layered on it:
//!
//! * [`L2_TAIL_ALIAS`] — the `(:)` alternative's second binder is the
//!   **tail alias**. It is not a field that leaves the flow: it *is* the
//!   rest of this spine, and the walk continues at its occurrences. This
//!   is what makes a recursive consumer close a loop back onto the same
//!   `case` instead of stopping at the first cell.
//! * [`L7_CONSED_AS_TAIL`] — the value is consed onto as the *tail*
//!   argument of another cell (a `go`-loop accumulator, a cons built from
//!   a parameter). The spine survives into that cell's flow, so the two
//!   flows are linked and the successor's facts are propagated back in a
//!   fixpoint rather than the store being called an escape.
//!
//! The `(:)` alternative's *first* binder is an element, not spine, and is
//! what [`HeadDemand`] is measured on ([`L3_HEAD_BOUND`]).
//!
//! # Six facts, then an advisory recommendation
//!
//! [`SpineDemand`], [`HeadDemand`], [`Reuse`], [`Storage`], [`Recursion`]
//! and [`ShortCircuit`] are recorded **independently**, each with its own
//! rules. [`Recommendation`] is a function of them and is advisory: the
//! theorem is the facts.
//!
//! [`Recursion::RecursiveKnot`] is **M1's** definition and only M1's — a
//! non-function member of a recursive group that refers to itself through
//! the value ([`Class::RecursiveValue`]). A recursive *function* building a
//! finite list is [`Recursion::FiniteProducer`]. The M1 census is read, not
//! re-derived.
//!
//! # Evidence hierarchy
//!
//! Strongest first: 1 lexical binder identity, 2 structural shape, 3
//! def-use dataflow, 4 GHC type compatibility, **5 library axiom**
//! ([`axioms`] — new at this milestone, below dataflow because it is
//! asserted rather than derived), 6 textual type comparison
//! (corroboration), 7 names (diagnostics).

pub mod axioms;

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{BinderId, DataConInfo, Edge, Expr, ExprId, Lit, Module};
use serde::Serialize;

use crate::callee::{Family, split_stable_name};
use crate::fields::evaluated_within;
use crate::flow::{
    self, Client, Consumer, Ctx, Evidence, FlowUse, R_STORED_CON, R_TOO_LARGE, WhnfHow,
    is_list_cons, manifest_params, saturated_con,
};
use crate::laziness::{Census, Class};
use crate::scope::Scope;
use crate::shape::value_args;

use axioms::{ArgSpine, Axiom, HeadExposure, ListKind, Produces};

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------

/// **Producer.** A saturated application of the list cons, selected through
/// the head's [`DataConInfo`] and never by name, that is not itself the
/// tail argument of another cons in the population. Evidence: structural
/// saturation (2) over the constructor's `DataConInfo` (4).
pub const L0_CONS: &str = "L0-CONS";
/// **Producer.** An occurrence of the list nil, by `DataConInfo`, that is
/// not the tail argument of a cons in the population. Evidence: 2 over 4.
pub const L0_NIL: &str = "L0-NIL";
/// **Producer.** A saturated call to an imported function whose
/// [axiom](axioms) says the result is a list, together with how it is
/// produced. Evidence: library axiom (5) over structural saturation (2).
pub const L0_IMPORTED: &str = "L0-IMPORTED";
/// **Producer.** A saturated call to a local function one of whose return
/// positions is a list producer, where that producer's own flow does not
/// reach this call site — the return crossed the module boundary, so the
/// call is the start of a flow rather than a location of one. Evidence:
/// structural shape (2) over lexical identity of the callee (1).
pub const L0_LOCAL: &str = "L0-LOCAL";
/// A cons whose tail argument is another cons or a nil construction is a
/// **cell of the same flow**: one producer builds the whole chain.
/// Evidence: structural shape (2).
pub const L1_CHAIN: &str = "L1-CHAIN";
/// The `(:)` alternative's **second** binder is the tail of this same
/// spine, not a field leaving the flow: the walk continues at its
/// occurrences. Evidence: lexical binder identity (1) over the
/// constructor-relative alternative selection (2).
pub const L2_TAIL_ALIAS: &str = "L2-TAIL-ALIAS";
/// The `(:)` alternative's **first** binder is an element of the list:
/// what happens to it is [`HeadDemand`], never spine demand. Evidence:
/// lexical binder identity (1).
pub const L3_HEAD_BOUND: &str = "L3-HEAD-BOUND";
/// The tail alias is handed to a local callee whose corresponding
/// parameter is scrutinised by **this same `case`**, unconditionally from
/// the alternative's right-hand side: a recursive consumer that reaches
/// every cell. Evidence: structural shape (2) over lexical identity of the
/// callee and its parameter (1).
pub const L4_LOOP_WHOLE: &str = "L4-LOOP-WHOLE";
/// …the same loop, but the recursive call sits under a `case` inside the
/// alternative: the consumer may stop before the end. Evidence: 2 over 1.
pub const L5_LOOP_SHORTCIRCUIT: &str = "L5-LOOP-SHORTCIRCUIT";
/// A scrutiny whose tail alias has no occurrence: this cell is observed
/// and the rest of the spine is not reached through it. Evidence: lexical
/// binder identity (1).
pub const L6_TAIL_DROPPED: &str = "L6-TAIL-DROPPED";
/// The value is the **tail** argument of another cons cell: the spine is
/// not stored, it continues into that cell's flow, whose facts are
/// propagated back in the successor fixpoint. Evidence: structural shape
/// (2) over the constructor's `DataConInfo` (4).
pub const L7_CONSED_AS_TAIL: &str = "L7-CONSED-AS-TAIL";
/// The value is an argument of a saturated call to an imported head that
/// has an [axiom](axioms) entry: the entry says what is demanded of the
/// spine, of the elements, whether it short-circuits and whether the
/// result aliases the argument. Evidence: **library axiom (5)**.
pub const L8_AXIOM: &str = "L8-AXIOM";
/// The value is an argument of a saturated call to an imported head with
/// **no** axiom entry: nothing is claimed. Evidence: none — this is the
/// refusal.
pub const L9_NO_AXIOM: &str = "L9-NO-AXIOM";
/// The value is a field of a constructor that is not a list cell: the
/// spine outlives every consumer visible here. Evidence: structural shape
/// (2) over `DataConInfo` (4).
pub const L10_STORED: &str = "L10-STORED";
/// The value left what the walk can follow, with the walk's own
/// machine-readable reason. Evidence: structural shape (2).
pub const L11_ESCAPE: &str = "L11-ESCAPE";
/// Nothing reachable observes the spine at all. Evidence: def-use (3).
pub const L12_NEVER_OBSERVED: &str = "L12-NEVER-OBSERVED";
/// The producer is the right-hand side of a binding **M1** classifies as
/// [`Class::RecursiveValue`], and a cell refers back to the group: the
/// spine is a value knot. M1's definition is read, not re-derived.
/// Evidence: lexical binder identity (1).
pub const L13_RECURSIVE_KNOT: &str = "L13-RECURSIVE-KNOT";
/// A tail of this spine survives in a second place: an axiom whose result
/// aliases the argument, or a tail-derived value that is stored, returned
/// or handed out. Evidence: library axiom (5) or def-use (3).
pub const L14_SHARED_TAIL: &str = "L14-SHARED-TAIL";
/// The spine is entered by more than one consumer that does not reach it
/// through another consumer's tail alias. Evidence: def-use (3).
pub const L15_MULTIPASS: &str = "L15-MULTIPASS";
/// A consumer stands under a lambda the producer does not: the spine is
/// captured by a closure. Evidence: structural shape (2).
pub const L16_CAPTURED: &str = "L16-CAPTURED";
/// The value is a field of a construction in the **constructor-field
/// census'** population (M2.3b), and that holder is taken apart somewhere
/// visible: the reads of the holder's field are reads of this spine. The
/// mirror of M2.3b's `D8-NESTED`, which stops at a list cell exactly
/// because this milestone owns it. The storage fact stays
/// [`Storage::StoredIn`] either way — it is orthogonal to the demand.
/// Evidence: structural shape (2) over the holder's own def-use proof (3).
pub const L18_STORED_FOLLOWED: &str = "L18-STORED-FOLLOWED";
/// The construction holding this spine escapes, so the reads that reach it
/// through the holder are not all visible.
pub const R_OUTER_ESCAPES: &str = "the-construction-holding-it-escapes";

/// The recursive consumer of [`L4_LOOP_WHOLE`], but with the recursive call
/// in a lazy position — inside a constructor field, a lazy argument or a
/// lambda. Each cell is reached at most once, on demand, so the spine is
/// `Incremental` and **not** `Whole`. Evidence: structural shape (2) over
/// lexical identity (1).
pub const L17_LOOP_INCREMENTAL: &str = "L17-LOOP-INCREMENTAL";

/// A consumer **retains this spine and traverses it again from the
/// front**: `cycle`'s argument, `isInfixOf`'s needle. Distinct from
/// [`L15_MULTIPASS`] (two independent entries), from [`L14_SHARED_TAIL`]
/// (a tail survives elsewhere) and from a lockstep second walk. Evidence:
/// library axiom (5). New at M2.3g.
pub const L19_REPLAYED: &str = "L19-REPLAYED";
/// An element **reaches** a function or class method this analysis cannot
/// see into. Not a proof that it is forced — that is [`L3_HEAD_BOUND`] and
/// the axiom table's [`HeadDemand`] — but enough to require the element to
/// exist as a value. Evidence: library axiom (5), or lexical binder
/// identity (1) for a `(:)` alternative's head binder. New at M2.3g.
pub const L20_HEAD_EXPOSED: &str = "L20-HEAD-EXPOSED";

/// **Recommendation** (advisory): whole spine, entered more than once or
/// outliving its consumers, no shared tail, a finite producer.
pub const L_REC_VEC: &str = "L-REC-VEC";
/// **Recommendation** (advisory): one pass, nothing retained, a finite
/// producer — every spine-demanding consumer streams.
pub const L_REC_ITER: &str = "L-REC-ITERATOR";
/// **Recommendation** (advisory): a tail survives in two places, or the
/// spine is entered repeatedly with tails retained.
pub const L_REC_PERSIST: &str = "L-REC-PERSISTENT";
/// **Recommendation** (advisory): a value knot, or a short-circuiting
/// consumer in front of an unbounded producer.
pub const L_REC_LAZY: &str = "L-REC-LAZY";
/// **Recommendation**: any fact is `Unknown`, or the facts match no
/// recommendation. Carries the reason.
pub const L_REC_UNKNOWN: &str = "L-REC-UNKNOWN";

// Reasons, machine-readable.
pub const R_NO_AXIOM: &str = "no-axiom-for";
pub const R_AXIOM_ARG_NOT_COVERED: &str = "axiom-does-not-cover-this-argument-of";
pub const R_STORED: &str = "stored-in-a-constructor-field";
pub const R_UNKNOWN_SPINE: &str = "spine-demand-is-unknown";
pub const R_UNKNOWN_HEAD: &str = "head-demand-is-unknown";
pub const R_REUSE_ESCAPES: &str = "the-spine-escapes-what-the-walk-follows";
pub const R_STORED_NO_DEMAND: &str = "stored-with-no-visible-spine-demand";
/// …and the holder is a construction M2.3b's census knows the field reads
/// of, so the residue is *this* flow's, not a missing hop: M2.3f can pick
/// the holder's verdict up without re-analysing anything.
pub const R_STORED_NO_DEMAND_HOLDER_KNOWN: &str =
    "stored-with-no-visible-spine-demand-in-a-holder-the-field-census-knows";
/// …and the holder is not in M2.3b's population at all, or is never taken
/// apart in this module: whole-program work (M2.4).
pub const R_STORED_NO_DEMAND_HOLDER_OPAQUE: &str =
    "stored-with-no-visible-spine-demand-in-a-holder-this-module-never-takes-apart";
pub const R_NO_MATCH: &str = "the-facts-match-no-recommendation";
pub const R_UNKNOWN_EXPOSURE: &str = "element-exposure-is-unknown";
pub const R_NEVER_OBSERVED: &str = "no-reachable-consumer-observes-the-spine";

/// How many rounds the tail-derivation closure may take before it is a bug.
const CLOSURE_ROUNDS: usize = 64;

//------------------------------------------------------------------------------
// The facts
//------------------------------------------------------------------------------

/// How far into the spine a prefix consumer reaches.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum PrefixBound {
    /// A literal count read off the call: `take 1 xs`.
    Known(u64),
    /// The data decides.
    DataDependent,
}

/// Fact 1 of 6: how much of the spine the reachable consumers demand.
/// Ordered weakest to strongest, so joining is a maximum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum SpineDemand {
    /// No reachable consumer scrutinises it.
    None,
    /// A bounded or data-dependent prefix.
    Prefix(PrefixBound),
    /// Each cell at most once, on demand, driven by the consumer's own
    /// consumer: the spine need never exist all at once.
    Incremental,
    /// Every cell is reached.
    Whole,
    /// A consumer is outside what this module proves.
    Unknown,
}

impl SpineDemand {
    pub fn name(self) -> &'static str {
        match self {
            SpineDemand::None => "None",
            SpineDemand::Prefix(PrefixBound::Known(_)) => "Prefix(Known)",
            SpineDemand::Prefix(PrefixBound::DataDependent) => "Prefix(DataDependent)",
            SpineDemand::Incremental => "Incremental",
            SpineDemand::Whole => "Whole",
            SpineDemand::Unknown => "Unknown",
        }
    }
}

/// Fact 2 of 7: which *elements* are **provably forced**. `None` means no
/// reachable observation forces one — an element that is merely passed on,
/// stored, or handed to a predicate or a class method is **not** forced.
/// Since M2.3g, "handed to a callback" is [`HeadExposure`], a fact of its
/// own: an arbitrary predicate may ignore its argument, so `any p xs`
/// proves nothing about the elements of `xs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum HeadDemand {
    None,
    /// Only the element of the first cell reached.
    First,
    /// The elements of a prefix.
    Prefix,
    /// Every element of every cell reached.
    All,
    Unknown,
}

impl HeadDemand {
    pub fn name(self) -> &'static str {
        match self {
            HeadDemand::None => "None",
            HeadDemand::First => "First",
            HeadDemand::Prefix => "Prefix",
            HeadDemand::All => "All",
            HeadDemand::Unknown => "Unknown",
        }
    }
}

/// Fact 3 of 6: how many times the same spine is traversed, and whether a
/// tail of it survives in two places at once.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Reuse {
    SinglePass,
    /// `n` consumers enter the spine independently.
    MultiPass(usize),
    /// A tail survives in a second place: `drop`'s result aliases its
    /// input, `xs ++ ys` returns `ys` as its own tail, a `(y:ys)`
    /// alternative stores `ys` while `xs` is used elsewhere.
    SharedTail {
        at: Vec<ExprId>,
    },
    /// A consumer retains this spine and walks it **again from the
    /// front**: `cycle xs`, `isInfixOf needle`. The cells must all still
    /// be there for the second traversal, which is neither a second
    /// independent entry nor a surviving tail ([`L19_REPLAYED`], M2.3g).
    Replayed {
        at: Vec<ExprId>,
    },
    /// The spine left what the walk can follow.
    Escapes(&'static str),
}

impl Reuse {
    /// How much of the spine survives beside its consumers, weakest first.
    /// A flow that is consed onto another cell is a **suffix** of that
    /// longer spine, so whatever is true of the longer one's reuse is true
    /// of this one: the join across [`L7_CONSED_AS_TAIL`] is a maximum of
    /// this rank.
    fn rank(&self) -> u8 {
        match self {
            Reuse::SinglePass => 0,
            Reuse::MultiPass(_) => 1,
            Reuse::Escapes(_) => 2,
            Reuse::Replayed { .. } => 3,
            Reuse::SharedTail { .. } => 4,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Reuse::SinglePass => "SinglePass",
            Reuse::MultiPass(_) => "MultiPass",
            Reuse::Replayed { .. } => "Replayed",
            Reuse::SharedTail { .. } => "SharedTail",
            Reuse::Escapes(_) => "Escapes",
        }
    }
}

/// Fact 4 of 6: does the spine outlive its consumers?
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Storage {
    NotStored,
    /// A field of a constructor that is not a list cell.
    StoredIn(String),
    /// The value crosses a function return.
    Returned,
    /// A consumer stands under a lambda the producer does not.
    Captured,
}

impl Storage {
    pub fn name(&self) -> &'static str {
        match self {
            Storage::NotStored => "NotStored",
            Storage::StoredIn(_) => "StoredIn",
            Storage::Returned => "Returned",
            Storage::Captured => "Captured",
        }
    }

    fn rank(&self) -> u8 {
        match self {
            Storage::NotStored => 0,
            Storage::Captured => 1,
            Storage::Returned => 2,
            Storage::StoredIn(_) => 3,
        }
    }
}

/// Fact 5 of 6, and it is **M1's** verdict, not a second definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Recursion {
    /// Including a recursive *function* that builds a finite list.
    FiniteProducer,
    /// [`Class::RecursiveValue`]: a non-function member of a recursive
    /// group that refers to itself through the value.
    RecursiveKnot,
}

/// Fact 6 of 6: consumers that may stop before the end of the spine.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct ShortCircuit {
    pub yes: Vec<ExprId>,
}

impl ShortCircuit {
    pub fn no(&self) -> bool {
        self.yes.is_empty()
    }
}

/// The **advisory** derivation. The theorem is the six facts above.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Recommendation {
    VecCandidate,
    IteratorCandidate,
    PersistentCandidate,
    LazyCandidate,
    Unknown,
}

impl Recommendation {
    pub fn name(self) -> &'static str {
        match self {
            Recommendation::VecCandidate => "VecCandidate",
            Recommendation::IteratorCandidate => "IteratorCandidate",
            Recommendation::PersistentCandidate => "PersistentCandidate",
            Recommendation::LazyCandidate => "LazyCandidate",
            Recommendation::Unknown => "Unknown",
        }
    }
}

/// What a representation must still provide, **whatever** the advisory
/// says. A constraint is a positive fact that survives an `Unknown`
/// recommendation: since M2.3g a proven shared tail no longer *makes* a
/// flow `PersistentCandidate` when another fact is unknown — it is
/// recorded here instead, so that "we do not know enough" and "whatever we
/// choose must support tail sharing" are two different statements.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Constraints {
    /// A tail of this spine survives in a second place ([`L14_SHARED_TAIL`]).
    pub tail_sharing: bool,
    /// M1 calls the producer's binding a recursive value ([`L13_RECURSIVE_KNOT`]).
    pub recursive_laziness: bool,
    /// A consumer retains the spine and walks it again ([`L19_REPLAYED`]).
    pub replay: bool,
}

pub const C_TAIL_SHARING: &str = "RequiresTailSharing";
pub const C_RECURSIVE_LAZINESS: &str = "RequiresRecursiveLaziness";
pub const C_REPLAY: &str = "RequiresReplay";

impl Constraints {
    pub fn any(self) -> bool {
        self.tail_sharing || self.recursive_laziness || self.replay
    }

    pub fn names(self) -> Vec<&'static str> {
        let mut v = Vec::new();
        if self.tail_sharing {
            v.push(C_TAIL_SHARING);
        }
        if self.recursive_laziness {
            v.push(C_RECURSIVE_LAZINESS);
        }
        if self.replay {
            v.push(C_REPLAY);
        }
        v
    }
}

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ProducerKind {
    ConsChain,
    Nil,
    ImportedCall,
    LocalCall,
}

impl ProducerKind {
    pub fn name(self) -> &'static str {
        match self {
            ProducerKind::ConsChain => "ConsChain",
            ProducerKind::Nil => "Nil",
            ProducerKind::ImportedCall => "ImportedCall",
            ProducerKind::LocalCall => "LocalCall",
        }
    }

    pub fn rule(self) -> &'static str {
        match self {
            ProducerKind::ConsChain => L0_CONS,
            ProducerKind::Nil => L0_NIL,
            ProducerKind::ImportedCall => L0_IMPORTED,
            ProducerKind::LocalCall => L0_LOCAL,
        }
    }
}

/// What a `(:)` alternative does with the tail alias.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum TailFate {
    /// The alternative binds the tail and never uses it.
    Dropped,
    /// The tail is handed back to a callee whose parameter this same
    /// `case` scrutinises, and the call runs whenever the alternative does,
    /// with only evaluating edges in between: every cell is reached before
    /// the consumer returns ([`L4_LOOP_WHOLE`]).
    Loop { call: ExprId },
    /// …the same loop, but the recursive call sits in a **lazy** position —
    /// a constructor field, a lazy argument, under a lambda — so a cell is
    /// reached only when the consumer's own consumer asks for one
    /// ([`L17_LOOP_INCREMENTAL`]). This is the `map`-shaped loop, and
    /// calling it `Whole` would be wrong.
    LoopIncremental { call: ExprId },
    /// …the same, under a `case` inside the alternative: it may stop early
    /// ([`L5_LOOP_SHORTCIRCUIT`]).
    LoopConditional { call: ExprId },
    /// The tail goes somewhere the walk follows: its own consumers speak
    /// for it.
    Followed,
}

/// One consumer of a flow, as this milestone classifies it.
#[derive(Debug, Clone, Serialize)]
pub struct ListConsumer {
    pub kind: ConsumerKind,
    pub at: ExprId,
    pub rule: &'static str,
    /// The spine demand this one consumer puts on the flow.
    pub spine: SpineDemand,
    /// What this consumer **provably forces** of the elements it reaches.
    pub head: HeadDemand,
    /// What it merely hands them to ([`L20_HEAD_EXPOSED`], M2.3g).
    pub head_exposure: HeadExposure,
    /// Does this consumer touch each cell once, retaining nothing?
    pub streaming: bool,
    pub short_circuits: bool,
    /// Does the consumer's result alias this spine or a tail of it?
    pub aliases: bool,
    /// Does its result share cells with a list that is an **element** of
    /// this one? That is not spine sharing ([`axioms::Alias::ResultSharesElementOf`]).
    pub aliases_element: bool,
    /// Does it retain this spine and walk it again ([`L19_REPLAYED`])?
    pub replays: bool,
    /// Is this consumer reached through another consumer's tail alias? Then
    /// it is the same traversal, not a new one.
    pub tail_derived: bool,
    pub detail: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ConsumerKind {
    /// `case xs of (y:ys) -> …` ([`L2_TAIL_ALIAS`], [`L3_HEAD_BOUND`]).
    ConsAlt {
        head_bound: bool,
        head_forced: bool,
        tail: TailFate,
    },
    /// A `case` that observes the cell and binds no field of it.
    Whnf { how: &'static str },
    /// An imported call with a table entry ([`L8_AXIOM`]).
    Axiom { name: String, rule: &'static str },
    /// An imported call with none, or with an entry that does not declare
    /// this argument to be a list ([`L9_NO_AXIOM`]).
    NoAxiom { name: String, in_table: bool },
    /// Stored in a constructor that is not a list cell ([`L10_STORED`]).
    StoredIn { con: String },
    /// Consed on as the tail of another cell ([`L7_CONSED_AS_TAIL`]).
    ConsedAsTail { cell: ExprId },
    /// Handed to a local callee's parameter: an internal hop, not a
    /// consumer of its own.
    PassedLocal { callee: String },
    /// Left what the walk follows ([`L11_ESCAPE`]).
    Escape { why: &'static str },
}

/// One list flow: its producer, its cells, the six facts, and the advisory
/// recommendation derived from them.
#[derive(Debug, Clone, Serialize)]
pub struct ListFlow {
    pub module: String,
    /// The node the flow starts at.
    pub producer: ExprId,
    pub kind: ProducerKind,
    /// Cons cells one producer builds, outermost first. Empty for the
    /// non-constructor producers.
    pub cells: Vec<ExprId>,
    /// The chain ends in a `[]` this producer also builds.
    pub nil_terminated: bool,
    /// For [`ProducerKind::ImportedCall`]: how the axiom says the result
    /// is produced.
    pub produces: Option<Produces>,
    /// For the imported producer: the head's stable name (a diagnostic).
    pub producer_name: String,
    pub bound: Option<BinderId>,
    /// The binder's type as GHC rendered it. **Corroboration only**: no
    /// verdict below reads it. M2.3d selects `[Char]` on this.
    pub list_ty: Option<String>,
    /// The `(:)` alternative head binder's type, likewise.
    pub elem_ty: Option<String>,
    pub consumers: Vec<ListConsumer>,
    /// Escapes, as (reason, detail, node).
    pub escapes: Vec<(&'static str, String, ExprId)>,
    /// Flows this spine continues into, by producer node.
    pub successors: Vec<ExprId>,

    pub spine: SpineDemand,
    pub spine_rule: &'static str,
    pub head: HeadDemand,
    /// Fact 2b: what the elements are handed to (M2.3g).
    pub head_exposure: HeadExposure,
    pub reuse: Reuse,
    /// Every consumer that retains this spine and walks it again.
    pub replayed: Vec<ExprId>,
    pub storage: Storage,
    pub recursion: Recursion,
    pub short_circuit: ShortCircuit,
    /// Every spine-demanding consumer touches each cell once, retaining
    /// nothing.
    pub streaming: bool,
    pub traversals: usize,

    pub rec: Recommendation,
    pub rec_rule: &'static str,
    pub rec_reason: Option<String>,
    /// What any representation must support, whatever the advisory says.
    pub constraints: Constraints,

    pub returned: bool,
    pub locations: usize,
    pub over_budget: bool,
    pub unreachable_alts: usize,
    pub alias_occurrences_unreachable: usize,
    pub evidence: Vec<Evidence>,
}

impl ListFlow {
    /// Reasons that make a fact `Unknown`, as opposed to storage facts the
    /// analysis records and keeps walking past.
    pub fn unknown_reasons(&self) -> Vec<String> {
        let mut out = Vec::new();
        for c in &self.consumers {
            match &c.kind {
                ConsumerKind::NoAxiom { name, in_table } => out.push(if *in_table {
                    format!("{R_AXIOM_ARG_NOT_COVERED}({name})")
                } else {
                    format!("{R_NO_AXIOM}({name})")
                }),
                ConsumerKind::Escape { why } => out.push((*why).to_string()),
                _ => {}
            }
        }
        if self.over_budget {
            out.push(R_TOO_LARGE.to_string());
        }
        out
    }
}

//------------------------------------------------------------------------------
// The client
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
enum ListUse {
    Flow(FlowUse),
    ConsAlt {
        case: ExprId,
        head: BinderId,
        tail: BinderId,
        rhs: ExprId,
    },
    ConsedAsTail {
        cell: ExprId,
    },
    Axiom {
        call: ExprId,
        ax: &'static Axiom,
        idx: usize,
        n: usize,
    },
    NoAxiom {
        call: ExprId,
        head: ExprId,
        /// The table *has* an entry for this head, but it does not declare
        /// the argument this value landed in to be a list.
        in_table: bool,
    },
}

impl Consumer for ListUse {
    fn at(self) -> ExprId {
        match self {
            ListUse::Flow(u) => u.at(),
            ListUse::ConsAlt { case, .. } => case,
            ListUse::ConsedAsTail { cell } => cell,
            ListUse::Axiom { call, .. } | ListUse::NoAxiom { call, .. } => call,
        }
    }
}

impl From<FlowUse> for ListUse {
    fn from(u: FlowUse) -> ListUse {
        ListUse::Flow(u)
    }
}

struct ListClient<'a> {
    /// M2.3b's published map from (construction, field) to where that field
    /// is read: what makes [`L18_STORED_FOLLOWED`] possible.
    reads: &'a FieldReads,
}

/// `(construction, field index)` -> (where that field is read, did the
/// holder's own flow escape?).
pub type FieldReads = HashMap<(ExprId, usize), (Vec<ExprId>, bool)>;

impl Client for ListClient<'_> {
    type Use = ListUse;

    /// The `(:)` alternative. Its second binder is the rest of this spine
    /// ([`L2_TAIL_ALIAS`]), so the walk continues there; its first binder
    /// is an element ([`L3_HEAD_BOUND`]) and is left to [`HeadDemand`].
    fn on_alt(
        &mut self,
        w: &mut flow::Walk<ListUse>,
        cx: &Ctx<'_, '_>,
        case: ExprId,
        _v: ExprId,
        alt: &h2r_core_ir::Alt,
    ) -> bool {
        if alt.binders.len() != 2 {
            return false;
        }
        let head = alt.binders[0];
        let tail = alt.binders[1];
        w.use_(ListUse::ConsAlt {
            case,
            head,
            tail,
            rhs: alt.rhs,
        });
        w.evidence.push(Evidence {
            rule: L2_TAIL_ALIAS,
            nodes: vec![case],
            binder: Some(tail),
            note: format!(
                "{} is the rest of this spine ({} occurrence(s)); {} is an element",
                cx.m.binder(tail).occ,
                cx.m.occurrences(tail).len(),
                cx.m.binder(head).occ
            ),
        });
        w.evidence.push(Evidence {
            rule: L3_HEAD_BOUND,
            nodes: vec![case],
            binder: Some(head),
            note: format!("{} occurrence(s)", cx.m.occurrences(head).len()),
        });
        for occ in cx.m.occurrences(tail) {
            w.push(*occ, 0);
        }
        true
    }

    /// The tail slot of another cons cell is not storage: the spine
    /// continues into that cell's flow ([`L7_CONSED_AS_TAIL`]).
    fn on_stored(
        &mut self,
        w: &mut flow::Walk<ListUse>,
        _cx: &Ctx<'_, '_>,
        root: ExprId,
        idx: usize,
        dc: &DataConInfo,
        occ: &str,
    ) -> Option<&'static str> {
        if is_list_cons(&dc.name) && idx == 1 {
            w.use_(ListUse::ConsedAsTail { cell: root });
            w.evidence.push(Evidence {
                rule: L7_CONSED_AS_TAIL,
                nodes: vec![root],
                binder: None,
                note: "the spine continues as the tail of another cell".into(),
            });
            return None;
        }
        // The holder is in M2.3b's population and is taken apart somewhere
        // visible: follow the reads of the field ([`L18_STORED_FOLLOWED`]).
        // The value is still stored — that fact is recorded by the caller —
        // but what is demanded of the spine is no longer invisible.
        if let Some((seeds, escaped)) = self.reads.get(&(root, idx)) {
            w.evidence.push(Evidence {
                rule: L18_STORED_FOLLOWED,
                nodes: vec![root],
                binder: None,
                note: format!("field {idx} of {occ}: {} read(s) follow", seeds.len()),
            });
            for seed in seeds {
                w.push(*seed, 0);
            }
            if *escaped {
                w.escape_at(root, false, R_OUTER_ESCAPES, occ.to_string());
            }
        }
        Some(R_STORED_CON)
    }

    /// An imported call: the [axiom table](axioms) speaks, or nothing does.
    fn on_call_arg(
        &mut self,
        w: &mut flow::Walk<ListUse>,
        cx: &Ctx<'_, '_>,
        root: ExprId,
        idx: usize,
        head: ExprId,
        _occ: &str,
        owed: u32,
    ) -> bool {
        if owed > 0 {
            return false;
        }
        let m = cx.m;
        let Expr::Var {
            name, is_global, ..
        } = m.expr(head)
        else {
            return false;
        };
        // An axiom is never applied to anything this module binds.
        if !*is_global || m.binding_of(head).is_some() || split_stable_name(name).is_none() {
            return false;
        }
        let (_, args) = m.spine(root);
        let n = value_args(cx.scope, &args).len();
        if let Some(ax) = axioms::axiom(name)
            && n >= ax.min_args
        {
            if ax.spine_of(idx, n).is_some() {
                w.use_(ListUse::Axiom {
                    call: root,
                    ax,
                    idx,
                    n,
                });
                w.evidence.push(Evidence {
                    rule: L8_AXIOM,
                    nodes: vec![root],
                    binder: None,
                    note: format!("{} argument {idx} of {n}: {}", ax.rule, ax.note),
                });
                return true;
            }
            w.use_(ListUse::NoAxiom {
                call: root,
                head,
                in_table: true,
            });
            w.evidence.push(Evidence {
                rule: L9_NO_AXIOM,
                nodes: vec![root],
                binder: None,
                note: format!("{R_AXIOM_ARG_NOT_COVERED}({name}) at argument {idx} of {n}"),
            });
            return true;
        }
        w.use_(ListUse::NoAxiom {
            call: root,
            head,
            in_table: false,
        });
        w.evidence.push(Evidence {
            rule: L9_NO_AXIOM,
            nodes: vec![root],
            binder: None,
            note: format!("{R_NO_AXIOM}({name})"),
        });
        true
    }
}

//------------------------------------------------------------------------------
// The analysis
//------------------------------------------------------------------------------

pub struct Lists<'m> {
    pub module: &'m Module,
    pub flows: Vec<ListFlow>,
    scope: Scope<'m>,
    /// Producer node -> flow index.
    index: HashMap<ExprId, usize>,
    /// Any cell of a chain -> flow index, so a census site that names an
    /// inner cell still lands on the flow that owns it.
    cell_index: HashMap<ExprId, usize>,
    top_pairs: Vec<BinderId>,
    top_rec: Vec<bool>,
    m1_recursive: HashSet<ExprId>,
    pub successor_rounds: usize,
    /// Imported heads the flows were handed to: stable name -> (count, has
    /// an axiom, a representative node).
    pub heads_seen: BTreeMap<String, (usize, bool, ExprId)>,
}

impl<'m> Lists<'m> {
    pub fn of_module(m: &'m Module, census: &Census, reads: &FieldReads) -> Lists<'m> {
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
        let mut l = Lists {
            module: m,
            flows: Vec::new(),
            scope: Scope::new(m),
            index: HashMap::new(),
            cell_index: HashMap::new(),
            top_pairs: m
                .top
                .iter()
                .flat_map(|b| b.pairs.iter())
                .map(|p| p.binder)
                .collect(),
            top_rec,
            m1_recursive,
            successor_rounds: 0,
            heads_seen: BTreeMap::new(),
        };
        l.find_producers();
        l.resolve_flows(reads);
        l
    }

    pub fn flow_at(&self, node: ExprId) -> Option<&ListFlow> {
        self.index
            .get(&node)
            .or_else(|| self.cell_index.get(&node))
            .map(|i| &self.flows[*i])
    }

    //--------------------------------------------------------------------------
    // The population
    //--------------------------------------------------------------------------

    fn find_producers(&mut self) {
        let m = self.module;
        // Every cons and nil construction in the module, by spine root.
        let mut cons: BTreeMap<ExprId, Vec<ExprId>> = BTreeMap::new();
        let mut nils: HashSet<ExprId> = HashSet::new();
        for id in 0..m.exprs.len() as ExprId {
            if let Some((dc, _, vargs)) = saturated_con(&self.scope, id)
                && is_list_cons(&dc.name)
                && vargs.len() == 2
            {
                cons.insert(id, vargs);
                continue;
            }
            if let Expr::Var { .. } = m.expr(id)
                && let Some(dc) = self.scope.head_sig(id).and_then(|s| s.data_con)
                && is_list_nil(&dc.name)
            {
                let root = m.spine_root(id);
                let (head, args) = m.spine(root);
                if head == id && value_args(&self.scope, &args).is_empty() {
                    nils.insert(root);
                }
            }
        }
        // A construction that is the tail argument of a cons is a *cell* of
        // that cons' chain, not a producer of its own ([`L1_CHAIN`]).
        let mut nested: HashSet<ExprId> = HashSet::new();
        for vargs in cons.values() {
            let t = m.strip(vargs[1]);
            if cons.contains_key(&t) || nils.contains(&t) {
                nested.insert(t);
            }
        }
        let cons_roots: Vec<ExprId> = cons
            .keys()
            .copied()
            .filter(|c| !nested.contains(c))
            .collect();
        for root in cons_roots {
            let mut cells = vec![root];
            let mut nil_terminated = false;
            let mut cur = root;
            while let Some(vargs) = cons.get(&cur) {
                let t = m.strip(vargs[1]);
                if cons.contains_key(&t) {
                    cells.push(t);
                    cur = t;
                } else {
                    if nils.contains(&t) {
                        nil_terminated = true;
                    }
                    break;
                }
            }
            let note = format!("{} cell(s) built by one producer", cells.len());
            self.add_flow(
                root,
                ProducerKind::ConsChain,
                cells,
                nil_terminated,
                None,
                String::new(),
                note,
            );
        }
        let mut lone_nils: Vec<ExprId> = nils
            .iter()
            .copied()
            .filter(|n| !nested.contains(n))
            .collect();
        lone_nils.sort_unstable();
        for root in lone_nils {
            self.add_flow(
                root,
                ProducerKind::Nil,
                Vec::new(),
                true,
                None,
                String::new(),
                "the empty spine".into(),
            );
        }
        // Imported calls the axiom table says return a list.
        for id in 0..m.exprs.len() as ExprId {
            if m.spine_root(id) != id || !matches!(m.expr(id), Expr::App { .. }) {
                continue;
            }
            let (head, args) = m.spine(id);
            let Expr::Var {
                name, is_global, ..
            } = m.expr(head)
            else {
                continue;
            };
            if !*is_global || m.binding_of(head).is_some() {
                continue;
            }
            let Some(ax) = axioms::axiom(name) else {
                continue;
            };
            // **M2.3g.** Only a call whose *outer return type* is a list
            // starts a list flow. `span` returns a pair, `mapM` returns
            // `m [b]`: their argument-demand and aliasing facts still speak
            // for the consumer side, but the call node is not a list and
            // making it one was a population bug.
            if !ax.produces.is_direct_list() || value_args(&self.scope, &args).len() < ax.min_args {
                continue;
            }
            let note = format!("{}: {}", ax.rule, ax.note);
            self.add_flow(
                id,
                ProducerKind::ImportedCall,
                Vec::new(),
                false,
                Some(ax.produces),
                name.clone(),
                note,
            );
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn add_flow(
        &mut self,
        producer: ExprId,
        kind: ProducerKind,
        cells: Vec<ExprId>,
        nil_terminated: bool,
        produces: Option<Produces>,
        producer_name: String,
        note: String,
    ) {
        let i = self.flows.len();
        self.index.insert(producer, i);
        for c in &cells {
            self.cell_index.insert(*c, i);
        }
        self.cell_index.entry(producer).or_insert(i);
        self.flows.push(ListFlow {
            module: self.module.name.clone(),
            producer,
            kind,
            cells,
            nil_terminated,
            produces,
            producer_name,
            bound: None,
            list_ty: None,
            elem_ty: None,
            consumers: Vec::new(),
            escapes: Vec::new(),
            successors: Vec::new(),
            spine: SpineDemand::None,
            spine_rule: L12_NEVER_OBSERVED,
            head: HeadDemand::None,
            head_exposure: HeadExposure::NotExposed,
            reuse: Reuse::SinglePass,
            replayed: Vec::new(),
            storage: Storage::NotStored,
            recursion: Recursion::FiniteProducer,
            short_circuit: ShortCircuit::default(),
            streaming: true,
            traversals: 0,
            rec: Recommendation::Unknown,
            rec_rule: L_REC_UNKNOWN,
            rec_reason: None,
            constraints: Constraints::default(),
            returned: false,
            locations: 0,
            over_budget: false,
            unreachable_alts: 0,
            alias_occurrences_unreachable: 0,
            evidence: vec![Evidence {
                rule: kind.rule(),
                nodes: vec![producer],
                binder: None,
                note,
            }],
        });
    }

    /// A saturated call to a local function that returns a list producer
    /// which the producer's own flow never reached ([`L0_LOCAL`]). Run
    /// after the first round of walks, so "never reached" is a fact rather
    /// than an assumption.
    fn find_local_call_producers(&mut self, visited: &HashSet<ExprId>) {
        let m = self.module;
        let mut found: Vec<ExprId> = Vec::new();
        for id in 0..m.exprs.len() as ExprId {
            if m.spine_root(id) != id || !matches!(m.expr(id), Expr::App { .. }) {
                continue;
            }
            if visited.contains(&id) || self.index.contains_key(&id) {
                continue;
            }
            let (head, args) = m.spine(id);
            let Some(bi) = m.binding_of(head) else {
                continue;
            };
            let Some(rhs) = bi.rhs else { continue };
            let params = manifest_params(m, rhs);
            if params.is_empty() || value_args(&self.scope, &args).len() != params.len() {
                continue;
            }
            if !self.returns_a_list(rhs, params.len()) {
                continue;
            }
            found.push(id);
        }
        for id in found {
            let (head, _) = m.spine(id);
            let occ = match m.expr(head) {
                Expr::Var { occ, .. } => occ.clone(),
                _ => String::new(),
            };
            let note = format!("a call to {occ} whose returns build a list this flow cannot reach");
            self.add_flow(
                id,
                ProducerKind::LocalCall,
                Vec::new(),
                false,
                None,
                occ,
                note,
            );
        }
    }

    /// Does the manifest lambda chain at `rhs` return a list producer in
    /// one of its return positions? Iterative, never recursive.
    fn returns_a_list(&self, rhs: ExprId, n_params: usize) -> bool {
        let m = self.module;
        let mut cur = m.strip(rhs);
        let mut left = n_params;
        while left > 0 {
            let Expr::Lam { binder, body } = m.expr(cur) else {
                break;
            };
            if m.binder(*binder).kind != h2r_core_ir::BinderKind::Tyvar {
                left -= 1;
            }
            cur = m.strip(*body);
        }
        let mut work = vec![cur];
        let mut seen = HashSet::new();
        while let Some(v) = work.pop() {
            if !seen.insert(v) {
                continue;
            }
            match m.expr(v) {
                Expr::Let { body, .. } => work.push(m.strip(*body)),
                Expr::Case { alts, .. } => work.extend(alts.iter().map(|a| m.strip(a.rhs))),
                _ => {
                    if self.index.contains_key(&v) || self.cell_index.contains_key(&v) {
                        return true;
                    }
                }
            }
        }
        false
    }

    //--------------------------------------------------------------------------
    // Running the flows
    //--------------------------------------------------------------------------

    fn resolve_flows(&mut self, reads: &FieldReads) {
        let mut visited: HashSet<ExprId> = HashSet::new();
        for i in 0..self.flows.len() {
            self.run_flow(i, &mut visited, reads);
        }
        let first_round = self.flows.len();
        self.find_local_call_producers(&visited);
        for i in first_round..self.flows.len() {
            self.run_flow(i, &mut visited, reads);
        }
        // The successor fixpoint: a spine consed onto another cell inherits
        // that cell's flow's facts. Monotone — every fact only ever joins
        // upwards and the short-circuit set only ever grows out of a finite
        // universe of nodes — so a worklist over the reverse edges settles.
        let rounds = self.propagate_successors();
        self.successor_rounds = rounds;
        for i in 0..self.flows.len() {
            let holder_known = self.flows[i].consumers.iter().any(|c| {
                matches!(c.kind, ConsumerKind::StoredIn { .. })
                    && reads.keys().any(|(root, _)| *root == c.at)
            });
            let (rec, rule, reason, constraints) = recommend(&self.flows[i], holder_known);
            self.flows[i].rec = rec;
            self.flows[i].rec_rule = rule;
            self.flows[i].rec_reason = reason;
            self.flows[i].constraints = constraints;
        }
    }

    fn run_flow(&mut self, i: usize, visited: &mut HashSet<ExprId>, reads: &FieldReads) {
        let producer = self.flows[i].producer;
        let con = saturated_con(&self.scope, producer)
            .map(|(dc, _, _)| dc)
            .or_else(|| {
                // A nil producer: the head *is* the constructor.
                let (head, _) = self.module.spine(producer);
                self.scope
                    .head_sig(head)
                    .and_then(|s| s.data_con)
                    .filter(|dc| is_list_nil(&dc.name))
            });
        let cx = Ctx {
            m: self.module,
            scope: &self.scope,
            top_pairs: &self.top_pairs,
            start: producer,
            arity: con.map(|dc| dc.rep_arity).unwrap_or(0),
            con,
        };
        let mut client = ListClient { reads };
        let w = flow::walk(&cx, &mut client);
        visited.extend(w.visited());
        self.record(i, &w);
    }

    /// Turn one walk into consumers, the six facts, and the evidence.
    fn record(&mut self, i: usize, w: &flow::Walk<ListUse>) {
        let m = self.module;
        let producer = self.flows[i].producer;
        let tail_derived = self.tail_derived(w);

        // Types, for M2.3d — corroboration only.
        let list_ty = w.bound.map(|b| m.binder(b).ty.clone());
        let elem_ty = w.consumers.iter().find_map(|u| match u {
            ListUse::ConsAlt { head, .. } => Some(m.binder(*head).ty.clone()),
            _ => None,
        });

        let mut consumers: Vec<ListConsumer> = Vec::new();
        let mut short_circuit = ShortCircuit::default();
        let mut shared_tail: Vec<ExprId> = Vec::new();
        let mut replayed: Vec<ExprId> = Vec::new();
        let mut successors: Vec<ExprId> = Vec::new();
        let mut storage = Storage::NotStored;
        let mut evidence: Vec<Evidence> = Vec::new();

        for u in &w.consumers {
            let c = match u {
                ListUse::ConsAlt {
                    case,
                    head,
                    tail,
                    rhs,
                } => {
                    let fate = self.tail_fate(*case, *tail, *rhs);
                    let head_bound = !m.occurrences(*head).is_empty();
                    let head_forced = head_bound
                        && m.occurrences(*head)
                            .iter()
                            .any(|o| evaluated_within(&self.scope, *o, *rhs))
                        || m.binder(*head)
                            .demand
                            .as_ref()
                            .is_some_and(|d| d.strict && !d.absent);
                    let (spine, rule) = match fate {
                        TailFate::Dropped => {
                            (SpineDemand::Prefix(PrefixBound::Known(1)), L6_TAIL_DROPPED)
                        }
                        TailFate::Loop { .. } => (SpineDemand::Whole, L4_LOOP_WHOLE),
                        TailFate::LoopIncremental { .. } => {
                            (SpineDemand::Incremental, L17_LOOP_INCREMENTAL)
                        }
                        TailFate::LoopConditional { .. } => (
                            SpineDemand::Prefix(PrefixBound::DataDependent),
                            L5_LOOP_SHORTCIRCUIT,
                        ),
                        TailFate::Followed => {
                            (SpineDemand::Prefix(PrefixBound::Known(1)), L2_TAIL_ALIAS)
                        }
                    };
                    if let TailFate::LoopConditional { call } = fate {
                        short_circuit.yes.push(call);
                    }
                    let head = if !head_forced {
                        HeadDemand::None
                    } else {
                        match fate {
                            TailFate::Loop { .. } | TailFate::LoopIncremental { .. } => {
                                HeadDemand::All
                            }
                            TailFate::LoopConditional { .. } => HeadDemand::Prefix,
                            _ => HeadDemand::First,
                        }
                    };
                    // A loop that only hands the tail to the recursive call
                    // retains nothing.
                    // A loop retains nothing when the tail alias goes
                    // nowhere but the recursive call.
                    let streaming = match fate {
                        TailFate::Loop { call }
                        | TailFate::LoopIncremental { call }
                        | TailFate::LoopConditional { call } => m
                            .occurrences(*tail)
                            .iter()
                            .all(|o| arg_spine_root(m, *o) == Some(call)),
                        _ => true,
                    };
                    ListConsumer {
                        kind: ConsumerKind::ConsAlt {
                            head_bound,
                            head_forced,
                            tail: fate,
                        },
                        at: *case,
                        rule,
                        spine,
                        head,
                        head_exposure: if head_bound {
                            HeadExposure::BoundAndUsed
                        } else {
                            HeadExposure::NotExposed
                        },
                        streaming,
                        short_circuits: matches!(fate, TailFate::LoopConditional { .. }),
                        aliases: false,
                        aliases_element: false,
                        replays: false,
                        tail_derived: false,
                        detail: String::new(),
                    }
                }
                ListUse::Flow(FlowUse::Whnf { case, how }) => ListConsumer {
                    kind: ConsumerKind::Whnf { how: how.name() },
                    at: *case,
                    rule: flow::T15_WHNF_ALT,
                    spine: SpineDemand::Prefix(PrefixBound::Known(1)),
                    head: HeadDemand::None,
                    head_exposure: HeadExposure::NotExposed,
                    streaming: true,
                    short_circuits: false,
                    aliases: false,
                    aliases_element: false,
                    replays: false,
                    tail_derived: false,
                    detail: how.name().to_string(),
                },
                ListUse::Flow(FlowUse::Forced { case }) => ListConsumer {
                    kind: ConsumerKind::Whnf {
                        how: WhnfHow::Forced.name(),
                    },
                    at: *case,
                    rule: flow::T14_FORCED,
                    spine: SpineDemand::Prefix(PrefixBound::Known(1)),
                    head: HeadDemand::None,
                    head_exposure: HeadExposure::NotExposed,
                    streaming: true,
                    short_circuits: false,
                    aliases: false,
                    aliases_element: false,
                    replays: false,
                    tail_derived: false,
                    detail: String::new(),
                },
                ListUse::Flow(FlowUse::Scrutinised { case, .. }) => ListConsumer {
                    kind: ConsumerKind::Whnf {
                        how: "alternative-binds-no-tail",
                    },
                    at: *case,
                    rule: flow::T2_SCRUTINISED,
                    spine: SpineDemand::Prefix(PrefixBound::Known(1)),
                    head: HeadDemand::None,
                    head_exposure: HeadExposure::NotExposed,
                    streaming: true,
                    short_circuits: false,
                    aliases: false,
                    aliases_element: false,
                    replays: false,
                    tail_derived: false,
                    detail: String::new(),
                },
                ListUse::Axiom { call, ax, idx, n } => {
                    if ax.short_circuit {
                        short_circuit.yes.push(*call);
                    }
                    // **M2.3g.** A tail surviving beside the call is one
                    // axis; whether the call node is itself a list is the
                    // other. `span`'s second component is a suffix of this
                    // spine even though `span` returns a pair, so the
                    // shared tail is recorded here all the same.
                    let aliases = ax.aliases_spine(*idx, *n);
                    if aliases {
                        shared_tail.push(*call);
                    }
                    let replays = ax.replays_arg(*idx, *n);
                    if replays {
                        replayed.push(*call);
                        evidence.push(Evidence {
                            rule: L19_REPLAYED,
                            nodes: vec![*call],
                            binder: None,
                            note: format!("{}: the argument is retained and walked again", ax.rule),
                        });
                    }
                    let spine = self.axiom_spine(*call, ax, *idx, *n);
                    let reached = spine != SpineDemand::None;
                    if reached && ax.exposure != HeadExposure::NotExposed {
                        evidence.push(Evidence {
                            rule: L20_HEAD_EXPOSED,
                            nodes: vec![*call],
                            binder: None,
                            note: format!("{}: {}", ax.rule, ax.exposure.name()),
                        });
                    }
                    ListConsumer {
                        kind: ConsumerKind::Axiom {
                            name: ax.name.to_string(),
                            rule: ax.rule,
                        },
                        at: *call,
                        rule: L8_AXIOM,
                        spine,
                        head: if reached { ax.head } else { HeadDemand::None },
                        head_exposure: if reached {
                            ax.exposure
                        } else {
                            HeadExposure::NotExposed
                        },
                        streaming: ax.streaming,
                        short_circuits: ax.short_circuit,
                        aliases,
                        aliases_element: ax.aliases_element(*idx, *n),
                        replays,
                        tail_derived: false,
                        detail: ax.note.to_string(),
                    }
                }
                ListUse::NoAxiom {
                    call,
                    head,
                    in_table,
                } => {
                    let name = match m.expr(*head) {
                        Expr::Var { name, .. } => name.clone(),
                        _ => String::new(),
                    };
                    ListConsumer {
                        kind: ConsumerKind::NoAxiom {
                            name: name.clone(),
                            in_table: *in_table,
                        },
                        at: *call,
                        rule: L9_NO_AXIOM,
                        spine: SpineDemand::Unknown,
                        head: HeadDemand::Unknown,
                        head_exposure: HeadExposure::Unknown,
                        streaming: false,
                        short_circuits: false,
                        aliases: false,
                        aliases_element: false,
                        replays: false,
                        tail_derived: false,
                        detail: if *in_table {
                            format!("{R_AXIOM_ARG_NOT_COVERED}({name})")
                        } else {
                            format!("{R_NO_AXIOM}({name})")
                        },
                    }
                }
                ListUse::ConsedAsTail { cell } => {
                    successors.push(*cell);
                    ListConsumer {
                        kind: ConsumerKind::ConsedAsTail { cell: *cell },
                        at: *cell,
                        rule: L7_CONSED_AS_TAIL,
                        spine: SpineDemand::None,
                        head: HeadDemand::None,
                        head_exposure: HeadExposure::NotExposed,
                        streaming: true,
                        short_circuits: false,
                        aliases: false,
                        aliases_element: false,
                        replays: false,
                        tail_derived: false,
                        detail: String::new(),
                    }
                }
                ListUse::Flow(FlowUse::StoredIn { con }) => {
                    let occ = head_name(m, *con);
                    if storage.rank() < 3 {
                        storage = Storage::StoredIn(occ.clone());
                    }
                    ListConsumer {
                        kind: ConsumerKind::StoredIn { con: occ },
                        at: *con,
                        rule: L10_STORED,
                        spine: SpineDemand::None,
                        head: HeadDemand::None,
                        head_exposure: HeadExposure::NotExposed,
                        streaming: true,
                        short_circuits: false,
                        aliases: false,
                        aliases_element: false,
                        replays: false,
                        tail_derived: false,
                        detail: R_STORED.to_string(),
                    }
                }
                ListUse::Flow(FlowUse::PassedTo { call, callee, .. }) => ListConsumer {
                    kind: ConsumerKind::PassedLocal {
                        callee: m.binder(*callee).occ.clone(),
                    },
                    at: *call,
                    rule: flow::T5_PASSED_LOCAL,
                    spine: SpineDemand::None,
                    head: HeadDemand::None,
                    head_exposure: HeadExposure::NotExposed,
                    streaming: true,
                    short_circuits: false,
                    aliases: false,
                    aliases_element: false,
                    replays: false,
                    tail_derived: false,
                    detail: String::new(),
                },
                ListUse::Flow(FlowUse::Returned { .. }) => continue,
                ListUse::Flow(FlowUse::PassedToUnknown { call, why }) => ListConsumer {
                    kind: ConsumerKind::Escape { why },
                    at: *call,
                    rule: L11_ESCAPE,
                    spine: SpineDemand::Unknown,
                    head: HeadDemand::Unknown,
                    head_exposure: HeadExposure::Unknown,
                    streaming: false,
                    short_circuits: false,
                    aliases: false,
                    aliases_element: false,
                    replays: false,
                    tail_derived: false,
                    detail: (*why).to_string(),
                },
                ListUse::Flow(FlowUse::Escapes { at, why }) => ListConsumer {
                    kind: ConsumerKind::Escape { why },
                    at: *at,
                    rule: L11_ESCAPE,
                    spine: SpineDemand::Unknown,
                    head: HeadDemand::Unknown,
                    head_exposure: HeadExposure::Unknown,
                    streaming: false,
                    short_circuits: false,
                    aliases: false,
                    aliases_element: false,
                    replays: false,
                    tail_derived: false,
                    detail: (*why).to_string(),
                },
            };
            consumers.push(c);
        }
        // A consumer reached through another consumer's tail alias is the
        // same traversal, not a new entry into the spine.
        for c in consumers.iter_mut() {
            c.tail_derived = tail_derived.contains(&c.at) || self.under_any(&tail_derived, c.at);
        }
        // A tail that is stored, returned or handed out survives beside the
        // rest of the spine ([`L14_SHARED_TAIL`]).
        for c in &consumers {
            if c.tail_derived
                && matches!(
                    c.kind,
                    ConsumerKind::StoredIn { .. } | ConsumerKind::Escape { .. }
                )
            {
                shared_tail.push(c.at);
            }
        }

        // Fact 1, 2 and 2b: join over the consumers. Forcing and exposure
        // are joined **separately** (M2.3g): a flow every one of whose
        // consumers only hands elements to a predicate has
        // `HeadDemand::None` and a non-trivial `HeadExposure`.
        let mut spine = SpineDemand::None;
        let mut spine_rule = L12_NEVER_OBSERVED;
        let mut head = HeadDemand::None;
        let mut head_exposure = HeadExposure::NotExposed;
        for c in &consumers {
            if c.spine > spine {
                spine = c.spine;
                spine_rule = c.rule;
            }
            head = head.max(c.head);
            head_exposure = head_exposure.max(c.head_exposure);
        }
        if w.over_budget {
            spine = SpineDemand::Unknown;
            spine_rule = L11_ESCAPE;
            head = HeadDemand::Unknown;
            head_exposure = HeadExposure::Unknown;
        }

        // Fact 4: storage.
        if storage.rank() < Storage::Returned.rank()
            && (w.returned
                || w.escapes
                    .iter()
                    .any(|(_, why, _, _)| *why == flow::R_EXPORTED_RETURN))
        {
            storage = Storage::Returned;
        }
        // Capture is a consumer *inside* a lambda the producer is outside
        // of, reached because the binder is in scope there. A consumer
        // reached by handing the value to a callee or by leaving a function
        // is inside that callee's lambdas by construction and is not a
        // capture, so a flow that crossed either is never called captured.
        let crossed_a_frame = w.returned
            || w.consumers
                .iter()
                .any(|u| matches!(u, ListUse::Flow(FlowUse::PassedTo { .. })));
        if storage == Storage::NotStored
            && !crossed_a_frame
            && consumers
                .iter()
                .any(|c| c.spine > SpineDemand::None && crosses_lambda_from(m, producer, c.at))
        {
            storage = Storage::Captured;
            evidence.push(Evidence {
                rule: L16_CAPTURED,
                nodes: vec![producer],
                binder: None,
                note: "a consumer stands under a lambda the producer does not".into(),
            });
        }

        // Fact 3: traversals and sharing.
        // Entries into the spine: a consumer reached through another's tail
        // alias continues that traversal rather than starting one. A loop
        // whose only scrutiny is its own recursive call's is still one
        // traversal, not none.
        let mut traversals = consumers
            .iter()
            .filter(|c| !c.tail_derived && c.spine > SpineDemand::None)
            .map(|c| c.at)
            .collect::<HashSet<_>>()
            .len();
        if traversals == 0 && consumers.iter().any(|c| c.spine > SpineDemand::None) {
            traversals = 1;
        }
        let escape_reason = consumers.iter().find_map(|c| match &c.kind {
            ConsumerKind::Escape { why } => Some(*why),
            ConsumerKind::NoAxiom { .. } => Some(R_NO_AXIOM),
            _ => None,
        });
        shared_tail.sort_unstable();
        shared_tail.dedup();
        replayed.sort_unstable();
        replayed.dedup();
        let reuse = if !shared_tail.is_empty() {
            evidence.push(Evidence {
                rule: L14_SHARED_TAIL,
                nodes: shared_tail.clone(),
                binder: None,
                note: format!(
                    "{} place(s) a tail of this spine survives in",
                    shared_tail.len()
                ),
            });
            Reuse::SharedTail { at: shared_tail }
        } else if !replayed.is_empty() {
            Reuse::Replayed {
                at: replayed.clone(),
            }
        } else if let Some(why) = escape_reason {
            Reuse::Escapes(why)
        } else if traversals > 1 {
            evidence.push(Evidence {
                rule: L15_MULTIPASS,
                nodes: consumers
                    .iter()
                    .filter(|c| !c.tail_derived)
                    .map(|c| c.at)
                    .collect(),
                binder: None,
                note: format!("{traversals} independent entries into the spine"),
            });
            Reuse::MultiPass(traversals)
        } else {
            Reuse::SinglePass
        };

        let streaming = consumers
            .iter()
            .filter(|c| c.spine > SpineDemand::None)
            .all(|c| c.streaming);

        // Fact 5: M1's, read not re-derived.
        let recursion = if self.is_knot(i) {
            evidence.push(Evidence {
                rule: L13_RECURSIVE_KNOT,
                nodes: vec![producer],
                binder: w.bound,
                note: "M1 calls this binding a recursive value; a cell refers back".into(),
            });
            Recursion::RecursiveKnot
        } else {
            Recursion::FiniteProducer
        };

        short_circuit.yes.sort_unstable();
        short_circuit.yes.dedup();

        for c in &consumers {
            if let ConsumerKind::NoAxiom { name, in_table } = &c.kind {
                let e = self
                    .heads_seen
                    .entry(name.clone())
                    .or_insert((0, *in_table, c.at));
                e.0 += 1;
                e.1 |= *in_table;
            }
            if let ConsumerKind::Axiom { name, .. } = &c.kind {
                let e = self
                    .heads_seen
                    .entry(name.clone())
                    .or_insert((0, true, c.at));
                e.0 += 1;
                e.1 = true;
            }
        }

        let f = &mut self.flows[i];
        f.bound = w.bound;
        f.list_ty = list_ty;
        f.elem_ty = elem_ty;
        f.consumers = consumers;
        f.escapes = w
            .escapes
            .iter()
            .map(|(_, why, detail, at)| (*why, detail.clone(), *at))
            .collect();
        f.successors = successors;
        f.spine = spine;
        f.spine_rule = spine_rule;
        f.head = head;
        f.head_exposure = head_exposure;
        f.reuse = reuse;
        f.replayed = replayed;
        f.storage = storage;
        f.recursion = recursion;
        f.short_circuit = short_circuit;
        f.streaming = streaming;
        f.traversals = traversals;
        f.returned = w.returned;
        f.locations = w.locations;
        f.over_budget = w.over_budget;
        f.unreachable_alts = w.unreachable_alts;
        f.alias_occurrences_unreachable = w.alias_occurrences_unreachable;
        f.evidence.truncate(1);
        f.evidence.extend(w.evidence.iter().cloned());
        f.evidence.append(&mut evidence);
    }

    /// Locations this flow reached through a `(:)` alternative's tail
    /// alias, grown through known-local calls until it settles.
    fn tail_derived(&self, w: &flow::Walk<ListUse>) -> HashSet<ExprId> {
        let m = self.module;
        let mut out: HashSet<ExprId> = HashSet::new();
        for u in &w.consumers {
            if let ListUse::ConsAlt { tail, .. } = u {
                out.extend(m.occurrences(*tail).iter().copied());
            }
        }
        // A callee's parameter is only tail-derived if **every** call of it
        // this flow reaches hands it a tail-derived argument. A parameter
        // that also receives the whole spine from another call site is an
        // independent entry into it, whatever the other call site does —
        // the same union-over-call-sites rule the rest of the walk uses.
        // Marking it tail-derived would *under*-count traversals, which is
        // the unsafe direction for a representation decision.
        let mut by_param: BTreeMap<(BinderId, u32), Vec<ExprId>> = BTreeMap::new();
        for u in &w.consumers {
            let ListUse::Flow(FlowUse::PassedTo {
                call,
                callee,
                param,
            }) = u
            else {
                continue;
            };
            let (_, args) = m.spine(*call);
            let vargs = value_args(&self.scope, &args);
            if let Some(arg) = vargs.get(*param as usize) {
                by_param.entry((*callee, *param)).or_default().push(*arg);
            }
        }
        let mut rounds = 0;
        loop {
            let before = out.len();
            for ((callee, param), argv) in &by_param {
                if !argv.iter().all(|a| out.contains(a)) {
                    continue;
                }
                let Some(rhs) = m.binding(*callee).rhs else {
                    continue;
                };
                let params = manifest_params(m, rhs);
                if let Some(p) = params.get(*param as usize) {
                    out.extend(m.occurrences(*p).iter().copied());
                }
            }
            rounds += 1;
            if out.len() == before || rounds > CLOSURE_ROUNDS {
                break;
            }
        }
        out
    }

    /// Is `at` inside a spine whose root is a tail-derived location? A
    /// `case` on the tail alias is rooted at the alias occurrence itself.
    fn under_any(&self, set: &HashSet<ExprId>, at: ExprId) -> bool {
        let m = self.module;
        if let Expr::Case { scrut, .. } = m.expr(at) {
            return set.contains(&m.strip(*scrut));
        }
        let (_, args) = m.spine(at);
        value_args(&self.scope, &args)
            .iter()
            .any(|a| set.contains(&m.strip(*a)))
    }

    /// What the `(:)` alternative at `case` does with its tail alias. The
    /// loop shape is recognised structurally: the alias is an argument of a
    /// saturated call to a local callee whose corresponding parameter is
    /// the scrutinee of **this very `case`**. Where the call stands then
    /// decides how much of the spine that loop reaches.
    fn tail_fate(&self, case: ExprId, tail: BinderId, rhs: ExprId) -> TailFate {
        let m = self.module;
        let occs = m.occurrences(tail);
        if occs.is_empty() {
            return TailFate::Dropped;
        }
        let Expr::Case { scrut, .. } = m.expr(case) else {
            return TailFate::Followed;
        };
        let scrut = m.strip(*scrut);
        for occ in occs {
            let Some(root) = arg_spine_root(m, *occ) else {
                continue;
            };
            let (head, args) = m.spine(root);
            let vargs = value_args(&self.scope, &args);
            let Some(idx) = vargs.iter().position(|a| m.strip(*a) == *occ) else {
                continue;
            };
            let Some(bi) = m.binding_of(head) else {
                continue;
            };
            let Some(callee_rhs) = bi.rhs else { continue };
            let params = manifest_params(m, callee_rhs);
            if vargs.len() != params.len() {
                continue;
            }
            let Some(p) = params.get(idx) else { continue };
            // Does the callee's parameter reach this very `case` again?
            if !m.occurrences(*p).contains(&scrut) {
                continue;
            }
            return match self.reach(root, rhs) {
                Reach::Conditional => TailFate::LoopConditional { call: root },
                Reach::Strict => TailFate::Loop { call: root },
                Reach::Lazy => TailFate::LoopIncremental { call: root },
            };
        }
        TailFate::Followed
    }

    /// How `at` is reached from `rhs`: behind a `case` (so it may never
    /// run), through evaluating edges only (so it runs whenever `rhs`
    /// does), or through a lazy position (so it runs only when something
    /// pulls on it).
    fn reach(&self, at: ExprId, rhs: ExprId) -> Reach {
        let m = self.module;
        let mut cur = at;
        let mut lazy = false;
        loop {
            if cur == rhs {
                return if lazy { Reach::Lazy } else { Reach::Strict };
            }
            let Some(p) = m.parent[cur as usize] else {
                return Reach::Lazy;
            };
            match m.edge[cur as usize] {
                Edge::CaseAlt { .. } => return Reach::Conditional,
                Edge::LamBody => lazy = true,
                _ => {
                    if !crate::fields::evaluates(&self.scope, cur) {
                        lazy = true;
                    }
                }
            }
            cur = p;
        }
    }

    /// The spine demand an axiom entry puts on one argument, resolving a
    /// [`ArgSpine::PrefixFromArg`] bound against a literal where the call
    /// site has one.
    fn axiom_spine(&self, call: ExprId, ax: &Axiom, idx: usize, n: usize) -> SpineDemand {
        match ax.spine_of(idx, n) {
            Some(ArgSpine::Whole) => SpineDemand::Whole,
            Some(ArgSpine::Incremental) => SpineDemand::Incremental,
            Some(ArgSpine::PrefixDataDependent) => SpineDemand::Prefix(PrefixBound::DataDependent),
            Some(ArgSpine::PrefixFromArg(e)) => {
                let bound = axioms::end_index(e, n)
                    .and_then(|k| {
                        let (_, args) = self.module.spine(call);
                        value_args(&self.scope, &args).get(k).copied()
                    })
                    .and_then(|a| literal_count(self.module, &self.scope, a));
                SpineDemand::Prefix(match bound {
                    Some(k) => PrefixBound::Known(k),
                    None => PrefixBound::DataDependent,
                })
            }
            Some(ArgSpine::NoDemand) | None => SpineDemand::None,
        }
    }

    /// Does the producer's binding sit in a recursive group M1 calls a
    /// recursive *value*, with a cell referring back into it?
    fn is_knot(&self, i: usize) -> bool {
        let m = self.module;
        let f = &self.flows[i];
        let Some((group, is_rec, rhs)) = self.enclosing_group(f.producer) else {
            return false;
        };
        if !is_rec {
            return false;
        }
        if !(self.m1_recursive.contains(&rhs) || matches!(m.edge[rhs as usize], Edge::Top { .. })) {
            return false;
        }
        let roots: Vec<ExprId> = if f.cells.is_empty() {
            vec![f.producer]
        } else {
            f.cells.clone()
        };
        roots.iter().any(|c| {
            m.preorder(*c)
                .any(|n| m.resolve(n).is_some_and(|b| group.contains(&b)))
        })
    }

    /// The binder group whose right-hand side this node is.
    fn enclosing_group(&self, at: ExprId) -> Option<(HashSet<BinderId>, bool, ExprId)> {
        let m = self.module;
        let mut cur = at;
        loop {
            match m.edge[cur as usize] {
                Edge::Cast | Edge::Tick => cur = m.parent[cur as usize]?,
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
                    let rec = self.top_rec.get(pair as usize).copied().unwrap_or(false);
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

    /// The successor fixpoint. A spine that becomes the tail of another
    /// cell inherits that cell's flow's demand, element demand, storage and
    /// short-circuiting. Driven by an explicit worklist over the reverse
    /// edges — never a recursion — and monotone, so it terminates; the
    /// number of updates it took is returned and asserted on by the
    /// accounting.
    fn propagate_successors(&mut self) -> usize {
        let n = self.flows.len();
        let succ: Vec<Vec<usize>> = self
            .flows
            .iter()
            .enumerate()
            .map(|(i, f)| {
                let mut v: Vec<usize> = f
                    .successors
                    .iter()
                    .filter_map(|c| self.cell_index.get(c).copied())
                    .filter(|j| *j != i)
                    .collect();
                v.sort_unstable();
                v.dedup();
                v
            })
            .collect();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, js) in succ.iter().enumerate() {
            for j in js {
                preds[*j].push(i);
            }
        }
        // Entries into the spine the flow has on its own, before anything
        // is inherited: a flow that is both consed onto a longer spine
        // *and* has a spine consumer of its own has its cells walked by
        // both, so it is entered at least twice ([`L15_MULTIPASS`]).
        let own: Vec<usize> = self.flows.iter().map(|f| f.traversals).collect();
        let mut queued = vec![true; n];
        let mut work: Vec<usize> = (0..n).rev().collect();
        let mut updates = 0usize;
        while let Some(i) = work.pop() {
            queued[i] = false;
            updates += 1;
            let mut changed = false;
            for j in &succ[i] {
                let (spine, head, exposure, storage, reuse, replayed, sc, streaming) = {
                    let s = &self.flows[*j];
                    (
                        s.spine,
                        s.head,
                        s.head_exposure,
                        s.storage.clone(),
                        s.reuse.clone(),
                        s.replayed.clone(),
                        s.short_circuit.yes.clone(),
                        s.streaming,
                    )
                };
                let f = &mut self.flows[i];
                if spine > f.spine {
                    f.spine = spine;
                    f.spine_rule = L7_CONSED_AS_TAIL;
                    changed = true;
                }
                if head > f.head {
                    f.head = head;
                    changed = true;
                }
                if exposure > f.head_exposure {
                    f.head_exposure = exposure;
                    changed = true;
                }
                for x in replayed {
                    if !f.replayed.contains(&x) {
                        f.replayed.push(x);
                        f.replayed.sort_unstable();
                        changed = true;
                    }
                }
                if storage.rank() > f.storage.rank() {
                    f.storage = storage;
                    changed = true;
                }
                // `L7` again: this spine is a suffix of the successor's, so
                // a tail the successor shares, an entry the successor is
                // walked by, and a head the successor escapes to are all
                // reached through this spine too.
                if reuse.rank() > f.reuse.rank() {
                    if let Reuse::MultiPass(k) = reuse {
                        f.traversals = f.traversals.max(k);
                    }
                    f.reuse = reuse;
                    changed = true;
                }
                if spine > SpineDemand::None && own[i] > 0 && f.traversals <= own[i] {
                    f.traversals = own[i] + 1;
                    if f.reuse.rank() <= Reuse::MultiPass(0).rank() {
                        f.reuse = Reuse::MultiPass(f.traversals);
                    }
                    changed = true;
                }
                for x in sc {
                    if !f.short_circuit.yes.contains(&x) {
                        f.short_circuit.yes.push(x);
                        changed = true;
                    }
                }
                f.short_circuit.yes.sort_unstable();
                if f.streaming && !streaming {
                    f.streaming = false;
                    changed = true;
                }
            }
            if changed {
                for p in &preds[i] {
                    if !queued[*p] {
                        queued[*p] = true;
                        work.push(*p);
                    }
                }
            }
        }
        updates
    }
}

//------------------------------------------------------------------------------
// Shared predicates
//------------------------------------------------------------------------------

/// Is this stable name the list nil constructor?
pub fn is_list_nil(name: &str) -> bool {
    matches!(
        split_stable_name(name),
        Some(("ghc-prim", "GHC.Types", "[]"))
    )
}

/// GHC's occurrence name of the head of the spine rooted at `root`.
fn head_name(m: &Module, root: ExprId) -> String {
    let (head, _) = m.spine(root);
    match m.expr(head) {
        Expr::Var { occ, .. } => occ.clone(),
        _ => String::new(),
    }
}

/// A literal count in an argument, through `I#`/`W#` boxes: what turns
/// `take 1 xs` into a `Known(1)` prefix rather than a data-dependent one.
fn literal_count(m: &Module, s: &Scope, arg: ExprId) -> Option<u64> {
    let inner = m.strip(arg);
    if let Expr::Lit(l) = m.expr(inner) {
        return lit_u64(l);
    }
    // A boxed literal: `I# 1#`.
    let (head, args) = m.spine(inner);
    s.head_sig(head)?.data_con?;
    let vargs = value_args(s, &args);
    if vargs.len() != 1 {
        return None;
    }
    match m.expr(m.strip(vargs[0])) {
        Expr::Lit(l) => lit_u64(l),
        _ => None,
    }
}

fn lit_u64(l: &Lit) -> Option<u64> {
    let t = l.pretty.trim().trim_end_matches('#');
    t.parse::<u64>().ok()
}

/// How far from `rhs` an expression stands: see [`Lists::reach`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reach {
    /// Behind a `case`: it may never run.
    Conditional,
    /// Only evaluating edges in between: it runs whenever `rhs` does.
    Strict,
    /// In a lazy position: it runs only when something pulls on it.
    Lazy,
}

/// The spine root of the application `occ` is an **argument** of. GHC's own
/// `spine_root` climbs `fun` edges only, so an argument is its own root;
/// this is the one extra hop that turns an occurrence into the call it
/// takes part in. `None` when the occurrence is not an argument at all.
fn arg_spine_root(m: &Module, occ: ExprId) -> Option<ExprId> {
    let mut cur = occ;
    loop {
        let p = m.parent[cur as usize]?;
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => cur = p,
            Edge::AppArg => return Some(m.spine_root(p)),
            _ => return None,
        }
    }
}

/// Does `at` stand under a lambda that does not also enclose `producer`?
fn crosses_lambda_from(m: &Module, producer: ExprId, at: ExprId) -> bool {
    let mut chain: HashSet<ExprId> = HashSet::from([producer]);
    chain.extend(m.ancestors(producer));
    let mut cur = at;
    loop {
        if chain.contains(&cur) {
            return false;
        }
        let Some(p) = m.parent[cur as usize] else {
            return false;
        };
        if m.edge[cur as usize] == Edge::LamBody {
            return true;
        }
        cur = p;
    }
}

//------------------------------------------------------------------------------
// The advisory recommendation
//------------------------------------------------------------------------------

/// Derive the advisory recommendation from the facts, and the constraints
/// that hold whatever it says. **Nothing below is a theorem**: the facts
/// are.
///
/// # The M2.3g ordering
///
/// Before M2.3g a proven `SharedTail` and M1's `RecursiveKnot` were
/// returned *before* the `Unknown` checks, so a flow with one unresolved
/// consumer could still be advised `PersistentCandidate` — "one known
/// property points this way" reading as "this is sufficient". It is not:
/// an advisory is a claim that the representation is adequate **given
/// everything we know**, and a flow with an unknown consumer does not
/// support such a claim. So every `Unknown` fact now wins, and the
/// positive facts are recorded as [`Constraints`] instead, which no
/// `Unknown` erases.
fn recommend(
    f: &ListFlow,
    holder_known: bool,
) -> (Recommendation, &'static str, Option<String>, Constraints) {
    let constraints = Constraints {
        tail_sharing: matches!(f.reuse, Reuse::SharedTail { .. }),
        recursive_laziness: f.recursion == Recursion::RecursiveKnot,
        replay: !f.replayed.is_empty() || matches!(f.reuse, Reuse::Replayed { .. }),
    };
    let unknown = |why: String| {
        (
            Recommendation::Unknown,
            L_REC_UNKNOWN,
            Some(why),
            constraints,
        )
    };
    // ---- every unknown fact first (M2.3g) ----------------------------
    if f.spine == SpineDemand::Unknown {
        return unknown(
            f.unknown_reasons()
                .first()
                .cloned()
                .unwrap_or_else(|| R_UNKNOWN_SPINE.to_string()),
        );
    }
    if f.head == HeadDemand::Unknown {
        return unknown(R_UNKNOWN_HEAD.to_string());
    }
    if f.head_exposure == HeadExposure::Unknown {
        return unknown(R_UNKNOWN_EXPOSURE.to_string());
    }
    if let Reuse::Escapes(why) = f.reuse {
        return unknown(format!("{R_REUSE_ESCAPES}: {why}"));
    }
    // ---- then the positive facts, in the order they decide ------------
    let advise =
        |r: Recommendation, rule: &'static str, why: Option<String>| (r, rule, why, constraints);
    if f.recursion == Recursion::RecursiveKnot {
        return advise(
            Recommendation::LazyCandidate,
            L_REC_LAZY,
            Some("M1 calls this binding a recursive value".into()),
        );
    }
    // A tail that provably survives in two places decides the
    // representation: two owners see the same cells.
    if matches!(f.reuse, Reuse::SharedTail { .. }) {
        return advise(Recommendation::PersistentCandidate, L_REC_PERSIST, None);
    }
    // A spine that is walked again from the front must still be there for
    // the second walk, which is exactly what a one-pass iterator is not.
    if matches!(f.reuse, Reuse::Replayed { .. }) {
        return advise(
            Recommendation::PersistentCandidate,
            L_REC_PERSIST,
            Some("a consumer retains this spine and walks it again".into()),
        );
    }
    // A short-circuiting consumer in front of an unbounded producer.
    if !f.short_circuit.no()
        && matches!(f.produces, Some(Produces::DirectList(ListKind::Unbounded)))
    {
        return advise(
            Recommendation::LazyCandidate,
            L_REC_LAZY,
            Some("a short-circuiting consumer of an unbounded producer".into()),
        );
    }
    if matches!(f.reuse, Reuse::MultiPass(_)) && f.storage != Storage::NotStored {
        return advise(Recommendation::PersistentCandidate, L_REC_PERSIST, None);
    }
    if f.spine == SpineDemand::Whole
        && (matches!(f.reuse, Reuse::MultiPass(_)) || f.storage != Storage::NotStored)
    {
        return advise(Recommendation::VecCandidate, L_REC_VEC, None);
    }
    if f.spine > SpineDemand::None
        && f.reuse == Reuse::SinglePass
        && f.storage == Storage::NotStored
        && f.streaming
    {
        return advise(Recommendation::IteratorCandidate, L_REC_ITER, None);
    }
    if f.spine == SpineDemand::None {
        return unknown(if f.storage == Storage::NotStored {
            R_NEVER_OBSERVED.to_string()
        } else if holder_known {
            R_STORED_NO_DEMAND_HOLDER_KNOWN.to_string()
        } else {
            R_STORED_NO_DEMAND_HOLDER_OPAQUE.to_string()
        });
    }
    unknown(format!(
        "{R_NO_MATCH} ({}, {}, {}, {})",
        f.spine.name(),
        f.reuse.name(),
        f.storage.name(),
        if f.streaming {
            "streaming"
        } else {
            "retaining"
        }
    ))
}

//------------------------------------------------------------------------------
// Accounting
//------------------------------------------------------------------------------

/// One of the M2 census' list-cons argument sites — the 1,310 `fields.rs`
/// deferred to this milestone — and the flow it belongs to.
#[derive(Debug, Clone, Serialize)]
pub struct SiteMap {
    pub module: String,
    pub app: ExprId,
    pub arg: ExprId,
    /// Index into [`ListCensus::flows`].
    pub flow: Option<usize>,
    /// Which field of the cell: 0 the element, 1 the tail.
    pub field: Option<u32>,
    pub kind: Option<ProducerKind>,
    pub spine: Option<SpineDemand>,
    pub rec: Option<Recommendation>,
    pub reason: Option<&'static str>,
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct ListAccounting {
    pub flows: usize,
    pub by_kind: Vec<(ProducerKind, usize)>,
    pub by_rec: Vec<(Recommendation, usize)>,
    pub by_spine: Vec<(&'static str, usize)>,
    pub by_head: Vec<(&'static str, usize)>,
    /// Fact 2b: what the elements are handed to (M2.3g).
    pub by_exposure: Vec<(&'static str, usize)>,
    pub by_reuse: Vec<(&'static str, usize)>,
    pub by_storage: Vec<(&'static str, usize)>,
    pub by_recursion: Vec<(&'static str, usize)>,
    pub short_circuit_yes: usize,
    pub short_circuit_no: usize,
    pub cells: usize,
    pub streaming: usize,
    pub over_budget: usize,
    pub unreachable_alts: usize,
    pub alias_occurrences_unreachable: usize,
    pub sites: Vec<SiteMap>,
    pub sites_mapped: usize,
    pub sites_unmapped: usize,
    pub consumers_by_kind: Vec<(&'static str, usize)>,
    pub rules: Vec<(&'static str, usize)>,
    /// Imported heads a flow reached: name -> (calls, has an axiom, node).
    pub heads: Vec<(String, usize, bool, ExprId)>,
    pub heads_with_axiom: usize,
    pub heads_without_axiom: usize,
    /// Flows carrying each constraint, whatever the advisory says (M2.3g).
    pub constraints: Vec<(&'static str, usize)>,
    /// Flows whose recommendation is `Unknown` **and** that carry at least
    /// one constraint: the population the M2.3g ordering created.
    pub unknown_with_constraints: usize,
}

impl ListAccounting {
    pub fn count(&self, r: Recommendation) -> usize {
        self.by_rec
            .iter()
            .find(|(x, _)| *x == r)
            .map(|(_, n)| *n)
            .unwrap_or(0)
    }

    /// Every flow lands in exactly one of every table, and every one of the
    /// census' list-cons sites is mapped onto a cell or carries a reason.
    pub fn check(&self) {
        for (what, total) in [
            (
                "producer kind",
                self.by_kind.iter().map(|(_, n)| n).sum::<usize>(),
            ),
            ("recommendation", self.by_rec.iter().map(|(_, n)| n).sum()),
            ("spine demand", self.by_spine.iter().map(|(_, n)| n).sum()),
            ("head demand", self.by_head.iter().map(|(_, n)| n).sum()),
            (
                "head exposure",
                self.by_exposure.iter().map(|(_, n)| n).sum(),
            ),
            ("reuse", self.by_reuse.iter().map(|(_, n)| n).sum()),
            ("storage", self.by_storage.iter().map(|(_, n)| n).sum()),
            ("recursion", self.by_recursion.iter().map(|(_, n)| n).sum()),
        ] {
            assert_eq!(
                total, self.flows,
                "every flow must land in exactly one {what} bucket"
            );
        }
        assert_eq!(
            self.short_circuit_yes + self.short_circuit_no,
            self.flows,
            "every flow either has a short-circuiting consumer or has not"
        );
        assert_eq!(
            self.sites_mapped + self.sites_unmapped,
            self.sites.len(),
            "every census list-cons site is mapped or carries a reason"
        );
        for s in &self.sites {
            assert!(
                s.flow.is_some() ^ s.reason.is_some(),
                "site {} in {} must map onto exactly one flow or carry a reason",
                s.app,
                s.module
            );
        }
        assert_eq!(
            self.heads_with_axiom + self.heads_without_axiom,
            self.heads.len(),
            "every imported head seen either has an axiom or has not"
        );
    }
}

/// The whole population over a set of modules.
pub struct ListCensus<'m> {
    pub per_module: Vec<Lists<'m>>,
    pub flows: Vec<ListFlow>,
    pub accounting: ListAccounting,
}

impl<'m> ListCensus<'m> {
    pub fn of_modules(modules: &'m [&'m Module], census: &Census) -> ListCensus<'m> {
        let per_module: Vec<Lists<'m>> = modules
            .iter()
            .map(|m| {
                // M2.3b's field census, read for one thing: where each
                // constructor field is read, so a list stored in one can be
                // followed through the holder ([`L18_STORED_FOLLOWED`]).
                let reads = crate::fields::Fields::of_module(m, census).field_reads();
                Lists::of_module(m, census, &reads)
            })
            .collect();
        let mut flows: Vec<ListFlow> = Vec::new();
        // (module, any cell node) -> flow index.
        let mut index: HashMap<(&str, ExprId), usize> = HashMap::new();
        for t in &per_module {
            let base = flows.len();
            for (i, f) in t.flows.iter().enumerate() {
                for c in &f.cells {
                    index.insert((t.module.name.as_str(), *c), base + i);
                }
                index
                    .entry((t.module.name.as_str(), f.producer))
                    .or_insert(base + i);
                flows.push(f.clone());
            }
        }

        let mut acct = ListAccounting::default();
        let mut by_kind: BTreeMap<ProducerKind, usize> = BTreeMap::new();
        let mut by_rec: BTreeMap<Recommendation, usize> = BTreeMap::new();
        let mut by_spine: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_head: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_exposure: BTreeMap<&'static str, usize> = BTreeMap::new();
        // Printed in full, zeros included: a constraint the table can
        // express and this program never exercises is a fact about the
        // program, and hiding it would make the table look smaller than it
        // is.
        let mut constraints: BTreeMap<&'static str, usize> =
            [C_TAIL_SHARING, C_RECURSIVE_LAZINESS, C_REPLAY]
                .into_iter()
                .map(|c| (c, 0))
                .collect();
        let mut by_reuse: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_storage: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_recursion: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut consumers: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut rules: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut heads: BTreeMap<String, (usize, bool, ExprId)> = BTreeMap::new();
        for t in &per_module {
            for (name, (n, has, node)) in &t.heads_seen {
                let e = heads.entry(name.clone()).or_insert((0, *has, *node));
                e.0 += n;
                e.1 |= *has;
            }
        }
        for f in &flows {
            acct.flows += 1;
            *by_kind.entry(f.kind).or_default() += 1;
            *by_rec.entry(f.rec).or_default() += 1;
            *by_spine.entry(f.spine.name()).or_default() += 1;
            *by_head.entry(f.head.name()).or_default() += 1;
            *by_exposure.entry(f.head_exposure.name()).or_default() += 1;
            for c in f.constraints.names() {
                *constraints.entry(c).or_default() += 1;
            }
            if f.rec == Recommendation::Unknown && f.constraints.any() {
                acct.unknown_with_constraints += 1;
            }
            *by_reuse.entry(f.reuse.name()).or_default() += 1;
            *by_storage.entry(f.storage.name()).or_default() += 1;
            *by_recursion
                .entry(match f.recursion {
                    Recursion::FiniteProducer => "FiniteProducer",
                    Recursion::RecursiveKnot => "RecursiveKnot",
                })
                .or_default() += 1;
            if f.short_circuit.no() {
                acct.short_circuit_no += 1;
            } else {
                acct.short_circuit_yes += 1;
            }
            acct.cells += f.cells.len();
            if f.streaming {
                acct.streaming += 1;
            }
            if f.over_budget {
                acct.over_budget += 1;
            }
            acct.unreachable_alts += f.unreachable_alts;
            acct.alias_occurrences_unreachable += f.alias_occurrences_unreachable;
            for c in &f.consumers {
                *consumers.entry(consumer_name(&c.kind)).or_default() += 1;
                *rules.entry(c.rule).or_default() += 1;
            }
            for e in &f.evidence {
                *rules.entry(e.rule).or_default() += 1;
            }
            *rules.entry(f.rec_rule).or_default() += 1;
        }
        acct.by_kind = by_kind.into_iter().collect();
        acct.by_rec = by_rec.into_iter().collect();
        acct.by_spine = by_spine.into_iter().collect();
        acct.by_head = by_head.into_iter().collect();
        acct.by_exposure = by_exposure.into_iter().collect();
        acct.constraints = constraints.into_iter().collect();
        acct.by_reuse = by_reuse.into_iter().collect();
        acct.by_storage = by_storage.into_iter().collect();
        acct.by_recursion = by_recursion.into_iter().collect();
        acct.consumers_by_kind = consumers.into_iter().collect();
        acct.rules = rules.into_iter().collect();
        acct.rules.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        acct.heads_with_axiom = heads.values().filter(|(_, has, _)| *has).count();
        acct.heads_without_axiom = heads.len() - acct.heads_with_axiom;
        acct.heads = heads
            .into_iter()
            .map(|(name, (n, has, node))| (name, n, has, node))
            .collect();
        acct.heads.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));

        // The M2 census' list-cons argument sites: fields.rs deferred every
        // one of them here, and every one must land on a cell.
        let known: HashSet<&str> = modules.iter().map(|m| m.name.as_str()).collect();
        for site in &census.args {
            if crate::fields::in_population(site) != Some(true) {
                continue;
            }
            if !known.contains(site.module.as_str()) {
                continue;
            }
            let flow = index.get(&(site.module.as_str(), site.app)).copied();
            let field = flow.and_then(|_| {
                let m = modules
                    .iter()
                    .find(|m| m.name == site.module)
                    .expect("module selected");
                let (_, args) = m.spine(site.app);
                let s = Scope::new(m);
                value_args(&s, &args)
                    .iter()
                    .position(|a| *a == site.arg)
                    .map(|k| k as u32)
            });
            let (flow, reason) = match (flow, field) {
                (Some(i), Some(_)) => (Some(i), None),
                (Some(_), None) => (None, Some("argument-is-not-a-field-of-the-cell")),
                (None, _) => (None, Some("cons-cell-not-in-the-population")),
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
                flow,
                field,
                kind: flow.map(|i| flows[i].kind),
                spine: flow.map(|i| flows[i].spine),
                rec: flow.map(|i| flows[i].rec),
                reason,
            });
        }
        acct.check();
        ListCensus {
            per_module,
            flows,
            accounting: acct,
        }
    }
}

pub fn consumer_name(k: &ConsumerKind) -> &'static str {
    match k {
        ConsumerKind::ConsAlt { .. } => "ConsAlt",
        ConsumerKind::Whnf { .. } => "Whnf",
        ConsumerKind::Axiom { .. } => "Axiom",
        ConsumerKind::NoAxiom { .. } => "NoAxiom",
        ConsumerKind::StoredIn { .. } => "StoredIn",
        ConsumerKind::ConsedAsTail { .. } => "ConsedAsTail",
        ConsumerKind::PassedLocal { .. } => "PassedLocal",
        ConsumerKind::Escape { .. } => "Escape",
    }
}

/// The M2 census' population predicate for list-cons argument sites: the
/// `Family::ListCons` half of what [`crate::fields::in_population`] splits.
/// Kept here so the 1,310 can be recounted from this side.
pub fn census_site(a: &crate::laziness::ArgSite) -> bool {
    a.callee.family == Family::ListCons && crate::fields::in_population(a) == Some(true)
}
