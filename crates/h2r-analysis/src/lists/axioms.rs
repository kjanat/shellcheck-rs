//! The **library demand-semantics table**: what a list function that this
//! module cannot see into does to the spine it is handed.
//!
//! GHC's dump contains the Core of *this* program. A call to `map`, `++` or
//! `$wlenAcc` has no unfolding here, so the def-use walk can say only that
//! the list left the module. That is honest but useless: almost every list
//! in ShellCheck passes through base at some point. This table restores the
//! missing facts — explicitly, one entry at a time, each with a rule id, so
//! that every claim about an imported consumer can be read off the table
//! and audited rather than inferred.
//!
//! # The evidence level
//!
//! A **library axiom** is a new level in the hierarchy, and it sits *below*
//! def-use dataflow and *above* textual type comparison:
//!
//! 1. lexical binder identity
//! 2. structural shape
//! 3. def-use dataflow
//! 4. GHC type compatibility
//! 5. **library axiom** (this table)
//! 6. textual type comparison (corroboration)
//! 7. names (diagnostics)
//!
//! It is below dataflow because it is *asserted*, not derived: nothing in
//! the dump proves that `$base$GHC.List$reverse` traverses its whole
//! argument. It is above textual types because it is a statement about
//! semantics rather than about spelling.
//!
//! # The one hard rule
//!
//! **An axiom is only ever applied to an imported id.** The lookup key is
//! GHC's full stable name (`$unit$Module$occ`), and [`crate::lists`] calls
//! it only when [`h2r_core_ir::Module::binding_of`] says nothing in this
//! module binds the head. A program-defined function called `map` is *not*
//! looked up, and neither is a local `go`. Names are otherwise diagnostics
//! everywhere in this compiler; this table is the single deliberate
//! exception, which is why it is a separate file with a separate evidence
//! level.
//!
//! # How an entry is read
//!
//! List arguments are indexed **from the end** of the call's value
//! arguments, because a dictionary-polymorphic function like
//! `elem :: Eq a => a -> [a] -> Bool` is called with the dictionary
//! *prepended*, and how many dictionaries GHC leaves in place at `-O1`
//! varies per call site. `End(0)` is the last value argument, `End(1)` the
//! one before it. An entry declares [`Axiom::min_args`]; a call supplying
//! fewer value arguments than that is a partial application and the axiom
//! is **not** applied — the walk's own opaque-call rule handles it.
//!
//! # The two axes of the result (M2.3g)
//!
//! [`Produces`] is a statement about the call's **outer return type** and
//! nothing else. `span` returns `([a],[a])`, `$wspan` an unboxed pair,
//! `mapM` returns `m [b]`, `dropLengthMaybe` returns `Maybe [b]`: none of
//! those call nodes is a list, and only [`Produces::DirectList`] makes a
//! call an `L0-IMPORTED` producer. Whether cells are **shared** is the
//! separate [`Alias`] axis, and it is still recorded for those heads —
//! `span`'s second component is a suffix of its argument, which puts a
//! shared tail on the *input* flow even though the call itself is a pair.
//!
//! # Forcing versus exposure (M2.3g)
//!
//! [`crate::lists::HeadDemand`] is **proven** forcing only: a primitive
//! comparison (`eqString` at `Char`, `isSpace` in `words`), a `case` on the
//! element, `(&&)` in `and`. A predicate or a class method is not forcing —
//! `any (const True)` never looks at an element — and is recorded on the
//! second axis, [`HeadExposure`], instead. Exposure is still enough to
//! require the element to exist as a value, which is what the text census
//! reads; what it is not is a proof of evaluation.
//!
//! # Replay (M2.3g)
//!
//! [`Axiom::replays`] names the arguments a call **retains and traverses
//! again from the front**: `cycle`'s input, `isInfixOf`'s needle and
//! haystack, `isSuffixOf`'s two spines, `intercalate`'s separator. It is a
//! different fact from walking a spine twice in lockstep (`eqString`) and
//! from a shared tail (`drop`), and it was previously mis-encoded as a
//! `Whole` spine demand, which is wrong on an infinite argument.
//!
//! # What is deliberately absent
//!
//! Entries are written only where the semantics are certain. Several
//! GHC-internal helpers occur in the `-O1` dump whose argument order or
//! sharing behaviour cannot be read off their names —
//! `splitAt_$s$wsplitAt'`, `intercalate_$spoly_go1`, `dropLength`,
//! `dropLengthMaybe`, `prependToAll`, `head1`, `init1`, `lvl` — and they
//! get **no entry**, so a flow reaching them is reported as `Unknown` with
//! `no-axiom-for(<stable name>)` rather than guessed at. That residual is
//! the honest measure of this table's coverage.

use serde::Serialize;

use super::HeadDemand;

/// The base/ghc-prim the table was written against, read from
/// `compiler/matrix/A/plan.json`.
pub const BASE_VERSION: &str = "base-4.18.3.0, ghc-prim-0.10.0, ghc-bignum-1.3 (GHC 9.6.7)";

/// What a function demands of the *spine* of one list argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ArgSpine {
    /// Every cell is reached before the call can return.
    Whole,
    /// A bounded prefix, whose length is the value argument at this
    /// end-index (a literal `Int`/`Int#` there gives a `Known` bound).
    PrefixFromArg(u8),
    /// A prefix whose length depends on the data.
    PrefixDataDependent,
    /// Each cell is reached at most once, on demand, as the *result* is
    /// consumed: the call itself forces nothing beyond what its own
    /// consumer asks for.
    Incremental,
    /// The argument's spine is not walked at all.
    NoDemand,
}

/// Does the result share cells with an argument? Two axes are kept apart
/// on purpose (M2.3g): whether the *outer* result is a list is
/// [`Produces`], and whether cells are shared is this.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Alias {
    /// Every cell of the result is freshly allocated.
    NoAlias,
    /// The result's own tail *is* this argument (end-indexed): the spine
    /// survives inside the result and is shared with it.
    ResultIsTailOfArg(u8),
    /// The result contains a suffix of this argument (end-indexed).
    ResultSharesArg(u8),
    /// The result is **not** a list, but a list *inside* it is a suffix of
    /// this argument: `span`'s second component, `dropLengthMaybe`'s
    /// `Just`. The argument's spine survives beside the call exactly as it
    /// does for [`Alias::ResultSharesArg`] — the difference is only that
    /// the call node itself is not a list (M2.3g).
    ResultContainsSuffixOfArg(u8),
    /// The result shares cells with a list that is an **element** of this
    /// argument, not with the argument's own spine: `head :: [[a]] -> [a]`
    /// returns one of the inner lists. This puts **no** sharing on the
    /// argument's spine, which is why it is a variant of its own (M2.3g).
    ResultSharesElementOf(u8),
}

/// How a produced list is built, once [`Produces`] has said that the
/// return type really does contain one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ListKind {
    /// One cell at a time, as the consumer asks for it.
    Incremental,
    /// Nothing is returned until the whole input has been consumed.
    WholeBeforeFirstCell,
    /// The result *is* (a suffix of) the input: no cell is built.
    SameAsInput,
    /// Infinite, or bounded only by the consumer.
    Unbounded,
}

impl ListKind {
    pub fn name(self) -> &'static str {
        match self {
            ListKind::Incremental => "Incremental",
            ListKind::WholeBeforeFirstCell => "WholeBeforeFirstCell",
            ListKind::SameAsInput => "SameAsInput",
            ListKind::Unbounded => "Unbounded",
        }
    }
}

/// What the call's **outer return type** is. This is a statement about the
/// type of the call node, not about what is reachable from it: `span`
/// returns a *pair* of lists and `mapM` returns `m [b]`, and neither call
/// node is a list. Only [`Produces::DirectList`] makes a call an
/// [`crate::lists::L0_IMPORTED`] producer; the other containing variants
/// keep their argument-demand and aliasing facts for the consumer side and
/// produce no flow, because recovering the components is tuple and effect
/// normalisation's job, not this milestone's (M2.3g).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Produces {
    /// The return type contains no list this table speaks about.
    NotAList,
    /// The return type **is** `[a]`.
    DirectList(ListKind),
    /// The return type is a product — a boxed or unboxed tuple — with this
    /// many list components.
    ProductContainsList { components: u8 },
    /// The return type is `m [b]`.
    EffectContainsList(ListKind),
    /// The return type is some other container holding a list: `Maybe [b]`.
    OtherContainsList,
}

impl Produces {
    /// Is the **call node itself** a list? The one question the population
    /// may ask.
    pub fn is_direct_list(self) -> bool {
        matches!(self, Produces::DirectList(_))
    }

    /// How a [`Produces::DirectList`] result is built.
    pub fn kind(self) -> Option<ListKind> {
        match self {
            Produces::DirectList(k) | Produces::EffectContainsList(k) => Some(k),
            _ => None,
        }
    }

    pub fn name(self) -> String {
        match self {
            Produces::NotAList => "NotAList".into(),
            Produces::DirectList(k) => format!("DirectList({})", k.name()),
            Produces::ProductContainsList { components } => {
                format!("ProductContainsList({components})")
            }
            Produces::EffectContainsList(k) => format!("EffectContainsList({})", k.name()),
            Produces::OtherContainsList => "OtherContainsList".into(),
        }
    }
}

/// Which callback an element is handed to, when the axiom can prove
/// exposure but **not** forcing (M2.3g).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum CallbackKind {
    /// `a -> Bool`, supplied at the call site.
    Predicate,
    /// A method of the `Eq` dictionary.
    Eq,
    /// A method of the `Ord` dictionary.
    Ord,
    /// A method of the `Show` dictionary.
    Show,
    /// Any other function the call site supplies.
    Other,
}

impl CallbackKind {
    pub fn name(self) -> &'static str {
        match self {
            CallbackKind::Predicate => "Predicate",
            CallbackKind::Eq => "Eq",
            CallbackKind::Ord => "Ord",
            CallbackKind::Show => "Show",
            CallbackKind::Other => "Other",
        }
    }
}

/// Fact 2b (M2.3g): an element **reaches** something this table cannot see
/// into. Exposure is not forcing — `any (const True)` never forces an
/// element — but it is enough to require the element to exist as a value,
/// which is what the text census needs. Recorded beside
/// [`crate::lists::HeadDemand`], never folded into it.
///
/// Ordered weakest to strongest, so joining is a maximum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum HeadExposure {
    /// No reachable observation hands an element anywhere.
    NotExposed,
    /// A `(:)` alternative binds the element and uses it.
    BoundAndUsed,
    /// An element is handed to a function or class method supplied at the
    /// call site.
    PassedToCallback(CallbackKind),
    /// A consumer is outside what this module proves.
    Unknown,
}

impl HeadExposure {
    pub fn name(self) -> &'static str {
        match self {
            HeadExposure::NotExposed => "NotExposed",
            HeadExposure::BoundAndUsed => "BoundAndUsed",
            HeadExposure::PassedToCallback(CallbackKind::Predicate) => {
                "PassedToCallback(Predicate)"
            }
            HeadExposure::PassedToCallback(CallbackKind::Eq) => "PassedToCallback(Eq)",
            HeadExposure::PassedToCallback(CallbackKind::Ord) => "PassedToCallback(Ord)",
            HeadExposure::PassedToCallback(CallbackKind::Show) => "PassedToCallback(Show)",
            HeadExposure::PassedToCallback(CallbackKind::Other) => "PassedToCallback(Other)",
            HeadExposure::Unknown => "Unknown",
        }
    }
}

/// One library function's demand semantics.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct Axiom {
    /// GHC's stable name, `$unit$Module$occ`.
    pub name: &'static str,
    /// The semantic rule id this entry asserts.
    pub rule: &'static str,
    /// Value arguments a call must supply before the entry applies.
    pub min_args: usize,
    /// `(end-index, spine demand)` for each list argument.
    pub list_args: &'static [(u8, ArgSpine)],
    /// End-indices of the list arguments this call **retains and traverses
    /// again from the front** — `cycle`'s input, `isInfixOf`'s needle,
    /// `intercalate`'s separator. Distinct from walking a spine twice in
    /// lockstep and from a shared tail (M2.3g).
    pub replays: &'static [u8],
    /// What the call **provably forces** of the elements it reaches. A
    /// callback that *may* force is not forcing: that is [`Axiom::exposure`]
    /// (M2.3g).
    pub head: HeadDemand,
    /// What the call hands the elements to, when it cannot prove forcing.
    pub exposure: HeadExposure,
    pub alias: Alias,
    /// May the call stop before reaching the end of the spine?
    pub short_circuit: bool,
    /// Does it touch each cell once as it goes, retaining nothing?
    pub streaming: bool,
    pub produces: Produces,
    pub note: &'static str,
}

impl Axiom {
    /// The spine demand this entry puts on the value argument at
    /// `idx` of a call supplying `n` value arguments, if that argument is
    /// one of the entry's list arguments.
    pub fn spine_of(&self, idx: usize, n: usize) -> Option<ArgSpine> {
        self.list_args
            .iter()
            .find(|(end, _)| end_index(*end, n) == Some(idx))
            .map(|(_, s)| *s)
    }

    /// Does a tail of the argument at `idx` survive beside the call —
    /// whether inside the result or as the result itself? This is the one
    /// question the `SharedTail` fact asks, and
    /// [`Alias::ResultSharesElementOf`] deliberately does **not** answer it
    /// yes: an element is not the spine.
    pub fn aliases_spine(&self, idx: usize, n: usize) -> bool {
        match self.alias {
            Alias::NoAlias | Alias::ResultSharesElementOf(_) => false,
            Alias::ResultIsTailOfArg(e)
            | Alias::ResultSharesArg(e)
            | Alias::ResultContainsSuffixOfArg(e) => end_index(e, n) == Some(idx),
        }
    }

    /// Does the result share cells with a list stored as an **element** of
    /// the argument at `idx`? No spine sharing follows from this.
    pub fn aliases_element(&self, idx: usize, n: usize) -> bool {
        match self.alias {
            Alias::ResultSharesElementOf(e) => end_index(e, n) == Some(idx),
            _ => false,
        }
    }

    /// Is the list argument at `idx` retained and traversed again?
    pub fn replays_arg(&self, idx: usize, n: usize) -> bool {
        self.replays.iter().any(|e| end_index(*e, n) == Some(idx))
    }
}

/// Turn an end-index into a position in a call's value-argument list.
pub fn end_index(end: u8, n: usize) -> Option<usize> {
    n.checked_sub(1 + end as usize)
}

/// The one lookup. `name` is GHC's stable name of an **imported** id; the
/// caller must have established that nothing in the module binds it.
pub fn axiom(name: &str) -> Option<&'static Axiom> {
    AXIOMS.iter().find(|a| a.name == name)
}

/// Every entry, for `h2r lists --axioms`.
pub fn all() -> &'static [Axiom] {
    AXIOMS
}

#[allow(clippy::too_many_arguments)]
const fn ax(
    name: &'static str,
    rule: &'static str,
    min_args: usize,
    list_args: &'static [(u8, ArgSpine)],
    replays: &'static [u8],
    head: HeadDemand,
    exposure: HeadExposure,
    alias: Alias,
    short_circuit: bool,
    streaming: bool,
    produces: Produces,
    note: &'static str,
) -> Axiom {
    Axiom {
        name,
        rule,
        min_args,
        list_args,
        replays,
        head,
        exposure,
        alias,
        short_circuit,
        streaming,
        produces,
        note,
    }
}

use ArgSpine::{Incremental, NoDemand, PrefixDataDependent, PrefixFromArg, Whole};
use CallbackKind as K;
use HeadDemand as H;
use HeadExposure as E;
use ListKind as LK;

/// No replayed argument: the call walks each list argument at most once.
const ONCE: &[u8] = &[];

/// The table. Entries are grouped by where they come from; every one of
/// them is asserted, not derived, and every one carries its own rule id.
static AXIOMS: &[Axiom] = &[
    //--------------------------------------------------------------------
    // ghc-prim: string literals unpacked into `[Char]`.
    //--------------------------------------------------------------------
    ax(
        "$ghc-prim$GHC.CString$unpackCString#",
        "L-AX-UNPACK-CSTRING",
        1,
        &[],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "static data unpacked one cell at a time; no list argument",
    ),
    ax(
        "$ghc-prim$GHC.CString$unpackCStringUtf8#",
        "L-AX-UNPACK-CSTRING-UTF8",
        1,
        &[],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "as unpackCString#, decoding UTF-8",
    ),
    ax(
        "$ghc-prim$GHC.CString$unpackAppendCString#",
        "L-AX-UNPACK-APPEND-CSTRING",
        2,
        &[(0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "literal ++ rest: the argument becomes the result's tail, untouched",
    ),
    ax(
        "$ghc-prim$GHC.CString$unpackAppendCStringUtf8#",
        "L-AX-UNPACK-APPEND-CSTRING-UTF8",
        2,
        &[(0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "as unpackAppendCString#, decoding UTF-8",
    ),
    //--------------------------------------------------------------------
    // GHC.Base
    //--------------------------------------------------------------------
    ax(
        "$base$GHC.Base$map",
        "L-AX-MAP",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one input cell per output cell, on demand; elements are not forced",
    ),
    ax(
        "$base$GHC.Base$++",
        "L-AX-APPEND",
        2,
        &[(1, Incremental), (0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "the left spine is copied on demand; the right argument IS the result's tail",
    ),
    ax(
        "$base$GHC.Base$++_$s++",
        "L-AX-APPEND-SPEC",
        2,
        &[(1, Incremental), (0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "a type-specialised copy of (++); same semantics",
    ),
    ax(
        "$base$GHC.Base$eqString",
        "L-AX-EQSTRING",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::Prefix,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "compares cell by cell and stops at the first difference. M2.3g: at Char the comparison is the `eqChar#` primop, so this one really does force each element pair it reaches",
    ),
    ax(
        "$base$GHC.Base$foldr",
        "L-AX-FOLDR",
        3,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "the combining function decides how far the spine is walked",
    ),
    //--------------------------------------------------------------------
    // GHC.List: the standard consumers, and the workers -O1 leaves behind.
    //--------------------------------------------------------------------
    ax(
        "$base$GHC.List$head",
        "L-AX-HEAD",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesElementOf(0),
        true,
        true,
        Produces::NotAList,
        "one cell; the element is returned unforced. M2.3g: `head (x:_) = x` — when the elements are themselves lists the result IS one of them, which is element sharing and puts nothing on this spine",
    ),
    ax(
        "$base$GHC.List$tail",
        "L-AX-TAIL",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultIsTailOfArg(0),
        true,
        true,
        Produces::DirectList(LK::SameAsInput),
        "one cell; the result IS the argument's tail",
    ),
    ax(
        "$base$GHC.List$last",
        "L-AX-LAST",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesElementOf(0),
        false,
        true,
        Produces::NotAList,
        "walks every cell; the element is returned unforced. M2.3g: the result is an element; element sharing, not spine sharing",
    ),
    ax(
        "$base$GHC.List$length",
        "L-AX-LENGTH",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "walks every cell; reads no element",
    ),
    ax(
        "$base$GHC.List$$wlenAcc",
        "L-AX-WLENACC",
        2,
        &[(1, Whole)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "the worker of length's accumulating loop: [a] -> Int# -> Int#",
    ),
    ax(
        "$base$GHC.List$reverse",
        "L-AX-REVERSE",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::WholeBeforeFirstCell),
        "nothing is returned until the whole input has been consumed",
    ),
    ax(
        "$base$GHC.List$reverse1",
        "L-AX-REVERSE1",
        2,
        &[(1, Whole), (0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::DirectList(LK::WholeBeforeFirstCell),
        "reverse's accumulating loop rev xs acc: acc becomes the result's tail",
    ),
    ax(
        "$base$GHC.List$head1",
        "L-AX-BADHEAD",
        1,
        &[],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "base's `badHead :: HasCallStack => a`, the head [] error, floated out of          `head`: its one value argument is the call stack and it has no list          argument at all. Confirmed against base-4.18.3.0 and against the dump,          where the type argument is the *result* type and the value argument is a          CallStack dictionary",
    ),
    ax(
        "$base$GHC.List$init1",
        "L-AX-INIT1",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "base's `init' :: t -> [t] -> [t]`, the local worker of `init` floated out:          one cell of the list argument per output cell, one cell ahead, elements          copied unforced, result freshly built",
    ),
    ax(
        "$base$GHC.List$flipSeq",
        "L-AX-FLIPSEQ",
        2,
        &[(1, NoDemand), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesArg(1),
        false,
        true,
        Produces::NotAList,
        "base's `flipSeq x !_n = x` (flip seq, not inlined too early): the result IS          the first argument, untouched, and the second is forced to WHNF and          discarded. `NotAList` because `a` is not a list at every call site in this          program, so the result must not be made a list flow; the aliasing entry          still records that the result keeps the argument alive",
    ),
    ax(
        "$base$GHC.List$splitAt_$s$wsplitAt'",
        "L-AX-WSPLITAT-SPEC",
        2,
        &[(0, PrefixFromArg(1))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::ProductContainsList { components: 2 },
        "a specialised worker of base's local `splitAt' :: Int -> [a] -> ([a],[a])`:          count first, list second, and the second component is a suffix of the          input. The dump's types corroborate the order (Int#, then the list). M2.3g: the worker returns an unboxed pair, not a list",
    ),
    ax(
        "$base$Data.OldList$dropLength",
        "L-AX-DROPLENGTH",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::DirectList(LK::SameAsInput),
        "base's `dropLength :: [a] -> [b] -> [b]`, used by isSuffixOf: walks both          spines in lockstep until the shorter runs out and returns a SUFFIX of the          second argument, forcing no element",
    ),
    ax(
        "$base$Data.OldList$dropLengthMaybe",
        "L-AX-DROPLENGTHMAYBE",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::OtherContainsList,
        "as dropLength, returning `Maybe [b]`: the suffix of the second argument          survives inside the `Just`, so the alias holds although the result is not          itself a list. M2.3g: the result is `Maybe [b]` — a container holding a suffix, not a list",
    ),
    ax(
        "$base$Data.OldList$prependToAll",
        "L-AX-PREPENDTOALL",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "base's `prependToAll sep (x:xs) = sep : x : prependToAll sep xs`, the          helper behind intersperse: separator first, list second, one input cell          per two output cells, on demand",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fEqList_$s$c==1",
        "L-AX-EQLIST-SPEC",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a SPECIALISE'd copy of ghc-prim's `instance Eq a => Eq [a]`: walks both          spines in lockstep and stops at the first difference, forcing each element          pair it reaches. Same semantics as eqString, which is this instance at Char. M2.3g: the element `==` is a dictionary method and may ignore its arguments; eqString is the Char case, where it is a primitive and does force",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fEqList_$s$c==2",
        "L-AX-EQLIST-SPEC2",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a second SPECIALISE'd copy of the same instance, at another element type. M2.3g: exposure to the element Eq, not forcing",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fOrdList_$s$ccompare",
        "L-AX-COMPARELIST-SPEC",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Ord),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a SPECIALISE'd copy of ghc-prim's `instance Ord a => Ord [a]` compare:          walks both spines in lockstep and stops at the first element pair that          does not compare EQ. M2.3g: exposure to the element Ord, not forcing",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fOrdList_$s$ccompare1",
        "L-AX-COMPARELIST-SPEC1",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Ord),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a second SPECIALISE'd copy of the same instance method. M2.3g: exposure to the element Ord, not forcing",
    ),
    ax(
        "$base$GHC.List$filter",
        "L-AX-FILTER",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "the predicate forces what it forces; cells are copied on demand",
    ),
    ax(
        "$base$GHC.List$takeWhile",
        "L-AX-TAKEWHILE",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::DirectList(LK::Incremental),
        "stops at the first element the predicate rejects. M2.3g: an arbitrary predicate may ignore its argument (`const True`), so the elements are exposed, not forced",
    ),
    ax(
        "$base$GHC.List$dropWhile",
        "L-AX-DROPWHILE",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::DirectList(LK::SameAsInput),
        "the result is a suffix of the argument: no cell is built. M2.3g: exposed to the predicate, not forced",
    ),
    ax(
        "$base$GHC.List$span",
        "L-AX-SPAN",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::ProductContainsList { components: 2 },
        "the second component is a suffix of the argument. M2.3g: `span p xs = (takeWhile p xs, dropWhile p xs)` returns a PAIR — the call node is not a list, so it is no longer a producer; the second component is still a suffix of the argument, and `p` may ignore its argument, so the elements are exposed and not forced",
    ),
    ax(
        "$base$GHC.List$$wspan",
        "L-AX-WSPAN",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::ProductContainsList { components: 2 },
        "span's worker, returning an unboxed pair; the second component is a suffix. M2.3g: the unboxed pair is not a list; the suffix aliasing and the predicate exposure are unchanged",
    ),
    ax(
        "$base$GHC.List$break",
        "L-AX-BREAK",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::ProductContainsList { components: 2 },
        "span with the predicate negated. M2.3g: as span — a pair, not a list",
    ),
    ax(
        "$base$GHC.List$$wbreak",
        "L-AX-WBREAK",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::ProductContainsList { components: 2 },
        "break's worker, returning an unboxed pair. M2.3g: as $wspan — an unboxed pair, not a list",
    ),
    ax(
        "$base$GHC.List$take",
        "L-AX-TAKE",
        2,
        &[(0, PrefixFromArg(1))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::DirectList(LK::Incremental),
        "at most n cells; a literal n gives a Known bound",
    ),
    ax(
        "$base$GHC.List$$wunsafeTake",
        "L-AX-WUNSAFETAKE",
        2,
        &[(0, PrefixFromArg(1))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::DirectList(LK::Incremental),
        "take's worker on an unboxed count, called when n is known positive",
    ),
    ax(
        "$base$GHC.List$drop",
        "L-AX-DROP",
        2,
        &[(0, PrefixFromArg(1))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::DirectList(LK::SameAsInput),
        "walks n cells and returns the suffix: the result aliases the input",
    ),
    ax(
        "$base$GHC.List$splitAt",
        "L-AX-SPLITAT",
        2,
        &[(0, PrefixFromArg(1))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultContainsSuffixOfArg(0),
        true,
        true,
        Produces::ProductContainsList { components: 2 },
        "the second component is a suffix of the input. M2.3g: `splitAt n xs = (take n xs, drop n xs)` returns a PAIR; the call node is not a list",
    ),
    ax(
        "$base$GHC.List$!!",
        "L-AX-INDEX",
        2,
        &[(1, PrefixFromArg(0))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesElementOf(1),
        true,
        true,
        Produces::NotAList,
        "walks n cells; the element is returned unforced. M2.3g: the result is an element; element sharing, not spine sharing",
    ),
    ax(
        "$base$GHC.List$$w!!",
        "L-AX-WINDEX",
        2,
        &[(1, PrefixFromArg(0))],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesElementOf(1),
        true,
        true,
        Produces::NotAList,
        "(!!)'s worker on an unboxed index. M2.3g: the result is an element; element sharing, not spine sharing",
    ),
    ax(
        "$base$GHC.List$elem",
        "L-AX-ELEM",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first match. M2.3g: `elem` calls the `Eq` dictionary's (==), which may ignore its argument, so the elements are EXPOSED and not provably forced",
    ),
    ax(
        "$base$GHC.List$notElem",
        "L-AX-NOTELEM",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first match. M2.3g: exposed to Eq, not provably forced",
    ),
    ax(
        "$base$GHC.List$lookup",
        "L-AX-LOOKUP",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first matching key; forces the keys it compares. M2.3g: the keys are exposed to Eq, not provably forced",
    ),
    ax(
        "$base$GHC.List$zip",
        "L-AX-ZIP",
        2,
        &[(1, Incremental), (0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::DirectList(LK::Incremental),
        "stops at the shorter spine; elements are not forced",
    ),
    ax(
        "$base$GHC.List$zipWith",
        "L-AX-ZIPWITH",
        3,
        &[(1, Incremental), (0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        true,
        true,
        Produces::DirectList(LK::Incremental),
        "stops at the shorter spine",
    ),
    ax(
        "$base$GHC.List$unzip",
        "L-AX-UNZIP",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        false,
        Produces::ProductContainsList { components: 2 },
        "both result spines are driven by the one input spine. M2.3g: `unzip :: [(a,b)] -> ([a],[b])` returns a PAIR of two freshly built lists; the call node is not a list",
    ),
    ax(
        "$base$GHC.List$concat",
        "L-AX-CONCAT",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "concat = foldr (++) []: every inner list is a LEFT operand of (++) and is          copied, and [[a]] spine cells can never be [a] result cells — no aliasing",
    ),
    ax(
        "$base$GHC.List$concatMap",
        "L-AX-CONCATMAP",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one input cell per exhausted inner list",
    ),
    ax(
        "$base$GHC.List$foldl",
        "L-AX-FOLDL",
        3,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "walks every cell; the accumulator is left unforced (thunks build up)",
    ),
    ax(
        "$base$GHC.List$foldl'",
        "L-AX-FOLDL-STRICT",
        3,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "walks every cell once, retaining nothing: a streaming consumer of the whole spine",
    ),
    ax(
        "$base$GHC.List$and",
        "L-AX-AND",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::Prefix,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first False. M2.3g: `and = foldr (&&) True` and (&&) case-analyses its argument, so the Bool elements really are forced",
    ),
    ax(
        "$base$GHC.List$or",
        "L-AX-OR",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::Prefix,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first True. M2.3g: `or = foldr (||) False` case-analyses each element: proven forcing",
    ),
    ax(
        "$base$GHC.List$any",
        "L-AX-ANY",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first element the predicate accepts. M2.3g: `any (const True)` forces no element: exposure, not forcing",
    ),
    ax(
        "$base$GHC.List$all",
        "L-AX-ALL",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first element the predicate rejects. M2.3g: exposure, not forcing",
    ),
    ax(
        "$base$GHC.List$replicate",
        "L-AX-REPLICATE",
        2,
        &[],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "produces n cells on demand; no list argument",
    ),
    ax(
        "$base$GHC.List$iterate",
        "L-AX-ITERATE",
        2,
        &[],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Unbounded),
        "infinite; bounded only by its consumer",
    ),
    ax(
        "$base$GHC.List$repeat",
        "L-AX-REPEAT",
        1,
        &[],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Unbounded),
        "infinite; bounded only by its consumer",
    ),
    ax(
        "$base$GHC.List$cycle",
        "L-AX-CYCLE",
        1,
        &[(0, Incremental)],
        &[0],
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::Unbounded),
        "infinite; the argument is retained and replayed. M2.3g: `cycle xs = xs' where xs' = xs ++ xs'` consumes the argument INCREMENTALLY and replays it forever; calling the demand `Whole` was wrong — on an infinite argument nothing would ever finish",
    ),
    ax(
        "$ghc-prim$GHC.Magic$lazy",
        "L-AX-LAZY",
        1,
        &[(0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesArg(0),
        false,
        true,
        Produces::NotAList,
        "the identity with a demand-analyser annotation: the result IS the argument. M2.3g: `lazy :: a -> a`, and `a` is not a list at every call site in this program, so the call must not be made a list producer — exactly the reason flipSeq is NotAList. The aliasing entry still records that the result IS the argument",
    ),
    ax(
        "$base$Data.Maybe$mapMaybe",
        "L-AX-MAPMAYBE",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one input cell per output cell, on demand; elements are not forced",
    ),
    //--------------------------------------------------------------------
    // Data.OldList
    //--------------------------------------------------------------------
    ax(
        "$base$Data.OldList$lines",
        "L-AX-LINES",
        1,
        &[(0, Incremental)],
        ONCE,
        H::All,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "splits on demand; each line's characters are forced to find the newline.          Each line is built by `break`'s first component, which is fresh, and a          [String] spine cell is never a String cell — no aliasing. M2.3g: the newline test is `eqChar` on Char, a primitive: proven forcing",
    ),
    ax(
        "$base$Data.OldList$unlines",
        "L-AX-UNLINES",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one input cell per exhausted line",
    ),
    ax(
        "$base$Data.OldList$words",
        "L-AX-WORDS",
        1,
        &[(0, Incremental)],
        ONCE,
        H::All,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "splits on demand; characters are forced to find the separators. M2.3g: `isSpace` case-analyses the Char: proven forcing",
    ),
    ax(
        "$base$Data.OldList$unwords",
        "L-AX-UNWORDS",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one input cell per exhausted word",
    ),
    ax(
        "$base$Data.OldList$intercalate",
        "L-AX-INTERCALATE",
        2,
        &[(0, Incremental), (1, Incremental)],
        &[1],
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::Incremental),
        "the separator is replayed between elements, so it is retained. M2.3g: the separator is a replayed argument",
    ),
    ax(
        "$base$Data.OldList$isPrefixOf",
        "L-AX-ISPREFIXOF",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first difference or at the end of the left argument. M2.3g: exposed to Eq, not provably forced",
    ),
    ax(
        "$base$Data.OldList$isSuffixOf",
        "L-AX-ISSUFFIXOF",
        2,
        &[(1, Whole), (0, Whole)],
        &[0, 1],
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        false,
        false,
        Produces::NotAList,
        "both spines are walked to the end before anything is compared. M2.3g: `isSuffixOf ns hs = maybe False id $ do delta <- dropLengthMaybe ns hs; return $ ns == dropLength delta hs` walks both spines twice — once to measure, once to compare — so both are replayed",
    ),
    ax(
        "$base$Data.OldList$isInfixOf",
        "L-AX-ISINFIXOF",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        &[0, 1],
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        false,
        Produces::NotAList,
        "the needle is retained and replayed against every position of the haystack. M2.3g: `isInfixOf needle hay = any (isPrefixOf needle) (tails hay)` retries the needle at successive positions: neither spine is necessarily walked to the end, and both are re-traversed, so this is a data-dependent prefix that is REPLAYED, not a whole traversal",
    ),
    ax(
        "$base$Data.OldList$nub",
        "L-AX-NUB",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::Incremental),
        "every element accepted so far is retained and compared against. M2.3g: the elements are compared with the `Eq` dictionary, which may ignore them: exposure, not forcing",
    ),
    ax(
        "$base$Data.OldList$nubBy",
        "L-AX-NUBBY",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::Incremental),
        "every element accepted so far is retained and compared against",
    ),
    ax(
        "$base$Data.OldList$sort",
        "L-AX-SORT",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Ord),
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::WholeBeforeFirstCell),
        "the whole spine is consumed and the elements compared before the first cell. M2.3g: exposed to `compare`, not provably forced",
    ),
    ax(
        "$base$Data.OldList$sortBy",
        "L-AX-SORTBY",
        2,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::WholeBeforeFirstCell),
        "the whole spine is consumed before the first cell; the comparator forces what it forces",
    ),
    ax(
        "$base$Data.OldList$sortOn",
        "L-AX-SORTON",
        2,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::DirectList(LK::WholeBeforeFirstCell),
        "the key of every element is computed before the first cell. M2.3g: base seqs the computed KEY, not the element: exposure of the element, not forcing",
    ),
    ax(
        "$base$Data.OldList$group",
        "L-AX-GROUP",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one group at a time, on demand. M2.3g: `group = groupBy (==)`: exposure to Eq, not forcing",
    ),
    ax(
        "$base$Data.OldList$groupBy",
        "L-AX-GROUPBY",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "one group at a time, on demand",
    ),
    ax(
        "$base$Data.OldList$find",
        "L-AX-FIND-OLDLIST",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first element the predicate accepts. M2.3g: exposure, not forcing",
    ),
    //--------------------------------------------------------------------
    // Data.Foldable / Data.Traversable, at the list instance.
    //--------------------------------------------------------------------
    ax(
        "$base$Data.Foldable$elem",
        "L-AX-FOLDABLE-ELEM",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first match. M2.3g: exposed to Eq, not provably forced",
    ),
    ax(
        "$base$Data.Foldable$notElem",
        "L-AX-FOLDABLE-NOTELEM",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Eq),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first match. M2.3g: exposed to Eq, not provably forced",
    ),
    ax(
        "$base$Data.Foldable$find",
        "L-AX-FOLDABLE-FIND",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first element the predicate accepts. M2.3g: exposure, not forcing",
    ),
    ax(
        "$base$Data.Foldable$any",
        "L-AX-FOLDABLE-ANY",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first acceptance. M2.3g: exposure, not forcing",
    ),
    ax(
        "$base$Data.Foldable$all",
        "L-AX-FOLDABLE-ALL",
        2,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Predicate),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first rejection. M2.3g: exposure, not forcing",
    ),
    ax(
        "$base$Data.Foldable$and",
        "L-AX-FOLDABLE-AND",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::Prefix,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first False",
    ),
    ax(
        "$base$Data.Foldable$or",
        "L-AX-FOLDABLE-OR",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::Prefix,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first True",
    ),
    ax(
        "$base$Data.Foldable$length",
        "L-AX-FOLDABLE-LENGTH",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: walks every cell, reads no element",
    ),
    ax(
        "$base$Data.Foldable$null",
        "L-AX-FOLDABLE-NULL",
        1,
        &[(0, PrefixDataDependent)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "one cell: is there a first one?",
    ),
    ax(
        "$base$Data.Foldable$sum",
        "L-AX-FOLDABLE-SUM",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell and every element. M2.3g: `(+)` comes from a `Num` dictionary and may ignore an argument: exposure, not forcing",
    ),
    ax(
        "$base$Data.Foldable$maximum",
        "L-AX-FOLDABLE-MAXIMUM",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Ord),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell and every element. M2.3g: exposed to `compare`, not provably forced",
    ),
    ax(
        "$base$Data.Foldable$minimum",
        "L-AX-FOLDABLE-MINIMUM",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Ord),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell and every element. M2.3g: exposed to `compare`, not provably forced",
    ),
    ax(
        "$base$Data.Foldable$concat",
        "L-AX-FOLDABLE-CONCAT",
        1,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "at the list instance, as GHC.List.concat: everything is copied, and the          argument's spine is one type constructor further out than the result's",
    ),
    ax(
        "$base$Data.Foldable$concatMap",
        "L-AX-FOLDABLE-CONCATMAP",
        2,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::DirectList(LK::Incremental),
        "at the list instance: one input cell per exhausted inner list",
    ),
    ax(
        "$base$Data.Foldable$toList",
        "L-AX-FOLDABLE-TOLIST",
        1,
        &[(0, NoDemand)],
        ONCE,
        H::None,
        E::NotExposed,
        Alias::ResultSharesArg(0),
        false,
        true,
        Produces::DirectList(LK::SameAsInput),
        "at the list instance: the identity",
    ),
    ax(
        "$base$Data.Foldable$foldr",
        "L-AX-FOLDABLE-FOLDR",
        3,
        &[(0, Incremental)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: the combining function decides how far the spine is walked",
    ),
    ax(
        "$base$Data.Foldable$foldl'",
        "L-AX-FOLDABLE-FOLDL-STRICT",
        3,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell once, retaining nothing",
    ),
    ax(
        "$base$Data.Foldable$mapM_",
        "L-AX-MAPM-UNIT",
        2,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell once, in order, retaining nothing",
    ),
    ax(
        "$base$Data.Foldable$forM_",
        "L-AX-FORM-UNIT",
        2,
        &[(1, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "mapM_ with the arguments flipped",
    ),
    ax(
        "$base$Data.Foldable$sequence_",
        "L-AX-SEQUENCE-UNIT",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell once, in order",
    ),
    ax(
        "$base$Data.Foldable$traverse_",
        "L-AX-TRAVERSE-UNIT",
        2,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell once, in order",
    ),
    ax(
        "$base$Data.Traversable$mapM",
        "L-AX-MAPM",
        2,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::EffectContainsList(LK::WholeBeforeFirstCell),
        "at the list instance: the whole spine is consumed before the result exists. M2.3g: `mapM :: (a -> m b) -> [a] -> m [b]` returns an ACTION, not a list; the list is inside it, and recovering it is effect normalisation's job",
    ),
    ax(
        "$base$Data.Traversable$forM",
        "L-AX-FORM",
        2,
        &[(1, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::EffectContainsList(LK::WholeBeforeFirstCell),
        "mapM with the arguments flipped. M2.3g: returns `m [b]`, not a list",
    ),
    ax(
        "$base$Data.Traversable$traverse",
        "L-AX-TRAVERSE",
        2,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::EffectContainsList(LK::WholeBeforeFirstCell),
        "at the list instance: the whole spine is consumed before the result exists. M2.3g: returns `f [b]`, not a list",
    ),
    ax(
        "$base$Data.Traversable$sequence",
        "L-AX-SEQUENCE",
        1,
        &[(0, Whole)],
        ONCE,
        H::None,
        E::PassedToCallback(K::Other),
        Alias::NoAlias,
        false,
        false,
        Produces::EffectContainsList(LK::WholeBeforeFirstCell),
        "at the list instance: the whole spine is consumed before the result exists. M2.3g: `sequence :: [m a] -> m [a]` returns an action, not a list",
    ),
];

#[cfg(test)]
mod tests {
    use super::*;

    /// Rule ids and stable names are the table's keys: both must be unique,
    /// or one entry silently shadows another.
    #[test]
    fn the_table_has_no_duplicate_keys() {
        let mut names: Vec<&str> = AXIOMS.iter().map(|a| a.name).collect();
        names.sort_unstable();
        let n = names.len();
        names.dedup();
        assert_eq!(names.len(), n, "duplicate stable name in the axiom table");
        let mut rules: Vec<&str> = AXIOMS.iter().map(|a| a.rule).collect();
        rules.sort_unstable();
        let n = rules.len();
        rules.dedup();
        assert_eq!(rules.len(), n, "duplicate rule id in the axiom table");
    }

    /// Every entry names a global the way GHC does, carries a rule id of
    /// the milestone's shape, and indexes only arguments a saturated call
    /// actually has.
    #[test]
    fn every_entry_is_well_formed() {
        for a in AXIOMS {
            assert!(
                crate::callee::split_stable_name(a.name).is_some(),
                "{}: not a stable name",
                a.name
            );
            assert!(a.rule.starts_with("L-AX-"), "{}: bad rule id", a.name);
            assert!(!a.note.is_empty(), "{}: no note", a.name);
            for (end, spine) in a.list_args {
                assert!(
                    (*end as usize) < a.min_args,
                    "{}: list argument End({end}) outside min_args {}",
                    a.name,
                    a.min_args
                );
                if let ArgSpine::PrefixFromArg(b) = spine {
                    assert!(
                        (*b as usize) < a.min_args,
                        "{}: bound argument End({b}) outside min_args",
                        a.name
                    );
                }
            }
            match a.alias {
                Alias::NoAlias => {}
                Alias::ResultIsTailOfArg(e)
                | Alias::ResultSharesArg(e)
                | Alias::ResultContainsSuffixOfArg(e)
                | Alias::ResultSharesElementOf(e) => assert!(
                    (e as usize) < a.min_args,
                    "{}: alias argument outside min_args",
                    a.name
                ),
            }
            for e in a.replays {
                assert!(
                    (*e as usize) < a.min_args,
                    "{}: replayed argument End({e}) outside min_args",
                    a.name
                );
                assert!(
                    a.list_args.iter().any(|(x, _)| x == e),
                    "{}: replayed argument End({e}) is not one of its list arguments",
                    a.name
                );
                assert!(
                    !a.streaming,
                    "{}: an argument it replays cannot be walked once, retaining nothing",
                    a.name
                );
            }
            // **M2.3g.** The two axes must not contradict each other: a
            // result that *is* the argument has to be a list when the
            // argument is, and a result that merely *contains* one must
            // not claim to be a list itself.
            if matches!(a.alias, Alias::ResultContainsSuffixOfArg(_)) {
                assert!(
                    !a.produces.is_direct_list(),
                    "{}: the result contains a list but is claimed to be one",
                    a.name
                );
            }
        }
    }

    /// End-indexing is what makes an entry survive a leading dictionary.
    #[test]
    fn end_indices_resolve_against_the_call_s_own_argument_count() {
        let a = axiom("$base$GHC.List$elem").unwrap();
        // elem x xs — two value arguments, the list last.
        assert_eq!(a.spine_of(1, 2), Some(ArgSpine::PrefixDataDependent));
        assert_eq!(a.spine_of(0, 2), None);
        // Eq dict, x, xs — three, and the list is still last.
        assert_eq!(a.spine_of(2, 3), Some(ArgSpine::PrefixDataDependent));
        assert_eq!(a.spine_of(1, 3), None);
    }

    /// (++) is the entry that carries both an incremental left argument and
    /// a right argument the result aliases.
    #[test]
    fn append_shares_its_right_argument_with_the_result() {
        let a = axiom("$base$GHC.Base$++").unwrap();
        assert_eq!(a.spine_of(0, 2), Some(ArgSpine::Incremental));
        assert_eq!(a.spine_of(1, 2), Some(ArgSpine::NoDemand));
        assert!(a.aliases_spine(1, 2));
        assert!(!a.aliases_spine(0, 2));
    }
}
