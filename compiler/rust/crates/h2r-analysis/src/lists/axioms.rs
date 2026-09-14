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

/// Does the result share cells with an argument?
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Alias {
    /// Every cell of the result is freshly allocated.
    NoAlias,
    /// The result's own tail *is* this argument (end-indexed): the spine
    /// survives inside the result and is shared with it.
    ResultIsTailOfArg(u8),
    /// The result contains a suffix of this argument (end-indexed).
    ResultSharesArg(u8),
}

/// How the *result* list is produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Produces {
    /// The call does not return a list.
    NotAList,
    /// One cell at a time, as the consumer asks for it.
    Incremental,
    /// Nothing is returned until the whole input has been consumed.
    WholeBeforeFirstCell,
    /// The result *is* (a suffix of) the input: no cell is built.
    SameAsInput,
    /// Infinite, or bounded only by the consumer.
    Unbounded,
}

impl Produces {
    pub fn is_list(self) -> bool {
        !matches!(self, Produces::NotAList)
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
    /// What the call forces of the *elements* it reaches.
    pub head: HeadDemand,
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

    /// Does the result alias the argument at `idx`?
    pub fn aliases(&self, idx: usize, n: usize) -> bool {
        match self.alias {
            Alias::NoAlias => false,
            Alias::ResultIsTailOfArg(e) | Alias::ResultSharesArg(e) => end_index(e, n) == Some(idx),
        }
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
    head: HeadDemand,
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
        head,
        alias,
        short_circuit,
        streaming,
        produces,
        note,
    }
}

use ArgSpine::{Incremental, NoDemand, PrefixDataDependent, PrefixFromArg, Whole};
use HeadDemand as H;

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
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "static data unpacked one cell at a time; no list argument",
    ),
    ax(
        "$ghc-prim$GHC.CString$unpackCStringUtf8#",
        "L-AX-UNPACK-CSTRING-UTF8",
        1,
        &[],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "as unpackCString#, decoding UTF-8",
    ),
    ax(
        "$ghc-prim$GHC.CString$unpackAppendCString#",
        "L-AX-UNPACK-APPEND-CSTRING",
        2,
        &[(0, NoDemand)],
        H::None,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::Incremental,
        "literal ++ rest: the argument becomes the result's tail, untouched",
    ),
    ax(
        "$ghc-prim$GHC.CString$unpackAppendCStringUtf8#",
        "L-AX-UNPACK-APPEND-CSTRING-UTF8",
        2,
        &[(0, NoDemand)],
        H::None,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::Incremental,
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
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "one input cell per output cell, on demand; elements are not forced",
    ),
    ax(
        "$base$GHC.Base$++",
        "L-AX-APPEND",
        2,
        &[(1, Incremental), (0, NoDemand)],
        H::None,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::Incremental,
        "the left spine is copied on demand; the right argument IS the result's tail",
    ),
    ax(
        "$base$GHC.Base$++_$s++",
        "L-AX-APPEND-SPEC",
        2,
        &[(1, Incremental), (0, NoDemand)],
        H::None,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::Incremental,
        "a type-specialised copy of (++); same semantics",
    ),
    ax(
        "$base$GHC.Base$eqString",
        "L-AX-EQSTRING",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "compares cell by cell and stops at the first difference",
    ),
    ax(
        "$base$GHC.Base$foldr",
        "L-AX-FOLDR",
        3,
        &[(0, Incremental)],
        H::None,
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
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "one cell; the element is returned unforced",
    ),
    ax(
        "$base$GHC.List$tail",
        "L-AX-TAIL",
        1,
        &[(0, PrefixDataDependent)],
        H::None,
        Alias::ResultIsTailOfArg(0),
        true,
        true,
        Produces::SameAsInput,
        "one cell; the result IS the argument's tail",
    ),
    ax(
        "$base$GHC.List$last",
        "L-AX-LAST",
        1,
        &[(0, Whole)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "walks every cell; the element is returned unforced",
    ),
    ax(
        "$base$GHC.List$length",
        "L-AX-LENGTH",
        1,
        &[(0, Whole)],
        H::None,
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
        H::None,
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
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::WholeBeforeFirstCell,
        "nothing is returned until the whole input has been consumed",
    ),
    ax(
        "$base$GHC.List$reverse1",
        "L-AX-REVERSE1",
        2,
        &[(1, Whole), (0, NoDemand)],
        H::None,
        Alias::ResultIsTailOfArg(0),
        false,
        true,
        Produces::WholeBeforeFirstCell,
        "reverse's accumulating loop rev xs acc: acc becomes the result's tail",
    ),
    ax(
        "$base$GHC.List$head1",
        "L-AX-BADHEAD",
        1,
        &[],
        H::None,
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
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "base's `init' :: t -> [t] -> [t]`, the local worker of `init` floated out:          one cell of the list argument per output cell, one cell ahead, elements          copied unforced, result freshly built",
    ),
    ax(
        "$base$GHC.List$flipSeq",
        "L-AX-FLIPSEQ",
        2,
        &[(1, NoDemand), (0, PrefixDataDependent)],
        H::None,
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
        H::None,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::Incremental,
        "a specialised worker of base's local `splitAt' :: Int -> [a] -> ([a],[a])`:          count first, list second, and the second component is a suffix of the          input. The dump's types corroborate the order (Int#, then the list)",
    ),
    ax(
        "$base$Data.OldList$dropLength",
        "L-AX-DROPLENGTH",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::None,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::SameAsInput,
        "base's `dropLength :: [a] -> [b] -> [b]`, used by isSuffixOf: walks both          spines in lockstep until the shorter runs out and returns a SUFFIX of the          second argument, forcing no element",
    ),
    ax(
        "$base$Data.OldList$dropLengthMaybe",
        "L-AX-DROPLENGTHMAYBE",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::None,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::NotAList,
        "as dropLength, returning `Maybe [b]`: the suffix of the second argument          survives inside the `Just`, so the alias holds although the result is not          itself a list",
    ),
    ax(
        "$base$Data.OldList$prependToAll",
        "L-AX-PREPENDTOALL",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "base's `prependToAll sep (x:xs) = sep : x : prependToAll sep xs`, the          helper behind intersperse: separator first, list second, one input cell          per two output cells, on demand",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fEqList_$s$c==1",
        "L-AX-EQLIST-SPEC",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a SPECIALISE'd copy of ghc-prim's `instance Eq a => Eq [a]`: walks both          spines in lockstep and stops at the first difference, forcing each element          pair it reaches. Same semantics as eqString, which is this instance at Char",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fEqList_$s$c==2",
        "L-AX-EQLIST-SPEC2",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a second SPECIALISE'd copy of the same instance, at another element type",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fOrdList_$s$ccompare",
        "L-AX-COMPARELIST-SPEC",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a SPECIALISE'd copy of ghc-prim's `instance Ord a => Ord [a]` compare:          walks both spines in lockstep and stops at the first element pair that          does not compare EQ",
    ),
    ax(
        "$ghc-prim$GHC.Classes$$fOrdList_$s$ccompare1",
        "L-AX-COMPARELIST-SPEC1",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "a second SPECIALISE'd copy of the same instance method",
    ),
    ax(
        "$base$GHC.List$filter",
        "L-AX-FILTER",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "the predicate forces what it forces; cells are copied on demand",
    ),
    ax(
        "$base$GHC.List$takeWhile",
        "L-AX-TAKEWHILE",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::Incremental,
        "stops at the first element the predicate rejects",
    ),
    ax(
        "$base$GHC.List$dropWhile",
        "L-AX-DROPWHILE",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::SameAsInput,
        "the result is a suffix of the argument: no cell is built",
    ),
    ax(
        "$base$GHC.List$span",
        "L-AX-SPAN",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::Incremental,
        "the second component is a suffix of the argument",
    ),
    ax(
        "$base$GHC.List$$wspan",
        "L-AX-WSPAN",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::Incremental,
        "span's worker, returning an unboxed pair; the second component is a suffix",
    ),
    ax(
        "$base$GHC.List$break",
        "L-AX-BREAK",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::Incremental,
        "span with the predicate negated",
    ),
    ax(
        "$base$GHC.List$$wbreak",
        "L-AX-WBREAK",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::Incremental,
        "break's worker, returning an unboxed pair",
    ),
    ax(
        "$base$GHC.List$take",
        "L-AX-TAKE",
        2,
        &[(0, PrefixFromArg(1))],
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::Incremental,
        "at most n cells; a literal n gives a Known bound",
    ),
    ax(
        "$base$GHC.List$$wunsafeTake",
        "L-AX-WUNSAFETAKE",
        2,
        &[(0, PrefixFromArg(1))],
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::Incremental,
        "take's worker on an unboxed count, called when n is known positive",
    ),
    ax(
        "$base$GHC.List$drop",
        "L-AX-DROP",
        2,
        &[(0, PrefixFromArg(1))],
        H::None,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::SameAsInput,
        "walks n cells and returns the suffix: the result aliases the input",
    ),
    ax(
        "$base$GHC.List$splitAt",
        "L-AX-SPLITAT",
        2,
        &[(0, PrefixFromArg(1))],
        H::None,
        Alias::ResultSharesArg(0),
        true,
        true,
        Produces::Incremental,
        "the second component is a suffix of the input",
    ),
    ax(
        "$base$GHC.List$!!",
        "L-AX-INDEX",
        2,
        &[(1, PrefixFromArg(0))],
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "walks n cells; the element is returned unforced",
    ),
    ax(
        "$base$GHC.List$$w!!",
        "L-AX-WINDEX",
        2,
        &[(1, PrefixFromArg(0))],
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "(!!)'s worker on an unboxed index",
    ),
    ax(
        "$base$GHC.List$elem",
        "L-AX-ELEM",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first match",
    ),
    ax(
        "$base$GHC.List$notElem",
        "L-AX-NOTELEM",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first match",
    ),
    ax(
        "$base$GHC.List$lookup",
        "L-AX-LOOKUP",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first matching key; forces the keys it compares",
    ),
    ax(
        "$base$GHC.List$zip",
        "L-AX-ZIP",
        2,
        &[(1, Incremental), (0, Incremental)],
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::Incremental,
        "stops at the shorter spine; elements are not forced",
    ),
    ax(
        "$base$GHC.List$zipWith",
        "L-AX-ZIPWITH",
        3,
        &[(1, Incremental), (0, Incremental)],
        H::None,
        Alias::NoAlias,
        true,
        true,
        Produces::Incremental,
        "stops at the shorter spine",
    ),
    ax(
        "$base$GHC.List$unzip",
        "L-AX-UNZIP",
        1,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::Incremental,
        "both result spines are driven by the one input spine",
    ),
    ax(
        "$base$GHC.List$concat",
        "L-AX-CONCAT",
        1,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "concat = foldr (++) []: every inner list is a LEFT operand of (++) and is          copied, and [[a]] spine cells can never be [a] result cells — no aliasing",
    ),
    ax(
        "$base$GHC.List$concatMap",
        "L-AX-CONCATMAP",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "one input cell per exhausted inner list",
    ),
    ax(
        "$base$GHC.List$foldl",
        "L-AX-FOLDL",
        3,
        &[(0, Whole)],
        H::None,
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
        H::None,
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
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first False",
    ),
    ax(
        "$base$GHC.List$or",
        "L-AX-OR",
        1,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first True",
    ),
    ax(
        "$base$GHC.List$any",
        "L-AX-ANY",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first element the predicate accepts",
    ),
    ax(
        "$base$GHC.List$all",
        "L-AX-ALL",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first element the predicate rejects",
    ),
    ax(
        "$base$GHC.List$replicate",
        "L-AX-REPLICATE",
        2,
        &[],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "produces n cells on demand; no list argument",
    ),
    ax(
        "$base$GHC.List$iterate",
        "L-AX-ITERATE",
        2,
        &[],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Unbounded,
        "infinite; bounded only by its consumer",
    ),
    ax(
        "$base$GHC.List$repeat",
        "L-AX-REPEAT",
        1,
        &[],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Unbounded,
        "infinite; bounded only by its consumer",
    ),
    ax(
        "$base$GHC.List$cycle",
        "L-AX-CYCLE",
        1,
        &[(0, Whole)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::Unbounded,
        "infinite; the argument is retained and replayed",
    ),
    ax(
        "$ghc-prim$GHC.Magic$lazy",
        "L-AX-LAZY",
        1,
        &[(0, NoDemand)],
        H::None,
        Alias::ResultSharesArg(0),
        false,
        true,
        Produces::SameAsInput,
        "the identity with a demand-analyser annotation: the result IS the argument",
    ),
    ax(
        "$base$Data.Maybe$mapMaybe",
        "L-AX-MAPMAYBE",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
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
        H::All,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "splits on demand; each line's characters are forced to find the newline.          Each line is built by `break`'s first component, which is fresh, and a          [String] spine cell is never a String cell — no aliasing",
    ),
    ax(
        "$base$Data.OldList$unlines",
        "L-AX-UNLINES",
        1,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "one input cell per exhausted line",
    ),
    ax(
        "$base$Data.OldList$words",
        "L-AX-WORDS",
        1,
        &[(0, Incremental)],
        H::All,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "splits on demand; characters are forced to find the separators",
    ),
    ax(
        "$base$Data.OldList$unwords",
        "L-AX-UNWORDS",
        1,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "one input cell per exhausted word",
    ),
    ax(
        "$base$Data.OldList$intercalate",
        "L-AX-INTERCALATE",
        2,
        &[(0, Incremental), (1, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "the separator is replayed between elements, so it is retained",
    ),
    ax(
        "$base$Data.OldList$isPrefixOf",
        "L-AX-ISPREFIXOF",
        2,
        &[(1, PrefixDataDependent), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first difference or at the end of the left argument",
    ),
    ax(
        "$base$Data.OldList$isSuffixOf",
        "L-AX-ISSUFFIXOF",
        2,
        &[(1, Whole), (0, Whole)],
        H::Prefix,
        Alias::NoAlias,
        false,
        false,
        Produces::NotAList,
        "both spines are walked to the end before anything is compared",
    ),
    ax(
        "$base$Data.OldList$isInfixOf",
        "L-AX-ISINFIXOF",
        2,
        &[(1, Whole), (0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        false,
        Produces::NotAList,
        "the needle is retained and replayed against every position of the haystack",
    ),
    ax(
        "$base$Data.OldList$nub",
        "L-AX-NUB",
        1,
        &[(0, Incremental)],
        H::All,
        Alias::NoAlias,
        false,
        false,
        Produces::Incremental,
        "every element accepted so far is retained and compared against",
    ),
    ax(
        "$base$Data.OldList$nubBy",
        "L-AX-NUBBY",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::Incremental,
        "every element accepted so far is retained and compared against",
    ),
    ax(
        "$base$Data.OldList$sort",
        "L-AX-SORT",
        1,
        &[(0, Whole)],
        H::All,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "the whole spine is consumed and the elements compared before the first cell",
    ),
    ax(
        "$base$Data.OldList$sortBy",
        "L-AX-SORTBY",
        2,
        &[(0, Whole)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "the whole spine is consumed before the first cell; the comparator forces what it forces",
    ),
    ax(
        "$base$Data.OldList$sortOn",
        "L-AX-SORTON",
        2,
        &[(0, Whole)],
        H::All,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "the key of every element is computed before the first cell",
    ),
    ax(
        "$base$Data.OldList$group",
        "L-AX-GROUP",
        1,
        &[(0, Incremental)],
        H::All,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "one group at a time, on demand",
    ),
    ax(
        "$base$Data.OldList$groupBy",
        "L-AX-GROUPBY",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "one group at a time, on demand",
    ),
    ax(
        "$base$Data.OldList$find",
        "L-AX-FIND-OLDLIST",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "stops at the first element the predicate accepts",
    ),
    //--------------------------------------------------------------------
    // Data.Foldable / Data.Traversable, at the list instance.
    //--------------------------------------------------------------------
    ax(
        "$base$Data.Foldable$elem",
        "L-AX-FOLDABLE-ELEM",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first match",
    ),
    ax(
        "$base$Data.Foldable$notElem",
        "L-AX-FOLDABLE-NOTELEM",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first match",
    ),
    ax(
        "$base$Data.Foldable$find",
        "L-AX-FOLDABLE-FIND",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first element the predicate accepts",
    ),
    ax(
        "$base$Data.Foldable$any",
        "L-AX-FOLDABLE-ANY",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first acceptance",
    ),
    ax(
        "$base$Data.Foldable$all",
        "L-AX-FOLDABLE-ALL",
        2,
        &[(0, PrefixDataDependent)],
        H::Prefix,
        Alias::NoAlias,
        true,
        true,
        Produces::NotAList,
        "at the list instance: stops at the first rejection",
    ),
    ax(
        "$base$Data.Foldable$and",
        "L-AX-FOLDABLE-AND",
        1,
        &[(0, PrefixDataDependent)],
        H::Prefix,
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
        H::Prefix,
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
        H::None,
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
        H::None,
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
        H::All,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell and every element",
    ),
    ax(
        "$base$Data.Foldable$maximum",
        "L-AX-FOLDABLE-MAXIMUM",
        1,
        &[(0, Whole)],
        H::All,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell and every element",
    ),
    ax(
        "$base$Data.Foldable$minimum",
        "L-AX-FOLDABLE-MINIMUM",
        1,
        &[(0, Whole)],
        H::All,
        Alias::NoAlias,
        false,
        true,
        Produces::NotAList,
        "at the list instance: every cell and every element",
    ),
    ax(
        "$base$Data.Foldable$concat",
        "L-AX-FOLDABLE-CONCAT",
        1,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "at the list instance, as GHC.List.concat: everything is copied, and the          argument's spine is one type constructor further out than the result's",
    ),
    ax(
        "$base$Data.Foldable$concatMap",
        "L-AX-FOLDABLE-CONCATMAP",
        2,
        &[(0, Incremental)],
        H::None,
        Alias::NoAlias,
        false,
        true,
        Produces::Incremental,
        "at the list instance: one input cell per exhausted inner list",
    ),
    ax(
        "$base$Data.Foldable$toList",
        "L-AX-FOLDABLE-TOLIST",
        1,
        &[(0, NoDemand)],
        H::None,
        Alias::ResultSharesArg(0),
        false,
        true,
        Produces::SameAsInput,
        "at the list instance: the identity",
    ),
    ax(
        "$base$Data.Foldable$foldr",
        "L-AX-FOLDABLE-FOLDR",
        3,
        &[(0, Incremental)],
        H::None,
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
        H::None,
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
        H::None,
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
        H::None,
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
        H::None,
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
        H::None,
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
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "at the list instance: the whole spine is consumed before the result exists",
    ),
    ax(
        "$base$Data.Traversable$forM",
        "L-AX-FORM",
        2,
        &[(1, Whole)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "mapM with the arguments flipped",
    ),
    ax(
        "$base$Data.Traversable$traverse",
        "L-AX-TRAVERSE",
        2,
        &[(0, Whole)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "at the list instance: the whole spine is consumed before the result exists",
    ),
    ax(
        "$base$Data.Traversable$sequence",
        "L-AX-SEQUENCE",
        1,
        &[(0, Whole)],
        H::None,
        Alias::NoAlias,
        false,
        false,
        Produces::WholeBeforeFirstCell,
        "at the list instance: the whole spine is consumed before the result exists",
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
                Alias::ResultIsTailOfArg(e) | Alias::ResultSharesArg(e) => assert!(
                    (e as usize) < a.min_args,
                    "{}: alias argument outside min_args",
                    a.name
                ),
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
        assert!(a.aliases(1, 2));
        assert!(!a.aliases(0, 2));
    }
}
