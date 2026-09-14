//! Which list flows are **text**, and what does the program do with them?
//!
//! This is M2.3d. It does not re-walk the Core: its population is
//! [M2.3c's list flows](crate::lists), *selected* and *refined*. Every
//! spine fact it needs — how much of the spine is demanded, whether a tail
//! is shared, whether the flow is stored, whether it escapes — is
//! inherited, with the list rule id cited, and never recomputed. What is
//! added here is text-specific: is the element a `Char`, is every consumer
//! a text-shaped one, is the value built by appending literals, is the
//! whole text needed or only a prefix, and does anything observe an
//! individual character.
//!
//! # The honesty caveat that governs this milestone
//!
//! **The dump carries pretty-printed type strings, not `TyCon` identity.**
//! Recognising `[Char]` from a rendered type — `[Char]`, `String`,
//! `[GHC.Types.Char]`, a synonym GHC happened to print as `String`, a type
//! variable instantiated somewhere this module cannot see — is evidence
//! *from a rendered type*: **level 6, textual type comparison,
//! corroboration**, exactly like M2.1's alpha-normalised type comparison.
//! It is not `TyConApp [] [Char]` with a stable `TyCon`.
//!
//! It is still far better than looking for `++`, and it is far better
//! still when a structural fact agrees with it, which is why every
//! selection records *how* `Char` was established
//! ([`ElementTypeEvidence`]) and why the structural corroborations
//! ([`X2_UNPACK_PRODUCER`], [`X3_CHAR_LITERAL_HEAD`],
//! [`X4_CHAR_SCRUTINY`], [`X5_AXIOM_FIXES_CHAR`]) are recorded separately
//! from the type reading ([`X0_ELEM_TYPE`], [`X1_LIST_TYPE`]).
//!
//! Where a flow's element type is a **type variable** or cannot be read at
//! all, the flow is [`Selection::ElementTypeUnknown`] — never assumed to be
//! text.
//!
//! *For the next plugin-format bump: expose structured types —
//! `TyConApp` with a stable `TyCon` identity — so that "the element is
//! `Char`" becomes a structural (level 2/4) fact instead of a string
//! comparison, and this whole caveat goes away.*
//!
//! # The population
//!
//! A list flow is selected when **either**
//!
//! * its element type, as GHC rendered it, reads as `Char`
//!   ([`X0_ELEM_TYPE`] on the `(:)` alternative's head binder,
//!   [`X1_LIST_TYPE`] on the flow's own binder) — level 6; **or**
//! * a fact that does not read a type string says the element is a `Char`:
//!   the producer is a call in the `unpackCString#` family
//!   ([`X2_UNPACK_PRODUCER`], level 2, and independent of what any type
//!   string says), a cell's element is a `Char` literal
//!   ([`X3_CHAR_LITERAL_HEAD`], level 2), an element is scrutinised as a
//!   character ([`X4_CHAR_SCRUTINY`], level 1/2), or a consumer's signature
//!   fixes the argument to `[Char]` ([`X5_AXIOM_FIXES_CHAR`], level 5).
//!
//! Each of those four stands on its own — none of them needs the rendered
//! type to agree — which is why a flow can be selected with no readable
//! type at all, and why [`ElementTypeEvidence`] records whether the two
//! kinds of evidence agreed.
//!
//! Everything else is either a flow whose element type reads as something
//! that is not `Char` (not text) or one whose element type could not be
//! read (element-type-unknown). Those three buckets partition M2.3c's
//! flows, and the accounting asserts it.
//!
//! # The text-head table
//!
//! [`TEXT_HEADS`] is a second deliberate name-keyed table, in the same
//! spirit as [the axiom table](crate::lists::axioms) and with the same
//! evidence level (**5, library axiom**), and subject to the same hard
//! rule: it is only ever consulted for an **imported** head, which is what
//! M2.3c has already established for every [`ConsumerKind::Axiom`] and
//! [`ConsumerKind::NoAxiom`] consumer. It is keyed on `(module, occ)`
//! rather than on the full stable name because a package's unit id carries
//! a build hash (`regex-tdfa-1.3.2.6-4dff8751…`) that is not stable across
//! dumps.
//!
//! It does one thing the axiom table does not: it gives a demand class to
//! heads the axiom table has **no entry for** (`hPutStr2`, `showLitString`,
//! the specialised list `==`, regex-tdfa's `compile`). A flow whose only
//! unresolved consumer is such a head is `Unknown` in M2.3c and decided
//! here. That is the one place this milestone is *more* decided than the
//! last, it is an asserted claim rather than a derived one, and it is
//! marked as such on every flow that uses it.
//!
//! # Facts, then an advisory
//!
//! [`TextShape`], [`Literal`]/[`AppendChain`], the per-consumer
//! [`ConsumerClass`], [`TextFlow::char_semantics_required`], and the
//! inherited `SharedTails`/`PrefixConsumers`/`Storage`/`Escapes` are
//! recorded independently. [`Advisory`] is a function of them and is
//! **advisory**: nothing here decides that anything is a Rust `String`.
//! `char_semantics_required` in particular does not preclude `String`; it
//! says a future representation must preserve character semantics
//! explicitly rather than treating the value as a bag of bytes.
//!
//! # Evidence hierarchy
//!
//! Strongest first: 1 lexical binder identity, 2 structural shape, 3
//! def-use dataflow, 4 GHC type compatibility, 5 library axiom, **6
//! textual type comparison (corroboration — where selection by type
//! lives)**, 7 names (diagnostics).

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{AltCon, BinderId, Edge, Expr, ExprId, Module};
use serde::Serialize;

use crate::callee::split_stable_name;
use crate::flow::Evidence;
use crate::lists::{
    ConsumerKind, HeadDemand, ListCensus, ListConsumer, ListFlow, ProducerKind, Recursion, Reuse,
    SpineDemand, Storage, TailFate,
};
use crate::scope::Scope;
use crate::shape::value_args;

//------------------------------------------------------------------------------
// Rule ids
//------------------------------------------------------------------------------

/// **Selection.** The `(:)` alternative's head binder, whose type GHC
/// rendered as `Char`. Evidence: **textual type comparison (6)** over the
/// lexical identity of the binder (1) that M2.3c already established.
pub const X0_ELEM_TYPE: &str = "X0-ELEM-TYPE";
/// **Selection.** The flow's own binder, whose type GHC rendered as a list
/// of `Char` (`[Char]`, `String`, `FilePath`, `[GHC.Types.Char]`).
/// Evidence: **textual type comparison (6)**.
pub const X1_LIST_TYPE: &str = "X1-LIST-TYPE";
/// **Selection, structural.** The producer is a saturated call to a member
/// of the `unpackCString#` family, whose result type is `[Char]` by the
/// definition of the primitive — regardless of what the rendered type of
/// any binder says. Evidence: structural shape (2) over the library axiom
/// (5) that made it a producer at all.
pub const X2_UNPACK_PRODUCER: &str = "X2-UNPACK-PRODUCER";
/// **Corroboration, structural.** A cell of this chain has a `Char`
/// literal (or a saturated `C#`) as its element. Evidence: structural
/// shape (2).
pub const X3_CHAR_LITERAL_HEAD: &str = "X3-CHAR-LITERAL-HEAD";
/// **Corroboration, structural.** The `(:)` alternative's head binder is
/// scrutinised by a `case` whose alternatives are `C#` or `Char`
/// literals. Evidence: lexical binder identity (1) over structural shape
/// (2).
pub const X4_CHAR_SCRUTINY: &str = "X4-CHAR-SCRUTINY";
/// **Corroboration, axiom.** A consumer whose signature fixes this
/// argument to `[Char]` (`eqString`, `unpackAppendCString#`, `lines`,
/// `words`, `showLitString`, `hPutStr`). Evidence: **library axiom (5)**.
pub const X5_AXIOM_FIXES_CHAR: &str = "X5-AXIOM-FIXES-CHAR";
/// The flow's element type is a type variable, or no binder of the flow
/// carried a readable type: the flow is **not** assumed to be text.
/// Evidence: the refusal.
pub const X6_ELEM_TYPE_UNKNOWN: &str = "X6-ELEM-TYPE-UNKNOWN";
/// The flow's element type reads as something that is not `Char`.
/// Evidence: textual type comparison (6).
pub const X7_ELEM_TYPE_NOT_CHAR: &str = "X7-ELEM-TYPE-NOT-CHAR";

/// **Fact.** Every consumer of the flow is a text-shaped consumer: an
/// entry of [`TEXT_HEADS`]. Evidence: library axiom (5) over the consumer
/// classification M2.3c proved (`L8-AXIOM`, `L9-NO-AXIOM`).
pub const X8_TEXT_ONLY: &str = "X8-TEXT-ONLY";
/// **Fact.** At least one consumer is a generic list combinator or a
/// structural `case` on the cells. Evidence: 5 over 2.
pub const X9_MIXED: &str = "X9-MIXED";
/// **Fact.** A consumer is an imported head neither table knows, or the
/// flow escaped: what is done with the text is not visible. Evidence: the
/// refusal.
pub const X10_SHAPE_UNKNOWN: &str = "X10-SHAPE-UNKNOWN";
/// **Fact.** Nothing observes the flow as text or as a list at all.
/// Evidence: def-use (3), inherited from `L12-NEVER-OBSERVED`.
pub const X11_UNOBSERVED: &str = "X11-UNOBSERVED";

/// **Fact.** The text is constructed from static data: the producer is an
/// `unpackCString#`-family call. Evidence: structural shape (2).
pub const X12_LITERAL: &str = "X12-LITERAL";
/// **Fact.** The producer is an append (`++`, `unpackAppendCString#`), and
/// the chain of appends feeding it has this many operand segments.
/// Evidence: structural shape (2) over lexical binder identity (1) where a
/// segment is reached through a let-bound binder.
pub const X13_APPEND_CHAIN: &str = "X13-APPEND-CHAIN";
/// **Fact.** This flow is an operand of an append chain. Evidence: 5 (the
/// axiom that says the head is an append) over 2.
pub const X14_APPEND_OPERAND: &str = "X14-APPEND-OPERAND";

/// **Fact.** The consumer needs the whole text: output, an equality or
/// ordering comparison, `length`, `reverse`, a hash or map key, a regex
/// compile. Evidence: the consumer's own `SpineDemand` (`L8-AXIOM`,
/// `L4-LOOP-WHOLE`), or [`TEXT_HEADS`] (5) where the axiom table is silent.
pub const X15_COMPLETE: &str = "X15-COMPLETE-OUTPUT";
/// **Fact.** The consumer needs a prefix: `isPrefixOf`, `take`, `head`,
/// `null`, `takeWhile`, a `case` on the first cell. Evidence: as above.
pub const X16_PREFIX: &str = "X16-PREFIX";
/// **Fact.** The consumer streams: the left side of `++`, a `map` over the
/// characters, streaming output. Evidence: as above.
pub const X17_INCREMENTAL: &str = "X17-INCREMENTAL";
/// **Fact.** The consumer demands nothing of the spine: the value is
/// stored, passed on, or becomes the tail of another value. Evidence: as
/// above.
pub const X18_RETAINED: &str = "X18-RETAINED";
/// **Fact.** Neither table says what this consumer does. Evidence: the
/// refusal.
pub const X19_CLASS_UNKNOWN: &str = "X19-CLASS-UNKNOWN";

/// **Fact.** The flow exposes an individual `Char`, or performs an
/// operation whose meaning depends on characters rather than on encoded
/// bytes. This does **not** preclude a `String` representation; it says a
/// future representation must preserve character semantics explicitly.
/// Evidence: whichever reason fired (see [`TextFlow::char_reasons`]).
pub const X20_CHAR_SEMANTICS: &str = "X20-CHAR-SEMANTICS-REQUIRED";

/// **Selection, structural.** An append (`++`, `unpackAppendCString#`)
/// does not change the element type: the flow the call produces and each
/// of its list operands have the same elements. So a `[Char]` established
/// anywhere in a connected component of that relation establishes it
/// everywhere in the component. Evidence: **library axiom (5)** that the
/// head is an append, over structural shape (2); the component is closed
/// to a fixpoint. A component containing a flow whose rendered element
/// type is concretely *not* `Char` is a contradiction and is refused
/// rather than propagated into.
pub const X24_APPEND_SAME_ELEM: &str = "X24-APPEND-SAME-ELEM";

/// **Inherited.** A tail of this spine survives in a second place
/// (`L14-SHARED-TAIL`). Not recomputed.
pub const X21_SHARED_TAIL: &str = "X21-SHARED-TAIL";
/// **Inherited.** The flow's storage fact (`L10-STORED`, `L16-CAPTURED`,
/// `T6-RETURNED`). Not recomputed.
pub const X22_STORAGE: &str = "X22-STORAGE";
/// **Inherited.** The flow left what the walk follows (`L11-ESCAPE`). Not
/// recomputed.
pub const X23_ESCAPE: &str = "X23-ESCAPE";

/// **Advisory.** Text, every consumer text-shaped, only complete-output or
/// incremental consumers, no individual character observed, no shared
/// tail, no prefix consumer, a finite producer.
pub const X_ADV_STRONG: &str = "X-ADV-STRONG-STRING";
/// **Advisory.** Text, but the representation is open: a prefix consumer,
/// a shared tail, character semantics, or a mixed consumer set.
pub const X_ADV_UNDECIDED: &str = "X-ADV-TEXT-VALUE-UNDECIDED";
/// **Advisory.** Selected as text by its type, but nothing text-shaped
/// consumes it: every consumer is a generic list combinator or a
/// structural `case`.
pub const X_ADV_NOT_TEXT: &str = "X-ADV-NOT-TEXT";
/// **Advisory.** Some fact is `Unknown`.
pub const X_ADV_UNKNOWN: &str = "X-ADV-UNKNOWN";

// Machine-readable reasons.
pub const R_OPAQUE_CONSUMER: &str = "a-consumer-is-an-imported-head-neither-table-knows";
pub const R_ESCAPED_AT_CONSUMER: &str = "the-value-left-the-walk-here";
pub const R_ESCAPES: &str = "the-flow-escapes-what-the-walk-follows";
pub const R_CLASS_UNKNOWN: &str = "a-consumer-demand-class-is-unknown";
pub const R_NO_TEXT_CONSUMER: &str = "no-text-shaped-consumer";
pub const R_UNOBSERVED: &str = "nothing-observes-it";
pub const R_PREFIX_CONSUMER: &str = "a-prefix-consumer";
pub const R_SHARED_TAIL: &str = "a-tail-survives-in-a-second-place";
pub const R_CHAR_SEMANTICS: &str = "character-semantics-are-required";
pub const R_MIXED: &str = "a-generic-or-structural-consumer";
pub const R_KNOT: &str = "the-producer-is-a-value-knot";
pub const R_NO_DEMANDING_CONSUMER: &str = "no-consumer-demands-the-text";

// char_semantics_required reasons.
pub const CS_HEAD_BOUND: &str = "a-cons-alternative-binds-and-uses-the-head";
pub const CS_HEAD_FORCED: &str = "an-element-is-forced";
pub const CS_CHAR_LITERAL: &str = "a-char-literal-is-an-element";
pub const CS_CHAR_SCRUTINY: &str = "the-head-is-compared-against-a-char-literal";
pub const CS_CHAR_CONSUMER: &str = "a-consumer-exposes-individual-characters";
pub const CS_POSITION: &str = "a-consumer-depends-on-character-positions-or-count";

/// How deep an append chain may be followed before it is a bug.
const CHAIN_DEPTH: usize = 64;

//------------------------------------------------------------------------------
// The text-head table
//------------------------------------------------------------------------------

/// Which text abstraction a consumer belongs to. Diagnostic grouping over
/// the [`TEXT_HEADS`] entries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TextFamily {
    /// `++`, `unpackAppendCString#`.
    Append,
    /// `eqString`, the specialised list `==` and `compare`.
    Compare,
    /// `isPrefixOf`, `isSuffixOf`, `isInfixOf`.
    Affix,
    /// `lines`, `unlines`, `words`, `unwords`.
    LinesWords,
    /// The `show` family.
    Show,
    /// `hPutStr`, `putStr` and friends.
    Output,
    /// regex-tdfa's `compile` and the matchers.
    Regex,
    /// `elem`/`notElem` with a `Char`.
    CharSearch,
}

impl TextFamily {
    pub fn name(self) -> &'static str {
        match self {
            TextFamily::Append => "Append",
            TextFamily::Compare => "Compare",
            TextFamily::Affix => "Affix",
            TextFamily::LinesWords => "LinesWords",
            TextFamily::Show => "Show",
            TextFamily::Output => "Output",
            TextFamily::Regex => "Regex",
            TextFamily::CharSearch => "CharSearch",
        }
    }
}

/// One text-shaped head. `class_override` is `Some` only where the axiom
/// table is silent or where the *value* the consumer needs differs from
/// the spine demand: `eqString` stops at the first difference, so its spine
/// demand is a data-dependent prefix, but the whole text is the subject of
/// the comparison, which is what a representation decision turns on.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct TextHead {
    /// GHC's module of the imported head.
    pub module: &'static str,
    /// GHC's occurrence name.
    pub occ: &'static str,
    pub family: TextFamily,
    pub class_override: Option<ConsumerClass>,
    /// Does the call expose individual characters?
    pub char_exposing: bool,
    /// Does it depend on character positions or on the character count?
    pub position_semantics: bool,
    /// Does the signature fix the list argument to `[Char]`?
    pub fixes_char: bool,
    pub note: &'static str,
}

#[allow(clippy::too_many_arguments)]
const fn th(
    module: &'static str,
    occ: &'static str,
    family: TextFamily,
    class_override: Option<ConsumerClass>,
    char_exposing: bool,
    position_semantics: bool,
    fixes_char: bool,
    note: &'static str,
) -> TextHead {
    TextHead {
        module,
        occ,
        family,
        class_override,
        char_exposing,
        position_semantics,
        fixes_char,
        note,
    }
}

use ConsumerClass::{Complete, Incremental};

/// The table. Every entry is **asserted** (evidence level 5), applies only
/// to imported heads, and is keyed on `(module, occ)` — the unit id is
/// ignored because it carries a package build hash.
pub static TEXT_HEADS: &[TextHead] = &[
    // Append.
    th(
        "GHC.Base",
        "++",
        TextFamily::Append,
        None,
        false,
        false,
        false,
        "the left spine is copied on demand; the right argument IS the result's tail",
    ),
    th(
        "GHC.Base",
        "++_$s++",
        TextFamily::Append,
        None,
        false,
        false,
        false,
        "a type-specialised (++)",
    ),
    th(
        "GHC.CString",
        "unpackAppendCString#",
        TextFamily::Append,
        None,
        false,
        false,
        true,
        "literal ++ rest, and the rest is [Char] by the primitive's type",
    ),
    th(
        "GHC.CString",
        "unpackAppendCStringUtf8#",
        TextFamily::Append,
        None,
        false,
        false,
        true,
        "as unpackAppendCString#, decoding UTF-8",
    ),
    // Compare.
    th(
        "GHC.Base",
        "eqString",
        TextFamily::Compare,
        Some(Complete),
        false,
        false,
        true,
        "String -> String -> Bool: the whole text is the subject, though it stops at the first difference",
    ),
    th(
        "GHC.Classes",
        "$fEqList_$s$c==",
        TextFamily::Compare,
        Some(Complete),
        true,
        false,
        false,
        "the specialised list (==)",
    ),
    th(
        "GHC.Classes",
        "$fEqList_$s$c==1",
        TextFamily::Compare,
        Some(Complete),
        true,
        false,
        false,
        "the specialised list (==)",
    ),
    th(
        "GHC.Classes",
        "$fEqList_$s$c==2",
        TextFamily::Compare,
        Some(Complete),
        true,
        false,
        false,
        "the specialised list (==)",
    ),
    th(
        "GHC.Classes",
        "$fOrdList_$s$ccompare",
        TextFamily::Compare,
        Some(Complete),
        true,
        false,
        false,
        "the specialised list compare",
    ),
    th(
        "GHC.Classes",
        "$fOrdList_$s$ccompare1",
        TextFamily::Compare,
        Some(Complete),
        true,
        false,
        false,
        "the specialised list compare",
    ),
    // Affix.
    th(
        "Data.OldList",
        "isPrefixOf",
        TextFamily::Affix,
        None,
        true,
        false,
        false,
        "stops at the first difference or at the end of the left argument",
    ),
    th(
        "Data.OldList",
        "isSuffixOf",
        TextFamily::Affix,
        None,
        true,
        true,
        false,
        "both spines are walked to the end: the character count matters",
    ),
    th(
        "Data.OldList",
        "isInfixOf",
        TextFamily::Affix,
        None,
        true,
        true,
        false,
        "the needle is replayed against every position",
    ),
    // Lines and words.
    th(
        "Data.OldList",
        "lines",
        TextFamily::LinesWords,
        None,
        true,
        false,
        true,
        "String -> [String]: characters are forced to find the newlines",
    ),
    th(
        "Data.OldList",
        "words",
        TextFamily::LinesWords,
        None,
        true,
        false,
        true,
        "String -> [String]: characters are forced to find the separators",
    ),
    th(
        "Data.OldList",
        "unlines",
        TextFamily::LinesWords,
        None,
        true,
        false,
        false,
        "[String] -> String",
    ),
    th(
        "Data.OldList",
        "unwords",
        TextFamily::LinesWords,
        None,
        true,
        false,
        false,
        "[String] -> String",
    ),
    // Show.
    th(
        "GHC.Show",
        "showLitString",
        TextFamily::Show,
        Some(Complete),
        true,
        false,
        true,
        "String -> ShowS: every character is escaped, so every character is read",
    ),
    th(
        "GHC.Show",
        "showLitChar",
        TextFamily::Show,
        Some(Complete),
        true,
        false,
        true,
        "Char -> ShowS, with the rest of the string as its continuation",
    ),
    th(
        "GHC.Show",
        "showString",
        TextFamily::Show,
        Some(Incremental),
        false,
        false,
        true,
        "String -> ShowS: (++) under another name",
    ),
    th(
        "GHC.Show",
        "$fShowChar_$cshowList",
        TextFamily::Show,
        Some(Complete),
        true,
        false,
        true,
        "showList at Char: the [Char] instance",
    ),
    // Output.
    th(
        "GHC.IO.Handle.Text",
        "hPutStr",
        TextFamily::Output,
        Some(Complete),
        false,
        false,
        true,
        "Handle -> String -> IO (): the whole text is written",
    ),
    th(
        "GHC.IO.Handle.Text",
        "hPutStr2",
        TextFamily::Output,
        Some(Complete),
        false,
        false,
        true,
        "the worker hPutStr is optimised into",
    ),
    th(
        "GHC.IO.Handle.Text",
        "hPutStrLn",
        TextFamily::Output,
        Some(Complete),
        false,
        false,
        true,
        "as hPutStr, with a newline",
    ),
    th(
        "System.IO",
        "putStr",
        TextFamily::Output,
        Some(Complete),
        false,
        false,
        true,
        "the whole text is written to stdout",
    ),
    th(
        "System.IO",
        "putStrLn",
        TextFamily::Output,
        Some(Complete),
        false,
        false,
        true,
        "as putStr, with a newline",
    ),
    // Regex.
    th(
        "Text.Regex.TDFA.String",
        "compile",
        TextFamily::Regex,
        Some(Complete),
        true,
        true,
        true,
        "the whole pattern is parsed, character by character and by position",
    ),
    th(
        "Text.Regex.TDFA.NewDFA.Tester",
        "matchTest_single5",
        TextFamily::Regex,
        Some(Complete),
        true,
        true,
        false,
        "the subject is matched character by character",
    ),
    th(
        "Text.Regex.TDFA.NewDFA.Tester",
        "matchTest_multi5",
        TextFamily::Regex,
        Some(Complete),
        true,
        true,
        false,
        "the subject is matched character by character",
    ),
    // elem with a Char.
    th(
        "GHC.List",
        "elem",
        TextFamily::CharSearch,
        None,
        true,
        false,
        false,
        "is this character in the text?",
    ),
    th(
        "GHC.List",
        "notElem",
        TextFamily::CharSearch,
        None,
        true,
        false,
        false,
        "is this character absent from the text?",
    ),
    th(
        "Data.Foldable",
        "elem",
        TextFamily::CharSearch,
        None,
        true,
        false,
        false,
        "at the list instance",
    ),
    th(
        "Data.Foldable",
        "notElem",
        TextFamily::CharSearch,
        None,
        true,
        false,
        false,
        "at the list instance",
    ),
];

/// The one lookup. `name` is the GHC stable name of an **imported** head,
/// which M2.3c has already established for every axiom and no-axiom
/// consumer.
pub fn text_head(name: &str) -> Option<&'static TextHead> {
    let (_, module, occ) = split_stable_name(name)?;
    TEXT_HEADS
        .iter()
        .find(|h| h.module == module && h.occ == occ)
}

/// Generic list heads whose semantics depend on *characters* — they hand an
/// element to a function, compare elements, or split on them — recorded so
/// that `char_semantics_required` does not need the element's own type.
/// `(module, occ)`, imported heads only, evidence level 5.
static CHAR_EXPOSING: &[(&str, &str)] = &[
    ("GHC.Base", "map"),
    ("GHC.List", "filter"),
    ("GHC.List", "head"),
    ("GHC.List", "last"),
    ("GHC.List", "!!"),
    ("GHC.List", "$w!!"),
    ("GHC.List", "takeWhile"),
    ("GHC.List", "dropWhile"),
    ("GHC.List", "span"),
    ("GHC.List", "$wspan"),
    ("GHC.List", "break"),
    ("GHC.List", "$wbreak"),
    ("GHC.List", "lookup"),
    ("GHC.List", "zip"),
    ("GHC.List", "zipWith"),
    ("GHC.List", "concatMap"),
    ("Data.OldList", "find"),
    ("Data.OldList", "nub"),
    ("Data.OldList", "nubBy"),
    ("Data.OldList", "sort"),
    ("Data.OldList", "sortBy"),
    ("Data.OldList", "sortOn"),
    ("Data.OldList", "group"),
    ("Data.OldList", "groupBy"),
    ("Data.OldList", "intercalate"),
    ("Data.Maybe", "mapMaybe"),
    ("Data.Foldable", "find"),
    ("Data.Foldable", "any"),
    ("Data.Foldable", "all"),
    ("Data.Foldable", "maximum"),
    ("Data.Foldable", "minimum"),
    ("GHC.List", "any"),
    ("GHC.List", "all"),
];

/// Generic list heads whose semantics depend on the character *count* or on
/// character *positions*: a byte-oriented representation would change what
/// they mean. `(module, occ)`, imported heads only, evidence level 5.
static POSITION_SEMANTICS: &[(&str, &str)] = &[
    ("GHC.List", "length"),
    ("GHC.List", "$wlenAcc"),
    ("GHC.List", "reverse"),
    ("GHC.List", "reverse1"),
    ("GHC.List", "take"),
    ("GHC.List", "$wunsafeTake"),
    ("GHC.List", "drop"),
    ("GHC.List", "splitAt"),
    ("GHC.List", "!!"),
    ("GHC.List", "$w!!"),
    ("GHC.List", "zip"),
    ("GHC.List", "zipWith"),
    ("GHC.List", "replicate"),
    ("Data.Foldable", "length"),
];

fn in_table(t: &[(&str, &str)], name: &str) -> bool {
    match split_stable_name(name) {
        Some((_, m, o)) => t.iter().any(|(tm, to)| *tm == m && *to == o),
        None => false,
    }
}

/// The `unpackCString#` family: producers of `[Char]` from static data.
/// The occurrence name is matched, the module is `GHC.CString`.
pub fn is_unpack_head(name: &str) -> bool {
    matches!(
        split_stable_name(name),
        Some((_, "GHC.CString", occ))
            if matches!(
                occ,
                "unpackCString#"
                    | "unpackCStringUtf8#"
                    | "unpackAppendCString#"
                    | "unpackAppendCStringUtf8#"
                    | "unpackFoldrCString#"
                    | "unpackFoldrCStringUtf8#"
                    | "unpackCStringAscii#"
            )
    )
}

/// A literal producer: an `unpackCString#`-family head that is not an
/// append (the append heads take a rest argument).
fn is_literal_head(name: &str) -> bool {
    matches!(
        split_stable_name(name),
        Some((_, "GHC.CString", occ))
            if matches!(
                occ,
                "unpackCString#" | "unpackCStringUtf8#" | "unpackCStringAscii#"
            )
    )
}

//------------------------------------------------------------------------------
// Rendered types: level 6, and labelled as such everywhere
//------------------------------------------------------------------------------

/// What a rendered type string says about an element type. Every verdict
/// here is **level 6**.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum RenderedElem {
    Char,
    Other(String),
    /// A type variable, or nothing readable.
    Unknown,
}

/// Is this rendered type a type *variable*? One lowercase-initial token,
/// which is how GHC renders one.
pub fn is_type_var(t: &str) -> bool {
    let t = t.trim();
    !t.is_empty()
        && t.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        && t.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Does this rendered type read as `Char`?
pub fn reads_as_char(t: &str) -> bool {
    matches!(t.trim(), "Char" | "GHC.Types.Char")
}

/// The element of a rendered *list* type, if it reads as one. `String` and
/// `FilePath` are the synonyms GHC prints for `[Char]`.
pub fn rendered_elem_of_list(t: &str) -> Option<String> {
    let t = t.trim();
    if matches!(t, "String" | "FilePath" | "GHC.Base.String") {
        return Some("Char".to_string());
    }
    let inner = t.strip_prefix('[')?.strip_suffix(']')?;
    // Balanced: `[a] -> [b]` also starts with '[' and ends with ']'.
    let mut depth = 0i32;
    for c in inner.chars() {
        match c {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            _ => {}
        }
    }
    if depth != 0 {
        None
    } else {
        Some(inner.to_string())
    }
}

/// The element type a flow's rendered types say it has.
fn rendered_element(f: &ListFlow) -> RenderedElem {
    let mut best = RenderedElem::Unknown;
    let mut candidates: Vec<String> = Vec::new();
    if let Some(e) = &f.elem_ty {
        candidates.push(e.clone());
    }
    if let Some(l) = &f.list_ty
        && let Some(e) = rendered_elem_of_list(l)
    {
        candidates.push(e);
    }
    for c in candidates {
        if reads_as_char(&c) {
            return RenderedElem::Char;
        }
        if !is_type_var(&c) && matches!(best, RenderedElem::Unknown) {
            best = RenderedElem::Other(c);
        }
    }
    best
}

//------------------------------------------------------------------------------
// The facts
//------------------------------------------------------------------------------

/// How `Char` was established for a selected flow.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ElementTypeEvidence {
    /// A rendered type read as `Char`, and no structural fact agreed.
    TypeStringOnly,
    /// A structural fact said `[Char]`, and no rendered type did.
    StructuralOnly,
    /// Both.
    Both,
}

impl ElementTypeEvidence {
    pub fn name(self) -> &'static str {
        match self {
            ElementTypeEvidence::TypeStringOnly => "type-string only",
            ElementTypeEvidence::StructuralOnly => "structural only",
            ElementTypeEvidence::Both => "both",
        }
    }
}

/// Which of the three buckets a list flow lands in. These partition
/// M2.3c's population.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Selection {
    Text,
    /// The element type reads as something that is not `Char`.
    NonText,
    /// The element type is a type variable or unreadable.
    ElementTypeUnknown,
}

/// Fact 1: is everything that consumes this flow text-shaped?
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TextShape {
    TextOnly,
    Mixed,
    Unknown,
    Unobserved,
}

impl TextShape {
    pub fn name(self) -> &'static str {
        match self {
            TextShape::TextOnly => "TextOnly",
            TextShape::Mixed => "Mixed",
            TextShape::Unknown => "Unknown",
            TextShape::Unobserved => "Unobserved",
        }
    }

    pub fn rule(self) -> &'static str {
        match self {
            TextShape::TextOnly => X8_TEXT_ONLY,
            TextShape::Mixed => X9_MIXED,
            TextShape::Unknown => X10_SHAPE_UNKNOWN,
            TextShape::Unobserved => X11_UNOBSERVED,
        }
    }
}

/// Fact 2: how much of the text one consumer needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ConsumerClass {
    /// The whole text is the subject: output, comparison, `length`.
    Complete,
    /// Only a prefix.
    Prefix,
    /// Streamed through.
    Incremental,
    /// Nothing is demanded of it here.
    Retained,
    Unknown,
}

impl ConsumerClass {
    pub fn name(self) -> &'static str {
        match self {
            ConsumerClass::Complete => "CompleteOutput",
            ConsumerClass::Prefix => "Prefix",
            ConsumerClass::Incremental => "Incremental",
            ConsumerClass::Retained => "Retained",
            ConsumerClass::Unknown => "Unknown",
        }
    }

    pub fn rule(self) -> &'static str {
        match self {
            ConsumerClass::Complete => X15_COMPLETE,
            ConsumerClass::Prefix => X16_PREFIX,
            ConsumerClass::Incremental => X17_INCREMENTAL,
            ConsumerClass::Retained => X18_RETAINED,
            ConsumerClass::Unknown => X19_CLASS_UNKNOWN,
        }
    }
}

/// Which side of the text/not-text line a consumer falls on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ConsumerShape {
    /// An entry of [`TEXT_HEADS`].
    Text,
    /// A list combinator that is not about text.
    Generic,
    /// A `case` on the cells.
    Structural,
    /// Stored, passed on, consed onto: demands nothing.
    Neutral,
    /// Neither table knows it, or the value left the walk.
    Opaque,
}

impl ConsumerShape {
    pub fn name(self) -> &'static str {
        match self {
            ConsumerShape::Text => "Text",
            ConsumerShape::Generic => "Generic",
            ConsumerShape::Structural => "Structural",
            ConsumerShape::Neutral => "Neutral",
            ConsumerShape::Opaque => "Opaque",
        }
    }
}

/// Fact 3: an append chain, counted in **operand segments**.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct AppendChain {
    /// How many operands the maximal chain of appends feeding this
    /// producer concatenates. `"a" ++ x` is 2.
    pub length: usize,
    /// Every operand is a string literal.
    pub all_literal: bool,
    /// Segments the walk could not look inside: a parameter, an imported
    /// call, anything that is not itself an append or a literal. They are
    /// counted in `length` as one segment each, which is a lower bound.
    pub opaque: usize,
}

/// One consumer of a text flow, refined from M2.3c's own.
#[derive(Debug, Clone, Serialize)]
pub struct TextConsumer {
    pub at: ExprId,
    pub shape: ConsumerShape,
    pub class: ConsumerClass,
    pub family: Option<TextFamily>,
    /// The imported head's stable name, where there is one.
    pub name: String,
    /// The M2.3c rule that classified the consumer, cited not recomputed.
    pub list_rule: &'static str,
    /// The rule this milestone's class came from.
    pub rule: &'static str,
    /// The class was asserted by [`TEXT_HEADS`] rather than derived from
    /// M2.3c's spine demand.
    pub asserted: bool,
}

/// The **advisory** derivation. The theorem is the facts above.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Advisory {
    StrongStringCandidate,
    TextValueUndecided,
    NotText,
    Unknown,
}

impl Advisory {
    pub fn name(self) -> &'static str {
        match self {
            Advisory::StrongStringCandidate => "StrongStringCandidate",
            Advisory::TextValueUndecided => "TextValueUndecided",
            Advisory::NotText => "NotText",
            Advisory::Unknown => "Unknown",
        }
    }

    pub fn rule(self) -> &'static str {
        match self {
            Advisory::StrongStringCandidate => X_ADV_STRONG,
            Advisory::TextValueUndecided => X_ADV_UNDECIDED,
            Advisory::NotText => X_ADV_NOT_TEXT,
            Advisory::Unknown => X_ADV_UNKNOWN,
        }
    }
}

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize)]
pub struct TextFlow {
    pub module: String,
    /// Index into [`ListCensus::flows`]: the flow this refines.
    pub list_flow: usize,
    pub producer: ExprId,
    pub kind: ProducerKind,
    pub producer_name: String,
    pub list_ty: Option<String>,
    pub elem_ty: Option<String>,
    pub element_type_evidence: ElementTypeEvidence,
    /// The selection and corroboration rules that fired, with their nodes.
    pub selection: Vec<Evidence>,

    pub shape: TextShape,
    pub shape_rule: &'static str,
    pub literal: bool,
    pub append_chain: Option<AppendChain>,
    pub append_operand: bool,
    pub consumers: Vec<TextConsumer>,
    pub complete: usize,
    pub prefix: usize,
    pub incremental: usize,
    pub retained: usize,
    pub class_unknown: usize,

    pub char_semantics_required: bool,
    /// `(rule, reason, node)`.
    pub char_reasons: Vec<(&'static str, String, ExprId)>,

    // Inherited from the list flow, cited and not recomputed.
    pub shared_tails: Vec<ExprId>,
    pub prefix_consumers: Vec<ExprId>,
    pub storage: Storage,
    pub escapes: Vec<(&'static str, String, ExprId)>,
    pub spine: SpineDemand,
    pub head: HeadDemand,
    pub recursion: Recursion,
    /// The list flow's `Reuse::Escapes` reason, inherited.
    pub escaped: Option<&'static str>,

    pub advisory: Advisory,
    pub advisory_rule: &'static str,
    pub advisory_reason: Option<String>,
    pub evidence: Vec<Evidence>,
}

impl TextFlow {
    /// Every reason a fact **this milestone records** reads `Unknown`.
    /// M2.3c's `SpineDemand::Unknown` is deliberately not one of them: it
    /// is `Unknown` exactly when the axiom table has no entry for a head,
    /// and [`TEXT_HEADS`] may well have one.
    pub fn unknown_reasons(&self) -> Vec<String> {
        let mut out = Vec::new();
        for c in &self.consumers {
            if c.shape != ConsumerShape::Opaque {
                continue;
            }
            out.push(if c.list_rule == crate::lists::L11_ESCAPE {
                format!("{R_ESCAPED_AT_CONSUMER}({})", c.name)
            } else {
                format!("{R_OPAQUE_CONSUMER}({})", c.name)
            });
        }
        if self.class_unknown > 0 && out.is_empty() {
            out.push(R_CLASS_UNKNOWN.to_string());
        }
        // M2.3c sets `Reuse::Escapes("no-axiom-for")` whenever *any*
        // consumer is an imported head its table has no entry for. That is
        // a restatement of those consumers, not a claim that the value left
        // the walk — and those consumers are each reported above, resolved
        // by [`TEXT_HEADS`] or not. Reporting it again would make a flow
        // this milestone fully resolves look unresolved.
        if let Some(why) = self.escaped
            && why != crate::lists::R_NO_AXIOM
        {
            out.push(format!("{R_ESCAPES}({why})"));
        }
        out
    }

    /// Does any consumer belong to a text family?
    pub fn has_text_consumer(&self) -> bool {
        self.consumers
            .iter()
            .any(|c| c.shape == ConsumerShape::Text)
    }

    /// Does any consumer demand the text at all?
    pub fn demanding_consumers(&self) -> usize {
        self.complete + self.prefix + self.incremental
    }
}

//------------------------------------------------------------------------------
// Structural corroboration: the only place this milestone reads Core
//------------------------------------------------------------------------------

/// Is this expression a `Char` literal, or a saturated `C#` of one?
fn is_char_literal(m: &Module, s: &Scope, id: ExprId) -> bool {
    let e = m.strip(id);
    if let Expr::Lit(l) = m.expr(e) {
        return l.kind == "char";
    }
    let (head, args) = m.spine(e);
    if let Expr::Var { name, .. } = m.expr(head)
        && name.ends_with("$C#")
        && value_args(s, &args).len() == 1
    {
        return true;
    }
    false
}

/// A cell of this chain whose element is a `Char` literal
/// ([`X3_CHAR_LITERAL_HEAD`]).
fn char_literal_head(m: &Module, s: &Scope, f: &ListFlow) -> Option<ExprId> {
    for cell in &f.cells {
        let (_, args) = m.spine(*cell);
        let vargs = value_args(s, &args);
        if vargs.len() == 2 && is_char_literal(m, s, vargs[0]) {
            return Some(*cell);
        }
    }
    None
}

/// Does a `case` decide on a `C#` constructor or on a `Char` literal?
fn is_char_case(m: &Module, case: ExprId) -> bool {
    let Expr::Case { alts, .. } = m.expr(case) else {
        return false;
    };
    alts.iter().any(|a| match &a.con {
        AltCon::DataAlt { name, .. } => name.ends_with("$C#"),
        AltCon::LitAlt { lit } => lit.kind == "char",
        AltCon::Default => false,
    })
}

/// The head binder of a `(:)` alternative, by the same lexical identity
/// M2.3c used to bind it.
fn cons_alt_head(m: &Module, case: ExprId) -> Option<BinderId> {
    let Expr::Case { alts, .. } = m.expr(case) else {
        return None;
    };
    alts.iter()
        .find(|a| {
            matches!(&a.con, AltCon::DataAlt { name, .. } if crate::flow::is_list_cons(name))
                && a.binders.len() == 2
        })
        .map(|a| a.binders[0])
}

/// An element of this flow that is scrutinised as a character
/// ([`X4_CHAR_SCRUTINY`]): an occurrence of a `(:)` alternative's head
/// binder that is the scrutinee of a `case` on `C#` or on a `Char` literal.
fn char_scrutiny(m: &Module, f: &ListFlow) -> Option<(ExprId, BinderId)> {
    for c in &f.consumers {
        if !matches!(c.kind, ConsumerKind::ConsAlt { .. }) {
            continue;
        }
        let Some(head) = cons_alt_head(m, c.at) else {
            continue;
        };
        for occ in m.occurrences(head) {
            if m.edge[*occ as usize] == Edge::CaseScrut
                && let Some(case) = m.parent[*occ as usize]
                && is_char_case(m, case)
            {
                return Some((case, head));
            }
        }
    }
    None
}

/// A consumer whose signature fixes its list arguments to `[Char]`
/// ([`X5_AXIOM_FIXES_CHAR`]).
fn axiom_fixes_char(f: &ListFlow) -> Option<(ExprId, &'static TextHead)> {
    for c in &f.consumers {
        let name = match &c.kind {
            ConsumerKind::Axiom { name, .. } | ConsumerKind::NoAxiom { name, .. } => name,
            _ => continue,
        };
        if let Some(h) = text_head(name)
            && h.fixes_char
        {
            return Some((c.at, h));
        }
    }
    None
}

//------------------------------------------------------------------------------
// Append chains
//------------------------------------------------------------------------------

/// Is this the head of an append call, and if so is it the two-list form
/// (`++`) or the literal-plus-rest form (`unpackAppendCString#`)?
fn append_kind(name: &str) -> Option<bool> {
    match split_stable_name(name) {
        Some((_, "GHC.Base", "++")) | Some((_, "GHC.Base", "++_$s++")) => Some(false),
        Some((_, "GHC.CString", "unpackAppendCString#"))
        | Some((_, "GHC.CString", "unpackAppendCStringUtf8#")) => Some(true),
        _ => None,
    }
}

/// Is this expression static text — an `unpackCString#`-family call with
/// exactly its address argument, or a bare string literal?
fn is_literal_text(m: &Module, s: &Scope, id: ExprId) -> bool {
    let e = m.strip(id);
    if let Expr::Lit(l) = m.expr(e) {
        return l.kind == "string";
    }
    let (head, args) = m.spine(e);
    if let Expr::Var {
        name, is_global, ..
    } = m.expr(head)
        && *is_global
        && is_literal_head(name)
        && value_args(s, &args).len() == 1
    {
        return true;
    }
    false
}

/// The append chain feeding `node`, counted in operand segments
/// ([`X13_APPEND_CHAIN`]). `None` when `node` is not an append call.
fn append_chain(m: &Module, s: &Scope, node: ExprId) -> Option<AppendChain> {
    let mut seen: HashSet<ExprId> = HashSet::new();
    let (len, lit, opaque, is_append) = chain_at(m, s, node, CHAIN_DEPTH, &mut seen);
    if !is_append {
        return None;
    }
    Some(AppendChain {
        length: len,
        all_literal: lit,
        opaque,
    })
}

/// `(segments, all segments are literal, opaque segments, this node is an
/// append call)`.
fn chain_at(
    m: &Module,
    s: &Scope,
    node: ExprId,
    depth: usize,
    seen: &mut HashSet<ExprId>,
) -> (usize, bool, usize, bool) {
    let e = m.strip(node);
    if depth == 0 || !seen.insert(e) {
        return (1, false, 1, false);
    }
    if is_literal_text(m, s, e) {
        return (1, true, 0, false);
    }
    let (head, args) = m.spine(e);
    if let Expr::Var {
        name, is_global, ..
    } = m.expr(head)
        && *is_global
        && let Some(literal_left) = append_kind(name)
    {
        let vargs = value_args(s, &args);
        if vargs.len() >= 2 {
            let right = vargs[vargs.len() - 1];
            let (rl, rlit, rop, _) = chain_at(m, s, right, depth - 1, seen);
            if literal_left {
                // The left operand is the `Addr#` the primitive unpacks.
                return (1 + rl, rlit, rop, true);
            }
            let left = vargs[vargs.len() - 2];
            let (ll, llit, lop, _) = chain_at(m, s, left, depth - 1, seen);
            return (ll + rl, llit && rlit, lop + rop, true);
        }
    }
    // A let- or top-level-bound operand: follow it by lexical identity.
    if let Expr::Var { .. } = m.expr(e)
        && let Some(b) = s.resolve(e)
        && let Some(rhs) = m.binding(b).rhs
    {
        let (l, lit, op, _) = chain_at(m, s, rhs, depth - 1, seen);
        return (l, lit, op, false);
    }
    (1, false, 1, false)
}

//------------------------------------------------------------------------------
// Consumer refinement
//------------------------------------------------------------------------------

fn class_of_spine(d: SpineDemand) -> ConsumerClass {
    match d {
        SpineDemand::Whole => ConsumerClass::Complete,
        SpineDemand::Prefix(_) => ConsumerClass::Prefix,
        SpineDemand::Incremental => ConsumerClass::Incremental,
        SpineDemand::None => ConsumerClass::Retained,
        SpineDemand::Unknown => ConsumerClass::Unknown,
    }
}

fn refine(c: &ListConsumer) -> TextConsumer {
    let (shape, class, family, name, asserted) = match &c.kind {
        ConsumerKind::Axiom { name, .. } => match text_head(name) {
            Some(h) => (
                ConsumerShape::Text,
                h.class_override.unwrap_or_else(|| class_of_spine(c.spine)),
                Some(h.family),
                name.clone(),
                h.class_override.is_some(),
            ),
            None => (
                ConsumerShape::Generic,
                class_of_spine(c.spine),
                None,
                name.clone(),
                false,
            ),
        },
        ConsumerKind::NoAxiom { name, .. } => match text_head(name) {
            Some(h) => (
                ConsumerShape::Text,
                h.class_override.unwrap_or(ConsumerClass::Unknown),
                Some(h.family),
                name.clone(),
                true,
            ),
            None => (
                ConsumerShape::Opaque,
                ConsumerClass::Unknown,
                None,
                name.clone(),
                false,
            ),
        },
        ConsumerKind::ConsAlt { tail, .. } => (
            ConsumerShape::Structural,
            match tail {
                TailFate::Loop { .. } => ConsumerClass::Complete,
                TailFate::LoopIncremental { .. } => ConsumerClass::Incremental,
                TailFate::LoopConditional { .. } | TailFate::Dropped => ConsumerClass::Prefix,
                TailFate::Followed => class_of_spine(c.spine),
            },
            None,
            String::new(),
            false,
        ),
        ConsumerKind::Whnf { .. } => (
            ConsumerShape::Structural,
            ConsumerClass::Prefix,
            None,
            String::new(),
            false,
        ),
        ConsumerKind::StoredIn { con } => (
            ConsumerShape::Neutral,
            ConsumerClass::Retained,
            None,
            con.clone(),
            false,
        ),
        ConsumerKind::ConsedAsTail { .. } => (
            ConsumerShape::Neutral,
            ConsumerClass::Retained,
            None,
            String::new(),
            false,
        ),
        ConsumerKind::PassedLocal { callee } => (
            ConsumerShape::Neutral,
            ConsumerClass::Retained,
            None,
            callee.clone(),
            false,
        ),
        ConsumerKind::Escape { why } => (
            ConsumerShape::Opaque,
            ConsumerClass::Unknown,
            None,
            (*why).to_string(),
            false,
        ),
    };
    TextConsumer {
        at: c.at,
        shape,
        class,
        family,
        name,
        list_rule: c.rule,
        rule: class.rule(),
        asserted,
    }
}

//------------------------------------------------------------------------------
// Accounting
//------------------------------------------------------------------------------

/// One of the M2 census' lazy-argument sites at an append head, and the
/// text flow the argument belongs to.
#[derive(Debug, Clone, Serialize)]
pub struct TextSite {
    pub module: String,
    pub app: ExprId,
    pub arg: ExprId,
    /// `GHC.Base.++` or `GHC.CString.unpackAppendCString#`.
    pub callee: String,
    /// Index into [`TextCensus::flows`].
    pub flow: Option<usize>,
    pub advisory: Option<Advisory>,
    pub reason: Option<&'static str>,
}

/// The M2 census' own population for the append argument tables: a
/// non-trivial *computation* in a lazy or unknown position — the same
/// filter the census report applies before it counts callees, so the two
/// milestones count the same sites.
pub fn census_site(a: &crate::laziness::ArgSite) -> bool {
    a.shape == crate::shape::ArgShape::Computation && a.position.escapes()
}

pub const R_SITE_NOT_TEXT: &str = "the-argument-s-flow-is-not-text";
pub const R_SITE_LOCAL_CALL: &str =
    "the-argument-is-a-local-call-result-M2.3c-follows-as-a-location-not-a-flow";
pub const R_SITE_NO_AXIOM: &str = "the-argument-is-an-imported-call-with-no-axiom";
pub const R_SITE_CASE: &str = "the-argument-is-a-case-or-let-with-no-single-producer";
pub const R_SITE_OTHER: &str = "the-argument-is-not-a-list-producer-this-milestone-sees";

/// Why an append argument carries no flow of its own. A diagnostic
/// breakdown of the refusal, so that no site is left with a bare "no".
fn why_no_flow(m: &Module, s: &Scope, arg: ExprId) -> &'static str {
    let node = m.strip(arg);
    match m.expr(node) {
        Expr::Case { .. } | Expr::Let { .. } => return R_SITE_CASE,
        Expr::App { .. } => {}
        _ => return R_SITE_OTHER,
    }
    let (head, _) = m.spine(node);
    match m.expr(head) {
        Expr::Var { is_global, .. } => {
            if s.binding_of(head).is_some() || !*is_global {
                R_SITE_LOCAL_CALL
            } else {
                R_SITE_NO_AXIOM
            }
        }
        _ => R_SITE_OTHER,
    }
}

#[derive(Debug, Default, Clone, Serialize)]
pub struct TextAccounting {
    // Selection.
    pub list_flows: usize,
    pub text_flows: usize,
    pub non_text: usize,
    pub elem_unknown: usize,
    pub type_only: usize,
    pub structural_only: usize,
    pub both: usize,
    /// Element-type-unknown flows that a consumer's signature would have
    /// fixed to `[Char]` — not selected, reported as the measure of what a
    /// signature-based selection rule would add.
    pub elem_unknown_with_char_axiom: usize,
    /// Flows selected because an append chain they belong to has `[Char]`
    /// elements ([`X24_APPEND_SAME_ELEM`]).
    pub propagated: usize,
    /// Components where that propagation would have contradicted a
    /// rendered element type, and was refused.
    pub propagation_refused: usize,
    /// Rendered element types of the flows that are not text.
    pub non_text_types: Vec<(String, usize)>,

    // Facts.
    pub by_shape: Vec<(&'static str, usize)>,
    pub by_advisory: Vec<(Advisory, usize)>,
    pub by_class: Vec<(&'static str, usize)>,
    pub by_consumer_shape: Vec<(&'static str, usize)>,
    pub by_family: Vec<(&'static str, usize)>,
    pub by_storage: Vec<(&'static str, usize)>,
    pub by_recursion: Vec<(&'static str, usize)>,
    pub literal_flows: usize,
    pub append_flows: usize,
    pub append_operands: usize,
    pub append_all_literal: usize,
    pub append_hist: Vec<(usize, usize)>,
    pub char_semantics: usize,
    pub char_reasons: Vec<(&'static str, usize)>,
    pub shared_tail_flows: usize,
    pub prefix_consumer_flows: usize,
    pub escaping_flows: usize,
    pub asserted_class_consumers: usize,

    /// Per module: (module, list flows, text flows).
    pub per_module: Vec<(String, usize, usize)>,
    /// Consumer sites at each append head: (stable name, total over all
    /// list flows, of those on text flows).
    pub append_consumer_sites: Vec<(String, usize, usize)>,
    pub rules: Vec<(&'static str, usize)>,

    pub sites: Vec<TextSite>,
    pub sites_mapped: usize,
    pub sites_unmapped: usize,
}

impl TextAccounting {
    pub fn count(&self, a: Advisory) -> usize {
        self.by_advisory
            .iter()
            .find(|(x, _)| *x == a)
            .map(|(_, n)| *n)
            .unwrap_or(0)
    }

    /// Every text flow lands in exactly one bucket of every table, the
    /// three selection buckets partition M2.3c's population, and every
    /// append argument site of the M2 census is mapped or carries a reason.
    pub fn check(&self) {
        assert_eq!(
            self.text_flows + self.non_text + self.elem_unknown,
            self.list_flows,
            "every list flow is text, not text, or of unknown element type"
        );
        assert_eq!(
            self.type_only + self.structural_only + self.both,
            self.text_flows,
            "every text flow was selected by a type string, by a structural fact, or by both"
        );
        for (what, total) in [
            ("shape", self.by_shape.iter().map(|(_, n)| n).sum::<usize>()),
            ("advisory", self.by_advisory.iter().map(|(_, n)| n).sum()),
            ("storage", self.by_storage.iter().map(|(_, n)| n).sum()),
            ("recursion", self.by_recursion.iter().map(|(_, n)| n).sum()),
        ] {
            assert_eq!(
                total, self.text_flows,
                "every text flow must land in exactly one {what} bucket"
            );
        }
        assert_eq!(
            self.append_hist.iter().map(|(_, n)| n).sum::<usize>(),
            self.append_flows,
            "every append-produced flow is in the histogram exactly once"
        );
        assert_eq!(
            self.per_module.iter().map(|(_, _, t)| t).sum::<usize>(),
            self.text_flows,
            "the per-module text totals must sum to the population"
        );
        assert_eq!(
            self.sites_mapped + self.sites_unmapped,
            self.sites.len(),
            "every append argument site is mapped or carries a reason"
        );
        for s in &self.sites {
            assert!(
                s.flow.is_some() ^ s.reason.is_some(),
                "site {} in {} must map onto exactly one text flow or carry a reason",
                s.app,
                s.module
            );
        }
    }
}

//------------------------------------------------------------------------------
// The census
//------------------------------------------------------------------------------

pub struct TextCensus {
    pub flows: Vec<TextFlow>,
    pub accounting: TextAccounting,
}

impl TextCensus {
    /// Select the text flows out of M2.3c's population and refine them.
    /// `lc` must have been built from `modules`.
    pub fn of_modules(
        modules: &[&Module],
        lc: &ListCensus,
        census: &crate::laziness::Census,
    ) -> TextCensus {
        let by_name: HashMap<&str, &Module> =
            modules.iter().map(|m| (m.name.as_str(), *m)).collect();
        let scopes: HashMap<&str, Scope<'_>> = modules
            .iter()
            .map(|m| (m.name.as_str(), Scope::new(m)))
            .collect();

        let mut acct = TextAccounting {
            list_flows: lc.flows.len(),
            ..Default::default()
        };
        let mut flows: Vec<TextFlow> = Vec::new();
        // (module, list flow index) -> text flow index.
        let mut index: HashMap<usize, usize> = HashMap::new();
        let mut non_text_types: BTreeMap<String, usize> = BTreeMap::new();
        let mut per_module_list: BTreeMap<String, usize> = BTreeMap::new();
        let mut per_module_text: BTreeMap<String, usize> = BTreeMap::new();

        // Pass 1: what each flow's own evidence says about its element.
        struct Pre {
            rendered: RenderedElem,
            type_says_char: bool,
            structural: bool,
            fixes: bool,
            selection: Vec<Evidence>,
        }
        let mut pre: Vec<Pre> = Vec::with_capacity(lc.flows.len());
        for f in &lc.flows {
            *per_module_list.entry(f.module.clone()).or_default() += 1;
            let m = by_name[f.module.as_str()];
            let s = &scopes[f.module.as_str()];

            let rendered = rendered_element(f);
            let mut selection: Vec<Evidence> = Vec::new();
            let type_says_char = rendered == RenderedElem::Char;
            if type_says_char {
                if let Some(e) = &f.elem_ty
                    && reads_as_char(e)
                {
                    selection.push(Evidence {
                        rule: X0_ELEM_TYPE,
                        nodes: vec![f.producer],
                        binder: None,
                        note: format!(
                            "the (:) alternative's head binder is rendered {e:?} \
                             (level 6: a rendered type, not TyCon identity)"
                        ),
                    });
                }
                if let Some(l) = &f.list_ty
                    && rendered_elem_of_list(l).is_some_and(|e| reads_as_char(&e))
                {
                    selection.push(Evidence {
                        rule: X1_LIST_TYPE,
                        nodes: vec![f.producer],
                        binder: f.bound,
                        note: format!(
                            "the flow's binder is rendered {l:?} \
                             (level 6: a rendered type, not TyCon identity)"
                        ),
                    });
                }
            }
            let mut structural = false;
            if f.kind == ProducerKind::ImportedCall && is_unpack_head(&f.producer_name) {
                structural = true;
                selection.push(Evidence {
                    rule: X2_UNPACK_PRODUCER,
                    nodes: vec![f.producer],
                    binder: None,
                    note: format!(
                        "{} produces [Char] by the primitive's type",
                        f.producer_name
                    ),
                });
            }
            if let Some(cell) = char_literal_head(m, s, f) {
                structural = true;
                selection.push(Evidence {
                    rule: X3_CHAR_LITERAL_HEAD,
                    nodes: vec![cell],
                    binder: None,
                    note: "a cell's element is a Char literal".into(),
                });
            }
            if let Some((case, head)) = char_scrutiny(m, f) {
                structural = true;
                selection.push(Evidence {
                    rule: X4_CHAR_SCRUTINY,
                    nodes: vec![case],
                    binder: Some(head),
                    note: "the element is scrutinised as a character".into(),
                });
            }
            let fixes = axiom_fixes_char(f);
            if let Some((at, h)) = fixes {
                structural = true;
                selection.push(Evidence {
                    rule: X5_AXIOM_FIXES_CHAR,
                    nodes: vec![at],
                    binder: None,
                    note: format!("{}.{}: {}", h.module, h.occ, h.note),
                });
            }
            pre.push(Pre {
                rendered,
                type_says_char,
                structural,
                fixes: fixes.is_some(),
                selection,
            });
        }

        // Pass 2: an append does not change the element type
        // ([`X24_APPEND_SAME_ELEM`]). Close the relation between an append
        // call's result flow and its list operands to a fixpoint.
        let mut producer_at: HashMap<(&str, ExprId), usize> = HashMap::new();
        for (i, f) in lc.flows.iter().enumerate() {
            producer_at
                .entry((f.module.as_str(), f.producer))
                .or_insert(i);
        }
        let mut edges: Vec<(usize, usize)> = Vec::new();
        for (i, f) in lc.flows.iter().enumerate() {
            for c in &f.consumers {
                let ConsumerKind::Axiom { name, .. } = &c.kind else {
                    continue;
                };
                if append_kind(name).is_none() {
                    continue;
                }
                if let Some(j) = producer_at.get(&(f.module.as_str(), c.at)) {
                    edges.push((i, *j));
                }
            }
        }
        let mut uf: Vec<usize> = (0..lc.flows.len()).collect();
        fn find(uf: &mut [usize], mut x: usize) -> usize {
            while uf[x] != x {
                uf[x] = uf[uf[x]];
                x = uf[x];
            }
            x
        }
        for (a, b) in &edges {
            let (ra, rb) = (find(&mut uf, *a), find(&mut uf, *b));
            if ra != rb {
                uf[ra] = rb;
            }
        }
        // Per component: is a Char established anywhere, and is a concrete
        // non-Char established anywhere (a contradiction)?
        let mut comp_char: HashMap<usize, ExprId> = HashMap::new();
        let mut comp_other: HashSet<usize> = HashSet::new();
        for (i, p) in pre.iter().enumerate() {
            let r = find(&mut uf, i);
            if p.type_says_char || p.structural {
                comp_char.entry(r).or_insert(lc.flows[i].producer);
            }
            if matches!(p.rendered, RenderedElem::Other(_)) {
                comp_other.insert(r);
            }
        }

        // Pass 3: select, refine, and count.
        for (i, f) in lc.flows.iter().enumerate() {
            let m = by_name[f.module.as_str()];
            let s = &scopes[f.module.as_str()];
            let p = &mut pre[i];
            let root = find(&mut uf, i);
            let own = p.type_says_char || p.structural;
            if !own
                && comp_char.contains_key(&root)
                && !matches!(p.rendered, RenderedElem::Other(_))
            {
                if comp_other.contains(&root) {
                    acct.propagation_refused += 1;
                } else {
                    p.structural = true;
                    p.selection.push(Evidence {
                        rule: X24_APPEND_SAME_ELEM,
                        nodes: vec![comp_char[&root]],
                        binder: None,
                        note: "an append chain this flow belongs to has [Char] elements".into(),
                    });
                    acct.propagated += 1;
                }
            }
            if !(p.type_says_char || p.structural) {
                match &p.rendered {
                    RenderedElem::Other(t) => {
                        acct.non_text += 1;
                        *non_text_types.entry(t.clone()).or_default() += 1;
                    }
                    _ => {
                        acct.elem_unknown += 1;
                        if p.fixes {
                            acct.elem_unknown_with_char_axiom += 1;
                        }
                    }
                }
                continue;
            }
            let element_type_evidence = match (p.type_says_char, p.structural) {
                (true, true) => ElementTypeEvidence::Both,
                (true, false) => ElementTypeEvidence::TypeStringOnly,
                (false, _) => ElementTypeEvidence::StructuralOnly,
            };
            index.insert(i, flows.len());
            *per_module_text.entry(f.module.clone()).or_default() += 1;
            flows.push(build(
                m,
                s,
                i,
                f,
                element_type_evidence,
                std::mem::take(&mut p.selection),
            ));
        }

        // Tables.
        let mut by_shape: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_advisory: BTreeMap<Advisory, usize> = BTreeMap::new();
        let mut by_class: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_cshape: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_family: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_storage: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut by_recursion: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut char_reasons: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut hist: BTreeMap<usize, usize> = BTreeMap::new();
        let mut rules: BTreeMap<&'static str, usize> = BTreeMap::new();
        for t in &flows {
            acct.text_flows += 1;
            match t.element_type_evidence {
                ElementTypeEvidence::TypeStringOnly => acct.type_only += 1,
                ElementTypeEvidence::StructuralOnly => acct.structural_only += 1,
                ElementTypeEvidence::Both => acct.both += 1,
            }
            *by_shape.entry(t.shape.name()).or_default() += 1;
            *by_advisory.entry(t.advisory).or_default() += 1;
            *by_storage.entry(t.storage.name()).or_default() += 1;
            *by_recursion
                .entry(match t.recursion {
                    Recursion::FiniteProducer => "FiniteProducer",
                    Recursion::RecursiveKnot => "RecursiveKnot",
                })
                .or_default() += 1;
            if t.literal {
                acct.literal_flows += 1;
            }
            if let Some(ch) = t.append_chain {
                acct.append_flows += 1;
                *hist.entry(ch.length).or_default() += 1;
                if ch.all_literal {
                    acct.append_all_literal += 1;
                }
            }
            if t.append_operand {
                acct.append_operands += 1;
            }
            if t.char_semantics_required {
                acct.char_semantics += 1;
            }
            for (_, reason, _) in &t.char_reasons {
                let key: &'static str = [
                    CS_HEAD_BOUND,
                    CS_HEAD_FORCED,
                    CS_CHAR_LITERAL,
                    CS_CHAR_SCRUTINY,
                    CS_CHAR_CONSUMER,
                    CS_POSITION,
                ]
                .into_iter()
                .find(|k| reason.starts_with(k))
                .unwrap_or(CS_CHAR_CONSUMER);
                *char_reasons.entry(key).or_default() += 1;
            }
            if !t.shared_tails.is_empty() {
                acct.shared_tail_flows += 1;
            }
            if !t.prefix_consumers.is_empty() {
                acct.prefix_consumer_flows += 1;
            }
            if t.escaped.is_some() {
                acct.escaping_flows += 1;
            }
            for c in &t.consumers {
                *by_class.entry(c.class.name()).or_default() += 1;
                *by_cshape.entry(c.shape.name()).or_default() += 1;
                if let Some(fam) = c.family {
                    *by_family.entry(fam.name()).or_default() += 1;
                }
                if c.asserted {
                    acct.asserted_class_consumers += 1;
                }
                *rules.entry(c.rule).or_default() += 1;
            }
            for e in &t.selection {
                *rules.entry(e.rule).or_default() += 1;
            }
            for e in &t.evidence {
                *rules.entry(e.rule).or_default() += 1;
            }
            *rules.entry(t.shape_rule).or_default() += 1;
            *rules.entry(t.advisory_rule).or_default() += 1;
        }
        acct.by_shape = by_shape.into_iter().collect();
        acct.by_advisory = by_advisory.into_iter().collect();
        acct.by_class = by_class.into_iter().collect();
        acct.by_consumer_shape = by_cshape.into_iter().collect();
        acct.by_family = by_family.into_iter().collect();
        acct.by_storage = by_storage.into_iter().collect();
        acct.by_recursion = by_recursion.into_iter().collect();
        acct.char_reasons = char_reasons.into_iter().collect();
        acct.char_reasons
            .sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        acct.append_hist = hist.into_iter().collect();
        acct.non_text_types = non_text_types.into_iter().collect();
        acct.non_text_types
            .sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        acct.rules = rules.into_iter().collect();
        acct.rules.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        acct.per_module = per_module_list
            .into_iter()
            .map(|(name, n)| {
                let t = per_module_text.get(&name).copied().unwrap_or(0);
                (name, n, t)
            })
            .collect();

        // The `++` / `unpackAppendCString#` consumer sites, as evidence:
        // how many of M2.3c's append consumers sit on a text flow?
        let mut append_sites: BTreeMap<String, (usize, usize)> = BTreeMap::new();
        for (i, f) in lc.flows.iter().enumerate() {
            let is_text = index.contains_key(&i);
            for c in &f.consumers {
                let name = match &c.kind {
                    ConsumerKind::Axiom { name, .. } | ConsumerKind::NoAxiom { name, .. } => name,
                    _ => continue,
                };
                if append_kind(name).is_none() {
                    continue;
                }
                let e = append_sites.entry(name.clone()).or_insert((0, 0));
                e.0 += 1;
                if is_text {
                    e.1 += 1;
                }
            }
        }
        acct.append_consumer_sites = append_sites
            .into_iter()
            .map(|(k, (a, b))| (k, a, b))
            .collect();
        acct.append_consumer_sites
            .sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));

        // The M2 census' lazy-argument sites at the two append heads.
        let offsets = module_offsets(lc);
        let known: HashSet<&str> = modules.iter().map(|m| m.name.as_str()).collect();
        for site in &census.args {
            if !known.contains(site.module.as_str()) || !census_site(site) {
                continue;
            }
            let Some(cm) = site.callee.module.as_deref() else {
                continue;
            };
            let callee = format!("{cm}.{}", site.callee.occ);
            if !matches!(
                (cm, site.callee.occ.as_str()),
                ("GHC.Base", "++") | ("GHC.CString", "unpackAppendCString#")
            ) {
                continue;
            }
            let list_flow = resolve_arg(lc, &offsets, &scopes, &site.module, site.arg);
            let (flow, reason) = match list_flow.and_then(|i| index.get(&i).copied()) {
                Some(t) => (Some(t), None),
                None => (
                    None,
                    Some(if list_flow.is_some() {
                        R_SITE_NOT_TEXT
                    } else {
                        why_no_flow(
                            by_name[site.module.as_str()],
                            &scopes[site.module.as_str()],
                            site.arg,
                        )
                    }),
                ),
            };
            if flow.is_some() {
                acct.sites_mapped += 1;
            } else {
                acct.sites_unmapped += 1;
            }
            acct.sites.push(TextSite {
                module: site.module.clone(),
                app: site.app,
                arg: site.arg,
                callee,
                flow,
                advisory: flow.map(|i| flows[i].advisory),
                reason,
            });
        }

        acct.check();
        TextCensus {
            flows,
            accounting: acct,
        }
    }
}

/// Where each module's flows start in [`ListCensus::flows`]: the flat list
/// is the per-module lists concatenated in order.
fn module_offsets(lc: &ListCensus) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    let mut base = 0usize;
    for l in &lc.per_module {
        out.push((l.module.name.clone(), base));
        base += l.flows.len();
    }
    out
}

/// Which list flow does this argument expression carry? Either it *is* a
/// producer or a cell of one, or it is an occurrence of the binder a flow
/// is bound to (lexical identity, level 1).
fn resolve_arg(
    lc: &ListCensus,
    offsets: &[(String, usize)],
    scopes: &HashMap<&str, Scope<'_>>,
    module: &str,
    arg: ExprId,
) -> Option<usize> {
    let (k, (_, base)) = offsets
        .iter()
        .enumerate()
        .find(|(_, (name, _))| name == module)?;
    let l = &lc.per_module[k];
    let s = scopes.get(module)?;
    let node = l.module.strip(arg);
    if let Some(f) = l.flow_at(node) {
        return lc.flows[*base..*base + l.flows.len()]
            .iter()
            .position(|g| g.producer == f.producer)
            .map(|p| base + p);
    }
    let b = s.resolve(node)?;
    l.flows
        .iter()
        .position(|g| g.bound == Some(b))
        .map(|p| base + p)
}

/// Refine one list flow into a text flow: the facts first, the advisory
/// last, and every inherited fact cited rather than recomputed.
fn build(
    m: &Module,
    s: &Scope,
    list_flow: usize,
    f: &ListFlow,
    element_type_evidence: ElementTypeEvidence,
    selection: Vec<Evidence>,
) -> TextFlow {
    let consumers: Vec<TextConsumer> = f.consumers.iter().map(refine).collect();
    let mut evidence: Vec<Evidence> = Vec::new();

    // Fact 1: is every consumer text-shaped?
    let shape = if consumers.iter().any(|c| c.shape == ConsumerShape::Opaque) {
        TextShape::Unknown
    } else if consumers
        .iter()
        .any(|c| matches!(c.shape, ConsumerShape::Generic | ConsumerShape::Structural))
    {
        TextShape::Mixed
    } else if consumers.iter().any(|c| c.shape == ConsumerShape::Text) {
        TextShape::TextOnly
    } else {
        TextShape::Unobserved
    };

    // Fact 2: literal construction and append chains.
    let literal = f.kind == ProducerKind::ImportedCall && is_literal_head(&f.producer_name);
    if literal {
        evidence.push(Evidence {
            rule: X12_LITERAL,
            nodes: vec![f.producer],
            binder: None,
            note: format!("{} unpacks static data", f.producer_name),
        });
    }
    let append_chain = append_chain(m, s, f.producer);
    if let Some(ch) = append_chain {
        evidence.push(Evidence {
            rule: X13_APPEND_CHAIN,
            nodes: vec![f.producer],
            binder: None,
            note: format!(
                "{} operand segment(s), {}, {} opaque",
                ch.length,
                if ch.all_literal {
                    "all literal"
                } else {
                    "not all literal"
                },
                ch.opaque
            ),
        });
    }
    let append_operand = consumers
        .iter()
        .any(|c| c.family == Some(TextFamily::Append));
    if append_operand {
        evidence.push(Evidence {
            rule: X14_APPEND_OPERAND,
            nodes: consumers
                .iter()
                .filter(|c| c.family == Some(TextFamily::Append))
                .map(|c| c.at)
                .collect(),
            binder: None,
            note: "an operand of an append".into(),
        });
    }

    // Fact 3: the consumer classes.
    let mut complete = 0;
    let mut prefix = 0;
    let mut incremental = 0;
    let mut retained = 0;
    let mut class_unknown = 0;
    let mut prefix_consumers: Vec<ExprId> = Vec::new();
    for c in &consumers {
        match c.class {
            ConsumerClass::Complete => complete += 1,
            ConsumerClass::Prefix => {
                prefix += 1;
                prefix_consumers.push(c.at);
            }
            ConsumerClass::Incremental => incremental += 1,
            ConsumerClass::Retained => retained += 1,
            ConsumerClass::Unknown => class_unknown += 1,
        }
    }

    // Fact 4: does anything require character semantics?
    let mut char_reasons: Vec<(&'static str, String, ExprId)> = Vec::new();
    for (c, lc) in consumers.iter().zip(f.consumers.iter()) {
        if let ConsumerKind::ConsAlt {
            head_bound: true, ..
        } = lc.kind
        {
            char_reasons.push((crate::lists::L3_HEAD_BOUND, CS_HEAD_BOUND.to_string(), c.at));
        }
        let exposing =
            text_head(&c.name).is_some_and(|h| h.char_exposing) || in_table(CHAR_EXPOSING, &c.name);
        if exposing {
            char_reasons.push((
                X20_CHAR_SEMANTICS,
                format!("{CS_CHAR_CONSUMER}({})", c.name),
                c.at,
            ));
        }
        let positional = text_head(&c.name).is_some_and(|h| h.position_semantics)
            || in_table(POSITION_SEMANTICS, &c.name);
        if positional {
            char_reasons.push((
                X20_CHAR_SEMANTICS,
                format!("{CS_POSITION}({})", c.name),
                c.at,
            ));
        }
    }
    if f.head != HeadDemand::None && f.head != HeadDemand::Unknown {
        char_reasons.push((
            crate::lists::L3_HEAD_BOUND,
            format!("{CS_HEAD_FORCED}({})", f.head.name()),
            f.producer,
        ));
    }
    for e in &selection {
        if e.rule == X3_CHAR_LITERAL_HEAD {
            char_reasons.push((
                X3_CHAR_LITERAL_HEAD,
                CS_CHAR_LITERAL.to_string(),
                e.nodes[0],
            ));
        }
        if e.rule == X4_CHAR_SCRUTINY {
            char_reasons.push((X4_CHAR_SCRUTINY, CS_CHAR_SCRUTINY.to_string(), e.nodes[0]));
        }
    }
    let char_semantics_required = !char_reasons.is_empty();
    if char_semantics_required {
        evidence.push(Evidence {
            rule: X20_CHAR_SEMANTICS,
            nodes: char_reasons.iter().map(|(_, _, n)| *n).collect(),
            binder: None,
            note: format!("{} reason(s)", char_reasons.len()),
        });
    }

    // Inherited facts, cited.
    let (shared_tails, escaped) = match &f.reuse {
        Reuse::SharedTail { at } => (at.clone(), None),
        Reuse::Escapes(why) => (Vec::new(), Some(*why)),
        _ => (Vec::new(), None),
    };
    if !shared_tails.is_empty() {
        evidence.push(Evidence {
            rule: X21_SHARED_TAIL,
            nodes: shared_tails.clone(),
            binder: None,
            note: format!("inherited from {}", crate::lists::L14_SHARED_TAIL),
        });
    }
    if f.storage != Storage::NotStored {
        evidence.push(Evidence {
            rule: X22_STORAGE,
            nodes: vec![f.producer],
            binder: None,
            note: format!("inherited: {}", f.storage.name()),
        });
    }
    if let Some(why) = escaped {
        evidence.push(Evidence {
            rule: X23_ESCAPE,
            nodes: f.escapes.iter().map(|(_, _, n)| *n).collect(),
            binder: None,
            note: format!("inherited from {}: {why}", crate::lists::L11_ESCAPE),
        });
    }

    let mut t = TextFlow {
        module: f.module.clone(),
        list_flow,
        producer: f.producer,
        kind: f.kind,
        producer_name: f.producer_name.clone(),
        list_ty: f.list_ty.clone(),
        elem_ty: f.elem_ty.clone(),
        element_type_evidence,
        selection,
        shape,
        shape_rule: shape.rule(),
        literal,
        append_chain,
        append_operand,
        consumers,
        complete,
        prefix,
        incremental,
        retained,
        class_unknown,
        char_semantics_required,
        char_reasons,
        shared_tails,
        prefix_consumers,
        storage: f.storage.clone(),
        escapes: f.escapes.clone(),
        spine: f.spine,
        head: f.head,
        recursion: f.recursion,
        escaped,
        advisory: Advisory::Unknown,
        advisory_rule: X_ADV_UNKNOWN,
        advisory_reason: None,
        evidence,
    };
    let (a, reason) = advise(&t);
    t.advisory = a;
    t.advisory_rule = a.rule();
    t.advisory_reason = reason;
    t
}

/// The **advisory**, derived from the facts and from nothing else. It does
/// not decide that anything is a Rust `String`.
fn advise(t: &TextFlow) -> (Advisory, Option<String>) {
    let unknown = t.unknown_reasons();
    if !unknown.is_empty() {
        return (Advisory::Unknown, Some(unknown.join(", ")));
    }
    if t.shape == TextShape::Unobserved {
        return (Advisory::TextValueUndecided, Some(R_UNOBSERVED.to_string()));
    }
    // "Consumed only structurally" means exactly that: nothing text-shaped,
    // and no character observed either. A `(:)` alternative whose head is
    // scrutinised as a character *is* a text observation, even though the
    // consumer set is structural and therefore `Mixed`.
    if !t.has_text_consumer() && !t.char_semantics_required {
        return (Advisory::NotText, Some(R_NO_TEXT_CONSUMER.to_string()));
    }
    let mut why: Vec<&str> = Vec::new();
    if t.shape != TextShape::TextOnly {
        why.push(R_MIXED);
    }
    if t.prefix > 0 {
        why.push(R_PREFIX_CONSUMER);
    }
    if !t.shared_tails.is_empty() {
        why.push(R_SHARED_TAIL);
    }
    if t.char_semantics_required {
        why.push(R_CHAR_SEMANTICS);
    }
    if t.recursion == Recursion::RecursiveKnot {
        why.push(R_KNOT);
    }
    if t.demanding_consumers() == 0 {
        why.push(R_NO_DEMANDING_CONSUMER);
    }
    if why.is_empty() {
        (Advisory::StrongStringCandidate, None)
    } else {
        (Advisory::TextValueUndecided, Some(why.join(", ")))
    }
}
