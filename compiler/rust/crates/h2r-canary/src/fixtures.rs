//! What the canary compiles, what it feeds it, and what each entry must
//! exhibit for it to be testing the thing it was written for.
//!
//! A fixture's `evidence` is the part that stops a test rotting into a
//! tautology. `dataChoice` compared against GHC proves the answer is right; it
//! does not prove a constructor was ever built, and a lowering that stopped
//! emitting `Construct` would keep passing. The evidence says what must be in
//! the NIR, so the fixture fails when it stops covering its subject.
//!
//! Which profile a check applies to is part of the check. `-O1` inlines the
//! dictionaries away before the dump is taken, so the entries that exercise
//! dictionary resolution can only do it unoptimised, and GHC folds `"a" ++ "b"`
//! into one literal there, so the appending unpacker is reachable only through
//! a tail it cannot fold.

use h2r_lower::nir::{IntBinary, ListOp, Predicate, external::Equality};

/// Which Core profile a check applies to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Profile {
    Optimized,
    Unoptimized,
}

impl Profile {
    pub const ALL: [Profile; 2] = [Profile::Optimized, Profile::Unoptimized];

    pub fn name(self) -> &'static str {
        match self {
            Profile::Optimized => "optimized",
            Profile::Unoptimized => "unoptimized",
        }
    }
}

/// When a check applies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum When {
    Both,
    Only(Profile),
}

impl When {
    pub fn covers(self, profile: Profile) -> bool {
        match self {
            When::Both => true,
            When::Only(only) => only == profile,
        }
    }
}

/// An NIR operation a fixture must produce, named structurally rather than by
/// the pretty printer's spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Construct,
    MakeUnboxedTuple,
    UnboxedTupleField,
    MatchData,
    MakeClosure,
    Apply,
    LocalScope,
    CallLocal,
    DelayBlock,
    EvaluateBlock,
    Move,
    OrdChar,
    ChrChar,
    CharCompare,
    Int(IntBinary),
    WordCompare,
    RaiseCallStackError,
    UnpackString,
    /// An unpacked literal appended to something: the `unpackAppendCString#`
    /// family, which `unpackCString#` alone never reaches.
    UnpackStringOnto,
    AppendList,
    ListPredicate(Predicate, Equality),
    ListFunction(ListOp),
    CompareStrings,
    DataToTag,
    TagToEnum,
    PointerEquality,
}

impl Op {
    pub fn name(self) -> &'static str {
        match self {
            Op::Construct => "construct",
            Op::MakeUnboxedTuple => "unboxed-tuple",
            Op::UnboxedTupleField => "unboxed-tuple-field",
            Op::MatchData => "match-data",
            Op::MakeClosure => "make-closure",
            Op::Apply => "apply",
            Op::LocalScope => "local-scope",
            Op::CallLocal => "call-local",
            Op::DelayBlock => "delay",
            Op::EvaluateBlock => "evaluate",
            Op::Move => "move",
            Op::OrdChar => "ord-char",
            Op::ChrChar => "chr-char",
            Op::CharCompare => "char-compare",
            Op::Int(IntBinary::ShiftLeft) => "uncheckedIShiftL#",
            Op::Int(IntBinary::ShiftRightArithmetic) => "uncheckedIShiftRA#",
            Op::Int(_) => "Int# arithmetic",
            Op::WordCompare => "Word# comparison",
            Op::RaiseCallStackError => "error with a call stack",
            Op::UnpackString => "unpack-string",
            Op::UnpackStringOnto => "unpack-string onto a tail",
            Op::AppendList => "append-list",
            Op::CompareStrings => "compare @[Char]",
            Op::DataToTag => "dataToTag#",
            Op::TagToEnum => "tagToEnum#",
            Op::PointerEquality => "reallyUnsafePtrEquality#",
            Op::ListFunction(ListOp::Map) => "map",
            Op::ListFunction(ListOp::Filter) => "filter",
            Op::ListFunction(ListOp::TakeWhile) => "takeWhile",
            Op::ListFunction(ListOp::DropWhile) => "dropWhile",
            Op::ListFunction(ListOp::Reverse) => "reverse",
            Op::ListFunction(ListOp::ReverseOnto) => "reverse1",
            Op::ListFunction(ListOp::Length) => "$wlenAcc",
            Op::ListFunction(ListOp::ConsAppend) => "++_$s++",
            Op::ListPredicate(Predicate::EqString, Equality::Char) => "eqString",
            Op::ListPredicate(Predicate::EqString, Equality::String) => "eqString over Eq [Char]",
            Op::ListPredicate(Predicate::Elem, Equality::Char) => "elem via $fEqChar",
            Op::ListPredicate(Predicate::Elem, Equality::String) => "elem via Eq [Char]",
            Op::ListPredicate(Predicate::IsPrefixOf, Equality::Char) => "isPrefixOf via $fEqChar",
            Op::ListPredicate(Predicate::IsPrefixOf, Equality::String) => {
                "isPrefixOf via Eq [Char]"
            }
        }
    }
}

/// An origin rule a fixture must produce.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuleKind {
    LazyBinding,
    StrictBinding,
    EraseCast,
    ResolveMethod,
    Diverge,
    MagicLazy,
}

impl RuleKind {
    pub fn name(self) -> &'static str {
        match self {
            RuleKind::LazyBinding => "LazyBinding",
            RuleKind::StrictBinding => "StrictBinding",
            RuleKind::EraseCast => "EraseCast",
            RuleKind::ResolveMethod => "ResolveMethod",
            RuleKind::Diverge => "Diverge",
            RuleKind::MagicLazy => "MagicLazy",
        }
    }
}

/// What a fixture must exhibit.
#[derive(Debug, Clone, Copy)]
pub enum Evidence {
    /// Somewhere in the owner's own leaf.
    Operation(Op),
    /// An instruction in the owner's own leaf carrying this origin rule.
    Rule(RuleKind),
    /// The owner's CFG switches on an unboxed scalar.
    ScalarSwitch,
    /// Specializing from this owner lowers every instance it reaches.
    InstancesComplete,
    /// Exactly this many instances of the binding with this occurrence name.
    InstancesOf { occ: &'static str, count: usize },
    /// Some instance in the closure was specialized on this many type
    /// arguments and dictionaries.
    SpecializedOn {
        type_arguments: usize,
        dictionaries: usize,
    },
    /// An operation anywhere in the specialized closure, not only the root.
    /// What a fixture demonstrates does not always stay in the binding that
    /// names it: GHC floats a constant list out to its own top-level binding,
    /// and the instance closure is where it then lives.
    ClosureOperation(Op),
    /// An origin rule anywhere in the specialized closure, not only the root.
    ClosureRule(RuleKind),
    /// The generated Rust contains this text. Used only for properties of the
    /// output, such as a CAF becoming one shared value, never as a stand-in
    /// for an NIR check.
    Emitted(&'static str),
}

#[derive(Debug, Clone, Copy)]
pub struct Check {
    pub when: When,
    pub what: Evidence,
}

const fn both(what: Evidence) -> Check {
    Check {
        when: When::Both,
        what,
    }
}

const fn unoptimized(what: Evidence) -> Check {
    Check {
        when: When::Only(Profile::Unoptimized),
        what,
    }
}

const fn optimized(what: Evidence) -> Check {
    Check {
        when: When::Only(Profile::Optimized),
        what,
    }
}

/// An operation the owner's own leaf must contain in both profiles.
const fn op(kind: Op) -> Check {
    both(Evidence::Operation(kind))
}

/// An operation the specialized closure must contain in both profiles. GHC
/// floats constant lists and their literals out to their own top-level
/// bindings, so these are not always in the binding that names the fixture.
const EQ_STRING: Op = Op::ListPredicate(Predicate::EqString, Equality::Char);
const ELEM_CHAR: Op = Op::ListPredicate(Predicate::Elem, Equality::Char);
const PREFIX_CHAR: Op = Op::ListPredicate(Predicate::IsPrefixOf, Equality::Char);

const MAP: Op = Op::ListFunction(ListOp::Map);
const FILTER: Op = Op::ListFunction(ListOp::Filter);
const TAKE_WHILE: Op = Op::ListFunction(ListOp::TakeWhile);
const DROP_WHILE: Op = Op::ListFunction(ListOp::DropWhile);
const REVERSE: &[Check] = &[
    optimized(Evidence::ClosureOperation(Op::ListFunction(
        ListOp::ReverseOnto,
    ))),
    unoptimized(Evidence::ClosureOperation(Op::ListFunction(
        ListOp::Reverse,
    ))),
];
const CONS_APPEND: &[Check] = &[
    optimized(Evidence::ClosureOperation(Op::ListFunction(
        ListOp::ConsAppend,
    ))),
    unoptimized(Evidence::ClosureOperation(Op::AppendList)),
];

const fn anywhere(kind: Op) -> Check {
    both(Evidence::ClosureOperation(kind))
}

/// An origin rule the owner's own leaf must carry in both profiles.
const fn rule(kind: RuleKind) -> Check {
    both(Evidence::Rule(kind))
}

/// An operation `-O1` removes entirely, so the unoptimised dump is the only
/// place it can be asked for.
const fn unoptimized_op(kind: Op) -> Check {
    unoptimized(Evidence::Operation(kind))
}

const fn unoptimized_rule(kind: RuleKind) -> Check {
    unoptimized(Evidence::Rule(kind))
}

/// How the generated CLI adapter is driven.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Inputs {
    /// No arguments at all: a CAF.
    Nullary,
    /// One argument, over the signed-64-bit boundary grid.
    Unary,
    /// Two arguments, over the full boundary grid.
    Binary,
    /// Small depths, plus one million-iteration case that would overflow a
    /// native stack if a scalar tail call grew one.
    Recursive,
    /// Small depths against a fixed second argument.
    Tree,
    /// Never compiled or run: the entry exists to be lowered, not entered.
    EvidenceOnly,
}

impl Inputs {
    pub fn runs(self) -> bool {
        self != Inputs::EvidenceOnly
    }

    /// The argument lists this fixture is driven with.
    pub fn grid(self) -> Vec<Vec<i64>> {
        match self {
            Inputs::EvidenceOnly => Vec::new(),
            Inputs::Nullary => vec![Vec::new()],
            Inputs::Unary => BOUNDARY.iter().map(|x| vec![*x]).collect(),
            Inputs::Binary => BOUNDARY
                .iter()
                .flat_map(|x| BOUNDARY_SECOND.iter().map(move |y| vec![*x, *y]))
                .collect(),
            Inputs::Recursive => RECURSION
                .iter()
                .flat_map(|x| RECURSION_SECOND.iter().map(move |y| vec![*x, *y]))
                .chain(std::iter::once(vec![DEEP.0, DEEP.1]))
                .collect(),
            Inputs::Tree => TREE.iter().map(|x| vec![*x, TREE_SECOND]).collect(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Fixture {
    /// The occurrence name in `compiler/canary/Canary.hs`.
    pub occ: &'static str,
    pub inputs: Inputs,
    /// Required exit code, independent of oracle/candidate agreement.
    /// Expected failures must opt in to their exact code; signals never pass.
    pub expected_exit: i32,
    /// Which profiles this entry is compiled and run in. Not every shape
    /// survives into both dumps, and an entry whose subject only exists in one
    /// of them is skipped in the other rather than failing there.
    pub when: When,
    pub evidence: &'static [Check],
}

const fn run(occ: &'static str, inputs: Inputs) -> Fixture {
    Fixture {
        occ,
        inputs,
        expected_exit: 0,
        when: When::Both,
        evidence: &[],
    }
}

const fn prove(occ: &'static str, inputs: Inputs, evidence: &'static [Check]) -> Fixture {
    Fixture {
        occ,
        inputs,
        expected_exit: 0,
        when: When::Both,
        evidence,
    }
}

/// An entry only one profile can compile.
const fn prove_in(
    profile: Profile,
    occ: &'static str,
    inputs: Inputs,
    evidence: &'static [Check],
) -> Fixture {
    Fixture {
        occ,
        inputs,
        expected_exit: 0,
        when: When::Only(profile),
        evidence,
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Entry {
    Occurrence(&'static str),
    Stable(&'static str),
}

/// An entry that must be refused, and the text the refusal must carry.
///
/// A refusal is as much a contract as a result: a wrong answer here would be a
/// miscompile rather than a missing feature, and the message is what says the
/// compiler stopped for the reason we think it did.
#[derive(Debug, Clone, Copy)]
pub struct Refusal {
    pub entry: Entry,
    pub when: When,
    /// `None` where only the refusal is contracted. `main` is refused for
    /// whichever of its several unsupported shapes the pass reaches first, and
    /// that moves as the blockers behind it are cleared.
    pub because: Option<&'static str>,
}

pub const REFUSALS: &[Refusal] = &[
    Refusal {
        entry: Entry::Stable("$main$Main$main"),
        when: When::Both,
        because: None,
    },
    // A value defined in terms of itself is refused for its dependency cycle.
    Refusal {
        entry: Entry::Occurrence("recursiveValue"),
        when: When::Both,
        because: Some("recursive value dependency closure is not supported"),
    },
    Refusal {
        entry: Entry::Occurrence("recursiveValueUse"),
        when: When::Both,
        because: Some("recursive value dependency closure is not supported"),
    },
    Refusal {
        entry: Entry::Occurrence("colourEqual"),
        when: When::Only(Profile::Unoptimized),
        because: Some("imported binding is outside the loaded world"),
    },
    Refusal {
        entry: Entry::Occurrence("colourCompare"),
        when: When::Only(Profile::Unoptimized),
        because: Some("imported binding is outside the loaded world"),
    },
    Refusal {
        entry: Entry::Occurrence("elemString"),
        when: When::Only(Profile::Unoptimized),
        because: Some("an Eq dictionary this backend does not implement"),
    },
    Refusal {
        entry: Entry::Occurrence("mapLookup"),
        when: When::Only(Profile::Unoptimized),
        because: Some("imported binding is outside the loaded world"),
    },
    Refusal {
        entry: Entry::Occurrence("mapUnion"),
        when: When::Only(Profile::Unoptimized),
        because: Some("imported binding is outside the loaded world"),
    },
    Refusal {
        entry: Entry::Occurrence("patternFail"),
        when: When::Both,
        because: Some("unimplemented non-returning call"),
    },
    Refusal {
        entry: Entry::Occurrence("undefinedUnused"),
        when: When::Both,
        because: Some("imported binding is outside the loaded world"),
    },
    // `$fMonadStateT`'s `return` field is a cast lambda.
    Refusal {
        entry: Entry::Occurrence("stateCollect"),
        when: When::Both,
        because: Some("instance has more type arguments than the owner binds"),
    },
    Refusal {
        entry: Entry::Occurrence("stateNumber"),
        when: When::Both,
        because: Some("instance has more type arguments than the owner binds"),
    },
    Refusal {
        entry: Entry::Occurrence("writerCollect"),
        when: When::Only(Profile::Optimized),
        because: Some("reference is neither a parameter nor a top-level binding"),
    },
    Refusal {
        entry: Entry::Occurrence("writerCollect"),
        when: When::Only(Profile::Unoptimized),
        because: Some("instance has more type arguments than the owner binds"),
    },
    Refusal {
        entry: Entry::Occurrence("stateClass"),
        when: When::Both,
        because: Some("instance has more type arguments than the owner binds"),
    },
    Refusal {
        entry: Entry::Occurrence("rwsRecord"),
        when: When::Both,
        because: Some("type arguments must precede value arguments"),
    },
    Refusal {
        entry: Entry::Occurrence("identityWalk"),
        when: When::Only(Profile::Unoptimized),
        because: Some("value applications are not lowered yet"),
    },
];

/// Forced stack-free errors checked against the oracle and both Rust modes.
#[derive(Debug, Clone, Copy)]
pub struct Probe {
    pub entry: &'static str,
    pub input: i64,
    pub message: Option<&'static [u8]>,
    pub when: When,
    /// The message is followed by a call stack, whose source locations are
    /// this compilation's and are read from the oracle's own output.
    pub located: bool,
}

const fn probe(entry: &'static str, input: i64, message: Option<&'static [u8]>) -> Probe {
    Probe {
        entry,
        input,
        message,
        when: When::Both,
        located: false,
    }
}

const fn optimized_probe(entry: &'static str, input: i64, message: &'static [u8]) -> Probe {
    Probe {
        entry,
        input,
        message: Some(message),
        when: When::Only(Profile::Optimized),
        located: false,
    }
}

const fn located_probe(
    when: When,
    entry: &'static str,
    input: i64,
    message: &'static [u8],
) -> Probe {
    Probe {
        entry,
        input,
        message: Some(message),
        when,
        located: true,
    }
}

pub const ERROR_PROBES: &[Probe] = &[
    probe("errorPlain", 0, Some(b"canary failure")),
    probe("errorUnboxed", 0, Some(b"canary failure")),
    probe("errorEmpty", 0, Some(b"")),
    probe("errorUnicode", 0, Some("fout: λ 🐚".as_bytes())),
    probe("errorMultiline", 0, Some(b"first\nsecond\n")),
    probe("errorNul", 0, Some(b"a")),
    probe("errorChar", 65, Some(b"Atail")),
    probe("errorChar", 0, Some(b"")),
    probe("errorChar", 0xd800, Some(b"tail")),
    probe("errorChar", 0x110000, Some(b"\xf4\x90\x80\x80tail")),
    probe("errorChar", -1, Some(b"\xef\xbf\xbf\xbftail")),
    probe("errorNulNested", 0, Some(b"inner after NUL")),
    probe("errorNestedMessage", 0, Some(b"inner")),
    probe("errorComputed", 0, Some("computed: λ 🐚".as_bytes())),
    probe("errorComputed", 1, Some("other: λ 🐚".as_bytes())),
    probe("errorBranch", 0, Some("computed: λ 🐚".as_bytes())),
    probe("errorBranch", 1, None),
    probe("errorBranch", -1, None),
    probe("eqSpineOrder", 0, Some(b"left spine")),
    probe("eqRightSpine", 0, Some(b"right spine")),
    probe("eqElementOrder", 0, Some(b"left char")),
    probe("elemSpineFirst", 0, Some(b"spine")),
    probe("elemNeedleOrder", 0, Some(b"needle")),
    probe("elemNeedleUnused", 0, None),
    probe("elemNeedleUnused", 1, Some(b"needle")),
    probe("prefixOrder", 0, Some(b"prefix spine")),
    probe("prefixListOrder", 0, Some(b"list spine")),
    probe("prefixElementOrder", 0, Some(b"prefix char")),
    optimized_probe("compareSpineOrder", 0, b"left spine"),
    optimized_probe("compareRightSpine", 0, b"right spine"),
    optimized_probe("compareElementOrder", 0, b"left char"),
    probe("tagForced", 0, Some(b"tagged")),
    probe("mapSpine", 0, Some(b"list spine")),
    probe("mapFunctionForced", 0, Some(b"map function")),
    probe("filterPredicate", 0, Some(b"filter predicate")),
    probe("takeWhileElement", 0, Some(b"list element")),
    probe("dropWhileSpine", 0, Some(b"list spine")),
    probe("reverseTail", 0, Some(b"list tail")),
    probe("lengthTail", 0, Some(b"list tail")),
    probe("consAppendRight", 0, Some(b"list spine")),
    probe("consAppendRight", 2, Some(b"list spine")),
    located_probe(When::Both, "errorCall", 0, b"canary error"),
    located_probe(When::Both, "errorCallComputed", 2, b"mab"),
    located_probe(When::Both, "errorCallComputed", 0, b"m"),
    located_probe(
        When::Only(Profile::Optimized),
        "setFindMin",
        5,
        b"Set.findMin: empty set has no minimal element",
    ),
];

/// One exported ShellCheck binding, the argument lists it is run with, and
/// nothing else: its Core is ShellCheck's own, not a fixture written for it.
#[derive(Debug, Clone, Copy)]
pub struct Library {
    pub name: &'static str,
    pub inputs: &'static [&'static [&'static str]],
}

impl Library {
    /// The name the oracle driver dispatches on.
    pub fn occ(&self) -> &'static str {
        self.name.rsplit('$').next().unwrap_or(self.name)
    }
}

const CONSTANT: &[&[&str]] = &[&[]];

const OPERATORS: &[&[&str]] = &[
    &[""],
    &["-eq"],
    &["-ne"],
    &["-lt"],
    &["-le"],
    &["-gt"],
    &["-ge"],
    &["-EQ"],
    &["eq"],
    &["-eq "],
    &["-e"],
    &["-equal"],
    &["-\u{e9}q"],
    &["λ"],
];

const EXECUTABLES: &[&[&str]] = &[
    &[""],
    &["sh"],
    &["bash"],
    &["bats"],
    &["busybox"],
    &["busybox sh"],
    &["busybox ash"],
    &["dash"],
    &["ash"],
    &["ksh"],
    &["ksh93"],
    &["zsh"],
    &["Bash"],
    &["bash "],
    &["/bin/sh"],
    &["🐚"],
];

const fn library(occ: &'static str, inputs: &'static [&'static [&'static str]]) -> Library {
    Library { name: occ, inputs }
}

pub const LIBRARY: &[Library] = &[
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.AnalyzerLib$isDereferencingBinaryOp",
        OPERATORS,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$shellForExecutable",
        EXECUTABLES,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$internalVariables",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$specialIntegerVariables",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$specialVariablesWithoutSpaces",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$arrayVariables",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$commonCommands",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$nonReadingCommands",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$sampleWords",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$binaryTestOps",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$arithmeticBinaryTestOps",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$unaryTestOps",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$flagsForRead",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$flagsForMapfile",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$declaringCommands",
        CONSTANT,
    ),
    library(
        "$ShellCheck-0.11.0-inplace$ShellCheck.Data$privilegeElevationCommands",
        CONSTANT,
    ),
];

/// Every fixture, in the order the report prints them.
pub const FIXTURES: &[Fixture] = &[
    run("errorLazyArgument", Inputs::Binary),
    run("errorLazyShared", Inputs::Binary),
    run("errorLazyField", Inputs::Binary),
    // Scalar arithmetic, comparison and control flow.
    run("constant", Inputs::Unary),
    run("forward", Inputs::Binary),
    run("add", Inputs::Binary),
    run("subtractInt", Inputs::Binary),
    run("multiply", Inputs::Binary),
    run("composed", Inputs::Binary),
    run("chained", Inputs::Binary),
    run("shared", Inputs::Binary),
    run("eqInt", Inputs::Binary),
    run("neInt", Inputs::Binary),
    run("ltInt", Inputs::Binary),
    run("leInt", Inputs::Binary),
    run("gtInt", Inputs::Binary),
    run("geInt", Inputs::Binary),
    run("minimumInt", Inputs::Binary),
    run("selectInt", Inputs::Binary),
    run("nestedBranch", Inputs::Binary),
    // Non-tail control flow: the branch is a region the caller resumes from.
    // `-O1` floats each branch into tail position, so the region it is
    // resumed from exists only in the unoptimised dump.
    prove(
        "operandBranches",
        Inputs::Binary,
        &[unoptimized_op(Op::EvaluateBlock)],
    ),
    prove(
        "scrutineeBranch",
        Inputs::Binary,
        &[unoptimized_op(Op::EvaluateBlock)],
    ),
    prove(
        "sharedBranch",
        Inputs::Binary,
        &[unoptimized_op(Op::EvaluateBlock)],
    ),
    prove(
        "branchCall",
        Inputs::Binary,
        &[unoptimized_op(Op::EvaluateBlock)],
    ),
    // Boxed Int.
    run("makeBox", Inputs::Binary),
    run("boxedSum", Inputs::Binary),
    run("boxedIgnore", Inputs::Binary),
    run("boxedChoose", Inputs::Binary),
    run("boxedRoundTrip", Inputs::Binary),
    run("boxedShared", Inputs::Binary),
    run("boxedStrictIgnore", Inputs::Binary),
    run("boxedCaf", Inputs::Nullary),
    // Laziness: a thunk region per delayed computation, and a shared binding
    // where the source bound one.
    prove("lazyArgument", Inputs::Binary, &[op(Op::DelayBlock)]),
    prove(
        "lazyLet",
        Inputs::Binary,
        &[op(Op::DelayBlock), rule(RuleKind::LazyBinding)],
    ),
    prove(
        "lazyNested",
        Inputs::Binary,
        &[op(Op::DelayBlock), rule(RuleKind::LazyBinding)],
    ),
    prove("lazyUnused", Inputs::Binary, &[op(Op::DelayBlock)]),
    prove("lazyBranch", Inputs::Binary, &[op(Op::DelayBlock)]),
    run("lazyStrictUse", Inputs::Binary),
    // Algebraic data.
    run("dataChoice", Inputs::Binary),
    run("dataPair", Inputs::Binary),
    run("dataNested", Inputs::Binary),
    run("dataDefault", Inputs::Binary),
    run("dataLazy", Inputs::Binary),
    run("dataStrict", Inputs::Binary),
    run("dataMaybe", Inputs::Binary),
    run("dataList", Inputs::Binary),
    run("dataCaseBinder", Inputs::Binary),
    // Recursion, local functions and join points.
    run("localJoin", Inputs::Binary),
    run("recursiveList", Inputs::Binary),
    run("localLazy", Inputs::Binary),
    run("recursiveSum", Inputs::Recursive),
    run("mutualRecursion", Inputs::Recursive),
    prove(
        "localLoop",
        Inputs::Recursive,
        &[
            both(Evidence::Operation(Op::LocalScope)),
            both(Evidence::Operation(Op::CallLocal)),
        ],
    ),
    prove(
        "localMutual",
        Inputs::Recursive,
        &[
            both(Evidence::Operation(Op::LocalScope)),
            both(Evidence::Operation(Op::CallLocal)),
        ],
    ),
    run("recursiveTree", Inputs::Tree),
    // Closures and higher-order calls.
    run("higherOrder", Inputs::Binary),
    prove("partialTop", Inputs::Binary, &[op(Op::Apply)]),
    prove("localClosure", Inputs::Binary, &[op(Op::MakeClosure)]),
    run("returnedClosure", Inputs::Binary),
    run("closureBranch", Inputs::Binary),
    run("functionField", Inputs::Binary),
    run("closureUnused", Inputs::Binary),
    prove("escapingRecursive", Inputs::Binary, &[op(Op::MakeClosure)]),
    run("overApplied", Inputs::Binary),
    // Specialization: one source binding, one instance per type it is used at.
    prove(
        "polyTwoTypes",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            both(Evidence::InstancesOf {
                occ: "polyIdentity",
                count: 2,
            }),
        ],
    ),
    prove(
        "polyCrossModule",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            both(Evidence::InstancesOf {
                occ: "crossPoly",
                count: 2,
            }),
        ],
    ),
    prove(
        "polyHigherOrder",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            both(Evidence::InstancesOf {
                occ: "crossApply",
                count: 2,
            }),
        ],
    ),
    // A recursive polymorphic function: two instances, each reusing itself.
    prove(
        "polyRecursive",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            both(Evidence::InstancesOf {
                occ: "polyCount",
                count: 2,
            }),
        ],
    ),
    prove(
        "polyNested",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            both(Evidence::InstancesOf {
                occ: "firstOfPair",
                count: 2,
            }),
        ],
    ),
    // Typeclasses. No method survives as a dispatch through its selector; each
    // was resolved to the instance's own method.
    prove(
        "classTwoInstances",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            both(Evidence::InstancesOf {
                occ: "size",
                count: 0,
            }),
            unoptimized(Evidence::ClosureRule(RuleKind::ResolveMethod)),
        ],
    ),
    // A default method, a superclass field read and a dictionary built from
    // another dictionary each specialize on the dictionary itself.
    prove(
        "classDefaultMethod",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            unoptimized(Evidence::ClosureRule(RuleKind::ResolveMethod)),
            unoptimized(Evidence::SpecializedOn {
                type_arguments: 1,
                dictionaries: 1,
            }),
        ],
    ),
    prove(
        "classSuperclass",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            unoptimized(Evidence::ClosureRule(RuleKind::ResolveMethod)),
            unoptimized(Evidence::SpecializedOn {
                type_arguments: 1,
                dictionaries: 1,
            }),
        ],
    ),
    prove(
        "classCrossModule",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            unoptimized(Evidence::ClosureRule(RuleKind::ResolveMethod)),
            unoptimized(Evidence::SpecializedOn {
                type_arguments: 1,
                dictionaries: 1,
            }),
        ],
    ),
    prove(
        "classParameterized",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            unoptimized(Evidence::ClosureRule(RuleKind::ResolveMethod)),
            unoptimized(Evidence::SpecializedOn {
                type_arguments: 1,
                dictionaries: 1,
            }),
        ],
    ),
    prove(
        "classMethodValue",
        Inputs::Binary,
        &[
            both(Evidence::InstancesComplete),
            unoptimized(Evidence::ClosureRule(RuleKind::ResolveMethod)),
        ],
    ),
    // Characters.
    prove(
        "charRoundTrip",
        Inputs::Binary,
        &[unoptimized_op(Op::OrdChar), unoptimized_op(Op::ChrChar)],
    ),
    prove("charOrder", Inputs::Binary, &[op(Op::CharCompare)]),
    // A Char# scrutinee reaches the same scalar switch an Int# does.
    prove(
        "charSwitch",
        Inputs::Binary,
        &[unoptimized(Evidence::ScalarSwitch)],
    ),
    // A `let` at an unboxed type is Core's strict binding, not a thunk.
    prove(
        "charField",
        Inputs::Binary,
        &[
            unoptimized_op(Op::OrdChar),
            unoptimized_rule(RuleKind::StrictBinding),
        ],
    ),
    // String literals.
    prove(
        "stringLength",
        Inputs::Binary,
        &[anywhere(Op::UnpackString)],
    ),
    run("stringIndex", Inputs::Binary),
    run("stringEmpty", Inputs::Binary),
    run("stringLazyHead", Inputs::Binary),
    prove(
        "stringUnicode",
        Inputs::Binary,
        &[anywhere(Op::UnpackString)],
    ),
    run("stringUnicodeIndex", Inputs::Binary),
    run("stringCount", Inputs::Binary),
    run("stringHighLatin1", Inputs::Binary),
    run("stringNulByte", Inputs::Binary),
    // At `-O1` GHC folds two adjacent literals into one, so `stringAppend`
    // covers the folded form and `stringAppendShared`, whose tail cannot be
    // folded in, is what reaches the appending unpacker.
    prove(
        "stringAppend",
        Inputs::Binary,
        &[unoptimized_op(Op::AppendList)],
    ),
    prove(
        "stringAppendShared",
        Inputs::Binary,
        &[
            optimized(Evidence::ClosureOperation(Op::UnpackStringOnto)),
            unoptimized(Evidence::ClosureOperation(Op::AppendList)),
        ],
    ),
    // A literal a program reads twice is one CAF, so the generated code holds
    // one shared value and decodes the bytes once rather than per use.
    prove(
        "stringShared",
        Inputs::Binary,
        &[
            both(Evidence::Emitted("std::thread_local!")),
            both(Evidence::Emitted("unpack_literal")),
        ],
    ),
    run("stringUnused", Inputs::Binary),
    // Newtypes: GHC turns every wrap and unwrap into a cast.
    prove(
        "newtypeRoundTrip",
        Inputs::Binary,
        &[op(Op::Move), rule(RuleKind::EraseCast)],
    ),
    run("newtypeField", Inputs::Binary),
    prove("newtypeFunction", Inputs::Binary, &[op(Op::Apply)]),
    prove(
        "newtypeMonad",
        Inputs::Binary,
        &[both(Evidence::SpecializedOn {
            type_arguments: 2,
            dictionaries: 0,
        })],
    ),
    // Text-processing programs: whole algorithms over `[Char]`, not single
    // operations. Each walks a literal end to end and builds new cells as it
    // goes, so a defect in the string machinery is a wrong answer here rather
    // than a refusal.
    prove("textWords", Inputs::Binary, &[anywhere(Op::UnpackString)]),
    prove("textLines", Inputs::Binary, &[anywhere(Op::UnpackString)]),
    prove(
        "textUnicodeWords",
        Inputs::Binary,
        &[anywhere(Op::UnpackString)],
    ),
    prove("textFind", Inputs::Binary, &[anywhere(Op::UnpackString)]),
    prove("textReverse", Inputs::Binary, &[anywhere(Op::Construct)]),
    prove("textFilter", Inputs::Binary, &[anywhere(Op::Construct)]),
    prove("textMap", Inputs::Binary, &[anywhere(Op::Construct)]),
    // The one that reads both inputs, so every boundary pair slices
    // differently rather than repeating one answer 49 times.
    prove("textSlice", Inputs::Binary, &[anywhere(Op::Construct)]),
    prove("textZip", Inputs::Binary, &[anywhere(Op::UnpackString)]),
    prove("textCompare", Inputs::Binary, &[anywhere(Op::UnpackString)]),
    prove("stringEqual", Inputs::Binary, &[anywhere(EQ_STRING)]),
    prove_in(
        Profile::Optimized,
        "stringEqualRule",
        Inputs::Binary,
        &[anywhere(EQ_STRING)],
    ),
    prove("stringEqualLazy", Inputs::Binary, &[anywhere(EQ_STRING)]),
    prove("elemChar", Inputs::Binary, &[anywhere(ELEM_CHAR)]),
    prove_in(
        Profile::Optimized,
        "elemString",
        Inputs::Binary,
        &[anywhere(Op::ListPredicate(
            Predicate::Elem,
            Equality::String,
        ))],
    ),
    prove("elemLazy", Inputs::Binary, &[anywhere(ELEM_CHAR)]),
    prove("prefixOf", Inputs::Binary, &[anywhere(PREFIX_CHAR)]),
    prove("prefixLazy", Inputs::Binary, &[anywhere(PREFIX_CHAR)]),
    prove("mapChars", Inputs::Binary, &[anywhere(MAP)]),
    prove("mapInts", Inputs::Binary, &[anywhere(MAP)]),
    prove("mapFunctions", Inputs::Binary, &[anywhere(MAP)]),
    prove("mapLazy", Inputs::Binary, &[anywhere(MAP)]),
    prove("mapUnapplied", Inputs::Binary, &[anywhere(MAP)]),
    prove("filterChars", Inputs::Binary, &[anywhere(FILTER)]),
    prove("filterLazy", Inputs::Binary, &[anywhere(FILTER)]),
    prove("takeWhileChars", Inputs::Binary, &[anywhere(TAKE_WHILE)]),
    prove("takeWhileLazy", Inputs::Binary, &[anywhere(TAKE_WHILE)]),
    prove("dropWhileChars", Inputs::Binary, &[anywhere(DROP_WHILE)]),
    prove("dropWhileLazy", Inputs::Binary, &[anywhere(DROP_WHILE)]),
    // `-O1` inlines `reverse` to its `reverse1` loop and rewrites `(x : xs) ++ ys`
    // by base's `SC:++0`; `-O0` calls `reverse` and `(++)` themselves.
    prove("reverseChars", Inputs::Binary, REVERSE),
    prove("reverseLazy", Inputs::Binary, REVERSE),
    prove(
        "lengthChars",
        Inputs::Binary,
        &[optimized(Evidence::ClosureOperation(Op::ListFunction(
            ListOp::Length,
        )))],
    ),
    prove(
        "lengthLazy",
        Inputs::Binary,
        &[optimized(Evidence::ClosureOperation(Op::ListFunction(
            ListOp::Length,
        )))],
    ),
    prove("consAppend", Inputs::Binary, CONS_APPEND),
    prove("consAppendLazy", Inputs::Binary, CONS_APPEND),
    prove(
        "shifts",
        Inputs::Binary,
        &[
            anywhere(Op::Int(IntBinary::ShiftLeft)),
            anywhere(Op::Int(IntBinary::ShiftRightArithmetic)),
        ],
    ),
    prove("wordOrder", Inputs::Binary, &[anywhere(Op::WordCompare)]),
    prove(
        "magicLazy",
        Inputs::Binary,
        &[both(Evidence::Rule(RuleKind::MagicLazy))],
    ),
    // `-O0` keeps the pattern-match failure join, which takes `(##)`.
    prove(
        "voidJoin",
        Inputs::Binary,
        &[unoptimized(Evidence::ClosureOperation(
            Op::MakeUnboxedTuple,
        ))],
    ),
    // containers, compiled from source into the world. `-O0` reaches `Ord Int`
    // through ghc-prim's dictionary, which the world does not contain yet.
    prove_in(
        Profile::Optimized,
        "setSize",
        Inputs::Binary,
        &[anywhere(Op::PointerEquality)],
    ),
    prove_in(
        Profile::Optimized,
        "setMember",
        Inputs::Binary,
        &[anywhere(Op::PointerEquality)],
    ),
    prove_in(
        Profile::Optimized,
        "setOrder",
        Inputs::Binary,
        &[anywhere(Op::PointerEquality)],
    ),
    prove_in(
        Profile::Optimized,
        "mapStrings",
        Inputs::Binary,
        &[anywhere(Op::CompareStrings)],
    ),
    // `Identity`'s `Functor` and `Applicative` methods are casts of top-level bindings.
    prove_in(
        Profile::Optimized,
        "identityWalk",
        Inputs::Binary,
        &[
            optimized(Evidence::SpecializedOn {
                type_arguments: 1,
                dictionaries: 1,
            }),
            optimized(Evidence::InstancesComplete),
        ],
    ),
    prove_in(
        Profile::Optimized,
        "mapLookup",
        Inputs::Binary,
        &[optimized(Evidence::InstancesComplete)],
    ),
    prove_in(
        Profile::Optimized,
        "mapUnion",
        Inputs::Binary,
        &[optimized(Evidence::InstancesComplete)],
    ),
    prove("tagColour", Inputs::Binary, &[anywhere(Op::DataToTag)]),
    prove("tagMaybe", Inputs::Binary, &[anywhere(Op::DataToTag)]),
    prove_in(
        Profile::Optimized,
        "colourEqual",
        Inputs::Binary,
        &[anywhere(Op::DataToTag), anywhere(Op::TagToEnum)],
    ),
    prove_in(
        Profile::Optimized,
        "colourCompare",
        Inputs::Binary,
        &[anywhere(Op::DataToTag)],
    ),
    prove(
        "pointerChoice",
        Inputs::Binary,
        &[anywhere(Op::PointerEquality)],
    ),
    prove_in(
        Profile::Optimized,
        "compareStrings",
        Inputs::Binary,
        &[anywhere(Op::CompareStrings)],
    ),
    prove_in(
        Profile::Optimized,
        "compareLazy",
        Inputs::Binary,
        &[anywhere(Op::CompareStrings)],
    ),
    prove_in(
        Profile::Optimized,
        "compareUnsigned",
        Inputs::Binary,
        &[anywhere(Op::CompareStrings)],
    ),
    // Unboxed tuples: GHC's multi-value return. No box, no tag, no
    // allocation, and a `case` that binds components and branches nowhere.
    prove(
        "tupleRoundTrip",
        Inputs::Binary,
        &[anywhere(Op::MakeUnboxedTuple), op(Op::UnboxedTupleField)],
    ),
    prove("tupleSwap", Inputs::Binary, &[op(Op::UnboxedTupleField)]),
    prove(
        "tupleSolo",
        Inputs::Binary,
        &[anywhere(Op::MakeUnboxedTuple), op(Op::UnboxedTupleField)],
    ),
    prove(
        "tupleWide",
        Inputs::Binary,
        &[anywhere(Op::MakeUnboxedTuple), op(Op::UnboxedTupleField)],
    ),
    prove(
        "tupleBoxed",
        Inputs::Binary,
        &[anywhere(Op::MakeUnboxedTuple), op(Op::UnboxedTupleField)],
    ),
    prove(
        "tupleNested",
        Inputs::Binary,
        &[anywhere(Op::MakeUnboxedTuple), op(Op::UnboxedTupleField)],
    ),
    prove(
        "tupleLazyComponent",
        Inputs::Binary,
        &[op(Op::UnboxedTupleField)],
    ),
    prove(
        "tupleUnusedComponent",
        Inputs::Binary,
        &[op(Op::UnboxedTupleField)],
    ),
    // `error`, bound and never demanded: the call is built and never raised.
    prove(
        "errorUnusedArgument",
        Inputs::Binary,
        &[anywhere(Op::RaiseCallStackError)],
    ),
    prove(
        "errorUnusedLet",
        Inputs::Binary,
        &[anywhere(Op::RaiseCallStackError)],
    ),
    prove(
        "errorUnusedShared",
        Inputs::Binary,
        &[anywhere(Op::RaiseCallStackError)],
    ),
    // GHC calls its wired-in `patError` at more type arguments than base's definition binds.
    prove(
        "patternFail",
        Inputs::EvidenceOnly,
        &[both(Evidence::ClosureRule(RuleKind::Diverge))],
    ),
    // Bindings that are not entry points: they exist so the shapes they
    // contain are lowered and checked.
    prove("chooseData", Inputs::EvidenceOnly, &[op(Op::Construct)]),
    prove("readData", Inputs::EvidenceOnly, &[op(Op::MatchData)]),
    prove("readNested", Inputs::EvidenceOnly, &[op(Op::MatchData)]),
    prove("readMaybe", Inputs::EvidenceOnly, &[op(Op::MatchData)]),
    prove("listFirst", Inputs::EvidenceOnly, &[op(Op::MatchData)]),
    prove("applyInt", Inputs::EvidenceOnly, &[op(Op::Apply)]),
    prove(
        "makeAdder",
        Inputs::EvidenceOnly,
        &[unoptimized_op(Op::MakeClosure)],
    ),
];

/// The signed-64-bit boundary grid every entry's first argument runs over.
pub const BOUNDARY: &[i64] = &[i64::MIN, -100, -1, 0, 1, 42, i64::MAX];

/// The second argument's grid.
pub const BOUNDARY_SECOND: &[i64] = &[i64::MIN, -17, -1, 0, 1, 23, i64::MAX];

/// Recursion runs over small depths, where the answer is checkable by hand.
pub const RECURSION: &[i64] = &[-1, 0, 1, 2, 7, 100];
pub const RECURSION_SECOND: &[i64] = &[-17, 0, 23];

/// Tree recursion, against a fixed second argument.
pub const TREE: &[i64] = &[-1, 0, 1, 2, 7];
pub const TREE_SECOND: i64 = 23;

/// Deep enough that a scalar tail call growing a native stack would be seen.
pub const DEEP: (i64, i64) = (1_000_000, 1);
