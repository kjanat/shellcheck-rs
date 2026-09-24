//! Typed, source-attributed scalar and algebraic control flow.
//!
//! `lower::lower_leaf` translates a restricted subset of Core leaves.
//! Direct and closure calls, explicit captures and constructor families are
//! supported; recursive thunk graphs remain outside this subset.
//! Values cross block boundaries explicitly through block parameters; there
//! are no implicit captures. IDs are function-local except for `FnId`, which
//! will be allocated by the program lowering driver.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use h2r_core_ir::{BinderId, ExprId, Lit, Module, Ty, TyVarId};

/// The modules one pass may read. Constructor layouts, imported bindings and
/// class evidence are whole-world facts: a function specialized at a type from
/// another module needs that module's evidence, not its own module's.
/// Without a loaded world the only readable module is the one being lowered,
/// and anything cross-module refuses rather than guessing.
#[derive(Clone, Copy)]
pub struct World<'a> {
    pub module: &'a Module,
    pub index: usize,
    pub modules: Option<&'a [Module]>,
    pub catalog: Option<&'a Catalog>,
}

pub struct Catalog {
    tops: HashMap<String, Option<(usize, BinderId)>>,
    families: HashMap<String, Vec<(usize, usize)>>,
    declaring: RefCell<HashMap<String, Result<Option<usize>, String>>>,
}

impl Catalog {
    pub fn of(modules: &[Module]) -> Catalog {
        let mut tops: HashMap<String, Option<(usize, BinderId)>> = HashMap::new();
        let mut families: HashMap<String, Vec<(usize, usize)>> = HashMap::new();
        for (index, module) in modules.iter().enumerate() {
            for pair in module.top.iter().flat_map(|group| &group.pairs) {
                tops.entry(module.binder(pair.binder).name.clone())
                    .and_modify(|found| *found = None)
                    .or_insert(Some((index, pair.binder)));
            }
            for (position, constructor) in module.constructors.iter().enumerate() {
                families
                    .entry(constructor.family.clone())
                    .or_default()
                    .push((index, position));
            }
        }
        Catalog {
            tops,
            families,
            declaring: RefCell::default(),
        }
    }

    pub(crate) fn top(&self, name: &str) -> Option<Option<(usize, BinderId)>> {
        self.tops.get(name).copied()
    }

    pub(crate) fn family(&self, name: &str) -> &[(usize, usize)] {
        self.families.get(name).map_or(&[], Vec::as_slice)
    }

    pub(crate) fn declaring(&self, name: &str) -> Option<Result<Option<usize>, String>> {
        self.declaring.borrow().get(name).cloned()
    }

    pub(crate) fn declare(&self, name: &str, module: Result<Option<usize>, String>) {
        self.declaring.borrow_mut().insert(name.to_string(), module);
    }
}

impl<'a> World<'a> {
    pub fn of(modules: &'a [Module], index: usize) -> Result<World<'a>, String> {
        Ok(World {
            module: modules
                .get(index)
                .ok_or("module index is outside the loaded world")?,
            index,
            modules: Some(modules),
            catalog: None,
        })
    }

    pub fn cataloged(
        modules: &'a [Module],
        index: usize,
        catalog: &'a Catalog,
    ) -> Result<World<'a>, String> {
        Ok(World {
            catalog: Some(catalog),
            ..World::of(modules, index)?
        })
    }

    pub fn at(&self, index: usize) -> Result<&'a Module, String> {
        match self.modules {
            Some(modules) => modules
                .get(index)
                .ok_or_else(|| "module index is outside the loaded world".into()),
            None if index == self.index => Ok(self.module),
            None => Err("cross-module evidence requires a loaded world".into()),
        }
    }

    /// Every readable module, with its index.
    pub fn iter(&self) -> Box<dyn Iterator<Item = (usize, &'a Module)> + '_> {
        match self.modules {
            Some(modules) => Box::new(modules.iter().enumerate()),
            None => Box::new(std::iter::once((self.index, self.module))),
        }
    }
}

pub(crate) mod boxed;
pub mod data;
mod dict;
pub mod diverge;
pub mod external;
mod instantiate;
mod linkage;
pub mod lower;
pub mod pretty;
mod primitive;
pub mod program;
pub mod specialize;
pub mod strings;
pub mod subst;
pub mod verify;
mod view;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FnId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Source {
    Expr(ExprId),
    Binder(BinderId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    Literal,
    TopReference,
    InstantiateTop,
    CallTop,
    IntBinary,
    EraseCast,
    StrictPosition,
    Return,
    Jump,
    IntSwitch,
    EvaluateBlock,
    BoxInt,
    UnboxInt,
    DelayBlock,
    LazyBinding,
    /// A `let` at an unboxed type: Core's strict binding, evaluated in place.
    StrictBinding,
    Construct,
    MakeUnboxedTuple,
    /// A `case` on an unboxed tuple, which binds its components and branches
    /// nowhere: the family has exactly one constructor.
    UnboxedTupleField,
    MatchData,
    LocalScope,
    CallLocal,
    MakeClosure,
    Apply,
    /// An application spine whose value arguments were all proven-unique
    /// dictionaries, so the spine denotes one instance and nothing else.
    ResolveInstance,
    /// A class method selector applied to a proven-unique dictionary,
    /// resolved to that instance's method.
    ResolveMethod,
    CharCompare,
    WordCompare,
    WordBinary,
    IntToWord,
    WordToInt,
    NegateInt,
    IndexCharAddr,
    PlusAddr,
    AddrLiteral,
    RecursiveCell,
    FillCell,
    Machine,
    RunRW,
    InstantiateValue,
    OrdChar,
    ChrChar,
    UnpackString,
    AppendList,
    ListPredicate,
    ListFunction,
    CompareStrings,
    DataToTag,
    TagToEnum,
    PointerEquality,
    /// `GHC.Magic.lazy`: its argument, moved.
    MagicLazy,
    RaiseError,
    EmptyCase,
    /// A call GHC's demand analysis proved never returns.
    Diverge,
}

#[derive(Debug, Clone)]
pub struct Origin {
    pub module: usize,
    pub source: Source,
    pub rule: Rule,
}

/// Retain the complete source type, including opaque shapes, until carrier
/// selection supplies a Rust representation. Never infer types from text.
#[derive(Debug, Clone)]
pub struct Value {
    pub id: ValueId,
    pub ty: Arc<Ty>,
}

thread_local! {
    static SHARED: RefCell<HashSet<Arc<Ty>>> = RefCell::new(HashSet::new());
}

pub fn shared(ty: &Ty) -> Arc<Ty> {
    SHARED.with(|shared| {
        let mut shared = shared.borrow_mut();
        if let Some(existing) = shared.get(ty) {
            return existing.clone();
        }
        let interned = Arc::new(ty.clone());
        shared.insert(interned.clone());
        interned
    })
}

#[derive(Debug, Clone)]
pub enum Operation {
    /// Code plus explicit lexical captures. Function arguments follow captures
    /// in the target block; no ambient environment or mutable backpatching.
    MakeClosure {
        target: BlockId,
        arguments: Vec<ValueId>,
    },
    Apply {
        callee: ValueId,
        arguments: Vec<ValueId>,
    },
    /// Lexical function definitions, followed by entering the let body.
    /// Definitions capture the surrounding value environment explicitly.
    LocalScope {
        definitions: Vec<LocalDefinition>,
        target: BlockId,
        arguments: Vec<ValueId>,
    },
    CallLocal {
        target: BlockId,
        arguments: Vec<ValueId>,
    },
    Construct {
        constructor: data::Constructor,
        arguments: Vec<ValueId>,
    },
    /// Build an unboxed tuple: several values side by side, with no box, no
    /// tag and nothing allocated. GHC's own type system guarantees one is
    /// never bound lazily, stored in a lifted field or passed where a value is
    /// expected, so unlike `Construct` there is nothing here to delay and no
    /// field strictness to honour.
    MakeUnboxedTuple {
        arguments: Vec<ValueId>,
    },
    /// One component of an unboxed tuple, by position.
    ///
    /// Not a projection through a heap object and not a forcing: an unboxed
    /// tuple *is* its components, so this only names one of them. It is what a
    /// `case` on an unboxed tuple does, which is why such a case is no control
    /// flow at all.
    UnboxedTupleField {
        tuple: ValueId,
        index: usize,
    },
    /// Force just the outer constructor, then enter exactly one arm. Arm
    /// parameters are captures, case binder, and constructor fields (in order).
    MatchData {
        scrutinee: ValueId,
        arguments: Vec<ValueId>,
        arms: Vec<DataArm>,
    },
    /// Allocate one shared lifted thunk. Explicit captures are retained
    /// without forcing them; the region runs only on demand, at most once.
    DelayBlock {
        target: BlockId,
        arguments: Vec<ValueId>,
    },
    BoxInt(ValueId),
    /// Force a boxed Int to WHNF and extract its strict Int# field.
    UnboxInt(ValueId),
    /// Evaluate a scalar region once and resume at the next instruction with
    /// its result. Captures are explicit arguments, never ambient locals.
    EvaluateBlock {
        target: BlockId,
        arguments: Vec<ValueId>,
    },
    /// Strict machine-Int operations; comparisons produce Int# 0 or 1.
    /// Arithmetic wraps. Both operands and the result are Int#.
    IntBinary {
        op: IntBinary,
        arguments: Vec<ValueId>,
    },
    /// Strict comparison of two Char#; the result is Int# 0 or 1.
    ///
    /// GHC orders `Char#` as an *unsigned* machine word and `chr#` narrows
    /// nothing, so this is the order `Ord Char` has only for values that are
    /// code points. `chr# -1#` is the largest `Char#`, not the smallest.
    CharCompare {
        op: CharCompare,
        arguments: Vec<ValueId>,
    },
    /// Strict unsigned comparison of two Word#; the result is Int# 0 or 1.
    WordCompare {
        op: CharCompare,
        arguments: Vec<ValueId>,
    },
    /// `int2Word#`: the same machine word, read as unsigned.
    IntToWord(ValueId),
    WordBinary {
        op: IntBinary,
        arguments: Vec<ValueId>,
    },
    WordToInt(ValueId),
    NegateInt(ValueId),
    IndexCharAddr {
        arguments: Vec<ValueId>,
    },
    PlusAddr {
        arguments: Vec<ValueId>,
    },
    AddrLiteral(Vec<u8>),
    PendingCell,
    FillCell {
        cell: ValueId,
        value: ValueId,
    },
    Machine {
        op: Machine,
        type_arguments: Vec<Ty>,
        arguments: Vec<ValueId>,
    },
    /// `ord#`: the code point of a Char#, as an Int#.
    OrdChar(ValueId),
    /// `chr#`: an Int# read as a code point. Unchecked and non-narrowing, as
    /// GHC's is: `ord#` after it returns the original word, whatever it was,
    /// and a value outside the Unicode range is the caller's error.
    ChrChar(ValueId),
    /// One of `GHC.CString`'s unpackers applied to a string literal: the whole
    /// spine, because an `Addr#` is not a value this backend carries. The
    /// result is a `[Char]` built on demand, one cell at a time.
    UnpackString(Box<UnpackString>),
    /// `GHC.Base.(++)` at a closed element type. Neither list is forced here;
    /// the result's cells are built as they are demanded, and the right list
    /// is reached, not copied.
    AppendList {
        left: ValueId,
        right: ValueId,
        nil: data::Constructor,
        cons: data::Constructor,
    },
    ListPredicate(Box<ListPredicate>),
    ListFunction(Box<ListFunction>),
    CompareStrings(Box<CompareStrings>),
    /// `GHC.Err.error`: an uncaught `ErrorCall` whose location is the rendered call stack.
    RaiseCallStackError(Box<CallStackError>),
    /// Force a value and return its constructor's position in the family, from zero.
    DataToTag {
        value: ValueId,
        constructors: Vec<data::Constructor>,
    },
    /// The nullary constructor whose position in an enumeration family is this tag.
    TagToEnum {
        tag: ValueId,
        constructors: Vec<data::Constructor>,
    },
    /// 1 when both values are one shared object, without forcing either.
    PointerEquality {
        left: ValueId,
        right: ValueId,
    },
    Literal(Lit),
    /// Evaluate a stack-free exception's String when this computation is entered.
    RaiseError {
        message: ValueId,
    },
    /// Force a scrutinee independently proved not to return.
    EmptyCase {
        scrutinee: ValueId,
    },
    /// Obtain the existing shared value of one instance of a top-level binding
    /// without forcing it, calling it or allocating another copy. This is a
    /// binding identity, not a FnId: the target may be a function, CAF or
    /// recursive thunk. Type and dictionary arguments are compile-time
    /// specialization evidence and carry no runtime operand.
    TopReference {
        module: usize,
        binder: BinderId,
        /// Leading compile-time type arguments, in source application order.
        type_arguments: Vec<Ty>,
        /// Leading dictionary arguments the instance was specialized on.
        dictionaries: Vec<DictionaryRef>,
    },
    /// Saturated direct call when the enclosing function is entered. Parameter
    /// values (possibly lazy), literals and shared top-level references are
    /// passed without pre-forcing. Computed Int# arguments are evaluated first;
    /// computed supported lifted arguments are explicit DelayBlock results.
    /// The target instance is identified independently of whether it has been
    /// lowered; its type and dictionary arguments precede the runtime ones.
    CallTop {
        module: usize,
        binder: BinderId,
        /// Leading compile-time type arguments, in source application order.
        type_arguments: Vec<Ty>,
        /// Leading dictionary arguments the instance was specialized on.
        dictionaries: Vec<DictionaryRef>,
        arguments: Vec<ValueId>,
    },
    Move(ValueId),
    Force(ValueId),
}

/// A dictionary argument an instance was specialized on: itself an instance of
/// a top-level dictionary producer, so a parameterized instance such as
/// `Show [Int]` is `$fShowList` at `[Int]` with `Show Int` as its argument.
/// This is a compile-time identity; it allocates nothing at runtime.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DictionaryRef {
    pub module: usize,
    pub binder: BinderId,
    pub type_arguments: Vec<Ty>,
    pub dictionaries: Vec<DictionaryRef>,
}

impl DictionaryRef {
    /// Two references name the same dictionary when their targets and their
    /// closed type arguments agree up to alpha-equivalence.
    pub fn same(&self, other: &DictionaryRef) -> bool {
        self.module == other.module
            && self.binder == other.binder
            && self.type_arguments.len() == other.type_arguments.len()
            && self.dictionaries.len() == other.dictionaries.len()
            && self
                .type_arguments
                .iter()
                .zip(&other.type_arguments)
                .all(|(a, b)| a.alpha_eq(b))
            && self
                .dictionaries
                .iter()
                .zip(&other.dictionaries)
                .all(|(a, b)| a.same(b))
    }
}

/// Do two instance-argument lists name the same instance?
pub fn same_dictionaries(left: &[DictionaryRef], right: &[DictionaryRef]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| a.same(b))
}

/// Do two type-argument lists name the same instance?
pub fn same_types(left: &[Ty], right: &[Ty]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| a.alpha_eq(b))
}

#[derive(Debug, Clone)]
pub struct LocalDefinition {
    pub binder: BinderId,
    pub target: BlockId,
    pub result_ty: Ty,
}

#[derive(Debug, Clone)]
pub struct DataArm {
    /// None is DEFAULT, which receives no field parameters.
    pub constructor: Option<data::Constructor>,
    pub target: BlockId,
}

/// A string literal and everything needed to build the list it denotes.
/// The constructor layouts come from the loaded world, like every other
/// construction: the runtime is handed the evidence, it does not assume it.
#[derive(Debug, Clone)]
pub struct UnpackString {
    /// The literal's own bytes, as GHC emitted them.
    pub bytes: Vec<u8>,
    pub encoding: strings::Encoding,
    /// What the last cell's tail is: `unpackAppendCString#`'s second argument,
    /// or nothing, which means `[]`.
    pub tail: Option<ValueId>,
    pub nil: data::Constructor,
    pub cons: data::Constructor,
    /// `C#`, which wraps each decoded code point.
    pub character: data::Constructor,
}

/// `eqString`, `elem` or `isPrefixOf`, with the `==` its dictionary supplies.
#[derive(Debug, Clone, PartialEq)]
pub struct ListPredicate {
    pub predicate: Predicate,
    pub equality: external::Equality,
    pub left: ValueId,
    pub right: ValueId,
    pub nil: data::Constructor,
    pub cons: data::Constructor,
    pub character: data::Constructor,
    pub false_: data::Constructor,
    pub true_: data::Constructor,
}

/// `error`'s message and call stack, and the layouts that render the stack.
#[derive(Debug, Clone, PartialEq)]
pub struct CallStackError {
    pub message: ValueId,
    /// The `IP "callStack" CallStack` argument, a `CallStack` once the newtype is peeled.
    pub stack: ValueId,
    pub layouts: CallStackLayouts,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallStackLayouts {
    pub empty: data::Constructor,
    pub push: data::Constructor,
    pub freeze: data::Constructor,
    pub location: data::Constructor,
}

/// A `base` list function at closed types, with the cells it reads and builds.
#[derive(Debug, Clone, PartialEq)]
pub struct ListFunction {
    pub function: ListOp,
    /// The value arguments, in the function's own order.
    pub arguments: Vec<ValueId>,
    /// The cells of the list the function reads.
    pub nil: data::Constructor,
    pub cons: data::Constructor,
    /// `map`'s result cells, which hold its second type argument.
    pub mapped: Option<(data::Constructor, data::Constructor)>,
    /// `False` and `True`, for a function that takes a predicate.
    pub truth: Option<(data::Constructor, data::Constructor)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ListOp {
    Map,
    Filter,
    TakeWhile,
    DropWhile,
    Reverse,
    ReverseOnto,
    Length,
    ConsAppend,
}

impl ListOp {
    pub fn external(self) -> external::External {
        match self {
            ListOp::Map => external::External::Map,
            ListOp::Filter => external::External::Filter,
            ListOp::TakeWhile => external::External::TakeWhile,
            ListOp::DropWhile => external::External::DropWhile,
            ListOp::Reverse => external::External::Reverse,
            ListOp::ReverseOnto => external::External::ReverseOnto,
            ListOp::Length => external::External::Length,
            ListOp::ConsAppend => external::External::ConsAppend,
        }
    }

    pub fn takes_predicate(self) -> bool {
        matches!(self, ListOp::Filter | ListOp::TakeWhile | ListOp::DropWhile)
    }
}

/// `compare` at `[Char]`.
#[derive(Debug, Clone, PartialEq)]
pub struct CompareStrings {
    pub left: ValueId,
    pub right: ValueId,
    pub nil: data::Constructor,
    pub cons: data::Constructor,
    pub character: data::Constructor,
    pub lt: data::Constructor,
    pub eq: data::Constructor,
    pub gt: data::Constructor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Predicate {
    EqString,
    Elem,
    IsPrefixOf,
}

/// A code-point comparison of two Char#.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CharCompare {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Machine {
    XorWord,
    OrWord,
    NotWord,
    NotInt,
    XorInt,
    QuotRemInt,
    Word8ToWord,
    WordToWord8,
    IndexWord8Addr,
    ShiftLeftWord,
    ShiftRightWord,
    ShiftRightLogicalInt,
    PlusWord,
    TimesWord,
    QuotWord,
    RemWord,
    QuotRemWord,
    QuotRemWord2,
    PlusWord2,
    TimesWord2,
    AddWordC,
    SubWordC,
    AddIntC,
    SubIntC,
    MulIntMayOflo,
    TimesInt2,
    Clz,
    Ctz,
    PopCnt,
    NewMutVar,
    ReadMutVar,
    WriteMutVar,
    Raise,
    RaiseDivZero,
    RaiseUnderflow,
    RaiseOverflow,
    AbsentError,
    NoDuplicate,
    Memcpy,
    RealWorld,
    NewByteArray,
    ReadWordArray,
    WriteWordArray,
    IndexWordArray,
    ReadIntArray,
    WriteIntArray,
    IndexIntArray,
    SizeofByteArray,
    GetSizeofMutableByteArray,
    ShrinkMutableByteArray,
    UnsafeFreezeByteArray,
    CopyByteArray,
    CopyMutableByteArray,
    SetByteArray,
    NewArray,
    ReadArray,
    WriteArray,
    IndexArray,
    UnsafeFreezeArray,
    UnsafeThawArray,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntBinary {
    Add,
    Subtract,
    Multiply,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    /// `uncheckedIShiftL#`, masking the count to the word as x86-64's `shl` does.
    ShiftLeft,
    /// `uncheckedIShiftRA#`, masking the count to the word as x86-64's `sar` does.
    ShiftRightArithmetic,
    And,
    Or,
    Quot,
    Rem,
}

#[derive(Debug, Clone)]
pub struct Instruction {
    pub result: Value,
    pub operation: Operation,
    pub origin: Origin,
}

#[derive(Debug, Clone)]
pub enum Exit {
    Return(ValueId),
    Jump {
        target: BlockId,
        args: Vec<ValueId>,
    },
    /// Evaluate exactly one arm. All successor blocks receive the same explicit
    /// environment followed by the evaluated case binder; no implicit captures.
    /// The scrutinee is an unboxed scalar and each pattern is its exact value:
    /// a code point for Char#, the number itself for Int#.
    IntSwitch {
        scrutinee: ValueId,
        arms: Vec<(i64, BlockId)>,
        default: BlockId,
        args: Vec<ValueId>,
    },
    /// A call that does not return, so the block has no successor and produces
    /// no value. The name is the binding GHC would have entered, carried for
    /// the runtime diagnostic; the arguments that would have built GHC's own
    /// message are not evaluated, because this backend does not reproduce it.
    ///
    /// `ty` is the type the call stands in for. A dead end inhabits every
    /// type, so unlike every other exit there is no value to read it off, and
    /// the block's context is the only thing that knows it.
    Diverge {
        name: String,
        ty: Ty,
    },
}

#[derive(Debug, Clone)]
pub struct Terminator {
    pub exit: Exit,
    pub origin: Origin,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub params: Vec<Value>,
    pub instructions: Vec<Instruction>,
    /// Mandatory by construction: an unterminated block cannot be represented.
    pub terminator: Terminator,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub id: FnId,
    pub module: usize,
    pub owner: BinderId,
    /// Quantified variables in source-signature scope. NIR value types retain
    /// that scope even when Core's lambda binders were alpha-renamed.
    pub type_params: Vec<TyVarId>,
    /// Specialization evidence: the closed types this instance's leading
    /// quantifiers were instantiated at, in source binding order. Empty for an
    /// owner lowered at its own signature.
    pub type_arguments: Vec<Ty>,
    /// Specialization evidence: the dictionaries this instance's leading
    /// dictionary lambdas were bound to. They bind no runtime parameter.
    pub dictionaries: Vec<DictionaryRef>,
    pub result_ty: Ty,
    pub entry: BlockId,
    /// The entry block's parameters are the function's arguments.
    pub blocks: Vec<Block>,
}
