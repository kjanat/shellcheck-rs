//! Typed, source-attributed scalar and algebraic control flow.
//!
//! `lower::lower_leaf` translates a restricted subset of Core leaves.
//! Direct and closure calls, explicit captures and constructor families are
//! supported; recursive thunk graphs remain outside this subset.
//! Values cross block boundaries explicitly through block parameters; there
//! are no implicit captures. IDs are function-local except for `FnId`, which
//! will be allocated by the program lowering driver.

use h2r_core_ir::{BinderId, ExprId, Lit, Ty, TyVarId};

pub(crate) mod boxed;
pub mod data;
mod instantiate;
pub mod lower;
pub mod pretty;
mod primitive;
pub mod program;
pub mod verify;
mod world;

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
    Construct,
    MatchData,
    LocalScope,
    CallLocal,
    MakeClosure,
    Apply,
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
    pub ty: Ty,
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
    Literal(Lit),
    /// Obtain the existing shared top-level value without forcing it, calling
    /// it or allocating another copy. This is a binding identity, not a FnId:
    /// the target may be a function, CAF or recursive thunk.
    TopReference {
        module: usize,
        binder: BinderId,
    },
    /// Type-only instantiation of a shared top-level value. No value arguments,
    /// runtime call, evaluation or allocation; retain specialization evidence.
    InstantiateTop {
        module: usize,
        binder: BinderId,
        arguments: Vec<Ty>,
    },
    /// Saturated direct call when the enclosing function is entered. Parameter
    /// values (possibly lazy), literals and shared top-level references are
    /// passed without pre-forcing. Computed Int# arguments are evaluated first;
    /// computed supported lifted arguments are explicit DelayBlock results.
    /// The target is identified independently of whether it has been lowered.
    CallTop {
        module: usize,
        binder: BinderId,
        /// Leading compile-time type arguments, in source application order.
        type_arguments: Vec<Ty>,
        arguments: Vec<ValueId>,
    },
    Move(ValueId),
    Force(ValueId),
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
    IntSwitch {
        scrutinee: ValueId,
        arms: Vec<(i64, BlockId)>,
        default: BlockId,
        args: Vec<ValueId>,
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
    pub result_ty: Ty,
    pub entry: BlockId,
    /// The entry block's parameters are the function's arguments.
    pub blocks: Vec<Block>,
}
