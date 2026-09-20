//! First NIR building block: typed, source-attributed scalar control flow.
//!
//! This is not yet a Core lowering pass. Calls, switches, closures and thunk
//! regions will extend this model as their lowering rules are implemented.
//! Values cross block boundaries explicitly through block parameters; there
//! are no implicit captures. IDs are function-local except for `FnId`, which
//! will be allocated by the program lowering driver.

use h2r_core_ir::{BinderId, ExprId, Lit, Ty};

pub mod verify;

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
    EraseCast,
    StrictPosition,
    Return,
    Jump,
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
    Literal(Lit),
    Move(ValueId),
    Force(ValueId),
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
    Jump { target: BlockId, args: Vec<ValueId> },
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
    pub result_ty: Ty,
    pub entry: BlockId,
    /// The entry block's parameters are the function's arguments.
    pub blocks: Vec<Block>,
}
