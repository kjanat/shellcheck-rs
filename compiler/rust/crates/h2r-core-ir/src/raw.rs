//! The JSON produced by `h2r-plugin` (format 2), one-to-one.
//!
//! This nested form exists only to be deserialised; every pass works on the
//! flattened [`crate::Module`] instead. Nothing here is walked recursively:
//! the arena builder consumes it piecewise off an explicit stack.

use std::collections::HashMap;

use serde::Deserialize;

pub const FORMAT: u32 = 4;

#[derive(Debug, Deserialize)]
pub struct RawModule {
    pub format: u32,
    pub module: String,
    pub unit: String,
    /// Facts about every Id referenced anywhere in the module, keyed by unique.
    pub ids: HashMap<String, IdInfo>,
    pub binds: Vec<RawBind>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct IdInfo {
    pub name: String,
    pub occ: String,
    pub arity: u32,
    #[serde(rename = "dmdSig")]
    pub dmd_sig: DmdSig,
    #[serde(rename = "isJoinPoint")]
    pub is_join_point: bool,
    /// A type-class method selector: a call through it is dictionary dispatch.
    #[serde(rename = "isClassOp", default)]
    pub is_class_op: bool,
    /// Pretty `IdDetails`, e.g. `[gid[ClassOp]]`, `[gid[DataConWrapper]]`.
    #[serde(default)]
    pub details: String,
    /// Whether the definition is visible (matters for imported ids: without
    /// an unfolding nothing can be specialised or inlined through it).
    #[serde(rename = "hasUnfolding", default)]
    pub has_unfolding: bool,
    #[serde(rename = "dataCon")]
    pub data_con: Option<DataConInfo>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct DataConInfo {
    pub name: String,
    #[serde(rename = "repArity")]
    pub rep_arity: u32,
    pub tag: u32,
    /// One entry per *source* field: `true` if the field is strict.
    #[serde(rename = "strictFields")]
    pub strict_fields: Vec<bool>,
}

/// A GHC demand, decomposed into the three facts that matter to us.
#[derive(Debug, Clone, Deserialize)]
pub struct Demand {
    pub strict: bool,
    pub absent: bool,
    #[serde(rename = "usedOnce")]
    pub used_once: bool,
    pub pretty: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct DmdSig {
    pub args: Vec<Demand>,
    pub diverges: bool,
    pub pretty: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub enum OccInfo {
    Dead,
    Many {
        #[serde(rename = "tailCalled")]
        tail_called: bool,
    },
    Once {
        #[serde(rename = "insideLam")]
        inside_lam: bool,
        branches: u32,
        #[serde(rename = "tailCalled")]
        tail_called: bool,
    },
    LoopBreaker {
        #[serde(rename = "tailCalled")]
        tail_called: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BinderKind {
    Id,
    Tyvar,
}

/// A Core binder. The `Id`-only fields are `None` for type variables.
#[derive(Debug, Clone, Deserialize)]
pub struct Binder {
    pub kind: BinderKind,
    pub name: String,
    pub occ: String,
    pub unique: String,
    #[serde(rename = "type")]
    pub ty: String,

    pub arity: Option<u32>,
    #[serde(rename = "callArity")]
    pub call_arity: Option<u32>,
    pub exported: Option<bool>,
    #[serde(rename = "dmdSig")]
    pub dmd_sig: Option<DmdSig>,
    #[serde(rename = "cprSig")]
    pub cpr_sig: Option<String>,
    /// How *this* binder is demanded at its binding site.
    pub demand: Option<Demand>,
    #[serde(rename = "occInfo")]
    pub occ_info: Option<OccInfo>,
    /// For lambda binders: GHC proved the lambda is entered at most once.
    #[serde(rename = "oneShot")]
    pub one_shot: Option<bool>,
    pub details: Option<String>,
    #[serde(rename = "hasUnfolding")]
    pub has_unfolding: Option<bool>,
    #[serde(rename = "isJoinPoint")]
    pub is_join_point: Option<bool>,
    #[serde(rename = "isDataCon")]
    pub is_data_con: Option<bool>,
}

#[derive(Debug, Deserialize)]
pub struct RawBind {
    #[serde(rename = "rec")]
    pub recursive: bool,
    pub pairs: Vec<RawPair>,
}

#[derive(Debug, Deserialize)]
pub struct RawPair {
    pub binder: Binder,
    pub rhs: RawExpr,
    pub whnf: bool,
    pub trivial: bool,
    pub cheap: bool,
    #[serde(rename = "okForSpec")]
    pub ok_for_spec: bool,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "node")]
pub enum RawExpr {
    Var {
        name: String,
        occ: String,
        unique: String,
        #[serde(rename = "isGlobal")]
        is_global: bool,
    },
    Lit {
        lit: Lit,
    },
    App {
        fun: Box<RawExpr>,
        arg: Box<RawExpr>,
    },
    Lam {
        binder: Binder,
        body: Box<RawExpr>,
    },
    Let {
        bind: RawBind,
        body: Box<RawExpr>,
    },
    Case {
        scrut: Box<RawExpr>,
        binder: Binder,
        #[serde(rename = "type")]
        ty: String,
        alts: Vec<RawAlt>,
    },
    Cast {
        expr: Box<RawExpr>,
    },
    Tick {
        expr: Box<RawExpr>,
    },
    Type {
        #[serde(rename = "type")]
        ty: String,
    },
    Coercion,
}

#[derive(Debug, Deserialize)]
pub struct RawAlt {
    pub con: AltCon,
    pub binders: Vec<Binder>,
    pub rhs: RawExpr,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind")]
pub enum AltCon {
    DataAlt {
        name: String,
        occ: String,
        tag: u32,
    },
    LitAlt {
        lit: Lit,
    },
    #[serde(rename = "DEFAULT")]
    Default,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Lit {
    pub kind: String,
    pub pretty: String,
}
