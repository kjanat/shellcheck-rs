//! The JSON produced by `h2r-plugin` (format 6, and format 5 before it),
//! one-to-one.
//!
//! This nested form exists only to be deserialised; every pass works on the
//! flattened [`crate::Module`] instead. Nothing here is walked recursively:
//! the arena builder consumes it piecewise off an explicit stack.
//!
//! **Format 5 vs format 6.** Format 5 was the program *before* GHC's
//! `CoreTidy`: a top-level binding carried the name it had before tidy
//! externalised it, so a defining module's dump and its clients' dumps
//! disagreed about what to call it. Format 6 is the program *after*
//! `CoreTidy` — the one GHC hands to codegen. Same field names, same
//! shapes; a different contract:
//!
//! * top-level names are the tidied ones, so a stable name links across
//!   modules;
//! * the implicit bindings GHC injects (class-op selectors, data
//!   constructor wrappers) are present, and bindings kept alive only by
//!   rules `CoreTidy` cannot use are gone;
//! * the id table admits only *external* names (an internal stable string
//!   is not unique);
//! * `demand` (on top-level, lambda, case and alternative binders),
//!   `oneShot` (on top-level and let binders) and `exported` are the
//!   *pre-tidy* values, joined back on by the plugin because `CoreTidy`
//!   rebuilds those binders' `IdInfo` from `vanillaIdInfo`; every other
//!   `IdInfo` field is `CoreTidy`'s finalised one;
//! * two new diagnostic fields on top-level binders, [`Binder::external_name`]
//!   and [`Binder::source_exported`]. Nothing reads them yet.
//!
//! Both formats load. No analysis branches on the number; it is recorded on
//! [`crate::Module::format`] and printed by `h2r stats`, so a report always
//! says which contract it was reading.
//!
//! Two things in both formats are *identity*, and both are deliberately not
//! uniques: an imported Id is named by its stable name (`$unit$Module$occ`),
//! and a type constructor likewise. Uniques are still dumped, on `Var`
//! nodes, binders, type variables and type constructors, but only ever as a
//! diagnostic — GHC's simplifier duplicates terms without freshening their
//! binders, so a unique names a binder only within its own scope, and the
//! IR resolves every local occurrence lexically instead
//! ([`crate::Module::resolve`]).

use std::collections::HashMap;

use serde::Deserialize;

use crate::Name;

/// The format the current plugin emits.
pub const FORMAT: u32 = 6;

/// Every format this crate can load. A dump with any other number is
/// refused rather than guessed at.
pub const FORMATS_ACCEPTED: &[u32] = &[5, 6];

/// An index into [`RawModule::types`] / [`crate::Module::types`].
pub type TyId = u32;

#[derive(Debug, Deserialize)]
pub struct RawModule {
    pub format: u32,
    pub module: String,
    pub unit: String,
    /// Facts about every referenced Id GHC gave us as a `GlobalId` with an
    /// *external* `Name`, keyed by that stable name. An internal name is
    /// never a key: internal stable strings are not unique. A locally bound
    /// Id is not in here — the lexical resolver owns it and its binder
    /// carries the authoritative facts — but since the dump is taken after
    /// `CoreTidy` the module's own externalised top-level binders can
    /// appear, redundantly, when the module references them.
    pub ids: HashMap<String, IdInfo>,
    /// Optional, additive format-6 evidence. Absence is not permission to
    /// infer general constructor layouts from names or pretty types.
    #[serde(default)]
    pub constructors: Vec<ConstructorInfo>,
    /// The module's hash-consed type table. Every child index is smaller
    /// than its parent's, so the table can be rebuilt in one forward pass.
    pub types: Vec<RawTy>,
    pub binds: Vec<RawBind>,
}

/// Optional worker-layout evidence for complete algebraic constructor families.
#[derive(Debug, Clone, Deserialize)]
pub struct ConstructorInfo {
    pub name: String,
    pub worker: String,
    pub family: String,
    #[serde(rename = "familySize")]
    pub family_size: u32,
    pub tag: u32,
    pub signature: TyId,
    #[serde(rename = "repArity")]
    pub rep_arity: u32,
    pub strict: Vec<bool>,
    /// Vanilla lifted algebraic representation: no newtypes, unboxed sums/
    /// tuples, unlifted datatypes, existential or equality evidence fields.
    pub vanilla: bool,
    /// Additive evidence, each a separate GHC fact, so the four reasons
    /// `vanilla` can be false are told apart. A class dictionary carries its
    /// superclass as a *constraint* field, which makes GHC's own
    /// `isVanillaDataCon` false although the representation is an ordinary
    /// boxed record; an existential or a GADT equality is a different matter
    /// and stays unsupported. `None` on a dump taken before this evidence
    /// existed, where only `vanilla` is known and the conservative answer is
    /// the only one available.
    #[serde(default)]
    pub newtype: Option<bool>,
    #[serde(default)]
    pub unlifted: Option<bool>,
    #[serde(default)]
    pub unboxed: Option<bool>,
    #[serde(default)]
    pub existential: Option<bool>,
    #[serde(default)]
    pub equalities: Option<bool>,
    /// GHC's `isClassTyCon`: this family is a class's dictionary. Nothing on
    /// the Rust side can tell a dictionary from a one-constructor record by
    /// its shape, and an occurrence name is not evidence.
    #[serde(rename = "class", default)]
    pub class_dictionary: Option<bool>,
}

impl ConstructorInfo {
    /// An ordinary boxed, lifted constructor whose fields are all values.
    /// `vanilla` alone answers this for a plain data type; for a class
    /// dictionary it does not, because a superclass is a constraint field.
    /// GHC's unboxed tuple: no heap object, no tag, and exactly one
    /// constructor whose fields *are* the values, side by side.
    ///
    /// `unboxed` is GHC's `isUnboxedTupleTyCon || isUnboxedSumTyCon`. A sum
    /// has one constructor per alternative and needs a discriminant to say
    /// which one is present; a tuple has exactly one. The family size is what
    /// tells them apart, and it is GHC's count, not an inference from the
    /// name.
    pub fn unboxed_tuple(&self) -> bool {
        self.unboxed == Some(true) && self.family_size == 1 && self.newtype == Some(false)
    }

    pub fn boxed_record(&self) -> bool {
        if self.vanilla {
            return true;
        }
        matches!(
            (
                self.newtype,
                self.unlifted,
                self.unboxed,
                self.existential,
                self.equalities,
            ),
            (
                Some(false),
                Some(false),
                Some(false),
                Some(false),
                Some(false)
            )
        )
    }
}

/// A type constructor's identity: its stable name. The unique is a
/// diagnostic and nothing keys by it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
pub struct TyConId {
    pub name: Name,
    pub occ: Name,
    pub unique: Name,
}

/// A type variable, as dumped. Type-variable *names* are internal, so they
/// are not identities either; alpha-equivalence is structural
/// ([`crate::Ty::alpha_eq`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
pub struct TyVarId {
    pub name: Name,
    pub occ: Name,
    pub unique: Name,
}

/// One entry of the type table, with its children as indices.
#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind")]
pub enum RawTy {
    TyVar {
        name: String,
        occ: String,
        unique: String,
    },
    TyConApp {
        tycon: TyConId,
        args: Vec<TyId>,
    },
    AppTy {
        fun: TyId,
        arg: TyId,
    },
    FunTy {
        mult: TyId,
        arg: TyId,
        res: TyId,
    },
    ForAllTy {
        binder: TyVarId,
        body: TyId,
    },
    LitTy {
        #[serde(rename = "litKind")]
        lit_kind: String,
        lit: String,
    },
    /// A `CastTy` or a `CoercionTy`: nothing downstream reads one, so the
    /// plugin keeps only the rendering.
    Opaque {
        pretty: String,
    },
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
    /// Diagnostics only: see the module header.
    pub unique: String,
    /// The binder's type, structurally: an index into the type table.
    pub ty: TyId,
    /// The same type as GHC rendered it, *before* synonym expansion. For
    /// diagnostics and for the rules that have not been migrated to the
    /// structured form yet.
    #[serde(rename = "type")]
    pub ty_pretty: String,

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

    /// Format 6, top-level binders only, **diagnostics**: the tidied `Name`
    /// is external, i.e. another module can name this binding. `None` on a
    /// format-5 dump and on every nested binder.
    #[serde(rename = "externalName", default)]
    pub external_name: Option<bool>,
    /// Format 6, top-level binders only, **diagnostics**: the tidied `Name`
    /// is in the module's source export list (`availsToNameSet
    /// (mg_exports)`). Narrower than [`Binder::exported`], which is the
    /// compiler's own export/liveness flag. `None` on a format-5 dump and
    /// on every nested binder.
    #[serde(rename = "sourceExported", default)]
    pub source_exported: Option<bool>,
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
        /// GHC's `isGlobalId`. A diagnostic fact about the `Var`, **not**
        /// the local-vs-import decision: after `CoreTidy` every top-level
        /// binder is a `GlobalId`, including the ones whose `Name` stays
        /// internal, so locality is decided lexically by
        /// [`crate::Module::resolve_scopes`] and by nothing else.
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
        ty: TyId,
        #[serde(rename = "type")]
        ty_pretty: String,
        alts: Vec<RawAlt>,
    },
    Cast {
        expr: Box<RawExpr>,
        /// The coercion's two types and its role. A coercion has no runtime
        /// content, so these are the only evidence a consumer has for deciding
        /// whether erasing the cast preserves the representation. Absent on a
        /// dump taken before they were emitted, where the answer is a refusal.
        #[serde(default)]
        from: Option<TyId>,
        #[serde(default)]
        to: Option<TyId>,
        #[serde(default)]
        role: Option<String>,
    },
    Tick {
        expr: Box<RawExpr>,
    },
    Type {
        ty: TyId,
        #[serde(rename = "type")]
        pretty: String,
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

/// A Core literal. `pretty` is GHC's own rendering, which escapes, so it is a
/// diagnostic and never a value. The exact fields below carry the value itself;
/// a dump taken before they existed has none of them, and a consumer that needs
/// an exact value refuses rather than parsing the rendering.
#[derive(Debug, Clone, Deserialize)]
pub struct Lit {
    pub kind: String,
    pub pretty: String,
    /// `LitChar`: the Unicode code point.
    #[serde(default)]
    pub codepoint: Option<u32>,
    /// `LitString`: the bytes, lower-case hex, two digits each. A Haskell
    /// string literal is an `Addr#` to bytes, not to text.
    #[serde(default)]
    pub bytes: Option<String>,
    /// `LitNumber`: the exact value in decimal. Arbitrary precision, because
    /// `LitNumBigNat` is.
    #[serde(default)]
    pub value: Option<String>,
    /// `LitNumber`: which `LitNumType` GHC gave it. The width and signedness
    /// of a numeric literal are this, never the spelling.
    #[serde(rename = "numType", default)]
    pub num_type: Option<String>,
}

impl Lit {
    /// An `Int#` literal as the dump carries one, for tests and fixtures.
    pub fn int(value: i64) -> Lit {
        Lit {
            kind: "number".into(),
            pretty: format!("{value}#"),
            codepoint: None,
            bytes: None,
            value: Some(value.to_string()),
            num_type: Some("Int".into()),
        }
    }

    /// A `Char#` literal as the dump carries one, for tests and fixtures.
    pub fn character(value: char) -> Lit {
        Lit {
            kind: "char".into(),
            pretty: format!("'{}'#", value.escape_default()),
            codepoint: Some(value as u32),
            bytes: None,
            value: None,
            num_type: None,
        }
    }

    /// An `Addr#` string literal as the dump carries one, for tests and
    /// fixtures. A Haskell string literal addresses bytes, not text.
    pub fn string(bytes: &[u8]) -> Lit {
        Lit {
            kind: "string".into(),
            pretty: format!("{:?}#", String::from_utf8_lossy(bytes)),
            codepoint: None,
            bytes: Some(bytes.iter().map(|b| format!("{b:02x}")).collect()),
            value: None,
            num_type: None,
        }
    }

    /// The exact bytes of a `LitString`.
    pub fn string_bytes(&self) -> Result<Vec<u8>, String> {
        if self.kind != "string" {
            return Err("literal is not a string".into());
        }
        let hex = self
            .bytes
            .as_deref()
            .ok_or("this dump carries no exact bytes for a string literal")?;
        if hex.len() % 2 != 0 {
            return Err("string literal bytes are not whole octets".into());
        }
        (0..hex.len() / 2)
            .map(|i| {
                u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
                    .map_err(|error| format!("string literal bytes are not hexadecimal: {error}"))
            })
            .collect()
    }

    /// The exact code point of a `LitChar`.
    pub fn char_codepoint(&self) -> Result<u32, String> {
        if self.kind != "char" {
            return Err("literal is not a character".into());
        }
        self.codepoint
            .ok_or_else(|| "this dump carries no exact code point for a character literal".into())
    }

    /// The exact value of a `LitNumber` of the named `LitNumType`, as `i128`
    /// so every fixed-width GHC number fits without wrapping.
    pub fn number(&self, num_type: &str) -> Result<i128, String> {
        if self.kind != "number" {
            return Err("literal is not a number".into());
        }
        match self.num_type.as_deref() {
            Some(found) if found == num_type => {}
            Some(found) => {
                return Err(format!("numeric literal is a {found}, not a {num_type}"));
            }
            None => return Err("this dump carries no LitNumType for a numeric literal".into()),
        }
        self.value
            .as_deref()
            .ok_or("this dump carries no exact value for a numeric literal")?
            .parse()
            .map_err(|error| {
                format!("numeric literal does not fit a signed 128-bit value: {error}")
            })
    }
}
