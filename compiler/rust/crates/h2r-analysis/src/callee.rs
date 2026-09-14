//! Who receives an argument? Two orthogonal questions about the head of an
//! application spine:
//!
//! * [`Resolution`] — can the compiler see the callee well enough to know
//!   what it does with the argument?
//! * [`Family`] — which abstraction is the callee part of? This is what
//!   decides which normalisation pass (dictionary specialisation, transformer
//!   collapse, Parsec normalisation, constructor-field strategy) would make
//!   the argument's laziness question disappear.

use std::collections::HashMap;

use h2r_core_ir::{BinderId, Expr, ExprId, IdInfo, Module};
use serde::Serialize;

/// How a local unique is bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindSite {
    Top,
    Let,
    Lam,
    CaseBinder,
    AltBinder,
}

/// Where and how a local unique is bound. The binding-site binder is the
/// authoritative source of a local's signature and arity: GHC does not keep
/// the `IdInfo` on occurrence `Var`s up to date.
#[derive(Debug, Clone, Copy)]
pub struct BindInfo {
    pub site: BindSite,
    pub binder: BinderId,
    /// The right-hand side, for let- and top-level-bound ids.
    pub rhs: Option<ExprId>,
}

/// Binding site of every binder in the module, by unique.
pub fn bind_sites(m: &Module) -> HashMap<&str, BindInfo> {
    let mut map = HashMap::new();
    let mut put = |b: BinderId, site: BindSite, rhs: Option<ExprId>| {
        map.insert(
            m.binder(b).unique.as_str(),
            BindInfo {
                site,
                binder: b,
                rhs,
            },
        );
    };
    for bind in &m.top {
        for p in &bind.pairs {
            put(p.binder, BindSite::Top, Some(p.rhs));
        }
    }
    for e in &m.exprs {
        match e {
            Expr::Lam { binder, .. } => put(*binder, BindSite::Lam, None),
            Expr::Let { bind, .. } => {
                for p in &bind.pairs {
                    put(p.binder, BindSite::Let, Some(p.rhs));
                }
            }
            Expr::Case { binder, alts, .. } => {
                put(*binder, BindSite::CaseBinder, None);
                for a in alts {
                    for b in &a.binders {
                        put(*b, BindSite::AltBinder, None);
                    }
                }
            }
            _ => {}
        }
    }
    map
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Resolution {
    /// A data constructor: field strictness is known exactly.
    DataCon,
    /// A global function with a demand signature covering this argument.
    ExactGlobal,
    /// A let- or top-level-bound local function with a signature.
    ExactLocal,
    /// A class method selector: which implementation runs depends on the
    /// dictionary argument. Resolved by specialisation.
    ClassOp,
    /// A lambda-bound or case-bound variable: an unknown higher-order value.
    HigherOrderParam,
    /// A global id with no demand signature (nothing is known about it).
    ImportedOpaque,
    /// A global with a signature, but this argument lies past its arity:
    /// it is applied to the *result* of the call.
    PastArity,
    /// A local bound to a lambda, applied past its signature.
    KnownLambdaShortSig,
    /// A local bound to the result of a call to a known function or
    /// constructor: the closure is statically traceable through the callee.
    ClosureFromKnownCall,
    /// A local bound to a case, let or other computation of function type.
    ComputedClosure,
    /// The head is not a variable (a lambda, a case, a let).
    NonVarHead,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Family {
    /// `Text.Parsec.*`
    Parsec,
    /// One of ParsecT's four CPS continuations (`cok`, `cerr`, `eok`, `eerr`)
    /// being applied: Parsec's representation, inlined into the program.
    ParsecContinuation,
    /// An eta-expansion parameter (`eta…`) being applied: an inlined
    /// monadic function (a parser, a `StateT` step) run on its state.
    EtaParam,
    /// `Control.Monad.Trans.*`, mtl classes, `Data.Functor.Identity`
    Transformers,
    /// `>>=`, `return`, `fmap`, `<*>`, `pure`, ... from `GHC.Base`
    MonadOps,
    /// A class-op selector: dictionary dispatch.
    ClassOp,
    /// A dfun or dictionary binding.
    Dictionary,
    /// A boxed tuple constructor: mostly inlined `StateT`/`Writer` results.
    Tuple,
    /// An unboxed tuple constructor: worker/wrapper results.
    UnboxedTuple,
    /// List cons.
    ListCons,
    /// A data constructor defined in the program.
    ProgramDataCon,
    /// A function defined in the program.
    ProgramFunction,
    /// A local let-bound function.
    LocalFunction,
    /// A data constructor from a library (`Just`, `(:)`, `(,)`, ...).
    LibraryDataCon,
    /// List and Foldable/Traversable operations from base.
    BaseList,
    /// `Data.Map`, `Data.Set`, `Data.IntMap`, ...
    Containers,
    /// Anything else from base / ghc-prim.
    BaseOther,
    /// Anything else from another library (regex-tdfa, aeson, fgl, ...).
    OtherLibrary,
    /// A higher-order parameter or other unknown value.
    Unknown,
}

/// `$unit$Module$occ` as produced by GHC's `nameStableString`.
pub fn split_stable_name(name: &str) -> Option<(&str, &str, &str)> {
    let rest = name.strip_prefix('$')?;
    let (unit, rest) = rest.split_once('$')?;
    let (module, occ) = rest.split_once('$')?;
    Some((unit, module, occ))
}

#[derive(Debug, Clone, Serialize)]
pub struct Callee {
    pub resolution: Resolution,
    pub family: Family,
    /// Defining module of the head, when it is a global.
    pub module: Option<String>,
    pub occ: String,
}

/// Classify the head of the spine rooted at `root`, for the value argument
/// at index `arg_index`.
pub fn classify(
    m: &Module,
    sites: &HashMap<&str, BindInfo>,
    root: ExprId,
    arg_index: usize,
) -> Callee {
    let (head, _) = m.spine(root);

    let Expr::Var {
        unique,
        name,
        occ,
        is_global,
    } = m.expr(head)
    else {
        return Callee {
            resolution: Resolution::NonVarHead,
            family: Family::Unknown,
            module: None,
            occ: String::new(),
        };
    };
    let info = m.ids.get(unique);
    let bound = sites.get(unique.as_str()).copied();
    let (unit, module) = split_stable_name(name)
        .map(|(u, md, _)| (u, md))
        .unwrap_or(("", ""));

    // Signature arity: from the binding site for locals, the id table for
    // globals.
    let sig_args = match bound {
        Some(b) if !*is_global => m
            .binder(b.binder)
            .dmd_sig
            .as_ref()
            .map(|s| s.args.len())
            .unwrap_or(0),
        _ => info.map(|i| i.dmd_sig.args.len()).unwrap_or(0),
    };

    let resolution = if info.is_some_and(|i| i.data_con.is_some()) {
        Resolution::DataCon
    } else if info.is_some_and(|i| i.is_class_op) {
        Resolution::ClassOp
    } else if *is_global {
        if info.is_none() || sig_args == 0 {
            Resolution::ImportedOpaque
        } else if arg_index >= sig_args {
            Resolution::PastArity
        } else {
            Resolution::ExactGlobal
        }
    } else {
        match bound {
            Some(BindInfo {
                site: BindSite::Let | BindSite::Top,
                rhs: Some(rhs),
                ..
            }) => {
                if arg_index < sig_args {
                    Resolution::ExactLocal
                } else {
                    let inner = m.strip(rhs);
                    match m.expr(inner) {
                        Expr::Lam { .. } => Resolution::KnownLambdaShortSig,
                        Expr::App { .. } | Expr::Var { .. } => {
                            let (h, _) = m.spine(inner);
                            let known = m.id_info(h).is_some_and(|i| {
                                i.data_con.is_some() || !i.dmd_sig.args.is_empty()
                            }) || matches!(
                                m.expr(h),
                                Expr::Var { unique, .. }
                                    if sites.get(unique.as_str()).is_some_and(|b| {
                                        matches!(b.site, BindSite::Let | BindSite::Top)
                                    })
                            );
                            if known {
                                Resolution::ClosureFromKnownCall
                            } else {
                                Resolution::ComputedClosure
                            }
                        }
                        _ => Resolution::ComputedClosure,
                    }
                }
            }
            _ => Resolution::HigherOrderParam,
        }
    };

    let family = family_of(info, *is_global, unit, module, occ, resolution);

    Callee {
        resolution,
        family,
        module: if *is_global {
            Some(module.to_string())
        } else {
            None
        },
        occ: occ.clone(),
    }
}

fn family_of(
    info: Option<&IdInfo>,
    is_global: bool,
    unit: &str,
    module: &str,
    occ: &str,
    resolution: Resolution,
) -> Family {
    let in_program = unit == "main" || module.starts_with("ShellCheck") || module == "Main";
    if resolution == Resolution::ClassOp {
        return Family::ClassOp;
    }
    if occ.starts_with("$f") || occ.starts_with("$p") || occ.starts_with("$d") {
        return Family::Dictionary;
    }
    if info.is_some_and(|i| i.data_con.is_some()) {
        return if in_program {
            Family::ProgramDataCon
        } else if occ == ":" {
            Family::ListCons
        } else if occ.starts_with("(#") {
            Family::UnboxedTuple
        } else if occ.starts_with("(,") {
            Family::Tuple
        } else {
            Family::LibraryDataCon
        };
    }
    if !is_global {
        return match resolution {
            Resolution::ExactLocal
            | Resolution::KnownLambdaShortSig
            | Resolution::ClosureFromKnownCall
            | Resolution::ComputedClosure => Family::LocalFunction,
            _ if matches!(occ, "cok" | "cerr" | "eok" | "eerr") => Family::ParsecContinuation,
            _ if occ.starts_with("eta") => Family::EtaParam,
            _ => Family::Unknown,
        };
    }
    if module.starts_with("Text.Parsec") || module.starts_with("Text.ParserCombinators") {
        return Family::Parsec;
    }
    if module.starts_with("Control.Monad.Trans")
        || module.starts_with("Control.Monad.Reader")
        || module.starts_with("Control.Monad.State")
        || module.starts_with("Control.Monad.Except")
        || module.starts_with("Control.Monad.Writer")
        || module.starts_with("Control.Monad.RWS")
        || module.starts_with("Control.Monad.Error")
        || module == "Data.Functor.Identity"
    {
        return Family::Transformers;
    }
    if in_program {
        return Family::ProgramFunction;
    }
    if (module == "GHC.Base" || module == "Control.Monad" || module == "Data.Functor")
        && matches!(
            occ,
            ">>="
                | ">>"
                | "return"
                | "fmap"
                | "<$>"
                | "<$"
                | "$>"
                | "<*>"
                | "*>"
                | "<*"
                | "pure"
                | "liftA2"
                | "=<<"
                | "ap"
                | "liftM"
                | "liftM2"
                | "join"
                | "when"
                | "unless"
                | "mapM"
                | "mapM_"
                | "forM"
                | "forM_"
                | "sequence"
                | "sequence_"
                | "void"
        )
    {
        return Family::MonadOps;
    }
    if module == "GHC.List"
        || module == "Data.OldList"
        || module == "Data.Foldable"
        || module == "Data.Traversable"
        || module == "Data.List"
        || (module == "GHC.Base" && matches!(occ, "map" | "++" | "foldr" | "build" | "augment"))
    {
        return Family::BaseList;
    }
    if module.starts_with("Data.Map")
        || module.starts_with("Data.Set")
        || module.starts_with("Data.IntMap")
        || module.starts_with("Data.IntSet")
        || module.starts_with("Data.Sequence")
        || module.starts_with("Data.Graph")
    {
        return Family::Containers;
    }
    if unit.starts_with("base") || unit.starts_with("ghc-prim") || unit.starts_with("ghc-bignum") {
        return Family::BaseOther;
    }
    Family::OtherLibrary
}
