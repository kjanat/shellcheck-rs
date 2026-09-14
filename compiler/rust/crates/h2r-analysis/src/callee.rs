//! Who receives an argument? Two orthogonal questions about the head of an
//! application spine:
//!
//! * [`Resolution`] — can the compiler see the callee well enough to know
//!   what it does with the argument?
//! * [`Family`] — which abstraction is the callee part of? This is what
//!   decides which normalisation pass (dictionary specialisation, transformer
//!   collapse, Parsec normalisation, constructor-field strategy) would make
//!   the argument's laziness question disappear.
//!
//! [`Tier`] collapses `Resolution` onto the only question that matters for
//! codegen: is the target proven? Family attribution is not target proof —
//! recognising a Parsec continuation name says which pass owns the site,
//! not what code runs.

use h2r_core_ir::{Expr, ExprId, IdInfo, Module};
use serde::Serialize;

pub use crate::scope::{BindInfo, BindSite};
use crate::scope::{Scope, SigSource};

/// How much of the eventual call target is proven. This is the honest
/// axis: [`Resolution`] says what kind of head we looked at, the tier says
/// whether we know what code runs when the argument is consumed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Tier {
    /// Exactly one target, and it is this head: a constructor, a function
    /// with a signature covering the argument, or a local lambda whose
    /// manifest parameter receives it.
    Exact,
    /// A finite, enumerated set of targets. Nothing lands here yet: class
    /// methods will, once the closed-world instance enumeration exists.
    FiniteSet,
    /// The closure's *producer* is known (a known call, or a known lambda
    /// applied past its parameters) but the returned target has not been
    /// followed. Awaiting target analysis, not proven dynamic.
    ProducerKnown,
    /// Nothing proven about the target: a higher-order parameter, a class
    /// method before enumeration, an opaque import, a computed closure.
    Unresolved,
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
    /// A local bound to a lambda; the argument lands on one of its
    /// manifest parameters, but the demand signature is shorter than the
    /// lambda and says nothing about it. The target is exact, the demand is
    /// unknown.
    KnownLambdaNoDemand,
    /// A local bound to a lambda, applied past its manifest parameters:
    /// the argument goes to whatever the lambda body returns.
    KnownLambdaPastArity,
    /// A local bound to the result of a call to a known function or
    /// constructor. The producer is known; the closure it returns has not
    /// been followed to its target.
    ClosureFromKnownCall,
    /// A local bound to a case, let or other computation of function type.
    ComputedClosure,
    /// The head is not a variable (a lambda, a case, a let).
    NonVarHead,
}

impl Resolution {
    pub fn tier(self) -> Tier {
        match self {
            Resolution::DataCon
            | Resolution::ExactGlobal
            | Resolution::ExactLocal
            | Resolution::KnownLambdaNoDemand => Tier::Exact,
            Resolution::PastArity
            | Resolution::KnownLambdaPastArity
            | Resolution::ClosureFromKnownCall => Tier::ProducerKnown,
            Resolution::ClassOp
            | Resolution::HigherOrderParam
            | Resolution::ImportedOpaque
            | Resolution::ComputedClosure
            | Resolution::NonVarHead => Tier::Unresolved,
        }
    }
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
    /// What the Parsec CPS recogniser proves about the code that runs when
    /// this argument is consumed ([`crate::parsec`]). Orthogonal to
    /// `resolution` and `family`, which keep saying what they said: the
    /// head is still syntactically a higher-order parameter, and the site
    /// still belongs to the Parsec normalisation pass. This says whether
    /// the *target* is nevertheless proven. Filled in by
    /// [`crate::parsec::integrate`]; `None` when the head is not a proven
    /// Parsec role binder at all.
    pub parsec: Option<ParsecTarget>,
}

/// The recogniser's verdict for one call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ParsecTarget {
    /// The head is a continuation with a single proven role and this call
    /// is a well-formed edge of it: the target is exactly one of ParsecT's
    /// four continuation slots.
    Role(crate::parsec::EdgeKind),
    /// The head's role is a proven finite set of slots.
    RoleSet,
    /// The head is a role binder of a recognised region, but the region is
    /// rejected or this particular call is not a well-formed edge.
    RegionUnresolved(&'static str),
}

impl Callee {
    /// What is actually proven about the code that runs: the best of the
    /// two independent proofs. The syntactic resolution and the Parsec
    /// recogniser each prove what they prove, and neither may weaken the
    /// other — a head the census already resolves exactly stays exact even
    /// where the recogniser only narrows its role to a pair of slots.
    /// ([`Tier`] is ordered strongest first.)
    pub fn tier(&self) -> Tier {
        let parsec = match self.parsec {
            Some(ParsecTarget::Role(_)) => Tier::Exact,
            Some(ParsecTarget::RoleSet) => Tier::FiniteSet,
            Some(ParsecTarget::RegionUnresolved(_)) | None => Tier::Unresolved,
        };
        self.resolution.tier().min(parsec)
    }
}

/// Number of manifest value lambdas at the top of an expression.
fn manifest_params(m: &Module, e: ExprId) -> usize {
    let mut n = 0;
    let mut cur = m.strip(e);
    while let Expr::Lam { binder, body } = m.expr(cur) {
        if m.binder(*binder).kind != h2r_core_ir::BinderKind::Tyvar {
            n += 1;
        }
        cur = m.strip(*body);
    }
    n
}

/// Classify the head of the spine rooted at `root`, for the value argument
/// at index `arg_index`.
pub fn classify(s: &Scope, root: ExprId, arg_index: usize) -> Callee {
    let m = s.m;
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
            parsec: None,
        };
    };
    let bound = s.binding_of(head);
    // Linkage by unique is only ever valid for an occurrence the resolver
    // classified as an import: a local's unique may name many binders and
    // the id table is populated from occurrences.
    let info = if bound.is_some() {
        None
    } else {
        m.ids.get(unique)
    };
    let sig = s.head_sig(head);
    let (unit, module) = split_stable_name(name)
        .map(|(u, md, _)| (u, md))
        .unwrap_or(("", ""));

    // Signature arity from the one shared lookup: the binding site for
    // anything bound here, the id table for imports.
    let sig_args = sig.map(|x| x.sig_arity()).unwrap_or(0);
    let bound_here = matches!(sig, Some(x) if x.source != SigSource::IdTable);

    let resolution = if sig.is_some_and(|x| x.data_con.is_some()) {
        Resolution::DataCon
    } else if sig.is_some_and(|x| x.is_class_op) {
        Resolution::ClassOp
    } else if !bound_here {
        if sig.is_none() || sig_args == 0 {
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
                        Expr::Lam { .. } => {
                            if arg_index < manifest_params(m, inner) {
                                Resolution::KnownLambdaNoDemand
                            } else {
                                Resolution::KnownLambdaPastArity
                            }
                        }
                        Expr::App { .. } | Expr::Var { .. } => {
                            let (h, _) = m.spine(inner);
                            let known = s
                                .head_sig(h)
                                .is_some_and(|x| x.data_con.is_some() || x.sig_arity() > 0)
                                || s.binding_of(h).is_some_and(|b| {
                                    matches!(b.site, BindSite::Let | BindSite::Top)
                                });
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
        parsec: None,
    }
}

/// `$f…` is a dfun, `$p…` a superclass selector, `$d…` a dictionary
/// binding. `$fApplicativeParsecT2`, with a numeric suffix, is not a
/// dictionary: it is a floated-out instance-method body — an ordinary
/// function GHC has already dispatched to. It is classified by its module.
pub fn is_dictionary_name(occ: &str) -> bool {
    if occ.starts_with("$p") || occ.starts_with("$d") {
        return true;
    }
    occ.starts_with("$f") && !occ.ends_with(|c: char| c.is_ascii_digit())
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
    if is_dictionary_name(occ) {
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
            | Resolution::KnownLambdaNoDemand
            | Resolution::KnownLambdaPastArity
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
