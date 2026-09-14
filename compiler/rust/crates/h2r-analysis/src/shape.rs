//! Syntactic shape of expressions: what kind of RHS is this, is it already a
//! value, and what does an argument position demand.
//!
//! Every arity and demand-signature question is answered by
//! [`Scope::head_sig`], never by reading an occurrence's own metadata.

use h2r_core_ir::{Edge, Expr, ExprId};
use serde::Serialize;

use crate::scope::Scope;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum RhsKind {
    Lambda,
    Constructor,
    Literal,
    Variable,
    Application,
    Case,
    Let,
    Cast,
    Other,
}

impl RhsKind {
    pub fn of(s: &Scope, id: ExprId) -> RhsKind {
        let m = s.m;
        let inner = m.strip(id);
        let cast = inner != id && matches!(m.expr(id), Expr::Cast(_));
        let kind = match m.expr(inner) {
            Expr::Lam { binder, .. } => {
                // A chain of type lambdas around a value is not a function.
                if m.binder(*binder).kind == h2r_core_ir::BinderKind::Tyvar {
                    let mut cur = inner;
                    while let Expr::Lam { binder, body } = m.expr(cur) {
                        if m.binder(*binder).kind != h2r_core_ir::BinderKind::Tyvar {
                            return RhsKind::Lambda;
                        }
                        cur = *body;
                    }
                    return RhsKind::of(s, cur);
                }
                RhsKind::Lambda
            }
            Expr::Lit(_) => RhsKind::Literal,
            Expr::Var { .. } => {
                if is_saturated_con(s, inner) {
                    RhsKind::Constructor
                } else {
                    RhsKind::Variable
                }
            }
            Expr::App { .. } => {
                if is_saturated_con(s, inner) {
                    RhsKind::Constructor
                } else {
                    RhsKind::Application
                }
            }
            Expr::Case { .. } => RhsKind::Case,
            Expr::Let { .. } => RhsKind::Let,
            Expr::Cast(_) | Expr::Tick(_) => unreachable!("stripped"),
            Expr::Type(_) | Expr::Coercion => RhsKind::Other,
        };
        if cast && kind == RhsKind::Other {
            RhsKind::Cast
        } else {
            kind
        }
    }
}

/// Value arguments of a spine: everything that is not a type or coercion.
pub fn value_args(s: &Scope, args: &[ExprId]) -> Vec<ExprId> {
    args.iter()
        .copied()
        .filter(|a| !matches!(s.m.expr(s.m.strip(*a)), Expr::Type(_) | Expr::Coercion))
        .collect()
}

pub fn is_saturated_con(s: &Scope, id: ExprId) -> bool {
    let (head, args) = s.m.spine(id);
    match s.head_sig(head).and_then(|sig| sig.data_con) {
        Some(dc) => value_args(s, &args).len() as u32 >= dc.rep_arity,
        None => false,
    }
}

/// Is the expression syntactically a value (needs no thunk to hold it)?
/// Lambdas, literals, saturated constructor applications and partial
/// applications of known functions all count.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ArgShape {
    Trivial,
    Closure,
    ConApp,
    PartialApp,
    /// `unpackCString# "…"#`: a string literal, static data.
    StringLiteral,
    Computation,
}

pub fn arg_shape(s: &Scope, id: ExprId) -> ArgShape {
    let m = s.m;
    let inner = m.strip(id);
    match m.expr(inner) {
        Expr::Var { .. } | Expr::Lit(_) | Expr::Type(_) | Expr::Coercion => ArgShape::Trivial,
        Expr::Lam { .. } => ArgShape::Closure,
        Expr::App { .. } => {
            let (head, args) = m.spine(inner);
            let n = value_args(s, &args).len() as u32;
            if let Expr::Var { occ, .. } = m.expr(head)
                && matches!(occ.as_str(), "unpackCString#" | "unpackCStringUtf8#")
                && n == 1
            {
                return ArgShape::StringLiteral;
            }
            match s.head_sig(head) {
                Some(sig) => {
                    if let Some(dc) = sig.data_con {
                        if n >= dc.rep_arity {
                            ArgShape::ConApp
                        } else {
                            ArgShape::PartialApp
                        }
                    } else if sig.arity > n {
                        // Fewer arguments than `idArity`: a PAP, a value.
                        ArgShape::PartialApp
                    } else {
                        ArgShape::Computation
                    }
                }
                None => ArgShape::Computation,
            }
        }
        _ => ArgShape::Computation,
    }
}

/// What a position demands of the expression placed there.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Position {
    /// Case scrutinee: evaluated right here.
    Scrutinee,
    /// Head of an application: evaluated right here.
    Head,
    /// Argument the callee is strict in, or a strict constructor field.
    StrictArg,
    /// Argument the callee never uses.
    AbsentArg,
    /// Lazy constructor field.
    LazyField,
    /// Argument a known function is lazy in.
    LazyParam,
    /// Argument to a call that supplies fewer value arguments than the
    /// callee's signature arity. The signature is not unleashed: the
    /// partial application is a function value that holds the argument
    /// unevaluated, whatever the callee would eventually do with it.
    UnsaturatedArg,
    /// Argument past the callee's signature arity: it is handed to whatever
    /// the call *returns*, about which the signature says nothing.
    PastSigArg,
    /// Argument to a callee with no signature at all.
    UnknownArg,
    /// Right-hand side of a let: its own binding decides.
    LetRhs,
    /// Anything else (lambda body, let body, case alternative...).
    Other,
}

impl Position {
    pub fn is_eager(self) -> bool {
        matches!(
            self,
            Position::Scrutinee | Position::Head | Position::StrictArg
        )
    }

    /// The expression is handed, unevaluated, to something else: a lazy
    /// field, a lazy parameter, a partial application, a call result, or an
    /// unknown callee.
    pub fn escapes(self) -> bool {
        matches!(
            self,
            Position::LazyField
                | Position::LazyParam
                | Position::UnsaturatedArg
                | Position::PastSigArg
                | Position::UnknownArg
        )
    }
}

/// The position of expression `id` in its parent, looking through casts and
/// ticks on the way up.
pub fn position(s: &Scope, id: ExprId) -> Position {
    let m = s.m;
    let mut cur = id;
    loop {
        let Some(parent) = m.parent[cur as usize] else {
            return Position::Other;
        };
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => {
                cur = parent;
                continue;
            }
            Edge::CaseScrut => return Position::Scrutinee,
            Edge::AppFun => return Position::Head,
            Edge::LetRhs { .. } => return Position::LetRhs,
            Edge::AppArg => return arg_position(s, parent, cur),
            _ => return Position::Other,
        }
    }
}

/// `app` is an `App` node whose argument is `arg`; classify that argument
/// slot by the callee's signature.
fn arg_position(s: &Scope, app: ExprId, arg: ExprId) -> Position {
    let m = s.m;
    let root = m.spine_root(app);
    let (head, args) = m.spine(root);
    let vargs = value_args(s, &args);
    let Some(idx) = vargs.iter().position(|a| *a == arg) else {
        // A type argument.
        return Position::Other;
    };
    let Some(sig) = s.head_sig(head) else {
        return Position::UnknownArg;
    };
    if let Some(dc) = sig.data_con {
        // A constructor's arity is its field count; anything less is a
        // partial application of the constructor.
        if vargs.len() < dc.rep_arity as usize {
            return Position::UnsaturatedArg;
        }
        if dc.strict_fields.len() == vargs.len() {
            return if dc.strict_fields[idx] {
                Position::StrictArg
            } else {
                Position::LazyField
            };
        }
        // Representation and source field counts differ (unboxed or
        // existential fields): no per-field verdict.
        return Position::UnknownArg;
    }
    if sig.sig_arity() == 0 {
        return Position::UnknownArg;
    }
    // GHC's demand transformer: the argument demands of a signature apply
    // only to calls that supply at least the signature's arity.
    if !sig.unleashed_by(vargs.len()) {
        return Position::UnsaturatedArg;
    }
    match sig.dmd_args.get(idx) {
        Some(d) if d.absent => Position::AbsentArg,
        Some(d) if d.strict => Position::StrictArg,
        Some(_) => Position::LazyParam,
        None => Position::PastSigArg,
    }
}

/// Is `head` (a `Var`) a dictionary or dictionary-selector? See
/// [`crate::callee::is_dictionary_name`].
pub fn is_dictionary_head(s: &Scope, head: ExprId) -> bool {
    match s.m.expr(head) {
        Expr::Var { occ, .. } => crate::callee::is_dictionary_name(occ),
        _ => false,
    }
}
