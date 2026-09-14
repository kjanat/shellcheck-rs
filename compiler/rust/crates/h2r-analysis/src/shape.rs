//! Syntactic shape of expressions: what kind of RHS is this, is it already a
//! value, and what does an argument position demand.

use h2r_core_ir::{Edge, Expr, ExprId, Module};
use serde::Serialize;

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
    pub fn of(m: &Module, id: ExprId) -> RhsKind {
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
                    return RhsKind::of(m, cur);
                }
                RhsKind::Lambda
            }
            Expr::Lit(_) => RhsKind::Literal,
            Expr::Var { .. } => {
                if is_saturated_con(m, inner) {
                    RhsKind::Constructor
                } else {
                    RhsKind::Variable
                }
            }
            Expr::App { .. } => {
                if is_saturated_con(m, inner) {
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
pub fn value_args(m: &Module, args: &[ExprId]) -> Vec<ExprId> {
    args.iter()
        .copied()
        .filter(|a| !matches!(m.expr(m.strip(*a)), Expr::Type(_) | Expr::Coercion))
        .collect()
}

pub fn is_saturated_con(m: &Module, id: ExprId) -> bool {
    let (head, args) = m.spine(id);
    match m.id_info(head) {
        Some(info) => match &info.data_con {
            Some(dc) => value_args(m, &args).len() as u32 >= dc.rep_arity,
            None => false,
        },
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

pub fn arg_shape(m: &Module, id: ExprId) -> ArgShape {
    let inner = m.strip(id);
    match m.expr(inner) {
        Expr::Var { .. } | Expr::Lit(_) | Expr::Type(_) | Expr::Coercion => ArgShape::Trivial,
        Expr::Lam { .. } => ArgShape::Closure,
        Expr::App { .. } => {
            let (head, args) = m.spine(inner);
            let n = value_args(m, &args).len() as u32;
            if let Expr::Var { occ, .. } = m.expr(head)
                && matches!(occ.as_str(), "unpackCString#" | "unpackCStringUtf8#")
                && n == 1
            {
                return ArgShape::StringLiteral;
            }
            match m.id_info(head) {
                Some(info) => {
                    if let Some(dc) = &info.data_con {
                        if n >= dc.rep_arity {
                            ArgShape::ConApp
                        } else {
                            ArgShape::PartialApp
                        }
                    } else if info.arity > n {
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
    /// Argument to an unknown callee, or beyond the signature's arity.
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
    /// field, a lazy parameter, or an unknown callee.
    pub fn escapes(self) -> bool {
        matches!(
            self,
            Position::LazyField | Position::LazyParam | Position::UnknownArg
        )
    }
}

/// The position of expression `id` in its parent, looking through casts and
/// ticks on the way up.
pub fn position(m: &Module, id: ExprId) -> Position {
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
            Edge::AppArg => return arg_position(m, parent, cur),
            _ => return Position::Other,
        }
    }
}

/// `app` is an `App` node whose argument is `arg`; classify that argument
/// slot by the callee's signature.
fn arg_position(m: &Module, app: ExprId, arg: ExprId) -> Position {
    // Climb to the root of the spine, then decompose it.
    let mut root = app;
    while let Some(p) = m.parent[root as usize] {
        if m.edge[root as usize] == Edge::AppFun && matches!(m.expr(p), Expr::App { .. }) {
            root = p;
        } else {
            break;
        }
    }
    let (head, args) = m.spine(root);
    let vargs = value_args(m, &args);
    let Some(idx) = vargs.iter().position(|a| *a == arg) else {
        // A type argument.
        return Position::Other;
    };
    let Some(info) = m.id_info(head) else {
        return Position::UnknownArg;
    };
    if let Some(dc) = &info.data_con {
        if dc.strict_fields.len() == vargs.len() {
            return if dc.strict_fields[idx] {
                Position::StrictArg
            } else {
                Position::LazyField
            };
        }
        return Position::UnknownArg;
    }
    match info.dmd_sig.args.get(idx) {
        Some(d) if d.absent => Position::AbsentArg,
        Some(d) if d.strict => Position::StrictArg,
        Some(_) => Position::LazyParam,
        None => Position::UnknownArg,
    }
}

/// Is `head` (a `Var`) a dictionary or dictionary-selector? GHC's naming
/// conventions: `$f` dfuns, `$p` superclass selectors, `$d` dictionary
/// bindings, `$c` method implementations.
pub fn is_dictionary_head(m: &Module, head: ExprId) -> bool {
    match m.expr(head) {
        Expr::Var { occ, .. } => {
            occ.starts_with("$f") || occ.starts_with("$p") || occ.starts_with("$d")
        }
        _ => false,
    }
}
