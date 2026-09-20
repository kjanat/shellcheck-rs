//! Conservative first slice of Core lowering: top-level literal and argument
//! leaves, with leading value lambdas. Unsupported constructs fail explicitly.
//! This is not a whole-program driver or an independent semantic verifier.

use std::collections::BTreeMap;

use h2r_core_ir::{BinderKind, Expr, Module};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LowerError {
    pub module: usize,
    pub owner: BinderId,
    pub source: Option<ExprId>,
    pub reason: String,
}

#[derive(Debug, Clone)]
pub struct LoweredLeaf {
    pub function: Function,
    /// Leading lambdas become entry parameters, not runtime instructions.
    pub parameters: Vec<(ExprId, ValueId)>,
    /// Ticks have no runtime representation but retain their source addresses.
    pub erased_ticks: Vec<ExprId>,
}

/// Lower one top-level owner from an already-loaded, well-typed Core module.
/// The caller allocates the function ID and module index. No input is mutated.
/// Literal types come from the enclosing binder signature, not literal text.
pub fn lower_leaf(
    module: &Module,
    module_index: usize,
    owner: BinderId,
    id: FnId,
) -> Result<LoweredLeaf, LowerError> {
    let fail = |source, reason: &str| LowerError {
        module: module_index,
        owner,
        source,
        reason: reason.into(),
    };
    let pair = module
        .top
        .iter()
        .flat_map(|b| &b.pairs)
        .find(|pair| pair.binder == owner)
        .ok_or_else(|| fail(None, "owner is not a top-level binding"))?;
    let mut current = pair.rhs;
    let mut ty = module.binder_ty(owner);
    let mut params = Vec::new();
    let mut parameters = Vec::new();
    let mut erased_ticks = Vec::new();
    let mut locals = BTreeMap::new();
    loop {
        match module.expr(current) {
            Expr::Tick(body) => {
                erased_ticks.push(current);
                current = *body;
            }
            Expr::Lam { binder, body } => {
                if module.binder(*binder).kind != BinderKind::Id {
                    return Err(fail(Some(current), "type lambdas are not lowered yet"));
                }
                let Ty::Fun { arg, res, .. } = ty else {
                    return Err(fail(Some(current), "value lambda needs a function type"));
                };
                if !arg.alpha_eq(module.binder_ty(*binder)) {
                    return Err(fail(Some(current), "lambda parameter type mismatch"));
                }
                let value = ValueId(params.len() as u32);
                params.push(Value {
                    id: value,
                    ty: (**arg).clone(),
                });
                parameters.push((current, value));
                locals.insert(*binder, value);
                ty = res;
                current = *body;
            }
            _ => break,
        }
    }
    let origin = |rule| Origin {
        module: module_index,
        source: Source::Expr(current),
        rule,
    };
    let mut instructions = Vec::new();
    let value = match module.expr(current) {
        Expr::Lit(lit) => {
            let value = ValueId(params.len() as u32);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: ty.clone(),
                },
                operation: Operation::Literal(lit.clone()),
                origin: origin(Rule::Literal),
            });
            value
        }
        Expr::Var { .. } => {
            let binder = module
                .resolve(current)
                .ok_or_else(|| fail(Some(current), "external references are not lowered yet"))?;
            let value = locals.get(&binder).copied().ok_or_else(|| {
                fail(
                    Some(current),
                    "non-parameter references are not lowered yet",
                )
            })?;
            if !module.binder_ty(binder).alpha_eq(ty) {
                return Err(fail(Some(current), "returned parameter type mismatch"));
            }
            value
        }
        Expr::Cast(_) => {
            return Err(fail(
                Some(current),
                "casts need source and target type evidence",
            ));
        }
        Expr::App { .. } => return Err(fail(Some(current), "applications are not lowered yet")),
        Expr::Let { .. } => return Err(fail(Some(current), "let bindings are not lowered yet")),
        Expr::Case { .. } => return Err(fail(Some(current), "cases are not lowered yet")),
        Expr::Type { .. } | Expr::Coercion => {
            return Err(fail(Some(current), "type or coercion in value position"));
        }
        Expr::Lam { .. } | Expr::Tick(_) => unreachable!("leading lambdas and ticks were consumed"),
    };
    let function = Function {
        id,
        module: module_index,
        owner,
        result_ty: ty.clone(),
        entry: BlockId(0),
        blocks: vec![Block {
            id: BlockId(0),
            params,
            instructions,
            terminator: Terminator {
                exit: Exit::Return(value),
                origin: origin(Rule::Return),
            },
        }],
    };
    verify::verify(&function).map_err(|reason| fail(Some(current), &reason))?;
    Ok(LoweredLeaf {
        function,
        parameters,
        erased_ticks,
    })
}
