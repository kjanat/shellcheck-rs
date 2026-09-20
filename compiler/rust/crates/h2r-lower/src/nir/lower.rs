//! Conservative first slice of Core lowering: literal, argument and top-reference
//! leaves, with leading type/value lambdas. Unsupported constructs fail explicitly.
//! This is not a whole-program driver or an independent semantic verifier.

use std::collections::BTreeMap;

use h2r_core_ir::{BindSite, BinderKind, Expr, Module};

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
    /// Type lambdas introduce no runtime value; retain their lexical binders
    /// (including their kind in the immutable source module) and source nodes.
    pub type_parameters: Vec<(ExprId, BinderId)>,
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
    let mut type_parameters = Vec::new();
    let mut type_scope: Vec<(TyVarId, TyVarId)> = Vec::new();
    let mut erased_ticks = Vec::new();
    let mut locals = BTreeMap::new();
    loop {
        match module.expr(current) {
            Expr::Tick(body) => {
                erased_ticks.push(current);
                current = *body;
            }
            Expr::Lam { binder, body } => {
                let source_binder = module.binder(*binder);
                if source_binder.kind == BinderKind::Tyvar {
                    let Ty::ForAll {
                        binder: signature,
                        body: result,
                    } = ty
                    else {
                        return Err(fail(Some(current), "type lambda needs a forall type"));
                    };
                    // Uniques are used only within this explicitly paired scope.
                    if type_scope.iter().any(|(sig, local)| {
                        sig.unique == signature.unique || local.unique == source_binder.unique
                    }) {
                        return Err(fail(Some(current), "ambiguous type-variable scope"));
                    }
                    type_scope.push((
                        signature.clone(),
                        TyVarId {
                            name: source_binder.name.clone(),
                            occ: source_binder.occ.clone(),
                            unique: source_binder.unique.clone(),
                        },
                    ));
                    type_parameters.push((current, *binder));
                    ty = result;
                    current = *body;
                    continue;
                }
                let Ty::Fun { arg, res, .. } = ty else {
                    return Err(fail(Some(current), "value lambda needs a function type"));
                };
                if !same_scoped_type(arg, module.binder_ty(*binder), &type_scope) {
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
            if !same_scoped_type(ty, module.binder_ty(binder), &type_scope) {
                return Err(fail(Some(current), "returned reference type mismatch"));
            }
            if let Some(value) = locals.get(&binder) {
                *value
            } else if matches!(module.binding(binder).site, BindSite::Top) {
                let value = ValueId(params.len() as u32);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: ty.clone(),
                    },
                    operation: Operation::TopReference {
                        module: module_index,
                        binder,
                    },
                    origin: origin(Rule::TopReference),
                });
                value
            } else {
                return Err(fail(
                    Some(current),
                    "reference is neither a parameter nor a top-level binding",
                ));
            }
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
        type_params: type_scope
            .iter()
            .map(|(signature, _)| signature.clone())
            .collect(),
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
    let lowered = LoweredLeaf {
        function,
        parameters,
        type_parameters,
        erased_ticks,
    };
    verify::verify_leaf(module, module_index, owner, id, &lowered)
        .map_err(|reason| fail(Some(current), &reason))?;
    Ok(lowered)
}

/// Close explicitly paired variables before comparing signature/body types.
fn same_scoped_type(signature: &Ty, body: &Ty, scope: &[(TyVarId, TyVarId)]) -> bool {
    let mut signature = signature.clone();
    let mut body = body.clone();
    for (sig, local) in scope.iter().rev() {
        signature = Ty::ForAll {
            binder: sig.clone(),
            body: Box::new(signature),
        };
        body = Ty::ForAll {
            binder: local.clone(),
            body: Box::new(body),
        };
    }
    signature.alpha_eq(&body)
}
