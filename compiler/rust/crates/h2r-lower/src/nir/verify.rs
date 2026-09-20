//! Structural CFG checks and independent source correspondence for leaf NIR.
//! The leaf check trusts loaded, well-typed Core and its lexical resolver.
//! It does not validate GHC's literal typing or certify later lowering forms.

use std::collections::{BTreeMap, BTreeSet};

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeafAccounting {
    pub source_nodes: usize,
    pub parameter_nodes: usize,
    pub value_nodes: usize,
    pub erased_ticks: usize,
}

/// Independently check the complete supported source subtree. Never rerun the
/// lowering builder or infer correctness from its origin records alone. Expected
/// identity is supplied by the caller, not taken from the candidate function.
/// IDs may be renumbered; parameter order and source ownership may not change.
pub fn verify_leaf(
    module: &h2r_core_ir::Module,
    module_index: usize,
    owner: BinderId,
    id: FnId,
    lowered: &lower::LoweredLeaf,
) -> Result<LeafAccounting, String> {
    use h2r_core_ir::{BinderKind, Expr};

    let function = &lowered.function;
    if (function.module, function.owner, function.id) != (module_index, owner, id) {
        return Err("leaf identity mismatch".into());
    }
    let pair = module
        .top
        .iter()
        .flat_map(|b| &b.pairs)
        .find(|pair| pair.binder == owner)
        .ok_or("leaf owner is not a top-level binding")?;
    verify(function)?;
    if function.blocks.len() != 1 {
        return Err("leaf must have exactly one block".into());
    }
    let block = &function.blocks[0];
    let Exit::Return(returned) = block.terminator.exit else {
        return Err("leaf must terminate with return".into());
    };
    let mut ty = module.binder_ty(owner);
    let mut params = Vec::new();
    let mut ticks = Vec::new();
    let mut leaf = None;
    let mut source_nodes = 0;
    for expr in module.preorder(pair.rhs) {
        source_nodes += 1;
        match module.expr(expr) {
            Expr::Tick(_) => ticks.push(expr),
            Expr::Lam { binder, .. } => {
                if module.binder(*binder).kind != BinderKind::Id {
                    return Err("unsupported type lambda in leaf source".into());
                }
                let Ty::Fun { arg, res, .. } = ty else {
                    return Err("source lambda lacks a function type".into());
                };
                let param = block
                    .params
                    .get(params.len())
                    .ok_or("missing leaf parameter")?;
                if !arg.alpha_eq(module.binder_ty(*binder)) || !arg.alpha_eq(&param.ty) {
                    return Err("leaf parameter type differs from source".into());
                }
                params.push((expr, *binder, param.id));
                ty = res;
            }
            Expr::Lit(_) | Expr::Var { .. } => {
                if leaf.replace(expr).is_some() {
                    return Err("multiple leaf values in source".into());
                }
            }
            _ => return Err(format!("unsupported leaf source at expression {expr}")),
        }
    }
    if params.len() != block.params.len()
        || lowered.parameters
            != params
                .iter()
                .map(|(expr, _, value)| (*expr, *value))
                .collect::<Vec<_>>()
    {
        return Err("leaf parameter provenance mismatch".into());
    }
    if ticks != lowered.erased_ticks {
        return Err("erased tick provenance mismatch".into());
    }
    if !ty.alpha_eq(&function.result_ty) {
        return Err("leaf result type differs from source".into());
    }
    let expr = leaf.ok_or("missing leaf value in source")?;
    let return_origin = &block.terminator.origin;
    if return_origin.source != Source::Expr(expr) || return_origin.rule != Rule::Return {
        return Err("leaf return origin mismatch".into());
    }
    match module.expr(expr) {
        Expr::Lit(source) => {
            if block.instructions.len() != 1 {
                return Err("literal leaf must have exactly one instruction".into());
            }
            let instruction = &block.instructions[0];
            let Operation::Literal(literal) = &instruction.operation else {
                return Err("source literal was not lowered as a literal".into());
            };
            if literal.kind != source.kind || literal.pretty != source.pretty {
                return Err("literal payload differs from source".into());
            }
            if instruction.origin.source != Source::Expr(expr)
                || instruction.origin.rule != Rule::Literal
            {
                return Err("literal origin mismatch".into());
            }
            if instruction.result.id != returned || !instruction.result.ty.alpha_eq(ty) {
                return Err("literal result mismatch".into());
            }
        }
        Expr::Var { .. } => {
            if !block.instructions.is_empty() {
                return Err("parameter leaf must not introduce instructions".into());
            }
            let binder = module
                .resolve(expr)
                .ok_or("leaf source is not a local reference")?;
            let param = params
                .iter()
                .find(|(_, source, _)| *source == binder)
                .ok_or("leaf source does not refer to a parameter")?;
            if param.2 != returned || !module.binder_ty(binder).alpha_eq(ty) {
                return Err("returned parameter differs from source".into());
            }
        }
        _ => return Err("unsupported leaf value".into()),
    }
    let accounting = LeafAccounting {
        source_nodes,
        parameter_nodes: params.len(),
        value_nodes: 1,
        erased_ticks: ticks.len(),
    };
    // Counts source nodes, not NIR instructions: a literal's instruction and
    // return share a source node; lambda nodes become entry parameters.
    if source_nodes != accounting.parameter_nodes + accounting.value_nodes + accounting.erased_ticks
    {
        return Err("leaf source accounting does not close".into());
    }
    Ok(accounting)
}

/// Reject malformed CFGs and SSA uses. Block-local availability is deliberately
/// stronger than dominance: all incoming values must be explicit parameters.
pub fn verify(function: &Function) -> Result<(), String> {
    let mut blocks = BTreeMap::new();
    let mut definitions = BTreeSet::new();
    for block in &function.blocks {
        if blocks.insert(block.id, block).is_some() {
            return Err(format!("duplicate block {:?}", block.id));
        }
        for value in block
            .params
            .iter()
            .chain(block.instructions.iter().map(|i| &i.result))
        {
            if !definitions.insert(value.id) {
                return Err(format!("duplicate value {:?}", value.id));
            }
        }
    }
    if !blocks.contains_key(&function.entry) {
        return Err("missing entry block".into());
    }
    for block in &function.blocks {
        let mut available: BTreeMap<_, _> = block.params.iter().map(|v| (v.id, &v.ty)).collect();
        for instruction in &block.instructions {
            if instruction.origin.module != function.module {
                return Err("instruction origin belongs to another module".into());
            }
            match instruction.operation {
                Operation::Literal(_) => {}
                Operation::Move(value) | Operation::Force(value) => {
                    if !available.contains_key(&value) {
                        return Err(format!("unavailable operand {value:?}"));
                    }
                }
            }
            available.insert(instruction.result.id, &instruction.result.ty);
        }
        if block.terminator.origin.module != function.module {
            return Err("terminator origin belongs to another module".into());
        }
        match &block.terminator.exit {
            Exit::Return(value) => {
                let ty = available
                    .get(value)
                    .ok_or_else(|| format!("unavailable return {value:?}"))?;
                if !ty.alpha_eq(&function.result_ty) {
                    return Err("return type mismatch".into());
                }
            }
            Exit::Jump { target, args } => {
                let target = blocks
                    .get(target)
                    .ok_or_else(|| format!("missing jump target {target:?}"))?;
                if args.len() != target.params.len() {
                    return Err("jump argument count mismatch".into());
                }
                for (arg, param) in args.iter().zip(&target.params) {
                    let ty = available
                        .get(arg)
                        .ok_or_else(|| format!("unavailable jump argument {arg:?}"))?;
                    if !ty.alpha_eq(&param.ty) {
                        return Err("jump argument type mismatch".into());
                    }
                }
            }
        }
    }
    let mut visited = BTreeSet::new();
    let mut pending = vec![function.entry];
    while let Some(id) = pending.pop() {
        if visited.insert(id)
            && let Exit::Jump { target, .. } = &blocks[&id].terminator.exit
        {
            pending.push(*target);
        }
    }
    if visited.len() != blocks.len() {
        return Err("unreachable block".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> Function {
        let ty = Ty::Lit {
            kind: "Nat".into(),
            text: "1".into(),
        };
        let origin = Origin {
            module: 0,
            source: Source::Expr(0),
            rule: Rule::Return,
        };
        Function {
            id: FnId(0),
            module: 0,
            owner: 0,
            result_ty: ty.clone(),
            entry: BlockId(0),
            blocks: vec![Block {
                id: BlockId(0),
                params: vec![Value { id: ValueId(0), ty }],
                instructions: vec![],
                terminator: Terminator {
                    exit: Exit::Return(ValueId(0)),
                    origin,
                },
            }],
        }
    }

    #[test]
    fn accepts_identity_and_explicit_block_arguments() {
        let mut f = fixture();
        assert_eq!(verify(&f), Ok(()));
        let mut next = f.blocks[0].clone();
        next.id = BlockId(1);
        next.params[0].id = ValueId(1);
        next.terminator.exit = Exit::Return(ValueId(1));
        f.blocks[0].terminator.exit = Exit::Jump {
            target: next.id,
            args: vec![ValueId(0)],
        };
        f.blocks[0].terminator.origin.rule = Rule::Jump;
        f.blocks.push(next);
        assert_eq!(verify(&f), Ok(()));
        f.blocks[1].terminator.exit = Exit::Return(ValueId(0));
        assert!(verify(&f).unwrap_err().contains("unavailable return"));
    }

    #[test]
    fn rejects_corrupted_graphs() {
        for corruption in 0..7 {
            let mut f = fixture();
            match corruption {
                0 => f.entry = BlockId(99),
                1 => f.blocks.push(f.blocks[0].clone()),
                2 => {
                    let duplicate = f.blocks[0].params[0].clone();
                    f.blocks[0].params.push(duplicate);
                }
                3 => f.blocks[0].terminator.exit = Exit::Return(ValueId(99)),
                4 => {
                    f.blocks[0].terminator.exit = Exit::Jump {
                        target: BlockId(99),
                        args: vec![],
                    }
                }
                5 => f.blocks[0].terminator.origin.module = 1,
                _ => {
                    f.result_ty = Ty::Lit {
                        kind: "Nat".into(),
                        text: "2".into(),
                    }
                }
            }
            assert!(verify(&f).is_err(), "corruption {corruption}");
        }
    }

    #[test]
    fn rejects_unreachable_blocks_and_bad_jump_arity() {
        let mut f = fixture();
        let mut next = f.blocks[0].clone();
        next.id = BlockId(1);
        next.params[0].id = ValueId(1);
        next.terminator.exit = Exit::Return(ValueId(1));
        f.blocks.push(next);
        assert_eq!(verify(&f).unwrap_err(), "unreachable block");
        f.blocks[0].terminator.exit = Exit::Jump {
            target: BlockId(1),
            args: vec![],
        };
        assert_eq!(verify(&f).unwrap_err(), "jump argument count mismatch");
    }

    #[test]
    fn checks_instruction_order_and_origins() {
        let mut f = fixture();
        f.blocks[0].instructions.push(Instruction {
            result: Value {
                id: ValueId(1),
                ty: f.result_ty.clone(),
            },
            operation: Operation::Force(ValueId(0)),
            origin: Origin {
                module: 0,
                source: Source::Expr(1),
                rule: Rule::StrictPosition,
            },
        });
        f.blocks[0].terminator.exit = Exit::Return(ValueId(1));
        assert_eq!(verify(&f), Ok(()));
        f.blocks[0].instructions[0].operation = Operation::Move(ValueId(1));
        assert!(verify(&f).unwrap_err().contains("unavailable operand"));
        f.blocks[0].instructions[0].operation = Operation::Move(ValueId(0));
        f.blocks[0].instructions[0].origin.module = 1;
        assert!(verify(&f).unwrap_err().contains("origin"));
    }

    #[test]
    fn accepts_cycles_but_checks_jump_types_and_uses() {
        let mut f = fixture();
        f.blocks[0].terminator.exit = Exit::Jump {
            target: BlockId(0),
            args: vec![ValueId(0)],
        };
        f.blocks[0].terminator.origin.rule = Rule::Jump;
        assert_eq!(verify(&f), Ok(()));
        f.blocks[0].terminator.exit = Exit::Jump {
            target: BlockId(0),
            args: vec![ValueId(9)],
        };
        assert!(
            verify(&f)
                .unwrap_err()
                .contains("unavailable jump argument")
        );
        f.blocks[0].instructions.push(Instruction {
            result: Value {
                id: ValueId(1),
                ty: Ty::Lit {
                    kind: "Nat".into(),
                    text: "2".into(),
                },
            },
            operation: Operation::Move(ValueId(0)),
            origin: Origin {
                module: 0,
                source: Source::Expr(1),
                rule: Rule::EraseCast,
            },
        });
        f.blocks[0].terminator.exit = Exit::Jump {
            target: BlockId(0),
            args: vec![ValueId(1)],
        };
        assert_eq!(verify(&f).unwrap_err(), "jump argument type mismatch");
    }
}
