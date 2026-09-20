//! Structural checks only. These do not certify correspondence with Core,
//! literal types, force placement or casts; that needs a source-aware verifier.

use std::collections::{BTreeMap, BTreeSet};

use super::*;

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
