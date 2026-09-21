//! Structural CFG checks and independent source correspondence for leaf NIR.
//! The leaf check trusts loaded, well-typed Core and its lexical resolver.
//! It does not validate GHC's literal typing or certify later lowering forms.

use std::collections::{BTreeMap, BTreeSet};

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeafAccounting {
    pub source_nodes: usize,
    pub parameter_nodes: usize,
    pub type_parameter_nodes: usize,
    pub value_nodes: usize,
    pub type_application_nodes: usize,
    pub type_argument_nodes: usize,
    pub value_application_nodes: usize,
    pub value_argument_nodes: usize,
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
    verify_leaf_impl(module, module_index, owner, id, lowered, None)
}

/// Verify against the source world, resolving imports from source names rather
/// than trusting the candidate's target module or binder.
pub fn verify_leaf_in_world(
    modules: &[h2r_core_ir::Module],
    module_index: usize,
    owner: BinderId,
    id: FnId,
    lowered: &lower::LoweredLeaf,
) -> Result<LeafAccounting, String> {
    let module = modules
        .get(module_index)
        .ok_or("module index is outside the loaded world")?;
    verify_leaf_impl(module, module_index, owner, id, lowered, Some(modules))
}

fn verify_leaf_impl(
    module: &h2r_core_ir::Module,
    module_index: usize,
    owner: BinderId,
    id: FnId,
    lowered: &lower::LoweredLeaf,
    modules: Option<&[h2r_core_ir::Module]>,
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
    let mut type_params = Vec::new();
    let mut type_scope: Vec<(TyVarId, TyVarId)> = Vec::new();
    let mut ticks = Vec::new();
    let mut leaf = None;
    let mut source_nodes = 0;
    let mut source = module.preorder(pair.rhs);
    while let Some(expr) = source.next() {
        source_nodes += 1;
        match module.expr(expr) {
            Expr::Tick(_) => ticks.push(expr),
            Expr::Lam { binder, .. } => {
                let source = module.binder(*binder);
                if source.kind == BinderKind::Tyvar {
                    let Ty::ForAll {
                        binder: signature,
                        body,
                    } = ty
                    else {
                        return Err("source type lambda lacks a forall type".into());
                    };
                    if type_scope.iter().any(|(sig, local)| {
                        sig.unique == signature.unique || local.unique == source.unique
                    }) {
                        return Err("ambiguous source type-variable scope".into());
                    }
                    type_scope.push((
                        signature.clone(),
                        TyVarId {
                            name: source.name.clone(),
                            occ: source.occ.clone(),
                            unique: source.unique.clone(),
                        },
                    ));
                    type_params.push((expr, *binder));
                    ty = body;
                    continue;
                }
                let Ty::Fun { arg, res, .. } = ty else {
                    return Err("source lambda lacks a function type".into());
                };
                let param = block
                    .params
                    .get(params.len())
                    .ok_or("missing leaf parameter")?;
                if !source_type_matches(arg, module.binder_ty(*binder), &type_scope)
                    || !arg.alpha_eq(&param.ty)
                {
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
            Expr::App { .. } => {
                if leaf.replace(expr).is_some() {
                    return Err("multiple leaf values in source".into());
                }
                // The application verifier below validates this entire subtree.
                source_nodes += source.count();
                break;
            }
            _ => return Err(format!("unsupported leaf source at expression {expr}")),
        }
    }
    if lowered.type_parameters != type_params
        || function.type_params
            != type_scope
                .iter()
                .map(|(sig, _)| sig.clone())
                .collect::<Vec<_>>()
    {
        return Err("leaf type parameter provenance mismatch".into());
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
    let mut type_applications = 0;
    let mut value_applications = 0;
    match module.expr(expr) {
        Expr::App { arg, .. } if !matches!(module.expr(*arg), Expr::Type { .. }) => {
            let mut source_args = Vec::new();
            let mut source_types = Vec::new();
            let mut head = expr;
            while let Expr::App { fun, arg } = module.expr(head) {
                if let Expr::Type { ty, .. } = module.expr(*arg) {
                    source_types.push(module.ty(*ty).clone());
                    head = *fun;
                    continue;
                }
                if !source_types.is_empty() {
                    return Err("source call interleaves type and value arguments".into());
                }
                source_args.push(*arg);
                head = *fun;
            }
            source_args.reverse();
            source_types.reverse();
            value_applications = source_args.len();
            type_applications = source_types.len();
            let primitive = primitive::resolve(module, head);
            let primitive_ty = primitive::signature();
            let target = if primitive.is_some() {
                None
            } else {
                Some(instantiate::target(module, module_index, modules, head)?)
            };
            let head_ty = target.map_or(&primitive_ty, |(_, _, ty)| ty);
            let instantiated = instantiate::apply(head_ty, &source_types)?;
            let mut signature = &instantiated;
            let arity = target.map_or(Some(2), |(m, b, _)| {
                modules.map_or(module, |world| &world[m]).binder(b).arity
            });
            if arity != Some(source_args.len() as u32) {
                return Err("source call is not saturated at known target arity".into());
            }
            if !world::closed_type(signature) || !world::closed_type(ty) {
                return Err("source call requires closed structured types".into());
            }
            let mut values = Vec::new();
            let mut argument_instructions = 0;
            for source in &source_args {
                let Ty::Fun { arg, res, .. } = signature else {
                    return Err("source call signature lacks an arrow".into());
                };
                let value = match module.expr(*source) {
                    Expr::Lit(expected) => {
                        let instruction = block
                            .instructions
                            .get(argument_instructions)
                            .ok_or("missing call literal")?;
                        let Operation::Literal(actual) = &instruction.operation else {
                            return Err("call literal was not lowered as a literal".into());
                        };
                        if actual.kind != expected.kind
                            || actual.pretty != expected.pretty
                            || instruction.origin.source != Source::Expr(*source)
                            || instruction.origin.rule != Rule::Literal
                            || !instruction.result.ty.alpha_eq(arg)
                        {
                            return Err("call literal differs from source".into());
                        }
                        argument_instructions += 1;
                        instruction.result.id
                    }
                    Expr::Var { .. } => {
                        let parameter = module.resolve(*source).and_then(|binder| {
                            params.iter().find(|(_, source, _)| *source == binder)
                        });
                        if let Some(parameter) = parameter {
                            let value = block
                                .params
                                .iter()
                                .find(|value| value.id == parameter.2)
                                .ok_or("missing call source parameter")?;
                            if !arg.alpha_eq(&value.ty) {
                                return Err("source call parameter type mismatch".into());
                            }
                            value.id
                        } else {
                            let (argument_module, argument_binder, argument_ty) =
                                instantiate::target(module, module_index, modules, *source)?;
                            if !world::closed_type(argument_ty) || !arg.alpha_eq(argument_ty) {
                                return Err("source top-level argument type mismatch".into());
                            }
                            let instruction = block
                                .instructions
                                .get(argument_instructions)
                                .ok_or("missing top-level call argument")?;
                            if !matches!(instruction.operation, Operation::TopReference { module, binder }
                                if module == argument_module && binder == argument_binder)
                                || instruction.origin.source != Source::Expr(*source)
                                || instruction.origin.rule != Rule::TopReference
                                || !instruction.result.ty.alpha_eq(arg)
                            {
                                return Err("top-level call argument differs from source".into());
                            }
                            argument_instructions += 1;
                            instruction.result.id
                        }
                    }
                    _ => return Err("unsupported call source argument".into()),
                };
                values.push(value);
                signature = res;
            }
            if block.instructions.len() != argument_instructions + 1 {
                return Err("direct call must contain only its atomic arguments and call".into());
            }
            let instruction = &block.instructions[argument_instructions];
            let expected_rule = if let Some(expected) = primitive {
                if !matches!(&instruction.operation, Operation::IntArithmetic { op, arguments }
                    if *op == expected && arguments == &values)
                {
                    return Err("primitive operation or arguments differ from source".into());
                }
                Rule::IntArithmetic
            } else {
                let (target_module, target_binder, _) = target.expect("resolved source target");
                let Operation::CallTop {
                    module: target,
                    binder,
                    type_arguments,
                    arguments,
                } = &instruction.operation
                else {
                    return Err("source call was not lowered as a direct call".into());
                };
                if (*target, *binder) != (target_module, target_binder)
                    || arguments != &values
                    || type_arguments != &source_types
                {
                    return Err("direct call target or arguments differ from source".into());
                }
                Rule::CallTop
            };
            if instruction.origin.source != Source::Expr(expr)
                || instruction.origin.rule != expected_rule
            {
                return Err("direct call origin mismatch".into());
            }
            if instruction.result.id != returned
                || !signature.alpha_eq(ty)
                || !instruction.result.ty.alpha_eq(ty)
            {
                return Err("direct call result mismatch".into());
            }
        }
        Expr::App { .. } => {
            // Read argument order from the source, never from candidate NIR.
            let mut spine = Vec::new();
            let mut head = expr;
            loop {
                match module.expr(head) {
                    Expr::App { fun, arg } => {
                        if !matches!(module.expr(*arg), Expr::Type { .. }) {
                            return Err("source application has a value argument".into());
                        }
                        spine.push(*arg);
                        head = *fun;
                    }
                    Expr::Var { .. } => break,
                    _ => return Err("unsupported source type application head".into()),
                }
            }
            let arguments: Vec<_> = spine
                .iter()
                .rev()
                .map(|arg| {
                    let Expr::Type { ty, .. } = module.expr(*arg) else {
                        unreachable!()
                    };
                    module.ty(*ty).clone()
                })
                .collect();
            type_applications = arguments.len();
            let (target_module, target_binder, head_ty) =
                instantiate::target(module, module_index, modules, head)?;
            let expected = instantiate::apply(head_ty, &arguments)?;
            if !world::closed_type(ty) || !expected.alpha_eq(ty) {
                return Err("source type application result mismatch".into());
            }
            let [instruction] = block.instructions.as_slice() else {
                return Err("type application must have exactly one instruction".into());
            };
            let Operation::InstantiateTop {
                module: target,
                binder,
                arguments: actual,
            } = &instruction.operation
            else {
                return Err("source type application lacks instantiation evidence".into());
            };
            if (*target, *binder) != (target_module, target_binder) || actual != &arguments {
                return Err("type application target or arguments differ from source".into());
            }
            if instruction.origin.source != Source::Expr(expr)
                || instruction.origin.rule != Rule::InstantiateTop
            {
                return Err("type application origin mismatch".into());
            }
            if instruction.result.id != returned || !instruction.result.ty.alpha_eq(&expected) {
                return Err("type application result mismatch".into());
            }
        }
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
        Expr::Var { name, .. } if module.reference(expr) == Some(h2r_core_ir::Ref::Global) => {
            let modules = modules.ok_or("import source requires a loaded world")?;
            let (target_module, target_binder) = world::imported_top(modules, name)?;
            let target_ty = modules[target_module].binder_ty(target_binder);
            if !world::closed_type(ty) || !world::closed_type(target_ty) || !ty.alpha_eq(target_ty)
            {
                return Err("import source lacks matching closed structured types".into());
            }
            let [instruction] = block.instructions.as_slice() else {
                return Err("import leaf must have exactly one instruction".into());
            };
            if !matches!(instruction.operation, Operation::TopReference { module, binder } if module == target_module && binder == target_binder)
            {
                return Err("import target differs from source".into());
            }
            if instruction.origin.source != Source::Expr(expr)
                || instruction.origin.rule != Rule::TopReference
            {
                return Err("import origin mismatch".into());
            }
            if instruction.result.id != returned || !instruction.result.ty.alpha_eq(ty) {
                return Err("import result mismatch".into());
            }
        }
        Expr::Var { .. } => {
            let binder = module
                .resolve(expr)
                .ok_or("leaf source is not a local reference")?;
            if !source_type_matches(ty, module.binder_ty(binder), &type_scope) {
                return Err("returned reference type differs from source".into());
            }
            let param = params.iter().find(|(_, source, _)| *source == binder);
            if let Some(param) = param {
                if !block.instructions.is_empty() {
                    return Err("parameter leaf must not introduce instructions".into());
                }
                if param.2 != returned {
                    return Err("returned parameter differs from source".into());
                }
            } else {
                // Independently enumerate top-level pairs rather than trusting
                // the builder's binding-site test or the candidate's target.
                if !module
                    .top
                    .iter()
                    .flat_map(|bind| &bind.pairs)
                    .any(|pair| pair.binder == binder)
                {
                    return Err("leaf source does not refer to a top-level binding".into());
                }
                if block.instructions.len() != 1 {
                    return Err("top reference leaf must have exactly one instruction".into());
                }
                let instruction = &block.instructions[0];
                if !matches!(instruction.operation, Operation::TopReference { module, binder: target } if module == module_index && target == binder)
                {
                    return Err("top reference target differs from source".into());
                }
                if instruction.origin.source != Source::Expr(expr)
                    || instruction.origin.rule != Rule::TopReference
                {
                    return Err("top reference origin mismatch".into());
                }
                if instruction.result.id != returned || !instruction.result.ty.alpha_eq(ty) {
                    return Err("top reference result mismatch".into());
                }
            }
        }
        _ => return Err("unsupported leaf value".into()),
    }
    let accounting = LeafAccounting {
        source_nodes,
        parameter_nodes: params.len(),
        type_parameter_nodes: type_params.len(),
        value_nodes: 1,
        type_application_nodes: type_applications,
        type_argument_nodes: type_applications,
        value_application_nodes: value_applications,
        value_argument_nodes: value_applications,
        erased_ticks: ticks.len(),
    };
    // Counts source nodes, not NIR instructions: a literal's instruction and
    // return share a source node; lambda nodes become entry parameters.
    if source_nodes
        != accounting.parameter_nodes
            + accounting.type_parameter_nodes
            + accounting.value_nodes
            + accounting.type_application_nodes
            + accounting.type_argument_nodes
            + accounting.value_application_nodes
            + accounting.value_argument_nodes
            + accounting.erased_ticks
    {
        return Err("leaf source accounting does not close".into());
    }
    Ok(accounting)
}

// Rebuild quantified types independently of the lowering builder. Only the
// source IR's structural alpha-equivalence is shared.
fn source_type_matches(expected: &Ty, actual: &Ty, binders: &[(TyVarId, TyVarId)]) -> bool {
    let mut expected = expected.clone();
    let mut actual = actual.clone();
    for (signature, source) in binders.iter().rev() {
        expected = Ty::ForAll {
            binder: signature.clone(),
            body: Box::new(expected),
        };
        actual = Ty::ForAll {
            binder: source.clone(),
            body: Box::new(actual),
        };
    }
    expected.alpha_eq(&actual)
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
                Operation::Literal(_)
                | Operation::TopReference { .. }
                | Operation::InstantiateTop { .. } => {}
                Operation::Move(value) | Operation::Force(value) => {
                    if !available.contains_key(&value) {
                        return Err(format!("unavailable operand {value:?}"));
                    }
                }
                Operation::IntArithmetic { ref arguments, .. } => {
                    let signature = primitive::signature();
                    let Ty::Fun { arg: int, .. } = signature else {
                        unreachable!()
                    };
                    if arguments.len() != 2
                        || !instruction.result.ty.alpha_eq(&int)
                        || arguments
                            .iter()
                            .any(|v| !available.get(v).is_some_and(|ty| ty.alpha_eq(&int)))
                    {
                        return Err("Int# arithmetic requires two available Int# operands and an Int# result".into());
                    }
                }
                Operation::CallTop { ref arguments, .. } => {
                    for value in arguments {
                        if !available.contains_key(value) {
                            return Err(format!("unavailable call argument {value:?}"));
                        }
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
            type_params: vec![],
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
