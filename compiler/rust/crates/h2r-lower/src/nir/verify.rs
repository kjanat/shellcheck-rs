//! Structural CFG checks and independent source correspondence for leaf NIR.
//! The leaf check trusts loaded, well-typed Core and its lexical resolver.
//! It does not validate GHC's literal typing or certify later lowering forms.

use std::collections::{BTreeMap, BTreeSet};

use super::view::TypeView;
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LeafAccounting {
    pub source_nodes: usize,
    pub parameter_nodes: usize,
    pub type_parameter_nodes: usize,
    /// Type lambdas specialization consumed, one per instance type argument.
    pub type_instantiation_nodes: usize,
    /// Dictionary lambdas specialization consumed, one per instance dictionary.
    pub dictionary_parameter_nodes: usize,
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
    verify_leaf_impl(module, module_index, owner, id, lowered, None, &[], &[])
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
    verify_leaf_specialized(modules, module_index, owner, id, lowered, &[], &[])
}

/// Verify one instance. The expected type and dictionary arguments come from
/// the caller; the substitution and dictionary scope they induce are re-derived
/// from the source, never read back out of the candidate's own evidence.
#[allow(clippy::too_many_arguments)]
pub fn verify_leaf_specialized(
    modules: &[h2r_core_ir::Module],
    module_index: usize,
    owner: BinderId,
    id: FnId,
    lowered: &lower::LoweredLeaf,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
) -> Result<LeafAccounting, String> {
    let module = modules
        .get(module_index)
        .ok_or("module index is outside the loaded world")?;
    verify_leaf_impl(
        module,
        module_index,
        owner,
        id,
        lowered,
        Some(modules),
        type_arguments,
        dictionaries,
    )
}

#[allow(clippy::too_many_arguments)]
fn verify_leaf_impl(
    module: &h2r_core_ir::Module,
    module_index: usize,
    owner: BinderId,
    id: FnId,
    lowered: &lower::LoweredLeaf,
    modules: Option<&[h2r_core_ir::Module]>,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
) -> Result<LeafAccounting, String> {
    use h2r_core_ir::{BinderKind, Expr};

    let function = &lowered.function;
    if (function.module, function.owner, function.id) != (module_index, owner, id) {
        return Err("leaf identity mismatch".into());
    }
    if function.type_arguments.len() != type_arguments.len()
        || function
            .type_arguments
            .iter()
            .zip(type_arguments)
            .any(|(claimed, expected)| !claimed.alpha_eq(expected))
    {
        return Err("leaf specialization evidence differs from the requested instance".into());
    }
    if !same_dictionaries(&function.dictionaries, dictionaries) {
        return Err("leaf dictionary evidence differs from the requested instance".into());
    }
    let pair = module
        .top
        .iter()
        .flat_map(|b| &b.pairs)
        .find(|pair| pair.binder == owner)
        .ok_or("leaf owner is not a top-level binding")?;
    verify(function)?;
    let block = function
        .blocks
        .iter()
        .find(|b| b.id == function.entry)
        .ok_or("missing entry")?;
    let (subst, signature) = lower::bind_type_arguments(module, pair.rhs, owner, type_arguments)?;
    let view = TypeView::specialized(module, &subst);
    let mut ty = &signature;
    let mut params = Vec::new();
    let mut type_params = Vec::new();
    let mut type_instantiations = Vec::new();
    let mut dictionary_parameters = Vec::new();
    let mut dictionary_scope: BTreeMap<BinderId, DictionaryRef> = BTreeMap::new();
    let world = World {
        module,
        index: module_index,
        modules,
    };
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
                    if type_instantiations.len() < type_arguments.len() {
                        type_instantiations.push((
                            expr,
                            *binder,
                            type_arguments[type_instantiations.len()].clone(),
                        ));
                        continue;
                    }
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
                if !source_type_matches(arg, view.binder_ty(*binder), &type_scope) {
                    return Err("leaf parameter type differs from source".into());
                }
                if dictionary_parameters.len() < dictionaries.len() {
                    let reference = &dictionaries[dictionary_parameters.len()];
                    if !arg.alpha_eq(&dict::reference_type(&world, reference)?) {
                        return Err(
                            "source dictionary parameter differs from the instance's dictionary"
                                .into(),
                        );
                    }
                    dictionary_parameters.push((expr, *binder, reference.clone()));
                    dictionary_scope.insert(*binder, reference.clone());
                    ty = res;
                    continue;
                }
                let param = block
                    .params
                    .get(params.len())
                    .ok_or("missing leaf parameter")?;
                if !arg.alpha_eq(&param.ty) {
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
            Expr::App { .. } | Expr::Case { .. } | Expr::Let { .. } => {
                if leaf.replace(expr).is_some() {
                    return Err("multiple leaf values in source".into());
                }
                // The expression verifier below validates this entire subtree.
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
    if type_instantiations.len() != type_arguments.len()
        || lowered.type_instantiations.len() != type_instantiations.len()
        || lowered
            .type_instantiations
            .iter()
            .zip(&type_instantiations)
            .any(|(claimed, expected)| {
                (claimed.0, claimed.1) != (expected.0, expected.1)
                    || !claimed.2.alpha_eq(&expected.2)
            })
    {
        return Err("leaf specialization provenance mismatch".into());
    }
    if dictionary_parameters.len() != dictionaries.len()
        || lowered.dictionary_parameters.len() != dictionary_parameters.len()
        || lowered
            .dictionary_parameters
            .iter()
            .zip(&dictionary_parameters)
            .any(|(claimed, expected)| {
                (claimed.0, claimed.1) != (expected.0, expected.1) || !claimed.2.same(&expected.2)
            })
    {
        return Err("leaf dictionary provenance mismatch".into());
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
    let visited = std::cell::RefCell::new(BTreeSet::new());
    let context = ValueContext {
        module,
        view: &view,
        module_index,
        modules,
        params: &params,
        type_scope: &type_scope,
        subst: &subst,
        dictionary_scope: &dictionary_scope,
        function,
        visited: &visited,
        functions: &BTreeMap::new(),
    };
    let (type_applications, value_applications, value_nodes) =
        verify_tail(&context, function, block.id, expr, ty)?;
    if visited.borrow().len() != function.blocks.len() {
        return Err("source correspondence leaves unused blocks".into());
    }
    let accounting = LeafAccounting {
        source_nodes,
        parameter_nodes: params.len(),
        type_parameter_nodes: type_params.len(),
        type_instantiation_nodes: type_instantiations.len(),
        dictionary_parameter_nodes: dictionary_parameters.len(),
        value_nodes,
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
            + accounting.type_instantiation_nodes
            + accounting.dictionary_parameter_nodes
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

struct ValueContext<'a> {
    function: &'a Function,
    visited: &'a std::cell::RefCell<BTreeSet<BlockId>>,
    module: &'a h2r_core_ir::Module,
    view: &'a TypeView<'a>,
    module_index: usize,
    modules: Option<&'a [h2r_core_ir::Module]>,
    params: &'a [(ExprId, BinderId, ValueId)],
    type_scope: &'a [(TyVarId, TyVarId)],
    subst: &'a super::subst::Substitution,
    dictionary_scope: &'a BTreeMap<BinderId, DictionaryRef>,
    functions: &'a BTreeMap<BinderId, (BlockId, Vec<BinderId>, usize)>,
}

impl<'a> ValueContext<'a> {
    fn world(&self) -> World<'a> {
        World {
            module: self.module,
            index: self.module_index,
            modules: self.modules,
        }
    }

    fn scope(&self) -> dict::Scope<'a> {
        dict::Scope {
            module: self.module_index,
            types: self.subst,
            dictionaries: self.dictionary_scope,
        }
    }
}

fn verify_tail(
    context: &ValueContext<'_>,
    function: &Function,
    id: BlockId,
    expr: ExprId,
    ty: &Ty,
) -> Result<(usize, usize, usize), String> {
    if !context.visited.borrow_mut().insert(id) {
        return Err("source branch is cyclic or shared".into());
    }
    let block = function
        .blocks
        .iter()
        .find(|b| b.id == id)
        .ok_or("missing source branch")?;
    if block.terminator.origin.source != Source::Expr(expr) {
        return Err("tail origin differs from source".into());
    }
    let module = context.module;
    let view = context.view;
    let world = context.world();
    match (&block.terminator.exit, module.expr(expr)) {
        (
            Exit::IntSwitch {
                scrutinee,
                arms,
                default,
                args,
            },
            h2r_core_ir::Expr::Case {
                scrut,
                binder,
                ty: result_ty,
                alts,
                ..
            },
        ) => {
            if block.terminator.origin.rule != Rule::IntSwitch
                || !primitive::is_int(view.binder_ty(*binder))
                || !data::supported(&world, ty)
                || !view.ty(*result_ty).alpha_eq(ty)
                || alts.iter().any(|a| !a.binders.is_empty())
            {
                return Err("invalid scalar source switch".into());
            }
            let (mut nt, mut nv, mut nn) =
                verify_value(context, block, *scrut, view.binder_ty(*binder), *scrutinee)?;
            nn += 1; // The source case node, separate from its scrutinee and arms.
            let mut expected_args: Vec<_> = block.params.iter().map(|p| p.id).collect();
            expected_args.push(*scrutinee);
            if *args != expected_args {
                return Err("switch environment differs from source".into());
            }
            let mut seen_patterns = BTreeSet::new();
            let mut defaults = 0;
            let mut arm_index = 0;
            for alt in alts {
                let target = match &alt.con {
                    h2r_core_ir::AltCon::Default => {
                        defaults += 1;
                        *default
                    }
                    h2r_core_ir::AltCon::LitAlt { lit } => {
                        let literal = primitive::int_literal(lit)?;
                        if !seen_patterns.insert(literal) {
                            return Err("duplicate source pattern".into());
                        }
                        let (pattern, target) = arms.get(arm_index).ok_or("missing switch arm")?;
                        arm_index += 1;
                        if *pattern != literal {
                            return Err("switch pattern differs from source".into());
                        }
                        *target
                    }
                    _ => return Err("non-scalar source alternative".into()),
                };
                let target_block = function
                    .blocks
                    .iter()
                    .find(|b| b.id == target)
                    .ok_or("missing switch block")?;
                if target_block.params.len() != block.params.len() + 1 {
                    return Err("source branch environment arity mismatch".into());
                }
                let mut params = Vec::new();
                for (origin, binder, value) in context.params {
                    let position = block
                        .params
                        .iter()
                        .position(|p| p.id == *value)
                        .ok_or("unknown source environment value")?;
                    params.push((*origin, *binder, target_block.params[position].id));
                }
                params.push((
                    expr,
                    *binder,
                    target_block.params.last().ok_or("missing case binder")?.id,
                ));
                let branch_context = ValueContext {
                    params: &params,
                    ..*context
                };
                let (bt, bv, bn) = verify_tail(&branch_context, function, target, alt.rhs, ty)?;
                nt += bt;
                nv += bv;
                nn += bn;
            }
            if defaults != 1 || arm_index != arms.len() {
                return Err("switch alternative census mismatch".into());
            }
            Ok((nt, nv, nn))
        }
        (Exit::Return(returned), _) if block.terminator.origin.rule == Rule::Return => {
            verify_value(context, block, expr, ty, *returned)
        }
        _ => Err("terminator differs from source control flow".into()),
    }
}

/// Walk source expressions independently, consuming exactly the corresponding
/// instruction slice. Strict case markers split evaluation from its continuation.
fn verify_value(
    context: &ValueContext<'_>,
    block: &Block,
    expr: ExprId,
    ty: &Ty,
    returned: ValueId,
) -> Result<(usize, usize, usize), String> {
    use h2r_core_ir::Expr;
    let ValueContext {
        module,
        view,
        module_index,
        modules,
        params,
        type_scope,
        ..
    } = *context;
    let world = context.world();
    if let [instruction] = block.instructions.as_slice()
        && let Operation::EvaluateBlock { target, arguments }
        | Operation::DelayBlock { target, arguments } = &instruction.operation
    {
        let delayed = matches!(instruction.operation, Operation::DelayBlock { .. });
        let valid_source = if delayed {
            data::lifted(&world, ty)
        } else {
            matches!(module.expr(expr), Expr::Case { .. } | Expr::Let { .. })
        };
        if !valid_source
            || !data::supported(&world, ty)
            || instruction.origin.source != Source::Expr(expr)
            || instruction.origin.rule
                != if delayed {
                    Rule::DelayBlock
                } else {
                    Rule::EvaluateBlock
                }
            || instruction.result.id != returned
            || !instruction.result.ty.alpha_eq(ty)
        {
            return Err("scalar region result or source mismatch".into());
        }
        let target_block = context
            .function
            .blocks
            .iter()
            .find(|b| b.id == *target)
            .ok_or("missing scalar region")?;
        let mut captured = context.params.to_vec();
        captured.sort_by_key(|(_, binder, _)| *binder);
        if arguments
            != &captured
                .iter()
                .map(|(_, _, value)| *value)
                .collect::<Vec<_>>()
            || target_block.params.len() != captured.len()
        {
            return Err("scalar region captures differ from source scope".into());
        }
        let params: Vec<_> = captured
            .iter()
            .zip(&target_block.params)
            .map(|((origin, binder, _), value)| (*origin, *binder, value.id))
            .collect();
        let region_context = ValueContext {
            params: &params,
            ..*context
        };
        return verify_tail(&region_context, context.function, *target, expr, ty);
    }
    if let Some(counts) = verify_constructor(context, block, expr, ty, returned)? {
        return Ok(counts);
    }
    if matches!(module.expr(expr), Expr::Lam { .. }) {
        return verify_lambda(context, block, expr, ty, returned);
    }
    if let Expr::Case { binder, .. } = module.expr(expr)
        && data::is_data(&world, view.binder_ty(*binder))
    {
        return verify_data_case(context, block, expr, ty, returned);
    }
    let mut value_nodes = 1;
    let mut type_applications = 0;
    let mut value_applications = 0;
    match module.expr(expr) {
        Expr::App { arg, .. } if !matches!(module.expr(*arg), Expr::Type { .. }) => {
            let mut source_args = Vec::new();
            let mut source_types = Vec::new();
            let mut head = expr;
            while let Expr::App { fun, arg } = module.expr(head) {
                if let Expr::Type { ty, .. } = module.expr(*arg) {
                    source_types.push(view.ty(*ty).clone());
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
            let constructor = boxed::resolves(module, head);
            let local = module
                .resolve(head)
                .and_then(|b| context.functions.get(&b).map(|f| (b, f)));
            let indirect = module
                .resolve(head)
                .filter(|b| params.iter().any(|(_, binder, _)| binder == b));
            let primitive_ty = if constructor {
                boxed::signature()
            } else {
                primitive::signature()
            };
            let target =
                if primitive.is_some() || constructor || local.is_some() || indirect.is_some() {
                    None
                } else {
                    Some(
                        dict::call_target(
                            &context.world(),
                            &context.scope(),
                            head,
                            &source_types,
                            &source_args,
                        )?
                        .ok_or("source application requires a top-level binding")?,
                    )
                };
            // The dictionary arguments the instance key absorbed are still
            // source nodes, and are accounted here rather than lowered.
            for erased in target.iter().flat_map(|resolved| &resolved.erased) {
                value_nodes += module.preorder(*erased).count() - 1;
            }
            let head_ty = indirect.map_or_else(
                || {
                    local.map_or_else(
                        || {
                            target
                                .as_ref()
                                .map_or(&primitive_ty, |resolved| &resolved.signature)
                        },
                        |(b, _)| view.binder_ty(b),
                    )
                },
                |b| view.binder_ty(b),
            );
            let instantiated = match &target {
                Some(resolved) => resolved.signature.clone(),
                None => instantiate::apply(head_ty, &source_types)?,
            };
            let mut signature = &instantiated;
            let source_args = match &target {
                Some(resolved) => resolved.arguments.clone(),
                None => source_args,
            };
            let arity = local.map_or_else(
                || {
                    target
                        .as_ref()
                        .map_or(Some(if constructor { 1 } else { 2 }), |resolved| {
                            Some(resolved.arity as u32)
                        })
                },
                |(_, (_, _, arity))| Some(*arity as u32),
            );
            let apply = indirect.is_some() || arity != Some(source_args.len() as u32);
            if apply
                && (primitive.is_some()
                    || constructor
                    || (target.is_none() && !source_types.is_empty())
                    || !data::function(&world, head_ty))
            {
                return Err("source call is not saturated at known target arity".into());
            }
            if !linkage::closed_type(signature) || !linkage::closed_type(ty) {
                return Err("source call requires closed structured types".into());
            }
            // Every value argument was a proven-unique dictionary: the spine
            // denotes one instance and lowers to a reference, not a call.
            if let Some(resolved) = &target
                && source_args.is_empty()
            {
                let [instruction] = block.instructions.as_slice() else {
                    return Err("an absorbed instance spine requires one reference".into());
                };
                verify_reference(instruction, &resolved.reference)?;
                if instruction.origin.source != Source::Expr(expr)
                    || instruction.origin.rule
                        != if resolved.method {
                            Rule::ResolveMethod
                        } else {
                            Rule::ResolveInstance
                        }
                    || instruction.result.id != returned
                    || !instruction.result.ty.alpha_eq(ty)
                    || !instantiated.alpha_eq(ty)
                {
                    return Err("absorbed instance reference differs from source".into());
                }
                return Ok((type_applications, value_applications, value_nodes));
            }
            let mut values = Vec::new();
            let mut argument_instructions = 0;
            for source in &source_args {
                let Ty::Fun { arg, res, .. } = signature else {
                    return Err("source call signature lacks an arrow".into());
                };
                let value = match module.expr(*source) {
                    Expr::App { .. } | Expr::Case { .. } | Expr::Let { .. } | Expr::Lam { .. }
                        if data::supported(&world, arg) =>
                    {
                        let end = block.instructions[argument_instructions..]
                            .iter()
                            .position(|i| i.origin.source == Source::Expr(*source))
                            .map(|offset| argument_instructions + offset)
                            .ok_or("missing computed Int# argument")?;
                        let result = block.instructions[end].result.id;
                        if data::lifted(&world, arg)
                            && !matches!(
                                block.instructions[end].operation,
                                Operation::DelayBlock { .. }
                            )
                        {
                            return Err("computed lifted argument must remain delayed".into());
                        }
                        let mut nested = block.clone();
                        nested.instructions =
                            block.instructions[argument_instructions..=end].to_vec();
                        let (nt, nv, nn) = verify_value(context, &nested, *source, arg, result)?;
                        type_applications += nt;
                        value_applications += nv;
                        value_nodes += nn - 1;
                        argument_instructions = end + 1;
                        result
                    }
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
                        if module
                            .resolve(*source)
                            .is_some_and(|b| context.functions.contains_key(&b))
                            || data::resolve(&world, module_index, *source, arg)?.is_some()
                        {
                            let instruction = block
                                .instructions
                                .get(argument_instructions)
                                .ok_or("missing nullary constructor argument")?;
                            let mut nested = block.clone();
                            nested.instructions = vec![instruction.clone()];
                            verify_value(context, &nested, *source, arg, instruction.result.id)?;
                            argument_instructions += 1;
                            instruction.result.id
                        } else if let Some(parameter) = parameter {
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
                            if !linkage::closed_type(argument_ty) || !arg.alpha_eq(argument_ty) {
                                return Err("source top-level argument type mismatch".into());
                            }
                            let instruction = block
                                .instructions
                                .get(argument_instructions)
                                .ok_or("missing top-level call argument")?;
                            if !matches!(&instruction.operation, Operation::TopReference { module, binder, type_arguments, dictionaries }
                                if *module == argument_module && *binder == argument_binder
                                    && type_arguments.is_empty() && dictionaries.is_empty())
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
            if apply {
                let instruction = block
                    .instructions
                    .last()
                    .ok_or("missing closure application")?;
                let Operation::Apply { callee, arguments } = &instruction.operation else {
                    return Err("missing indirect application".into());
                };
                let mut prefix = block.clone();
                prefix.instructions = block.instructions
                    [argument_instructions..block.instructions.len() - 1]
                    .to_vec();
                // A top-level callee is one instance; its type and dictionary
                // arguments are evidence, so the source spine's head alone does
                // not identify it and the reference is checked directly.
                let (nt, nv, nn) = match &target {
                    Some(resolved) => {
                        let [reference] = prefix.instructions.as_slice() else {
                            return Err("an instance callee requires one reference".into());
                        };
                        verify_reference(reference, &resolved.reference)?;
                        if reference.origin.source != Source::Expr(head)
                            || reference.result.id != *callee
                            || !reference.result.ty.alpha_eq(&instantiated)
                            || reference.origin.rule != expected_instance_rule(resolved)
                        {
                            return Err("instance callee differs from source".into());
                        }
                        (0, 0, 1)
                    }
                    None => verify_value(context, &prefix, head, head_ty, *callee)?,
                };
                if arguments != &values
                    || instruction.origin.source != Source::Expr(expr)
                    || instruction.origin.rule != Rule::Apply
                    || instruction.result.id != returned
                    || !instruction.result.ty.alpha_eq(ty)
                    || !signature.alpha_eq(ty)
                {
                    return Err("closure application differs from source".into());
                }
                return Ok((
                    type_applications + nt,
                    value_applications + nv,
                    value_nodes + nn - 1,
                ));
            }
            if block.instructions.len() != argument_instructions + 1 {
                return Err(
                    "direct call must contain exactly its argument evaluations and call".into(),
                );
            }
            let instruction = &block.instructions[argument_instructions];
            let expected_rule = if constructor {
                if !matches!(instruction.operation, Operation::BoxInt(value) if values == [value]) {
                    return Err("Int constructor field differs from source".into());
                }
                Rule::BoxInt
            } else if let Some(expected) = primitive {
                if !matches!(&instruction.operation, Operation::IntBinary { op, arguments }
                    if *op == expected && arguments == &values)
                {
                    return Err("primitive operation or arguments differ from source".into());
                }
                Rule::IntBinary
            } else if let Some((_, (expected, captures, _))) = local {
                let mut arguments = captures
                    .iter()
                    .map(|b| {
                        params
                            .iter()
                            .find(|(_, binder, _)| binder == b)
                            .map(|(_, _, v)| *v)
                            .ok_or("missing local call capture")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                arguments.extend(values);
                if !matches!(&instruction.operation, Operation::CallLocal { target, arguments: actual } if target == expected && actual == &arguments)
                    || !source_types.is_empty()
                {
                    return Err("local call target or captures differ from source".into());
                }
                Rule::CallLocal
            } else {
                let resolved = target.as_ref().expect("resolved source target");
                let expected = &resolved.reference;
                let Operation::CallTop {
                    module: target,
                    binder,
                    type_arguments,
                    dictionaries,
                    arguments,
                } = &instruction.operation
                else {
                    return Err("source call was not lowered as a direct call".into());
                };
                if (*target, *binder) != (expected.module, expected.binder)
                    || arguments != &values
                    || !same_types(type_arguments, &expected.type_arguments)
                    || !same_dictionaries(dictionaries, &expected.dictionaries)
                {
                    return Err("direct call target or arguments differ from source".into());
                }
                if resolved.method {
                    Rule::ResolveMethod
                } else {
                    Rule::CallTop
                }
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
                    view.ty(*ty).clone()
                })
                .collect();
            type_applications = arguments.len();
            let (target_module, target_binder, head_ty) =
                instantiate::target(module, module_index, modules, head)?;
            let expected = instantiate::apply(head_ty, &arguments)?;
            if !linkage::closed_type(ty) || !expected.alpha_eq(ty) {
                return Err("source type application result mismatch".into());
            }
            let [instruction] = block.instructions.as_slice() else {
                return Err("type application must have exactly one instruction".into());
            };
            let Operation::TopReference {
                module: target,
                binder,
                type_arguments: actual,
                dictionaries,
            } = &instruction.operation
            else {
                return Err("source type application lacks instantiation evidence".into());
            };
            if (*target, *binder) != (target_module, target_binder)
                || !same_types(actual, &arguments)
                || !dictionaries.is_empty()
            {
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
            let (target_module, target_binder) = linkage::imported_top(modules, name)?;
            let target_ty = modules[target_module].binder_ty(target_binder);
            if !linkage::closed_type(ty)
                || !linkage::closed_type(target_ty)
                || !ty.alpha_eq(target_ty)
            {
                return Err("import source lacks matching closed structured types".into());
            }
            let [instruction] = block.instructions.as_slice() else {
                return Err("import leaf must have exactly one instruction".into());
            };
            if !matches!(&instruction.operation, Operation::TopReference { module, binder, type_arguments, dictionaries } if *module == target_module && *binder == target_binder && type_arguments.is_empty() && dictionaries.is_empty())
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
            if !source_type_matches(ty, view.binder_ty(binder), type_scope) {
                return Err("returned reference type differs from source".into());
            }
            if let Some((target, captures, 0)) = context.functions.get(&binder) {
                let arguments = captures
                    .iter()
                    .map(|b| {
                        params
                            .iter()
                            .find(|(_, binder, _)| binder == b)
                            .map(|(_, _, v)| *v)
                            .ok_or("missing nullary join capture")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let [instruction] = block.instructions.as_slice() else {
                    return Err("nullary join requires one call".into());
                };
                if !matches!(&instruction.operation, Operation::CallLocal { target: actual, arguments: args } if actual == target && args == &arguments)
                    || instruction.result.id != returned
                    || !instruction.result.ty.alpha_eq(ty)
                    || instruction.origin.source != Source::Expr(expr)
                    || instruction.origin.rule != Rule::CallLocal
                {
                    return Err("nullary join differs from source".into());
                }
                return Ok((0, 0, 1));
            }
            if let Some((target, captures, _)) = context.functions.get(&binder) {
                let arguments = captures
                    .iter()
                    .map(|b| {
                        params
                            .iter()
                            .find(|(_, binder, _)| binder == b)
                            .map(|(_, _, v)| *v)
                            .ok_or("missing local closure capture")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let [instruction] = block.instructions.as_slice() else {
                    return Err("local closure requires one instruction".into());
                };
                if !matches!(&instruction.operation, Operation::MakeClosure { target: actual, arguments: args } if actual == target && args == &arguments)
                    || instruction.result.id != returned
                    || !instruction.result.ty.alpha_eq(ty)
                    || instruction.origin.source != Source::Expr(expr)
                    || instruction.origin.rule != Rule::MakeClosure
                {
                    return Err("local closure differs from source".into());
                }
                return Ok((0, 0, 1));
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
                if !matches!(&instruction.operation, Operation::TopReference { module, binder: target, type_arguments, dictionaries } if *module == module_index && *target == binder && type_arguments.is_empty() && dictionaries.is_empty())
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
        Expr::Let { bind, body } => {
            if !bind.pairs.is_empty()
                && bind.pairs.iter().all(|p| {
                    matches!(module.expr(p.rhs), Expr::Lam { .. })
                        || (module.binder(p.binder).is_join_point == Some(true)
                            && module.binder(p.binder).arity == Some(0))
                })
            {
                return verify_local_scope(context, block, expr, ty, returned);
            }
            let [pair] = bind.pairs.as_slice() else {
                return Err("source lazy let requires one binding".into());
            };
            // A locally bound dictionary is compile-time evidence: it leaves
            // no instruction, and its whole right-hand side is accounted here.
            let extended;
            if !bind.recursive
                && module.binder(pair.binder).is_join_point != Some(true)
                && let Some(reference) =
                    dict::resolve_dictionary(&world, &context.scope(), pair.rhs, 0)?
            {
                extended = {
                    let mut scope = context.dictionary_scope.clone();
                    scope.insert(pair.binder, reference);
                    scope
                };
                let nested = ValueContext {
                    dictionary_scope: &extended,
                    ..*context
                };
                let (bt, bv, bn) = verify_value(&nested, block, *body, ty, returned)?;
                return Ok((bt, bv, 1 + module.preorder(pair.rhs).count() + bn));
            }
            let binding_ty = view.binder_ty(pair.binder);
            if bind.recursive
                || !data::lifted(&world, binding_ty)
                || module.binder(pair.binder).is_join_point == Some(true)
            {
                return Err("unsupported recursive, unlifted or join-point let".into());
            }
            let split = block
                .instructions
                .iter()
                .position(|i| {
                    i.origin.source == Source::Expr(expr) && i.origin.rule == Rule::LazyBinding
                })
                .ok_or("missing lazy binding marker")?;
            let binding = &block.instructions[split];
            let Operation::Move(rhs) = binding.operation else {
                return Err("lazy let must preserve shared identity".into());
            };
            if !binding.result.ty.alpha_eq(binding_ty) {
                return Err("lazy binding type mismatch".into());
            }
            let mut prefix = block.clone();
            prefix.instructions.truncate(split);
            if !matches!(module.expr(pair.rhs), Expr::Var { .. })
                && !prefix
                    .instructions
                    .last()
                    .is_some_and(|i| matches!(i.operation, Operation::DelayBlock { .. }))
            {
                return Err("computed lazy binding must be delayed".into());
            }
            let (rt, rv, rn) = verify_value(context, &prefix, pair.rhs, binding_ty, rhs)?;
            let mut suffix = block.clone();
            suffix.instructions = block.instructions[split + 1..].to_vec();
            suffix.params.push(binding.result.clone());
            let mut params = params.to_vec();
            params.push((expr, pair.binder, binding.result.id));
            let extended = ValueContext {
                params: &params,
                ..*context
            };
            let (bt, bv, bn) = verify_value(&extended, &suffix, *body, ty, returned)?;
            type_applications = rt + bt;
            value_applications = rv + bv;
            value_nodes = 1 + rn + bn;
        }
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } if boxed::is_int(view.binder_ty(*binder)) => {
            let [alt] = alts.as_slice() else {
                return Err("boxed source case is not exhaustive".into());
            };
            let field = match alt.binders.as_slice() {
                [field]
                    if boxed::alternative(&alt.con)
                        && primitive::is_int(view.binder_ty(*field)) =>
                {
                    Some(*field)
                }
                [] if matches!(alt.con, h2r_core_ir::AltCon::Default) => None,
                _ => return Err("invalid boxed source alternative".into()),
            };
            if !view.ty(*result_ty).alpha_eq(ty) {
                return Err("boxed source case result mismatch".into());
            }
            let split = block
                .instructions
                .iter()
                .position(|i| {
                    i.origin.source == Source::Expr(expr) && i.origin.rule == Rule::UnboxInt
                })
                .ok_or("missing boxed case forcing")?;
            let binding = &block.instructions[split];
            let Operation::UnboxInt(scrutinee) = binding.operation else {
                return Err("boxed case must force its scrutinee".into());
            };
            let mut prefix = block.clone();
            prefix.instructions.truncate(split);
            let (st, sv, sn) =
                verify_value(context, &prefix, *scrut, view.binder_ty(*binder), scrutinee)?;
            let scrutinee_value = block
                .params
                .iter()
                .chain(prefix.instructions.iter().map(|i| &i.result))
                .find(|v| v.id == scrutinee)
                .ok_or("missing boxed scrutinee")?;
            let mut suffix = block.clone();
            suffix.instructions = block.instructions[split + 1..].to_vec();
            if !suffix.params.iter().any(|p| p.id == scrutinee) {
                suffix.params.push(scrutinee_value.clone());
            }
            suffix.params.push(binding.result.clone());
            let mut params = params.to_vec();
            params.push((expr, *binder, scrutinee));
            if let Some(field) = field {
                params.push((expr, field, binding.result.id));
            }
            let extended = ValueContext {
                params: &params,
                ..*context
            };
            let (bt, bv, bn) = verify_value(&extended, &suffix, alt.rhs, ty, returned)?;
            type_applications = st + bt;
            value_applications = sv + bv;
            value_nodes = 1 + sn + bn;
        }
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } => {
            let [alt] = alts.as_slice() else {
                return Err("source strict case must have one alternative".into());
            };
            if !matches!(alt.con, h2r_core_ir::AltCon::Default)
                || !alt.binders.is_empty()
                || !primitive::is_int(view.binder_ty(*binder))
                || !data::supported(&world, ty)
                || !view.ty(*result_ty).alpha_eq(ty)
            {
                return Err("source strict case has unsupported type or alternative".into());
            }
            let split = block
                .instructions
                .iter()
                .position(|i| {
                    i.origin.source == Source::Expr(expr) && i.origin.rule == Rule::StrictPosition
                })
                .ok_or("missing strict case binding")?;
            let binding = &block.instructions[split];
            let Operation::Move(scrutinee) = binding.operation else {
                return Err("strict case binding must preserve the evaluated scrutinee".into());
            };
            if !binding.result.ty.alpha_eq(view.binder_ty(*binder)) {
                return Err("strict case binder type mismatch".into());
            }
            let mut prefix = block.clone();
            prefix.instructions.truncate(split);
            let (st, sv, sn) =
                verify_value(context, &prefix, *scrut, view.binder_ty(*binder), scrutinee)?;
            let mut suffix = block.clone();
            suffix.instructions = block.instructions[split + 1..].to_vec();
            suffix.params.push(binding.result.clone());
            let mut extended_params = params.to_vec();
            extended_params.push((expr, *binder, binding.result.id));
            let extended = ValueContext {
                params: &extended_params,
                ..*context
            };
            let (bt, bv, bn) = verify_value(&extended, &suffix, alt.rhs, ty, returned)?;
            type_applications = st + bt;
            value_applications = sv + bv;
            value_nodes = 1 + sn + bn;
        }
        _ => return Err("unsupported leaf value".into()),
    }

    Ok((type_applications, value_applications, value_nodes))
}

// Check each lexical definition once; calls validate its identity and captures
// without recursively revisiting its body.
fn verify_lambda(
    context: &ValueContext<'_>,
    block: &Block,
    expr: ExprId,
    ty: &Ty,
    returned: ValueId,
) -> Result<(usize, usize, usize), String> {
    use h2r_core_ir::{BinderKind, Expr};
    if !data::function(&context.world(), ty) {
        return Err("unsupported closure signature".into());
    }
    let [i] = block.instructions.as_slice() else {
        return Err("lambda requires one closure".into());
    };
    let Operation::MakeClosure { target, arguments } = &i.operation else {
        return Err("lambda is not a closure".into());
    };
    if i.origin.source != Source::Expr(expr)
        || i.origin.rule != Rule::MakeClosure
        || i.result.id != returned
        || !i.result.ty.alpha_eq(ty)
    {
        return Err("lambda provenance mismatch".into());
    }
    let mut captured = context.params.to_vec();
    captured.sort_by_key(|(_, b, _)| *b);
    if *arguments != captured.iter().map(|(_, _, v)| *v).collect::<Vec<_>>() {
        return Err("lambda capture mismatch".into());
    }
    let target_block = context
        .function
        .blocks
        .iter()
        .find(|b| b.id == *target)
        .ok_or("missing lambda body")?;
    let mut bindings: Vec<_> = captured.iter().map(|(e, b, _)| (*e, *b)).collect();
    let mut rhs = expr;
    let mut result = ty;
    let mut lambdas = 0;
    while let Expr::Lam { binder, body } = context.module.expr(rhs) {
        let Ty::Fun { arg, res, .. } = result else {
            return Err("lambda arrow mismatch".into());
        };
        if context.module.binder(*binder).kind != BinderKind::Id
            || !arg.alpha_eq(context.view.binder_ty(*binder))
        {
            return Err("lambda argument mismatch".into());
        }
        bindings.push((rhs, *binder));
        lambdas += 1;
        rhs = *body;
        result = res;
    }
    if bindings.len() != target_block.params.len() {
        return Err("lambda parameter count mismatch".into());
    }
    let params: Vec<_> = bindings
        .iter()
        .zip(&target_block.params)
        .map(|((e, b), p)| (*e, *b, p.id))
        .collect();
    let nested = ValueContext {
        params: &params,
        ..*context
    };
    let (nt, nv, nn) = verify_tail(&nested, context.function, *target, rhs, result)?;
    Ok((nt, nv, nn + lambdas))
}

fn verify_local_scope(
    context: &ValueContext<'_>,
    block: &Block,
    expr: ExprId,
    ty: &Ty,
    returned: ValueId,
) -> Result<(usize, usize, usize), String> {
    use h2r_core_ir::{BinderKind, Expr};
    let module = context.module;
    let view = context.view;
    let world = context.world();
    let Expr::Let { bind, body } = module.expr(expr) else {
        return Err("local scope source is not a let".into());
    };
    let [instruction] = block.instructions.as_slice() else {
        return Err("local scope requires exactly one instruction".into());
    };
    let Operation::LocalScope {
        definitions,
        target,
        arguments,
    } = &instruction.operation
    else {
        return Err("missing local scope".into());
    };
    if instruction.origin.source != Source::Expr(expr)
        || instruction.origin.rule != Rule::LocalScope
        || instruction.result.id != returned
        || !instruction.result.ty.alpha_eq(ty)
        || definitions.len() != bind.pairs.len()
    {
        return Err("local scope provenance mismatch".into());
    }
    let mut captured = context.params.to_vec();
    captured.sort_by_key(|(_, b, _)| *b);
    if *arguments != captured.iter().map(|(_, _, v)| *v).collect::<Vec<_>>() {
        return Err("local scope captures differ from source".into());
    }
    let capture_types = captured
        .iter()
        .map(|(_, _, v)| {
            block
                .params
                .iter()
                .find(|p| p.id == *v)
                .map(|p| &p.ty)
                .ok_or("missing captured value")
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut functions = context.functions.clone();
    let mut bodies = Vec::new();
    let mut counts = (0, 0, 1);
    for (pair, definition) in bind.pairs.iter().zip(definitions) {
        if pair.binder != definition.binder {
            return Err("local definition identity mismatch".into());
        }
        let mut rhs = pair.rhs;
        let mut result = view.binder_ty(pair.binder);
        let mut lambdas = Vec::new();
        while let Expr::Lam { binder, body } = module.expr(rhs) {
            let Ty::Fun { arg, res, .. } = result else {
                return Err("local lambda lacks value arrow".into());
            };
            if module.binder(*binder).kind != BinderKind::Id
                || !arg.alpha_eq(view.binder_ty(*binder))
                || !data::supported(&world, arg)
            {
                return Err("invalid local lambda parameter".into());
            }
            lambdas.push((rhs, *binder));
            result = res;
            rhs = *body;
        }
        if (lambdas.is_empty()
            && !(module.binder(pair.binder).is_join_point == Some(true)
                && module.binder(pair.binder).arity == Some(0)))
            || !linkage::closed_type(view.binder_ty(pair.binder))
            || !data::supported(&world, result)
            || !result.alpha_eq(&definition.result_ty)
        {
            return Err("local definition signature mismatch".into());
        }
        functions.insert(
            pair.binder,
            (
                definition.target,
                captured.iter().map(|(_, b, _)| *b).collect(),
                lambdas.len(),
            ),
        );
        counts.2 += lambdas.len();
        bodies.push((rhs, lambdas));
    }
    for (definition, (rhs, lambdas)) in definitions.iter().zip(bodies) {
        let target_block = context
            .function
            .blocks
            .iter()
            .find(|b| b.id == definition.target)
            .ok_or("missing local definition block")?;
        let expected_types: Vec<_> = capture_types
            .iter()
            .copied()
            .chain(lambdas.iter().map(|(_, b)| view.binder_ty(*b)))
            .collect();
        if target_block.params.len() != expected_types.len()
            || target_block
                .params
                .iter()
                .zip(expected_types)
                .any(|(p, t)| !p.ty.alpha_eq(t))
        {
            return Err("local definition parameter layout mismatch".into());
        }
        let params: Vec<_> = captured
            .iter()
            .map(|(e, b, _)| (*e, *b))
            .chain(lambdas)
            .zip(&target_block.params)
            .map(|((e, b), p)| (e, b, p.id))
            .collect();
        let nested = ValueContext {
            params: &params,
            functions: if bind.recursive {
                &functions
            } else {
                context.functions
            },
            ..*context
        };
        let (nt, nv, nn) = verify_tail(
            &nested,
            context.function,
            definition.target,
            rhs,
            &definition.result_ty,
        )?;
        counts.0 += nt;
        counts.1 += nv;
        counts.2 += nn;
    }
    let target_block = context
        .function
        .blocks
        .iter()
        .find(|b| b.id == *target)
        .ok_or("missing local scope body")?;
    if target_block.params.len() != captured.len()
        || target_block
            .params
            .iter()
            .zip(&capture_types)
            .any(|(p, t)| !p.ty.alpha_eq(t))
    {
        return Err("local body capture layout mismatch".into());
    }
    let params: Vec<_> = captured
        .iter()
        .zip(&target_block.params)
        .map(|((e, b, _), p)| (*e, *b, p.id))
        .collect();
    let nested = ValueContext {
        params: &params,
        functions: &functions,
        ..*context
    };
    let (nt, nv, nn) = verify_tail(&nested, context.function, *target, *body, ty)?;
    Ok((counts.0 + nt, counts.1 + nv, counts.2 + nn))
}

/// Check one instruction is exactly the expected instance reference. Type and
/// dictionary arguments are compile-time evidence: they must match the
/// independently resolved instance, not merely the target binding.
fn verify_reference(instruction: &Instruction, expected: &DictionaryRef) -> Result<(), String> {
    let Operation::TopReference {
        module,
        binder,
        type_arguments,
        dictionaries,
    } = &instruction.operation
    else {
        return Err("instance reference was not lowered as a shared reference".into());
    };
    if (*module, *binder) != (expected.module, expected.binder)
        || !same_types(type_arguments, &expected.type_arguments)
        || !same_dictionaries(dictionaries, &expected.dictionaries)
    {
        return Err("instance reference target or evidence differs from source".into());
    }
    Ok(())
}

/// Which rule an instance reference in callee position must carry.
fn expected_instance_rule(target: &dict::CallTarget) -> Rule {
    if target.method {
        Rule::ResolveMethod
    } else if target.reference.type_arguments.is_empty() && target.reference.dictionaries.is_empty()
    {
        Rule::TopReference
    } else {
        Rule::ResolveInstance
    }
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

fn verify_constructor(
    context: &ValueContext<'_>,
    block: &Block,
    expr: ExprId,
    ty: &Ty,
    returned: ValueId,
) -> Result<Option<(usize, usize, usize)>, String> {
    use h2r_core_ir::Expr;
    let module = context.module;
    let view = context.view;
    let world = context.world();
    let mut head = expr;
    let mut args = Vec::new();
    let mut types = Vec::new();
    while let Expr::App { fun, arg } = module.expr(head) {
        match module.expr(*arg) {
            Expr::Type { ty, .. } => types.push(view.ty(*ty).clone()),
            _ if types.is_empty() => args.push(*arg),
            _ => return Err("interleaved source constructor spine".into()),
        }
        head = *fun;
    }
    let Some(expected) = data::resolve(&world, context.module_index, head, ty)? else {
        return Ok(None);
    };
    args.reverse();
    types.reverse();
    let Ty::Con { args: instance, .. } = ty else {
        unreachable!()
    };
    if types != *instance || args.len() != expected.fields.len() {
        return Err("source constructor saturation/type arguments mismatch".into());
    }
    let instruction = block
        .instructions
        .last()
        .ok_or("missing constructor instruction")?;
    let Operation::Construct {
        constructor,
        arguments,
    } = &instruction.operation
    else {
        return Err("source constructor was not constructed".into());
    };
    if constructor != &expected
        || instruction.origin.source != Source::Expr(expr)
        || instruction.origin.rule != Rule::Construct
        || instruction.result.id != returned
        || !instruction.result.ty.alpha_eq(ty)
        || arguments.len() != args.len()
    {
        return Err("constructor identity, layout, result or origin mismatch".into());
    }
    let mut nt = types.len();
    let mut nv = args.len();
    let mut nn = 1;
    let mut offset = 0;
    for ((source, field), value) in args.iter().zip(&expected.fields).zip(arguments) {
        let parameter = module
            .resolve(*source)
            .and_then(|b| context.params.iter().find(|(_, binder, _)| *binder == b));
        let end = if parameter.is_some() {
            offset
        } else {
            block.instructions[offset..block.instructions.len() - 1]
                .iter()
                .position(|i| i.result.id == *value)
                .map(|i| offset + i + 1)
                .ok_or("missing constructor field evaluation")?
        };
        let mut argument = block.clone();
        argument.instructions = block.instructions[offset..end].to_vec();
        if data::lifted(&world, field)
            && !matches!(module.expr(*source), Expr::Var { .. })
            && !argument
                .instructions
                .last()
                .is_some_and(|i| matches!(i.operation, Operation::DelayBlock { .. }))
        {
            return Err("constructor field computation must remain delayed".into());
        }
        let (at, av, an) = verify_value(context, &argument, *source, field, *value)?;
        nt += at;
        nv += av;
        nn += an - 1;
        offset = end;
    }
    if offset + 1 != block.instructions.len() {
        return Err("extra constructor instructions".into());
    }
    Ok(Some((nt, nv, nn)))
}

fn verify_data_case(
    context: &ValueContext<'_>,
    block: &Block,
    expr: ExprId,
    ty: &Ty,
    returned: ValueId,
) -> Result<(usize, usize, usize), String> {
    let module = context.module;
    let view = context.view;
    let world = context.world();
    let h2r_core_ir::Expr::Case {
        scrut,
        binder,
        ty: result,
        alts,
        ..
    } = module.expr(expr)
    else {
        unreachable!()
    };
    let instruction = block.instructions.last().ok_or("missing algebraic match")?;
    let Operation::MatchData {
        scrutinee,
        arguments,
        arms,
    } = &instruction.operation
    else {
        return Err("case must force and match constructor".into());
    };
    if instruction.origin.rule != Rule::MatchData
        || instruction.origin.source != Source::Expr(expr)
        || instruction.result.id != returned
        || !instruction.result.ty.alpha_eq(ty)
        || !view.ty(*result).alpha_eq(ty)
        || arms.len() != alts.len()
        || arms.is_empty()
    {
        return Err("algebraic case result/origin/arity mismatch".into());
    }
    let mut prefix = block.clone();
    prefix.instructions.pop();
    let (mut nt, mut nv, mut nn) = verify_value(
        context,
        &prefix,
        *scrut,
        view.binder_ty(*binder),
        *scrutinee,
    )?;
    nn += 1;
    let family = data::family(&world, view.binder_ty(*binder))?;
    let mut captured = context.params.to_vec();
    captured.sort_by_key(|(_, b, _)| *b);
    if *arguments != captured.iter().map(|(_, _, v)| *v).collect::<Vec<_>>() {
        return Err("case captures differ from lexical scope".into());
    }
    let mut seen = BTreeSet::new();
    let mut default = false;
    for (alt, arm) in alts.iter().zip(arms) {
        let expected = match &alt.con {
            h2r_core_ir::AltCon::DataAlt { name, tag, .. } => {
                let c = family
                    .iter()
                    .find(|c| c.name == *name && c.tag == *tag)
                    .ok_or("case constructor outside source family")?;
                if !seen.insert(*tag) {
                    return Err("duplicate source constructor alternative".into());
                }
                Some(c)
            }
            h2r_core_ir::AltCon::Default if !default => {
                default = true;
                None
            }
            _ => return Err("invalid source algebraic pattern".into()),
        };
        if arm.constructor.as_ref() != expected {
            return Err("case pattern differs from source".into());
        }
        let fields = expected.map_or(&[][..], |c| c.fields.as_slice());
        if fields.len() != alt.binders.len()
            || fields
                .iter()
                .zip(&alt.binders)
                .any(|(t, b)| !t.alpha_eq(view.binder_ty(*b)))
        {
            return Err("source pattern field layout mismatch".into());
        }
        let target = context
            .function
            .blocks
            .iter()
            .find(|b| b.id == arm.target)
            .ok_or("missing case arm")?;
        if target.params.len() != captured.len() + 1 + fields.len() {
            return Err("case arm parameter count mismatch".into());
        }
        let mut params: Vec<_> = captured
            .iter()
            .zip(&target.params)
            .map(|((e, b, _), p)| (*e, *b, p.id))
            .collect();
        for (b, p) in std::iter::once(binder)
            .chain(&alt.binders)
            .zip(&target.params[captured.len()..])
        {
            if !p.ty.alpha_eq(view.binder_ty(*b)) {
                return Err("case arm binder type mismatch".into());
            }
            params.push((expr, *b, p.id));
        }
        let branch = ValueContext {
            params: &params,
            ..*context
        };
        let (at, av, an) = verify_tail(&branch, context.function, arm.target, alt.rhs, ty)?;
        nt += at;
        nv += av;
        nn += an;
    }
    if !default && seen.len() != family.len() {
        return Err("non-exhaustive source algebraic case".into());
    }
    Ok((nt, nv, nn))
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
    // Region returns belong to their call site, not necessarily the enclosing
    // function's result type. Ordinary control-flow successors inherit it.
    let mut return_types: BTreeMap<BlockId, &Ty> = BTreeMap::new();
    let mut pending_types = vec![(function.entry, &function.result_ty)];
    for block in &function.blocks {
        for instruction in &block.instructions {
            if let Operation::MakeClosure { target, arguments } = &instruction.operation {
                let target_block = blocks.get(target).ok_or("missing closure target")?;
                let count = target_block
                    .params
                    .len()
                    .checked_sub(arguments.len())
                    .filter(|n| *n > 0)
                    .ok_or("closure requires value parameters")?;
                let mut result = &instruction.result.ty;
                for _ in 0..count {
                    let Ty::Fun { res, .. } = result else {
                        return Err("closure arity exceeds function type".into());
                    };
                    result = res;
                }
                pending_types.push((*target, result));
            }
            if let Operation::LocalScope { definitions, .. } = &instruction.operation {
                pending_types.extend(definitions.iter().map(|d| (d.target, &d.result_ty)));
            }
            if let Operation::MatchData { arms, .. } = &instruction.operation {
                pending_types.extend(arms.iter().map(|a| (a.target, &instruction.result.ty)));
            }
            if let Operation::EvaluateBlock { target, .. }
            | Operation::DelayBlock { target, .. }
            | Operation::CallLocal { target, .. }
            | Operation::LocalScope { target, .. } = instruction.operation
            {
                pending_types.push((target, &instruction.result.ty));
            }
        }
    }
    while let Some((id, ty)) = pending_types.pop() {
        if let Some(previous) = return_types.insert(id, ty) {
            if !previous.alpha_eq(ty) {
                return Err("conflicting region return types".into());
            }
            continue;
        }
        match &blocks
            .get(&id)
            .ok_or("missing region block")?
            .terminator
            .exit
        {
            Exit::Return(_) => {}
            Exit::Jump { target, .. } => pending_types.push((*target, ty)),
            Exit::IntSwitch { arms, default, .. } => {
                pending_types.push((*default, ty));
                pending_types.extend(arms.iter().map(|(_, target)| (*target, ty)));
            }
        }
    }
    for block in &function.blocks {
        let mut available: BTreeMap<_, _> = block.params.iter().map(|v| (v.id, &v.ty)).collect();
        for instruction in &block.instructions {
            if instruction.origin.module != function.module {
                return Err("instruction origin belongs to another module".into());
            }
            match instruction.operation {
                Operation::MakeClosure {
                    target,
                    ref arguments,
                } => {
                    let target_block = blocks.get(&target).ok_or("missing closure body")?;
                    if !linkage::closed_type(&instruction.result.ty) {
                        return Err("open closure signature".into());
                    }
                    for (n, arg) in arguments.iter().enumerate() {
                        if !available.get(arg).is_some_and(|t| {
                            target_block.params.get(n).is_some_and(|p| p.ty.alpha_eq(t))
                        }) {
                            return Err("closure capture type mismatch".into());
                        }
                    }
                    let mut signature = &instruction.result.ty;
                    for param in &target_block.params[arguments.len()..] {
                        let Ty::Fun { arg, res, .. } = signature else {
                            return Err("closure signature lacks arrow".into());
                        };
                        if !arg.alpha_eq(&param.ty) {
                            return Err("closure parameter type mismatch".into());
                        }
                        signature = res;
                    }
                }
                Operation::Apply {
                    callee,
                    ref arguments,
                } => {
                    let mut signature = *available.get(&callee).ok_or("unavailable closure")?;
                    if arguments.is_empty() {
                        return Err("empty application".into());
                    }
                    for value in arguments {
                        let Ty::Fun { arg, res, .. } = signature else {
                            return Err("application lacks arrow".into());
                        };
                        if !available.get(value).is_some_and(|t| t.alpha_eq(arg)) {
                            return Err("application argument type mismatch".into());
                        }
                        signature = res;
                    }
                    if !signature.alpha_eq(&instruction.result.ty) {
                        return Err("application result type mismatch".into());
                    }
                }
                Operation::Construct {
                    ref constructor,
                    ref arguments,
                } => {
                    if !constructor.result.alpha_eq(&instruction.result.ty)
                        || constructor.fields.len() != arguments.len()
                        || constructor.strict.len() != arguments.len()
                        || constructor.tag == 0
                        || arguments
                            .iter()
                            .zip(&constructor.fields)
                            .any(|(v, t)| !available.get(v).is_some_and(|a| a.alpha_eq(t)))
                    {
                        return Err("constructor field/result type mismatch".into());
                    }
                }
                Operation::MatchData {
                    scrutinee,
                    ref arguments,
                    ref arms,
                } => {
                    let scrut_ty = available.get(&scrutinee).ok_or("missing case scrutinee")?;
                    let mut patterns = BTreeSet::new();
                    let mut default = false;
                    if arms.is_empty() {
                        return Err("empty algebraic match".into());
                    }
                    for arm in arms {
                        let target = blocks.get(&arm.target).ok_or("missing constructor arm")?;
                        let fields = if let Some(c) = &arm.constructor {
                            if !c.result.alpha_eq(scrut_ty) || c.tag == 0 || !patterns.insert(c.tag)
                            {
                                return Err("invalid constructor match layout".into());
                            }
                            &c.fields[..]
                        } else {
                            if default {
                                return Err("duplicate DEFAULT".into());
                            }
                            default = true;
                            &[]
                        };
                        let expected: Vec<_> = arguments
                            .iter()
                            .map(|v| available.get(v).copied().ok_or("missing case capture"))
                            .collect::<Result<_, _>>()?;
                        let expected: Vec<_> = expected
                            .into_iter()
                            .chain(std::iter::once(*scrut_ty))
                            .chain(fields)
                            .collect();
                        if target.params.len() != expected.len()
                            || target
                                .params
                                .iter()
                                .zip(expected)
                                .any(|(p, t)| !p.ty.alpha_eq(t))
                        {
                            return Err("constructor arm edge type mismatch".into());
                        }
                    }
                }
                Operation::DelayBlock {
                    target,
                    ref arguments,
                } => {
                    if primitive::is_int(&instruction.result.ty)
                        || !matches!(instruction.result.ty, Ty::Con { .. } | Ty::Fun { .. })
                        || !linkage::closed_type(&instruction.result.ty)
                    {
                        return Err("delayed region requires a boxed Int result".into());
                    }
                    verify_edge(&blocks, &available, target, arguments)?;
                }
                Operation::BoxInt(value) | Operation::UnboxInt(value) => {
                    let input = available
                        .get(&value)
                        .ok_or("unavailable constructor operand")?;
                    let valid = if matches!(instruction.operation, Operation::BoxInt(_)) {
                        primitive::is_int(input) && boxed::is_int(&instruction.result.ty)
                    } else {
                        boxed::is_int(input) && primitive::is_int(&instruction.result.ty)
                    };
                    if !valid {
                        return Err("boxed Int carrier mismatch".into());
                    }
                }
                Operation::EvaluateBlock {
                    target,
                    ref arguments,
                }
                | Operation::CallLocal {
                    target,
                    ref arguments,
                }
                | Operation::LocalScope {
                    target,
                    ref arguments,
                    ..
                } => {
                    if !matches!(instruction.result.ty, Ty::Con { .. } | Ty::Fun { .. })
                        || !linkage::closed_type(&instruction.result.ty)
                    {
                        return Err("region evaluation requires an Int# or Int result".into());
                    }
                    verify_edge(&blocks, &available, target, arguments)?;
                }
                Operation::Literal(_) | Operation::TopReference { .. } => {}
                Operation::Move(value) | Operation::Force(value) => {
                    if !available.contains_key(&value) {
                        return Err(format!("unavailable operand {value:?}"));
                    }
                }
                Operation::IntBinary { ref arguments, .. } => {
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
                if !ty.alpha_eq(return_types.get(&block.id).ok_or("unreachable block")?) {
                    return Err("return type mismatch".into());
                }
            }
            Exit::Jump { target, args } => verify_edge(&blocks, &available, *target, args)?,
            Exit::IntSwitch {
                scrutinee,
                arms,
                default,
                args,
            } => {
                if !available
                    .get(scrutinee)
                    .is_some_and(|ty| primitive::is_int(ty))
                {
                    return Err("switch scrutinee must be an available Int#".into());
                }
                let mut patterns = BTreeSet::new();
                for (pattern, target) in arms {
                    if !patterns.insert(*pattern) {
                        return Err("duplicate switch pattern".into());
                    }
                    verify_edge(&blocks, &available, *target, args)?;
                }
                verify_edge(&blocks, &available, *default, args)?;
            }
        }
    }
    let mut visited = BTreeSet::new();
    let mut pending = vec![function.entry];
    while let Some(id) = pending.pop() {
        if visited.insert(id) {
            for instruction in &blocks[&id].instructions {
                if let Operation::LocalScope { definitions, .. } = &instruction.operation {
                    pending.extend(definitions.iter().map(|d| d.target));
                }
                if let Operation::MatchData { arms, .. } = &instruction.operation {
                    pending.extend(arms.iter().map(|a| a.target));
                }
                if let Operation::EvaluateBlock { target, .. }
                | Operation::DelayBlock { target, .. }
                | Operation::CallLocal { target, .. }
                | Operation::LocalScope { target, .. }
                | Operation::MakeClosure { target, .. } = instruction.operation
                {
                    pending.push(target);
                }
            }
            match &blocks[&id].terminator.exit {
                Exit::Return(_) => {}
                Exit::Jump { target, .. } => pending.push(*target),
                Exit::IntSwitch { arms, default, .. } => {
                    pending.push(*default);
                    pending.extend(arms.iter().map(|(_, target)| *target));
                }
            }
        }
    }
    if visited.len() != blocks.len() {
        return Err("unreachable block".into());
    }
    Ok(())
}

fn verify_edge(
    blocks: &BTreeMap<BlockId, &Block>,
    available: &BTreeMap<ValueId, &Ty>,
    target: BlockId,
    args: &[ValueId],
) -> Result<(), String> {
    let target = blocks
        .get(&target)
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
            type_arguments: vec![],
            dictionaries: vec![],
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
    fn region_return_type_is_checked_independently_of_function_result() {
        let mut f = fixture();
        let Ty::Fun { arg: int, .. } = primitive::signature() else {
            panic!()
        };
        let origin = f.blocks[0].terminator.origin.clone();
        f.blocks[0].params.push(Value {
            id: ValueId(1),
            ty: (*int).clone(),
        });
        f.blocks[0].instructions.push(Instruction {
            result: Value {
                id: ValueId(2),
                ty: (*int).clone(),
            },
            operation: Operation::EvaluateBlock {
                target: BlockId(1),
                arguments: vec![ValueId(1)],
            },
            origin: Origin {
                rule: Rule::EvaluateBlock,
                ..origin
            },
        });
        f.blocks.push(Block {
            id: BlockId(1),
            params: vec![Value {
                id: ValueId(3),
                ty: *int,
            }],
            instructions: vec![],
            terminator: Terminator {
                exit: Exit::Return(ValueId(3)),
                origin: f.blocks[0].terminator.origin.clone(),
            },
        });
        verify(&f).unwrap();
        let mut bad = f.clone();
        bad.blocks[1].params[0].ty = f.result_ty.clone();
        assert!(verify(&bad).is_err());
        let mut bad = f.clone();
        bad.blocks[0].terminator.exit = Exit::Jump {
            target: BlockId(1),
            args: vec![ValueId(1)],
        };
        assert_eq!(verify(&bad).unwrap_err(), "conflicting region return types");
        f.blocks[0].instructions[0].result.ty = f.result_ty.clone();
        assert!(verify(&f).is_err());
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
