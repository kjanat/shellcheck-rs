//! Conservative Core lowering: direct calls, scalar control flow, lazy regions
//! and algebraic construction/matching. Unsupported constructs fail explicitly.
//! This is not a whole-program driver or an independent semantic verifier.

use std::collections::BTreeMap;

use h2r_core_ir::{BindSite, BinderKind, Expr, Module};

use super::subst::Substitution;
use super::view::TypeView;
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
    /// Type lambdas this instance consumed, paired with the closed type each
    /// was specialized at. Source order; disjoint from `type_parameters`.
    pub type_instantiations: Vec<(ExprId, BinderId, Ty)>,
    /// Dictionary lambdas this instance consumed, paired with the dictionary
    /// each was specialized on. They bind no runtime parameter.
    pub dictionary_parameters: Vec<(ExprId, BinderId, DictionaryRef)>,
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
    lower_leaf_impl(module, module_index, owner, id, None, &[], &[])
}

/// Lower with access to authoritative in-world definitions for imports.
pub fn lower_leaf_in_world(
    modules: &[Module],
    module_index: usize,
    owner: BinderId,
    id: FnId,
) -> Result<LoweredLeaf, LowerError> {
    lower_leaf_specialized(modules, module_index, owner, id, &[], &[])
}

/// Lower one instance of an owner: its leading quantifiers bound to the given
/// closed types and its leading dictionary lambdas to the given dictionaries.
/// Empty argument lists are the owner's own signature.
pub fn lower_leaf_specialized(
    modules: &[Module],
    module_index: usize,
    owner: BinderId,
    id: FnId,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
) -> Result<LoweredLeaf, LowerError> {
    let module = modules.get(module_index).ok_or_else(|| LowerError {
        module: module_index,
        owner,
        source: None,
        reason: "module index is outside the loaded world".into(),
    })?;
    lower_leaf_impl(
        module,
        module_index,
        owner,
        id,
        Some(modules),
        type_arguments,
        dictionaries,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_leaf_impl(
    module: &Module,
    module_index: usize,
    owner: BinderId,
    id: FnId,
    modules: Option<&[Module]>,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
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
    // Bind the source type lambdas first, so the body's types can be read
    // through one substituted view of the module's immutable type table.
    let (subst, signature) = bind_type_arguments(module, pair.rhs, owner, type_arguments)
        .map_err(|reason| fail(Some(pair.rhs), &reason))?;
    let view = TypeView::specialized(module, &subst);
    let mut current = pair.rhs;
    let mut ty = &signature;
    let mut params = Vec::new();
    let mut parameters = Vec::new();
    let mut type_parameters = Vec::new();
    let mut type_instantiations = Vec::new();
    let mut type_scope: Vec<(TyVarId, TyVarId)> = Vec::new();
    let mut erased_ticks = Vec::new();
    let mut locals = BTreeMap::new();
    let mut instantiated = 0;
    let mut dictionary_parameters = Vec::new();
    let mut dictionary_scope: BTreeMap<BinderId, DictionaryRef> = BTreeMap::new();
    let world = World {
        module,
        index: module_index,
        modules,
    };
    loop {
        match module.expr(current) {
            Expr::Tick(body) => {
                erased_ticks.push(current);
                current = *body;
            }
            Expr::Lam { binder, body } => {
                let source_binder = module.binder(*binder);
                if source_binder.kind == BinderKind::Tyvar {
                    if instantiated < type_arguments.len() {
                        type_instantiations.push((
                            current,
                            *binder,
                            type_arguments[instantiated].clone(),
                        ));
                        instantiated += 1;
                        current = *body;
                        continue;
                    }
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
                if !same_scoped_type(arg, view.binder_ty(*binder), &type_scope) {
                    return Err(fail(Some(current), "lambda parameter type mismatch"));
                }
                // A dictionary the instance was specialized on binds no runtime
                // parameter: its identity is already in the instance key.
                if dictionary_parameters.len() < dictionaries.len() {
                    let reference = &dictionaries[dictionary_parameters.len()];
                    let expected = dict::reference_type(&world, reference)
                        .map_err(|reason| fail(Some(current), &reason))?;
                    if !arg.alpha_eq(&expected) {
                        return Err(fail(
                            Some(current),
                            "dictionary parameter type differs from the instance's dictionary",
                        ));
                    }
                    dictionary_parameters.push((current, *binder, reference.clone()));
                    dictionary_scope.insert(*binder, reference.clone());
                    ty = res;
                    current = *body;
                    continue;
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
    if instantiated != type_arguments.len() || dictionary_parameters.len() != dictionaries.len() {
        return Err(fail(
            Some(current),
            "instance supplies more arguments than the owner's leading lambdas bind",
        ));
    }
    let next_value = std::cell::Cell::new(params.len() as u32);
    let context = BodyContext {
        module,
        view: &view,
        module_index,
        owner,
        modules,
        params: &params,
        next_value: &next_value,
        type_scope: &type_scope,
        subst: &subst,
        dictionary_scope: &dictionary_scope,
        functions: &BTreeMap::new(),
    };
    let mut blocks = Vec::new();
    let entry = lower_tail(&context, current, ty, &locals, &mut blocks)?;
    let function = Function {
        id,
        module: module_index,
        owner,
        result_ty: ty.clone(),
        type_params: type_scope
            .iter()
            .map(|(signature, _)| signature.clone())
            .collect(),
        type_arguments: type_arguments.to_vec(),
        dictionaries: dictionaries.to_vec(),
        entry,
        blocks,
    };
    let lowered = LoweredLeaf {
        function,
        parameters,
        type_parameters,
        type_instantiations,
        dictionary_parameters,
        erased_ticks,
    };
    let verified = match modules {
        Some(modules) => verify::verify_leaf_specialized(
            modules,
            module_index,
            owner,
            id,
            &lowered,
            type_arguments,
            dictionaries,
        ),
        None => verify::verify_leaf(module, module_index, owner, id, &lowered),
    };
    verified.map_err(|reason| fail(Some(current), &reason))?;
    Ok(lowered)
}

/// Pair the instance's closed type arguments with the owner's leading type
/// lambdas and the matching quantifiers of its signature. Substitution is
/// capture-safe, so a rebinding quantifier inside the body is left alone.
pub(super) fn bind_type_arguments(
    module: &Module,
    rhs: ExprId,
    owner: BinderId,
    type_arguments: &[Ty],
) -> Result<(Substitution, Ty), String> {
    let mut subst = Substitution::default();
    let mut signature = module.binder_ty(owner).clone();
    if type_arguments.is_empty() {
        return Ok((subst, signature));
    }
    let mut current = rhs;
    for argument in type_arguments {
        if !linkage::closed_type(argument) {
            return Err("specialization requires closed structured type arguments".into());
        }
        while let Expr::Tick(body) = module.expr(current) {
            current = *body;
        }
        let Expr::Lam { binder, body } = module.expr(current) else {
            return Err("instance has more type arguments than the owner binds".into());
        };
        let source = module.binder(*binder);
        if source.kind != BinderKind::Tyvar {
            return Err("instance type argument meets a value lambda".into());
        }
        let Ty::ForAll {
            binder: quantifier,
            body: result,
        } = signature
        else {
            return Err("specialized type lambda needs a forall type".into());
        };
        let mut instantiated = *result;
        super::subst::substitute_capture_safe(&mut instantiated, &quantifier.unique, argument);
        signature = instantiated;
        subst.bind(
            TyVarId {
                name: source.name.clone(),
                occ: source.occ.clone(),
                unique: source.unique.clone(),
            },
            argument.clone(),
        )?;
        current = *body;
    }
    if !linkage::closed_type(&signature) {
        return Err("specialized signature is not closed".into());
    }
    Ok((subst, signature))
}

struct BodyContext<'a> {
    module: &'a Module,
    view: &'a TypeView<'a>,
    module_index: usize,
    owner: BinderId,
    modules: Option<&'a [Module]>,
    params: &'a [Value],
    next_value: &'a std::cell::Cell<u32>,
    type_scope: &'a [(TyVarId, TyVarId)],
    /// This instance's type arguments, for reading source types in scope.
    subst: &'a Substitution,
    /// Dictionary lambdas the instance key absorbed. These are compile-time
    /// identities that scope over the whole body, not runtime values.
    dictionary_scope: &'a BTreeMap<BinderId, DictionaryRef>,
    functions: &'a BTreeMap<BinderId, (BlockId, Vec<BinderId>, usize)>,
}

impl<'a> BodyContext<'a> {
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

fn reference_operation(reference: &DictionaryRef) -> Operation {
    Operation::TopReference {
        module: reference.module,
        binder: reference.binder,
        type_arguments: reference.type_arguments.clone(),
        dictionaries: reference.dictionaries.clone(),
    }
}

/// Which source rule produced an instance reference: a resolved class method, a
/// spine absorbed into an instance key, or a plain shared top-level value.
fn instance_rule(target: &dict::CallTarget) -> Rule {
    if target.method {
        Rule::ResolveMethod
    } else if target.reference.type_arguments.is_empty() && target.reference.dictionaries.is_empty()
    {
        Rule::TopReference
    } else {
        Rule::ResolveInstance
    }
}

fn fresh_value(context: &BodyContext<'_>) -> ValueId {
    let id = context.next_value.get();
    context.next_value.set(id + 1);
    ValueId(id)
}

/// Tail cases become explicit CFG successors. Non-tail cases call scalar
/// regions and resume without cloning their continuation into every arm.
fn lower_tail(
    context: &BodyContext<'_>,
    source: ExprId,
    ty: &Ty,
    locals: &BTreeMap<BinderId, ValueId>,
    blocks: &mut Vec<Block>,
) -> Result<BlockId, LowerError> {
    let id = BlockId(blocks.len() as u32);
    blocks.push(Block {
        id,
        params: Vec::new(),
        instructions: Vec::new(),
        terminator: Terminator {
            exit: Exit::Return(ValueId(u32::MAX)),
            origin: Origin {
                module: context.module_index,
                source: Source::Expr(source),
                rule: Rule::Return,
            },
        },
    });
    lower_tail_at(context, source, ty, locals, blocks, id)
}

fn lower_tail_at(
    context: &BodyContext<'_>,
    source: ExprId,
    ty: &Ty,
    locals: &BTreeMap<BinderId, ValueId>,
    blocks: &mut Vec<Block>,
    id: BlockId,
) -> Result<BlockId, LowerError> {
    let module = context.module;
    let view = context.view;
    let world = context.world();
    let fail = |reason: String| LowerError {
        module: context.module_index,
        owner: context.owner,
        source: Some(source),
        reason,
    };
    let origin = |rule| Origin {
        module: context.module_index,
        source: Source::Expr(source),
        rule,
    };
    let mut instructions = Vec::new();
    let mut locals = locals.clone();
    blocks[id.0 as usize] = Block {
        id,
        params: context.params.to_vec(),
        instructions: Vec::new(),
        terminator: Terminator {
            exit: Exit::Return(ValueId(u32::MAX)),
            origin: origin(Rule::Return),
        },
    };
    if let Expr::Case {
        scrut,
        binder,
        ty: result_ty,
        alts,
        ..
    } = module.expr(source)
        && !data::lifted(&world, view.binder_ty(*binder))
    {
        if !primitive::is_int(view.binder_ty(*binder))
            || !data::supported(&world, ty)
            || !view.ty(*result_ty).alpha_eq(ty)
            || alts.iter().any(|a| !a.binders.is_empty())
        {
            return Err(fail(
                "switch requires Int# scrutinee, Int#/Int result and no alternative binders".into(),
            ));
        }
        let mut patterns = std::collections::BTreeSet::new();
        let mut defaults = 0;
        let mut alternatives = Vec::new();
        for alt in alts {
            let pattern = match &alt.con {
                h2r_core_ir::AltCon::Default => {
                    defaults += 1;
                    None
                }
                h2r_core_ir::AltCon::LitAlt { lit } => {
                    let value = primitive::int_literal(lit).map_err(&fail)?;
                    if !patterns.insert(value) {
                        return Err(fail("duplicate Int# case alternative".into()));
                    }
                    Some(value)
                }
                _ => return Err(fail("constructor alternatives are not scalar".into())),
            };
            alternatives.push((pattern, alt.rhs));
        }
        if defaults != 1 {
            return Err(fail(
                "Int# switch requires exactly one DEFAULT alternative".into(),
            ));
        }
        let scrutinee = lower_value(
            context,
            *scrut,
            view.binder_ty(*binder),
            &mut locals,
            &mut instructions,
            blocks,
        )?;
        let mut args: Vec<_> = context.params.iter().map(|p| p.id).collect();
        args.push(scrutinee);
        blocks[id.0 as usize] = Block {
            id,
            params: context.params.to_vec(),
            instructions,
            terminator: Terminator {
                exit: Exit::Return(scrutinee),
                origin: origin(Rule::IntSwitch),
            },
        };
        let mut arms = Vec::new();
        let mut default = None;
        for (pattern, rhs) in alternatives {
            let mut params: Vec<_> = context
                .params
                .iter()
                .map(|p| Value {
                    id: fresh_value(context),
                    ty: p.ty.clone(),
                })
                .collect();
            let mut branch_locals = BTreeMap::new();
            for (binder, value) in &locals {
                let position = context
                    .params
                    .iter()
                    .position(|p| p.id == *value)
                    .ok_or_else(|| fail("case environment contains an unbound value".into()))?;
                branch_locals.insert(*binder, params[position].id);
            }
            let case_value = Value {
                id: fresh_value(context),
                ty: view.binder_ty(*binder).clone(),
            };
            branch_locals.insert(*binder, case_value.id);
            params.push(case_value);
            let branch_context = BodyContext {
                params: &params,
                ..*context
            };
            let target = lower_tail(&branch_context, rhs, ty, &branch_locals, blocks)?;
            if let Some(pattern) = pattern {
                arms.push((pattern, target));
            } else {
                default = Some(target);
            }
        }
        blocks[id.0 as usize].terminator.exit = Exit::IntSwitch {
            scrutinee,
            arms,
            default: default.expect("validated DEFAULT"),
            args,
        };
    } else {
        let value = lower_value(context, source, ty, &mut locals, &mut instructions, blocks)?;
        blocks[id.0 as usize] = Block {
            id,
            params: context.params.to_vec(),
            instructions,
            terminator: Terminator {
                exit: Exit::Return(value),
                origin: origin(Rule::Return),
            },
        };
    }
    Ok(id)
}

fn lower_value(
    context: &BodyContext<'_>,
    current: ExprId,
    ty: &Ty,
    locals: &mut BTreeMap<BinderId, ValueId>,
    instructions: &mut Vec<Instruction>,
    blocks: &mut Vec<Block>,
) -> Result<ValueId, LowerError> {
    let BodyContext {
        module,
        view,
        module_index,
        owner,
        modules,
        params,
        type_scope,
        ..
    } = *context;
    let world = context.world();
    let fail = |source, reason: &str| LowerError {
        module: module_index,
        owner,
        source,
        reason: reason.into(),
    };
    let origin = |rule| Origin {
        module: module_index,
        source: Source::Expr(current),
        rule,
    };
    // Constructor spines include nullary workers and type-only applications.
    let mut head = current;
    let mut sources = Vec::new();
    let mut types = Vec::new();
    while let Expr::App { fun, arg } = module.expr(head) {
        if let Expr::Type { ty, .. } = module.expr(*arg) {
            types.push(view.ty(*ty).clone());
        } else {
            if !types.is_empty() {
                return Err(fail(
                    Some(current),
                    "type arguments must precede value arguments",
                ));
            }
            sources.push(*arg);
        }
        head = *fun;
    }
    if let Some(constructor) =
        data::resolve(&world, module_index, head, ty).map_err(|e| fail(Some(current), &e))?
    {
        sources.reverse();
        types.reverse();
        let Ty::Con { args, .. } = ty else {
            unreachable!()
        };
        if types != *args || sources.len() != constructor.fields.len() {
            return Err(fail(
                Some(current),
                "constructor type arguments or saturation mismatch",
            ));
        }
        let mut arguments = Vec::new();
        for (source, field) in sources.into_iter().zip(&constructor.fields) {
            let value = if data::lifted(&world, field)
                && !matches!(module.expr(source), Expr::Var { .. })
            {
                lower_region(context, source, field, locals, instructions, blocks, true)?
            } else if matches!(module.expr(source), Expr::Case { .. } | Expr::Let { .. }) {
                lower_region(context, source, field, locals, instructions, blocks, false)?
            } else {
                lower_value(context, source, field, locals, instructions, blocks)?
            };
            arguments.push(value);
        }
        let value = fresh_value(context);
        instructions.push(Instruction {
            result: Value {
                id: value,
                ty: ty.clone(),
            },
            operation: Operation::Construct {
                constructor,
                arguments,
            },
            origin: origin(Rule::Construct),
        });
        return Ok(value);
    }
    let value = match module.expr(current) {
        Expr::Lit(lit) => {
            let value = fresh_value(context);
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
        Expr::Var { name, .. } if module.reference(current) == Some(h2r_core_ir::Ref::Global) => {
            let modules = modules
                .ok_or_else(|| fail(Some(current), "external references require a loaded world"))?;
            let (target_module, binder) = linkage::imported_top(modules, name)
                .map_err(|reason| fail(Some(current), &reason))?;
            let target_ty = modules[target_module].binder_ty(binder);
            if !linkage::closed_type(ty) || !linkage::closed_type(target_ty) {
                return Err(fail(
                    Some(current),
                    "import reference requires closed structured types",
                ));
            }
            if !ty.alpha_eq(target_ty) {
                return Err(fail(Some(current), "import reference type mismatch"));
            }
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: ty.clone(),
                },
                operation: Operation::TopReference {
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                    module: target_module,
                    binder,
                },
                origin: origin(Rule::TopReference),
            });
            value
        }
        Expr::Var { .. } => {
            let binder = module
                .resolve(current)
                .ok_or_else(|| fail(Some(current), "external references are not lowered yet"))?;
            if !same_scoped_type(ty, view.binder_ty(binder), type_scope) {
                return Err(fail(Some(current), "returned reference type mismatch"));
            }
            if let Some((target, captures, 0)) = context.functions.get(&binder) {
                let arguments = captures
                    .iter()
                    .map(|b| {
                        locals
                            .get(b)
                            .copied()
                            .ok_or_else(|| fail(Some(current), "nullary join capture out of scope"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: ty.clone(),
                    },
                    operation: Operation::CallLocal {
                        target: *target,
                        arguments,
                    },
                    origin: origin(Rule::CallLocal),
                });
                return Ok(value);
            }
            if let Some((target, captures, _)) = context.functions.get(&binder) {
                let arguments = captures
                    .iter()
                    .map(|b| {
                        locals
                            .get(b)
                            .copied()
                            .ok_or_else(|| fail(Some(current), "closure capture out of scope"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: ty.clone(),
                    },
                    operation: Operation::MakeClosure {
                        target: *target,
                        arguments,
                    },
                    origin: origin(Rule::MakeClosure),
                });
                return Ok(value);
            }
            if let Some(value) = locals.get(&binder) {
                *value
            } else if matches!(module.binding(binder).site, BindSite::Top) {
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: ty.clone(),
                    },
                    operation: Operation::TopReference {
                        type_arguments: Vec::new(),
                        dictionaries: Vec::new(),
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
        Expr::App { arg, .. } if !matches!(module.expr(*arg), Expr::Type { .. }) => {
            let mut head = current;
            let mut argument_sources = Vec::new();
            let mut type_arguments = Vec::new();
            while let Expr::App { fun, arg } = module.expr(head) {
                if let Expr::Type { ty, .. } = module.expr(*arg) {
                    type_arguments.push(view.ty(*ty).clone());
                    head = *fun;
                    continue;
                }
                // Traversal is right-to-left: after reaching type arguments,
                // another value argument would mean an interleaved spine.
                if !type_arguments.is_empty() {
                    return Err(fail(
                        Some(head),
                        "type arguments must precede value arguments",
                    ));
                }
                argument_sources.push(*arg);
                head = *fun;
            }
            argument_sources.reverse();
            type_arguments.reverse();
            let primitive = primitive::resolve(module, head);
            let constructor = boxed::resolves(module, head);
            let local = module
                .resolve(head)
                .and_then(|b| context.functions.get(&b).map(|f| (b, f)));
            let indirect = module.resolve(head).filter(|b| locals.contains_key(b));
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
                            &type_arguments,
                            &argument_sources,
                        )
                        .map_err(|reason| fail(Some(head), &reason))?
                        .ok_or_else(|| {
                            fail(Some(head), "application requires a top-level binding")
                        })?,
                    )
                };
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
                // Already instantiated at the instance's type arguments.
                Some(resolved) => resolved.signature.clone(),
                None => instantiate::apply(head_ty, &type_arguments)
                    .map_err(|reason| fail(Some(current), &reason))?,
            };
            let mut signature = &instantiated;
            let argument_sources = match &target {
                Some(resolved) => resolved.arguments.clone(),
                None => argument_sources,
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
            let apply = indirect.is_some() || arity != Some(argument_sources.len() as u32);
            if apply
                && (primitive.is_some()
                    || constructor
                    || (target.is_none() && !type_arguments.is_empty())
                    || !data::function(&world, head_ty))
            {
                return Err(fail(
                    Some(current),
                    "direct call must match known target arity",
                ));
            }
            if !linkage::closed_type(signature) || !linkage::closed_type(ty) {
                return Err(fail(
                    Some(current),
                    "direct call requires closed structured types",
                ));
            }
            // Every value argument was a dictionary: the spine denotes one
            // instance, with no runtime call and no allocation.
            if let Some(resolved) = &target
                && argument_sources.is_empty()
            {
                if !instantiated.alpha_eq(ty) {
                    return Err(fail(Some(current), "instance reference type mismatch"));
                }
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: ty.clone(),
                    },
                    operation: reference_operation(&resolved.reference),
                    origin: origin(if resolved.method {
                        Rule::ResolveMethod
                    } else {
                        Rule::ResolveInstance
                    }),
                });
                return Ok(value);
            }
            let mut arguments = Vec::new();
            for source in argument_sources {
                let Ty::Fun { arg, res, .. } = signature else {
                    return Err(fail(Some(current), "direct call lacks a value arrow"));
                };
                let value = match module.expr(source) {
                    Expr::App { .. } if primitive::is_int(arg) => {
                        lower_value(context, source, arg, locals, instructions, blocks)?
                    }
                    Expr::Case { .. } | Expr::Let { .. } if primitive::is_int(arg) => {
                        lower_region(context, source, arg, locals, instructions, blocks, false)?
                    }
                    Expr::App { .. } | Expr::Case { .. } | Expr::Let { .. } | Expr::Lam { .. }
                        if data::lifted(&world, arg) =>
                    {
                        lower_region(context, source, arg, locals, instructions, blocks, true)?
                    }
                    Expr::Lit(lit) => {
                        let value = fresh_value(context);
                        instructions.push(Instruction {
                            result: Value {
                                id: value,
                                ty: (**arg).clone(),
                            },
                            operation: Operation::Literal(lit.clone()),
                            origin: Origin {
                                module: module_index,
                                source: Source::Expr(source),
                                rule: Rule::Literal,
                            },
                        });
                        value
                    }
                    Expr::Var { .. } => {
                        if module
                            .resolve(source)
                            .is_some_and(|b| context.functions.contains_key(&b))
                            || data::resolve(&world, module_index, source, arg)
                                .map_err(|e| fail(Some(source), &e))?
                                .is_some()
                        {
                            lower_value(context, source, arg, locals, instructions, blocks)?
                        } else if let Some(value) = module
                            .resolve(source)
                            .and_then(|binder| locals.get(&binder))
                        {
                            if !arg.alpha_eq(
                                &params
                                    .iter()
                                    .chain(instructions.iter().map(|i: &Instruction| &i.result))
                                    .find(|v| v.id == *value)
                                    .expect("available local value")
                                    .ty,
                            ) {
                                return Err(fail(
                                    Some(source),
                                    "direct call argument type mismatch",
                                ));
                            }
                            *value
                        } else {
                            let (argument_module, argument_binder, argument_ty) =
                                instantiate::target(module, module_index, modules, source)
                                    .map_err(|reason| fail(Some(source), &reason))?;
                            if !linkage::closed_type(argument_ty) || !arg.alpha_eq(argument_ty) {
                                return Err(fail(Some(source), "top-level argument type mismatch"));
                            }
                            let value = fresh_value(context);
                            instructions.push(Instruction {
                                result: Value {
                                    id: value,
                                    ty: (**arg).clone(),
                                },
                                operation: Operation::TopReference {
                                    type_arguments: Vec::new(),
                                    dictionaries: Vec::new(),
                                    module: argument_module,
                                    binder: argument_binder,
                                },
                                origin: Origin {
                                    module: module_index,
                                    source: Source::Expr(source),
                                    rule: Rule::TopReference,
                                },
                            });
                            value
                        }
                    }
                    _ => {
                        return Err(fail(
                            Some(source),
                            "call arguments require supported Int#/Int computations or shared references",
                        ));
                    }
                };
                arguments.push(value);
                signature = res;
            }
            if !signature.alpha_eq(ty) {
                return Err(fail(Some(current), "direct call result type mismatch"));
            }
            let callee = match (apply, &target) {
                (false, _) => None,
                // The callee is one instance, not the bare head: its type and
                // dictionary arguments are compile-time evidence, so nothing
                // in the source spine corresponds to them at runtime.
                (true, Some(resolved)) => {
                    let value = fresh_value(context);
                    instructions.push(Instruction {
                        result: Value {
                            id: value,
                            ty: instantiated.clone(),
                        },
                        operation: reference_operation(&resolved.reference),
                        origin: Origin {
                            module: module_index,
                            source: Source::Expr(head),
                            rule: instance_rule(resolved),
                        },
                    });
                    Some(value)
                }
                (true, None) => Some(lower_value(
                    context,
                    head,
                    head_ty,
                    locals,
                    instructions,
                    blocks,
                )?),
            };
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: ty.clone(),
                },
                operation: if let Some(callee) = callee {
                    Operation::Apply { callee, arguments }
                } else if constructor {
                    Operation::BoxInt(arguments[0])
                } else if let Some(op) = primitive {
                    Operation::IntBinary { op, arguments }
                } else if let Some((_, (target, captures, _))) = local {
                    let mut actual = captures
                        .iter()
                        .map(|b| {
                            locals.get(b).copied().ok_or_else(|| {
                                fail(Some(current), "local function capture out of scope")
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    actual.extend(arguments);
                    Operation::CallLocal {
                        target: *target,
                        arguments: actual,
                    }
                } else {
                    let resolved = target.as_ref().expect("resolved direct target");
                    Operation::CallTop {
                        module: resolved.reference.module,
                        binder: resolved.reference.binder,
                        type_arguments: resolved.reference.type_arguments.clone(),
                        dictionaries: resolved.reference.dictionaries.clone(),
                        arguments,
                    }
                },
                origin: origin(if apply {
                    Rule::Apply
                } else if constructor {
                    Rule::BoxInt
                } else if primitive.is_some() {
                    Rule::IntBinary
                } else if local.is_some() {
                    Rule::CallLocal
                } else if target.as_ref().is_some_and(|r| r.method) {
                    Rule::ResolveMethod
                } else {
                    Rule::CallTop
                }),
            });
            value
        }
        Expr::App { .. } => {
            let mut head = current;
            let mut arguments = Vec::new();
            while let Expr::App { fun, arg } = module.expr(head) {
                let Expr::Type { ty, .. } = module.expr(*arg) else {
                    return Err(fail(Some(head), "value applications are not lowered yet"));
                };
                arguments.push(view.ty(*ty).clone());
                head = *fun;
            }
            arguments.reverse();
            let (target_module, binder, head_ty) =
                instantiate::target(module, module_index, modules, head)
                    .map_err(|reason| fail(Some(head), &reason))?;
            let result_ty = instantiate::apply(head_ty, &arguments)
                .map_err(|reason| fail(Some(current), &reason))?;
            if !linkage::closed_type(ty) || !ty.alpha_eq(&result_ty) {
                return Err(fail(Some(current), "type application result mismatch"));
            }
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: ty.clone(),
                },
                operation: Operation::TopReference {
                    module: target_module,
                    binder,
                    type_arguments: arguments,
                    dictionaries: Vec::new(),
                },
                origin: origin(Rule::InstantiateTop),
            });
            value
        }
        Expr::Let { bind, body } => {
            if !bind.pairs.is_empty()
                && bind.pairs.iter().all(|p| {
                    matches!(module.expr(p.rhs), Expr::Lam { .. })
                        || (module.binder(p.binder).is_join_point == Some(true)
                            && module.binder(p.binder).arity == Some(0))
                })
            {
                return lower_functions(
                    context,
                    current,
                    bind,
                    *body,
                    ty,
                    locals,
                    instructions,
                    blocks,
                );
            }
            let [pair] = bind.pairs.as_slice() else {
                return Err(fail(
                    Some(current),
                    "lazy let requires one non-recursive binding",
                ));
            };
            // A dictionary the desugarer bound locally is a compile-time
            // identity, not a runtime value: binding it here keeps the method
            // calls under it resolvable and allocates nothing.
            let extended;
            if !bind.recursive
                && module.binder(pair.binder).is_join_point != Some(true)
                && let Some(reference) =
                    dict::resolve_dictionary(&world, &context.scope(), pair.rhs, 0)
                        .map_err(|reason| fail(Some(current), &reason))?
            {
                extended = {
                    let mut scope = context.dictionary_scope.clone();
                    scope.insert(pair.binder, reference);
                    scope
                };
                let nested = BodyContext {
                    dictionary_scope: &extended,
                    ..*context
                };
                return lower_value(&nested, *body, ty, locals, instructions, blocks);
            }
            let binding_ty = view.binder_ty(pair.binder);
            if bind.recursive
                || !data::lifted(&world, binding_ty)
                || module.binder(pair.binder).is_join_point == Some(true)
            {
                return Err(fail(
                    Some(current),
                    "lazy let requires a supported non-recursive lifted value, not a join point",
                ));
            }
            let rhs = if matches!(module.expr(pair.rhs), Expr::Var { .. }) {
                lower_value(context, pair.rhs, binding_ty, locals, instructions, blocks)?
            } else {
                lower_region(
                    context,
                    pair.rhs,
                    binding_ty,
                    locals,
                    instructions,
                    blocks,
                    true,
                )?
            };
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: binding_ty.clone(),
                },
                operation: Operation::Move(rhs),
                origin: origin(Rule::LazyBinding),
            });
            let previous = locals.insert(pair.binder, value);
            let result = lower_value(context, *body, ty, locals, instructions, blocks);
            if let Some(previous) = previous {
                locals.insert(pair.binder, previous);
            } else {
                locals.remove(&pair.binder);
            }
            result?
        }
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } if data::is_data(&world, view.binder_ty(*binder)) => {
            if !view.ty(*result_ty).alpha_eq(ty) || !data::supported(&world, ty) {
                return Err(fail(Some(current), "algebraic case result mismatch"));
            }
            let family = data::family(&world, view.binder_ty(*binder))
                .map_err(|e| fail(Some(current), &e))?;
            let scrutinee = lower_value(
                context,
                *scrut,
                view.binder_ty(*binder),
                locals,
                instructions,
                blocks,
            )?;
            let captures: Vec<_> = locals.iter().map(|(b, v)| (*b, *v)).collect();
            let arguments: Vec<_> = captures.iter().map(|(_, v)| *v).collect();
            let mut arms = Vec::new();
            let mut seen = std::collections::BTreeSet::new();
            let mut default = false;
            for alt in alts {
                let constructor = match &alt.con {
                    h2r_core_ir::AltCon::DataAlt { name, tag, .. } => {
                        let c = family
                            .iter()
                            .find(|c| c.name == *name && c.tag == *tag)
                            .ok_or_else(|| fail(Some(current), "case constructor not in family"))?
                            .clone();
                        if !seen.insert(*tag) {
                            return Err(fail(Some(current), "duplicate constructor pattern"));
                        }
                        Some(c)
                    }
                    h2r_core_ir::AltCon::Default if !default => {
                        default = true;
                        None
                    }
                    _ => return Err(fail(Some(current), "invalid algebraic alternative")),
                };
                let fields = constructor
                    .as_ref()
                    .map_or(&[][..], |c| c.fields.as_slice());
                if fields.len() != alt.binders.len()
                    || fields
                        .iter()
                        .zip(&alt.binders)
                        .any(|(ty, b)| !ty.alpha_eq(view.binder_ty(*b)))
                {
                    return Err(fail(Some(current), "case field layout mismatch"));
                }
                let mut branch_params = Vec::new();
                let mut branch_locals = BTreeMap::new();
                for (b, v) in &captures {
                    let ty = &params
                        .iter()
                        .chain(instructions.iter().map(|i| &i.result))
                        .find(|p| p.id == *v)
                        .expect("available capture")
                        .ty;
                    let id = fresh_value(context);
                    branch_params.push(Value { id, ty: ty.clone() });
                    branch_locals.insert(*b, id);
                }
                for b in std::iter::once(binder).chain(&alt.binders) {
                    let id = fresh_value(context);
                    branch_params.push(Value {
                        id,
                        ty: view.binder_ty(*b).clone(),
                    });
                    branch_locals.insert(*b, id);
                }
                let branch_context = BodyContext {
                    params: &branch_params,
                    ..*context
                };
                let target = lower_tail(&branch_context, alt.rhs, ty, &branch_locals, blocks)?;
                arms.push(DataArm {
                    constructor,
                    target,
                });
            }
            if arms.is_empty() || (!default && seen.len() != family.len()) {
                return Err(fail(Some(current), "non-exhaustive algebraic case"));
            }
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: ty.clone(),
                },
                operation: Operation::MatchData {
                    scrutinee,
                    arguments,
                    arms,
                },
                origin: origin(Rule::MatchData),
            });
            value
        }
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } if boxed::is_int(view.binder_ty(*binder)) => {
            let [alt] = alts.as_slice() else {
                return Err(fail(
                    Some(current),
                    "boxed Int case requires one exhaustive alternative",
                ));
            };
            let field = match alt.binders.as_slice() {
                [field]
                    if boxed::alternative(&alt.con)
                        && primitive::is_int(view.binder_ty(*field)) =>
                {
                    Some(*field)
                }
                [] if matches!(alt.con, h2r_core_ir::AltCon::Default) => None,
                _ => return Err(fail(Some(current), "unsupported boxed Int alternative")),
            };
            if !view.ty(*result_ty).alpha_eq(ty) {
                return Err(fail(Some(current), "boxed case result type mismatch"));
            }
            let scrutinee = lower_value(
                context,
                *scrut,
                view.binder_ty(*binder),
                locals,
                instructions,
                blocks,
            )?;
            let value = fresh_value(context);
            let Ty::Fun { arg: int, .. } = primitive::signature() else {
                unreachable!()
            };
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: *int,
                },
                operation: Operation::UnboxInt(scrutinee),
                origin: origin(Rule::UnboxInt),
            });
            let previous = locals.clone();
            locals.insert(*binder, scrutinee);
            if let Some(field) = field {
                locals.insert(field, value);
            }
            let result = lower_value(context, alt.rhs, ty, locals, instructions, blocks);
            *locals = previous;
            result?
        }
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } => {
            if alts.len() != 1 || !matches!(alts[0].con, h2r_core_ir::AltCon::Default) {
                if !primitive::is_int(view.binder_ty(*binder)) {
                    return Err(fail(Some(current), "unsupported case scrutinee carrier"));
                }
                return lower_region(context, current, ty, locals, instructions, blocks, false);
            }
            let [alt] = alts.as_slice() else {
                return Err(fail(
                    Some(current),
                    "strict Int# case requires one DEFAULT alternative",
                ));
            };
            if !matches!(alt.con, h2r_core_ir::AltCon::Default)
                || !alt.binders.is_empty()
                || !primitive::is_int(view.binder_ty(*binder))
                || !data::supported(&world, ty)
                || !view.ty(*result_ty).alpha_eq(ty)
            {
                return Err(fail(
                    Some(current),
                    "unsupported strict case type or alternative",
                ));
            }
            let scrutinee = lower_value(
                context,
                *scrut,
                view.binder_ty(*binder),
                locals,
                instructions,
                blocks,
            )?;
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: view.binder_ty(*binder).clone(),
                },
                operation: Operation::Move(scrutinee),
                origin: origin(Rule::StrictPosition),
            });
            let previous = locals.insert(*binder, value);
            let result = lower_value(context, alt.rhs, ty, locals, instructions, blocks);
            if let Some(previous) = previous {
                locals.insert(*binder, previous);
            } else {
                locals.remove(binder);
            }
            result?
        }
        Expr::Type { .. } | Expr::Coercion => {
            return Err(fail(Some(current), "type or coercion in value position"));
        }
        Expr::Lam { .. } => {
            return lower_lambda(context, current, ty, locals, instructions, blocks);
        }
        Expr::Tick(_) => {
            return Err(fail(
                Some(current),
                "nested lambda or tick is not lowered yet",
            ));
        }
    };

    Ok(value)
}

#[allow(clippy::too_many_arguments)]
fn lower_functions(
    context: &BodyContext<'_>,
    source: ExprId,
    bind: &h2r_core_ir::Bind,
    body: ExprId,
    ty: &Ty,
    locals: &BTreeMap<BinderId, ValueId>,
    instructions: &mut Vec<Instruction>,
    blocks: &mut Vec<Block>,
) -> Result<ValueId, LowerError> {
    let fail = |reason: &str| LowerError {
        module: context.module_index,
        owner: context.owner,
        source: Some(source),
        reason: reason.into(),
    };
    let module = context.module;
    let view = context.view;
    let world = context.world();
    let captures: Vec<_> = locals.keys().copied().collect();
    let capture_types: Vec<_> = locals
        .values()
        .map(|id| {
            context
                .params
                .iter()
                .chain(instructions.iter().map(|i| &i.result))
                .find(|v| v.id == *id)
                .expect("available capture")
                .ty
                .clone()
        })
        .collect();
    let mut functions = context.functions.clone();
    let mut definitions = Vec::new();
    let mut bodies = Vec::new();
    for pair in &bind.pairs {
        let mut rhs = pair.rhs;
        let mut result = view.binder_ty(pair.binder);
        let mut parameters = Vec::new();
        while let Expr::Lam { binder, body } = module.expr(rhs) {
            let Ty::Fun { arg, res, .. } = result else {
                return Err(fail("local functions require monomorphic value lambdas"));
            };
            if module.binder(*binder).kind != BinderKind::Id
                || !arg.alpha_eq(view.binder_ty(*binder))
                || !data::supported(&world, arg)
            {
                return Err(fail("unsupported local function parameter"));
            }
            parameters.push(*binder);
            result = res;
            rhs = *body;
        }
        if (parameters.is_empty()
            && !(module.binder(pair.binder).is_join_point == Some(true)
                && module.binder(pair.binder).arity == Some(0)))
            || !data::supported(&world, result)
            || !linkage::closed_type(view.binder_ty(pair.binder))
        {
            return Err(fail("local functions require supported closed signatures"));
        }
        let target = BlockId(blocks.len() as u32);
        blocks.push(Block {
            id: target,
            params: Vec::new(),
            instructions: Vec::new(),
            terminator: Terminator {
                exit: Exit::Return(ValueId(u32::MAX)),
                origin: Origin {
                    module: context.module_index,
                    source: Source::Expr(rhs),
                    rule: Rule::Return,
                },
            },
        });
        functions.insert(pair.binder, (target, captures.clone(), parameters.len()));
        definitions.push(LocalDefinition {
            binder: pair.binder,
            target,
            result_ty: result.clone(),
        });
        bodies.push((rhs, parameters));
    }
    for (definition, (rhs, parameters)) in definitions.iter().zip(bodies) {
        let mut params = Vec::new();
        let mut scope = BTreeMap::new();
        for (binder, ty) in captures
            .iter()
            .copied()
            .zip(capture_types.iter().cloned())
            .chain(parameters.iter().map(|b| (*b, view.binder_ty(*b).clone())))
        {
            let id = fresh_value(context);
            scope.insert(binder, id);
            params.push(Value { id, ty });
        }
        let nested = BodyContext {
            params: &params,
            functions: if bind.recursive {
                &functions
            } else {
                context.functions
            },
            ..*context
        };
        lower_tail_at(
            &nested,
            rhs,
            &definition.result_ty,
            &scope,
            blocks,
            definition.target,
        )?;
    }
    let nested = BodyContext {
        functions: &functions,
        ..*context
    };
    let value = lower_region(&nested, body, ty, locals, instructions, blocks, false)?;
    let instruction = instructions.last_mut().expect("body region");
    let Operation::EvaluateBlock { target, arguments } = &instruction.operation else {
        unreachable!()
    };
    instruction.operation = Operation::LocalScope {
        definitions,
        target: *target,
        arguments: arguments.clone(),
    };
    instruction.origin = Origin {
        module: context.module_index,
        source: Source::Expr(source),
        rule: Rule::LocalScope,
    };
    Ok(value)
}

fn lower_lambda(
    context: &BodyContext<'_>,
    source: ExprId,
    ty: &Ty,
    locals: &BTreeMap<BinderId, ValueId>,
    instructions: &mut Vec<Instruction>,
    blocks: &mut Vec<Block>,
) -> Result<ValueId, LowerError> {
    let fail = |reason: &str| LowerError {
        module: context.module_index,
        owner: context.owner,
        source: Some(source),
        reason: reason.into(),
    };
    if !data::function(&context.world(), ty) {
        return Err(fail(
            "closure requires a supported monomorphic function type",
        ));
    }
    let mut params = Vec::new();
    let mut scope = BTreeMap::new();
    let mut arguments = Vec::new();
    for (binder, value) in locals {
        let original = context
            .params
            .iter()
            .chain(instructions.iter().map(|i| &i.result))
            .find(|v| v.id == *value)
            .ok_or_else(|| fail("missing closure capture"))?;
        let id = fresh_value(context);
        params.push(Value {
            id,
            ty: original.ty.clone(),
        });
        scope.insert(*binder, id);
        arguments.push(*value);
    }
    let mut rhs = source;
    let mut result = ty;
    while let Expr::Lam { binder, body } = context.module.expr(rhs) {
        let Ty::Fun { arg, res, .. } = result else {
            return Err(fail("closure lambda lacks function arrow"));
        };
        if context.module.binder(*binder).kind != BinderKind::Id
            || !arg.alpha_eq(context.view.binder_ty(*binder))
        {
            return Err(fail("closure lambda parameter mismatch"));
        }
        let id = fresh_value(context);
        params.push(Value {
            id,
            ty: (**arg).clone(),
        });
        scope.insert(*binder, id);
        result = res;
        rhs = *body;
    }
    let nested = BodyContext {
        params: &params,
        ..*context
    };
    let target = lower_tail(&nested, rhs, result, &scope, blocks)?;
    let id = fresh_value(context);
    instructions.push(Instruction {
        result: Value { id, ty: ty.clone() },
        operation: Operation::MakeClosure { target, arguments },
        origin: Origin {
            module: context.module_index,
            source: Source::Expr(source),
            rule: Rule::MakeClosure,
        },
    });
    Ok(id)
}

fn lower_region(
    context: &BodyContext<'_>,
    source: ExprId,
    ty: &Ty,
    locals: &BTreeMap<BinderId, ValueId>,
    instructions: &mut Vec<Instruction>,
    blocks: &mut Vec<Block>,
    delayed: bool,
) -> Result<ValueId, LowerError> {
    let mut params = Vec::new();
    let mut arguments = Vec::new();
    let mut region_locals = BTreeMap::new();
    for (binder, value) in locals {
        let source_value = context
            .params
            .iter()
            .chain(instructions.iter().map(|i| &i.result))
            .find(|p| p.id == *value)
            .expect("lexical value available");
        let id = fresh_value(context);
        params.push(Value {
            id,
            ty: source_value.ty.clone(),
        });
        arguments.push(*value);
        region_locals.insert(*binder, id);
    }
    let region_context = BodyContext {
        params: &params,
        ..*context
    };
    let target = lower_tail(&region_context, source, ty, &region_locals, blocks)?;
    let value = fresh_value(context);
    instructions.push(Instruction {
        result: Value {
            id: value,
            ty: ty.clone(),
        },
        operation: if delayed {
            Operation::DelayBlock { target, arguments }
        } else {
            Operation::EvaluateBlock { target, arguments }
        },
        origin: Origin {
            module: context.module_index,
            source: Source::Expr(source),
            rule: if delayed {
                Rule::DelayBlock
            } else {
                Rule::EvaluateBlock
            },
        },
    });
    Ok(value)
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
