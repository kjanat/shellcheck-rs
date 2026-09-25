//! Conservative Core lowering: direct calls, scalar control flow, lazy regions
//! and algebraic construction/matching. Unsupported constructs fail explicitly.
//! This is not a whole-program driver or an independent semantic verifier.

use std::collections::{BTreeMap, BTreeSet};

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
    /// The concrete subject the refusal is about — an external stable name, a
    /// type constructor — where the refusing site knows one. Ranking blockers
    /// by reason alone cannot say *which* dependency or carrier is missing.
    pub detail: Option<String>,
}

impl LowerError {
    /// Name the subject of a refusal. Nothing reads this back as evidence.
    pub(super) fn about(mut self, subject: impl Into<String>) -> Self {
        self.detail = Some(subject.into());
        self
    }
}

/// Name the occurrence a refusal is about, when the source node is a variable.
/// A spelling is a ranking key here and never evidence for a decision.
fn named(module: &Module, source: ExprId, error: LowerError) -> LowerError {
    match module.expr(source) {
        Expr::Var { name, .. } => error.about(name.clone()),
        _ => error,
    }
}

/// Which part of a function type has no carrier, for a refusal that is about
/// the type rather than the call. The first argument or the result that fails,
/// so a ranking names the type to carry next rather than the arrow it sat in.
fn unsupported_component(world: &World<'_>, ty: &Ty) -> String {
    let mut current = ty;
    while let Ty::Fun { arg, res, .. } = current {
        if !data::supported(world, arg) {
            return type_head(arg);
        }
        current = res;
    }
    type_head(current)
}

/// The head of a type, as a ranking key. Not an identity and not evidence.
pub fn type_head(ty: &Ty) -> String {
    match ty {
        Ty::Con { tycon, args } if args.is_empty() => tycon.name.to_string(),
        Ty::Con { tycon, args } => format!("{} /{}", tycon.name, args.len()),
        Ty::Fun { .. } => "->".into(),
        Ty::Var(_) => "a type variable".into(),
        Ty::ForAll { .. } => "forall".into(),
        Ty::App { .. } => "a type application".into(),
        Ty::Lit { kind, .. } => format!("a {kind} type literal"),
        Ty::Opaque { .. } => "an opaque type".into(),
    }
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
    pub erased_cast: Option<ExprId>,
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
    let (leaf, verified) = lower_leaf_impl(module, module_index, owner, id, None, None, &[], &[])?;
    verified.map(|()| leaf)
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
    let (leaf, verified) = lower_leaf_unverified(
        modules,
        None,
        module_index,
        owner,
        id,
        type_arguments,
        dictionaries,
    )?;
    verified.map(|()| leaf)
}

pub fn lower_leaf_unverified(
    modules: &[Module],
    catalog: Option<&super::Catalog>,
    module_index: usize,
    owner: BinderId,
    id: FnId,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
) -> Result<(LoweredLeaf, Result<(), LowerError>), LowerError> {
    let module = modules.get(module_index).ok_or_else(|| LowerError {
        module: module_index,
        owner,
        source: None,
        reason: "module index is outside the loaded world".into(),
        detail: None,
    })?;
    lower_leaf_impl(
        module,
        module_index,
        owner,
        id,
        Some(modules),
        catalog,
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
    catalog: Option<&super::Catalog>,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
) -> Result<(LoweredLeaf, Result<(), LowerError>), LowerError> {
    let fail = |source, reason: &str| LowerError {
        module: module_index,
        owner,
        source,
        reason: reason.into(),
        detail: None,
    };
    let pair = module
        .top
        .iter()
        .flat_map(|b| &b.pairs)
        .find(|pair| pair.binder == owner)
        .ok_or_else(|| fail(None, "owner is not a top-level binding"))?;
    let requested = type_arguments;
    let extended = leaf_type_arguments(module, pair.rhs, owner, requested);
    let type_arguments = extended.as_slice();
    // Bind the source type lambdas first, so the body's types can be read
    // through one substituted view of the module's immutable type table.
    let (subst, signature, cast) = bind_type_arguments(module, pair.rhs, owner, type_arguments)
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
    let mut erased_cast = None;
    let mut locals = BTreeMap::new();
    let mut instantiated = 0;
    let mut dictionary_parameters = Vec::new();
    let mut dictionary_scope: BTreeMap<BinderId, DictionaryRef> = BTreeMap::new();
    let world = World {
        module,
        index: module_index,
        modules,
        catalog,
    };
    loop {
        match module.expr(current) {
            Expr::Tick(body) => {
                erased_ticks.push(current);
                current = *body;
            }
            Expr::Cast { expr, .. } if cast == Some(current) => {
                erased_cast = Some(current);
                current = *expr;
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
                            name: source_binder.name.as_str().into(),
                            occ: source_binder.occ.as_str().into(),
                            unique: source_binder.unique.as_str().into(),
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
                    ty: shared(arg),
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
    if erased_cast.is_some() {
        leaf_cast_preserves_representation(&world, pair.rhs, owner, requested, dictionaries.len())
            .map_err(|reason| fail(erased_cast, &reason))?;
    }
    let next_value = std::cell::Cell::new(params.len() as u32);
    let context = BodyContext {
        module,
        view: &view,
        module_index,
        owner,
        modules,
        catalog,
        params: &params,
        next_value: &next_value,
        type_scope: &type_scope,
        subst: &subst,
        dictionary_scope: &dictionary_scope,
        field_scope: &dict::NO_FIELDS,
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
        type_arguments: requested.to_vec(),
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
        erased_cast,
    };
    let verified = match modules {
        Some(modules) => verify::verify_leaf_cataloged(
            modules,
            catalog,
            module_index,
            owner,
            id,
            &lowered,
            requested,
            dictionaries,
        ),
        None => verify::verify_leaf(module, module_index, owner, id, &lowered),
    };
    let verified = verified
        .map(|_| ())
        .map_err(|reason| fail(Some(current), &reason));
    Ok((lowered, verified))
}

pub(super) fn leaf_type_arguments(
    module: &Module,
    rhs: ExprId,
    owner: BinderId,
    type_arguments: &[Ty],
) -> Vec<Ty> {
    let (leading, total) = type_lambda_counts(module, rhs, owner);
    let mut extended = type_arguments.to_vec();
    if type_arguments.len() >= leading {
        extended.resize(total.max(type_arguments.len()), data::erased_ty());
    }
    extended
}

pub(super) fn type_lambda_counts(module: &Module, rhs: ExprId, owner: BinderId) -> (usize, usize) {
    let (_, cast) = leaf_signature(module, rhs, owner);
    let mut current = rhs;
    let mut leading = 0;
    let mut total = 0;
    let mut valued = false;
    loop {
        match module.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::Cast { expr, .. } if cast == Some(current) => current = *expr,
            Expr::Lam { binder, body } => {
                if module.binder(*binder).kind == BinderKind::Tyvar {
                    total += 1;
                    leading += usize::from(!valued);
                } else {
                    valued = true;
                }
                current = *body;
            }
            _ => break,
        }
    }
    (leading, total)
}

pub(super) fn manifest_arity(module: &Module, rhs: ExprId, owner: BinderId) -> usize {
    let (_, cast) = leaf_signature(module, rhs, owner);
    let mut current = rhs;
    let mut values = 0;
    loop {
        match module.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::Cast { expr, .. } if cast == Some(current) => current = *expr,
            Expr::Lam { binder, body } => {
                values += usize::from(module.binder(*binder).kind != BinderKind::Tyvar);
                current = *body;
            }
            _ => return values,
        }
    }
}

/// Pair the instance's closed type arguments with the owner's leading type
/// lambdas and the matching quantifiers of its signature. Substitution is
/// capture-safe, so a rebinding quantifier inside the body is left alone.
pub(super) fn bind_type_arguments(
    module: &Module,
    rhs: ExprId,
    owner: BinderId,
    type_arguments: &[Ty],
) -> Result<(Substitution, Ty, Option<ExprId>), String> {
    let mut subst = Substitution::default();
    let (signature, cast) = leaf_signature(module, rhs, owner);
    if type_arguments.is_empty() {
        return Ok((subst, signature, cast));
    }
    let signature = bind_lambdas(module, rhs, cast, signature, type_arguments, &mut subst)?;
    if !linkage::closed_type(&signature) {
        return Err("specialized signature is not closed".into());
    }
    Ok((subst, signature, cast))
}

fn leaf_signature(module: &Module, rhs: ExprId, owner: BinderId) -> (Ty, Option<ExprId>) {
    let declared = module.binder_ty(owner);
    let top = under_ticks(module, rhs);
    match module.expr(top) {
        Expr::Cast {
            expr,
            from: Some(from),
            to: Some(to),
            ..
        } if matches!(module.expr(under_ticks(module, *expr)), Expr::Lam { .. })
            && module.ty(*to).alpha_eq(declared) =>
        {
            (module.ty(*from).clone(), Some(top))
        }
        _ => (declared.clone(), None),
    }
}

fn under_ticks(module: &Module, mut expr: ExprId) -> ExprId {
    while let Expr::Tick(body) = module.expr(expr) {
        expr = *body;
    }
    expr
}

pub(super) fn leaf_cast_preserves_representation(
    world: &World<'_>,
    rhs: ExprId,
    owner: BinderId,
    type_arguments: &[Ty],
    dictionaries: usize,
) -> Result<(), String> {
    let module = world.module;
    let (source, cast) = leaf_signature(module, rhs, owner);
    if cast.is_none() {
        return Err("the owner is not a cast of its lambdas".into());
    }
    let source = dict::instantiate_arguments(&source, type_arguments, dictionaries)?;
    let declared =
        dict::instantiate_arguments(module.binder_ty(owner), type_arguments, dictionaries)?;
    if data::same_representation(world, &source, &declared) {
        Ok(())
    } else {
        Err("a leaf's cast must not change how its value is held".into())
    }
}

/// Instantiate each type lambda's quantifier in lambda order. A value lambda
/// between two type lambdas keeps its arrow, and the quantifiers after it are
/// instantiated inside its result.
fn bind_lambdas(
    module: &Module,
    mut current: ExprId,
    cast: Option<ExprId>,
    signature: Ty,
    type_arguments: &[Ty],
    subst: &mut Substitution,
) -> Result<Ty, String> {
    let [argument, rest @ ..] = type_arguments else {
        return Ok(signature);
    };
    if !linkage::closed_type(argument) {
        return Err("specialization requires closed structured type arguments".into());
    }
    loop {
        match module.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::Cast { expr, .. } if cast == Some(current) => current = *expr,
            _ => break,
        }
    }
    let Expr::Lam { binder, body } = module.expr(current) else {
        return Err("instance has more type arguments than the owner binds".into());
    };
    let source = module.binder(*binder);
    if source.kind != BinderKind::Tyvar {
        let Ty::Fun { mult, arg, res } = signature else {
            return Err("value lambda needs a function type".into());
        };
        let res = bind_lambdas(module, *body, cast, *res, type_arguments, subst)?;
        return Ok(Ty::Fun {
            mult,
            arg,
            res: Box::new(res),
        });
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
    subst.bind(
        TyVarId {
            name: source.name.as_str().into(),
            occ: source.occ.as_str().into(),
            unique: source.unique.as_str().into(),
        },
        argument.clone(),
    )?;
    bind_lambdas(module, *body, cast, instantiated, rest, subst)
}

struct BodyContext<'a> {
    module: &'a Module,
    view: &'a TypeView<'a>,
    module_index: usize,
    owner: BinderId,
    modules: Option<&'a [Module]>,
    catalog: Option<&'a super::Catalog>,
    params: &'a [Value],
    next_value: &'a std::cell::Cell<u32>,
    type_scope: &'a [(TyVarId, TyVarId)],
    /// This instance's type arguments, for reading source types in scope.
    subst: &'a Substitution,
    /// Dictionary lambdas the instance key absorbed. These are compile-time
    /// identities that scope over the whole body, not runtime values.
    dictionary_scope: &'a BTreeMap<BinderId, DictionaryRef>,
    field_scope: &'a BTreeMap<BinderId, (DictionaryRef, dict::Selector)>,
    functions: &'a LocalFunctions,
}

impl<'a> BodyContext<'a> {
    fn world(&self) -> World<'a> {
        World {
            module: self.module,
            index: self.module_index,
            modules: self.modules,
            catalog: self.catalog,
        }
    }

    fn scope(&self) -> dict::Scope<'a> {
        dict::Scope {
            module: self.module_index,
            types: self.subst,
            dictionaries: self.dictionary_scope,
            fields: self.field_scope,
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

/// A saturated `GHC.CString` unpacker applied to a string literal, as one
/// spine: the unpacker, the literal's node and the list it appends to. An
/// unpacker applied to anything but a literal is not this shape, because this
/// backend has no `Addr#` value to give it.
fn unpacker_spine(
    context: &BodyContext<'_>,
    current: ExprId,
) -> Option<(strings::Unpacker, ExprId, Option<ExprId>)> {
    let module = context.module;
    let mut head = current;
    let mut arguments = Vec::new();
    while let Expr::App { fun, arg } = module.expr(head) {
        if matches!(module.expr(*arg), Expr::Type { .. }) {
            return None;
        }
        arguments.push(*arg);
        head = *fun;
    }
    arguments.reverse();
    if module.reference(head) != Some(h2r_core_ir::Ref::Global) {
        return None;
    }
    let unpacker = strings::resolve(module, head)?;
    if arguments.len() != unpacker.arity() as usize {
        return None;
    }
    let literal = *arguments.first()?;
    strings::address_literal(&context.world(), context.module_index, literal)?;
    Some((unpacker, literal, arguments.get(1).copied()))
}

/// A saturated call to an implemented library function, as one spine: the
/// entry, its closed type arguments and its value arguments. A partial
/// application is not this shape and falls through to the ordinary path,
/// which refuses it by name.
fn world_spine(context: &BodyContext<'_>, mut head: ExprId) -> bool {
    let module = context.module;
    while let Expr::App { fun, .. } = module.expr(head) {
        head = *fun;
    }
    module
        .resolve(head)
        .is_some_and(|b| matches!(module.binding(b).site, BindSite::Top))
        || (module.reference(head) == Some(h2r_core_ir::Ref::Global)
            && instantiate::target(&context.world(), head).is_ok())
}

fn external_spine(
    context: &BodyContext<'_>,
    current: ExprId,
) -> Option<(external::External, Vec<Ty>, Vec<ExprId>)> {
    let module = context.module;
    let mut head = current;
    let mut types = Vec::new();
    let mut values = Vec::new();
    while let Expr::App { fun, arg } = module.expr(head) {
        match module.expr(*arg) {
            Expr::Type { ty, .. } => types.push(context.view.ty(*ty).clone()),
            // Right-to-left: a value argument after a type argument is an
            // interleaved spine, which none of these entries has.
            _ if types.is_empty() => values.push(*arg),
            _ => return None,
        }
        head = *fun;
    }
    types.reverse();
    values.reverse();
    if module.reference(head) != Some(h2r_core_ir::Ref::Global) {
        return None;
    }
    let entry = external::resolve(module, head)?;
    if types.len() != entry.type_arity()
        || values.len() != entry.dictionary_arity() + entry.value_arity()
    {
        return None;
    }
    types.iter().all(linkage::closed_type).then_some(())?;
    if entry.dictionary_arity() == 1 {
        external::equality(module, values[0], &entry.element(&types)?)?;
    }
    Some((entry, types, values))
}

/// A saturated call to a binding GHC proved never returns.
///
/// Direct calls must be outside the loaded world, or pass more type arguments
/// than the world's definition binds. Inside an empty case, any divergent
/// global qualifies, and so does a lexical top-level binding's own demand
/// signature. Neither proof establishes runtime behavior: the resulting
/// terminator is analysis-only and cannot be emitted.
fn divergent_spine(
    context: &BodyContext<'_>,
    current: ExprId,
    ty: &Ty,
) -> Option<diverge::Divergent> {
    let module = context.module;
    let mut head = current;
    let mut expected = ty;
    while let Expr::Case {
        scrut,
        binder,
        ty: result,
        alts,
        ..
    } = module.expr(head)
    {
        if !alts.is_empty() || !context.view.ty(*result).alpha_eq(expected) {
            return None;
        }
        expected = context.view.binder_ty(*binder);
        head = *scrut;
    }
    let mut values = 0usize;
    let mut types = 0usize;
    let mut first = None;
    while let Expr::App { fun, arg } = module.expr(head) {
        if let Expr::Type { ty, .. } = module.expr(*arg) {
            types += 1;
            first = Some(*ty);
        } else {
            values += 1;
        }
        head = *fun;
    }
    let empty_case = current != head && matches!(module.expr(current), Expr::Case { .. });
    if empty_case
        && let Some(binder) = module.resolve(head)
        && matches!(module.binding(binder).site, BindSite::Top)
    {
        let source = module.binder(binder);
        let demand = source.dmd_sig.as_ref()?;
        return (source.details.as_deref() == Some("")
            && demand.diverges
            && values >= demand.args.len())
        .then(|| diverge::Divergent {
            name: source.name.clone(),
            arity: demand.args.len(),
        });
    }
    if module.reference(head) != Some(h2r_core_ir::Ref::Global) {
        return None;
    }
    let divergent = diverge::resolve(module, head)?;
    // Fewer arguments than the demand signature's own count is a partial
    // application, which is a value and returns perfectly well.
    if values < divergent.arity {
        return None;
    }
    let wired = dict::wired_representation(&divergent.name, first.map(|ty| context.view.ty(ty)));
    match diverge::defined_quantifiers(context.world().iter().map(|(_, loaded)| loaded), &divergent)
    {
        Some(bound) if !empty_case && types - wired <= bound => None,
        _ => Some(divergent),
    }
}

/// The one operation a resolved primop denotes. Its carriers were already
/// fixed by the asserted signature the arguments were lowered at.
pub(super) fn erased_lambdas(
    module: &Module,
    subst: &Substitution,
    source: ExprId,
) -> Result<Option<Substitution>, String> {
    let mut local = subst.clone();
    let mut erased = false;
    let mut rhs = source;
    while let Expr::Lam { binder, body } = module.expr(rhs) {
        let source_binder = module.binder(*binder);
        if source_binder.kind == BinderKind::Tyvar {
            local.bind(
                TyVarId {
                    name: source_binder.name.as_str().into(),
                    occ: source_binder.occ.as_str().into(),
                    unique: source_binder.unique.as_str().into(),
                },
                data::erased_ty(),
            )?;
            erased = true;
        }
        rhs = *body;
    }
    Ok(erased.then_some(local))
}

pub(super) fn raise(
    module: &Module,
    head: ExprId,
    spine: &[dict::SpineArg],
) -> Option<(Machine, Vec<Ty>, ExprId)> {
    let Some(primitive::Prim::Machine(
        op @ (Machine::Raise
        | Machine::RaiseDivZero
        | Machine::RaiseUnderflow
        | Machine::RaiseOverflow),
    )) = primitive::resolve(module, head)
    else {
        return None;
    };
    let (operand, types) = spine.split_last()?;
    let dict::SpineArg::Value(operand) = operand else {
        return None;
    };
    let types = types
        .iter()
        .map(|argument| match argument {
            dict::SpineArg::Type(ty) => Some(ty.clone()),
            dict::SpineArg::Value(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    op.results(&types)?;
    Some((op, types, *operand))
}

pub(super) fn run_rw(
    module: &Module,
    view: &TypeView<'_>,
    head: ExprId,
    spine: &[dict::SpineArg],
) -> Option<(ExprId, BinderId, ExprId)> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    if name != "$ghc-prim$GHC.Magic$runRW#"
        || module.reference(head) != Some(h2r_core_ir::Ref::Global)
    {
        return None;
    }
    let [
        dict::SpineArg::Type(_),
        dict::SpineArg::Type(_),
        dict::SpineArg::Value(lambda),
    ] = spine
    else {
        return None;
    };
    let Expr::Lam { binder, body } = module.expr(*lambda) else {
        return None;
    };
    let state = view.binder_ty(*binder);
    (module.binder(*binder).kind == BinderKind::Id
        && primitive::is_state(state)
        && state.args()[0].is_tycon(primitive::REAL_WORLD))
    .then_some((*lambda, *binder, *body))
}

fn primitive_operation(
    prim: primitive::Prim,
    type_arguments: Vec<Ty>,
    arguments: Vec<ValueId>,
) -> Operation {
    match prim {
        primitive::Prim::Int(op) => Operation::IntBinary { op, arguments },
        primitive::Prim::Char(op) => Operation::CharCompare { op, arguments },
        primitive::Prim::Ord => Operation::OrdChar(arguments[0]),
        primitive::Prim::Chr => Operation::ChrChar(arguments[0]),
        primitive::Prim::Word(op) => Operation::WordCompare { op, arguments },
        primitive::Prim::IntToWord => Operation::IntToWord(arguments[0]),
        primitive::Prim::Negate => Operation::NegateInt(arguments[0]),
        primitive::Prim::WordBinary(op) => Operation::WordBinary { op, arguments },
        primitive::Prim::WordToInt => Operation::WordToInt(arguments[0]),
        primitive::Prim::IndexChar => Operation::IndexCharAddr { arguments },
        primitive::Prim::PlusAddr => Operation::PlusAddr { arguments },
        primitive::Prim::Machine(op) => Operation::Machine {
            op,
            type_arguments,
            arguments,
        },
    }
}

fn primitive_rule(prim: primitive::Prim) -> Rule {
    match prim {
        primitive::Prim::Int(_) => Rule::IntBinary,
        primitive::Prim::Char(_) => Rule::CharCompare,
        primitive::Prim::Ord => Rule::OrdChar,
        primitive::Prim::Chr => Rule::ChrChar,
        primitive::Prim::Word(_) => Rule::WordCompare,
        primitive::Prim::IntToWord => Rule::IntToWord,
        primitive::Prim::Negate => Rule::NegateInt,
        primitive::Prim::WordBinary(_) => Rule::WordBinary,
        primitive::Prim::WordToInt => Rule::WordToInt,
        primitive::Prim::IndexChar => Rule::IndexCharAddr,
        primitive::Prim::PlusAddr => Rule::PlusAddr,
        primitive::Prim::Machine(_) => Rule::Machine,
    }
}

fn literal_operation(ty: &Ty, lit: &h2r_core_ir::Lit) -> Result<(Operation, Rule), String> {
    if primitive::is_addr(ty) {
        Ok((
            Operation::AddrLiteral(lit.string_bytes()?),
            Rule::AddrLiteral,
        ))
    } else {
        Ok((Operation::Literal(lit.clone()), Rule::Literal))
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
        detail: None,
    };
    let origin = |rule| Origin {
        module: context.module_index,
        source: Source::Expr(source),
        rule,
    };
    let mut instructions = Vec::new();
    let mut locals = locals.clone();
    // Preserve executable scrutinees and implemented calls. Demand evidence
    // alone still yields analysis-only Diverge, which emission refuses.
    let executable_empty = if let Expr::Case { scrut, alts, .. } = module.expr(source) {
        alts.is_empty()
            && (module
                .resolve(*scrut)
                .is_some_and(|b| matches!(module.binding(b).site, BindSite::Top))
                || external_spine(context, *scrut).is_some()
                || world_spine(context, *scrut))
    } else {
        false
    };
    if let Some(divergent) = divergent_spine(context, source, ty)
        && external_spine(context, source).is_none()
        && !executable_empty
    {
        blocks[id.0 as usize] = Block {
            id,
            params: context.params.to_vec(),
            instructions: Vec::new(),
            terminator: Terminator {
                exit: Exit::Diverge {
                    name: divergent.name,
                    ty: ty.clone(),
                },
                origin: origin(Rule::Diverge),
            },
        };
        return Ok(id);
    }
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
        && !executable_empty
        && data::carrier(&world, view.binder_ty(*binder)) == Some(data::Carrier::Scalar)
    {
        if !data::supported(&world, ty) {
            return Err(fail("a scalar switch result has no carrier".into()).about(type_head(ty)));
        }
        if !view.ty(*result_ty).alpha_eq(ty) {
            return Err(fail("scalar switch result type mismatch".into()).about(type_head(ty)));
        }
        if alts.iter().any(|a| !a.binders.is_empty()) {
            return Err(fail("a scalar switch alternative binds values".into())
                .about(type_head(view.binder_ty(*binder))));
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
                    let value =
                        primitive::scalar_literal(view.binder_ty(*binder), lit).map_err(&fail)?;
                    if !patterns.insert(value) {
                        return Err(fail("duplicate scalar case alternative".into()));
                    }
                    Some(value)
                }
                h2r_core_ir::AltCon::DataAlt { .. } => {
                    return Err(fail("constructor alternatives are not scalar".into()));
                }
            };
            alternatives.push((pattern, alt.rhs));
        }
        if defaults != 1 {
            return Err(fail(
                "a scalar switch requires exactly one DEFAULT alternative".into(),
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
                ty: shared(view.binder_ty(*binder)),
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
        detail: None,
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
    let mut interleaved = false;
    while let Expr::App { fun, arg } = module.expr(head) {
        if let Expr::Type { ty, .. } = module.expr(*arg) {
            types.push(view.ty(*ty).clone());
        } else {
            interleaved |= !types.is_empty();
            sources.push(*arg);
        }
        head = *fun;
    }
    if !interleaved
        && let Some(fields) = data::unboxed_tuple_worker(&world, module_index, head, ty)
            .map_err(|e| fail(Some(current), &e).about(type_head(ty)))?
    {
        sources.reverse();
        types.reverse();
        let Ty::Con { args, .. } = ty else {
            unreachable!()
        };
        if types.len() != args.len()
            || !types.iter().zip(args).all(|(a, b)| a.alpha_eq(b))
            || sources.len() != fields.len()
        {
            return Err(fail(
                Some(current),
                "unboxed tuple type arguments or saturation mismatch",
            ));
        }
        let mut arguments = Vec::new();
        for (source, field) in sources.into_iter().zip(&fields) {
            // A lifted component is still a lifted value: an unboxed tuple
            // holds what it is given without forcing it, exactly as a
            // constructor field does.
            let value = if data::lifted(&world, field)
                && !matches!(module.expr(source), Expr::Var { .. })
                && !constructed(context, source, field)
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
                ty: shared(ty),
            },
            operation: Operation::MakeUnboxedTuple { arguments },
            origin: origin(Rule::MakeUnboxedTuple),
        });
        return Ok(value);
    }
    if !interleaved
        && let Some(constructor) = data::resolve(&world, module_index, head, ty)
            .map_err(|e| fail(Some(current), &e).about(type_head(ty)))?
    {
        sources.reverse();
        types.reverse();
        let Ty::Con { args, .. } = ty else {
            unreachable!()
        };
        if types.len() != args.len()
            || !types.iter().zip(args).all(|(a, b)| a.alpha_eq(b))
            || sources.len() != constructor.fields.len()
        {
            return Err(fail(
                Some(current),
                "constructor type arguments or saturation mismatch",
            ));
        }
        let mut arguments = Vec::new();
        for (source, field) in sources.into_iter().zip(&constructor.fields) {
            let value = if data::lifted(&world, field)
                && !matches!(module.expr(source), Expr::Var { .. })
                && !constructed(context, source, field)
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
                ty: shared(ty),
            },
            operation: Operation::Construct {
                constructor,
                arguments,
            },
            origin: origin(Rule::Construct),
        });
        return Ok(value);
    }
    if let Expr::Case {
        scrut,
        binder,
        ty: result_ty,
        alts,
        ..
    } = module.expr(current)
        && let Some(known) = dict::known_case(&world, &context.scope(), *scrut, alts)
            .map_err(|reason| fail(Some(current), &reason))?
    {
        if !view.ty(*result_ty).alpha_eq(ty) {
            return Err(fail(Some(current), "known dictionary case result mismatch"));
        }
        let mut dictionaries = context.dictionary_scope.clone();
        dictionaries.insert(*binder, known.dictionary.clone());
        let mut fields = context.field_scope.clone();
        for (field, selector) in known.fields {
            fields.insert(field, (known.dictionary.clone(), selector));
        }
        let nested = BodyContext {
            dictionary_scope: &dictionaries,
            field_scope: &fields,
            ..*context
        };
        return lower_value(&nested, alts[0].rhs, ty, locals, instructions, blocks);
    }
    let unboxed_tuple = match module.expr(current) {
        Expr::Case { binder, alts, .. } if !alts.is_empty() => {
            data::unboxed_tuple_constructor(&world, view.binder_ty(*binder))
                .map_err(|e| fail(Some(current), &e).about(type_head(view.binder_ty(*binder))))?
        }
        _ => None,
    };
    let value = match module.expr(current) {
        Expr::Case {
            scrut,
            binder,
            alts,
            ..
        } if alts.is_empty() && divergent_spine(context, current, ty).is_some() => {
            let operand_ty = view.binder_ty(*binder);
            let scrutinee = lower_value(context, *scrut, operand_ty, locals, instructions, blocks)?;
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
                },
                operation: Operation::EmptyCase { scrutinee },
                origin: origin(Rule::EmptyCase),
            });
            value
        }
        Expr::Case { alts, .. } if alts.is_empty() => {
            return Err(fail(
                Some(current),
                "empty case scrutinee lacks supported non-return evidence",
            ));
        }
        Expr::Lit(lit) => {
            let (operation, rule) =
                literal_operation(ty, lit).map_err(|reason| fail(Some(current), &reason))?;
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
                },
                operation,
                origin: origin(rule),
            });
            value
        }
        Expr::Var { name, .. } if module.reference(current) == Some(h2r_core_ir::Ref::Global) => {
            let modules = modules
                .ok_or_else(|| fail(Some(current), "external references require a loaded world"))?;
            let (target_module, binder) = linkage::imported_top(&world, name)
                .map_err(|reason| fail(Some(current), &reason).about(name.clone()))?;
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
                    ty: shared(ty),
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
            if let Some(reference) = context.dictionary_scope.get(&binder) {
                let reference_ty = dict::reference_type(&world, reference)
                    .map_err(|reason| fail(Some(current), &reason))?;
                if !reference_ty.alpha_eq(ty) {
                    return Err(fail(Some(current), "dictionary reference type mismatch"));
                }
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(ty),
                    },
                    operation: reference_operation(reference),
                    origin: origin(Rule::ResolveInstance),
                });
                return Ok(value);
            }
            if context.field_scope.contains_key(&binder) {
                let resolved = dict::call_target(&world, &context.scope(), current, &[])
                    .map_err(|reason| named(module, current, fail(Some(current), &reason)))?
                    .ok_or_else(|| fail(Some(current), "a known dictionary field has no method"))?;
                if !resolved.arguments.is_empty() || !resolved.signature.alpha_eq(ty) {
                    return Err(fail(Some(current), "method reference type mismatch"));
                }
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(ty),
                    },
                    operation: reference_operation(&resolved.reference),
                    origin: origin(Rule::ResolveMethod),
                });
                return Ok(value);
            }
            if let Some((_, function)) = local_function(module, view, context.functions, current)
                .map_err(|reason| fail(Some(current), &reason))?
            {
                return local_closure(context, function, current, ty, locals, instructions);
            }
            if let Some(value) = locals.get(&binder) {
                *value
            } else if matches!(module.binding(binder).site, BindSite::Top) {
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(ty),
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
        Expr::Cast {
            expr,
            from,
            to,
            role,
        } => {
            // A coercion has no runtime content: this evaluates exactly as the
            // cast expression does. What changes is the type, so erasing the
            // cast is sound here only when both sides are held the same way —
            // the NIR is typed, and a value read at the wrong carrier is a
            // miscompile. The coercion's own kind is the evidence for that;
            // a dump that carries none leaves nothing to decide on.
            let (Some(from), Some(to), Some(role)) = (from, to, role) else {
                return Err(fail(
                    Some(current),
                    "casts need source and target type evidence",
                ));
            };
            let source_ty = view.ty(*from).clone();
            let target_ty = view.ty(*to);
            if !target_ty.alpha_eq(ty) {
                return Err(fail(
                    Some(current),
                    "cast target differs from the expression's own type",
                ));
            }
            let Some(carrier) = data::carrier(&world, &source_ty) else {
                return Err(fail(Some(current), "cast source has no supported carrier")
                    .about(type_head(&source_ty)));
            };
            if data::carrier(&world, target_ty) != Some(carrier) {
                return Err(
                    fail(Some(current), "a cast must not change the carrier").about(format!(
                        "{} to {} ({role})",
                        type_head(&source_ty),
                        type_head(target_ty)
                    )),
                );
            }
            let inner = lower_value(context, *expr, &source_ty, locals, instructions, blocks)?;
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
                },
                operation: Operation::Move(inner),
                origin: origin(Rule::EraseCast),
            });
            value
        }
        Expr::App { arg, .. }
            if !matches!(module.expr(*arg), Expr::Type { .. })
                && unpacker_spine(context, current).is_some() =>
        {
            let (unpacker, literal, tail_source) =
                unpacker_spine(context, current).expect("matched spine");
            if !ty.alpha_eq(&strings::string_ty()) {
                return Err(fail(Some(current), "a string literal unpacks to [Char]"));
            }
            let bytes = strings::address_literal(&world, module_index, literal)
                .ok_or_else(|| fail(Some(literal), "string unpacker needs a literal address"))?
                .string_bytes()
                .map_err(|reason| fail(Some(literal), &reason))?;
            // Decode here so a malformed literal is refused before anything is
            // built; the emitted code walks the same bytes at run time.
            strings::decode(&bytes, unpacker.encoding).map_err(|r| fail(Some(literal), &r))?;
            let (nil, cons, character) =
                data::string_layouts(&world).map_err(|r| fail(Some(current), &r))?;
            let tail = tail_source
                .map(|source| {
                    let list = strings::string_ty();
                    match module.expr(source) {
                        Expr::App { .. } if constructed(context, source, &list) => {
                            lower_value(context, source, &list, locals, instructions, blocks)
                        }
                        Expr::App { .. } | Expr::Case { .. } | Expr::Let { .. } => {
                            lower_region(context, source, &list, locals, instructions, blocks, true)
                        }
                        _ => lower_value(context, source, &list, locals, instructions, blocks),
                    }
                })
                .transpose()?;
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
                },
                operation: Operation::UnpackString(Box::new(UnpackString {
                    bytes,
                    encoding: unpacker.encoding,
                    tail,
                    nil,
                    cons,
                    character,
                })),
                origin: origin(Rule::UnpackString),
            });
            value
        }
        Expr::App { arg, .. }
            if !matches!(module.expr(*arg), Expr::Type { .. })
                && external_spine(context, current).is_some() =>
        {
            let (entry, type_arguments, argument_sources) =
                external_spine(context, current).expect("matched spine");
            let signature = entry
                .signature(&type_arguments)
                .ok_or_else(|| fail(Some(current), "external call type arguments mismatch"))?;
            let element = entry.element(&type_arguments);
            if !linkage::closed_type(&signature) {
                return Err(fail(
                    Some(current),
                    "external call requires closed structured types",
                ));
            }
            let lists = element
                .as_ref()
                .map(|element| data::list_layouts(&world, element))
                .transpose()
                .map_err(|reason| fail(Some(current), &reason))?;
            let list_layouts = || {
                lists
                    .clone()
                    .ok_or_else(|| fail(Some(current), "external call has no list layouts"))
            };
            let (dictionaries, argument_sources) =
                argument_sources.split_at(entry.dictionary_arity());
            let equality = match (entry, dictionaries) {
                (external::External::EqString, []) => Some(external::Equality::Char),
                (external::External::Elem | external::External::IsPrefixOf, [dictionary]) => Some(
                    element
                        .as_ref()
                        .and_then(|element| external::equality(module, *dictionary, element))
                        .ok_or_else(|| {
                            named(
                                module,
                                *dictionary,
                                fail(
                                    Some(*dictionary),
                                    "an Eq dictionary this backend does not implement",
                                ),
                            )
                        })?,
                ),
                (
                    external::External::Append
                    | external::External::ErrorWithoutStackTrace
                    | external::External::Error
                    | external::External::CompareString
                    | external::External::DataToTag
                    | external::External::PointerEquality
                    | external::External::TagToEnum
                    | external::External::Map
                    | external::External::Filter
                    | external::External::TakeWhile
                    | external::External::DropWhile
                    | external::External::Reverse
                    | external::External::ReverseOnto
                    | external::External::Length
                    | external::External::ConsAppend
                    | external::External::Lazy,
                    [],
                ) => None,
                _ => return Err(fail(Some(current), "external call dictionary mismatch")),
            };
            let mut remaining = &signature;
            let mut arguments = Vec::new();
            for &source in argument_sources {
                let Ty::Fun { arg, res, .. } = remaining else {
                    return Err(fail(Some(current), "external call lacks a value arrow"));
                };
                // Lifted arguments stay thunks; each implemented operation
                // decides when they are demanded (append versus error).
                let value = match module.expr(source) {
                    Expr::App { .. }
                    | Expr::Case { .. }
                    | Expr::Let { .. }
                    | Expr::Lam { .. }
                    | Expr::Cast { .. }
                        if data::lifted(&world, arg) && !constructed(context, source, arg) =>
                    {
                        lower_region(context, source, arg, locals, instructions, blocks, true)?
                    }
                    _ => lower_value(context, source, arg, locals, instructions, blocks)?,
                };
                arguments.push(value);
                remaining = res;
            }
            if !remaining.alpha_eq(ty) {
                return Err(fail(Some(current), "external call result type mismatch"));
            }
            let list_function = match entry.list_function() {
                Some(function) => {
                    let (nil, cons) = list_layouts()?;
                    let mapped = match function {
                        ListOp::Map => Some(
                            data::list_layouts(&world, &type_arguments[1])
                                .map_err(|reason| fail(Some(current), &reason))?,
                        ),
                        _ => None,
                    };
                    let truth = if function.takes_predicate() {
                        Some(
                            data::bool_layouts(&world)
                                .map_err(|reason| fail(Some(current), &reason))?,
                        )
                    } else {
                        None
                    };
                    Some(ListFunction {
                        function,
                        arguments: arguments.clone(),
                        nil,
                        cons,
                        mapped,
                        truth,
                    })
                }
                None => None,
            };
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
                },
                operation: match list_function {
                    Some(list) => Operation::ListFunction(Box::new(list)),
                    None => match (entry, entry.predicate(), equality) {
                        (external::External::Lazy, None, None) => Operation::Move(arguments[0]),
                    (external::External::Error, None, None) => {
                        let layouts = data::call_stack_layouts(&world)
                            .map_err(|reason| fail(Some(current), &reason))?;
                        Operation::RaiseCallStackError(Box::new(CallStackError {
                            message: arguments[1],
                            stack: arguments[0],
                            layouts,
                        }))
                    }
                        (external::External::Append, None, None) => {
                            let (nil, cons) = list_layouts()?;
                            Operation::AppendList {
                                left: arguments[0],
                                right: arguments[1],
                                nil,
                                cons,
                            }
                        }
                        (external::External::DataToTag, None, None) => {
                            let constructors = data::represented(&world, &type_arguments[0])
                                .filter(|ty| data::carrier(&world, ty) == Some(data::Carrier::Data))
                                .ok_or_else(|| {
                                    fail(
                                        Some(current),
                                        "dataToTag# requires an algebraic data carrier",
                                    )
                                    .about(type_head(&type_arguments[0]))
                                })
                                .and_then(|ty| {
                                    data::family(&world, &ty)
                                        .map_err(|reason| fail(Some(current), &reason))
                                })?;
                            Operation::DataToTag {
                                value: arguments[0],
                                constructors,
                            }
                        }
                        (external::External::TagToEnum, None, None) => {
                            let constructors = data::represented(&world, &type_arguments[0])
                                .filter(|ty| data::carrier(&world, ty) == Some(data::Carrier::Data))
                                .ok_or_else(|| {
                                    fail(
                                        Some(current),
                                        "tagToEnum# requires an algebraic data carrier",
                                    )
                                    .about(type_head(&type_arguments[0]))
                                })
                                .and_then(|ty| {
                                    data::family(&world, &ty)
                                        .map_err(|reason| fail(Some(current), &reason))
                                })?;
                            if constructors.iter().any(|c| !c.fields.is_empty()) {
                                return Err(fail(
                                    Some(current),
                                    "tagToEnum# requires an enumeration type",
                                )
                                .about(type_head(&type_arguments[0])));
                            }
                            Operation::TagToEnum {
                                tag: arguments[0],
                                constructors,
                            }
                        }
                        (external::External::PointerEquality, None, None) => {
                            if !data::same_heap_carrier(
                                &world,
                                &type_arguments[2],
                                &type_arguments[3],
                            ) {
                                return Err(fail(
                                    Some(current),
                                    "pointer equality requires one boxed Int or algebraic data carrier",
                                )
                                .about(type_head(&type_arguments[2])));
                            }
                            Operation::PointerEquality {
                                left: arguments[0],
                                right: arguments[1],
                            }
                        }
                        (external::External::ErrorWithoutStackTrace, None, None) => {
                            Operation::RaiseError {
                                message: arguments[0],
                            }
                        }
                        (external::External::CompareString, None, None) => {
                            let (nil, cons) = list_layouts()?;
                            let (_, _, character) = data::string_layouts(&world)
                                .map_err(|reason| fail(Some(current), &reason))?;
                            let (lt, eq, gt) = data::ordering_layouts(&world)
                                .map_err(|reason| fail(Some(current), &reason))?;
                            Operation::CompareStrings(Box::new(CompareStrings {
                                left: arguments[0],
                                right: arguments[1],
                                nil,
                                cons,
                                character,
                                lt,
                                eq,
                                gt,
                            }))
                        }
                        (_, Some(predicate), Some(equality)) => {
                            let (nil, cons) = list_layouts()?;
                            let (_, _, character) = data::string_layouts(&world)
                                .map_err(|reason| fail(Some(current), &reason))?;
                            let (false_, true_) = data::bool_layouts(&world)
                                .map_err(|reason| fail(Some(current), &reason))?;
                            Operation::ListPredicate(Box::new(ListPredicate {
                                predicate,
                                equality,
                                left: arguments[0],
                                right: arguments[1],
                                nil,
                                cons,
                                character,
                                false_,
                                true_,
                            }))
                        }
                        _ => return Err(fail(Some(current), "external call dictionary mismatch")),
                    },
                },
                origin: origin(match entry {
                    external::External::Append => Rule::AppendList,
                    external::External::ErrorWithoutStackTrace | external::External::Error => {
                        Rule::RaiseError
                    }
                    external::External::EqString
                    | external::External::Elem
                    | external::External::IsPrefixOf => Rule::ListPredicate,
                    external::External::CompareString => Rule::CompareStrings,
                    external::External::DataToTag => Rule::DataToTag,
                    external::External::TagToEnum => Rule::TagToEnum,
                    external::External::PointerEquality => Rule::PointerEquality,
                    external::External::Map
                    | external::External::Filter
                    | external::External::TakeWhile
                    | external::External::DropWhile
                    | external::External::Reverse
                    | external::External::ReverseOnto
                    | external::External::Length
                    | external::External::ConsAppend => Rule::ListFunction,
                    external::External::Lazy => Rule::MagicLazy,
                }),
            });
            value
        }
        Expr::App { .. } if applies_value(module, current) => {
            let mut head = current;
            let mut spine = Vec::new();
            while let Expr::App { fun, arg } = module.expr(head) {
                spine.push(match module.expr(*arg) {
                    Expr::Type { ty, .. } => dict::SpineArg::Type(view.ty(*ty).clone()),
                    _ => dict::SpineArg::Value(*arg),
                });
                head = *fun;
            }
            spine.reverse();
            let leading = spine
                .iter()
                .take_while(|argument| matches!(argument, dict::SpineArg::Type(_)))
                .count();
            let type_arguments: Vec<Ty> = spine[..leading]
                .iter()
                .filter_map(|argument| match argument {
                    dict::SpineArg::Type(ty) => Some(ty.clone()),
                    dict::SpineArg::Value(_) => None,
                })
                .collect();
            let argument_sources: Vec<ExprId> = spine[leading..]
                .iter()
                .filter_map(|argument| match argument {
                    dict::SpineArg::Value(source) => Some(*source),
                    dict::SpineArg::Type(_) => None,
                })
                .collect();
            let interleaved = leading + argument_sources.len() != spine.len();
            if let Some((op, types, _)) = raise(module, head, &spine) {
                if !types.last().is_some_and(|result| result.alpha_eq(ty))
                    || !data::supported(&world, ty)
                {
                    return Err(
                        fail(Some(current), "raise# result type mismatch").about(type_head(ty))
                    );
                }
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(ty),
                    },
                    operation: Operation::Machine {
                        op,
                        type_arguments: types,
                        arguments: Vec::new(),
                    },
                    origin: origin(Rule::Machine),
                });
                return Ok(value);
            }
            if let Some((_, state, body)) = run_rw(module, view, head, &spine) {
                let token = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: token,
                        ty: shared(view.binder_ty(state)),
                    },
                    operation: Operation::Machine {
                        op: Machine::RealWorld,
                        type_arguments: Vec::new(),
                        arguments: Vec::new(),
                    },
                    origin: origin(Rule::RunRW),
                });
                let previous = locals.insert(state, token);
                let result = lower_value(context, body, ty, locals, instructions, blocks);
                match previous {
                    Some(value) => locals.insert(state, value),
                    None => locals.remove(&state),
                };
                return result;
            }
            if let Some((constructor, _)) =
                dict::constructor_method(&world, &context.scope(), head, &spine, ty)
                    .map_err(|reason| fail(Some(current), &reason))?
            {
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(ty),
                    },
                    operation: Operation::Construct {
                        constructor,
                        arguments: Vec::new(),
                    },
                    origin: origin(Rule::ResolveMethod),
                });
                return Ok(value);
            }
            let primitive = primitive::resolve(module, head);
            let constructor = boxed::resolves(module, head);
            let local = local_function(module, view, context.functions, head)
                .map_err(|reason| fail(Some(head), &reason))?;
            let indirect = module.resolve(head).filter(|b| locals.contains_key(b));
            // The asserted signature of the head, when it is not a binding this
            // world can link: a primop's own GHC type, or `I#`'s worker type.
            let primitive_ty = match primitive {
                _ if constructor => boxed::signature(),
                Some(prim) => prim
                    .signature_at(&world, &type_arguments, ty)
                    .map_err(|reason| fail(Some(current), &reason))?,
                None => primitive::signature(),
            };
            // A cast names its own type, so an application whose head is one
            // can still be lowered: the head is a value of the cast's target
            // type and the call is indirect, exactly as through a parameter.
            let cast_head = match module.expr(head) {
                Expr::Cast { to: Some(to), .. } => Some(view.ty(*to).clone()),
                _ => None,
            };
            let target = if cast_head.is_some()
                || primitive.is_some()
                || constructor
                || local.is_some()
                || indirect.is_some()
            {
                if interleaved && (primitive.is_some() || constructor) {
                    return Err(fail(
                        Some(head),
                        "type arguments must precede value arguments",
                    ));
                }
                None
            } else {
                Some(
                    dict::call_target(&context.world(), &context.scope(), head, &spine)
                        .map_err(|reason| named(module, head, fail(Some(head), &reason)))?
                        .ok_or_else(|| {
                            named(
                                module,
                                head,
                                fail(Some(head), "application requires a top-level binding"),
                            )
                        })?,
                )
            };
            let head_ty = cast_head.as_ref().unwrap_or_else(|| {
                indirect.map_or_else(
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
                )
            });
            let instantiated = match &target {
                // Already instantiated at the instance's type arguments.
                Some(resolved) => resolved.signature.clone(),
                None if primitive.is_some() => primitive_ty.clone(),
                None => {
                    positional(head_ty, &spine).map_err(|reason| fail(Some(current), &reason))?
                }
            };
            let typed = spine
                .iter()
                .any(|argument| matches!(argument, dict::SpineArg::Type(_)));
            let mut signature = &instantiated;
            let argument_sources = match &target {
                Some(resolved) => resolved.arguments.clone(),
                None => argument_sources,
            };
            let arity = if cast_head.is_some() {
                None
            } else {
                local.map_or_else(
                    || {
                        target.as_ref().map_or_else(
                            || Some(if constructor { 1 } else { primitive?.arity() }),
                            |resolved| Some(resolved.arity as u32),
                        )
                    },
                    |(_, function)| Some(function.arity as u32),
                )
            };
            let apply = cast_head.is_some()
                || indirect.is_some()
                || target.as_ref().is_some_and(|resolved| resolved.cast)
                || arity != Some(argument_sources.len() as u32);
            if apply {
                // Four different things end up here, and saying which one is
                // the difference between "this call is unsaturated" and "this
                // type has no carrier" — the second is the usual answer, and
                // it names a type rather than a call.
                if primitive.is_some() {
                    return Err(fail(
                        Some(current),
                        "a primop must be applied to exactly its own arguments",
                    ));
                }
                if constructor {
                    return Err(fail(
                        Some(current),
                        "a constructor must be applied to exactly its own fields",
                    ));
                }
                if target.is_none()
                    && typed
                    && data::carrier(&world, head_ty) != data::carrier(&world, &instantiated)
                {
                    return Err(fail(
                        Some(current),
                        "an indirect call's instantiation changes its carrier",
                    ));
                }
                if !data::function(&world, head_ty) {
                    return Err(fail(
                        Some(current),
                        "partial application needs a carried function type",
                    )
                    .about(unsupported_component(&world, head_ty)));
                }
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
                        ty: shared(ty),
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
            let strict_carried = |ty: &Ty| data::supported(&world, ty) && !data::lifted(&world, ty);
            let mut arguments = Vec::new();
            for source in argument_sources {
                let Ty::Fun { arg, res, .. } = signature else {
                    return Err(fail(Some(current), "direct call lacks a value arrow"));
                };
                let value = match module.expr(source) {
                    Expr::App { .. } | Expr::Cast { .. } if strict_carried(arg) => {
                        lower_value(context, source, arg, locals, instructions, blocks)?
                    }
                    Expr::Case { .. } | Expr::Let { .. } if strict_carried(arg) => {
                        lower_region(context, source, arg, locals, instructions, blocks, false)?
                    }
                    Expr::App { .. } | Expr::Lam { .. } | Expr::Cast { .. }
                        if constructed(context, source, arg) =>
                    {
                        lower_value(context, source, arg, locals, instructions, blocks)?
                    }
                    Expr::App { .. }
                    | Expr::Case { .. }
                    | Expr::Let { .. }
                    | Expr::Lam { .. }
                    | Expr::Cast { .. }
                        if data::lifted(&world, arg) =>
                    {
                        lower_region(context, source, arg, locals, instructions, blocks, true)?
                    }
                    Expr::Lit(lit) => {
                        let (operation, rule) = literal_operation(arg, lit)
                            .map_err(|reason| fail(Some(source), &reason))?;
                        let value = fresh_value(context);
                        instructions.push(Instruction {
                            result: Value {
                                id: value,
                                ty: shared(arg),
                            },
                            operation,
                            origin: Origin {
                                module: module_index,
                                source: Source::Expr(source),
                                rule,
                            },
                        });
                        value
                    }
                    Expr::Var { .. } => {
                        if module
                            .resolve(source)
                            .is_some_and(|b| context.functions.contains_key(&b))
                            || data::unboxed_tuple_worker(&world, module_index, source, arg)
                                .map_err(|e| fail(Some(source), &e))?
                                .is_some()
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
                        } else if let Some(reference) = module
                            .resolve(source)
                            .and_then(|binder| context.dictionary_scope.get(&binder))
                        {
                            let reference_ty = dict::reference_type(&world, reference)
                                .map_err(|reason| fail(Some(source), &reason))?;
                            if !arg.alpha_eq(&reference_ty) {
                                return Err(fail(
                                    Some(source),
                                    "dictionary argument type mismatch",
                                ));
                            }
                            let value = fresh_value(context);
                            instructions.push(Instruction {
                                result: Value {
                                    id: value,
                                    ty: shared(arg),
                                },
                                operation: reference_operation(reference),
                                origin: Origin {
                                    module: module_index,
                                    source: Source::Expr(source),
                                    rule: Rule::ResolveInstance,
                                },
                            });
                            value
                        } else {
                            let (argument_module, argument_binder, argument_ty) =
                                instantiate::target(&world, source).map_err(|reason| {
                                    named(module, source, fail(Some(source), &reason))
                                })?;
                            if !linkage::closed_type(argument_ty) || !arg.alpha_eq(argument_ty) {
                                return Err(fail(Some(source), "top-level argument type mismatch"));
                            }
                            let value = fresh_value(context);
                            instructions.push(Instruction {
                                result: Value {
                                    id: value,
                                    ty: shared(arg),
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
                            ty: shared(&instantiated),
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
                (true, None) if local.is_some() => {
                    let (_, function) = local.expect("matched local head");
                    Some(local_closure(
                        context,
                        function,
                        head,
                        &instantiated,
                        locals,
                        instructions,
                    )?)
                }
                (true, None) => {
                    let callee = lower_value(context, head, head_ty, locals, instructions, blocks)?;
                    if !typed {
                        Some(callee)
                    } else {
                        let value = fresh_value(context);
                        instructions.push(Instruction {
                            result: Value {
                                id: value,
                                ty: shared(&instantiated),
                            },
                            operation: Operation::Move(callee),
                            origin: Origin {
                                module: module_index,
                                source: Source::Expr(head),
                                rule: Rule::InstantiateValue,
                            },
                        });
                        Some(value)
                    }
                }
            };
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
                },
                operation: if let Some(callee) = callee {
                    Operation::Apply { callee, arguments }
                } else if constructor {
                    Operation::BoxInt(arguments[0])
                } else if let Some(prim) = primitive {
                    primitive_operation(prim, type_arguments.clone(), arguments)
                } else if let Some((_, function)) = local {
                    let mut actual = function
                        .captures
                        .iter()
                        .map(|b| {
                            locals.get(b).copied().ok_or_else(|| {
                                fail(Some(current), "local function capture out of scope")
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    actual.extend(arguments);
                    Operation::CallLocal {
                        target: function.target,
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
                } else if let Some(prim) = primitive {
                    primitive_rule(prim)
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
            if let Some((binder, function)) = local_function(module, view, context.functions, head)
                .map_err(|reason| fail(Some(current), &reason))?
            {
                let spine: Vec<_> = arguments
                    .iter()
                    .cloned()
                    .map(dict::SpineArg::Type)
                    .collect();
                let expected = positional(view.binder_ty(binder), &spine)
                    .map_err(|reason| fail(Some(current), &reason))?;
                if !same_scoped_type(ty, &expected, type_scope) {
                    return Err(fail(
                        Some(current),
                        "local type application result mismatch",
                    ));
                }
                return local_closure(context, function, current, ty, locals, instructions);
            }
            if let Some(binder) = module.resolve(head)
                && let Some(polymorphic) = locals.get(&binder).copied()
            {
                let expected = instantiate::apply(view.binder_ty(binder), &arguments)
                    .map_err(|reason| fail(Some(current), &reason))?;
                if !same_scoped_type(ty, &expected, type_scope)
                    || data::carrier(&world, ty) != data::carrier(&world, view.binder_ty(binder))
                    || !data::supported(&world, ty)
                {
                    return Err(fail(
                        Some(current),
                        "a local value's instantiation changes its type or carrier",
                    ));
                }
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(ty),
                    },
                    operation: Operation::Move(polymorphic),
                    origin: origin(Rule::InstantiateValue),
                });
                return Ok(value);
            }
            let (target_module, binder, head_ty) = instantiate::target(&world, head)
                .map_err(|reason| named(module, head, fail(Some(head), &reason)))?;
            let result_ty = instantiate::apply(head_ty, &arguments)
                .map_err(|reason| fail(Some(current), &reason))?;
            if !linkage::closed_type(ty) || !ty.alpha_eq(&result_ty) {
                return Err(fail(Some(current), "type application result mismatch"));
            }
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
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
                && bind
                    .pairs
                    .iter()
                    .all(|pair| function_pair(module, pair.binder, pair.rhs))
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
            if bind.recursive {
                return lower_recursive_group(context, current, ty, locals, instructions, blocks);
            }
            let [pair] = bind.pairs.as_slice() else {
                return Err(fail(
                    Some(current),
                    "a let group binds several values at once",
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
            // Three different things used to share one sentence here, which
            // made the ranking unable to say which of them the live set
            // actually contains. They are separate refusals now.
            if bind.recursive {
                return Err(
                    fail(Some(current), "a recursive value binding").about(type_head(binding_ty))
                );
            }
            if module.binder(pair.binder).is_join_point == Some(true) {
                return Err(fail(Some(current), "a join point bound as a value")
                    .about(type_head(binding_ty)));
            }
            if !data::supported(&world, binding_ty) {
                return Err(fail(
                    Some(current),
                    "a let binds a value whose type has no carrier",
                )
                .about(type_head(binding_ty)));
            }
            // A `let` at an unboxed type is not a thunk. Core only admits one
            // whose right-hand side is ok for speculation, and it is evaluated
            // where it stands, so binding it eagerly is what it means.
            let delayed = data::lifted(&world, binding_ty);
            let rhs = match module.expr(pair.rhs) {
                Expr::Var { .. } => {
                    lower_value(context, pair.rhs, binding_ty, locals, instructions, blocks)?
                }
                // A strict scalar computation is emitted where it stands; only
                // its own control flow needs a region of its own.
                _ if !delayed
                    && !matches!(module.expr(pair.rhs), Expr::Case { .. } | Expr::Let { .. }) =>
                {
                    lower_value(context, pair.rhs, binding_ty, locals, instructions, blocks)?
                }
                _ if delayed && constructed(context, pair.rhs, binding_ty) => {
                    lower_value(context, pair.rhs, binding_ty, locals, instructions, blocks)?
                }
                _ => lower_region(
                    context,
                    pair.rhs,
                    binding_ty,
                    locals,
                    instructions,
                    blocks,
                    delayed,
                )?,
            };
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(binding_ty),
                },
                operation: Operation::Move(rhs),
                origin: origin(if delayed {
                    Rule::LazyBinding
                } else {
                    Rule::StrictBinding
                }),
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
        // A `case` on an unboxed tuple is no control flow: the family has one
        // constructor, nothing is in a box and nothing is forced. It names the
        // components and carries straight on into the body.
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } if unboxed_tuple.is_some() => {
            let Some((constructor, fields)) = unboxed_tuple else {
                unreachable!("guarded by is_some")
            };
            if !view.ty(*result_ty).alpha_eq(ty) || !data::supported(&world, ty) {
                return Err(
                    fail(Some(current), "unboxed tuple case result mismatch").about(type_head(ty))
                );
            }
            let [alt] = alts.as_slice() else {
                return Err(fail(
                    Some(current),
                    "an unboxed tuple case has exactly one alternative",
                ));
            };
            // Two forms, and GHC emits both. `DEFAULT` names the tuple in
            // the case binder and nothing else; the constructor pattern also
            // names the components. Neither is a branch, and at `-O0` an
            // unboxed tuple case is usually the first wrapping the second.
            let components: &[BinderId] = match &alt.con {
                h2r_core_ir::AltCon::DataAlt { name, tag, .. }
                    if *name == constructor && *tag == 1 =>
                {
                    &alt.binders
                }
                h2r_core_ir::AltCon::Default if alt.binders.is_empty() => &[],
                _ => {
                    return Err(fail(
                        Some(current),
                        "an unboxed tuple case matches its one constructor or binds nothing",
                    ));
                }
            };
            if !components.is_empty()
                && (components.len() != fields.len()
                    || fields
                        .iter()
                        .zip(components)
                        .any(|(t, b)| !t.alpha_eq(view.binder_ty(*b))))
            {
                return Err(fail(
                    Some(current),
                    "unboxed tuple case field layout mismatch",
                ));
            }
            let tuple = lower_value(
                context,
                *scrut,
                view.binder_ty(*binder),
                locals,
                instructions,
                blocks,
            )?;
            // The case binder names the tuple itself and the alternative's
            // binders name its components. Both are already evaluated, so
            // neither naming is a forcing.
            //
            // The binder is bound even when the source never reads it, because
            // it is what marks where the scrutinee's instructions end: a
            // nullary unboxed tuple has no components to project and would
            // otherwise leave the boundary unstated.
            let mut inner = locals.clone();
            let named = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: named,
                    ty: shared(view.binder_ty(*binder)),
                },
                operation: Operation::Move(tuple),
                origin: origin(Rule::UnboxedTupleField),
            });
            inner.insert(*binder, named);
            for (index, (component, field)) in components.iter().zip(&fields).enumerate() {
                let value = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: value,
                        ty: shared(field),
                    },
                    operation: Operation::UnboxedTupleField {
                        tuple: named,
                        index,
                    },
                    origin: origin(Rule::UnboxedTupleField),
                });
                inner.insert(*component, value);
            }
            lower_value(context, alt.rhs, ty, &mut inner, instructions, blocks)?
        }
        Expr::Case {
            scrut,
            binder,
            ty: result_ty,
            alts,
            ..
        } if data::is_data(&world, view.binder_ty(*binder)) => {
            if !view.ty(*result_ty).alpha_eq(ty) || !data::supported(&world, ty) {
                return Err(
                    fail(Some(current), "algebraic case result mismatch").about(type_head(ty))
                );
            }
            let family = data::represented(&world, view.binder_ty(*binder))
                .ok_or_else(|| "a case scrutinee's newtype chain does not end".to_string())
                .and_then(|represented| data::family(&world, &represented))
                .map_err(|e| fail(Some(current), &e).about(type_head(view.binder_ty(*binder))))?;
            let scrutinee = lower_value(
                context,
                *scrut,
                view.binder_ty(*binder),
                locals,
                instructions,
                blocks,
            )?;
            let captures: Vec<_> = captured_locals(module, context.functions, &[current], locals)
                .into_iter()
                .collect();
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
                        ty: shared(view.binder_ty(*b)),
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
            if arms.is_empty() {
                return Err(fail(Some(current), "non-exhaustive algebraic case"));
            }
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(ty),
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
                    ty: shared(&int),
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
            if !data::supported(&world, view.binder_ty(*binder)) {
                return Err(fail(Some(current), "unsupported case scrutinee carrier")
                    .about(type_head(view.binder_ty(*binder))));
            }
            if alts.len() != 1 || !matches!(alts[0].con, h2r_core_ir::AltCon::Default) {
                if !primitive::is_scalar(view.binder_ty(*binder)) {
                    return Err(fail(Some(current), "unsupported case scrutinee carrier")
                        .about(type_head(view.binder_ty(*binder))));
                }
                return lower_region(context, current, ty, locals, instructions, blocks, false);
            }
            let [alt] = alts.as_slice() else {
                return Err(fail(
                    Some(current),
                    "a strict scalar case requires one DEFAULT alternative",
                ));
            };
            let binder_ty = view.binder_ty(*binder);
            let forced = data::lifted(&world, binder_ty);
            if !matches!(alt.con, h2r_core_ir::AltCon::Default)
                || !alt.binders.is_empty()
                || !data::supported(&world, binder_ty)
                || !data::supported(&world, ty)
                || !view.ty(*result_ty).alpha_eq(ty)
            {
                return Err(fail(
                    Some(current),
                    "unsupported strict case type or alternative",
                ));
            }
            let scrutinee =
                if forced && matches!(module.expr(*scrut), Expr::Case { .. } | Expr::Let { .. }) {
                    lower_region(
                        context,
                        *scrut,
                        binder_ty,
                        locals,
                        instructions,
                        blocks,
                        true,
                    )?
                } else {
                    lower_value(context, *scrut, binder_ty, locals, instructions, blocks)?
                };
            let value = fresh_value(context);
            instructions.push(Instruction {
                result: Value {
                    id: value,
                    ty: shared(binder_ty),
                },
                operation: if forced {
                    Operation::Force(scrutinee)
                } else {
                    Operation::Move(scrutinee)
                },
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

pub(super) struct LocalInstance {
    pub subst: Substitution,
    pub ty: Ty,
    pub types: Vec<Ty>,
    pub shape: Vec<(BinderId, bool)>,
}

pub(super) fn positional(ty: &Ty, spine: &[dict::SpineArg]) -> Result<Ty, String> {
    let Some((first, rest)) = spine.split_first() else {
        return Ok(ty.clone());
    };
    match (ty, first) {
        (Ty::ForAll { .. }, dict::SpineArg::Type(argument)) => positional(
            &instantiate::apply(ty, std::slice::from_ref(argument))?,
            rest,
        ),
        (Ty::Fun { mult, arg, res }, dict::SpineArg::Value(_)) => Ok(Ty::Fun {
            mult: mult.clone(),
            arg: arg.clone(),
            res: Box::new(positional(res, rest)?),
        }),
        _ => Err("the spine applies a value where its target quantifies a type".into()),
    }
}

fn lambda_shape(module: &Module, mut rhs: ExprId) -> Vec<(BinderId, bool)> {
    let mut shape = Vec::new();
    while let Expr::Lam { binder, body } = module.expr(rhs) {
        shape.push((*binder, module.binder(*binder).kind == BinderKind::Tyvar));
        rhs = *body;
    }
    let used = shape
        .iter()
        .rposition(|(_, ty)| *ty)
        .map_or(0, |last| last + 1);
    shape.truncate(used);
    shape
}

fn spine_types(
    module: &Module,
    occurrence: ExprId,
    shape: &[(BinderId, bool)],
    read: impl Fn(h2r_core_ir::TyId) -> Ty,
) -> Result<Vec<Ty>, String> {
    let mut types = Vec::new();
    let mut current = occurrence;
    let mut applied = 0;
    for (parent, (_, type_lambda)) in module.ancestors(occurrence).zip(shape) {
        let Expr::App { fun, arg } = module.expr(parent) else {
            break;
        };
        if *fun != current {
            break;
        }
        match (module.expr(*arg), type_lambda) {
            (Expr::Type { ty, .. }, true) => types.push(read(*ty)),
            (Expr::Type { .. }, false) | (_, true) => {
                return Err(
                    "a polymorphic local function is applied out of its lambdas' order".into(),
                );
            }
            (_, false) => {}
        }
        applied += 1;
        current = parent;
    }
    types.extend(
        shape[applied..]
            .iter()
            .filter(|(_, type_lambda)| *type_lambda)
            .map(|_| data::erased_ty()),
    );
    if !types.iter().all(linkage::closed_type) {
        return Err("a polymorphic local function needs closed type arguments at every use".into());
    }
    Ok(types)
}

pub(super) const LOCAL_INSTANCE_BUDGET: usize = 16;

#[derive(Debug, Clone)]
pub(super) struct LocalFunction {
    pub types: Vec<Ty>,
    pub shape: Vec<(BinderId, bool)>,
    pub target: BlockId,
    pub captures: Vec<BinderId>,
    pub arity: usize,
}

pub(super) type LocalFunctions = BTreeMap<BinderId, Vec<LocalFunction>>;

pub(super) fn free_in(
    module: &Module,
    functions: &LocalFunctions,
    roots: &[ExprId],
) -> BTreeSet<BinderId> {
    let mut free = BTreeSet::new();
    for node in roots.iter().flat_map(|root| module.preorder(*root)) {
        if let Expr::Var { .. } = module.expr(node)
            && let Some(binder) = module.resolve(node)
            && free.insert(binder)
            && let Some(instances) = functions.get(&binder)
        {
            free.extend(instances.iter().flat_map(|f| f.captures.iter().copied()));
        }
    }
    free
}

fn captured_locals(
    module: &Module,
    functions: &LocalFunctions,
    roots: &[ExprId],
    locals: &BTreeMap<BinderId, ValueId>,
) -> BTreeMap<BinderId, ValueId> {
    let free = free_in(module, functions, roots);
    locals
        .iter()
        .filter(|(binder, _)| free.contains(binder))
        .map(|(binder, value)| (*binder, *value))
        .collect()
}

fn local_closure(
    context: &BodyContext<'_>,
    function: &LocalFunction,
    source: ExprId,
    ty: &Ty,
    locals: &BTreeMap<BinderId, ValueId>,
    instructions: &mut Vec<Instruction>,
) -> Result<ValueId, LowerError> {
    let arguments = function
        .captures
        .iter()
        .map(|b| {
            locals.get(b).copied().ok_or_else(|| LowerError {
                module: context.module_index,
                owner: context.owner,
                source: Some(source),
                reason: "closure capture out of scope".into(),
                detail: None,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (operation, rule) = if function.arity == 0 {
        (
            Operation::CallLocal {
                target: function.target,
                arguments,
            },
            Rule::CallLocal,
        )
    } else {
        (
            Operation::MakeClosure {
                target: function.target,
                arguments,
            },
            Rule::MakeClosure,
        )
    };
    let value = fresh_value(context);
    instructions.push(Instruction {
        result: Value {
            id: value,
            ty: shared(ty),
        },
        operation,
        origin: Origin {
            module: context.module_index,
            source: Source::Expr(source),
            rule,
        },
    });
    Ok(value)
}

pub(super) fn local_function<'f>(
    module: &Module,
    view: &TypeView<'_>,
    functions: &'f LocalFunctions,
    occurrence: ExprId,
) -> Result<Option<(BinderId, &'f LocalFunction)>, String> {
    let Some(binder) = module.resolve(occurrence) else {
        return Ok(None);
    };
    let Some(instances) = functions.get(&binder) else {
        return Ok(None);
    };
    let found = match instances.as_slice() {
        [only] => only,
        many => {
            let types = spine_types(module, occurrence, &many[0].shape, |ty| {
                data::erase_free(view.ty(ty).clone())
            })?;
            many.iter()
                .find(|instance| same_types(&instance.types, &types))
                .ok_or(
                    "a polymorphic local function is used at a type it was not instantiated at",
                )?
        }
    };
    Ok(Some((binder, found)))
}

fn instance_subst(
    module: &Module,
    subst: &Substitution,
    shape: &[(BinderId, bool)],
    types: &[Ty],
) -> Result<Substitution, String> {
    let mut local = subst.clone();
    let mut next = types.iter();
    for (binder, _) in shape.iter().filter(|(_, type_lambda)| *type_lambda) {
        let ty = next
            .next()
            .ok_or("instantiation is shorter than the lambdas")?;
        let source = module.binder(*binder);
        local.bind(
            TyVarId {
                name: source.name.as_str().into(),
                occ: source.occ.as_str().into(),
                unique: source.unique.as_str().into(),
            },
            ty.clone(),
        )?;
    }
    Ok(local)
}

fn record_instance(found: &mut Vec<Vec<Ty>>, types: Vec<Ty>) -> Result<bool, String> {
    if found.iter().any(|known| same_types(known, &types)) {
        return Ok(false);
    }
    if found.len() == LOCAL_INSTANCE_BUDGET {
        return Err(
            "a polymorphic local function is used at more types than the budget allows".into(),
        );
    }
    found.push(types);
    Ok(true)
}

pub(super) fn local_instances(
    module: &Module,
    subst: &Substitution,
    bind: &h2r_core_ir::Bind,
) -> Result<Vec<Option<Vec<LocalInstance>>>, String> {
    let inside = |occurrence: ExprId| {
        bind.pairs.iter().position(|pair| {
            occurrence == pair.rhs || module.ancestors(occurrence).any(|a| a == pair.rhs)
        })
    };
    let shapes: Vec<_> = bind
        .pairs
        .iter()
        .map(|pair| lambda_shape(module, pair.rhs))
        .collect();
    let polymorphic: Vec<bool> = shapes
        .iter()
        .map(|shape| shape.iter().any(|(_, ty)| *ty))
        .collect();
    let mut found: Vec<Vec<Vec<Ty>>> = vec![Vec::new(); bind.pairs.len()];
    for (index, pair) in bind.pairs.iter().enumerate() {
        if !polymorphic[index] {
            continue;
        }
        for &occurrence in module.occurrences(pair.binder) {
            if inside(occurrence).is_some_and(|enclosing| polymorphic[enclosing]) {
                continue;
            }
            for types in occurrence_types(module, subst, bind, occurrence, &shapes[index])? {
                record_instance(&mut found[index], types)?;
            }
        }
        if found[index].is_empty() {
            found[index].push(
                shapes[index]
                    .iter()
                    .filter(|(_, type_lambda)| *type_lambda)
                    .map(|_| data::erased_ty())
                    .collect(),
            );
        }
    }
    let mut pending: Vec<(usize, usize)> = found
        .iter()
        .enumerate()
        .flat_map(|(index, types)| (0..types.len()).map(move |k| (index, k)))
        .collect();
    while let Some((enclosing, k)) = pending.pop() {
        let local = instance_subst(module, subst, &shapes[enclosing], &found[enclosing][k])?;
        for (index, pair) in bind.pairs.iter().enumerate() {
            if !polymorphic[index] {
                continue;
            }
            for &occurrence in module.occurrences(pair.binder) {
                if inside(occurrence) != Some(enclosing) {
                    continue;
                }
                for types in occurrence_types(module, &local, bind, occurrence, &shapes[index])? {
                    if record_instance(&mut found[index], types)? {
                        pending.push((index, found[index].len() - 1));
                    }
                }
            }
        }
    }
    bind.pairs
        .iter()
        .enumerate()
        .map(|(index, pair)| {
            if !polymorphic[index] {
                return Ok(None);
            }
            let declared = subst.apply(module.binder_ty(pair.binder)).into_owned();
            found[index]
                .iter()
                .map(|types| {
                    let local = instance_subst(module, subst, &shapes[index], types)?;
                    let mut next = types.iter();
                    let spine = shapes[index]
                        .iter()
                        .map(|(_, type_lambda)| {
                            if *type_lambda {
                                next.next()
                                    .cloned()
                                    .map(dict::SpineArg::Type)
                                    .ok_or("instantiation is shorter than the lambdas")
                            } else {
                                Ok(dict::SpineArg::Value(pair.rhs))
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let ty = positional(&declared, &spine)?;
                    Ok(LocalInstance {
                        subst: local,
                        ty,
                        types: types.clone(),
                        shape: shapes[index].clone(),
                    })
                })
                .collect::<Result<Vec<_>, String>>()
                .map(Some)
        })
        .collect()
}

fn enclosing_instances(
    module: &Module,
    bind: &h2r_core_ir::Bind,
    occurrence: ExprId,
) -> Vec<(ExprId, usize)> {
    let mut chain = Vec::new();
    let mut child = occurrence;
    for parent in module.ancestors(occurrence) {
        if let Expr::Let { bind: here, .. } = module.expr(parent) {
            if here.pairs.first().map(|pair| pair.binder)
                == bind.pairs.first().map(|pair| pair.binder)
            {
                break;
            }
            if let Some(index) = here.pairs.iter().position(|pair| pair.rhs == child)
                && here
                    .pairs
                    .iter()
                    .all(|pair| function_pair(module, pair.binder, pair.rhs))
                && lambda_shape(module, here.pairs[index].rhs)
                    .iter()
                    .any(|(_, ty)| *ty)
            {
                chain.push((parent, index));
            }
        }
        child = parent;
    }
    chain.reverse();
    chain
}

fn occurrence_types(
    module: &Module,
    subst: &Substitution,
    bind: &h2r_core_ir::Bind,
    occurrence: ExprId,
    shape: &[(BinderId, bool)],
) -> Result<Vec<Vec<Ty>>, String> {
    let mut substs = vec![subst.clone()];
    for (let_expr, index) in enclosing_instances(module, bind, occurrence) {
        let Expr::Let { bind: here, .. } = module.expr(let_expr) else {
            unreachable!("an enclosing instance is bound by a let")
        };
        let mut next = Vec::new();
        for outer in &substs {
            let instances = local_instances(module, outer, here)?;
            for instance in instances[index].iter().flatten() {
                next.push(instance.subst.clone());
            }
        }
        substs = next;
    }
    substs
        .iter()
        .map(|local| {
            spine_types(module, occurrence, shape, |ty| {
                data::erase_free(local.apply(module.ty(ty)).into_owned())
            })
        })
        .collect()
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
        detail: None,
    };
    let module = context.module;
    let view = context.view;
    let world = context.world();
    let rhs: Vec<_> = bind.pairs.iter().map(|pair| pair.rhs).collect();
    let captured = captured_locals(module, context.functions, &rhs, locals);
    let captures: Vec<_> = captured.keys().copied().collect();
    let capture_types: Vec<_> = captured
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
    let mut group = LocalFunctions::new();
    let mut definitions = Vec::new();
    let mut bodies = Vec::new();
    let instances = local_instances(module, context.subst, bind).map_err(|reason| fail(&reason))?;
    let variants = bind
        .pairs
        .iter()
        .zip(instances)
        .flat_map(|(pair, instances)| {
            let variants: Vec<Option<LocalInstance>> = match instances {
                None => vec![None],
                Some(instances) => instances.into_iter().map(Some).collect(),
            };
            variants.into_iter().map(move |instance| (pair, instance))
        });
    for (pair, instance) in variants {
        let polymorphic = instance.is_some();
        let (types, shape) = instance.as_ref().map_or_else(
            || (Vec::new(), Vec::new()),
            |instance| (instance.types.clone(), instance.shape.clone()),
        );
        let (local_view, local_subst, signature) = match instance {
            Some(instance) => (
                Some(TypeView::specialized(module, &instance.subst)),
                Some(instance.subst),
                instance.ty,
            ),
            None => (None, None, view.binder_ty(pair.binder).clone()),
        };
        let parameter_view = local_view.as_ref().unwrap_or(view);
        let mut rhs = pair.rhs;
        let mut result = &signature;
        let mut parameters = Vec::new();
        while let Expr::Lam { binder, body } = module.expr(rhs) {
            if polymorphic && module.binder(*binder).kind == BinderKind::Tyvar {
                rhs = *body;
                continue;
            }
            let Ty::Fun { arg, res, .. } = result else {
                return Err(fail("local functions require monomorphic value lambdas"));
            };
            if module.binder(*binder).kind != BinderKind::Id
                || !arg.alpha_eq(parameter_view.binder_ty(*binder))
                || !data::supported(&world, arg)
            {
                return Err(fail("unsupported local function parameter"));
            }
            parameters.push(*binder);
            result = res;
            rhs = *body;
        }
        let result = result.clone();
        if (parameters.is_empty()
            && !(module.binder(pair.binder).is_join_point == Some(true)
                && module.binder(pair.binder).arity == Some(0)))
            || !data::supported(&world, &result)
            || !linkage::closed_type(&signature)
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
        group.entry(pair.binder).or_default().push(LocalFunction {
            types,
            shape,
            target,
            captures: captures.clone(),
            arity: parameters.len(),
        });
        definitions.push(LocalDefinition {
            binder: pair.binder,
            target,
            result_ty: result,
        });
        bodies.push((rhs, parameters, local_view, local_subst));
    }
    functions.extend(group);
    for (definition, (rhs, parameters, local_view, local_subst)) in definitions.iter().zip(bodies) {
        let local_view = local_view.as_ref().unwrap_or(view);
        let mut params = Vec::new();
        let mut scope = BTreeMap::new();
        for (binder, ty) in captures
            .iter()
            .copied()
            .zip(capture_types.iter().cloned())
            .chain(
                parameters
                    .iter()
                    .map(|b| (*b, shared(local_view.binder_ty(*b)))),
            )
        {
            let id = fresh_value(context);
            scope.insert(binder, id);
            params.push(Value { id, ty });
        }
        let nested = BodyContext {
            params: &params,
            view: local_view,
            subst: local_subst.as_ref().unwrap_or(context.subst),
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

pub(super) fn applies_value(module: &Module, mut expr: ExprId) -> bool {
    while let Expr::App { fun, arg } = module.expr(expr) {
        if !matches!(module.expr(*arg), Expr::Type { .. }) {
            return true;
        }
        expr = *fun;
    }
    false
}

pub(super) fn under_type_lambdas(module: &Module, mut expr: ExprId) -> (ExprId, usize) {
    let mut count = 0;
    while let Expr::Lam { binder, body } = module.expr(expr)
        && module.binder(*binder).kind == BinderKind::Tyvar
    {
        expr = *body;
        count += 1;
    }
    (expr, count)
}

pub(super) fn function_pair(module: &Module, binder: BinderId, rhs: ExprId) -> bool {
    matches!(
        module.expr(under_type_lambdas(module, rhs).0),
        Expr::Lam { .. }
    ) || (module.binder(binder).is_join_point == Some(true)
        && module.binder(binder).arity == Some(0))
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
        detail: None,
    };
    if !matches!(
        context
            .module
            .expr(under_type_lambdas(context.module, source).0),
        Expr::Lam { .. }
    ) {
        return lower_type_abstraction(context, source, ty, locals, instructions, blocks);
    }
    if !data::function(&context.world(), ty) {
        return Err(fail(
            "closure requires a supported monomorphic function type",
        ));
    }
    let mut params = Vec::new();
    let mut scope = BTreeMap::new();
    let mut arguments = Vec::new();
    for (binder, value) in &captured_locals(context.module, context.functions, &[source], locals) {
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
    let local_subst =
        erased_lambdas(context.module, context.subst, source).map_err(|r| fail(&r))?;
    let local_view = local_subst
        .as_ref()
        .map(|subst| TypeView::specialized(context.module, subst));
    let view = local_view.as_ref().unwrap_or(context.view);
    let mut rhs = source;
    let mut result = ty.clone();
    while let Expr::Lam { binder, body } = context.module.expr(rhs) {
        if context.module.binder(*binder).kind == BinderKind::Tyvar {
            if !matches!(result, Ty::ForAll { .. }) {
                return Err(fail("closure type lambda lacks a quantifier"));
            }
            result = instantiate::apply(&result, &[data::erased_ty()]).map_err(|r| fail(&r))?;
            rhs = *body;
            continue;
        }
        let Ty::Fun { arg, res, .. } = result else {
            return Err(fail("closure lambda lacks function arrow"));
        };
        if context.module.binder(*binder).kind != BinderKind::Id
            || !arg.alpha_eq(view.binder_ty(*binder))
        {
            return Err(fail("closure lambda parameter mismatch"));
        }
        let id = fresh_value(context);
        params.push(Value {
            id,
            ty: shared(&arg),
        });
        scope.insert(*binder, id);
        result = *res;
        rhs = *body;
    }
    let nested = BodyContext {
        params: &params,
        view,
        subst: local_subst.as_ref().unwrap_or(context.subst),
        ..*context
    };
    let target = lower_tail(&nested, rhs, &result, &scope, blocks)?;
    let id = fresh_value(context);
    instructions.push(Instruction {
        result: Value { id, ty: shared(ty) },
        operation: Operation::MakeClosure { target, arguments },
        origin: Origin {
            module: context.module_index,
            source: Source::Expr(source),
            rule: Rule::MakeClosure,
        },
    });
    Ok(id)
}

fn lower_type_abstraction(
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
        detail: None,
    };
    let (inner, abstractions) = under_type_lambdas(context.module, source);
    let mut result = ty.clone();
    for _ in 0..abstractions {
        if !matches!(result, Ty::ForAll { .. }) {
            return Err(fail("a type abstraction lacks a quantifier"));
        }
        result = instantiate::apply(&result, &[data::erased_ty()]).map_err(|r| fail(&r))?;
    }
    if data::carrier(&context.world(), &result) != data::carrier(&context.world(), ty)
        || !data::supported(&context.world(), ty)
    {
        return Err(fail("a type abstraction's erasure changes its carrier"));
    }
    let local_subst =
        erased_lambdas(context.module, context.subst, source).map_err(|r| fail(&r))?;
    let local_view = local_subst
        .as_ref()
        .map(|subst| TypeView::specialized(context.module, subst));
    let nested = BodyContext {
        view: local_view.as_ref().unwrap_or(context.view),
        subst: local_subst.as_ref().unwrap_or(context.subst),
        ..*context
    };
    let mut scope = locals.clone();
    let erased = lower_value(&nested, inner, &result, &mut scope, instructions, blocks)?;
    let value = fresh_value(context);
    instructions.push(Instruction {
        result: Value {
            id: value,
            ty: shared(ty),
        },
        operation: Operation::Move(erased),
        origin: Origin {
            module: context.module_index,
            source: Source::Expr(source),
            rule: Rule::InstantiateValue,
        },
    });
    Ok(value)
}

fn lower_recursive_group(
    context: &BodyContext<'_>,
    current: ExprId,
    ty: &Ty,
    locals: &mut BTreeMap<BinderId, ValueId>,
    instructions: &mut Vec<Instruction>,
    blocks: &mut Vec<Block>,
) -> Result<ValueId, LowerError> {
    let module = context.module;
    let world = context.world();
    let Expr::Let { bind, body } = module.expr(current) else {
        unreachable!("a recursive group is a let");
    };
    let fail = |reason: &str, about: &Ty| {
        LowerError {
            module: context.module_index,
            owner: context.owner,
            source: Some(current),
            reason: reason.into(),
            detail: None,
        }
        .about(type_head(about))
    };
    let origin = |rule| Origin {
        module: context.module_index,
        source: Source::Expr(current),
        rule,
    };
    let mut cells = Vec::new();
    for pair in &bind.pairs {
        let binding_ty = context.view.binder_ty(pair.binder);
        if module.binder(pair.binder).is_join_point == Some(true) {
            return Err(fail("a join point bound as a value", binding_ty));
        }
        if matches!(module.expr(pair.rhs), Expr::Var { .. }) {
            return Err(fail("a recursive binding that only renames", binding_ty));
        }
        if !data::lifted(&world, binding_ty) {
            return Err(fail(
                "a recursive binding needs a lifted carrier",
                binding_ty,
            ));
        }
        let cell = fresh_value(context);
        instructions.push(Instruction {
            result: Value {
                id: cell,
                ty: shared(binding_ty),
            },
            operation: Operation::PendingCell,
            origin: origin(Rule::RecursiveCell),
        });
        cells.push(cell);
    }
    let previous: Vec<_> = bind
        .pairs
        .iter()
        .zip(&cells)
        .map(|(pair, cell)| (pair.binder, locals.insert(pair.binder, *cell)))
        .collect();
    let mut result = Ok(ValueId(0));
    for (pair, cell) in bind.pairs.iter().zip(&cells) {
        let binding_ty = context.view.binder_ty(pair.binder);
        match lower_region(
            context,
            pair.rhs,
            binding_ty,
            locals,
            instructions,
            blocks,
            true,
        ) {
            Ok(value) => {
                let filled = fresh_value(context);
                instructions.push(Instruction {
                    result: Value {
                        id: filled,
                        ty: shared(binding_ty),
                    },
                    operation: Operation::FillCell { cell: *cell, value },
                    origin: origin(Rule::FillCell),
                });
            }
            Err(error) => {
                result = Err(error);
                break;
            }
        }
    }
    if result.is_ok() {
        result = lower_value(context, *body, ty, locals, instructions, blocks);
    }
    for (binder, previous) in previous.into_iter().rev() {
        match previous {
            Some(value) => locals.insert(binder, value),
            None => locals.remove(&binder),
        };
    }
    result
}

fn constructed(context: &BodyContext<'_>, source: ExprId, ty: &Ty) -> bool {
    builds(context, source, ty, false)
}

fn builds(context: &BodyContext<'_>, source: ExprId, ty: &Ty, forced: bool) -> bool {
    let module = context.module;
    let world = context.world();
    match module.expr(source) {
        Expr::Var { .. } => !forced,
        Expr::Lit(_) => !data::lifted(&world, ty),
        Expr::Lam { .. } => {
            data::function(&world, ty)
                && matches!(
                    module.expr(under_type_lambdas(module, source).0),
                    Expr::Lam { .. }
                )
        }
        Expr::Cast {
            expr,
            from: Some(from),
            to: Some(_),
            role: Some(_),
        } => {
            let from = context.view.ty(*from);
            data::carrier(&world, from).is_some()
                && data::carrier(&world, from) == data::carrier(&world, ty)
                && builds(context, *expr, from, forced)
        }
        Expr::App { .. } => {
            let mut head = source;
            let mut types = Vec::new();
            let mut values = Vec::new();
            while let Expr::App { fun, arg } = module.expr(head) {
                if let Expr::Type { ty, .. } = module.expr(*arg) {
                    types.push(context.view.ty(*ty).clone());
                } else if types.is_empty() {
                    values.push(*arg);
                } else {
                    return false;
                }
                head = *fun;
            }
            let Ok(Some(constructor)) = data::resolve(&world, context.module_index, head, ty)
            else {
                return false;
            };
            types.reverse();
            values.reverse();
            let Ty::Con { args, .. } = ty else {
                return false;
            };
            types.len() == args.len()
                && types.iter().zip(args).all(|(a, b)| a.alpha_eq(b))
                && values.len() == constructor.fields.len()
                && values
                    .iter()
                    .zip(&constructor.fields)
                    .zip(&constructor.strict)
                    .all(|((&value, field), &strict)| {
                        builds(context, value, field, strict && data::lifted(&world, field))
                    })
        }
        _ => false,
    }
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
    for (binder, value) in &captured_locals(context.module, context.functions, &[source], locals) {
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
            ty: shared(ty),
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
