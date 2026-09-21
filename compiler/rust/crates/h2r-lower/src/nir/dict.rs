//! Class dictionaries as the algebraic values they are.
//!
//! A class dictionary is an ordinary single-constructor data value and a class
//! method selector is an ordinary case on it, so nothing here needs a new
//! runtime concept. What it does need is *evidence*: the selector's field index
//! is read out of the selector's own Core body, and an instance dictionary's
//! fields are read out of the constructor application its binding is. GHC's
//! `IdDetails` (`[ClassOp]`, `[DFunId]`) corroborates each shape; neither the
//! occurrence name nor the rendered type is ever the proof.
//!
//! Resolution is compile-time only and reads the source alone, so the lowering
//! builder and the independent verifier both reach the same target without
//! either consulting the other's result. A dictionary that resolves here is
//! erased into an instance key and allocates nothing. A dictionary that does
//! not resolve stays an ordinary runtime value, and a method call on it stays
//! an ordinary constructor match.

use std::collections::BTreeMap;

use h2r_core_ir::{BindSite, BinderId, BinderKind, Expr, ExprId, Module, Ref, Ty};

use super::subst::Substitution;
use super::{DictionaryRef, World, instantiate, linkage};

/// How deep a chain of dictionary arguments, superclass fields and top-level
/// aliases may go before resolution gives up. A recursive dictionary has no
/// finite normal form, so past this depth the answer is that the dictionary is
/// not proven unique, and its method calls keep their runtime dispatch.
pub(super) const DEPTH_BUDGET: usize = 16;

/// The lexical scope a dictionary expression is read in: the instance's type
/// substitution and the dictionary lambdas it has already consumed.
pub(super) struct Scope<'a> {
    pub module: usize,
    pub types: &'a Substitution,
    pub dictionaries: &'a BTreeMap<BinderId, DictionaryRef>,
}

/// One class method selector, as its own body establishes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Selector {
    pub constructor: String,
    pub field: usize,
    pub fields: usize,
}

/// A top-level instance dictionary, as the constructor application it is.
pub(super) struct Producer {
    pub module: usize,
    pub constructor: String,
    pub type_params: Vec<BinderId>,
    pub dictionary_params: Vec<BinderId>,
    pub fields: Vec<ExprId>,
}

fn details(world: &World<'_>, module: usize, binder: BinderId) -> Result<Option<String>, String> {
    Ok(world.at(module)?.binder(binder).details.clone())
}

fn top_pair(module: &Module, binder: BinderId) -> Option<ExprId> {
    module
        .top
        .iter()
        .flat_map(|bind| &bind.pairs)
        .find(|pair| pair.binder == binder)
        .map(|pair| pair.rhs)
}

/// The top-level binding an occurrence names, wherever in the world it lives.
pub(super) fn top_target(
    world: &World<'_>,
    module_index: usize,
    head: ExprId,
) -> Result<Option<(usize, BinderId)>, String> {
    let module = world.at(module_index)?;
    let Expr::Var { name, .. } = module.expr(head) else {
        return Ok(None);
    };
    match module.reference(head) {
        Some(Ref::Local(binder)) if matches!(module.binding(binder).site, BindSite::Top) => {
            Ok(Some((module_index, binder)))
        }
        Some(Ref::Global) => {
            let modules = world
                .modules
                .ok_or("import evidence requires a loaded world")?;
            linkage::imported_top(modules, name).map(Some)
        }
        _ => Ok(None),
    }
}

/// The same lookup, for a probe rather than a demand: an occurrence that names
/// nothing this world can link is simply not a target, and the caller decides
/// whether that is a refusal or just an argument that is not a dictionary.
fn probe_target(world: &World<'_>, module_index: usize, head: ExprId) -> Option<(usize, BinderId)> {
    top_target(world, module_index, head).ok().flatten()
}

/// Split an application spine, refusing an interleaved one. Returns the head,
/// the type arguments and the value arguments, all in source order.
pub(super) fn spine(
    module: &Module,
    mut current: ExprId,
) -> Result<(ExprId, Vec<Ty>, Vec<ExprId>), String> {
    let mut types = Vec::new();
    let mut values = Vec::new();
    loop {
        match module.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::App { fun, arg } => {
                match module.expr(*arg) {
                    Expr::Type { ty, .. } => types.push(module.ty(*ty).clone()),
                    _ if types.is_empty() => values.push(*arg),
                    _ => return Err("interleaved type and value arguments".into()),
                }
                current = *fun;
            }
            _ => break,
        }
    }
    types.reverse();
    values.reverse();
    Ok((current, types, values))
}

/// Read a class method selector out of its own body: leading type lambdas, one
/// dictionary lambda, and a single-alternative case returning one field.
pub(super) fn selector(
    world: &World<'_>,
    module_index: usize,
    head: ExprId,
) -> Result<Option<(usize, BinderId, Selector)>, String> {
    let Some((target_module, binder)) = probe_target(world, module_index, head) else {
        return Ok(None);
    };
    if details(world, target_module, binder)?.as_deref() != Some("[ClassOp]") {
        return Ok(None);
    }
    let module = world.at(target_module)?;
    let rhs =
        top_pair(module, binder).ok_or("class method selector has no top-level right-hand side")?;
    let mut current = rhs;
    let mut dictionary = None;
    loop {
        match module.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::Lam { binder, body } => {
                if module.binder(*binder).kind == BinderKind::Tyvar {
                    if dictionary.is_some() {
                        return Err(
                            "class method selector binds a type after its dictionary".into()
                        );
                    }
                } else if dictionary.replace(*binder).is_some() {
                    return Err("class method selector binds more than one dictionary".into());
                }
                current = *body;
            }
            _ => break,
        }
    }
    let dictionary = dictionary.ok_or("class method selector binds no dictionary")?;
    let Expr::Case { scrut, alts, .. } = module.expr(current) else {
        return Err("class method selector does not match its dictionary".into());
    };
    if module.resolve(*scrut) != Some(dictionary) {
        return Err("class method selector matches something other than its dictionary".into());
    }
    let [alt] = alts.as_slice() else {
        return Err("class method selector is not a single-constructor match".into());
    };
    let h2r_core_ir::AltCon::DataAlt { name, .. } = &alt.con else {
        return Err("class method selector does not match a constructor".into());
    };
    let selected = module
        .resolve(alt.rhs)
        .ok_or("class method selector does not return a bound field")?;
    let field = alt
        .binders
        .iter()
        .position(|b| *b == selected)
        .ok_or("class method selector returns something other than a field")?;
    Ok(Some((
        target_module,
        binder,
        Selector {
            constructor: name.clone(),
            field,
            fields: alt.binders.len(),
        },
    )))
}

/// Read a dictionary out of its binding: leading type and dictionary lambdas,
/// then one saturated application of a class's constructor.
///
/// GHC marks an *instance* dictionary `[DFunId]`, but a dictionary the
/// desugarer floated to the top level carries no such mark, so the deciding
/// evidence is the constructor's family being a class. A binding whose shape
/// does not match is not a dictionary, which is an answer rather than an
/// error: its method calls then keep their runtime dispatch.
pub(super) fn producer(
    world: &World<'_>,
    module_index: usize,
    binder: BinderId,
) -> Result<Option<Producer>, String> {
    let module = world.at(module_index)?;
    let Some(rhs) = top_pair(module, binder) else {
        return Ok(None);
    };
    let mut current = rhs;
    let mut type_params = Vec::new();
    let mut dictionary_params = Vec::new();
    loop {
        match module.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::Lam { binder, body } => {
                if module.binder(*binder).kind == BinderKind::Tyvar {
                    if !dictionary_params.is_empty() {
                        return Ok(None);
                    }
                    type_params.push(*binder);
                } else {
                    dictionary_params.push(*binder);
                }
                current = *body;
            }
            _ => break,
        }
    }
    // The constructor's type arguments are the class's, derived from the
    // instance head; they need not be the dictionary's own binders.
    let Ok((head, _, fields)) = spine(module, current) else {
        return Ok(None);
    };
    let Expr::Var { name, .. } = module.expr(head) else {
        return Ok(None);
    };
    if module.reference(head) != Some(Ref::Global) {
        return Ok(None);
    }
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.worker == *name)
        .collect();
    let [info] = found.as_slice() else {
        return Ok(None);
    };
    if info.class_dictionary != Some(true)
        && details(world, module_index, binder)?.as_deref() != Some("[DFunId]")
    {
        return Ok(None);
    }
    if !info.boxed_record() || info.family_size != 1 || info.rep_arity as usize != fields.len() {
        return Err("unsupported class dictionary representation".into());
    }
    Ok(Some(Producer {
        module: module_index,
        constructor: info.name.clone(),
        type_params,
        dictionary_params,
        fields,
    }))
}

/// The type one instance reference has, from its target's own signature.
pub(super) fn reference_type(world: &World<'_>, reference: &DictionaryRef) -> Result<Ty, String> {
    let signature = world.at(reference.module)?.binder_ty(reference.binder);
    let mut ty = instantiate::apply(signature, &reference.type_arguments)?;
    for _ in &reference.dictionaries {
        let Ty::Fun { res, .. } = ty else {
            return Err(
                "instance reference supplies more dictionaries than its target takes".into(),
            );
        };
        ty = *res;
    }
    Ok(ty)
}

/// How many runtime parameters one instance still takes: GHC's arity for the
/// target, less the dictionary lambdas the instance key already consumed.
pub(super) fn residual_arity(
    world: &World<'_>,
    reference: &DictionaryRef,
) -> Result<usize, String> {
    let arity = world
        .at(reference.module)?
        .binder(reference.binder)
        .arity
        .ok_or("instance target has no arity")? as usize;
    arity
        .checked_sub(reference.dictionaries.len())
        .ok_or_else(|| "instance consumes more dictionaries than its target's arity".into())
}

/// Resolve one expression to a compile-time instance reference: a spine whose
/// head is a top-level binding or a dictionary already bound by this instance,
/// and whose value arguments are all themselves resolvable dictionaries.
pub(super) fn resolve_reference(
    world: &World<'_>,
    scope: &Scope<'_>,
    expr: ExprId,
    depth: usize,
) -> Result<Option<DictionaryRef>, String> {
    if depth > DEPTH_BUDGET {
        // A chain this long is not a proven-unique dictionary. Saying so is
        // an answer: the call keeps its runtime dispatch.
        return Ok(None);
    }
    let module = world.at(scope.module)?;
    let (head, types, values) = spine(module, expr)?;
    if !matches!(module.expr(head), Expr::Var { .. }) {
        return Ok(None);
    }
    if let Some(binder) = module.resolve(head)
        && let Some(bound) = scope.dictionaries.get(&binder)
    {
        if !types.is_empty() || !values.is_empty() {
            return Err("a bound dictionary cannot take further arguments".into());
        }
        return Ok(Some(bound.clone()));
    }
    let Some((target_module, binder)) = probe_target(world, scope.module, head) else {
        return Ok(None);
    };
    let mut type_arguments = Vec::new();
    for ty in &types {
        let applied = scope.types.apply(ty).into_owned();
        if !linkage::closed_type(&applied) {
            return Err("instance reference needs closed structured type arguments".into());
        }
        type_arguments.push(applied);
    }
    let mut dictionaries = Vec::new();
    for value in &values {
        match resolve_dictionary(world, scope, *value, depth + 1)? {
            Some(dictionary) => dictionaries.push(dictionary),
            None => return Ok(None),
        }
    }
    Ok(Some(DictionaryRef {
        module: target_module,
        binder,
        type_arguments,
        dictionaries,
    }))
}

/// Resolve an expression that must denote a dictionary: an instance reference
/// whose target is an instance dictionary, a dictionary already bound by this
/// instance, or a superclass field read out of one of those.
pub(super) fn resolve_dictionary(
    world: &World<'_>,
    scope: &Scope<'_>,
    expr: ExprId,
    depth: usize,
) -> Result<Option<DictionaryRef>, String> {
    if depth > DEPTH_BUDGET {
        // A chain this long is not a proven-unique dictionary. Saying so is
        // an answer: the call keeps its runtime dispatch.
        return Ok(None);
    }
    let module = world.at(scope.module)?;
    let (head, _, values) = spine(module, expr)?;
    // A superclass is a field of a dictionary, reached through its selector.
    // The field it names is only a dictionary if it is one: an ordinary
    // method read the same way is not, and must not be absorbed as one.
    let resolved = match selector(world, scope.module, head)? {
        Some((_, _, method)) if values.len() == 1 => {
            match resolve_dictionary(world, scope, values[0], depth + 1)? {
                Some(dictionary) => field(world, &dictionary, &method, depth + 1)?,
                None => None,
            }
        }
        _ => resolve_reference(world, scope, expr, depth)?,
    };
    let Some(reference) = resolved else {
        return Ok(None);
    };
    // Every dictionary in scope was resolved through this same test, so one
    // check against the producer covers bound and freshly resolved alike.
    if producer(world, reference.module, reference.binder)?.is_some() {
        return Ok(Some(reference));
    }
    // The desugarer gives a dictionary it needed a top-level name of its own,
    // and a superclass field is such a name applied to the instance's own
    // arguments. That name denotes the dictionary its right-hand side builds,
    // so read the right-hand side in the scope those arguments create rather
    // than treating the binding as opaque. The depth budget bounds a chain
    // that never reaches a constructor.
    let target = world.at(reference.module)?;
    let Some(rhs) = top_pair(target, reference.binder) else {
        return Ok(None);
    };
    let mut current = rhs;
    let mut types = Substitution::default();
    let mut dictionaries = BTreeMap::new();
    loop {
        match target.expr(current) {
            Expr::Tick(body) => current = *body,
            Expr::Lam { binder, body } => {
                let bound = target.binder(*binder);
                if bound.kind == BinderKind::Tyvar {
                    let Some(argument) = reference.type_arguments.get(types.len()) else {
                        return Ok(None);
                    };
                    types.bind(
                        h2r_core_ir::TyVarId {
                            name: bound.name.clone(),
                            occ: bound.occ.clone(),
                            unique: bound.unique.clone(),
                        },
                        argument.clone(),
                    )?;
                } else {
                    let Some(argument) = reference.dictionaries.get(dictionaries.len()) else {
                        return Ok(None);
                    };
                    dictionaries.insert(*binder, argument.clone());
                }
                current = *body;
            }
            _ => break,
        }
    }
    if types.len() != reference.type_arguments.len()
        || dictionaries.len() != reference.dictionaries.len()
    {
        return Ok(None);
    }
    let inner = Scope {
        module: reference.module,
        types: &types,
        dictionaries: &dictionaries,
    };
    resolve_dictionary(world, &inner, current, depth + 1)
}

/// One resolved call target: which instance the spine's head denotes, what it
/// still expects at runtime, and which source arguments the instance key
/// absorbed.
pub(super) struct CallTarget {
    pub reference: DictionaryRef,
    /// The target's type after its type and dictionary arguments.
    pub signature: Ty,
    /// Runtime parameters the instance still takes.
    pub arity: usize,
    /// Argument sources that remain runtime arguments, in source order.
    pub arguments: Vec<ExprId>,
    /// Argument sources the instance key absorbed, in source order.
    pub erased: Vec<ExprId>,
    /// The head was a class method selector whose dictionary was proven unique.
    pub method: bool,
}

/// Resolve an application spine's head to one instance, absorbing the leading
/// dictionary arguments. A class method whose dictionary is proven unique
/// resolves to that instance's method; anything else keeps its dictionary as an
/// ordinary runtime value, so dispatch survives where uniqueness is not proven.
pub(super) fn call_target(
    world: &World<'_>,
    scope: &Scope<'_>,
    head: ExprId,
    type_arguments: &[Ty],
    argument_sources: &[ExprId],
) -> Result<Option<CallTarget>, String> {
    if let Some((_, _, method)) = selector(world, scope.module, head)?
        && let [dictionary_source, rest @ ..] = argument_sources
        && let Some(dictionary) = resolve_dictionary(world, scope, *dictionary_source, 0)?
        && let Some(target) = field(world, &dictionary, &method, 0)?
    {
        let mut resolved = absorb(world, scope, target, rest)?;
        resolved.erased.insert(0, *dictionary_source);
        resolved.method = true;
        return Ok(Some(resolved));
    }
    let Some((target_module, binder)) = top_target(world, scope.module, head)? else {
        return Ok(None);
    };
    let reference = DictionaryRef {
        module: target_module,
        binder,
        type_arguments: type_arguments.to_vec(),
        dictionaries: Vec::new(),
    };
    absorb(world, scope, reference, argument_sources).map(Some)
}

/// Absorb the leading argument sources that are proven-unique dictionaries into
/// the instance key. The first argument that is not stops the absorption, so a
/// dictionary that arrives later stays exactly where the source put it.
fn absorb(
    world: &World<'_>,
    scope: &Scope<'_>,
    mut reference: DictionaryRef,
    argument_sources: &[ExprId],
) -> Result<CallTarget, String> {
    let mut erased = Vec::new();
    let mut rest = argument_sources;
    while let [source, tail @ ..] = rest {
        let Some(dictionary) = resolve_dictionary(world, scope, *source, 0)? else {
            break;
        };
        reference.dictionaries.push(dictionary);
        erased.push(*source);
        rest = tail;
    }
    let signature = reference_type(world, &reference)?;
    let arity = residual_arity(world, &reference)?;
    Ok(CallTarget {
        reference,
        signature,
        arity,
        arguments: rest.to_vec(),
        erased,
        method: false,
    })
}

/// Read one field of a known dictionary, in the producer's own scope.
pub(super) fn field(
    world: &World<'_>,
    dictionary: &DictionaryRef,
    method: &Selector,
    depth: usize,
) -> Result<Option<DictionaryRef>, String> {
    if depth > DEPTH_BUDGET {
        return Ok(None);
    }
    let Some(producer) = producer(world, dictionary.module, dictionary.binder)? else {
        return Ok(None);
    };
    if producer.constructor != method.constructor || producer.fields.len() != method.fields {
        return Err("dictionary layout disagrees with the selector's class".into());
    }
    if producer.type_params.len() != dictionary.type_arguments.len()
        || producer.dictionary_params.len() != dictionary.dictionaries.len()
    {
        return Err("dictionary instantiation differs from its producer's binders".into());
    }
    let module = world.at(producer.module)?;
    let mut types = Substitution::default();
    for (binder, argument) in producer.type_params.iter().zip(&dictionary.type_arguments) {
        let source = module.binder(*binder);
        types.bind(
            h2r_core_ir::TyVarId {
                name: source.name.clone(),
                occ: source.occ.clone(),
                unique: source.unique.clone(),
            },
            argument.clone(),
        )?;
    }
    let dictionaries: BTreeMap<_, _> = producer
        .dictionary_params
        .iter()
        .copied()
        .zip(dictionary.dictionaries.iter().cloned())
        .collect();
    let inner = Scope {
        module: producer.module,
        types: &types,
        dictionaries: &dictionaries,
    };
    let selected = *producer
        .fields
        .get(method.field)
        .ok_or("selector field index is outside the dictionary's layout")?;
    resolve_reference(world, &inner, selected, depth + 1)
}
