//! Constructor layouts come from GHC worker signatures, never printed types.
//!
//! Layouts are whole-world facts. A function from one module, specialized at a
//! type declared in another, needs that other module's constructor evidence, so
//! every query here searches the loaded world rather than one module's table.
//! The same constructor appears in every module that mentions it; those entries
//! must agree, and a disagreement is an error rather than a first-wins pick.

use h2r_core_ir::{Expr, ExprId, Module, Ty, raw::ConstructorInfo};

use super::linkage::closed_type;
use super::{World, boxed, instantiate, primitive};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: String,
    pub tag: u32,
    pub result: Ty,
    pub fields: Vec<Ty>,
    pub strict: Vec<bool>,
}

/// Does any readable module carry a usable constructor of this family?
pub fn is_data(world: &World<'_>, ty: &Ty) -> bool {
    !boxed::is_int(ty)
        && closed_type(ty)
        && matches!(ty, Ty::Con { tycon, .. } if world.iter().any(|(_, module)| {
            module
                .constructors
                .iter()
                .any(|c| c.family == tycon.name && c.boxed_record())
        }))
}

pub fn lifted(world: &World<'_>, ty: &Ty) -> bool {
    boxed::is_int(ty) || is_data(world, ty) || function(world, ty)
}

pub fn function(world: &World<'_>, ty: &Ty) -> bool {
    matches!(ty, Ty::Fun { arg, res, .. }
        if closed_type(ty) && supported(world, arg) && supported(world, res))
}

pub fn supported(world: &World<'_>, ty: &Ty) -> bool {
    primitive::is_int(ty) || lifted(world, ty)
}

/// The module whose table the family's layouts are read from, with every other
/// module's entries checked to agree. A constructor that two modules describe
/// differently is an error, not a first-wins pick.
fn declaring<'a>(world: &World<'a>, family: &str) -> Result<Option<&'a Module>, String> {
    let mut chosen: Option<&Module> = None;
    for (_, module) in world.iter() {
        let here: Vec<&ConstructorInfo> = module
            .constructors
            .iter()
            .filter(|c| c.family == family)
            .collect();
        if here.is_empty() {
            continue;
        }
        let Some(first) = chosen else {
            chosen = Some(module);
            continue;
        };
        let there: Vec<&ConstructorInfo> = first
            .constructors
            .iter()
            .filter(|c| c.family == family)
            .collect();
        if here.len() != there.len()
            || here.iter().zip(&there).any(|(a, b)| {
                (
                    &a.name,
                    a.tag,
                    a.family_size,
                    a.rep_arity,
                    &a.strict,
                    a.boxed_record(),
                ) != (
                    &b.name,
                    b.tag,
                    b.family_size,
                    b.rep_arity,
                    &b.strict,
                    b.boxed_record(),
                ) || !module
                    .types
                    .get(a.signature as usize)
                    .zip(first.types.get(b.signature as usize))
                    .is_some_and(|(x, y)| x.alpha_eq(y))
            })
        {
            return Err("modules disagree about a constructor family's layout".into());
        }
    }
    Ok(chosen)
}

pub fn layout(world: &World<'_>, name: &str, ty: &Ty) -> Result<Constructor, String> {
    let Ty::Con { tycon, args } = ty else {
        return Err("constructor requires an algebraic result type".into());
    };
    let module =
        declaring(world, &tycon.name)?.ok_or("missing or ambiguous constructor layout evidence")?;
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.name == name && c.family == tycon.name)
        .collect();
    let [info] = found.as_slice() else {
        return Err("missing or ambiguous constructor layout evidence".into());
    };
    if !info.boxed_record() || info.tag == 0 || boxed::is_int(ty) {
        return Err("unsupported constructor family or representation".into());
    }
    let signature = module
        .types
        .get(info.signature as usize)
        .ok_or("invalid constructor signature index")?;
    let instantiated = instantiate::apply(signature, args)?;
    let mut result = &instantiated;
    let mut fields = Vec::new();
    while let Ty::Fun { arg, res, .. } = result {
        if !supported(world, arg) {
            return Err("unsupported constructor field carrier".into());
        }
        fields.push((**arg).clone());
        result = res;
    }
    if !result.alpha_eq(ty)
        || fields.len() != info.rep_arity as usize
        || fields.len() != info.strict.len()
    {
        return Err("constructor worker signature/layout mismatch".into());
    }
    Ok(Constructor {
        name: name.into(),
        tag: info.tag,
        result: ty.clone(),
        fields,
        strict: info.strict.clone(),
    })
}

/// Resolve only unbound global worker occurrences. A local shadow never gains
/// constructor semantics from its spelling or an unrelated id-table entry.
pub fn resolve(
    world: &World<'_>,
    module_index: usize,
    source: ExprId,
    ty: &Ty,
) -> Result<Option<Constructor>, String> {
    let module = world.at(module_index)?;
    let Expr::Var { name, .. } = module.expr(source) else {
        return Ok(None);
    };
    if module.reference(source) != Some(h2r_core_ir::Ref::Global) {
        return Ok(None);
    }
    let mut constructor = None;
    for (_, readable) in world.iter() {
        for info in readable.constructors.iter().filter(|c| c.worker == *name) {
            match constructor {
                None => constructor = Some(info.name.clone()),
                Some(ref already) if *already == info.name => {}
                Some(_) => return Err("ambiguous constructor worker".into()),
            }
        }
    }
    let Some(constructor) = constructor else {
        return Ok(None);
    };
    if boxed::is_int(ty) {
        return Ok(None);
    }
    layout(world, &constructor, ty).map(Some)
}

pub fn family(world: &World<'_>, ty: &Ty) -> Result<Vec<Constructor>, String> {
    let Ty::Con { tycon, .. } = ty else {
        return Err("non-algebraic case type".into());
    };
    let module = declaring(world, &tycon.name)?.ok_or("missing or ambiguous constructor family")?;
    let layouts = module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .map(|c| layout(world, &c.name, ty))
        .collect::<Result<Vec<_>, _>>()?;
    let mut tags = std::collections::BTreeSet::new();
    if layouts.is_empty() || layouts.iter().any(|c| !tags.insert(c.tag)) {
        return Err("missing or ambiguous constructor family".into());
    }
    if module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .any(|c| c.family_size as usize != layouts.len())
    {
        return Err("incomplete constructor family census".into());
    }
    // GHC tags are contiguous, starting at one. Missing entries fail closed.
    if tags.iter().copied().ne(1..=layouts.len() as u32) {
        return Err("incomplete constructor family".into());
    }
    Ok(layouts)
}
