//! Constructor layouts come from GHC worker signatures, never printed types.
use h2r_core_ir::{Expr, ExprId, Module, Ty};

use super::{boxed, instantiate, primitive, world};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: String,
    pub tag: u32,
    pub result: Ty,
    pub fields: Vec<Ty>,
    pub strict: Vec<bool>,
}

pub fn is_data(module: &Module, ty: &Ty) -> bool {
    !boxed::is_int(ty)
        && world::closed_type(ty)
        && matches!(ty, Ty::Con { tycon, .. }
            if module.constructors.iter().any(|c| c.family == tycon.name && c.vanilla))
}

pub fn lifted(module: &Module, ty: &Ty) -> bool {
    boxed::is_int(ty) || is_data(module, ty) || function(module, ty)
}

pub fn function(module: &Module, ty: &Ty) -> bool {
    matches!(ty, Ty::Fun { arg, res, .. } if world::closed_type(ty) && supported(module, arg) && supported(module, res))
}

pub fn supported(module: &Module, ty: &Ty) -> bool {
    primitive::is_int(ty) || lifted(module, ty)
}

pub fn layout(module: &Module, name: &str, ty: &Ty) -> Result<Constructor, String> {
    let Ty::Con { tycon, args } = ty else {
        return Err("constructor requires an algebraic result type".into());
    };
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.name == name)
        .collect();
    let [info] = found.as_slice() else {
        return Err("missing or ambiguous constructor layout evidence".into());
    };
    if !info.vanilla || info.family != tycon.name || info.tag == 0 || boxed::is_int(ty) {
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
        if !supported(module, arg) {
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
pub fn resolve(module: &Module, source: ExprId, ty: &Ty) -> Result<Option<Constructor>, String> {
    let Expr::Var { name, .. } = module.expr(source) else {
        return Ok(None);
    };
    if module.reference(source) != Some(h2r_core_ir::Ref::Global) {
        return Ok(None);
    }
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.worker == *name)
        .collect();
    if found.is_empty() {
        return Ok(None);
    }
    let [info] = found.as_slice() else {
        return Err("ambiguous constructor worker".into());
    };
    if boxed::is_int(ty) {
        return Ok(None);
    }
    layout(module, &info.name, ty).map(Some)
}

pub fn family(module: &Module, ty: &Ty) -> Result<Vec<Constructor>, String> {
    let Ty::Con { tycon, .. } = ty else {
        return Err("non-algebraic case type".into());
    };
    let layouts = module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .map(|c| layout(module, &c.name, ty))
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
