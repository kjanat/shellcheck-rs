//! Source linkage and cross-module type evidence, shared by builder and checker.
//! Neither routine inspects candidate NIR.

use h2r_core_ir::{BinderId, Module, Ty, is_external_name};

pub(super) fn imported_top(modules: &[Module], name: &str) -> Result<(usize, BinderId), String> {
    if !is_external_name(name) {
        return Err("import reference lacks an external stable name".into());
    }
    let mut found = None;
    for (index, module) in modules.iter().enumerate() {
        for pair in module.top.iter().flat_map(|group| &group.pairs) {
            if module.binder(pair.binder).name == name
                && found.replace((index, pair.binder)).is_some()
            {
                return Err("ambiguous imported top-level binding".into());
            }
        }
    }
    found.ok_or_else(|| "imported binding is outside the loaded world".into())
}

/// Free uniques and internal constructor names cannot identify types across
/// modules. Opaque text is not evidence either. Quantified, alpha-renamed types
/// are supported, but shadowed uniques are conservatively refused.
pub(super) fn closed_type(ty: &Ty) -> bool {
    let mut work = vec![(ty, 0)];
    let mut bound: Vec<&str> = Vec::new();
    while let Some((ty, depth)) = work.pop() {
        bound.truncate(depth);
        match ty {
            Ty::Var(var) if !bound.contains(&var.unique.as_str()) => return false,
            Ty::Var(_) | Ty::Lit { .. } => {}
            Ty::Con { tycon, args } => {
                if !is_external_name(&tycon.name) {
                    return false;
                }
                work.extend(args.iter().map(|arg| (arg, depth)));
            }
            Ty::App { fun, arg } => work.extend([(fun.as_ref(), depth), (arg.as_ref(), depth)]),
            Ty::Fun { mult, arg, res } => work.extend([
                (mult.as_ref(), depth),
                (arg.as_ref(), depth),
                (res.as_ref(), depth),
            ]),
            Ty::ForAll { binder, body } => {
                if bound.contains(&binder.unique.as_str()) {
                    return false;
                }
                bound.push(&binder.unique);
                work.push((body, depth + 1));
            }
            Ty::Opaque { .. } => return false,
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use h2r_core_ir::TyVarId;

    #[test]
    fn closedness_does_not_leak_binders_into_siblings() {
        let var = TyVarId {
            name: "a".into(),
            occ: "a".into(),
            unique: "a".into(),
        };
        let quantified = Ty::ForAll {
            binder: var.clone(),
            body: Box::new(Ty::Var(var.clone())),
        };
        assert!(closed_type(&quantified));
        for (fun, arg) in [
            (quantified.clone(), Ty::Var(var.clone())),
            (Ty::Var(var.clone()), quantified.clone()),
        ] {
            assert!(!closed_type(&Ty::App {
                fun: Box::new(fun),
                arg: Box::new(arg)
            }));
        }
        assert!(!closed_type(&Ty::ForAll {
            binder: var,
            body: Box::new(quantified)
        }));
    }
}
