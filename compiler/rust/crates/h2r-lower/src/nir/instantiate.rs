//! Closed type instantiation. Source-spine recognition lives in the builder and
//! verifier separately; only source linkage and type substitution are shared.

use h2r_core_ir::{BindSite, BinderId, Expr, ExprId, Module, Ref, Ty};

use super::linkage;

pub(super) fn target<'a>(
    module: &'a Module,
    module_index: usize,
    modules: Option<&'a [Module]>,
    head: ExprId,
) -> Result<(usize, BinderId, &'a Ty), String> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return Err("application requires a top-level variable head".into());
    };
    match module.reference(head) {
        Some(Ref::Local(binder)) if matches!(module.binding(binder).site, BindSite::Top) => {
            Ok((module_index, binder, module.binder_ty(binder)))
        }
        Some(Ref::Global) => {
            let modules = modules.ok_or("application import requires a loaded world")?;
            let (index, binder) = linkage::imported_top(modules, name)?;
            Ok((index, binder, modules[index].binder_ty(binder)))
        }
        _ => Err("application requires a top-level binding".into()),
    }
}

/// Closed arguments cannot capture variables during substitution. GHC remains
/// trusted for kind correctness, as for all loaded source types in leaf lowering.
pub(super) fn apply(head: &Ty, arguments: &[Ty]) -> Result<Ty, String> {
    if !linkage::closed_type(head) || arguments.iter().any(|arg| !linkage::closed_type(arg)) {
        return Err("type application requires closed structured types".into());
    }
    let mut result = head.clone();
    for argument in arguments {
        let Ty::ForAll { binder, body } = result else {
            return Err("type application exceeds forall parameters".into());
        };
        result = *body;
        super::subst::substitute_capture_safe(&mut result, &binder.unique, argument);
        if !linkage::closed_type(&result) {
            return Err("type instantiation leaves ambiguous type scope".into());
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use h2r_core_ir::TyVarId;

    #[test]
    fn substitution_preserves_remaining_quantifiers_and_visits_arrows_and_apps() {
        let a = TyVarId {
            name: "a".into(),
            occ: "a".into(),
            unique: "a".into(),
        };
        let b = TyVarId {
            name: "b".into(),
            occ: "b".into(),
            unique: "b".into(),
        };
        let body = |argument: Ty| Ty::Fun {
            mult: Box::new(argument.clone()),
            arg: Box::new(argument.clone()),
            res: Box::new(Ty::App {
                fun: Box::new(Ty::Var(b.clone())),
                arg: Box::new(argument),
            }),
        };
        let head = Ty::ForAll {
            binder: a.clone(),
            body: Box::new(Ty::ForAll {
                binder: b.clone(),
                body: Box::new(body(Ty::Var(a))),
            }),
        };
        let replacement = Ty::Lit {
            kind: "Nat".into(),
            text: "1".into(),
        };
        let expected = Ty::ForAll {
            binder: b.clone(),
            body: Box::new(body(replacement.clone())),
        };
        assert_eq!(apply(&head, &[replacement]).unwrap(), expected);
        // These are structural substitution tests, not GHC kind checking.
        assert!(apply(&head, &[Ty::Var(b)]).is_err());
        assert!(apply(&head, &[Ty::Opaque { pretty: "T".into() }]).is_err());
    }
}
