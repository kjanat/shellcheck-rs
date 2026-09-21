//! One instance's view of a module's immutable type table.
//!
//! Specialization never rewrites Core. It reads every type through this view,
//! which applies the instance substitution to the shared table. An empty
//! substitution borrows the table unchanged, so a monomorphic owner sees
//! exactly the types the module carries.

use h2r_core_ir::{BinderId, Module, Ty, TyId};

use super::subst::{Substitution, free_uniques};

pub(super) struct TypeView<'m> {
    module: &'m Module,
    /// Parallel to the module's type table; `None` keeps the shared entry.
    substituted: Vec<Option<Ty>>,
}

impl<'m> TypeView<'m> {
    pub(super) fn identity(module: &'m Module) -> TypeView<'m> {
        TypeView {
            module,
            substituted: Vec::new(),
        }
    }

    pub(super) fn specialized(module: &'m Module, subst: &Substitution) -> TypeView<'m> {
        if subst.is_empty() {
            return TypeView::identity(module);
        }
        let substituted = module
            .types
            .iter()
            .map(|ty| {
                let free = free_uniques(ty);
                if free.is_empty() {
                    return None;
                }
                let applied = subst.apply(ty);
                match applied {
                    std::borrow::Cow::Borrowed(_) => None,
                    std::borrow::Cow::Owned(ty) => Some(ty),
                }
            })
            .collect();
        TypeView {
            module,
            substituted,
        }
    }

    pub(super) fn ty(&self, id: TyId) -> &Ty {
        match self.substituted.get(id as usize).and_then(Option::as_ref) {
            Some(ty) => ty,
            None => self.module.ty(id),
        }
    }

    pub(super) fn binder_ty(&self, binder: BinderId) -> &Ty {
        self.ty(self.module.binder(binder).ty)
    }
}
