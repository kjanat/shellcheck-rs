//! One instance's view of a module's immutable type table.
//!
//! Specialization never rewrites Core. It reads every type through this view,
//! which applies the instance substitution to the shared table. An empty
//! substitution borrows the table unchanged, so a monomorphic owner sees
//! exactly the types the module carries.

use std::cell::OnceCell;

use h2r_core_ir::{BinderId, Module, Ty, TyId};

use super::subst::{Substitution, free_uniques};

type Chunk = Box<[OnceCell<Option<Ty>>]>;

pub(super) struct TypeView<'m> {
    module: &'m Module,
    subst: Substitution,
    /// Parallel to the module's type table; `None` keeps the shared entry.
    substituted: Vec<OnceCell<Chunk>>,
}

const CHUNK: usize = 256;

impl<'m> TypeView<'m> {
    pub(super) fn identity(module: &'m Module) -> TypeView<'m> {
        TypeView {
            module,
            subst: Substitution::default(),
            substituted: Vec::new(),
        }
    }

    pub(super) fn specialized(module: &'m Module, subst: &Substitution) -> TypeView<'m> {
        if subst.is_empty() {
            return TypeView::identity(module);
        }
        TypeView {
            module,
            subst: subst.clone(),
            substituted: std::iter::repeat_with(OnceCell::new)
                .take(module.types.len().div_ceil(CHUNK))
                .collect(),
        }
    }

    pub(super) fn ty(&self, id: TyId) -> &Ty {
        let shared = self.module.ty(id);
        let index = id as usize;
        let Some(chunk) = self.substituted.get(index / CHUNK) else {
            return shared;
        };
        let cell = &chunk
            .get_or_init(|| std::iter::repeat_with(OnceCell::new).take(CHUNK).collect())
            [index % CHUNK];
        let substituted = cell.get_or_init(|| {
            if free_uniques(shared).is_empty() {
                return None;
            }
            match self.subst.apply(shared) {
                std::borrow::Cow::Borrowed(_) => None,
                std::borrow::Cow::Owned(ty) => Some(ty),
            }
        });
        substituted.as_ref().unwrap_or(shared)
    }

    pub(super) fn binder_ty(&self, binder: BinderId) -> &Ty {
        self.ty(self.module.binder(binder).ty)
    }
}
