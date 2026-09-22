//! Library functions this backend implements rather than links.
//!
//! These are not primops. They are ordinary Haskell bindings in packages the
//! dump does not contain, so the whole-world resolver cannot find a definition
//! to lower and the choice is to implement the function or to refuse.
//!
//! Each entry asserts the exact GHC signature, and the builder checks the site
//! against it: the spine must be saturated at the entry's own argument count,
//! every argument is lowered *at* the asserted argument type, and the result
//! is compared with the asserted result type. In well-typed Core that pins the
//! signature. What is deliberately not used as evidence is the `IdInfo` arity,
//! which for an imported Id with no unfolding records what this compilation
//! inferred — 0 under `-O0`, the real arity under `-O1` — and so says nothing
//! about the function itself.
//!
//! Nothing is added here because a name looks familiar. An entry exists only
//! when a program this compiler must build reaches it, and it carries the
//! semantics of the named binding, not an approximation of them.

use h2r_core_ir::{Expr, ExprId, Module, Ty, TyConId};

/// One implemented library function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum External {
    /// `GHC.Base.(++) :: forall a. [a] -> [a] -> [a]`.
    ///
    /// Lazy in both arguments and in the spine: forcing the result to WHNF
    /// forces only the left list to WHNF, and the right one is not touched
    /// until the left runs out.
    Append,
}

impl External {
    /// How many type arguments precede the value arguments.
    pub fn type_arity(self) -> usize {
        match self {
            External::Append => 1,
        }
    }

    pub fn value_arity(self) -> usize {
        match self {
            External::Append => 2,
        }
    }

    /// The signature at these closed type arguments, or `None` when the count
    /// is wrong. The quantifiers are instantiated here rather than left open,
    /// so the caller compares closed types throughout.
    pub fn signature(self, type_arguments: &[Ty]) -> Option<Ty> {
        if type_arguments.len() != self.type_arity() {
            return None;
        }
        match self {
            External::Append => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(list.clone(), arrow(list.clone(), list)))
            }
        }
    }

    /// The element type the result's cells hold, for reading the constructor
    /// layouts out of the world.
    pub fn element(self, type_arguments: &[Ty]) -> Option<Ty> {
        match self {
            External::Append => type_arguments.first().cloned(),
        }
    }
}

fn list_of(element: Ty) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: h2r_core_ir::LIST_TYCON.into(),
            occ: "List".into(),
            unique: String::new(),
        },
        args: vec![element],
    }
}

fn arrow(arg: Ty, res: Ty) -> Ty {
    Ty::Fun {
        mult: Box::new(Ty::Con {
            tycon: TyConId {
                name: "$ghc-prim$GHC.Types$Many".into(),
                occ: "Many".into(),
                unique: String::new(),
            },
            args: vec![],
        }),
        arg: Box::new(arg),
        res: Box::new(res),
    }
}

/// Resolve an unbound global occurrence to an implemented library function.
/// The occurrence must be a global this world cannot link, whose `IdInfo` is
/// its own and describes an ordinary Id.
pub fn resolve(module: &Module, head: ExprId) -> Option<External> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    let info = module.id_info(head)?;
    if info.name != *name || !info.details.is_empty() {
        return None;
    }
    match name.as_str() {
        "$base$GHC.Base$++" => Some(External::Append),
        _ => None,
    }
}

/// The quantified type these entries are written against, for a test that the
/// instantiated signature is the one GHC gives the binding.
#[cfg(test)]
fn quantified(external: External) -> Ty {
    let variable = h2r_core_ir::TyVarId {
        name: "a".into(),
        occ: "a".into(),
        unique: "appendElement".into(),
    };
    let body = external
        .signature(&[Ty::Var(variable.clone())])
        .expect("one type argument");
    Ty::ForAll {
        binder: variable,
        body: Box::new(body),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn append_is_quantified_over_one_element_type_and_takes_two_lists() {
        let signature = quantified(External::Append);
        let Ty::ForAll { binder, body } = &signature else {
            panic!("append quantifies over its element type");
        };
        let list = list_of(Ty::Var(binder.clone()));
        assert_eq!(**body, arrow(list.clone(), arrow(list.clone(), list)));
        assert_eq!(
            (
                External::Append.type_arity(),
                External::Append.value_arity()
            ),
            (1, 2)
        );
    }

    #[test]
    fn a_signature_needs_exactly_its_own_type_arguments() {
        let int = Ty::Con {
            tycon: TyConId {
                name: "$ghc-prim$GHC.Types$Int".into(),
                occ: "Int".into(),
                unique: String::new(),
            },
            args: vec![],
        };
        assert!(External::Append.signature(&[]).is_none());
        assert!(
            External::Append
                .signature(&[int.clone(), int.clone()])
                .is_none()
        );
        assert_eq!(
            External::Append.element(std::slice::from_ref(&int)),
            Some(int)
        );
    }
}
