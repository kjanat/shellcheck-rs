//! Library functions this backend implements rather than links.
//!
//! Most are ordinary Haskell bindings in packages the dump does not contain,
//! so the whole-world resolver cannot find a definition to lower and the
//! choice is to implement the function or to refuse. The three primops here
//! take type arguments, which the monomorphic primop table does not model.
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
    /// The uncaught, stack-free error boundary; its message is a lazy String.
    ErrorWithoutStackTrace,
    /// `GHC.Base.eqString :: String -> String -> Bool`.
    EqString,
    /// `GHC.List.elem :: forall a. Eq a => a -> [a] -> Bool`.
    Elem,
    /// `Data.OldList.isPrefixOf :: forall a. Eq a => [a] -> [a] -> Bool`.
    IsPrefixOf,
    /// `compare :: [Char] -> [Char] -> Ordering`, `Ord [Char]`'s specialised method.
    CompareString,
    /// The primop `dataToTag# :: forall a. a -> Int#`: its argument's constructor, from zero.
    DataToTag,
    /// The primop `reallyUnsafePtrEquality#`: whether two lifted values are one heap object.
    PointerEquality,
    /// The primop `tagToEnum# :: forall a. Int# -> a`, at an enumeration type.
    TagToEnum,
    /// `GHC.Base.map :: forall a b. (a -> b) -> [a] -> [b]`.
    Map,
    /// `GHC.List.filter :: forall a. (a -> Bool) -> [a] -> [a]`.
    Filter,
    /// `GHC.List.takeWhile :: forall a. (a -> Bool) -> [a] -> [a]`.
    TakeWhile,
    /// `GHC.List.dropWhile :: forall a. (a -> Bool) -> [a] -> [a]`.
    DropWhile,
    /// `GHC.List.reverse :: forall a. [a] -> [a]`.
    Reverse,
    /// `GHC.List.reverse1 :: forall a. [a] -> [a] -> [a]`, `reverse`'s accumulating loop.
    ReverseOnto,
    /// `GHC.List.$wlenAcc :: forall a. [a] -> Int# -> Int#`, `lenAcc`'s call-by-value worker.
    Length,
    /// `GHC.Base.++_$s++ :: forall a. a -> [a] -> [a] -> [a]`, which base's rule
    /// `SC:++0` makes `(x : xs) ++ ys`.
    ConsAppend,
}

/// The `==` a call's `Eq` dictionary supplies, read from the dictionary itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Equality {
    /// `GHC.Classes.eqChar`, from `$fEqChar`.
    Char,
    /// `Eq [a]`'s `==` over `eqChar`, from the `Eq [Char]` specialisation of `$fEqList`.
    String,
}

impl External {
    /// How many type arguments precede the value arguments.
    pub fn type_arity(self) -> usize {
        match self {
            External::Append
            | External::Elem
            | External::IsPrefixOf
            | External::DataToTag
            | External::TagToEnum
            | External::Filter
            | External::TakeWhile
            | External::DropWhile
            | External::Reverse
            | External::ReverseOnto
            | External::Length
            | External::ConsAppend => 1,
            External::ErrorWithoutStackTrace | External::Map => 2,
            External::PointerEquality => 4,
            External::EqString | External::CompareString => 0,
        }
    }

    pub fn predicate(self) -> Option<super::Predicate> {
        match self {
            External::EqString => Some(super::Predicate::EqString),
            External::Elem => Some(super::Predicate::Elem),
            External::IsPrefixOf => Some(super::Predicate::IsPrefixOf),
            External::Append
            | External::ErrorWithoutStackTrace
            | External::CompareString
            | External::DataToTag
            | External::PointerEquality
            | External::TagToEnum
            | External::Map
            | External::Filter
            | External::TakeWhile
            | External::DropWhile
            | External::Reverse
            | External::ReverseOnto
            | External::Length
            | External::ConsAppend => None,
        }
    }

    pub fn list_function(self) -> Option<super::ListOp> {
        match self {
            External::Map => Some(super::ListOp::Map),
            External::Filter => Some(super::ListOp::Filter),
            External::TakeWhile => Some(super::ListOp::TakeWhile),
            External::DropWhile => Some(super::ListOp::DropWhile),
            External::Reverse => Some(super::ListOp::Reverse),
            External::ReverseOnto => Some(super::ListOp::ReverseOnto),
            External::Length => Some(super::ListOp::Length),
            External::ConsAppend => Some(super::ListOp::ConsAppend),
            External::Append
            | External::ErrorWithoutStackTrace
            | External::EqString
            | External::Elem
            | External::IsPrefixOf
            | External::CompareString
            | External::DataToTag
            | External::PointerEquality
            | External::TagToEnum => None,
        }
    }

    /// How many dictionary arguments follow the type arguments.
    pub fn dictionary_arity(self) -> usize {
        match self {
            External::Elem | External::IsPrefixOf => 1,
            External::Append
            | External::ErrorWithoutStackTrace
            | External::EqString
            | External::CompareString
            | External::DataToTag
            | External::PointerEquality
            | External::TagToEnum
            | External::Map
            | External::Filter
            | External::TakeWhile
            | External::DropWhile
            | External::Reverse
            | External::ReverseOnto
            | External::Length
            | External::ConsAppend => 0,
        }
    }

    /// How many runtime values follow the dictionaries.
    pub fn value_arity(self) -> usize {
        match self {
            External::Append
            | External::EqString
            | External::Elem
            | External::IsPrefixOf
            | External::CompareString
            | External::PointerEquality
            | External::Map
            | External::Filter
            | External::TakeWhile
            | External::DropWhile
            | External::ReverseOnto
            | External::Length => 2,
            External::ErrorWithoutStackTrace
            | External::DataToTag
            | External::TagToEnum
            | External::Reverse => 1,
            External::ConsAppend => 3,
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
            External::ErrorWithoutStackTrace => {
                // This backend currently carries lifted error results only.
                let Ty::Con { tycon, args } = &type_arguments[0] else {
                    return None;
                };
                if tycon.name != "$ghc-prim$GHC.Types$BoxedRep"
                    || args.len() != 1
                    || !matches!(&args[0], Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Types$Lifted" && args.is_empty())
                {
                    return None;
                }
                Some(arrow(
                    super::strings::string_ty(),
                    type_arguments[1].clone(),
                ))
            }
            External::Append => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(list.clone(), arrow(list.clone(), list)))
            }
            External::EqString => {
                let string = super::strings::string_ty();
                Some(arrow(string.clone(), arrow(string, super::data::bool_ty())))
            }
            External::Elem => Some(arrow(
                type_arguments[0].clone(),
                arrow(list_of(type_arguments[0].clone()), super::data::bool_ty()),
            )),
            External::IsPrefixOf => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(list.clone(), arrow(list, super::data::bool_ty())))
            }
            External::CompareString => {
                let string = super::strings::string_ty();
                Some(arrow(
                    string.clone(),
                    arrow(string, super::data::ordering_ty()),
                ))
            }
            External::DataToTag => {
                Some(arrow(type_arguments[0].clone(), super::primitive::int_ty()))
            }
            External::TagToEnum => {
                Some(arrow(super::primitive::int_ty(), type_arguments[0].clone()))
            }
            External::PointerEquality => {
                if !type_arguments[..2].iter().all(|levity| {
                    matches!(levity, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Types$Lifted" && args.is_empty())
                }) {
                    return None;
                }
                Some(arrow(
                    type_arguments[2].clone(),
                    arrow(type_arguments[3].clone(), super::primitive::int_ty()),
                ))
            }
            External::Map => Some(arrow(
                arrow(type_arguments[0].clone(), type_arguments[1].clone()),
                arrow(
                    list_of(type_arguments[0].clone()),
                    list_of(type_arguments[1].clone()),
                ),
            )),
            External::Filter | External::TakeWhile | External::DropWhile => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(
                    arrow(type_arguments[0].clone(), super::data::bool_ty()),
                    arrow(list.clone(), list),
                ))
            }
            External::Reverse => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(list.clone(), list))
            }
            External::ReverseOnto => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(list.clone(), arrow(list.clone(), list)))
            }
            External::Length => Some(arrow(
                list_of(type_arguments[0].clone()),
                arrow(super::primitive::int_ty(), super::primitive::int_ty()),
            )),
            External::ConsAppend => {
                let list = list_of(type_arguments[0].clone());
                Some(arrow(
                    type_arguments[0].clone(),
                    arrow(list.clone(), arrow(list.clone(), list)),
                ))
            }
        }
    }

    /// The element type the result's cells hold, for reading the constructor
    /// layouts out of the world.
    pub fn element(self, type_arguments: &[Ty]) -> Option<Ty> {
        match self {
            External::Append
            | External::Elem
            | External::IsPrefixOf
            | External::Map
            | External::Filter
            | External::TakeWhile
            | External::DropWhile
            | External::Reverse
            | External::ReverseOnto
            | External::Length
            | External::ConsAppend => type_arguments.first().cloned(),
            External::ErrorWithoutStackTrace | External::EqString | External::CompareString => {
                Some(super::strings::char_ty())
            }
            External::DataToTag | External::PointerEquality | External::TagToEnum => None,
        }
    }
}

/// `Eq [Char]` and `Eq [[Char]]` both specialise `$fEqList`, so the element type decides.
pub fn equality(module: &Module, dictionary: ExprId, element: &Ty) -> Option<Equality> {
    let Expr::Var { name, .. } = module.expr(dictionary) else {
        return None;
    };
    if module.reference(dictionary) != Some(h2r_core_ir::Ref::Global) {
        return None;
    }
    match name.as_str() {
        "$ghc-prim$GHC.Classes$$fEqChar" if element.is_char() => Some(Equality::Char),
        "$ghc-prim$GHC.Classes$$fEqList_$s$fEqList1"
            if element.list_elem().is_some_and(Ty::is_char) =>
        {
            Some(Equality::String)
        }
        _ => None,
    }
}

pub fn list_of(element: Ty) -> Ty {
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
/// its own and describes the kind of Id the entry names: ordinary, a primop,
/// or a call-by-value worker.
pub fn resolve(module: &Module, head: ExprId) -> Option<External> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    let info = module.id_info(head)?;
    if info.name != *name {
        return None;
    }
    let entry = match name.as_str() {
        "$base$GHC.Base$++" => Some(External::Append),
        "$base$GHC.Err$errorWithoutStackTrace" => Some(External::ErrorWithoutStackTrace),
        "$base$GHC.Base$eqString" => Some(External::EqString),
        "$base$GHC.List$elem" => Some(External::Elem),
        "$base$Data.OldList$isPrefixOf" => Some(External::IsPrefixOf),
        "$ghc-prim$GHC.Classes$$fOrdList_$s$ccompare1" => Some(External::CompareString),
        "$ghc-prim$GHC.Prim$dataToTag#" => Some(External::DataToTag),
        "$ghc-prim$GHC.Prim$reallyUnsafePtrEquality#" => Some(External::PointerEquality),
        "$ghc-prim$GHC.Prim$tagToEnum#" => Some(External::TagToEnum),
        "$base$GHC.Base$map" => Some(External::Map),
        "$base$GHC.List$filter" => Some(External::Filter),
        "$base$GHC.List$takeWhile" => Some(External::TakeWhile),
        "$base$GHC.List$dropWhile" => Some(External::DropWhile),
        "$base$GHC.List$reverse" => Some(External::Reverse),
        "$base$GHC.List$reverse1" => Some(External::ReverseOnto),
        "$base$GHC.List$$wlenAcc" => Some(External::Length),
        "$base$GHC.Base$++_$s++" => Some(External::ConsAppend),
        _ => None,
    }?;
    let primop = matches!(
        entry,
        External::DataToTag | External::PointerEquality | External::TagToEnum
    );
    let details = match entry {
        _ if primop => "[PrimOp]",
        External::Length => "[StrictWorker([!])]",
        _ => "",
    };
    (info.details == details && (!primop || info.arity as usize == entry.value_arity()))
        .then_some(entry)
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

    #[test]
    fn list_functions_take_base_signatures() {
        let con = |name: &str| Ty::Con {
            tycon: TyConId {
                name: name.into(),
                occ: String::new(),
                unique: String::new(),
            },
            args: vec![],
        };
        let (a, b) = (con("A"), con("B"));
        let (list_a, list_b) = (list_of(a.clone()), list_of(b.clone()));
        let bool_ty = super::super::data::bool_ty();
        let int = super::super::primitive::int_ty();
        let predicate = arrow(a.clone(), bool_ty);
        let cases = [
            (
                External::Map,
                vec![a.clone(), b.clone()],
                arrow(arrow(a.clone(), b), arrow(list_a.clone(), list_b)),
                2,
            ),
            (
                External::Filter,
                vec![a.clone()],
                arrow(predicate.clone(), arrow(list_a.clone(), list_a.clone())),
                2,
            ),
            (
                External::DropWhile,
                vec![a.clone()],
                arrow(predicate, arrow(list_a.clone(), list_a.clone())),
                2,
            ),
            (
                External::Reverse,
                vec![a.clone()],
                arrow(list_a.clone(), list_a.clone()),
                1,
            ),
            (
                External::Length,
                vec![a.clone()],
                arrow(list_a.clone(), arrow(int.clone(), int)),
                2,
            ),
            (
                External::ConsAppend,
                vec![a.clone()],
                arrow(a, arrow(list_a.clone(), arrow(list_a.clone(), list_a))),
                3,
            ),
        ];
        for (entry, types, signature, arity) in cases {
            assert_eq!(entry.signature(&types), Some(signature), "{entry:?}");
            assert_eq!(entry.value_arity(), arity, "{entry:?}");
            assert_eq!(entry.dictionary_arity(), 0, "{entry:?}");
            assert!(entry.signature(&types[1..]).is_none(), "{entry:?}");
            assert_eq!(
                entry.list_function().map(super::super::ListOp::external),
                Some(entry)
            );
        }
    }

    #[test]
    fn stack_free_errors_require_lifted_rep_and_preserve_function_results() {
        let con = |name: &str, args| Ty::Con {
            tycon: TyConId {
                name: name.into(),
                occ: String::new(),
                unique: String::new(),
            },
            args,
        };
        let rep = con(
            "$ghc-prim$GHC.Types$BoxedRep",
            vec![con("$ghc-prim$GHC.Types$Lifted", vec![])],
        );
        let result = arrow(
            super::super::strings::string_ty(),
            super::super::strings::string_ty(),
        );
        let entry = External::ErrorWithoutStackTrace;
        assert_eq!(
            entry.signature(&[rep.clone(), result.clone()]),
            Some(arrow(super::super::strings::string_ty(), result.clone()))
        );
        assert!(entry.signature(&[rep]).is_none());
        assert!(
            entry
                .signature(&[con("$ghc-prim$GHC.Types$IntRep", vec![]), result])
                .is_none()
        );
        assert_eq!(entry.value_arity(), 1);
    }
}
