//! Capture-safe type substitution and canonical type identity.
//!
//! Substitution renames a quantifier whose variable occurs free in a
//! replacement, so an argument's free variable can never be captured. Canonical
//! keys are built from the structured type — stable type-constructor names and
//! de Bruijn levels — never from GHC's rendering, and two closed types share a
//! key exactly when they are alpha-equivalent.

use std::borrow::Cow;
use std::collections::BTreeSet;

use h2r_core_ir::{Name, Ty, TyVarId};

/// An ordered type-variable substitution. Order is the source binding order,
/// which is what an instance key records; lookup is by type-variable unique,
/// which is an identity only inside one explicitly paired scope.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Substitution {
    bindings: Vec<(TyVarId, Ty)>,
}

impl Substitution {
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Bind one more variable. A repeated unique would make lookup ambiguous
    /// inside the same scope, so it is refused rather than shadowed silently.
    pub fn bind(&mut self, var: TyVarId, ty: Ty) -> Result<(), String> {
        if self
            .bindings
            .iter()
            .any(|(bound, _)| bound.unique == var.unique)
        {
            return Err("ambiguous type-variable scope in substitution".into());
        }
        self.bindings.push((var, ty));
        Ok(())
    }

    /// The bound types, in binding order.
    pub fn arguments(&self) -> Vec<Ty> {
        self.bindings.iter().map(|(_, ty)| ty.clone()).collect()
    }

    /// Substitute into `ty`, borrowing when nothing in the domain occurs free.
    pub fn apply<'a>(&self, ty: &'a Ty) -> Cow<'a, Ty> {
        if self.bindings.is_empty() {
            return Cow::Borrowed(ty);
        }
        let free = free_uniques(ty);
        if !self
            .bindings
            .iter()
            .any(|(var, _)| free.contains(var.unique.as_str()))
        {
            return Cow::Borrowed(ty);
        }
        let mut result = ty.clone();
        for (var, replacement) in &self.bindings {
            substitute_capture_safe(&mut result, &var.unique, replacement);
        }
        Cow::Owned(result)
    }
}

/// Replace every free occurrence of `unique`, renaming any quantifier that
/// would capture a free variable of `replacement`.
pub fn substitute_capture_safe(ty: &mut Ty, unique: &str, replacement: &Ty) {
    let captured = free_uniques(replacement);
    if !captured.is_empty() {
        let mut used = all_uniques(ty);
        used.extend(captured.iter().cloned());
        freshen(ty, &captured, &mut used);
    }
    substitute_one(ty, unique, replacement);
    while fold_constructor_applications(ty) {}
}

/// GHC's `mkAppTy` keeps a constructor application's arguments on the
/// constructor, so `m (a, w)` at `m := Identity` is `Identity (a, w)`.
fn fold_constructor_applications(ty: &mut Ty) -> bool {
    let mut folded = false;
    let mut work = vec![ty];
    while let Some(node) = work.pop() {
        if let Ty::App { fun, arg } = node
            && let Ty::Con { tycon, args } = fun.as_mut()
        {
            let mut args = std::mem::take(args);
            args.push(std::mem::replace(
                arg.as_mut(),
                Ty::Opaque {
                    pretty: String::new(),
                },
            ));
            *node = Ty::Con {
                tycon: tycon.clone(),
                args,
            };
            folded = true;
        }
        match node {
            Ty::Var(_) | Ty::Lit { .. } | Ty::Opaque { .. } => {}
            Ty::Con { args, .. } => work.extend(args.iter_mut()),
            Ty::App { fun, arg } => work.extend([fun.as_mut(), arg.as_mut()]),
            Ty::Fun { mult, arg, res } => {
                work.extend([mult.as_mut(), arg.as_mut(), res.as_mut()]);
            }
            Ty::ForAll { body, .. } => work.push(body.as_mut()),
        }
    }
    folded
}

/// Replace every free occurrence of `unique`. A quantifier that rebinds it
/// shadows the substitution, so its body is left alone.
fn substitute_one(ty: &mut Ty, unique: &str, replacement: &Ty) {
    let mut work = vec![ty];
    while let Some(node) = work.pop() {
        match node {
            Ty::Var(var) if var.unique == unique => *node = replacement.clone(),
            Ty::Var(_) | Ty::Lit { .. } | Ty::Opaque { .. } => {}
            Ty::Con { args, .. } => work.extend(args.iter_mut()),
            Ty::App { fun, arg } => work.extend([fun.as_mut(), arg.as_mut()]),
            Ty::Fun { mult, arg, res } => {
                work.extend([mult.as_mut(), arg.as_mut(), res.as_mut()]);
            }
            Ty::ForAll { binder, body } if binder.unique != unique => work.push(body.as_mut()),
            Ty::ForAll { .. } => {}
        }
    }
}

/// Rename every quantifier whose variable is in `avoid`, so a later
/// substitution cannot move a free variable under a binder that captures it.
fn freshen(ty: &mut Ty, avoid: &BTreeSet<Name>, used: &mut BTreeSet<Name>) {
    let mut work = vec![ty];
    while let Some(node) = work.pop() {
        match node {
            Ty::Var(_) | Ty::Lit { .. } | Ty::Opaque { .. } => {}
            Ty::Con { args, .. } => work.extend(args.iter_mut()),
            Ty::App { fun, arg } => work.extend([fun.as_mut(), arg.as_mut()]),
            Ty::Fun { mult, arg, res } => {
                work.extend([mult.as_mut(), arg.as_mut(), res.as_mut()]);
            }
            Ty::ForAll { binder, body } => {
                if avoid.contains(&binder.unique) {
                    let fresh = fresh_unique(used);
                    substitute_one(
                        body,
                        &binder.unique,
                        &Ty::Var(TyVarId {
                            name: binder.name.clone(),
                            occ: binder.occ.clone(),
                            unique: fresh.clone(),
                        }),
                    );
                    binder.unique = fresh;
                }
                work.push(body.as_mut());
            }
        }
    }
}

fn fresh_unique(used: &mut BTreeSet<Name>) -> Name {
    let mut n = used.len();
    loop {
        let candidate = Name::from(format!("h2rSpec{n}"));
        if used.insert(candidate.clone()) {
            return candidate;
        }
        n += 1;
    }
}

/// Every type-variable unique that occurs free.
pub fn free_uniques(ty: &Ty) -> BTreeSet<Name> {
    let mut free = BTreeSet::new();
    let mut bound: Vec<&str> = Vec::new();
    let mut work = vec![(ty, 0usize)];
    while let Some((node, depth)) = work.pop() {
        bound.truncate(depth);
        match node {
            Ty::Var(var) => {
                if !bound.contains(&var.unique.as_str()) {
                    free.insert(var.unique.clone());
                }
            }
            Ty::Lit { .. } | Ty::Opaque { .. } => {}
            Ty::Con { args, .. } => work.extend(args.iter().map(|arg| (arg, depth))),
            Ty::App { fun, arg } => {
                work.extend([(fun.as_ref(), depth), (arg.as_ref(), depth)]);
            }
            Ty::Fun { mult, arg, res } => work.extend([
                (mult.as_ref(), depth),
                (arg.as_ref(), depth),
                (res.as_ref(), depth),
            ]),
            Ty::ForAll { binder, body } => {
                bound.push(&binder.unique);
                work.push((body, depth + 1));
            }
        }
    }
    free
}

/// Every type-variable unique mentioned, bound or free.
fn all_uniques(ty: &Ty) -> BTreeSet<Name> {
    let mut seen = BTreeSet::new();
    let mut work = vec![ty];
    while let Some(node) = work.pop() {
        match node {
            Ty::Var(var) => {
                seen.insert(var.unique.clone());
            }
            Ty::Lit { .. } | Ty::Opaque { .. } => {}
            Ty::Con { args, .. } => work.extend(args.iter()),
            Ty::App { fun, arg } => work.extend([fun.as_ref(), arg.as_ref()]),
            Ty::Fun { mult, arg, res } => {
                work.extend([mult.as_ref(), arg.as_ref(), res.as_ref()]);
            }
            Ty::ForAll { binder, body } => {
                seen.insert(binder.unique.clone());
                work.push(body);
            }
        }
    }
    seen
}

enum Token<'a> {
    Node(&'a Ty, usize),
    Text(&'static str),
}

/// A canonical, injective rendering of the *structured* type. Bound variables
/// become de Bruijn indices and free ones keep their unique, so the key is
/// equal exactly when [`Ty::alpha_eq`] holds. Lengths frame every string, so
/// no name can be confused with the syntax around it.
pub fn type_key(ty: &Ty) -> String {
    let mut out = String::new();
    let mut bound: Vec<&str> = Vec::new();
    let mut work = vec![Token::Node(ty, 0usize)];
    while let Some(token) = work.pop() {
        let (node, depth) = match token {
            Token::Text(text) => {
                out.push_str(text);
                continue;
            }
            Token::Node(node, depth) => (node, depth),
        };
        bound.truncate(depth);
        match node {
            Ty::Var(var) => match bound.iter().rposition(|u| *u == var.unique) {
                Some(level) => out.push_str(&format!("B{};", bound.len() - 1 - level)),
                None => out.push_str(&format!("F{}", framed(&var.unique))),
            },
            Ty::Con { tycon, args } => {
                out.push_str(&format!("C{}{};", framed(&tycon.name), args.len()));
                work.push(Token::Text(")"));
                for arg in args.iter().rev() {
                    work.push(Token::Node(arg, depth));
                }
                out.push('(');
            }
            Ty::App { fun, arg } => {
                out.push_str("A(");
                work.push(Token::Text(")"));
                work.push(Token::Node(arg, depth));
                work.push(Token::Text(","));
                work.push(Token::Node(fun, depth));
            }
            Ty::Fun { mult, arg, res } => {
                out.push_str("U(");
                work.push(Token::Text(")"));
                work.push(Token::Node(res, depth));
                work.push(Token::Text(","));
                work.push(Token::Node(arg, depth));
                work.push(Token::Text(","));
                work.push(Token::Node(mult, depth));
            }
            Ty::ForAll { binder, body } => {
                out.push_str("Q(");
                work.push(Token::Text(")"));
                work.push(Token::Node(body, depth + 1));
                bound.push(&binder.unique);
            }
            Ty::Lit { kind, text } => {
                out.push_str(&format!("L{}{}", framed(kind), framed(text)));
            }
            Ty::Opaque { pretty } => out.push_str(&format!("O{}", framed(pretty))),
        }
    }
    out
}

/// Every type's key, framed so a list cannot be confused with another list.
pub fn type_list_key(types: &[Ty]) -> String {
    let mut out = format!("{};", types.len());
    for ty in types {
        let key = type_key(ty);
        out.push_str(&framed(&key));
    }
    out
}

fn framed(text: &str) -> String {
    format!("{}:{text}", text.len())
}

/// The greatest constructor nesting depth, used to detect an instance chain
/// whose type arguments grow without bound.
pub fn type_depth(ty: &Ty) -> usize {
    let mut deepest = 0;
    let mut work = vec![(ty, 1usize)];
    while let Some((node, depth)) = work.pop() {
        deepest = deepest.max(depth);
        match node {
            Ty::Var(_) | Ty::Lit { .. } | Ty::Opaque { .. } => {}
            Ty::Con { args, .. } => work.extend(args.iter().map(|arg| (arg, depth + 1))),
            Ty::App { fun, arg } => {
                work.extend([(fun.as_ref(), depth + 1), (arg.as_ref(), depth + 1)]);
            }
            Ty::Fun { mult, arg, res } => work.extend([
                (mult.as_ref(), depth + 1),
                (arg.as_ref(), depth + 1),
                (res.as_ref(), depth + 1),
            ]),
            Ty::ForAll { body, .. } => work.push((body, depth + 1)),
        }
    }
    deepest
}

#[cfg(test)]
mod tests {
    use super::*;
    use h2r_core_ir::TyConId;

    fn tv(unique: &str) -> TyVarId {
        TyVarId {
            name: format!("$_in${unique}").into(),
            occ: unique.into(),
            unique: unique.into(),
        }
    }

    fn con(name: &str, args: Vec<Ty>) -> Ty {
        Ty::Con {
            tycon: TyConId {
                name: name.into(),
                occ: name.into(),
                unique: name.into(),
            },
            args,
        }
    }

    fn arrow(arg: Ty, res: Ty) -> Ty {
        Ty::Fun {
            mult: Box::new(con("Many", vec![])),
            arg: Box::new(arg),
            res: Box::new(res),
        }
    }

    /// The quantifier is renamed rather than capturing the argument's free
    /// variable; the naive substitution this replaces would produce `b -> b`.
    #[test]
    fn substitution_renames_a_quantifier_that_would_capture() {
        let mut ty = Ty::ForAll {
            binder: tv("b"),
            body: Box::new(arrow(Ty::Var(tv("a")), Ty::Var(tv("b")))),
        };
        substitute_capture_safe(&mut ty, "a", &Ty::Var(tv("b")));
        let Ty::ForAll { binder, body } = &ty else {
            panic!("quantifier lost")
        };
        assert_ne!(binder.unique, "b", "the capturing binder kept its name");
        let Ty::Fun { arg, res, .. } = body.as_ref() else {
            panic!("arrow lost")
        };
        assert_eq!(**arg, Ty::Var(tv("b")), "the argument was captured");
        assert_eq!(**res, Ty::Var(binder.clone()));
        let captured = Ty::ForAll {
            binder: tv("b"),
            body: Box::new(arrow(Ty::Var(tv("b")), Ty::Var(tv("b")))),
        };
        assert!(!ty.alpha_eq(&captured));
    }

    #[test]
    fn a_substituted_constructor_takes_its_applied_arguments() {
        let app = |fun: Ty, arg: Ty| Ty::App {
            fun: Box::new(fun),
            arg: Box::new(arg),
        };
        let pair = con("(,)", vec![con("()", vec![]), con("W", vec![])]);
        let mut writer = arrow(
            app(Ty::Var(tv("m")), pair.clone()),
            app(app(Ty::Var(tv("m")), con("A", vec![])), con("B", vec![])),
        );
        substitute_capture_safe(&mut writer, "m", &con("Identity", vec![]));
        assert_eq!(
            writer,
            arrow(
                con("Identity", vec![pair]),
                con("Identity", vec![con("A", vec![]), con("B", vec![])]),
            )
        );
        let mut variable = app(Ty::Var(tv("m")), con("A", vec![]));
        substitute_capture_safe(&mut variable, "m", &Ty::Var(tv("n")));
        assert_eq!(variable, app(Ty::Var(tv("n")), con("A", vec![])));
    }

    #[test]
    fn a_rebinding_quantifier_shadows_the_substitution() {
        let shadowed = Ty::ForAll {
            binder: tv("a"),
            body: Box::new(Ty::Var(tv("a"))),
        };
        let mut ty = arrow(Ty::Var(tv("a")), shadowed.clone());
        substitute_capture_safe(&mut ty, "a", &con("Int", vec![]));
        let Ty::Fun { arg, res, .. } = &ty else {
            panic!("arrow lost")
        };
        assert_eq!(**arg, con("Int", vec![]));
        assert_eq!(**res, shadowed);
    }

    #[test]
    fn a_substitution_borrows_when_nothing_in_its_domain_occurs() {
        let mut subst = Substitution::default();
        subst.bind(tv("a"), con("Int", vec![])).unwrap();
        assert!(subst.bind(tv("a"), con("Char", vec![])).is_err());
        let untouched = con("List", vec![con("Char", vec![])]);
        assert!(matches!(subst.apply(&untouched), Cow::Borrowed(_)));
        let touched = con("List", vec![Ty::Var(tv("a"))]);
        assert_eq!(
            subst.apply(&touched).into_owned(),
            con("List", vec![con("Int", vec![])])
        );
        assert_eq!(subst.arguments(), vec![con("Int", vec![])]);
        assert!(Substitution::default().is_empty());
        assert_eq!(subst.len(), 1);
    }

    /// The key is equal exactly when the types are alpha-equivalent, so it can
    /// serve as an instance identity without re-deriving alpha-equivalence.
    #[test]
    fn canonical_keys_agree_with_alpha_equivalence() {
        let quantified = |u: &str| Ty::ForAll {
            binder: tv(u),
            body: Box::new(arrow(Ty::Var(tv(u)), con("Int", vec![]))),
        };
        let samples = vec![
            con("Int", vec![]),
            con("List", vec![con("Int", vec![])]),
            con("List", vec![con("Char", vec![])]),
            arrow(con("Int", vec![]), con("Char", vec![])),
            arrow(con("Char", vec![]), con("Int", vec![])),
            quantified("a"),
            quantified("b"),
            Ty::Var(tv("free")),
            Ty::Var(tv("other")),
            Ty::App {
                fun: Box::new(Ty::Var(tv("free"))),
                arg: Box::new(con("Int", vec![])),
            },
            Ty::Lit {
                kind: "Nat".into(),
                text: "1".into(),
            },
            Ty::Lit {
                kind: "Nat".into(),
                text: "2".into(),
            },
            Ty::Opaque {
                pretty: "co".into(),
            },
        ];
        for left in &samples {
            for right in &samples {
                assert_eq!(
                    type_key(left) == type_key(right),
                    left.alpha_eq(right),
                    "{left:?} vs {right:?}"
                );
            }
        }
        // Framing keeps neighbouring names from running together.
        assert_ne!(
            type_list_key(&[con("A", vec![]), con("BC", vec![])]),
            type_list_key(&[con("AB", vec![]), con("C", vec![])])
        );
        assert_ne!(type_list_key(&samples[..2]), type_list_key(&samples[..1]));
    }

    #[test]
    fn depth_grows_with_nesting() {
        let int = con("Int", vec![]);
        let list = con("List", vec![int.clone()]);
        assert!(type_depth(&int) < type_depth(&list));
        assert!(type_depth(&list) < type_depth(&con("List", vec![list.clone()])));
        assert!(type_depth(&arrow(int.clone(), int)) > 1);
        assert!(
            type_depth(&Ty::ForAll {
                binder: tv("a"),
                body: Box::new(list)
            }) > 2
        );
    }

    #[test]
    fn free_and_bound_uniques_are_separated() {
        let ty = Ty::ForAll {
            binder: tv("a"),
            body: Box::new(arrow(Ty::Var(tv("a")), Ty::Var(tv("b")))),
        };
        assert_eq!(free_uniques(&ty), BTreeSet::from([Name::from("b")]));
        assert_eq!(
            all_uniques(&ty),
            BTreeSet::from([Name::from("a"), Name::from("b")])
        );
        // A binder in one branch does not scope over its sibling.
        let siblings = con("Pair", vec![ty, Ty::Var(tv("a"))]);
        assert_eq!(
            free_uniques(&siblings),
            BTreeSet::from([Name::from("a"), Name::from("b")])
        );
    }
}
