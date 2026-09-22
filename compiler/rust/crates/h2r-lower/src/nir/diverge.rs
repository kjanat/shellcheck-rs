//! Calls GHC proved do not return.
//!
//! `error`, `patError`, `errorEmptyList` and the rest of that family are
//! ordinary imported bindings whose bodies this world does not contain, so the
//! resolver cannot lower them and the external boundary refuses them. But a
//! call to one of them has no result to lower: GHC's own demand analysis has
//! already proved the call is a dead end, and a dead end needs a terminator
//! rather than a value.
//!
//! The evidence is `DmdSig`'s divergence, which the plugin records through
//! GHC's `isDeadEndDiv` — the predicate for "this does not return normally",
//! covering both `Diverges` and `ExnOrDiv`. It is a property of the binding
//! that GHC computed and wrote into the interface file, so it is available for
//! an imported Id at every optimisation level, and it is not a guess about
//! what a name means.
//!
//! The arity comes from the same signature. `<S><S>b` says the bottom holds
//! *after two arguments*; applied to one, `error` is a partial application and
//! an ordinary value. So the demand signature states both facts this rule
//! needs, and `IdInfo.arity` — which for an imported Id records what this
//! compilation inferred rather than what the function is — states neither.

use h2r_core_ir::{Expr, ExprId, Module};

/// A call GHC's demand analysis proved is a dead end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Divergent {
    /// The binding's stable name, for the runtime diagnostic. A dead end that
    /// is reached should say which call it was.
    pub name: String,
    /// How many value arguments the divergence holds at.
    pub arity: usize,
}

/// Does this occurrence name a binding GHC proved never returns?
///
/// The occurrence must be a global whose `IdInfo` is its own and describes an
/// ordinary Id: a class-method selector or a constructor worker is dispatch or
/// allocation, and neither is a dead end whatever its signature says.
pub fn resolve(module: &Module, head: ExprId) -> Option<Divergent> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    let info = module.id_info(head)?;
    if info.name != *name || !info.details.is_empty() {
        return None;
    }
    if !info.dmd_sig.diverges {
        return None;
    }
    Some(Divergent {
        name: name.clone(),
        arity: info.dmd_sig.args.len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The arity a dead end holds at is the demand signature's own argument
    /// count, so a partial application is not one.
    #[test]
    fn the_signature_states_the_arity_the_bottom_holds_at() {
        let two = Divergent {
            name: "$base$GHC.Err$error".into(),
            arity: 2,
        };
        assert_eq!(two.arity, 2);
        let one = Divergent {
            name: "$base$GHC.Err$errorWithoutStackTrace".into(),
            arity: 1,
        };
        assert_eq!(one.arity, 1);
        assert_ne!(one, two);
    }
}
