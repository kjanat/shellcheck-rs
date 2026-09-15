//! The one lookup every signature question goes through.
//!
//! Variable *identity* is not decided here: it is decided once, when the
//! arena is built, by [`h2r_core_ir::Module::resolve`] — every local `Var`
//! occurrence gets the [`BinderId`] that actually binds it, and nothing
//! downstream ever keys by, looks up by, or compares a local unique string.
//! (Uniques are not unique in an optimised dump; see that function.) **No
//! unique is used here at all**: the one lookup that leaves this module is
//! the linkage key into the imported-id table, and since dump format 5 the
//! key is the *stable name* — unit, module and occurrence — of an
//! occurrence the resolver has already classified as
//! [`h2r_core_ir::Ref::Global`], never its unique.
//!
//! What this module adds on top of identity is the *signature* question.
//! GHC does not keep the `IdInfo` on occurrence `Var`s of local ids up to
//! date: the demand signature and arity on an occurrence can be stale, and
//! the binder at the binding site is authoritative. The id table the plugin
//! dumps is keyed by stable name but populated from occurrences, so for
//! anything bound in this module it may disagree with the binder. Imported ids have
//! no binding site here; for them the id table is all there is.
//!
//! Every consumer that needs the arity or demand signature of a head
//! ([`crate::shape`] for argument position and partial-application shape,
//! [`crate::callee`] for resolution) asks [`Scope::head_sig`], so they can
//! never disagree about which source they read.

use h2r_core_ir::{BinderId, DataConInfo, Demand, Expr, ExprId, Module};
use serde::Serialize;

pub use h2r_core_ir::{BindInfo, BindSite};

/// Which source a [`HeadSig`] was read from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SigSource {
    /// The binder at the binding site in this module.
    BindingSite(BindSite),
    /// The imported-id table: the id is not bound in this module.
    IdTable,
}

/// What is known about the head of an application, from the authoritative
/// source. Two arities live here and they are deliberately not conflated:
///
/// * [`HeadSig::arity`] is GHC's `idArity`: how many value arguments the
///   head takes before it does any work. Fewer arguments than this is a
///   partial application, a value.
/// * [`HeadSig::dmd_args`] is the demand signature, whose length is the
///   *signature arity*. The per-argument demands hold only once a call
///   supplies at least that many value arguments; an undersaturated call
///   unleashes none of them.
#[derive(Debug, Clone, Copy)]
pub struct HeadSig<'m> {
    pub source: SigSource,
    pub arity: u32,
    pub dmd_args: &'m [Demand],
    pub diverges: bool,
    pub data_con: Option<&'m DataConInfo>,
    pub is_class_op: bool,
}

impl HeadSig<'_> {
    /// Signature arity: the number of value arguments a call needs before
    /// the argument demands apply.
    pub fn sig_arity(&self) -> usize {
        self.dmd_args.len()
    }

    /// Does a call with `n_value_args` arguments unleash the signature?
    pub fn unleashed_by(&self, n_value_args: usize) -> bool {
        n_value_args >= self.sig_arity()
    }
}

/// A module, viewed through its signatures. Identity questions are
/// forwarded straight to the IR so there is only ever one answer.
pub struct Scope<'m> {
    pub m: &'m Module,
}

impl<'m> Scope<'m> {
    pub fn new(m: &'m Module) -> Scope<'m> {
        Scope { m }
    }

    /// The binder a `Var` occurrence refers to; `None` for an import.
    pub fn resolve(&self, occ: ExprId) -> Option<BinderId> {
        self.m.resolve(occ)
    }

    /// Where a binder is bound.
    pub fn binding(&self, b: BinderId) -> BindInfo {
        self.m.binding(b)
    }

    /// Every occurrence of a binder, in pre-order.
    pub fn occurrences(&self, b: BinderId) -> &'m [ExprId] {
        self.m.occurrences(b)
    }

    /// The binding site of the variable at `head`, if it is bound here.
    pub fn binding_of(&self, head: ExprId) -> Option<BindInfo> {
        self.m.binding_of(head)
    }

    /// The signature of the variable at `head`: from the binder it resolves
    /// to when it is bound in this module, from the id table otherwise.
    /// `None` when `head` is not a variable or nothing at all is known.
    pub fn head_sig(&self, head: ExprId) -> Option<HeadSig<'m>> {
        let Expr::Var { name, .. } = self.m.expr(head) else {
            return None;
        };
        if let Some(bound) = self.binding_of(head) {
            let b = self.m.binder(bound.binder);
            return Some(HeadSig {
                source: SigSource::BindingSite(bound.site),
                arity: b.arity.unwrap_or(0),
                dmd_args: b.dmd_sig.as_ref().map(|s| s.args.as_slice()).unwrap_or(&[]),
                diverges: b.dmd_sig.as_ref().is_some_and(|s| s.diverges),
                // Locals are never constructors or class methods.
                data_con: None,
                is_class_op: false,
            });
        }
        // Linkage, not identity: the resolver has already said this
        // occurrence is an import, so its stable name is the table key.
        let info = self.m.ids.get(name)?;
        Some(HeadSig {
            source: SigSource::IdTable,
            arity: info.arity,
            dmd_args: &info.dmd_sig.args,
            diverges: info.dmd_sig.diverges,
            data_con: info.data_con.as_ref(),
            is_class_op: info.is_class_op,
        })
    }
}
