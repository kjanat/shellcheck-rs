//! The binding scope of a module, and the one lookup every signature
//! question goes through.
//!
//! GHC does not keep the `IdInfo` on occurrence `Var`s of local ids up to
//! date: the demand signature and arity on an occurrence can be stale. The
//! binder at the binding site is authoritative. The id table the plugin
//! dumps is keyed by unique but populated from occurrences, so for anything
//! bound in this module it may disagree with the binder. Imported ids have
//! no binding site here; for them the id table is all there is.
//!
//! Every consumer that needs the arity or demand signature of a head
//! ([`crate::shape`] for argument position and partial-application shape,
//! [`crate::callee`] for resolution) asks [`Scope::head_sig`], so they can
//! never disagree about which source they read.

use std::collections::HashMap;

use h2r_core_ir::{BinderId, DataConInfo, Demand, Expr, ExprId, Module};
use serde::Serialize;

/// How a unique is bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum BindSite {
    Top,
    Let,
    Lam,
    CaseBinder,
    AltBinder,
}

/// Where and how a unique is bound in this module.
#[derive(Debug, Clone, Copy)]
pub struct BindInfo {
    pub site: BindSite,
    pub binder: BinderId,
    /// The right-hand side, for let- and top-level-bound ids.
    pub rhs: Option<ExprId>,
}

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

/// A module plus its binding-site index.
pub struct Scope<'m> {
    pub m: &'m Module,
    sites: HashMap<&'m str, BindInfo>,
}

impl<'m> Scope<'m> {
    pub fn new(m: &'m Module) -> Scope<'m> {
        let mut sites = HashMap::new();
        let mut put = |b: BinderId, site: BindSite, rhs: Option<ExprId>| {
            sites.insert(
                m.binder(b).unique.as_str(),
                BindInfo {
                    site,
                    binder: b,
                    rhs,
                },
            );
        };
        for bind in &m.top {
            for p in &bind.pairs {
                put(p.binder, BindSite::Top, Some(p.rhs));
            }
        }
        for e in &m.exprs {
            match e {
                Expr::Lam { binder, .. } => put(*binder, BindSite::Lam, None),
                Expr::Let { bind, .. } => {
                    for p in &bind.pairs {
                        put(p.binder, BindSite::Let, Some(p.rhs));
                    }
                }
                Expr::Case { binder, alts, .. } => {
                    put(*binder, BindSite::CaseBinder, None);
                    for a in alts {
                        for b in &a.binders {
                            put(*b, BindSite::AltBinder, None);
                        }
                    }
                }
                _ => {}
            }
        }
        Scope { m, sites }
    }

    /// The binding site of a unique, if it is bound in this module.
    pub fn site(&self, unique: &str) -> Option<BindInfo> {
        self.sites.get(unique).copied()
    }

    /// The binding site of the variable at `head`, if it is bound here.
    pub fn site_of(&self, head: ExprId) -> Option<BindInfo> {
        match self.m.expr(head) {
            Expr::Var { unique, .. } => self.site(unique),
            _ => None,
        }
    }

    /// The signature of the variable at `head`: from its binding site when
    /// it is bound in this module, from the id table otherwise. `None` when
    /// `head` is not a variable or nothing at all is known about it.
    pub fn head_sig(&self, head: ExprId) -> Option<HeadSig<'m>> {
        let Expr::Var { unique, .. } = self.m.expr(head) else {
            return None;
        };
        if let Some(bound) = self.site(unique) {
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
        let info = self.m.ids.get(unique)?;
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
