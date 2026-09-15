//! Turning the M2.4 analyses' verdicts into the plain-data claim list
//! [`crate::verify_m24`] re-derives.
//!
//! The split is what keeps the verifier independent: it must not see
//! [`crate::dictflow`] or [`crate::higher`] at all, so the conversion lives
//! here instead — exactly as [`crate::m23`] assembles the M2.3 claims for
//! [`crate::verify_rep`]. **Nothing in this file derives anything.** It
//! reads verdicts already published and writes them down as data.

use crate::dictflow::{self, DictFlow, Outcome, Verdict as DVerdict};
use crate::higher::{self, Higher, Slot, Verdict as HVerdict};
use crate::verify_m24::{Claim, ClaimKind, ClaimSlot, Subject};
use h2r_core_ir::Module;

/// How a method target is written down, so that both sides name the same
/// binding: the defining module, the node the binding sits at, and the
/// name — an address, and not a derivation.
fn target_key(t: &dictflow::MethodTarget) -> String {
    format!("{}#{} {}", t.module, t.node, t.name)
}

/// Every **positive** claim the two milestones publish.
pub fn claims(modules: &[&Module]) -> (Vec<Claim>, DictFlow, Higher) {
    let dp = dictflow::Program::new(modules.iter().copied());
    let f = DictFlow::of_program(&dp);
    let hp = higher::Program::new(modules.iter().copied());
    let h = Higher::of_program(&hp);
    let mut out = Vec::new();

    // 1 — class-op sites: the method target, and the bounded dictionary set.
    for s in &f.sites {
        let keys: Vec<String> = s.set.keys().iter().cloned().collect();
        if let Outcome::Exact(t) = &s.outcome {
            out.push(Claim {
                kind: ClaimKind::SiteExact,
                subject: Subject::Site {
                    module: s.module.clone(),
                    node: s.node,
                },
                what: format!("{} node {} ({})", s.module, s.node, s.method),
                keys: keys.clone(),
                target: Some(target_key(t)),
                verdict: "Exact".into(),
                n: 1,
            });
        }
        if !s.set.is_top() && !keys.is_empty() {
            out.push(Claim {
                kind: ClaimKind::SiteBounded,
                subject: Subject::Site {
                    module: s.module.clone(),
                    node: s.node,
                },
                what: format!("{} node {} ({})", s.module, s.node, s.method),
                n: keys.len(),
                keys,
                target: None,
                verdict: "bounded".into(),
            });
        }
    }

    // 2 — dictionary parameters whose set the fixpoint bounded.
    for p in &f.params {
        if p.set.is_top() {
            continue;
        }
        let keys: Vec<String> = p.set.keys().iter().cloned().collect();
        out.push(Claim {
            kind: ClaimKind::ParamBounded,
            subject: Subject::Param {
                module: p.module.clone(),
                binder: p.binder,
            },
            what: format!("{} {}.{}#{}", p.module, p.owner, p.occ, p.index),
            n: keys.len(),
            keys,
            target: None,
            verdict: "bounded".into(),
        });
    }

    // 3 — erasure: the dictionary values…
    for (key, e) in dp.values.keys().zip(f.values.iter()) {
        if !matches!(
            e.verdict,
            DVerdict::Erasable
                | DVerdict::ErasableWithClone(_)
                | DVerdict::ErasableWithObligation(_)
        ) {
            continue;
        }
        out.push(Claim {
            kind: ClaimKind::ValueErasure,
            subject: Subject::Value { key: key.clone() },
            what: e.what.clone(),
            keys: vec![key.clone()],
            target: None,
            verdict: e.verdict.label().into(),
            n: e.instances,
        });
    }
    // …and the dictionary parameters.
    for (p, e) in f.params.iter().zip(f.param_erasure.iter()) {
        let n = match &e.verdict {
            DVerdict::Erasable | DVerdict::ErasableWithObligation(_) => 1,
            DVerdict::ErasableWithClone(n) => *n,
            _ => continue,
        };
        out.push(Claim {
            kind: ClaimKind::ParamErasure,
            subject: Subject::Param {
                module: p.module.clone(),
                binder: p.binder,
            },
            what: e.what.clone(),
            keys: p.set.keys().iter().cloned().collect(),
            target: None,
            verdict: e.verdict.label().into(),
            n,
        });
    }

    // 4 — the owner-level dictionary clone plans.
    for o in &f.owners {
        let Some(n) = o.clones else { continue };
        out.push(Claim {
            kind: ClaimKind::DictClonePlan,
            subject: Subject::DictOwner {
                module: o.module.clone(),
                owner: o.owner_binder,
            },
            what: format!("{} {}", o.module, o.owner),
            keys: Vec::new(),
            target: None,
            verdict: "clone plan".into(),
            n,
        });
    }

    // 5 — the higher-order verdicts.
    for b in &h.boundaries {
        let n = match &b.verdict {
            HVerdict::ExactClosure | HVerdict::TypeShapeUniform => 1,
            HVerdict::CloneRequired(n) | HVerdict::FiniteClosureSet(n) => *n,
            _ => continue,
        };
        let slot = match &b.slot {
            Slot::Param { .. } => ClaimSlot::Param {
                binder: b.binder.unwrap_or_default(),
            },
            Slot::Return { .. } => ClaimSlot::Return {
                binder: b.binder.unwrap_or_default(),
            },
            Slot::Field { con, index } => ClaimSlot::Field {
                con: con.clone(),
                index: *index,
            },
        };
        out.push(Claim {
            kind: ClaimKind::HigherVerdict,
            subject: Subject::Boundary {
                module: b.module.clone(),
                slot,
            },
            what: format!("{} {}", b.module, b.name),
            keys: b.set.keys().iter().cloned().collect(),
            target: None,
            verdict: b.verdict.label().into(),
            n,
        });
    }

    // 6 — the owner-level closure clone plans.
    for o in &h.owners {
        let Some(n) = o.clones else { continue };
        out.push(Claim {
            kind: ClaimKind::ClosureClonePlan,
            subject: Subject::ClosureOwner {
                module: o.module.clone(),
                owner: o.owner_binder,
            },
            what: format!("{} {}", o.module, o.owner),
            keys: Vec::new(),
            target: None,
            verdict: "clone plan".into(),
            n,
        });
    }

    (out, f, h)
}
