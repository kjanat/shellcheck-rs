//! The cross-milestone link: which of M1's thunk sites are M2.2's tuples.
//!
//! [M1](crate::laziness) counts the local bindings that would still have to
//! be emitted as deferred evaluation, and attributes a large share of them
//! to `ds…` desugar bindings. That is not a coincidence: the desugarer turns
//! a lazy tuple pattern `~(b, s, w)` into *one selector thunk per field* —
//! `let ds1 = case t of (a, _, _) -> a` — and a field-wise re-tupling is the
//! same shape written forwards.
//!
//! If the tuple those selectors read is proven removable **and** the
//! [independent verifier](crate::verify) re-derives that verdict, the
//! selector does not survive scalar replacement: the field is bound at the
//! scrutiny (or arrives as a scalar result), so there is nothing left to
//! defer. Those thunk sites are *explained by tuple transport* — they
//! disappear as a consequence of M2.2, not as work of their own.
//!
//! The rule is deliberately narrow, because over-claiming here would make
//! the M1 table lie:
//!
//! * only a binding M1 itself calls a potential thunk site counts;
//! * only an RHS that *is* the lazy selection ([`T3_SELECTED`]) or the
//!   field-wise copy ([`T4_RETUPLE`]) counts — not a binding that merely
//!   mentions a field;
//! * and only over a tuple that is `ScalarReplace`/`WorkerReturn` *and*
//!   verified. A `Preserve` or `Unresolved` tuple keeps its box, so its
//!   selector thunks stay.

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{ExprId, Module};
use serde::Serialize;

use crate::laziness::{Census, Fate, Origin, Sink};
use crate::tuples::{T1_LET_BOUND, T3_SELECTED, T4_RETUPLE, TupleCensus, TupleFlow, TupleUse};

/// One M1 thunk site that tuple normalisation removes.
#[derive(Debug, Clone, Serialize)]
pub struct Explained {
    pub module: String,
    pub occ: String,
    pub origin: Origin,
    pub fate: Fate,
    /// The `let` and its right-hand side: the key M1 reports this binding
    /// under.
    pub let_node: ExprId,
    pub rhs: ExprId,
    /// [`T3_SELECTED`] or [`T4_RETUPLE`].
    pub rule: &'static str,
    /// The removable construction the RHS reads.
    pub over: ExprId,
    pub memo: bool,
    pub under_lambda: bool,
    pub shared: bool,
}

/// One row of the M1 table, before and after tuple normalisation.
#[derive(Debug, Clone, Serialize)]
pub struct Row {
    pub label: &'static str,
    pub before: usize,
    pub explained: usize,
}

impl Row {
    pub fn after(&self) -> usize {
        self.before - self.explained
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct ThunkLink {
    /// M1's potential thunk sites over the selected modules.
    pub thunk_sites: usize,
    pub explained: Vec<Explained>,
    /// Thunk sites that *hold* a normalised tuple: the binding's right-hand
    /// side is the tuple itself ([`T1_LET_BOUND`]), so after scalar
    /// replacement there is no box left for the binding to hold — it
    /// becomes *n* scalar bindings.
    ///
    /// Reported **beside** [`ThunkLink::explained`] and never folded into
    /// it. The milestone's criterion is the deferred *selection*
    /// disappearing; whether the *n* scalars that replace one of these
    /// bindings are themselves thunks is a question for the let census to
    /// answer again after the rewrite, not one this link may answer now.
    pub holds: Vec<Explained>,
    /// The thunk-site rows of the M1 table.
    pub fates: Vec<Row>,
    /// The memo split: captured by a many-entry lambda / shared on a path.
    pub memo: Vec<Row>,
    /// By binder origin.
    pub origins: Vec<(Origin, usize, usize)>,
    /// By the rule that explains it.
    pub by_rule: BTreeMap<&'static str, usize>,
    /// The M2 census' tuple-attributed lazy argument sites (the 1,321):
    /// how many become a scalar binding because their tuple is removable
    /// and verified.
    pub sites: usize,
    pub sites_explained: usize,
    /// …of those, by representation.
    pub sites_explained_boxed: usize,
    pub sites_explained_unboxed: usize,
}

impl ThunkLink {
    /// Thunk sites that survive tuple normalisation.
    pub fn remaining(&self) -> usize {
        self.thunk_sites - self.explained.len()
    }

    /// The invariant this whole section exists to state: every thunk site
    /// is either explained by tuple transport or still there, and the rows
    /// of the table partition the same population.
    pub fn check(&self) {
        assert!(
            self.explained.len() <= self.thunk_sites,
            "more thunk sites explained than exist"
        );
        assert_eq!(
            self.remaining() + self.explained.len(),
            self.thunk_sites,
            "remaining thunk sites + explained must be the M1 population"
        );
        let before: usize = self.fates.iter().map(|r| r.before).sum();
        let explained: usize = self.fates.iter().map(|r| r.explained).sum();
        assert_eq!(before, self.thunk_sites, "the fate rows must cover M1");
        assert_eq!(
            explained,
            self.explained.len(),
            "every explained thunk site lands in exactly one fate row"
        );
        let by_origin: usize = self.origins.iter().map(|(_, _, e)| e).sum();
        assert_eq!(
            by_origin,
            self.explained.len(),
            "every explained thunk site lands in exactly one origin row"
        );
        let by_rule: usize = self.by_rule.values().sum();
        assert_eq!(
            by_rule,
            self.explained.len(),
            "every explained thunk site is explained by exactly one rule"
        );
        for r in self.fates.iter().chain(&self.memo) {
            assert!(
                r.explained <= r.before,
                "{}: explained ({}) exceeds the population ({})",
                r.label,
                r.explained,
                r.before
            );
        }
        let held: HashSet<(&str, ExprId, ExprId)> = self
            .holds
            .iter()
            .map(|e| (e.module.as_str(), e.let_node, e.rhs))
            .collect();
        assert_eq!(held.len(), self.holds.len(), "a holder is counted once");
        for e in &self.explained {
            assert!(
                !held.contains(&(e.module.as_str(), e.let_node, e.rhs)),
                "a binding is a selector or a holder, never both"
            );
        }
        assert!(self.holds.len() + self.explained.len() <= self.thunk_sites);
        assert!(self.sites_explained <= self.sites);
        assert_eq!(
            self.sites_explained,
            self.sites_explained_boxed + self.sites_explained_unboxed
        );
    }
}

/// Nodes whose value is a lazy selection or a field-wise copy over a tuple
/// that this milestone actually removes.
fn explaining_nodes(tc: &TupleCensus<'_>) -> HashMap<(String, ExprId), (&'static str, ExprId)> {
    let mut out: HashMap<(String, ExprId), (&'static str, ExprId)> = HashMap::new();
    let normalised: Vec<&TupleFlow> = tc.flows.iter().filter(|f| tc.is_normalised(f)).collect();
    for f in normalised {
        for u in &f.consumers {
            match *u {
                TupleUse::Selected { case, .. } => {
                    out.insert((f.module.clone(), case), (T3_SELECTED, f.construction));
                }
                TupleUse::Retupled { outer } => {
                    out.insert((f.module.clone(), outer), (T4_RETUPLE, f.construction));
                }
                _ => {}
            }
        }
    }
    out
}

/// Right-hand sides that *are* a normalised tuple: the value locations
/// [`T1_LET_BOUND`] proved were bound to a binder. Both the node the walk
/// recorded and its cast-stripped form, since a let right-hand side the
/// simplifier left a cast on is the same binding.
fn holding_nodes(
    tc: &TupleCensus<'_>,
    by_name: &HashMap<&str, &Module>,
) -> HashMap<(String, ExprId), ExprId> {
    let mut out: HashMap<(String, ExprId), ExprId> = HashMap::new();
    for f in tc.flows.iter().filter(|f| tc.is_normalised(f)) {
        let Some(m) = by_name.get(f.module.as_str()) else {
            continue;
        };
        for e in f.evidence.iter().filter(|e| e.rule == T1_LET_BOUND) {
            for n in &e.nodes {
                out.insert((f.module.clone(), *n), f.construction);
                out.insert((f.module.clone(), m.strip(*n)), f.construction);
            }
        }
    }
    out
}

/// Compute the link. `modules` must be the same set the two censuses were
/// built over.
pub fn link(census: &Census, tc: &TupleCensus<'_>, modules: &[&Module]) -> ThunkLink {
    let by_name: HashMap<&str, &Module> = modules.iter().map(|m| (m.name.as_str(), *m)).collect();
    let nodes = explaining_nodes(tc);
    let holds = holding_nodes(tc, &by_name);

    let mut out = ThunkLink::default();
    let thunks: Vec<&crate::laziness::BindingReport> = census
        .bindings
        .iter()
        .filter(|b| b.fate != Fate::NotAThunk)
        .collect();
    out.thunk_sites = thunks.len();

    // Keyed by let node + binding, so that a binding is explained once.
    let mut seen: HashSet<(String, ExprId, ExprId)> = HashSet::new();
    for b in &thunks {
        let Some(m) = by_name.get(b.module.as_str()) else {
            continue;
        };
        let rhs = m.strip(b.rhs);
        let Some((rule, over)) = nodes.get(&(b.module.clone(), rhs)) else {
            continue;
        };
        if !seen.insert((b.module.clone(), b.let_node, b.rhs)) {
            continue;
        }
        out.explained.push(Explained {
            module: b.module.clone(),
            occ: b.occ.clone(),
            origin: b.origin,
            fate: b.fate,
            let_node: b.let_node,
            rhs: b.rhs,
            rule,
            over: *over,
            memo: b.fate == Fate::Memo,
            under_lambda: matches!(b.sink, Sink::UnderLambda { .. }),
            shared: b.fate == Fate::Memo && !matches!(b.sink, Sink::UnderLambda { .. }),
        });
        *out.by_rule.entry(rule).or_default() += 1;
    }

    // The adjacent population, reported on its own line: bindings that hold
    // the box rather than defer a selection out of it.
    for b in &thunks {
        let Some(m) = by_name.get(b.module.as_str()) else {
            continue;
        };
        let over = holds
            .get(&(b.module.clone(), b.rhs))
            .or_else(|| holds.get(&(b.module.clone(), m.strip(b.rhs))));
        let Some(over) = over else { continue };
        if seen.contains(&(b.module.clone(), b.let_node, b.rhs)) {
            continue;
        }
        out.holds.push(Explained {
            module: b.module.clone(),
            occ: b.occ.clone(),
            origin: b.origin,
            fate: b.fate,
            let_node: b.let_node,
            rhs: b.rhs,
            rule: T1_LET_BOUND,
            over: *over,
            memo: b.fate == Fate::Memo,
            under_lambda: matches!(b.sink, Sink::UnderLambda { .. }),
            shared: b.fate == Fate::Memo && !matches!(b.sink, Sink::UnderLambda { .. }),
        });
    }

    let explained_keys: HashSet<(String, ExprId, ExprId)> = out
        .explained
        .iter()
        .map(|e| (e.module.clone(), e.let_node, e.rhs))
        .collect();
    let is_explained = |b: &crate::laziness::BindingReport| {
        explained_keys.contains(&(b.module.clone(), b.let_node, b.rhs))
    };

    for (fate, label) in [
        (Fate::SinkEager, "sinkable, lands in an evaluating position"),
        (Fate::SinkLazyPosition, "sinkable, lands in a lazy position"),
        (Fate::Memo, "memoisation required"),
        (Fate::Recursive, "recursive value"),
        (Fate::Unknown, "unknown"),
    ] {
        out.fates.push(Row {
            label,
            before: thunks.iter().filter(|b| b.fate == fate).count(),
            explained: thunks
                .iter()
                .filter(|b| b.fate == fate && is_explained(b))
                .count(),
        });
    }
    let memo: Vec<&&crate::laziness::BindingReport> =
        thunks.iter().filter(|b| b.fate == Fate::Memo).collect();
    let lam = |b: &crate::laziness::BindingReport| matches!(b.sink, Sink::UnderLambda { .. });
    out.memo = vec![
        Row {
            label: "captured by a many-entry lambda",
            before: memo.iter().filter(|b| lam(b)).count(),
            explained: memo.iter().filter(|b| lam(b) && is_explained(b)).count(),
        },
        Row {
            label: "shared on one path",
            before: memo.iter().filter(|b| !lam(b)).count(),
            explained: memo.iter().filter(|b| !lam(b) && is_explained(b)).count(),
        },
    ];
    for origin in [
        Origin::Dictionary,
        Origin::FloatOut,
        Origin::Desugar,
        Origin::Eta,
        Origin::WorkerOrSpec,
        Origin::Join,
        Origin::User,
    ] {
        out.origins.push((
            origin,
            thunks.iter().filter(|b| b.origin == origin).count(),
            thunks
                .iter()
                .filter(|b| b.origin == origin && is_explained(b))
                .count(),
        ));
    }

    // The M2 lazy-argument sites: an argument of a tuple construction that
    // is normalised becomes a scalar binding, so the lazy position is gone.
    for s in &tc.accounting.sites {
        out.sites += 1;
        let Some(i) = s.flow else { continue };
        if !tc.is_normalised(&tc.flows[i]) {
            continue;
        }
        out.sites_explained += 1;
        if s.boxed {
            out.sites_explained_boxed += 1;
        } else {
            out.sites_explained_unboxed += 1;
        }
    }

    out.check();
    out
}
