//! M2.3's own accounting, and its cross-milestone link.
//!
//! M2.2 states its milestone as one equation per representation —
//! `before = normalised + preserved + unsupported` — with *normalised*
//! meaning "removable **and** re-derived by the independent verifier". This
//! module does the same for M2.3, in the shape this milestone's question
//! takes rather than M2.2's:
//!
//! ```text
//! fields  total = proven-eager + proven-lazy + dead + unsupported
//! lists   total = advised + unsupported
//! text    total = advised + unsupported
//! ```
//!
//! and with the same rule pointing the same way: **any claim the
//! [verifier](crate::verify_rep) refused, for coverage or otherwise, is
//! counted as unsupported and never as proven.** A `Direct` field whose
//! timing only one walk established is not eager here; an
//! `IteratorCandidate` the verifier declined to re-derive is not advised.
//!
//! `proven-lazy` is the honest home of the verdicts M2.3 *can* stand
//! behind without a second walk: `Deferred` is a coverage-only verdict — a
//! wrong one loses an optimisation and cannot miscompile — so nothing
//! re-derives it and nothing needs to. `Recursive`, which *is* re-derived,
//! only counts as proven-lazy when it was.
//!
//! The second half is [`link`]: which of M1's 2,242 thunk sites stop being
//! thunks because of an M2.3 verdict, counted beside M2.2's tuple link and
//! disjoint from it, with `remaining + tuples + M2.3 = 2,242` asserted.

use std::collections::{BTreeMap, HashMap, HashSet};

use h2r_core_ir::{Expr, ExprId, Module};
use serde::Serialize;

use crate::fields::{FieldCensus, FieldRep, ObsKind};
use crate::laziness::{Census, Fate, Origin, Sink};
use crate::lists::{ListCensus, Recommendation, SpineDemand};
use crate::text::{Advisory, TextCensus};
use crate::views::{Verdicts, Verified};

//------------------------------------------------------------------------------
// The accounting
//------------------------------------------------------------------------------

/// One row of the field equation: a program/library × strict/lazy class, or
/// the total.
#[derive(Debug, Clone, Default, Serialize)]
pub struct FieldRow {
    pub label: String,
    pub before: usize,
    /// `Direct`, re-derived by the independent verifier.
    pub proven_eager: usize,
    /// `Deferred`, plus `Recursive` where the verifier re-derived it.
    pub proven_lazy: usize,
    /// `Dead`, re-derived.
    pub dead: usize,
    /// `Unknown`, **plus** every eager/dead/recursive claim the verifier
    /// did not confirm.
    pub unsupported: usize,
}

impl FieldRow {
    fn sum(&self) -> usize {
        self.proven_eager + self.proven_lazy + self.dead + self.unsupported
    }
}

/// One row of the list or text equation.
#[derive(Debug, Clone, Default, Serialize)]
pub struct AdvisoryRow {
    pub label: String,
    pub before: usize,
    /// A named advisory, verified wherever it is a claim.
    pub advised: usize,
    pub unsupported: usize,
    /// Of `advised`, by advisory name.
    pub by_advisory: Vec<(&'static str, usize)>,
}

impl AdvisoryRow {
    fn sum(&self) -> usize {
        self.advised + self.unsupported
    }
}

/// One of the three census-site tables, in the milestone's own shape.
#[derive(Debug, Clone, Default, Serialize)]
pub struct SiteRow {
    pub label: &'static str,
    pub before: usize,
    /// Sites whose verdict this milestone proves eager or single-pass.
    pub proven: usize,
    /// Sites whose verdict is a named advisory that is not eager.
    pub advised_lazy: usize,
    /// Sites deferred to another census' population (the 1,310).
    pub deferred: usize,
    pub unsupported: usize,
}

impl SiteRow {
    fn sum(&self) -> usize {
        self.proven + self.advised_lazy + self.deferred + self.unsupported
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct RepAccounting {
    pub fields: Vec<FieldRow>,
    pub lists: AdvisoryRow,
    pub text: AdvisoryRow,
    /// The three site tables: the 1,996, the 1,310 and the 1,118.
    pub sites: Vec<SiteRow>,
    /// The `Direct` route-set histogram, printed unconditionally so that a
    /// zero overlap is visible rather than absent.
    pub routes: Vec<(String, usize)>,
    /// Claims the verifier did not confirm, by kind: what moved out of
    /// proven and into unsupported.
    pub unconfirmed: Vec<(&'static str, usize)>,
}

impl RepAccounting {
    /// Every equation closes, and every route-set bucket is part of the
    /// `Direct` population.
    pub fn check(&self) {
        for r in &self.fields {
            assert_eq!(
                r.sum(),
                r.before,
                "the field equation must close for {}: {} != {}",
                r.label,
                r.sum(),
                r.before
            );
        }
        // The rows above the total must sum to it.
        if let Some(total) = self.fields.last() {
            let mut acc = FieldRow::default();
            for r in &self.fields[..self.fields.len() - 1] {
                acc.before += r.before;
                acc.proven_eager += r.proven_eager;
                acc.proven_lazy += r.proven_lazy;
                acc.dead += r.dead;
                acc.unsupported += r.unsupported;
            }
            assert_eq!(acc.before, total.before, "the field classes must partition");
            assert_eq!(acc.proven_eager, total.proven_eager);
            assert_eq!(acc.proven_lazy, total.proven_lazy);
            assert_eq!(acc.dead, total.dead);
            assert_eq!(acc.unsupported, total.unsupported);
        }
        assert_eq!(
            self.lists.sum(),
            self.lists.before,
            "the list equation must close"
        );
        assert_eq!(
            self.text.sum(),
            self.text.before,
            "the text equation must close"
        );
        for r in &self.sites {
            assert_eq!(
                r.sum(),
                r.before,
                "the {} site equation must close: {} != {}",
                r.label,
                r.sum(),
                r.before
            );
        }
        let routed: usize = self.routes.iter().map(|(_, n)| n).sum();
        let direct: usize = self.fields.last().map(|r| r.proven_eager).unwrap_or(0);
        let unconfirmed_direct = self
            .unconfirmed
            .iter()
            .find(|(k, _)| *k == "field Direct")
            .map(|(_, n)| *n)
            .unwrap_or(0);
        assert_eq!(
            routed,
            direct + unconfirmed_direct,
            "the route-set histogram must cover every Direct verdict"
        );
    }
}

/// Build the milestone accounting. `v` must be the verification index over
/// exactly these three censuses.
pub fn accounting(
    fc: &FieldCensus<'_>,
    lc: &ListCensus<'_>,
    tc: &TextCensus,
    v: &Verdicts,
) -> RepAccounting {
    let mut out = RepAccounting::default();
    let mut unconfirmed: BTreeMap<&'static str, usize> = BTreeMap::new();

    // ---- fields -------------------------------------------------------
    // All four classes are printed, including the ones with no fields at
    // all: an absent row hides a zero.
    let mut rows: BTreeMap<(bool, bool), FieldRow> = BTreeMap::new();
    for (program, ghc_strict) in [(true, true), (true, false), (false, true), (false, false)] {
        rows.insert(
            (program, ghc_strict),
            FieldRow {
                label: format!(
                    "{}{}",
                    if program { "program" } else { "library" },
                    if ghc_strict { " !" } else { "" }
                ),
                ..Default::default()
            },
        );
    }
    let mut total = FieldRow {
        label: "total".into(),
        ..Default::default()
    };
    for f in &fc.flows {
        for fv in &f.verdicts {
            let ghc_strict = fv.strictness == crate::fields::ConStrictness::StrictField;
            let key = (f.program, ghc_strict);
            let row = rows.entry(key).or_insert_with(|| FieldRow {
                label: format!(
                    "{}{}",
                    if f.program { "program" } else { "library" },
                    if ghc_strict { " !" } else { "" }
                ),
                ..Default::default()
            });
            let status = v.field(&f.module, f.construction, fv);
            let confirmed = status.proven() || status == Verified::NotAClaim;
            for r in [&mut *row, &mut total] {
                r.before += 1;
                match fv.rep {
                    FieldRep::Direct if confirmed => r.proven_eager += 1,
                    FieldRep::Dead if confirmed => r.dead += 1,
                    FieldRep::Recursive if confirmed => r.proven_lazy += 1,
                    FieldRep::Deferred => r.proven_lazy += 1,
                    _ => r.unsupported += 1,
                }
            }
            if !confirmed {
                *unconfirmed
                    .entry(match fv.rep {
                        FieldRep::Direct => "field Direct",
                        FieldRep::Dead => "field Dead",
                        _ => "field Recursive",
                    })
                    .or_default() += 1;
            }
        }
    }
    // program !, program, library !, library — the order M2.3b's own rep
    // table prints.
    out.fields = [(true, true), (true, false), (false, true), (false, false)]
        .into_iter()
        .filter_map(|k| rows.remove(&k))
        .collect();
    out.fields.push(total);

    // ---- lists --------------------------------------------------------
    let mut lists = AdvisoryRow {
        label: "list flows".into(),
        ..Default::default()
    };
    let mut by_adv: BTreeMap<&'static str, usize> = BTreeMap::new();
    for f in &lc.flows {
        lists.before += 1;
        let status = v.list(f);
        let confirmed = status.proven() || status == Verified::NotAClaim;
        // A `LazyCandidate` that rests on M1's knot verdict is a claim too.
        let knot_ok = f.recursion != crate::lists::Recursion::RecursiveKnot
            || v.status(
                &f.module,
                crate::verify_rep::ClaimKind::ListKnot,
                f.producer,
                0,
            )
            .proven();
        if f.rec != Recommendation::Unknown && confirmed && knot_ok {
            lists.advised += 1;
            *by_adv.entry(f.rec.name()).or_default() += 1;
        } else {
            lists.unsupported += 1;
            if !confirmed {
                *unconfirmed
                    .entry(match f.rec {
                        Recommendation::VecCandidate => "list VecCandidate",
                        _ => "list IteratorCandidate",
                    })
                    .or_default() += 1;
            } else if !knot_ok {
                *unconfirmed.entry("list RecursiveKnot").or_default() += 1;
            }
        }
    }
    lists.by_advisory = by_adv.into_iter().collect();
    out.lists = lists;

    // ---- text ---------------------------------------------------------
    let mut text = AdvisoryRow {
        label: "text flows".into(),
        ..Default::default()
    };
    let mut by_adv: BTreeMap<&'static str, usize> = BTreeMap::new();
    for f in &tc.flows {
        text.before += 1;
        let status = v.text(f);
        let confirmed = status.proven() || status == Verified::NotAClaim;
        if f.advisory != Advisory::Unknown && confirmed {
            text.advised += 1;
            *by_adv.entry(f.advisory.name()).or_default() += 1;
        } else {
            text.unsupported += 1;
            if !confirmed {
                *unconfirmed.entry("text StrongStringCandidate").or_default() += 1;
            }
        }
    }
    text.by_advisory = by_adv.into_iter().collect();
    out.text = text;

    // ---- the three site tables ----------------------------------------
    let mut s1996 = SiteRow {
        label: "the M2 census' 1,996 constructor-field sites",
        ..Default::default()
    };
    for s in &fc.accounting.sites {
        s1996.before += 1;
        if s.list_cons {
            s1996.deferred += 1;
            continue;
        }
        let Some(i) = s.flow else {
            s1996.unsupported += 1;
            continue;
        };
        let f = &fc.flows[i];
        let Some(fv) = f.verdicts.iter().find(|x| Some(x.index) == s.field) else {
            s1996.unsupported += 1;
            continue;
        };
        let status = v.field(&f.module, f.construction, fv);
        let confirmed = status.proven() || status == Verified::NotAClaim;
        match fv.rep {
            FieldRep::Direct if confirmed => s1996.proven += 1,
            FieldRep::Dead if confirmed => s1996.proven += 1,
            FieldRep::Deferred => s1996.advised_lazy += 1,
            FieldRep::Recursive if confirmed => s1996.advised_lazy += 1,
            _ => s1996.unsupported += 1,
        }
    }
    out.sites.push(s1996);

    let mut s1310 = SiteRow {
        label: "…of which the 1,310 list-cons sites, on M2.3c's population",
        ..Default::default()
    };
    for s in &lc.accounting.sites {
        s1310.before += 1;
        let Some(i) = s.flow else {
            s1310.unsupported += 1;
            continue;
        };
        let f = &lc.flows[i];
        let status = v.list(f);
        let confirmed = status.proven() || status == Verified::NotAClaim;
        if !confirmed || f.rec == Recommendation::Unknown {
            s1310.unsupported += 1;
        } else if single_pass_eager(f) {
            s1310.proven += 1;
        } else {
            s1310.advised_lazy += 1;
        }
    }
    out.sites.push(s1310);

    let mut s1118 = SiteRow {
        label: "the M2 census' 1,118 append argument sites",
        ..Default::default()
    };
    for s in &tc.accounting.sites {
        s1118.before += 1;
        let Some(i) = s.flow else {
            s1118.unsupported += 1;
            continue;
        };
        let f = &tc.flows[i];
        let status = v.text(f);
        let confirmed = status.proven() || status == Verified::NotAClaim;
        let lf = &lc.flows[f.list_flow];
        if !confirmed || f.advisory == Advisory::Unknown {
            s1118.unsupported += 1;
        } else if v.list(lf).proven() && single_pass_eager(lf) {
            s1118.proven += 1;
        } else {
            s1118.advised_lazy += 1;
        }
    }
    out.sites.push(s1118);

    out.routes = fc.accounting.direct_by_routes.clone();
    out.unconfirmed = unconfirmed.into_iter().collect();
    out.check();
    out
}

/// Is this spine consumed eagerly by a single pass — the condition under
/// which a cell's tail thunk becomes an iterator step rather than a
/// deferred cell? The advisory has to be `Vec` or `Iterator` (one pass,
/// nothing retained, no shared tail) **and** the spine demand has to be a
/// whole or incremental traversal rather than a prefix or an unknown.
pub fn single_pass_eager(f: &crate::lists::ListFlow) -> bool {
    matches!(
        f.rec,
        Recommendation::VecCandidate | Recommendation::IteratorCandidate
    ) && matches!(f.spine, SpineDemand::Whole | SpineDemand::Incremental)
}

//------------------------------------------------------------------------------
// The cross-milestone link
//------------------------------------------------------------------------------

/// The rule that explains an M1 thunk site away.
pub const M23_A_FIELD_VALUE: &str = "M23-A-FIELD-ALREADY-A-VALUE";
pub const M23_B_STRICT_SELECTOR: &str = "M23-B-SELECTOR-OVER-AN-EAGER-FIELD";
pub const M23_C_SPINE_STEP: &str = "M23-C-CELL-OF-A-SINGLE-PASS-SPINE";

/// One M1 thunk site an M2.3 verdict removes.
#[derive(Debug, Clone, Serialize)]
pub struct Explained {
    pub module: String,
    pub occ: String,
    pub origin: Origin,
    pub fate: Fate,
    pub let_node: ExprId,
    pub rhs: ExprId,
    pub rule: &'static str,
    /// The construction or producer whose verdict explains it.
    pub over: ExprId,
    pub detail: String,
}

/// One row of the M1 table, with both milestones' columns.
#[derive(Debug, Clone, Serialize)]
pub struct Row {
    pub label: &'static str,
    pub before: usize,
    pub by_tuples: usize,
    pub by_m23: usize,
}

impl Row {
    pub fn after(&self) -> usize {
        self.before - self.by_tuples - self.by_m23
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct RepLink {
    pub thunk_sites: usize,
    /// M2.2's count, read from its own link and never recomputed here.
    pub by_tuples: usize,
    pub explained: Vec<Explained>,
    pub fates: Vec<Row>,
    pub memo: Vec<Row>,
    pub origins: Vec<(Origin, usize, usize, usize)>,
    pub by_rule: BTreeMap<&'static str, usize>,
    /// The M2 lazy-argument sites that stop being lazy positions.
    pub sites_1996: usize,
    pub sites_1996_explained: usize,
    pub sites_1118: usize,
    pub sites_1118_explained: usize,
    /// What was deliberately **not** counted, with the count and why.
    pub not_counted: Vec<(&'static str, usize, &'static str)>,
}

impl RepLink {
    pub fn remaining(&self) -> usize {
        self.thunk_sites - self.by_tuples - self.explained.len()
    }

    /// The invariant the section exists to state.
    pub fn check(&self) {
        assert!(
            self.by_tuples + self.explained.len() <= self.thunk_sites,
            "more thunk sites explained than exist"
        );
        assert_eq!(
            self.remaining() + self.by_tuples + self.explained.len(),
            self.thunk_sites,
            "remaining + explained-by-tuples + explained-by-M2.3 must be the M1 population"
        );
        let keys: HashSet<(&str, ExprId, ExprId)> = self
            .explained
            .iter()
            .map(|e| (e.module.as_str(), e.let_node, e.rhs))
            .collect();
        assert_eq!(
            keys.len(),
            self.explained.len(),
            "no thunk site may be explained twice"
        );
        let before: usize = self.fates.iter().map(|r| r.before).sum();
        assert_eq!(before, self.thunk_sites, "the fate rows must cover M1");
        assert_eq!(
            self.fates.iter().map(|r| r.by_m23).sum::<usize>(),
            self.explained.len(),
            "every explained site lands in exactly one fate row"
        );
        assert_eq!(
            self.fates.iter().map(|r| r.by_tuples).sum::<usize>(),
            self.by_tuples,
            "every tuple-explained site lands in exactly one fate row"
        );
        assert_eq!(
            self.origins.iter().map(|(_, _, _, e)| e).sum::<usize>(),
            self.explained.len(),
            "every explained site lands in exactly one origin row"
        );
        assert_eq!(
            self.by_rule.values().sum::<usize>(),
            self.explained.len(),
            "every explained site is explained by exactly one rule"
        );
        for r in self.fates.iter().chain(&self.memo) {
            assert!(
                r.by_tuples + r.by_m23 <= r.before,
                "{}: explained exceeds the population",
                r.label
            );
        }
        assert!(self.sites_1996_explained <= self.sites_1996);
        assert!(self.sites_1118_explained <= self.sites_1118);
    }
}

/// The binder a `let` pair binds, given the `let` node and the right-hand
/// side M1 reports.
fn binder_of(m: &Module, let_node: ExprId, rhs: ExprId) -> Option<h2r_core_ir::BinderId> {
    let Expr::Let { bind, .. } = m.expr(let_node) else {
        return None;
    };
    bind.pairs.iter().find(|p| p.rhs == rhs).map(|p| p.binder)
}

/// Compute the link. `tuple_explained` is M2.2's own set of explained thunk
/// sites, keyed the same way M1 keys a binding, so that the two milestones
/// can be shown side by side without either counting a site the other
/// already did.
pub fn link(
    census: &Census,
    fc: &FieldCensus<'_>,
    lc: &ListCensus<'_>,
    tc: &TextCensus,
    v: &Verdicts,
    modules: &[&Module],
    tuple_explained: &HashSet<(String, ExprId, ExprId)>,
) -> RepLink {
    let by_name: HashMap<&str, &Module> = modules.iter().map(|m| (m.name.as_str(), *m)).collect();

    // (a) A binder whose occurrence is a constructor field that is proven
    //     `Direct` by `R2` — the field expression is already a value, so
    //     the binding it reads is not a thunk at all.
    let mut a_binders: HashMap<(String, h2r_core_ir::BinderId), (ExprId, String)> = HashMap::new();
    // (b) A `case` node that is a lazy selection over a field this
    //     milestone proves eager.
    let mut b_cases: HashMap<(String, ExprId), (ExprId, String)> = HashMap::new();
    for f in &fc.flows {
        let Some(m) = by_name.get(f.module.as_str()) else {
            continue;
        };
        for fv in &f.verdicts {
            if fv.rep != FieldRep::Direct || !v.field(&f.module, f.construction, fv).proven() {
                continue;
            }
            if fv.routes.contains(&crate::fields::R2_FIELD_IS_VALUE) {
                let expr = m.strip(f.fields[fv.index as usize]);
                if let Some(b) = m.resolve(expr) {
                    a_binders.insert(
                        (f.module.clone(), b),
                        (
                            f.construction,
                            format!("field {} of {} is Direct by R2", fv.index, f.occ),
                        ),
                    );
                }
            }
            // A lazy selector over this field: `case c of C .. x .. -> x`.
            for o in &f.observations {
                if o.kind != ObsKind::FieldDemanded || o.field != Some(fv.index) {
                    continue;
                }
                let Some(binder) = o.binder else { continue };
                if !is_selector_case(m, o.at, binder) {
                    continue;
                }
                b_cases.insert(
                    (f.module.clone(), o.at),
                    (
                        f.construction,
                        format!(
                            "a lazy selection of field {} of {}, which is Direct [{}]",
                            fv.index, f.occ, fv.rule
                        ),
                    ),
                );
            }
        }
    }

    // (c) A binder that is the tail of a cell, or an append operand, of a
    //     flow whose advisory is Vec/Iterator over a whole or incremental
    //     spine: the spine is consumed by a single eager pass, so the cell
    //     thunk becomes an iterator step.
    let mut c_binders: HashMap<(String, h2r_core_ir::BinderId), (ExprId, String)> = HashMap::new();
    let mut eager_text_flows: HashSet<(String, ExprId)> = HashSet::new();
    for f in &tc.flows {
        let lf = &lc.flows[f.list_flow];
        if v.list(lf).proven() && single_pass_eager(lf) {
            eager_text_flows.insert((f.module.clone(), f.producer));
        }
    }
    for f in &lc.flows {
        if !single_pass_eager(f) || !v.list(f).proven() {
            continue;
        }
        let Some(m) = by_name.get(f.module.as_str()) else {
            continue;
        };
        let text = eager_text_flows.contains(&(f.module.clone(), f.producer));
        for cell in &f.cells {
            // The tail is the last value argument of the cons spine.
            let (_, args) = m.spine(*cell);
            let Some(tail) = args.last() else { continue };
            let t = m.strip(*tail);
            if let Some(b) = m.resolve(t) {
                c_binders.insert(
                    (f.module.clone(), b),
                    (
                        f.producer,
                        format!(
                            "the tail of the cell at node {cell} of a {} spine with {} demand{}",
                            f.rec.name(),
                            f.spine.name(),
                            if text { ", text" } else { "" }
                        ),
                    ),
                );
            }
        }
    }

    let mut out = RepLink::default();
    let thunks: Vec<&crate::laziness::BindingReport> = census
        .bindings
        .iter()
        .filter(|b| b.fate != Fate::NotAThunk)
        .collect();
    out.thunk_sites = thunks.len();
    out.by_tuples = thunks
        .iter()
        .filter(|b| tuple_explained.contains(&(b.module.clone(), b.let_node, b.rhs)))
        .count();

    let mut seen: HashSet<(String, ExprId, ExprId)> = HashSet::new();
    for b in &thunks {
        let key = (b.module.clone(), b.let_node, b.rhs);
        // A site M2.2 already explains is M2.2's; nothing is counted twice.
        if tuple_explained.contains(&key) {
            continue;
        }
        let Some(m) = by_name.get(b.module.as_str()) else {
            continue;
        };
        let binder = binder_of(m, b.let_node, b.rhs);
        let hit = binder
            .and_then(|bi| a_binders.get(&(b.module.clone(), bi)))
            .map(|(o, d)| (M23_A_FIELD_VALUE, *o, d.clone()))
            .or_else(|| {
                b_cases
                    .get(&(b.module.clone(), m.strip(b.rhs)))
                    .map(|(o, d)| (M23_B_STRICT_SELECTOR, *o, d.clone()))
            })
            .or_else(|| {
                binder
                    .and_then(|bi| c_binders.get(&(b.module.clone(), bi)))
                    .map(|(o, d)| (M23_C_SPINE_STEP, *o, d.clone()))
            });
        let Some((rule, over, detail)) = hit else {
            continue;
        };
        if !seen.insert(key) {
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
            over,
            detail,
        });
        *out.by_rule.entry(rule).or_default() += 1;
    }

    let explained_keys: HashSet<(String, ExprId, ExprId)> = out
        .explained
        .iter()
        .map(|e| (e.module.clone(), e.let_node, e.rhs))
        .collect();
    let mine = |b: &crate::laziness::BindingReport| {
        explained_keys.contains(&(b.module.clone(), b.let_node, b.rhs))
    };
    let theirs = |b: &crate::laziness::BindingReport| {
        tuple_explained.contains(&(b.module.clone(), b.let_node, b.rhs))
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
            by_tuples: thunks
                .iter()
                .filter(|b| b.fate == fate && theirs(b))
                .count(),
            by_m23: thunks.iter().filter(|b| b.fate == fate && mine(b)).count(),
        });
    }
    let memo: Vec<&&crate::laziness::BindingReport> =
        thunks.iter().filter(|b| b.fate == Fate::Memo).collect();
    let lam = |b: &crate::laziness::BindingReport| matches!(b.sink, Sink::UnderLambda { .. });
    out.memo = vec![
        Row {
            label: "captured by a many-entry lambda",
            before: memo.iter().filter(|b| lam(b)).count(),
            by_tuples: memo.iter().filter(|b| lam(b) && theirs(b)).count(),
            by_m23: memo.iter().filter(|b| lam(b) && mine(b)).count(),
        },
        Row {
            label: "shared on one path",
            before: memo.iter().filter(|b| !lam(b)).count(),
            by_tuples: memo.iter().filter(|b| !lam(b) && theirs(b)).count(),
            by_m23: memo.iter().filter(|b| !lam(b) && mine(b)).count(),
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
                .filter(|b| b.origin == origin && theirs(b))
                .count(),
            thunks
                .iter()
                .filter(|b| b.origin == origin && mine(b))
                .count(),
        ));
    }

    // The M2 lazy-argument sites, from the other side.
    for s in &fc.accounting.sites {
        out.sites_1996 += 1;
        if s.list_cons {
            // Deferred to M2.3c: it stops being a lazy position when the
            // spine it lands in is consumed by one eager pass.
            continue;
        }
        let Some(i) = s.flow else { continue };
        let f = &fc.flows[i];
        let Some(fv) = f.verdicts.iter().find(|x| Some(x.index) == s.field) else {
            continue;
        };
        if fv.rep == FieldRep::Direct && v.field(&f.module, f.construction, fv).proven() {
            out.sites_1996_explained += 1;
        }
    }
    for s in &lc.accounting.sites {
        let Some(i) = s.flow else { continue };
        let f = &lc.flows[i];
        if single_pass_eager(f) && v.list(f).proven() {
            out.sites_1996_explained += 1;
        }
    }
    for s in &tc.accounting.sites {
        out.sites_1118 += 1;
        let Some(i) = s.flow else { continue };
        let f = &tc.flows[i];
        let lf = &lc.flows[f.list_flow];
        if single_pass_eager(lf) && v.list(lf).proven() {
            out.sites_1118_explained += 1;
        }
    }

    // What is deliberately not counted, and why. The same discipline as
    // M2.2's 377 holders: an adjacent population that would make the number
    // larger and the claim weaker.
    let direct_unverified = fc
        .flows
        .iter()
        .flat_map(|f| f.verdicts.iter().map(move |x| (f, x)))
        .filter(|(f, x)| {
            x.rep == FieldRep::Direct && !v.field(&f.module, f.construction, x).proven()
        })
        .count();
    out.not_counted = vec![
        (
            "a Deferred field's thunk",
            fc.accounting.count(FieldRep::Deferred),
            "Deferred says the evaluation stays where GHC put it: the thunk is exactly what remains",
        ),
        (
            "a PersistentCandidate spine's cells",
            lc.accounting.count(Recommendation::PersistentCandidate),
            "a shared tail or a second entry means the cells outlive one pass; the thunk stays",
        ),
        (
            "a Prefix spine's cells, however eager the consumer",
            lc.flows
                .iter()
                .filter(|f| {
                    matches!(
                        f.rec,
                        Recommendation::VecCandidate | Recommendation::IteratorCandidate
                    ) && !matches!(f.spine, SpineDemand::Whole | SpineDemand::Incremental)
                })
                .count(),
            "a data-dependent or bounded prefix is precisely a spine whose tail may never be reached",
        ),
        (
            "a field of a construction the verifier refused",
            direct_unverified,
            "a claim proven once is not proven",
        ),
    ];

    out.check();
    out
}

/// Is this `case` a *lazy selector* — one alternative whose right-hand side
/// is nothing but an occurrence of the field binder? That is the shape the
/// desugarer produces for a lazy pattern, and the only shape rule (b)
/// accepts: a `case` that does anything else with the field is not a
/// selection that disappears when the field becomes eager.
fn is_selector_case(m: &Module, case: ExprId, binder: h2r_core_ir::BinderId) -> bool {
    let Expr::Case { alts, .. } = m.expr(case) else {
        return false;
    };
    alts.iter()
        .any(|a| a.binders.contains(&binder) && m.resolve(m.strip(a.rhs)) == Some(binder))
}
