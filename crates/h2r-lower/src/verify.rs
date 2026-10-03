//! The independent re-derivation of M3a's live set.
//!
//! This walk shares **nothing** with [`crate::reachability`] but the IR
//! and a named list of trusted inputs, and it reads the
//! [`LiveSet`](crate::reachability::LiveSet) only as *data*: a population
//! of nodes, a set of verdicts, a set of witnesses, a set of edges. It
//! never calls the closure, never calls the edge walk, and never asks
//! `h2r_analysis` anything.
//!
//! Where the census walks *down* — pre-order over every top-level
//! right-hand side, collecting the occurrences it finds — the verifier
//! works *up*: it derives, for every node of every module's arena, which
//! top-level pair encloses it, by climbing [`Module::parent`] to the root
//! and reading the [`Edge::Top`] it arrived by. Every check below is
//! phrased over that owner map and over [`Module::occurrences`], the
//! IR's own occurrence index. The two derivations agree or the audit
//! fails; nothing reconciles them.
//!
//! The trusted inputs are the same five
//! [`crate::reachability::TRUSTED`] names. They are *consulted* on both
//! sides — the module list, the root name, the resolver, GHC's flags,
//! and `W0` — and the audit says so rather than calling them verified.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use h2r_core_ir::{BindSite, BinderId, Edge, Expr, ExprId, Module, Ref};
use serde::Serialize;

use h2r_analysis::dictflow::is_external_name;

use crate::reachability::{
    A2_EDGE_LOCAL, A3_EDGE_GLOBAL, DeadReason, LiveSet, NodeId, TRUSTED, TopKey, root_name,
};

//------------------------------------------------------------------------------
// Checks
//------------------------------------------------------------------------------

/// Every claimed root is a top-level binding of the `Main` module carrying
/// the trusted root name, and every such binding is claimed.
pub const V1_ROOTS: &str = "V1-ROOTS";
/// Every top-level binding of every module appears exactly once in
/// `live ∪ dead`, and every node's `(module, binder)` really is a
/// top-level binding of that module.
pub const V2_POPULATION: &str = "V2-POPULATION";
/// For every **live** binding, every `Var` occurrence inside its
/// right-hand side that names a top-level binding — locally through the
/// resolver, globally through the stable name — names a **live** one.
pub const V3_LIVE_CLOSED: &str = "V3-LIVE-CLOSED";
/// For every **dead** binding, every occurrence of its binder anywhere in
/// the world lies inside the right-hand side of a **dead** binding: no
/// live right-hand side contains one.
pub const V4_DEAD_UNREFERENCED: &str = "V4-DEAD-UNREFERENCED";
/// Every witness path starts at a claimed root, ends at the binding it
/// belongs to, and every consecutive pair is a real edge — re-derived
/// here from the IR, not read from the recorded edge list.
pub const V5_WITNESS: &str = "V5-WITNESS";
/// The recorded edge list is exactly the edge relation the IR gives, with
/// the same occurrence counts: nothing dropped, nothing invented.
pub const V6_EDGES: &str = "V6-EDGES";
/// Every dead reason is the right one: `DeadNoReferences` exactly when the
/// binder has no occurrence anywhere in the world, and the recorded
/// referrers are exactly the top-level bindings that reference it.
pub const V7_DEAD_REASON: &str = "V7-DEAD-REASON";
/// The accounting identities, recomputed from the contents rather than
/// from the counters.
pub const V8_ACCOUNTING: &str = "V8-ACCOUNTING";
/// The subset gate, re-derived without asking `h2r_analysis` anything: the
/// recorded zero-reference set is exactly the set of top-level bindings
/// with no occurrence anywhere in the world, and every one of them is
/// dead.
pub const V9_ZERO_REFERENCE: &str = "V9-ZERO-REFERENCE";

pub const CHECKS: &[(&str, &str)] = &[
    (V1_ROOTS, "the roots are exactly Main's $<unit>$Main$main"),
    (
        V2_POPULATION,
        "every top-level binding appears exactly once in live + dead",
    ),
    (
        V3_LIVE_CLOSED,
        "a live right-hand side never names a dead top-level binding",
    ),
    (
        V4_DEAD_UNREFERENCED,
        "every occurrence of a dead binder lies inside a dead right-hand side",
    ),
    (
        V5_WITNESS,
        "every witness is a real root-to-binding chain of edges",
    ),
    (V6_EDGES, "the recorded edges are exactly the IR's"),
    (
        V7_DEAD_REASON,
        "every dead reason and referrer list is the one the IR gives",
    ),
    (V8_ACCOUNTING, "the identities hold over the contents"),
    (
        V9_ZERO_REFERENCE,
        "the zero-reference set is exactly the unreferenced bindings, and all are dead",
    ),
];

//------------------------------------------------------------------------------
// The audit
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize)]
pub struct Disagreement {
    pub check: &'static str,
    pub what: String,
    pub detail: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct CheckResult {
    pub check: &'static str,
    pub meaning: &'static str,
    /// How many claims this check looked at.
    pub population: usize,
    pub disagreements: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct Audit {
    pub trusted: &'static [&'static str],
    pub checks: Vec<CheckResult>,
    /// At most [`MAX_REPORTED`] per check; the counts are complete.
    pub disagreements: Vec<Disagreement>,
    pub total_population: usize,
    pub total_disagreements: usize,
}

/// How many disagreements of one kind the audit spells out. The counts are
/// always complete.
pub const MAX_REPORTED: usize = 10;

impl Audit {
    pub fn ok(&self) -> bool {
        self.total_disagreements == 0
    }

    pub fn headline(&self) -> String {
        format!(
            "{} claims re-derived, {} disagreements",
            self.total_population, self.total_disagreements
        )
    }

    pub fn report_lines(&self) -> Vec<String> {
        let mut out = Vec::new();
        for c in &self.checks {
            out.push(format!(
                "{:<22} {:>8} claims   {:>4} disagreements   {}",
                c.check, c.population, c.disagreements, c.meaning
            ));
        }
        if self.disagreements.is_empty() {
            out.push(format!(
                "0 disagreements over {} claims: the live set is confirmed",
                self.total_population
            ));
        } else {
            for d in &self.disagreements {
                out.push(format!("DISAGREE {} {}: {}", d.check, d.what, d.detail));
            }
        }
        out
    }
}

//------------------------------------------------------------------------------
// The walk
//------------------------------------------------------------------------------

struct Checker<'a> {
    modules: &'a [&'a Module],
    live: &'a LiveSet,
    /// Per module, per `ExprId`: the flat top-level pair the node lies in.
    owner_pair: Vec<Vec<u32>>,
    /// Per module, the binder of every flat top-level pair.
    pair_binder: Vec<Vec<BinderId>>,
    /// `(module, binder)` → node, from the population the claim declares
    /// (checked by [`V2_POPULATION`] before anything reads it).
    node_of: Vec<HashMap<BinderId, NodeId>>,
    /// External stable name → node, re-derived here.
    by_name: HashMap<String, NodeId>,
    /// Every `Ref::Global` occurrence in the world, by stable name.
    gvars: HashMap<String, Vec<(usize, ExprId)>>,
    out: Vec<CheckResult>,
    bad: Vec<Disagreement>,
    seen: BTreeMap<&'static str, usize>,
}

pub fn verify(modules: &[&Module], live: &LiveSet) -> Audit {
    let mut c = Checker::new(modules, live);
    c.population();
    c.roots();
    c.live_closed();
    c.dead_unreferenced();
    c.edges();
    c.witnesses();
    c.dead_reasons();
    c.accounting();
    c.zero_reference();
    let total_population = c.out.iter().map(|x| x.population).sum();
    let total_disagreements = c.out.iter().map(|x| x.disagreements).sum();
    Audit {
        trusted: TRUSTED,
        checks: c.out,
        disagreements: c.bad,
        total_population,
        total_disagreements,
    }
}

impl<'a> Checker<'a> {
    fn new(modules: &'a [&'a Module], live: &'a LiveSet) -> Self {
        let mut owner_pair = Vec::with_capacity(modules.len());
        let mut pair_binder = Vec::with_capacity(modules.len());
        let mut gvars: HashMap<String, Vec<(usize, ExprId)>> = HashMap::new();
        for (mi, m) in modules.iter().enumerate() {
            pair_binder.push(
                m.top
                    .iter()
                    .flat_map(|b| b.pairs.iter().map(|p| p.binder))
                    .collect::<Vec<_>>(),
            );
            owner_pair.push(owners(m));
            for id in 0..m.exprs.len() as ExprId {
                if let (Expr::Var { name, .. }, Some(Ref::Global)) = (m.expr(id), m.reference(id)) {
                    gvars.entry(name.clone()).or_default().push((mi, id));
                }
            }
        }
        let mut node_of = vec![HashMap::new(); modules.len()];
        let mut by_name: HashMap<String, NodeId> = HashMap::new();
        for (i, t) in live.nodes.iter().enumerate() {
            node_of[t.key.module as usize].insert(t.key.binder, i as NodeId);
            if is_external_name(&t.name) {
                by_name.insert(t.name.clone(), i as NodeId);
            }
        }
        Checker {
            modules,
            live,
            owner_pair,
            pair_binder,
            node_of,
            by_name,
            gvars,
            out: Vec::new(),
            bad: Vec::new(),
            seen: BTreeMap::new(),
        }
    }

    fn fail(&mut self, check: &'static str, what: String, detail: String) {
        let n = self.seen.entry(check).or_insert(0);
        *n += 1;
        if *n <= MAX_REPORTED {
            self.bad.push(Disagreement {
                check,
                what,
                detail,
            });
        }
    }

    fn done(&mut self, check: &'static str, population: usize) {
        let meaning = CHECKS
            .iter()
            .find(|(c, _)| *c == check)
            .map(|(_, m)| *m)
            .unwrap_or("");
        let disagreements = self.seen.get(check).copied().unwrap_or(0);
        self.out.push(CheckResult {
            check,
            meaning,
            population,
            disagreements,
        });
    }

    /// The node whose right-hand side contains `(mi, node)`.
    fn owner(&self, mi: usize, node: ExprId) -> Option<NodeId> {
        let pair = self.owner_pair[mi][node as usize];
        if pair == u32::MAX {
            return None;
        }
        let b = *self.pair_binder[mi].get(pair as usize)?;
        self.node_of[mi].get(&b).copied()
    }

    //--- V2 -----------------------------------------------------------------

    fn population(&mut self) {
        let mut declared: BTreeSet<TopKey> = BTreeSet::new();
        let mut pop = 0usize;
        for (i, t) in self.live.nodes.iter().enumerate() {
            pop += 1;
            let mi = t.key.module as usize;
            if mi >= self.modules.len() {
                self.fail(
                    V2_POPULATION,
                    format!("node {i}"),
                    "module out of range".into(),
                );
                continue;
            }
            let m = self.modules[mi];
            if m.name != t.module_name {
                self.fail(
                    V2_POPULATION,
                    format!("node {i}"),
                    format!(
                        "claims module {} but index {mi} is {}",
                        t.module_name, m.name
                    ),
                );
            }
            if m.binding(t.key.binder).site != BindSite::Top {
                self.fail(
                    V2_POPULATION,
                    format!("node {i}"),
                    format!("binder {} is not bound at top level", t.key.binder),
                );
                continue;
            }
            if m.binder(t.key.binder).name != t.name {
                self.fail(
                    V2_POPULATION,
                    format!("node {i}"),
                    format!("stable name {} is not the binder's", t.name),
                );
            }
            if !declared.insert(t.key) {
                self.fail(
                    V2_POPULATION,
                    format!("node {i}"),
                    "the same top-level binding twice".into(),
                );
            }
        }
        // Every top-level binding of every module is in the population.
        for (mi, m) in self.modules.iter().enumerate() {
            for bind in &m.top {
                for p in &bind.pairs {
                    pop += 1;
                    let k = TopKey {
                        module: mi as u32,
                        binder: p.binder,
                    };
                    if !declared.contains(&k) {
                        self.fail(
                            V2_POPULATION,
                            format!("{} binder {}", m.name, p.binder),
                            "a top-level binding the population does not carry".into(),
                        );
                    }
                }
            }
        }
        // …and exactly once in live ∪ dead.
        let mut verdict: BTreeMap<NodeId, u8> = BTreeMap::new();
        for l in &self.live.live {
            pop += 1;
            *verdict.entry(l.node).or_insert(0) += 1;
        }
        for d in &self.live.dead {
            pop += 1;
            *verdict.entry(d.node).or_insert(0) += 2;
        }
        for i in 0..self.live.nodes.len() as NodeId {
            match verdict.get(&i) {
                Some(1) | Some(2) => {}
                Some(other) => self.fail(
                    V2_POPULATION,
                    self.name_of(i),
                    format!("carries {other} verdicts, not one"),
                ),
                None => self.fail(V2_POPULATION, self.name_of(i), "no verdict at all".into()),
            }
        }
        self.done(V2_POPULATION, pop);
    }

    fn name_of(&self, n: NodeId) -> String {
        match self.live.nodes.get(n as usize) {
            Some(t) => format!("{} {}", t.module_name, t.occ),
            None => format!("node {n}"),
        }
    }

    //--- V1 -----------------------------------------------------------------

    fn roots(&mut self) {
        let mains: Vec<&&Module> = self.modules.iter().filter(|m| m.name == "Main").collect();
        let want = match mains.as_slice() {
            [m] => root_name(&m.unit),
            _ => {
                self.fail(
                    V1_ROOTS,
                    "Main".into(),
                    format!("{} modules named Main", mains.len()),
                );
                self.done(V1_ROOTS, self.live.roots.len());
                return;
            }
        };
        let mut pop = 0usize;
        let claimed: BTreeSet<NodeId> = self.live.roots.iter().map(|r| r.node).collect();
        for r in &self.live.roots {
            pop += 1;
            let Some(t) = self.live.nodes.get(r.node as usize) else {
                self.fail(V1_ROOTS, format!("node {}", r.node), "out of range".into());
                continue;
            };
            if t.name != want {
                self.fail(
                    V1_ROOTS,
                    self.name_of(r.node),
                    format!("a root whose stable name is not {want}"),
                );
            }
            if !self.live.is_live(r.node) {
                self.fail(
                    V1_ROOTS,
                    self.name_of(r.node),
                    "a root that is not live".into(),
                );
            }
        }
        for (i, t) in self.live.nodes.iter().enumerate() {
            if t.name == want {
                pop += 1;
                if !claimed.contains(&(i as NodeId)) {
                    self.fail(
                        V1_ROOTS,
                        self.name_of(i as NodeId),
                        format!("carries the root name {want} and is not a root"),
                    );
                }
            }
        }
        self.done(V1_ROOTS, pop);
    }

    //--- V3 -----------------------------------------------------------------
    //
    // Driven by a linear scan over every arena node, with the owner read
    // from the climbed map — never a walk down a right-hand side.

    fn live_closed(&mut self) {
        let mut pop = 0usize;
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        for (mi, m) in self.modules.iter().enumerate() {
            for id in 0..m.exprs.len() as ExprId {
                let Expr::Var { name, .. } = m.expr(id) else {
                    continue;
                };
                let Some(target) = self.target_of(mi, m, id, name) else {
                    continue;
                };
                let Some(owner) = self.owner(mi, id) else {
                    continue;
                };
                if !self.live.is_live(owner) {
                    continue;
                }
                pop += 1;
                if !self.live.is_live(target) {
                    hits.push((
                        V3_LIVE_CLOSED,
                        self.name_of(owner),
                        format!(
                            "its right-hand side names {} at node {id}, which is claimed dead",
                            self.name_of(target)
                        ),
                    ));
                }
            }
        }
        for (c, w, d) in hits {
            self.fail(c, w, d);
        }
        self.done(V3_LIVE_CLOSED, pop);
    }

    /// The top-level binding a `Var` occurrence names, if any. The
    /// verifier's own two rules, written out rather than borrowed.
    fn target_of(&self, mi: usize, m: &Module, id: ExprId, name: &str) -> Option<NodeId> {
        match m.reference(id)? {
            Ref::Local(b) => {
                if m.binding(b).site == BindSite::Top {
                    self.node_of[mi].get(&b).copied()
                } else {
                    None
                }
            }
            Ref::Global => self.by_name.get(name).copied(),
        }
    }

    //--- V4 -----------------------------------------------------------------
    //
    // Driven by the IR's own occurrence index and, for globals, by the
    // stable-name scan. Never by a walk over a right-hand side.

    fn dead_unreferenced(&mut self) {
        let mut pop = 0usize;
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        for d in &self.live.dead {
            let t = &self.live.nodes[d.node as usize];
            let mi = t.key.module as usize;
            let m = self.modules[mi];
            for &o in m.occurrences(t.key.binder) {
                pop += 1;
                match self.owner(mi, o) {
                    Some(owner) if self.live.is_live(owner) => hits.push((
                        V4_DEAD_UNREFERENCED,
                        self.name_of(d.node),
                        format!(
                            "claimed dead, but the live binding {} names it at node {o}",
                            self.name_of(owner)
                        ),
                    )),
                    _ => {}
                }
            }
            if !t.external {
                continue;
            }
            for &(omi, o) in self.gvars.get(&t.name).into_iter().flatten() {
                pop += 1;
                match self.owner(omi, o) {
                    Some(owner) if self.live.is_live(owner) => hits.push((
                        V4_DEAD_UNREFERENCED,
                        self.name_of(d.node),
                        format!(
                            "claimed dead, but the live binding {} names it at {} node {o}",
                            self.name_of(owner),
                            self.modules[omi].name
                        ),
                    )),
                    _ => {}
                }
            }
        }
        for (c, w, dt) in hits {
            self.fail(c, w, dt);
        }
        self.done(V4_DEAD_UNREFERENCED, pop);
    }

    //--- V6 -----------------------------------------------------------------

    /// The edge relation, re-derived from the occurrence side: for every
    /// node, the multiset of top-level bindings that name it.
    fn derive_edges(&self) -> BTreeMap<(NodeId, NodeId, &'static str), u32> {
        let mut out: BTreeMap<(NodeId, NodeId, &'static str), u32> = BTreeMap::new();
        for (mi, m) in self.modules.iter().enumerate() {
            for id in 0..m.exprs.len() as ExprId {
                let Expr::Var { name, .. } = m.expr(id) else {
                    continue;
                };
                let Some(to) = self.target_of(mi, m, id, name) else {
                    continue;
                };
                let Some(from) = self.owner(mi, id) else {
                    continue;
                };
                let rule = match m.reference(id) {
                    Some(Ref::Local(_)) => A2_EDGE_LOCAL,
                    _ => A3_EDGE_GLOBAL,
                };
                *out.entry((from, to, rule)).or_insert(0) += 1;
            }
        }
        out
    }

    fn edges(&mut self) {
        let mine = self.derive_edges();
        let mut theirs: BTreeMap<(NodeId, NodeId, &'static str), u32> = BTreeMap::new();
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        for e in &self.live.edges {
            if theirs
                .insert((e.from, e.to, e.rule), e.occurrences)
                .is_some()
            {
                hits.push((
                    V6_EDGES,
                    format!("{} -> {}", self.name_of(e.from), self.name_of(e.to)),
                    "recorded twice".into(),
                ));
            }
        }
        let pop = mine.len() + theirs.len();
        for (&(f, t, r), &n) in &mine {
            match theirs.get(&(f, t, r)) {
                Some(&k) if k == n => {}
                Some(&k) => hits.push((
                    V6_EDGES,
                    format!("{} -> {} [{r}]", self.name_of(f), self.name_of(t)),
                    format!("recorded {k} occurrences, the IR gives {n}"),
                )),
                None => hits.push((
                    V6_EDGES,
                    format!("{} -> {} [{r}]", self.name_of(f), self.name_of(t)),
                    format!("an edge of {n} occurrence(s) the report does not carry"),
                )),
            }
        }
        for &(f, t, r) in theirs.keys() {
            if !mine.contains_key(&(f, t, r)) {
                hits.push((
                    V6_EDGES,
                    format!("{} -> {} [{r}]", self.name_of(f), self.name_of(t)),
                    "an edge the IR does not give".into(),
                ));
            }
        }
        for (c, w, d) in hits {
            self.fail(c, w, d);
        }
        self.done(V6_EDGES, pop);
    }

    //--- V5 -----------------------------------------------------------------

    fn witnesses(&mut self) {
        let pairs: BTreeSet<(NodeId, NodeId)> = self
            .derive_edges()
            .keys()
            .map(|&(f, t, _)| (f, t))
            .collect();
        let roots: BTreeSet<NodeId> = self.live.roots.iter().map(|r| r.node).collect();
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        let mut pop = 0usize;
        for l in &self.live.live {
            pop += 1;
            let w = &l.witness;
            if w.last() != Some(&l.node) {
                hits.push((
                    V5_WITNESS,
                    self.name_of(l.node),
                    "the witness does not end at the binding".into(),
                ));
                continue;
            }
            match w.first() {
                Some(r) if roots.contains(r) => {}
                _ => {
                    hits.push((
                        V5_WITNESS,
                        self.name_of(l.node),
                        "the witness does not start at a root".into(),
                    ));
                    continue;
                }
            }
            for pair in w.windows(2) {
                if !pairs.contains(&(pair[0], pair[1])) {
                    hits.push((
                        V5_WITNESS,
                        self.name_of(l.node),
                        format!(
                            "the witness hop {} -> {} is not an edge of the IR",
                            self.name_of(pair[0]),
                            self.name_of(pair[1])
                        ),
                    ));
                }
            }
        }
        for (c, w, d) in hits {
            self.fail(c, w, d);
        }
        self.done(V5_WITNESS, pop);
    }

    //--- V7 -----------------------------------------------------------------

    fn dead_reasons(&mut self) {
        let mine = self.derive_edges();
        let mut into: BTreeMap<NodeId, BTreeSet<NodeId>> = BTreeMap::new();
        for &(f, t, _) in mine.keys() {
            into.entry(t).or_default().insert(f);
        }
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        let mut pop = 0usize;
        for d in &self.live.dead {
            pop += 1;
            let t = &self.live.nodes[d.node as usize];
            let mi = t.key.module as usize;
            let m = self.modules[mi];
            // Zero references, by the IR's own indices.
            let local = m.occurrences(t.key.binder).len();
            let global = if t.external {
                self.gvars.get(&t.name).map(|v| v.len()).unwrap_or(0)
            } else {
                0
            };
            let zero = local + global == 0;
            let want = if zero {
                DeadReason::DeadNoReferences
            } else {
                DeadReason::DeadReferencedOnlyFromDead
            };
            if d.reason != want {
                hits.push((
                    V7_DEAD_REASON,
                    self.name_of(d.node),
                    format!(
                        "claims {} but has {} occurrence(s) in the world",
                        d.reason.label(),
                        local + global
                    ),
                ));
            }
            let want_refs: BTreeSet<NodeId> = into.get(&d.node).cloned().unwrap_or_default();
            let got: BTreeSet<NodeId> = d.referrers.iter().copied().collect();
            if got != want_refs {
                hits.push((
                    V7_DEAD_REASON,
                    self.name_of(d.node),
                    format!(
                        "records {} referrer(s), the IR gives {}",
                        got.len(),
                        want_refs.len()
                    ),
                ));
            }
        }
        for (c, w, dt) in hits {
            self.fail(c, w, dt);
        }
        self.done(V7_DEAD_REASON, pop);
    }

    //--- V8 -----------------------------------------------------------------

    fn accounting(&mut self) {
        let a = &self.live.accounting;
        let mut pop = 0usize;
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        let mut top = vec![0usize; self.modules.len()];
        let mut lv = vec![0usize; self.modules.len()];
        let mut d0 = vec![0usize; self.modules.len()];
        let mut d1 = vec![0usize; self.modules.len()];
        for t in &self.live.nodes {
            top[t.key.module as usize] += 1;
        }
        for l in &self.live.live {
            lv[self.live.nodes[l.node as usize].key.module as usize] += 1;
        }
        for d in &self.live.dead {
            let mi = self.live.nodes[d.node as usize].key.module as usize;
            match d.reason {
                DeadReason::DeadNoReferences => d0[mi] += 1,
                DeadReason::DeadReferencedOnlyFromDead => d1[mi] += 1,
            }
        }
        for (mi, m) in self.modules.iter().enumerate() {
            pop += 1;
            let Some(row) = a.modules.get(mi) else {
                hits.push((V8_ACCOUNTING, m.name.clone(), "no accounting row".into()));
                continue;
            };
            if row.module != m.name {
                hits.push((
                    V8_ACCOUNTING,
                    m.name.clone(),
                    format!("row {mi} is {}", row.module),
                ));
            }
            if (row.top, row.live, row.dead_no_refs, row.dead_only_from_dead)
                != (top[mi], lv[mi], d0[mi], d1[mi])
            {
                hits.push((
                    V8_ACCOUNTING,
                    m.name.clone(),
                    format!(
                        "row ({}, {}, {}, {}) but the contents give ({}, {}, {}, {})",
                        row.top,
                        row.live,
                        row.dead_no_refs,
                        row.dead_only_from_dead,
                        top[mi],
                        lv[mi],
                        d0[mi],
                        d1[mi]
                    ),
                ));
            }
            if row.top != row.live + row.dead() {
                hits.push((V8_ACCOUNTING, m.name.clone(), "top != live + dead".into()));
            }
        }
        pop += 1;
        if a.top != self.live.nodes.len()
            || a.live != self.live.live.len()
            || a.dead != self.live.dead.len()
            || a.top != a.live + a.dead
        {
            hits.push((
                V8_ACCOUNTING,
                "TOTAL".into(),
                format!(
                    "top {} live {} dead {} against {} nodes, {} live, {} dead",
                    a.top,
                    a.live,
                    a.dead,
                    self.live.nodes.len(),
                    self.live.live.len(),
                    self.live.dead.len()
                ),
            ));
        }
        pop += 1;
        if a.dead != a.dead_no_refs + a.dead_only_from_dead {
            hits.push((
                V8_ACCOUNTING,
                "TOTAL".into(),
                "dead != no-refs + only-from-dead".into(),
            ));
        }
        for (c, w, d) in hits {
            self.fail(c, w, d);
        }
        self.done(V8_ACCOUNTING, pop);
    }
}

impl Checker<'_> {
    //--- V9 -----------------------------------------------------------------

    fn zero_reference(&mut self) {
        let mut mine: BTreeSet<NodeId> = BTreeSet::new();
        for (i, t) in self.live.nodes.iter().enumerate() {
            let m = self.modules[t.key.module as usize];
            let local = m.occurrences(t.key.binder).len();
            let global = if t.external {
                self.gvars.get(&t.name).map(|v| v.len()).unwrap_or(0)
            } else {
                0
            };
            if local + global == 0 {
                mine.insert(i as NodeId);
            }
        }
        let theirs: BTreeSet<NodeId> = self.live.zero_reference.iter().copied().collect();
        let pop = mine.len() + theirs.len();
        let mut hits: Vec<(&'static str, String, String)> = Vec::new();
        for &n in mine.difference(&theirs) {
            hits.push((
                V9_ZERO_REFERENCE,
                self.name_of(n),
                "has no occurrence in the world and is not in the zero-reference set".into(),
            ));
        }
        for &n in theirs.difference(&mine) {
            hits.push((
                V9_ZERO_REFERENCE,
                self.name_of(n),
                "is in the zero-reference set and does have an occurrence".into(),
            ));
        }
        for &n in &theirs {
            if self.live.is_live(n) && !self.live.is_root(n) {
                hits.push((
                    V9_ZERO_REFERENCE,
                    self.name_of(n),
                    "is zero-reference, not a root and claimed live: the subset gate fails".into(),
                ));
            }
        }
        for (c, w, d) in hits {
            self.fail(c, w, d);
        }
        self.done(V9_ZERO_REFERENCE, pop);
    }
}

/// For every node of a module's arena, the flat top-level pair index it
/// lies in — by climbing [`Module::parent`] to the root and reading the
/// [`Edge::Top`] it arrived by, memoised so the whole arena costs one
/// pass. `u32::MAX` for a node no top-level pair encloses (there are
/// none; the map is built without assuming it).
fn owners(m: &Module) -> Vec<u32> {
    let n = m.exprs.len();
    let mut out = vec![u32::MAX - 1; n];
    let mut path: Vec<usize> = Vec::new();
    for start in 0..n {
        if out[start] != u32::MAX - 1 {
            continue;
        }
        path.clear();
        let mut cur = start;
        let found = loop {
            if out[cur] != u32::MAX - 1 {
                break out[cur];
            }
            path.push(cur);
            match m.parent[cur] {
                Some(p) => cur = p as usize,
                None => {
                    break match m.edge[cur] {
                        Edge::Top { pair } => pair,
                        _ => u32::MAX,
                    };
                }
            }
        };
        for &p in &path {
            out[p] = found;
        }
    }
    out
}
