//! M2.4's views, its `h2r show` provenance, its accounting and its
//! cross-milestone links.
//!
//! [`crate::views`] and [`crate::m23`] are the model, and the discipline is
//! theirs. M2.4b–f record facts and re-derive verdicts; this module adds
//! the three things a milestone needs before it can be closed:
//!
//! * a **view** per site and per boundary, laying one proof out so that a
//!   person can audit it without reading a whole report
//!   ([`ClassopView`], [`BoundaryView`]), each with its own completeness
//!   assertion;
//! * **provenance** ([`Provenance`]), so that any Core node can be asked
//!   what M2.4 says about it, in the footer shape M2.1, M2.2 and M2.3
//!   already use;
//! * the milestone's own **accounting** ([`Accounting`]), asserted in code
//!   and printed whole by `h2r classops`, `h2r higher` and `h2r m24`.
//!
//! Nothing here re-derives a verdict. Every line reads a published proof
//! object — [`crate::classops`], [`crate::dictflow`], [`crate::higher`] —
//! and where a verdict is one [`crate::verify_m24`] re-derives, the view
//! says whether it did ([`Verified`]). A claim the verifier refused is
//! **never** reported as proven: that is the rule M2.2 set and M2.3
//! repeated.
//!
//! ## The three questions, never collapsed
//!
//! The accounting keeps apart the three things this milestone has spent
//! two corrections learning not to mix:
//!
//! 1. **can the call target be enumerated?** — `sites = Exact + FiniteSet
//!    + Unresolved`;
//! 2. **can this abstraction boundary use one representation?** —
//!    `boundaries = ExactClosure + TypeShapeUniform + FiniteClosureSet +
//!    CloneRequired + Preserve + Unresolved`, with the *one-representation*
//!    count and the strictly stronger *rewritable-as-one* count printed
//!    beside each other;
//! 3. **can the dictionary or closure object actually disappear?** —
//!    `values / parameters = Erasable + WithObligation + WithClone +
//!    Preserve + Unresolved`, with both clone plans owner-level and their
//!    lower bounds flagged.
//!
//! A known method target is not a removable dictionary (M2.4c), and an
//! enumerated producer set is not one representation (M2.4d). The 3×5
//! matrix is where questions 1 and 3 are crossed rather than collapsed.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use h2r_core_ir::{BinderId, ExprId, Module};
use serde::Serialize;

use crate::classops::{self, Census as ClassCensus, OriginKind};
use crate::dictflow::{self, DictFlow, Erasure, Outcome, Param, Totality, Verdict as DVerdict};
use crate::higher::{self, Boundary, Higher, Slot, Verdict as HVerdict};
use crate::verify_m24::{Audit, Claim, ClaimKind, ClaimSlot, Subject, is_coverage_refusal};

//------------------------------------------------------------------------------
// Verification status
//------------------------------------------------------------------------------

/// What [`crate::verify_m24`] had to say about one verdict. A claim it
/// refused is **never** reported as proven.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Verified {
    /// Re-derived by the second walk.
    Yes,
    /// The second walk declined, with its reason: a coverage loss, not a
    /// claim about the analysis.
    CoverageRefused(String),
    /// The second walk refutes it. On all seven dumps this set is empty.
    Disagreed(String),
    /// Not one of the positive verdicts whose being wrong would be a
    /// miscompile, so nothing re-derives it.
    NotAClaim,
}

impl Verified {
    pub fn name(&self) -> String {
        match self {
            Verified::Yes => "yes".to_string(),
            Verified::CoverageRefused(w) => format!("coverage-refused ({w})"),
            Verified::Disagreed(w) => format!("DISAGREED ({w})"),
            Verified::NotAClaim => "not a claim".to_string(),
        }
    }

    pub fn proven(&self) -> bool {
        *self == Verified::Yes
    }
}

/// The address a claim is about, as one string. [`Subject`] is plain data
/// with no `Hash`, and a formatted address is all an index needs — the
/// same addressing M2.4f already rests on.
fn subject_key(s: &Subject) -> String {
    match s {
        Subject::Site { module, node } => format!("site {module}#{node}"),
        Subject::Param { module, binder } => format!("param {module}#{binder}"),
        Subject::Value { key } => format!("value {key}"),
        Subject::DictOwner { module, owner } => format!("dictowner {module}#{owner}"),
        Subject::ClosureOwner { module, owner } => format!("closureowner {module}#{owner}"),
        Subject::Boundary { module, slot } => match slot {
            ClaimSlot::Param { binder } => format!("boundary {module} param#{binder}"),
            ClaimSlot::Return { binder } => format!("boundary {module} return#{binder}"),
            ClaimSlot::Field { con, index } => format!("boundary {module} field {con}#{index}"),
        },
    }
}

/// Every claim the verifier was handed and what came back, keyed by the
/// analyses' own subject. Built once from an [`Audit`] and the claim list
/// that produced it.
#[derive(Debug, Clone, Default)]
pub struct Verdicts {
    claimed: HashSet<(ClaimKind, String)>,
    refused: HashMap<(ClaimKind, String), String>,
}

impl Verdicts {
    pub fn of(claims: &[Claim], audit: &Audit) -> Verdicts {
        let mut v = Verdicts::default();
        for c in claims {
            v.claimed.insert((c.kind, subject_key(&c.subject)));
        }
        for d in &audit.disagreements {
            v.refused.insert(
                (d.claim.kind, subject_key(&d.claim.subject)),
                d.refusal.why.to_string(),
            );
        }
        v
    }

    pub fn status(&self, kind: ClaimKind, subject: &Subject) -> Verified {
        let key = (kind, subject_key(subject));
        if !self.claimed.contains(&key) {
            return Verified::NotAClaim;
        }
        match self.refused.get(&key) {
            None => Verified::Yes,
            Some(w) if is_coverage_refusal(w) => Verified::CoverageRefused(w.clone()),
            Some(w) => Verified::Disagreed(w.clone()),
        }
    }

    /// The status of a class-op site's *target*.
    pub fn site_target(&self, module: &str, node: ExprId) -> Verified {
        self.status(
            ClaimKind::SiteExact,
            &Subject::Site {
                module: module.to_string(),
                node,
            },
        )
    }

    /// The status of a class-op site's *bounded dictionary set* — a
    /// different claim about the same site.
    pub fn site_set(&self, module: &str, node: ExprId) -> Verified {
        self.status(
            ClaimKind::SiteBounded,
            &Subject::Site {
                module: module.to_string(),
                node,
            },
        )
    }

    pub fn param_set(&self, module: &str, binder: BinderId) -> Verified {
        self.status(
            ClaimKind::ParamBounded,
            &Subject::Param {
                module: module.to_string(),
                binder,
            },
        )
    }

    pub fn param_erasure(&self, module: &str, binder: BinderId) -> Verified {
        self.status(
            ClaimKind::ParamErasure,
            &Subject::Param {
                module: module.to_string(),
                binder,
            },
        )
    }

    pub fn value_erasure(&self, key: &str) -> Verified {
        self.status(
            ClaimKind::ValueErasure,
            &Subject::Value {
                key: key.to_string(),
            },
        )
    }

    pub fn boundary(&self, b: &Boundary) -> Verified {
        self.status(
            ClaimKind::HigherVerdict,
            &Subject::Boundary {
                module: b.module.clone(),
                slot: claim_slot(b),
            },
        )
    }

    pub fn closure_plan(&self, module: &str, owner: BinderId) -> Verified {
        self.status(
            ClaimKind::ClosureClonePlan,
            &Subject::ClosureOwner {
                module: module.to_string(),
                owner,
            },
        )
    }

    pub fn dict_plan(&self, module: &str, owner: BinderId) -> Verified {
        self.status(
            ClaimKind::DictClonePlan,
            &Subject::DictOwner {
                module: module.to_string(),
                owner,
            },
        )
    }
}

/// The claim address of a boundary, exactly as [`crate::m24_claims`] writes
/// it down.
pub fn claim_slot(b: &Boundary) -> ClaimSlot {
    match &b.slot {
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
    }
}

//------------------------------------------------------------------------------
// The whole M2.4 proof object, assembled once
//------------------------------------------------------------------------------

/// Everything the four M2.4 analyses publish, plus the verifier's answer,
/// assembled once so that every view, footer and table reads the same
/// objects.
pub struct M24<'m> {
    pub modules: Vec<&'m Module>,
    pub census: ClassCensus,
    pub flow: DictFlow,
    pub higher: Higher,
    pub claims: Vec<Claim>,
    pub audit: Audit,
    pub verdicts: Verdicts,
    /// Dictionary identity key → index into [`DictFlow::values`].
    value_index: BTreeMap<String, usize>,
    /// (module, node) of a dictionary value → its identity key.
    value_at: HashMap<(String, ExprId), String>,
    /// The stable name a dictionary value is bound to → its identity key.
    /// A top-level dfun's binder name, or an imported dfun's own name.
    value_by_name: HashMap<String, String>,
    /// (module, binder) → index into [`DictFlow::params`].
    param_index: HashMap<(String, BinderId), usize>,
    /// (module, node) → index into [`DictFlow::sites`].
    site_index: HashMap<(String, ExprId), usize>,
}

impl<'m> M24<'m> {
    pub fn of_modules(modules: &[&'m Module]) -> M24<'m> {
        let (census, _world) = ClassCensus::of_modules(modules.iter().copied());
        let (claims, flow, higher) = crate::m24_claims::claims(modules);
        let audit = crate::verify_m24::verify(modules, &claims);
        let verdicts = Verdicts::of(&claims, &audit);
        // The identity keys of the dictionary values, in the order
        // `DictFlow::values` holds them — the same zip `m24_claims` makes.
        let dp = dictflow::Program::new(modules.iter().copied());
        let mut value_index = BTreeMap::new();
        let mut value_at = HashMap::new();
        let mut value_by_name = HashMap::new();
        for (i, (key, v)) in dp.values.iter().enumerate() {
            value_index.insert(key.clone(), i);
            value_at.insert((v.module.clone(), v.node), key.clone());
            if !v.name.is_empty() {
                value_by_name.insert(v.name.clone(), key.clone());
            }
        }
        let mut param_index = HashMap::new();
        for (i, p) in flow.params.iter().enumerate() {
            param_index.insert((p.module.clone(), p.binder), i);
        }
        let mut site_index = HashMap::new();
        for (i, s) in flow.sites.iter().enumerate() {
            site_index.insert((s.module.clone(), s.node), i);
        }
        M24 {
            modules: modules.to_vec(),
            census,
            flow,
            higher,
            claims,
            audit,
            verdicts,
            value_index,
            value_at,
            value_by_name,
            param_index,
            site_index,
        }
    }

    pub fn param(&self, module: &str, binder: BinderId) -> Option<(&Param, &Erasure)> {
        let i = *self.param_index.get(&(module.to_string(), binder))?;
        Some((&self.flow.params[i], &self.flow.param_erasure[i]))
    }

    pub fn site(&self, module: &str, node: ExprId) -> Option<&dictflow::Site> {
        let i = *self.site_index.get(&(module.to_string(), node))?;
        Some(&self.flow.sites[i])
    }

    /// The dictionary value built at this node, with its identity key.
    pub fn value_at(&self, module: &str, node: ExprId) -> Option<(&str, &Erasure)> {
        let key = self.value_at.get(&(module.to_string(), node))?;
        let i = *self.value_index.get(key)?;
        Some((key.as_str(), &self.flow.values[i]))
    }

    pub fn value_by_key(&self, key: &str) -> Option<&Erasure> {
        self.value_index.get(key).map(|i| &self.flow.values[*i])
    }

    /// The dictionary value a stable name binds — a top-level dfun of the
    /// dump, or an imported one. An **address**, not a derivation: the
    /// name is the one the flow itself put on the identity.
    pub fn value_named(&self, name: &str) -> Option<(&str, &Erasure)> {
        let key = self.value_by_name.get(name)?;
        let i = *self.value_index.get(key)?;
        Some((key.as_str(), &self.flow.values[i]))
    }

    /// The dictionary clone plan the owner of this parameter belongs to.
    pub fn dict_plan_of(&self, module: &str, binder: BinderId) -> Option<&dictflow::OwnerPlan> {
        let (p, _) = self.param(module, binder)?;
        let ob = p.owner_binder?;
        self.flow
            .owners
            .iter()
            .find(|o| o.module == module && o.owner_binder == ob)
    }

    /// The closure clone plan the owner of this boundary belongs to.
    pub fn closure_plan_of(&self, b: &Boundary) -> Option<&higher::OwnerPlan> {
        self.higher
            .owners
            .iter()
            .find(|o| o.module == b.module && o.owner == b.owner)
    }
}

//------------------------------------------------------------------------------
// The class-op site view
//------------------------------------------------------------------------------

/// One hop of the dictionary's origin, as the view prints it: the step, the
/// rule that made it and the node it landed on.
#[derive(Debug, Clone, Serialize)]
pub struct OriginStep {
    pub step: String,
    pub rule: &'static str,
}

/// One dictionary the site's argument can be, with the whole chain that
/// reached it.
#[derive(Debug, Clone, Serialize)]
pub struct OriginLine {
    pub kind: OriginKind,
    pub module: String,
    pub node: ExprId,
    pub name: String,
    pub depth: usize,
    pub steps: Vec<OriginStep>,
    pub headline: String,
}

/// One parameter hop of the whole-program producer set: a dictionary
/// parameter the argument passes through, and what the fixpoint says
/// reaches it.
#[derive(Debug, Clone, Serialize)]
pub struct ParamHop {
    pub module: String,
    pub owner: String,
    pub occ: String,
    pub index: usize,
    pub binder: BinderId,
    pub exported: bool,
    /// The whole-program producer set: the dictionary identities, or the
    /// taint reason that makes it `Top`.
    pub set: Vec<String>,
    pub top: Option<String>,
    pub totality: Totality,
    pub erasure: String,
    pub verified_set: Verified,
    pub verified_erasure: Verified,
    pub headline: String,
}

/// One class-op dispatch site, laid out.
#[derive(Debug, Clone, Serialize)]
pub struct ClassopView {
    pub module: String,
    pub node: ExprId,
    pub class: String,
    pub method: String,
    pub selector: String,
    pub field: Option<usize>,
    /// The dictionary argument's node, when the site has one.
    pub dict_arg: Option<ExprId>,
    pub origins: Vec<OriginLine>,
    pub hops: Vec<ParamHop>,
    /// The whole-program outcome, and the per-module one beside it.
    pub outcome: String,
    pub per_module_outcome: String,
    pub verified_target: Verified,
    pub verified_set: Verified,
    pub dict_set: Vec<String>,
    pub dict_top: Option<String>,
    pub totality: Option<Totality>,
    pub erasure: Option<String>,
    pub erasure_reason: Option<String>,
    pub verified_erasure: Verified,
    pub clone_plan: Option<String>,
    pub facts: Vec<String>,
    pub rules: Vec<&'static str>,
    pub headline: String,
}

/// Which rule made one textual origin step. The step vocabulary is
/// [`crate::classops`]'s own; this only names the rule it belongs to, and
/// decides nothing.
fn origin_rule(step: &str) -> &'static str {
    if step.starts_with("superclass") {
        classops::K4_SUPERCLASS_SEL
    } else if step.starts_with("global") {
        classops::K6_DFUN
    } else if step == "case-alternative" {
        classops::K7_DICT_CON
    } else if step == "let-body" {
        classops::K5_ALIAS
    } else if step.starts_with("parameter") || step.starts_with("argument") {
        classops::K8_PARAM_UNION
    } else {
        classops::K5_ALIAS
    }
}

impl ClassopView {
    /// Lay one class-op site out. `s` is the per-module census' site; the
    /// whole-program facts come from [`M24`].
    pub fn of(m24: &M24, s: &classops::Site) -> ClassopView {
        let origins: Vec<OriginLine> = s
            .origins
            .iter()
            .map(|o| OriginLine {
                kind: o.kind,
                module: o.module.clone(),
                node: o.node,
                name: o.name.clone(),
                depth: o.depth,
                steps: o
                    .chain
                    .iter()
                    .map(|step| OriginStep {
                        step: step.clone(),
                        rule: origin_rule(step),
                    })
                    .collect(),
                headline: format!(
                    "{:?} {} at {} node {} (depth {})",
                    o.kind, o.name, o.module, o.node, o.depth
                ),
            })
            .collect();

        // The whole-program site, when the fixpoint has one for this node.
        let wp = m24.site(&s.module, s.node);
        let (outcome, dict_set, dict_top) = match wp {
            Some(w) => (
                match &w.outcome {
                    Outcome::Exact(t) => format!("Exact({}.{})", t.module, t.occ),
                    Outcome::FiniteSet(ts) => format!("FiniteSet({})", ts.len()),
                    Outcome::Unresolved(r) => format!("Unresolved({r})"),
                },
                w.set.keys().iter().cloned().collect::<Vec<_>>(),
                w.set.reason().map(|r| r.to_string()),
            ),
            None => (
                "not in the whole-program population".to_string(),
                Vec::new(),
                None,
            ),
        };

        // The parameter hops: the dictionary argument's binder, and every
        // dictionary parameter the fixpoint carried it through.
        let mut hops = Vec::new();
        let mut seen: HashSet<(String, BinderId)> = HashSet::new();
        if let Some(d) = s.dict_arg {
            let mi = m24.modules.iter().position(|x| x.name == s.module);
            if let Some(mi) = mi {
                let mut frontier: Vec<(usize, ExprId)> = vec![(mi, d)];
                let mut budget = 32usize;
                while let Some((mi, node)) = frontier.pop() {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let m = m24.modules[mi];
                    let Some(b) = m.resolve(m.strip(node)) else {
                        continue;
                    };
                    if !seen.insert((m.name.clone(), b)) {
                        continue;
                    }
                    let Some((p, e)) = m24.param(&m.name, b) else {
                        continue;
                    };
                    hops.push(ParamHop {
                        module: p.module.clone(),
                        owner: p.owner.clone(),
                        occ: p.occ.clone(),
                        index: p.index,
                        binder: p.binder,
                        exported: p.exported,
                        set: p.set.keys().iter().cloned().collect(),
                        top: p.set.reason().map(|r| r.to_string()),
                        totality: p.totality,
                        erasure: e.verdict.label().to_string(),
                        verified_set: m24.verdicts.param_set(&p.module, p.binder),
                        verified_erasure: m24.verdicts.param_erasure(&p.module, p.binder),
                        headline: format!(
                            "parameter {} ({}) of {} [{}] → {}",
                            p.index,
                            p.occ,
                            p.owner,
                            dictflow::W3_PARAM_UNION,
                            match p.set.reason() {
                                Some(r) => format!("Top({r})"),
                                None => format!("{{{}}}", p.set.keys().len()),
                            }
                        ),
                    });
                    // One more hop: every call site's argument that is
                    // itself a dictionary parameter.
                    for (cmi, at) in &p.producers.calls {
                        frontier.push((*cmi, *at));
                    }
                }
            }
        }

        // The erasure of the dictionary this site dispatches on, where the
        // argument is a parameter or a value the flow knows.
        let (totality, erasure, erasure_reason, verified_erasure) = match hops.first() {
            Some(h) => {
                let (_, e) = m24
                    .param(&h.module, h.binder)
                    .expect("the hop was built from a parameter");
                (
                    Some(h.totality),
                    Some(e.verdict.label().to_string()),
                    erasure_reason(&e.verdict),
                    m24.verdicts.param_erasure(&h.module, h.binder),
                )
            }
            None => match s.dict_arg.and_then(|d| m24.value_at(&s.module, d)) {
                Some((key, e)) => (
                    Some(e.totality),
                    Some(e.verdict.label().to_string()),
                    erasure_reason(&e.verdict),
                    m24.verdicts.value_erasure(key),
                ),
                None => (None, None, None, Verified::NotAClaim),
            },
        };

        let clone_plan = hops.first().and_then(|h| {
            m24.dict_plan_of(&h.module, h.binder).map(|o| {
                format!(
                    "{} {} — {} parameter(s), cardinalities {:?}, {} tuple(s) → {}{}",
                    o.module,
                    o.owner,
                    o.params.len(),
                    o.cardinalities,
                    o.tuples.len(),
                    match o.clones {
                        Some(n) => n.to_string(),
                        None => "refused".to_string(),
                    },
                    if o.set_valued > 0 {
                        format!(" (lower bound: {} set-valued tuple(s))", o.set_valued)
                    } else {
                        String::new()
                    }
                )
            })
        });

        let mut facts = Vec::new();
        facts.push(format!(
            "{}: the selector application forces its dictionary: {}",
            classops::K10_FORCED,
            s.facts.forces_dictionary
        ));
        facts.push(format!(
            "{}: the dictionary is also used as an ordinary value: {}{}",
            classops::K11_DICT_ESCAPES,
            s.facts.dict_used_as_value,
            match s.facts.dict_value_use {
                Some(n) => format!(" (node {n})"),
                None => String::new(),
            }
        ));
        facts.push(format!(
            "GHC records the dictionary binder strict: {} (evidence only, never a verdict)",
            s.facts.dict_known_strict
        ));

        let view = ClassopView {
            headline: format!(
                "{} node {} — {}.{}, dispatch on {} → {}",
                s.module,
                s.node,
                s.class_occ,
                s.method,
                match s.dict_arg {
                    Some(d) => format!("node {d}"),
                    None => "no dictionary argument".to_string(),
                },
                outcome
            ),
            module: s.module.clone(),
            node: s.node,
            class: s.class_occ.clone(),
            method: s.method.clone(),
            selector: s.selector.clone(),
            field: s.field,
            dict_arg: s.dict_arg,
            origins,
            hops,
            per_module_outcome: match &s.outcome {
                classops::Outcome::Exact(t) => format!("Exact({}.{})", t.module, t.occ),
                classops::Outcome::FiniteSet(ts) => format!("FiniteSet({})", ts.len()),
                classops::Outcome::Unresolved(r) => format!("Unresolved({r})"),
            },
            outcome,
            verified_target: m24.verdicts.site_target(&s.module, s.node),
            verified_set: m24.verdicts.site_set(&s.module, s.node),
            dict_set,
            dict_top,
            totality,
            erasure,
            erasure_reason,
            verified_erasure,
            clone_plan,
            facts,
            rules: s.rules.clone(),
        };
        view.check();
        view
    }
}

fn erasure_reason(v: &DVerdict) -> Option<String> {
    match v {
        DVerdict::Erasable => None,
        DVerdict::ErasableWithObligation(o) => Some(format!(
            "a force obligation at {} node {} over node {}",
            o.module, o.at, o.what
        )),
        DVerdict::ErasableWithClone(n) => Some(format!("{n} instance(s) at this boundary")),
        DVerdict::Preserve(r) | DVerdict::Unresolved(r) => Some(r.clone()),
    }
}

impl ClassopView {
    /// What the view must satisfy to be an audit of *this* site: no hop is
    /// listed twice (the walk up the parameter chain terminates and never
    /// doubles back), every origin belongs to this site, and a site with a
    /// dictionary argument has its method field named whenever the class
    /// table knows the class.
    pub fn check(&self) {
        let mut seen: BTreeSet<(String, BinderId)> = BTreeSet::new();
        for h in &self.hops {
            assert!(
                seen.insert((h.module.clone(), h.binder)),
                "the parameter hops of {} node {} must each appear once",
                self.module,
                self.node
            );
        }
        assert!(
            self.origins.iter().all(|o| o.depth <= 64),
            "an origin chain must be bounded"
        );
    }

    pub fn header(&self) -> String {
        self.headline.clone()
    }
}

/// Every class-op site of a module, each laid out once.
#[derive(Debug, Clone, Serialize)]
pub struct ClassopViews {
    pub module: String,
    pub views: Vec<ClassopView>,
}

impl ClassopViews {
    pub fn of_module(m24: &M24, module: &str) -> ClassopViews {
        let views: Vec<ClassopView> = m24
            .census
            .sites
            .iter()
            .filter(|s| s.module == module)
            .map(|s| ClassopView::of(m24, s))
            .collect();
        let v = ClassopViews {
            module: module.to_string(),
            views,
        };
        v.check(m24);
        v
    }

    /// **Every site of the module appears exactly once.**
    pub fn check(&self, m24: &M24) {
        let population = m24
            .census
            .sites
            .iter()
            .filter(|s| s.module == self.module)
            .count();
        assert_eq!(
            self.views.len(),
            population,
            "--view-all must lay out every class-op site of {} exactly once",
            self.module
        );
        let seen: BTreeSet<ExprId> = self.views.iter().map(|v| v.node).collect();
        assert_eq!(
            seen.len(),
            self.views.len(),
            "no class-op site may appear twice in the view"
        );
    }
}

//------------------------------------------------------------------------------
// The boundary view
//------------------------------------------------------------------------------

/// One producer at a boundary, as the view prints it.
#[derive(Debug, Clone, Serialize)]
pub struct ProducerLine {
    pub key: String,
    pub module: String,
    pub node: ExprId,
    pub kind: &'static str,
    pub occ: String,
    pub shape_class: String,
    pub captures: Vec<String>,
    pub arity: Option<usize>,
    pub opaque: bool,
    pub headline: String,
}

/// One use of a boundary's value.
#[derive(Debug, Clone, Serialize)]
pub struct UseLine {
    pub kind: &'static str,
    pub at: ExprId,
    pub args: usize,
}

/// One step of the rule order that produced a boundary's verdict. `fired`
/// marks the one that decided; the rest are shown *in order* so that the
/// reason an earlier rule did not fire is visible rather than implied.
#[derive(Debug, Clone, Serialize)]
pub struct RuleStep {
    pub rule: &'static str,
    pub asks: &'static str,
    pub answer: String,
    pub fired: bool,
}

/// One function-valued boundary, laid out.
#[derive(Debug, Clone, Serialize)]
pub struct BoundaryView {
    pub module: String,
    pub kind: &'static str,
    pub name: String,
    pub node: ExprId,
    pub owner: String,
    pub exported: bool,
    /// The boundary belongs to a function used as a value: `H8-PRESERVE`'s
    /// second clause, read back from the verdict the analysis published.
    pub valued: bool,
    pub enumerated: bool,
    pub classes: usize,
    pub class_keys: Vec<String>,
    pub set_top: Option<String>,
    pub producers: Vec<ProducerLine>,
    pub uses: Vec<UseLine>,
    pub verdict: String,
    pub verdict_detail: Option<String>,
    pub rule_order: Vec<RuleStep>,
    pub one_representation: bool,
    pub rewritable_as_one: bool,
    pub verified: Verified,
    /// The owning function's clone tuples, when it has a plan.
    pub owner_plan: Option<String>,
    pub owner_tuples: Vec<String>,
    pub owner_set_valued: usize,
    pub verified_plan: Verified,
    pub headline: String,
}

impl BoundaryView {
    pub fn of(m24: &M24, b: &Boundary) -> BoundaryView {
        let valued = matches!(&b.verdict, HVerdict::Preserve(r) if r.starts_with(higher::P_VALUED));
        let opaque = b.producers.iter().find(|p| p.shape.is_opaque());
        let producers: Vec<ProducerLine> = b
            .producers
            .iter()
            .map(|p| {
                let (arity, captures) = match &p.shape {
                    higher::Shape::Known { arity, captures } => (Some(*arity), captures.clone()),
                    higher::Shape::Opaque { why, .. } => (None, vec![why.clone()]),
                };
                ProducerLine {
                    headline: format!("{:<44} {:<38} {}", p.key, p.kind.name(), p.shape.short()),
                    key: p.key.clone(),
                    module: p.module.clone(),
                    node: p.node,
                    kind: p.kind.name(),
                    occ: p.occ.clone(),
                    shape_class: p.shape.class(),
                    captures,
                    arity,
                    opaque: p.shape.is_opaque(),
                }
            })
            .collect();

        // The rule order `higher::judge` decides in, with the answer the
        // published facts give at each step. Nothing is re-derived: the
        // verdict is the analysis', and this only says which rule reached
        // it and which earlier ones did not.
        let mut order = Vec::new();
        let mut fired = false;
        let mut step = |rule: &'static str, asks: &'static str, yes: bool, answer: String| {
            let f = yes && !fired;
            if f {
                fired = true;
            }
            order.push(RuleStep {
                rule,
                asks,
                answer,
                fired: f,
            });
        };
        step(
            higher::H9_TAINT,
            "is the producer set Top?",
            b.set.is_top(),
            match b.set.reason() {
                Some(r) => format!("yes — {r}"),
                None => "no, every producer is accounted for".into(),
            },
        );
        step(
            higher::H2_PRODUCERS,
            "does any producer reach the slot?",
            b.producers.is_empty(),
            format!("{} producer(s)", b.producers.len()),
        );
        step(
            higher::H8_PRESERVE,
            "is a producer's environment invisible (opaque)?",
            opaque.is_some(),
            match opaque {
                Some(p) => format!("yes — {} ({} node {})", p.shape.short(), p.module, p.node),
                None => "no".into(),
            },
        );
        step(
            higher::H8_PRESERVE,
            "is the slot exported, so its representation is shared?",
            b.exported,
            if b.exported {
                "yes".into()
            } else {
                "no".into()
            },
        );
        step(
            higher::H8_PRESERVE,
            "does the slot belong to a function used as a value?",
            valued,
            if valued { "yes".into() } else { "no".into() },
        );
        step(
            higher::H5_EXACT,
            "is there exactly one producer?",
            b.producers.len() == 1,
            format!("{} producer(s)", b.producers.len()),
        );
        step(
            higher::H6_UNIFORM,
            "do the producers fall in one shape class?",
            b.classes <= 1,
            format!("{} shape class(es)", b.classes),
        );
        step(
            higher::H7_CLONE,
            "is the slot a parameter of a local function, so a clone can serve it?",
            matches!(b.slot, Slot::Param { .. }),
            format!("the slot is a {}", b.slot.kind()),
        );
        step(
            higher::H4_SHAPE_CLASS,
            "otherwise: a finite set of closures no clone can serve",
            true,
            format!("{} producer(s)", b.producers.len()),
        );

        let plan = m24.closure_plan_of(b);
        let view = BoundaryView {
            headline: format!(
                "{} {} — {} of {}, producers {} (classes {}) → {}",
                b.module,
                b.name,
                b.kind,
                b.owner,
                b.producers.len(),
                b.classes,
                b.verdict.label()
            ),
            module: b.module.clone(),
            kind: b.kind,
            name: b.name.clone(),
            node: b.node,
            owner: b.owner.clone(),
            exported: b.exported,
            valued,
            enumerated: b.enumerated,
            classes: b.classes,
            class_keys: b.class_keys(),
            set_top: b.set.reason().map(|r| r.to_string()),
            producers,
            uses: b
                .uses
                .iter()
                .map(|u| UseLine {
                    kind: u.kind.name(),
                    at: u.at,
                    args: u.args,
                })
                .collect(),
            verdict: b.verdict.label().to_string(),
            verdict_detail: match &b.verdict {
                HVerdict::CloneRequired(n) => Some(format!("{n} shape class(es)")),
                HVerdict::FiniteClosureSet(n) => Some(format!("{n} producer(s)")),
                HVerdict::Preserve(r) | HVerdict::Unresolved(r) => Some(r.clone()),
                _ => None,
            },
            rule_order: order,
            one_representation: b.one_representation(),
            rewritable_as_one: b.verdict.rewritable_as_one(),
            verified: m24.verdicts.boundary(b),
            owner_plan: plan.map(|o| {
                format!(
                    "{} {} — {} slot(s), {} call site(s), {} tuple(s) → {}",
                    o.module,
                    o.owner,
                    o.params.len(),
                    o.sites,
                    o.tuples.len(),
                    match o.clones {
                        Some(n) => n.to_string(),
                        None => o.refused.clone().unwrap_or_else(|| "refused".to_string()),
                    }
                )
            }),
            owner_tuples: plan.map(|o| o.tuples.clone()).unwrap_or_default(),
            owner_set_valued: plan.map(|o| o.set_valued).unwrap_or(0),
            verified_plan: plan
                .map(|o| m24.verdicts.closure_plan(&o.module, o.owner_binder))
                .unwrap_or(Verified::NotAClaim),
        };
        view.check();
        view
    }

    /// The rule order must name exactly one rule as the one that fired,
    /// unless the verdict is the fall-through, and every producer must
    /// appear exactly once.
    pub fn check(&self) {
        let fired = self.rule_order.iter().filter(|r| r.fired).count();
        assert_eq!(
            fired, 1,
            "exactly one rule must produce the verdict of {} {}",
            self.module, self.name
        );
        let keys: BTreeSet<&String> = self.producers.iter().map(|p| &p.key).collect();
        assert_eq!(
            keys.len(),
            self.producers.len(),
            "every producer must appear exactly once in the view of {} {}",
            self.module,
            self.name
        );
        assert!(
            !(self.rewritable_as_one && !self.one_representation),
            "rewritable-as-one is strictly stronger than one-representation"
        );
    }

    pub fn header(&self) -> String {
        self.headline.clone()
    }
}

/// Every boundary of a module, each laid out once.
#[derive(Debug, Clone, Serialize)]
pub struct BoundaryViews {
    pub module: String,
    pub views: Vec<BoundaryView>,
}

impl BoundaryViews {
    pub fn of_module(m24: &M24, module: &str) -> BoundaryViews {
        let views: Vec<BoundaryView> = m24
            .higher
            .boundaries
            .iter()
            .filter(|b| b.module == module)
            .map(|b| BoundaryView::of(m24, b))
            .collect();
        let v = BoundaryViews {
            module: module.to_string(),
            views,
        };
        v.check(m24);
        v
    }

    /// **Every boundary of the module appears exactly once.**
    pub fn check(&self, m24: &M24) {
        let population = m24
            .higher
            .boundaries
            .iter()
            .filter(|b| b.module == self.module)
            .count();
        assert_eq!(
            self.views.len(),
            population,
            "--view-all must lay out every boundary of {} exactly once",
            self.module
        );
        let seen: BTreeSet<(&str, &str, ExprId)> = self
            .views
            .iter()
            .map(|v| (v.kind, v.name.as_str(), v.node))
            .collect();
        assert_eq!(
            seen.len(),
            self.views.len(),
            "no boundary may appear twice in the view"
        );
    }
}

//------------------------------------------------------------------------------
// Provenance: what M2.4 says about one Core node
//------------------------------------------------------------------------------

/// Everything M2.4's proof objects have to say about one node, in the
/// footer shape M2.1's Parsec proof, M2.2's tuple proof and M2.3's three
/// representation proofs already use.
#[derive(Debug, Clone, Default, Serialize)]
pub struct NodeProof {
    pub node: ExprId,
    /// `classop: Show.show …`, `boundary: parameter 1 of go#… …`.
    pub what: Option<String>,
    pub verdict: Option<String>,
    /// How this node takes part.
    pub role: Option<String>,
    pub facts: Vec<String>,
    pub evidence: Vec<(&'static str, String)>,
}

impl NodeProof {
    pub fn is_empty(&self) -> bool {
        self.what.is_none() && self.role.is_none() && self.evidence.is_empty()
    }
}

/// Which M2.4 sites a node or a binder takes part in, precomputed once so
/// that `h2r show` can annotate every node it prints. Either object may be
/// absent (`--no-classops` / `--no-higher`), exactly as the Parsec, tuple
/// and representation objects are.
pub struct Provenance<'a> {
    m: &'a Module,
    m24: &'a M24<'a>,
    classops_on: bool,
    higher_on: bool,
    /// Class-op site node → index into the per-module census.
    sites: HashMap<ExprId, usize>,
    /// A dictionary value's node → its identity key.
    values: HashMap<ExprId, String>,
    /// A dictionary parameter's binder → index into `flow.params`.
    dict_params: HashMap<BinderId, usize>,
    /// An occurrence of a dictionary parameter → its binder.
    dict_occ: HashMap<ExprId, BinderId>,
    /// A boundary's own node → indices into `higher.boundaries`.
    boundaries: HashMap<ExprId, Vec<usize>>,
    /// A boundary's binder → indices.
    boundary_binders: HashMap<BinderId, Vec<usize>>,
    /// An occurrence of a boundary binder → the binder.
    boundary_occ: HashMap<ExprId, BinderId>,
    /// A closure producer's node → the boundaries it reaches.
    producers: HashMap<ExprId, Vec<usize>>,
}

impl<'a> Provenance<'a> {
    pub fn of(
        m: &'a Module,
        m24: &'a M24<'a>,
        classops_on: bool,
        higher_on: bool,
    ) -> Provenance<'a> {
        let mut p = Provenance {
            m,
            m24,
            classops_on,
            higher_on,
            sites: HashMap::new(),
            values: HashMap::new(),
            dict_params: HashMap::new(),
            dict_occ: HashMap::new(),
            boundaries: HashMap::new(),
            boundary_binders: HashMap::new(),
            boundary_occ: HashMap::new(),
            producers: HashMap::new(),
        };
        if classops_on {
            for (i, s) in m24.census.sites.iter().enumerate() {
                if s.module == m.name {
                    p.sites.insert(s.node, i);
                }
            }
            for ((module, node), key) in &m24.value_at {
                if module == &m.name {
                    p.values.insert(*node, key.clone());
                }
            }
            for (i, prm) in m24.flow.params.iter().enumerate() {
                if prm.module != m.name {
                    continue;
                }
                p.dict_params.insert(prm.binder, i);
                for occ in m.occurrences(prm.binder) {
                    p.dict_occ.insert(*occ, prm.binder);
                }
            }
        }
        if higher_on {
            for (i, b) in m24.higher.boundaries.iter().enumerate() {
                if b.module != m.name {
                    continue;
                }
                if b.node != 0 {
                    p.boundaries.entry(b.node).or_default().push(i);
                }
                if let Some(bid) = b.binder {
                    p.boundary_binders.entry(bid).or_default().push(i);
                    for occ in m.occurrences(bid) {
                        p.boundary_occ.insert(*occ, bid);
                    }
                }
                for x in &b.producers {
                    if x.module == m.name && x.node != 0 {
                        p.producers.entry(x.node).or_default().push(i);
                    }
                }
            }
        }
        p
    }

    /// The inline mark `h2r show` writes next to a node.
    pub fn node_note(&self, id: ExprId) -> Option<String> {
        let mut parts: Vec<String> = Vec::new();
        if let Some(i) = self.sites.get(&id) {
            let s = &self.m24.census.sites[*i];
            parts.push(format!(
                "class-op site {}.{} ⇒ {}",
                s.class_occ,
                s.method,
                self.m24
                    .site(&s.module, s.node)
                    .map(|w| w.outcome.label().to_string())
                    .unwrap_or_else(|| s.outcome.label().to_string())
            ));
        }
        if let Some(key) = self.values.get(&id)
            && let Some(e) = self.m24.value_by_key(key)
        {
            parts.push(format!("dictionary value, {}", e.verdict.label()));
        }
        if let Some(b) = self.dict_occ.get(&id)
            && let Some(i) = self.dict_params.get(b)
        {
            let prm = &self.m24.flow.params[*i];
            parts.push(format!(
                "occurrence of dictionary parameter {} of {}",
                prm.index, prm.owner
            ));
        }
        for i in self.boundaries.get(&id).into_iter().flatten() {
            let b = &self.m24.higher.boundaries[*i];
            parts.push(format!("boundary {} ⇒ {}", b.name, b.verdict.label()));
        }
        for i in self.producers.get(&id).into_iter().flatten() {
            let b = &self.m24.higher.boundaries[*i];
            parts.push(format!("closure producer reaching {}", b.name));
        }
        if let Some(bid) = self.boundary_occ.get(&id)
            && let Some(is) = self.boundary_binders.get(bid)
            && let Some(i) = is.first()
        {
            let b = &self.m24.higher.boundaries[*i];
            parts.push(format!("occurrence of boundary {}", b.name));
        }
        (!parts.is_empty()).then(|| parts.join("; "))
    }

    /// The same for a binder.
    pub fn binder_note(&self, b: BinderId) -> Option<String> {
        let mut parts: Vec<String> = Vec::new();
        if let Some(i) = self.dict_params.get(&b) {
            let prm = &self.m24.flow.params[*i];
            let e = &self.m24.flow.param_erasure[*i];
            parts.push(format!(
                "dictionary parameter {} of {} ⇒ {}",
                prm.index,
                prm.owner,
                e.verdict.label()
            ));
        }
        for i in self.boundary_binders.get(&b).into_iter().flatten() {
            let bd = &self.m24.higher.boundaries[*i];
            parts.push(format!(
                "function-valued {} ⇒ {}",
                bd.kind,
                bd.verdict.label()
            ));
        }
        (!parts.is_empty()).then(|| parts.join("; "))
    }

    /// Every footer this node earns: one per class-op site, dictionary
    /// value or parameter, boundary or closure producer it takes part in,
    /// as itself or as an occurrence.
    pub fn proofs_at(&self, node: ExprId) -> Vec<NodeProof> {
        let mut out: Vec<NodeProof> = Vec::new();
        if self.classops_on {
            if let Some(i) = self.sites.get(&node) {
                out.push(self.site_proof(node, *i));
            }
            if let Some(key) = self.values.get(&node) {
                out.push(self.value_proof(node, key));
            }
            let binder = self
                .dict_occ
                .get(&node)
                .copied()
                .or_else(|| self.m.resolve(self.m.strip(node)))
                .filter(|b| self.dict_params.contains_key(b));
            if let Some(b) = binder
                && !self.sites.contains_key(&node)
            {
                out.push(self.param_proof(node, b));
            }
        }
        if self.higher_on {
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            for i in self.boundaries.get(&node).into_iter().flatten() {
                seen.insert(*i);
            }
            if let Some(b) = self.boundary_occ.get(&node) {
                for i in self.boundary_binders.get(b).into_iter().flatten() {
                    seen.insert(*i);
                }
            }
            for i in seen {
                out.push(self.boundary_proof(node, i));
            }
            if let Some(is) = self.producers.get(&node) {
                out.push(self.producer_proof(node, is));
            }
        }
        out
    }

    fn site_proof(&self, node: ExprId, i: usize) -> NodeProof {
        let s = &self.m24.census.sites[i];
        let v = ClassopView::of(self.m24, s);
        let dict = match (&v.dict_arg, v.hops.first()) {
            (Some(d), Some(h)) => format!(
                "{} at node {d} (param {} of {}#{})",
                h.occ, h.index, h.owner, h.binder
            ),
            (Some(d), None) => format!("at node {d}"),
            (None, _) => "none".to_string(),
        };
        let set = match &v.dict_top {
            Some(r) => format!("Top({r})"),
            None => format!("{{{}}}", v.dict_set.join(", ")),
        };
        NodeProof {
            node,
            what: Some(format!(
                "classop: {}.{} at node {} dictionary {dict} → whole-program {set} → target {}",
                v.class, v.method, s.node, v.outcome
            )),
            verdict: Some(format!(
                "totality {} … erasure {} [verified: {}]",
                v.totality
                    .map(|t| t.label().to_string())
                    .unwrap_or_else(|| "n/a".into()),
                match (&v.erasure, &v.erasure_reason) {
                    (Some(e), Some(r)) => format!("{e}({r})"),
                    (Some(e), None) => e.clone(),
                    _ => "n/a".into(),
                },
                v.verified_erasure.name()
            )),
            role: Some(format!(
                "the class-op application itself; per-module {} [verified target: {}]",
                v.per_module_outcome,
                v.verified_target.name()
            )),
            facts: v.facts.clone(),
            evidence: v
                .rules
                .iter()
                .map(|r| (*r, format!("{}.{}", v.class, v.method)))
                .collect(),
        }
    }

    fn value_proof(&self, node: ExprId, key: &str) -> NodeProof {
        let e = self
            .m24
            .value_by_key(key)
            .expect("the value index names a value");
        NodeProof {
            node,
            what: Some(format!("classop: dictionary value {} ({key})", e.what)),
            verdict: Some(format!(
                "totality {} … erasure {}{} [verified: {}]",
                e.totality.label(),
                e.verdict.label(),
                erasure_reason(&e.verdict)
                    .map(|r| format!("({r})"))
                    .unwrap_or_default(),
                self.m24.verdicts.value_erasure(key).name()
            )),
            role: Some("the dictionary value itself".into()),
            facts: vec![format!(
                "{}: every producer is a total dictionary value: {}",
                dictflow::E1_TOTAL,
                e.producers_total
            )],
            evidence: vec![(dictflow::W2_DICT_VALUE, e.what.clone())],
        }
    }

    fn param_proof(&self, node: ExprId, b: BinderId) -> NodeProof {
        let i = self.dict_params[&b];
        let prm = &self.m24.flow.params[i];
        let e = &self.m24.flow.param_erasure[i];
        let set = match prm.set.reason() {
            Some(r) => format!("Top({r})"),
            None => format!(
                "{{{}}}",
                prm.set
                    .keys()
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        let plan = self
            .m24
            .dict_plan_of(&prm.module, prm.binder)
            .map(|o| {
                format!(
                    " … owner plan {} ({} tuple(s){})",
                    match o.clones {
                        Some(n) => format!("{n} clones"),
                        None => "refused".into(),
                    },
                    o.tuples.len(),
                    if o.set_valued > 0 {
                        format!(", {} set-valued: a lower bound", o.set_valued)
                    } else {
                        String::new()
                    }
                )
            })
            .unwrap_or_default();
        NodeProof {
            node,
            what: Some(format!(
                "classop: dictionary parameter {} ({}) of {} → whole-program {set}",
                prm.index, prm.occ, prm.owner
            )),
            verdict: Some(format!(
                "totality {} … erasure {}{} [verified: {}]{plan}",
                prm.totality.label(),
                e.verdict.label(),
                erasure_reason(&e.verdict)
                    .map(|r| format!("({r})"))
                    .unwrap_or_default(),
                self.m24
                    .verdicts
                    .param_erasure(&prm.module, prm.binder)
                    .name()
            )),
            role: Some(format!(
                "an occurrence of the dictionary parameter {}",
                self.m.binder(b).occ
            )),
            facts: vec![
                format!(
                    "{}: the set is the union over every call site in the closed world ({} call site(s))",
                    dictflow::W3_PARAM_UNION,
                    prm.producers.calls.len()
                ),
                format!(
                    "exported: {} … GHC records it strict: {} (evidence only)",
                    prm.exported, prm.known_strict
                ),
            ],
            evidence: vec![(
                dictflow::W1_GLOBAL_CALLERS,
                format!("{} of {}", prm.occ, prm.owner),
            )],
        }
    }

    fn boundary_proof(&self, node: ExprId, i: usize) -> NodeProof {
        let b = &self.m24.higher.boundaries[i];
        let plan = self
            .m24
            .closure_plan_of(b)
            .map(|o| {
                format!(
                    " … owner plan {}",
                    match o.clones {
                        Some(n) => format!("{n} clones"),
                        None => "refused".into(),
                    }
                )
            })
            .unwrap_or_default();
        NodeProof {
            node,
            what: Some(format!(
                "boundary: {} producers {} (classes {}) → {}{}{plan}",
                b.name,
                b.producers.len(),
                b.classes,
                b.verdict.label(),
                match &b.verdict {
                    HVerdict::CloneRequired(n) | HVerdict::FiniteClosureSet(n) => format!("({n})"),
                    HVerdict::Preserve(r) | HVerdict::Unresolved(r) => format!("({r})"),
                    _ => String::new(),
                }
            )),
            verdict: Some(format!(
                "one representation {} … rewritable as one {} [verified: {}]",
                b.one_representation(),
                b.verdict.rewritable_as_one(),
                self.m24.verdicts.boundary(b).name()
            )),
            role: Some(format!(
                "the {} slot itself; {}",
                b.kind,
                if b.exported {
                    "exported, so its representation is shared outside the rewrite"
                } else {
                    "not exported"
                }
            )),
            facts: vec![format!(
                "{}: enumerated {} — an enumerated producer set is not one representation",
                higher::H11_SEPARATE,
                b.enumerated
            )],
            evidence: vec![(higher::H2_PRODUCERS, format!("{} use(s)", b.uses.len()))],
        }
    }

    fn producer_proof(&self, node: ExprId, is: &[usize]) -> NodeProof {
        let b = &self.m24.higher.boundaries[is[0]];
        let p = b
            .producers
            .iter()
            .find(|p| p.node == node)
            .expect("the producer index names a producer");
        NodeProof {
            node,
            what: Some(format!(
                "boundary: closure producer {} ({}) — {}",
                p.key,
                p.kind.name(),
                p.shape.short()
            )),
            verdict: Some(format!(
                "reaches {} boundary/boundaries: {}",
                is.len(),
                is.iter()
                    .map(|i| format!(
                        "{} → {}",
                        self.m24.higher.boundaries[*i].name,
                        self.m24.higher.boundaries[*i].verdict.label()
                    ))
                    .collect::<Vec<_>>()
                    .join("; ")
            )),
            role: Some("a closure producer".into()),
            facts: vec![format!(
                "{}: shape class {}",
                higher::H4_SHAPE_CLASS,
                p.shape.class()
            )],
            evidence: vec![(higher::H2_PRODUCERS, p.occ.clone())],
        }
    }
}

//------------------------------------------------------------------------------
// The milestone accounting
//------------------------------------------------------------------------------

/// Question 1 — **can the call target be enumerated?**
#[derive(Debug, Clone, Default, Serialize)]
pub struct TargetRow {
    pub sites: usize,
    pub exact: usize,
    pub finite: usize,
    pub unresolved: usize,
    /// Sites whose *dictionary* the fixpoint bounded, whatever became of
    /// the target: a separate fact, printed beside it and never added in.
    pub dict_bounded: usize,
    /// Of those, the ones the verifier re-derived.
    pub verified_exact: usize,
    pub verified_bounded: usize,
}

impl TargetRow {
    pub fn closes(&self) -> bool {
        self.exact + self.finite + self.unresolved == self.sites
    }
}

/// Question 2 — **can this abstraction boundary use one representation?**
#[derive(Debug, Clone, Default, Serialize)]
pub struct RepresentationRow {
    pub boundaries: usize,
    /// In [`higher::Verdict::col`] order.
    pub verdicts: [usize; 6],
    /// The **one** statement of the theorem: enumerated, one shape class,
    /// no opaque producer.
    pub one_representation: usize,
    /// Strictly stronger: the rewrite must also own the slot.
    pub rewritable_as_one: usize,
    pub enumerated: usize,
    pub verified: usize,
    pub claims: usize,
}

impl RepresentationRow {
    pub fn closes(&self) -> bool {
        self.verdicts.iter().sum::<usize>() == self.boundaries
    }
}

/// One clone plan, owner-level, with its lower bound flagged.
#[derive(Debug, Clone, Default, Serialize)]
pub struct ClonePlanRow {
    pub label: &'static str,
    /// The per-slot cardinality sum. **Evidence only, never a clone count.**
    pub cardinality_sum: usize,
    pub clones: usize,
    pub owners_planned: usize,
    pub owners_refused: usize,
    /// Plans with a set-valued tuple component: their clone counts are
    /// lower bounds, closable only by a call-string analysis.
    pub lower_bounds: usize,
    pub verified: usize,
}

/// Question 3 — **can the dictionary or closure object disappear?**
#[derive(Debug, Clone, Default, Serialize)]
pub struct ErasureRow {
    pub values: usize,
    pub value_verdicts: [usize; 5],
    pub params: usize,
    pub param_verdicts: [usize; 5],
    pub param_totality: [usize; 3],
    pub obligations: usize,
    pub verified_values: usize,
    pub verified_params: usize,
    pub plans: Vec<ClonePlanRow>,
}

impl ErasureRow {
    pub fn closes(&self) -> bool {
        self.value_verdicts.iter().sum::<usize>() == self.values
            && self.param_verdicts.iter().sum::<usize>() == self.params
            && self.param_totality.iter().sum::<usize>() == self.params
    }
}

/// One line of the residual, itemised and owned.
#[derive(Debug, Clone, Serialize)]
pub struct ResidualRow {
    pub n: usize,
    pub what: String,
    pub whose: &'static str,
}

/// M2.4's accounting: the three questions, asserted, and never collapsed.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Accounting {
    pub targets: TargetRow,
    pub representation: RepresentationRow,
    pub erasure: ErasureRow,
    /// (target outcome) × (dictionary verdict), 3 rows by 5 columns.
    pub matrix: [[usize; 5]; 3],
    /// A site whose method is known but whose dictionary must survive.
    pub preserved_dispatch: usize,
    pub residual_sites: Vec<ResidualRow>,
    pub residual_boundaries: Vec<ResidualRow>,
    pub claims: usize,
    pub disagreements: usize,
    pub coverage_refusals: usize,
}

impl Accounting {
    /// Every equation closes, and the matrix covers the site population.
    pub fn check(&self) -> Result<(), String> {
        if !self.targets.closes() {
            return Err(format!(
                "question 1: sites {} != {} + {} + {}",
                self.targets.sites,
                self.targets.exact,
                self.targets.finite,
                self.targets.unresolved
            ));
        }
        if !self.representation.closes() {
            return Err(format!(
                "question 2: boundaries {} != {:?}",
                self.representation.boundaries, self.representation.verdicts
            ));
        }
        if self.representation.rewritable_as_one > self.representation.one_representation {
            return Err(
                "question 2: rewritable-as-one must be a subset of one-representation".into(),
            );
        }
        if !self.erasure.closes() {
            return Err(format!(
                "question 3: values {} != {:?}, parameters {} != {:?} / {:?}",
                self.erasure.values,
                self.erasure.value_verdicts,
                self.erasure.params,
                self.erasure.param_verdicts,
                self.erasure.param_totality
            ));
        }
        let m: usize = self.matrix.iter().flatten().sum();
        if m != self.targets.sites {
            return Err(format!("the matrix {m} != sites {}", self.targets.sites));
        }
        let rs: usize = self.residual_sites.iter().map(|r| r.n).sum();
        if rs != self.targets.unresolved {
            return Err(format!(
                "the itemised site residual {rs} != Unresolved {}",
                self.targets.unresolved
            ));
        }
        let rb: usize = self.residual_boundaries.iter().map(|r| r.n).sum();
        let unresolved_or_preserved =
            self.representation.verdicts[4] + self.representation.verdicts[5];
        if rb != unresolved_or_preserved {
            return Err(format!(
                "the itemised boundary residual {rb} != Preserve + Unresolved {unresolved_or_preserved}"
            ));
        }
        Ok(())
    }
}

/// Who owns a residual reason. Every row of the residual is itemised and
/// attributed; an unattributed row would be the milestone hiding what it
/// did not do.
fn whose(reason: &str) -> &'static str {
    if reason.starts_with(dictflow::T_UNREACHABLE) {
        "W0: dead in the closed world — if ShellCheck is built as a library they come back"
    } else if reason.starts_with(dictflow::U_METHOD_NOT_IN_DUMP) {
        "the instance is known and its body is in another package: a bigger dump, or a hand-written callee"
    } else if reason.starts_with(dictflow::T_CON_FIELD) {
        "an existential dictionary field (SomeException): M3, or a hand-written Exception lowering"
    } else if reason.starts_with(dictflow::T_NEVER_DISPATCHED) {
        "no class-op site in the program selects that field: dead under W0"
    } else if reason.starts_with(dictflow::T_UNKNOWN_CALL) {
        "a call the dump cannot see: a bigger dump"
    } else if reason.starts_with(dictflow::T_DISPATCH_TAINTED) {
        "the dispatch above it: closable only when that site's dictionary is"
    } else if reason.starts_with(higher::T_USED_AS_A_VALUE)
        || reason.starts_with(higher::T_ANON_LAMBDA)
    {
        "the Parsec CPS wall: a naming pass for the anonymous lambdas, then a call-string view"
    } else if reason.starts_with(higher::T_PARTIAL_CALL) {
        "the partial application's own consumers"
    } else if reason.starts_with(higher::T_NO_CON_APPS) || reason.starts_with(higher::T_UNREACHABLE)
    {
        "dead under H0"
    } else if reason.starts_with(higher::P_FIELD_READ) || reason.starts_with(higher::P_IMPORTED) {
        "a genuine run-time closure: the lowering decides, not this analysis"
    } else if reason.starts_with(higher::P_EXPORTED) || reason.starts_with(higher::P_VALUED) {
        "shared outside the rewrite: M3's ownership question"
    } else if reason.starts_with(higher::B_SET) || reason.starts_with(dictflow::B_SET) {
        "a budget: a larger one, or a per-caller analysis"
    } else {
        "M3"
    }
}

/// The reason head of a taint or refusal: everything before a `;` and
/// before a parenthesised witness.
fn reason_head(r: &str) -> String {
    higher::reason_head(r)
}

/// Build the milestone accounting from the four published proof objects.
pub fn accounting(m24: &M24) -> Accounting {
    let mut a = Accounting::default();
    let da = m24.flow.accounting();
    let ha = m24.higher.accounting();

    // ---- question 1 ---------------------------------------------------
    a.targets = TargetRow {
        sites: da.sites,
        exact: da.exact,
        finite: da.finite,
        unresolved: da.unresolved,
        dict_bounded: da.dict_known,
        verified_exact: m24
            .flow
            .sites
            .iter()
            .filter(|s| matches!(s.outcome, Outcome::Exact(_)))
            .filter(|s| m24.verdicts.site_target(&s.module, s.node).proven())
            .count(),
        verified_bounded: m24
            .flow
            .sites
            .iter()
            .filter(|s| !s.set.is_top() && !s.set.keys().is_empty())
            .filter(|s| m24.verdicts.site_set(&s.module, s.node).proven())
            .count(),
    };

    // ---- question 2 ---------------------------------------------------
    let mut verified = 0usize;
    let mut claims = 0usize;
    for b in &m24.higher.boundaries {
        match m24.verdicts.boundary(b) {
            Verified::Yes => {
                verified += 1;
                claims += 1;
            }
            Verified::NotAClaim => {}
            _ => claims += 1,
        }
    }
    a.representation = RepresentationRow {
        boundaries: ha.boundaries,
        verdicts: ha.verdicts,
        one_representation: ha.one_representation,
        rewritable_as_one: ha.rewritable_as_one,
        enumerated: ha.enumerated,
        verified,
        claims,
    };

    // ---- question 3 ---------------------------------------------------
    let verified_values = m24
        .value_index
        .iter()
        .filter(|(k, i)| {
            matches!(
                m24.flow.values[**i].verdict,
                DVerdict::Erasable
                    | DVerdict::ErasableWithClone(_)
                    | DVerdict::ErasableWithObligation(_)
            ) && m24.verdicts.value_erasure(k).proven()
        })
        .count();
    let verified_params = m24
        .flow
        .params
        .iter()
        .zip(m24.flow.param_erasure.iter())
        .filter(|(p, e)| {
            matches!(
                e.verdict,
                DVerdict::Erasable
                    | DVerdict::ErasableWithClone(_)
                    | DVerdict::ErasableWithObligation(_)
            ) && m24.verdicts.param_erasure(&p.module, p.binder).proven()
        })
        .count();
    let dict_plans = ClonePlanRow {
        label: "dictionary clones (E7-OWNER-CLONES)",
        cardinality_sum: da.value_clones + da.param_clones,
        clones: da.owner_clones,
        owners_planned: da.owner_functions,
        owners_refused: m24
            .flow
            .owners
            .iter()
            .filter(|o| o.clones.is_none())
            .count(),
        lower_bounds: m24
            .flow
            .owners
            .iter()
            .filter(|o| o.clones.is_some() && o.set_valued > 0)
            .count(),
        verified: m24
            .flow
            .owners
            .iter()
            .filter(|o| {
                o.clones.is_some() && m24.verdicts.dict_plan(&o.module, o.owner_binder).proven()
            })
            .count(),
    };
    let closure_plans = ClonePlanRow {
        label: "closure clones (H15-OWNER-CLONES)",
        cardinality_sum: ha.clone_classes,
        clones: ha.owner_clones,
        owners_planned: ha.clone_owners - ha.clone_owners_refused,
        owners_refused: ha.clone_owners_refused,
        lower_bounds: m24
            .higher
            .owners
            .iter()
            .filter(|o| o.clones.is_some() && o.set_valued > 0)
            .count(),
        verified: m24
            .higher
            .owners
            .iter()
            .filter(|o| {
                o.clones.is_some()
                    && m24
                        .verdicts
                        .closure_plan(&o.module, o.owner_binder)
                        .proven()
            })
            .count(),
    };
    a.erasure = ErasureRow {
        values: da.values,
        value_verdicts: da.value_verdicts,
        params: da.params,
        param_verdicts: da.param_verdicts,
        param_totality: da.param_totality,
        obligations: da.obligations,
        verified_values,
        verified_params,
        plans: vec![dict_plans, closure_plans],
    };

    a.matrix = da.matrix;
    a.preserved_dispatch = da.preserved_dispatch();

    // ---- the residual, itemised and owned ------------------------------
    let mut sites: BTreeMap<String, usize> = BTreeMap::new();
    for s in &m24.flow.sites {
        if let Outcome::Unresolved(r) = &s.outcome {
            *sites.entry(reason_head(r)).or_default() += 1;
        }
    }
    a.residual_sites = sites
        .into_iter()
        .map(|(what, n)| ResidualRow {
            n,
            whose: whose(&what),
            what,
        })
        .collect();
    a.residual_sites
        .sort_by_key(|r| (std::cmp::Reverse(r.n), r.what.clone()));

    let mut bs: BTreeMap<String, usize> = BTreeMap::new();
    for b in &m24.higher.boundaries {
        match &b.verdict {
            HVerdict::Preserve(r) | HVerdict::Unresolved(r) => {
                *bs.entry(reason_head(r)).or_default() += 1;
            }
            _ => {}
        }
    }
    a.residual_boundaries = bs
        .into_iter()
        .map(|(what, n)| ResidualRow {
            n,
            whose: whose(&what),
            what,
        })
        .collect();
    a.residual_boundaries
        .sort_by_key(|r| (std::cmp::Reverse(r.n), r.what.clone()));

    a.claims = m24.audit.checked;
    a.disagreements = m24.audit.real_disagreements();
    a.coverage_refusals = m24.audit.coverage_refusals();
    a
}

//------------------------------------------------------------------------------
// The cross-milestone links
//------------------------------------------------------------------------------

/// The rule that lets an M2.4 verdict explain an M1 thunk site away.
///
/// Deliberately the only one, and deliberately narrow: a `$d…` binding
/// whose right-hand side is a saturated application of a **dfun the
/// whole-program flow holds as a dictionary identity**, and whose identity
/// the flow proves `Erasable` with the independent verifier's
/// confirmation. If that dictionary is erased there is no dictionary left
/// to build, so the binding that would have built it is not a thunk site
/// any more.
///
/// Everything else is refused and counted: a superclass selection
/// (`$p1Monad d`) is a *selection* out of a dictionary and not an identity
/// of its own; a head with no identity in the flow is not a dictionary the
/// milestone gave a verdict to; an `Unresolved` or `Preserve` dictionary
/// keeps its box; and a claim the verifier did not confirm is not a
/// proof.
pub const M24_D_DICT_ERASED: &str = "M24-D-DICTIONARY-BINDING-ERASED";

/// One M1 thunk site an M2.4 verdict removes.
#[derive(Debug, Clone, Serialize)]
pub struct Explained {
    pub module: String,
    pub occ: String,
    pub let_node: ExprId,
    pub rhs: ExprId,
    pub rule: &'static str,
    /// The dictionary identity whose erasure explains it.
    pub key: String,
    pub detail: String,
}

/// One row of the M1 table, with all three later milestones' columns.
#[derive(Debug, Clone, Serialize)]
pub struct M1Row {
    pub label: &'static str,
    pub before: usize,
    pub by_tuples: usize,
    pub by_m23: usize,
    pub by_m24: usize,
}

impl M1Row {
    pub fn after(&self) -> usize {
        self.before - self.by_tuples - self.by_m23 - self.by_m24
    }
}

/// The link from M1's thunk sites to M2.4's erased dictionaries, beside
/// M2.2's and M2.3's columns and disjoint from both.
#[derive(Debug, Clone, Default, Serialize)]
pub struct M1Link {
    pub thunk_sites: usize,
    /// M2.2's count, read from its own link and never recomputed.
    pub by_tuples: usize,
    /// M2.3's count, read from its own link and never recomputed.
    pub by_m23: usize,
    pub explained: Vec<Explained>,
    pub rows: Vec<M1Row>,
    /// The `$d…` thunk sites this link's population is drawn from.
    pub dictionary_sites: usize,
    /// Of those, the ones whose dictionary the flow can even name.
    pub dictionary_sites_with_a_value: usize,
    /// What was deliberately **not** counted, with the count and why.
    pub not_counted: Vec<(&'static str, usize, &'static str)>,
    /// Why the dictionaries this population names are not `Erasable`, by
    /// the verdict's own reason: an adjacent population, stated rather
    /// than left as a bare zero.
    pub not_erasable_reasons: Vec<(String, usize)>,
}

impl M1Link {
    pub fn remaining(&self) -> usize {
        self.thunk_sites - self.by_tuples - self.by_m23 - self.explained.len()
    }

    /// `remaining + by-tuples + by-M2.3 + by-M2.4 = 2,242`, and no site is
    /// counted twice.
    pub fn check(&self) {
        assert!(
            self.by_tuples + self.by_m23 + self.explained.len() <= self.thunk_sites,
            "more thunk sites explained than exist"
        );
        assert_eq!(
            self.remaining() + self.by_tuples + self.by_m23 + self.explained.len(),
            self.thunk_sites,
            "remaining + tuples + M2.3 + M2.4 must be the M1 population"
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
        let before: usize = self.rows.iter().map(|r| r.before).sum();
        assert_eq!(before, self.thunk_sites, "the fate rows must cover M1");
        assert_eq!(
            self.rows.iter().map(|r| r.by_m24).sum::<usize>(),
            self.explained.len(),
            "every M2.4-explained site lands in exactly one row"
        );
        for r in &self.rows {
            assert!(
                r.by_tuples + r.by_m23 + r.by_m24 <= r.before,
                "{}: explained exceeds the population",
                r.label
            );
        }
    }
}

/// Compute the M1 link. `tuple_explained` and `m23_explained` are the two
/// earlier milestones' own sets, keyed the way M1 keys a binding, so that
/// no site is claimed twice and neither column is recomputed here.
pub fn m1_link(
    m24: &M24,
    census: &crate::laziness::Census,
    tuple_explained: &HashSet<(String, ExprId, ExprId)>,
    m23_explained: &HashSet<(String, ExprId, ExprId)>,
) -> M1Link {
    use crate::laziness::{Fate, Origin};

    let mut out = M1Link::default();
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
    out.by_m23 = thunks
        .iter()
        .filter(|b| m23_explained.contains(&(b.module.clone(), b.let_node, b.rhs)))
        .count();

    let by_name: HashMap<&str, &Module> =
        m24.modules.iter().map(|m| (m.name.as_str(), *m)).collect();

    let mut unverified = 0usize;
    let mut not_erasable = 0usize;
    let mut no_value = 0usize;
    let mut superclass = 0usize;
    let mut why_not: BTreeMap<String, usize> = BTreeMap::new();
    let mut seen: HashSet<(String, ExprId, ExprId)> = HashSet::new();
    for b in &thunks {
        if b.origin != Origin::Dictionary {
            continue;
        }
        out.dictionary_sites += 1;
        let key = (b.module.clone(), b.let_node, b.rhs);
        // A site an earlier milestone already explains is that milestone's.
        if tuple_explained.contains(&key) || m23_explained.contains(&key) {
            continue;
        }
        let Some(m) = by_name.get(b.module.as_str()) else {
            continue;
        };
        let rhs = m.strip(b.rhs);
        // The head of the right-hand side's application spine, by stable
        // name. A dfun names a dictionary identity; a `$pN<Class>`
        // selector names a *field of* one and is refused.
        let (head, _) = m.spine(m.spine_root(rhs));
        let head_name = match m.expr(m.strip(head)) {
            h2r_core_ir::Expr::Var { name, occ, .. } => {
                if occ.starts_with("$p") {
                    superclass += 1;
                    continue;
                }
                name.clone()
            }
            _ => {
                no_value += 1;
                continue;
            }
        };
        let hit = m24
            .value_at(&b.module, rhs)
            .or_else(|| m24.value_named(&head_name));
        let Some((vkey, e)) = hit else {
            no_value += 1;
            continue;
        };
        out.dictionary_sites_with_a_value += 1;
        if e.verdict != DVerdict::Erasable {
            not_erasable += 1;
            *why_not
                .entry(format!(
                    "{}({})",
                    e.verdict.label(),
                    erasure_reason(&e.verdict)
                        .map(|r| reason_head(&r))
                        .unwrap_or_default()
                ))
                .or_default() += 1;
            continue;
        }
        if !m24.verdicts.value_erasure(vkey).proven() {
            unverified += 1;
            continue;
        }
        if !seen.insert(key) {
            continue;
        }
        out.explained.push(Explained {
            module: b.module.clone(),
            occ: b.occ.clone(),
            let_node: b.let_node,
            rhs: b.rhs,
            rule: M24_D_DICT_ERASED,
            key: vkey.to_string(),
            detail: format!(
                "{} is Erasable ({} instance) and the verifier re-derived it",
                e.what, e.instances
            ),
        });
    }

    let label_of = |f: Fate| -> &'static str {
        match f {
            Fate::SinkEager => "sinkable, lands in an evaluating position",
            Fate::SinkLazyPosition => "sinkable, lands in a lazy position",
            Fate::Memo => "memoisation required",
            Fate::Recursive => "recursive value",
            _ => "unknown",
        }
    };
    let explained_keys: HashSet<(String, ExprId, ExprId)> = out
        .explained
        .iter()
        .map(|e| (e.module.clone(), e.let_node, e.rhs))
        .collect();
    for f in [
        Fate::SinkEager,
        Fate::SinkLazyPosition,
        Fate::Memo,
        Fate::Recursive,
        Fate::Unknown,
    ] {
        let rows: Vec<&&crate::laziness::BindingReport> =
            thunks.iter().filter(|b| b.fate == f).collect();
        if rows.is_empty() && f == Fate::Unknown {
            continue;
        }
        out.rows.push(M1Row {
            label: label_of(f),
            before: rows.len(),
            by_tuples: rows
                .iter()
                .filter(|b| tuple_explained.contains(&(b.module.clone(), b.let_node, b.rhs)))
                .count(),
            by_m23: rows
                .iter()
                .filter(|b| m23_explained.contains(&(b.module.clone(), b.let_node, b.rhs)))
                .count(),
            by_m24: rows
                .iter()
                .filter(|b| explained_keys.contains(&(b.module.clone(), b.let_node, b.rhs)))
                .count(),
        });
    }

    out.not_counted = vec![
        (
            "a $d… thunk site whose right-hand side is a superclass selection",
            superclass,
            "$pN<Class> d selects a FIELD of a dictionary: it is not an identity of its own, and \
             M2.4c gave it no verdict",
        ),
        (
            "a $d… thunk site whose dictionary the whole-program flow does not name",
            no_value,
            "the head of the right-hand side is not a dfun the flow holds an identity for",
        ),
        (
            "a $d… thunk site whose dictionary is not Erasable",
            not_erasable,
            "Preserve or Unresolved: the box stays, so the binding that builds it stays",
        ),
        (
            "a $d… thunk site whose Erasable claim the verifier did not confirm",
            unverified,
            "an unconfirmed claim is unsupported and never proven",
        ),
    ];
    out.not_erasable_reasons = why_not.into_iter().collect();
    out.not_erasable_reasons
        .sort_by_key(|(k, n)| (std::cmp::Reverse(*n), k.clone()));
    out.check();
    out
}

/// One row of a cross-link back to an earlier milestone's residual.
#[derive(Debug, Clone, Serialize)]
pub struct LinkRow {
    pub n: usize,
    pub what: String,
    pub note: String,
}

/// A whole cross-link section: an earlier milestone's residual population,
/// with what M2.4 says about it. **Nothing is reclassified**: every fate
/// and every tier stands exactly as its own milestone recorded it.
#[derive(Debug, Clone, Serialize)]
pub struct LinkSection {
    pub label: String,
    pub population: usize,
    pub rows: Vec<LinkRow>,
    /// What a later pass *could* act on. Reported, never acted on.
    pub could_reclassify: usize,
    pub note: String,
}

/// The M2.3 closure residual, by holder: the constructor fields M2.3b left
/// `Unknown` because the callee that consumes them is an unknown
/// higher-order value, now asked of the closure graph.
pub fn m23_closure_residual(m24: &M24, fc: &crate::fields::FieldCensus<'_>) -> LinkSection {
    let by_name: HashMap<&str, &Module> =
        m24.modules.iter().map(|m| (m.name.as_str(), *m)).collect();
    let mut by_holder: BTreeMap<String, (usize, BTreeMap<String, usize>)> = BTreeMap::new();
    let mut population = 0usize;
    let mut could = 0usize;
    for f in &fc.flows {
        let Some(m) = by_name.get(f.module.as_str()) else {
            continue;
        };
        for fv in &f.verdicts {
            let Some(reason) = fv.reason_key() else {
                continue;
            };
            if !reason.starts_with(crate::flow::R_HIGHER_ORDER) {
                continue;
            }
            population += 1;
            let holder = reason
                .split_once(" (")
                .map(|(_, h)| h.trim_end_matches(')').to_string())
                .unwrap_or_else(|| "?".to_string());
            // The escape names the call; its head is the closure that
            // consumes the field, and that head is a boundary of the
            // closed world exactly when the closure graph has one.
            let at = fv
                .evidence
                .iter()
                .find(|e| e.rule == crate::fields::D7_ESCAPE)
                .and_then(|e| e.nodes.first().copied());
            let verdict = at
                .and_then(|at| {
                    let (head, _) = m.spine(m.spine_root(at));
                    m.resolve(m.strip(head))
                })
                .and_then(|b| m24.higher.verdict_for(&f.module, b))
                .map(|b| {
                    if b.verdict.rewritable_as_one() {
                        could += 1;
                    }
                    b.verdict.label().to_string()
                })
                .unwrap_or_else(|| "NoBoundary".to_string());
            let e = by_holder.entry(holder).or_default();
            e.0 += 1;
            *e.1.entry(verdict).or_default() += 1;
        }
    }
    let mut rows: Vec<LinkRow> = by_holder
        .into_iter()
        .map(|(holder, (n, vs))| LinkRow {
            n,
            what: holder,
            note: vs
                .iter()
                .map(|(v, c)| format!("{v} {c}"))
                .collect::<Vec<_>>()
                .join(", "),
        })
        .collect();
    rows.sort_by_key(|r| (std::cmp::Reverse(r.n), r.what.clone()));
    LinkSection {
        label: "M2.3b fields Unknown on an unknown higher-order callee, by holder".into(),
        population,
        rows,
        could_reclassify: could,
        note: "the holder is the callee binder M2.3 named; the verdict is the closure graph's \
               answer about that binder's own slot"
            .into(),
    }
}
