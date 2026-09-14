//! The representation **view**: what each M2.3 verdict rests on, per site.
//!
//! [`crate::scalar`] is the model. M2.2's scalar view says what replaces a
//! tuple; it rewrites nothing, it only lays the proof out so that a person
//! can audit one construction without reading the census' whole report.
//! This module does the same for the three M2.3 censuses, with one
//! difference that is the whole point of the milestone: M2.3 **decides
//! nothing to rewrite**. A field rep is a statement about when a field is
//! evaluated, and a list or text advisory is a named conjunction of facts.
//! So the view is not "what the program looks like after" — it is *the
//! facts, the observations that establish them, and the route from the
//! facts to the verdict*, each line carrying its rule id and its nodes.
//!
//! Three views, one per census:
//!
//! * [`FieldView`] — one line per field: the three facts, the derived rep,
//!   and the route that proved it; then the observations that justify the
//!   facts, with node ids; and for `Unknown`, the escape with its refined
//!   reason. **Every field appears exactly once** ([`FieldView::check`]).
//! * [`ListView`] — the producer, every cell, every consumer with its rule
//!   id and the demand *that consumer* contributes, the six facts, and the
//!   advisory with the fact combination that produced it. **Every consumer
//!   appears exactly once** ([`ListView::check`]).
//! * [`TextView`] — the text facts on top of the list view: the selection
//!   evidence, the shape, the consumer classes, the char-semantics
//!   reasons, the append chain, and the advisory.
//!
//! Nothing here re-derives a verdict; every line reads the census' own
//! proof object. Where a verdict is one the [independent
//! verifier](crate::verify_rep) re-derives, the view says whether it did
//! ([`Verified`]) — a claim the verifier refused for coverage is reported
//! as refused, never as proven.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use h2r_core_ir::{BinderId, Expr, ExprId, Module};
use serde::Serialize;

use crate::fields::{
    ConStrictness, D7_ESCAPE, FieldDemand, FieldFlow, FieldRep, FieldVerdict, ObsKind, Observation,
};
use crate::laziness::Census;
use crate::lists::{
    ConsumerKind, ListConsumer, ListFlow, ProducerKind, Recommendation, TailFate, consumer_name,
};
use crate::text::{Advisory, TextFlow};
use crate::verify_rep::{Claim, ClaimKind, RepCrossCheck, is_coverage_refusal};

//------------------------------------------------------------------------------
// Verification status
//------------------------------------------------------------------------------

/// What the [independent verifier](crate::verify_rep) had to say about one
/// verdict. A claim it refused for coverage is **never** reported as
/// proven: that is the direction the acceptance rule points.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Verified {
    /// Re-derived by the second walk.
    Yes,
    /// The second walk declined to re-derive it, with its reason. A
    /// coverage loss, not a claim about the census.
    CoverageRefused(&'static str),
    /// The second walk refutes it. On `-O1` this set is empty.
    Disagreed(&'static str),
    /// Not one of the verdicts whose being wrong would be a miscompile, so
    /// nothing re-derives it.
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

    /// Does this verdict carry a proof from both sides?
    pub fn proven(&self) -> bool {
        *self == Verified::Yes
    }
}

/// Every claim the verifier was handed, and what came back, keyed by the
/// census' own site. Built once from a [`RepCrossCheck`] and the claim list
/// that produced it.
#[derive(Debug, Clone, Default)]
pub struct Verdicts {
    claimed: HashSet<(String, ClaimKind, ExprId, u32)>,
    refused: HashMap<(String, ClaimKind, ExprId, u32), &'static str>,
}

impl Verdicts {
    pub fn of(claims: &[Claim], cc: &RepCrossCheck) -> Verdicts {
        let mut v = Verdicts::default();
        for c in claims {
            v.claimed.insert((c.module.clone(), c.kind, c.at, c.field));
        }
        for d in &cc.disagreements {
            v.refused.insert(
                (
                    d.claim.module.clone(),
                    d.claim.kind,
                    d.claim.at,
                    d.claim.field,
                ),
                d.refusal.why,
            );
        }
        v
    }

    pub fn status(&self, module: &str, kind: ClaimKind, at: ExprId, field: u32) -> Verified {
        let key = (module.to_string(), kind, at, field);
        if !self.claimed.contains(&key) {
            return Verified::NotAClaim;
        }
        match self.refused.get(&key) {
            Some(why) if is_coverage_refusal(why) => Verified::CoverageRefused(why),
            Some(why) => Verified::Disagreed(why),
            None => Verified::Yes,
        }
    }

    /// The status of a field verdict, choosing the claim kind from the rep.
    pub fn field(&self, module: &str, at: ExprId, v: &FieldVerdict) -> Verified {
        let kind = match v.rep {
            FieldRep::Direct => ClaimKind::FieldDirect,
            FieldRep::Dead => ClaimKind::FieldDead,
            FieldRep::Recursive => ClaimKind::FieldRecursive,
            _ => return Verified::NotAClaim,
        };
        self.status(module, kind, at, v.index)
    }

    /// The status of a list flow's advisory.
    pub fn list(&self, f: &ListFlow) -> Verified {
        let kind = match f.rec {
            Recommendation::VecCandidate => ClaimKind::ListVec,
            Recommendation::IteratorCandidate => ClaimKind::ListIterator,
            _ => return Verified::NotAClaim,
        };
        self.status(&f.module, kind, f.producer, 0)
    }

    /// The status of a text flow's advisory.
    pub fn text(&self, f: &TextFlow) -> Verified {
        if f.advisory != Advisory::StrongStringCandidate {
            return Verified::NotAClaim;
        }
        self.status(&f.module, ClaimKind::TextStrong, f.producer, 0)
    }
}

/// Collect every claim the three censuses publish, in exactly the shape
/// `h2r verify-rep` hands to the verifier. Shared so that the views, the
/// accounting and the cross-milestone link all see the same claim set as
/// the verifier does, rather than each rebuilding it.
pub fn claims_of(
    fc: &crate::fields::FieldCensus<'_>,
    lc: &crate::lists::ListCensus<'_>,
    tc: &crate::text::TextCensus,
) -> Vec<Claim> {
    let mut claims = Vec::new();
    for f in &fc.flows {
        for v in &f.verdicts {
            let kind = match v.rep {
                FieldRep::Direct => ClaimKind::FieldDirect,
                FieldRep::Dead => ClaimKind::FieldDead,
                FieldRep::Recursive => ClaimKind::FieldRecursive,
                _ => continue,
            };
            claims.push(Claim {
                module: f.module.clone(),
                kind,
                at: f.construction,
                field: v.index,
                rule: v.rule,
            });
        }
    }
    for f in &lc.flows {
        let kind = match f.rec {
            Recommendation::VecCandidate => ClaimKind::ListVec,
            Recommendation::IteratorCandidate => ClaimKind::ListIterator,
            _ => {
                if f.recursion == crate::lists::Recursion::RecursiveKnot {
                    ClaimKind::ListKnot
                } else {
                    continue;
                }
            }
        };
        claims.push(Claim {
            module: f.module.clone(),
            kind,
            at: f.producer,
            field: 0,
            rule: f.rec_rule,
        });
        if f.recursion == crate::lists::Recursion::RecursiveKnot && kind != ClaimKind::ListKnot {
            claims.push(Claim {
                module: f.module.clone(),
                kind: ClaimKind::ListKnot,
                at: f.producer,
                field: 0,
                rule: f.rec_rule,
            });
        }
    }
    for f in &tc.flows {
        if f.advisory != Advisory::StrongStringCandidate {
            continue;
        }
        claims.push(Claim {
            module: f.module.clone(),
            kind: ClaimKind::TextStrong,
            at: f.producer,
            field: 0,
            rule: f.advisory_rule,
        });
    }
    claims
}

/// Run the verifier over every claim, module by module, and return both the
/// cross-check and the per-site index. The one place the three views, the
/// accounting and the link get their verification status from.
pub fn verify_all(
    modules: &[&Module],
    census: &Census,
    fc: &crate::fields::FieldCensus<'_>,
    lc: &crate::lists::ListCensus<'_>,
    tc: &crate::text::TextCensus,
) -> (RepCrossCheck, Verdicts) {
    let claims = claims_of(fc, lc, tc);
    let mut by_module: BTreeMap<&str, Vec<Claim>> = BTreeMap::new();
    for c in &claims {
        by_module
            .entry(c.module.as_str())
            .or_default()
            .push(c.clone());
    }
    let mut cc = RepCrossCheck::default();
    for m in modules {
        if let Some(cs) = by_module.get(m.name.as_str()) {
            crate::verify_rep::cross_check(m, census, cs, &mut cc);
        }
    }
    let v = Verdicts::of(&claims, &cc);
    (cc, v)
}

//------------------------------------------------------------------------------
// The field view
//------------------------------------------------------------------------------

/// One field of one construction, as the view prints it.
#[derive(Debug, Clone, Serialize)]
pub struct FieldLine {
    pub index: u32,
    pub demand: FieldDemand,
    pub strictness: ConStrictness,
    pub recursion: crate::fields::ValueRecursion,
    pub rep: FieldRep,
    /// The rule the derivation reached, and the whole route set behind it.
    pub rule: &'static str,
    pub routes: Vec<&'static str>,
    pub route_key: String,
    pub reason: Option<String>,
    pub verified: Verified,
    /// The field expression's node, so `h2r show` can be pointed at it.
    pub expr: ExprId,
    /// GHC makes the field strict but nothing demands it: forced at WHNF,
    /// which is why it is not `Dead`.
    pub force_on_whnf: bool,
    /// The observations that justify the demand fact, with their nodes.
    pub observations: Vec<String>,
    /// For `Unknown`: the escape and its refined reason.
    pub escape: Option<String>,
    /// The verdict's own evidence, rule and note.
    pub evidence: Vec<(&'static str, String)>,
    /// One line, in the shape the report prints it.
    pub headline: String,
}

/// One construction, field by field.
#[derive(Debug, Clone, Serialize)]
pub struct FieldView {
    pub module: String,
    pub construction: ExprId,
    pub con: String,
    pub occ: String,
    pub program: bool,
    pub arity: u32,
    pub observed: bool,
    pub escaped: bool,
    pub returned: bool,
    pub locations: usize,
    pub lines: Vec<FieldLine>,
}

impl FieldView {
    pub fn of(m: &Module, f: &FieldFlow, v: &Verdicts) -> FieldView {
        let mut lines = Vec::new();
        for fv in &f.verdicts {
            let idx = fv.index;
            let mut observations: Vec<String> = Vec::new();
            for o in &f.observations {
                if let Some(s) = describe_observation(m, o, idx) {
                    observations.push(s);
                }
            }
            let escape = (fv.rep == FieldRep::Unknown)
                .then(|| {
                    fv.evidence
                        .iter()
                        .find(|e| e.rule == D7_ESCAPE)
                        .map(|e| {
                            format!(
                                "{}: {} at node {}",
                                D7_ESCAPE,
                                fv.reason_key().unwrap_or_else(|| e.note.clone()),
                                e.nodes.first().copied().unwrap_or(f.construction)
                            )
                        })
                        .or_else(|| {
                            fv.reason_key()
                                .map(|r| format!("{D7_ESCAPE}: {r} at node {}", f.construction))
                        })
                })
                .flatten();
            let verified = v.field(&f.module, f.construction, fv);
            let route = if fv.routes.is_empty() {
                fv.rule.to_string()
            } else {
                format!("{}: {}", fv.route_key(), fv.rule)
            };
            let tail = match (&fv.reason_key(), fv.rep) {
                (Some(r), _) => format!("[{}: {r}]", fv.rule),
                (None, FieldRep::Direct) => format!("[{route}]"),
                (None, _) => format!("[{}]", fv.rule),
            };
            let headline = format!(
                "f{idx}  demand={:?}  strict={:?}  rec={:?}  ⇒ {}  {tail}",
                fv.demand,
                fv.strictness,
                fv.recursion,
                fv.rep.name()
            );
            lines.push(FieldLine {
                index: idx,
                demand: fv.demand,
                strictness: fv.strictness,
                recursion: fv.recursion,
                rep: fv.rep,
                rule: fv.rule,
                routes: fv.routes.clone(),
                route_key: fv.route_key(),
                reason: fv.reason_key(),
                verified,
                expr: f.fields[idx as usize],
                force_on_whnf: fv.force_on_whnf,
                observations,
                escape,
                evidence: fv
                    .evidence
                    .iter()
                    .map(|e| (e.rule, evidence_note(m, e)))
                    .collect(),
                headline,
            });
        }
        let view = FieldView {
            module: f.module.clone(),
            construction: f.construction,
            con: f.con.clone(),
            occ: f.occ.clone(),
            program: f.program,
            arity: f.arity,
            observed: f.observed(),
            escaped: f.escaped(),
            returned: f.returned,
            locations: f.locations,
            lines,
        };
        view.check();
        view
    }

    /// Every field of the construction appears exactly once, and no field
    /// outside its arity appears at all.
    pub fn check(&self) {
        assert_eq!(
            self.lines.len(),
            self.arity as usize,
            "the field view of {} node {} must have one line per field",
            self.module,
            self.construction
        );
        let seen: BTreeSet<u32> = self.lines.iter().map(|l| l.index).collect();
        assert_eq!(
            seen.len(),
            self.lines.len(),
            "every field must appear exactly once in the view"
        );
        assert!(
            seen.iter().all(|i| *i < self.arity),
            "no line may name a field outside the construction's arity"
        );
    }

    pub fn header(&self) -> String {
        format!(
            "{} node {} — {} ({}), arity {}, {}{}{}",
            self.module,
            self.construction,
            self.occ,
            if self.program { "program" } else { "library" },
            self.arity,
            if self.observed {
                "observed"
            } else if self.escaped {
                "escaped before any observation"
            } else {
                "never observed"
            },
            if self.returned { ", returned" } else { "" },
            if self.escaped && self.observed {
                ", and escapes"
            } else {
                ""
            },
        )
    }
}

fn describe_observation(m: &Module, o: &Observation, idx: u32) -> Option<String> {
    let b = |b: Option<BinderId>| match b {
        Some(b) => format!(" [{}#{b}]", m.binder(b).occ),
        None => String::new(),
    };
    match o.kind {
        ObsKind::FieldDemanded if o.field == Some(idx) => Some(format!(
            "{}: field {idx} bound and used at node {}{} — {}",
            o.how.map(|h| h.rule()).unwrap_or(o.rule),
            o.at,
            b(o.binder),
            o.detail
        )),
        ObsKind::FieldBoundUnused if o.field == Some(idx) => Some(format!(
            "{}: field {idx} bound and unused at node {}{}",
            o.rule,
            o.at,
            b(o.binder)
        )),
        ObsKind::WhnfOnly => Some(format!(
            "{}: observed at WHNF at node {}, no field read ({})",
            o.rule,
            o.at,
            o.whnf
                .map(|w| format!("{w:?}"))
                .unwrap_or_else(|| o.detail.clone())
        )),
        ObsKind::Escape => Some(format!(
            "{}: {} at node {}",
            o.rule,
            o.why.unwrap_or("escape"),
            o.at
        )),
        _ => None,
    }
}

fn evidence_note(m: &Module, e: &crate::flow::Evidence) -> String {
    let nodes = e
        .nodes
        .iter()
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let b = match e.binder {
        Some(b) => format!(" [{}#{b}]", m.binder(b).occ),
        None => String::new(),
    };
    format!("{} (node(s) {nodes}){b}", e.note)
}

//------------------------------------------------------------------------------
// The list view
//------------------------------------------------------------------------------

/// One consumer of a list flow, as the view prints it: what it is, where,
/// the rule that classified it, and the demand **it** contributes.
#[derive(Debug, Clone, Serialize)]
pub struct ConsumerLine {
    pub at: ExprId,
    pub kind: &'static str,
    pub rule: &'static str,
    pub spine: &'static str,
    pub head: &'static str,
    pub streaming: bool,
    pub short_circuits: bool,
    pub aliases: bool,
    pub tail_derived: bool,
    pub what: String,
    pub headline: String,
}

/// One list flow: its producer, its cells, its consumers, the six facts and
/// the advisory.
#[derive(Debug, Clone, Serialize)]
pub struct ListView {
    pub module: String,
    pub producer: ExprId,
    pub kind: ProducerKind,
    pub producer_name: String,
    pub cells: Vec<ExprId>,
    pub nil_terminated: bool,
    pub bound: Option<String>,
    pub list_ty: Option<String>,
    pub elem_ty: Option<String>,
    pub consumers: Vec<ConsumerLine>,
    /// The six facts, each with the rule that decided it.
    pub facts: Vec<(&'static str, String, &'static str)>,
    pub traversals: usize,
    pub streaming: bool,
    pub advisory: Recommendation,
    pub advisory_rule: &'static str,
    pub advisory_reason: Option<String>,
    /// The fact combination the advisory was derived from, as one line.
    pub advisory_from: String,
    pub verified: Verified,
    pub successors: Vec<ExprId>,
    pub escapes: Vec<String>,
    pub locations: usize,
}

impl ListView {
    pub fn of(m: &Module, f: &ListFlow, v: &Verdicts) -> ListView {
        let consumers: Vec<ConsumerLine> = f
            .consumers
            .iter()
            .map(|c| consumer_line(m, c))
            .collect::<Vec<_>>();
        let facts = vec![
            ("SpineDemand", f.spine.name().to_string(), f.spine_rule),
            ("HeadDemand", f.head.name().to_string(), head_rule(f)),
            ("Reuse", f.reuse.name().to_string(), reuse_rule(f)),
            ("Storage", f.storage.name().to_string(), storage_rule(f)),
            (
                "Recursion",
                format!("{:?}", f.recursion),
                match f.recursion {
                    crate::lists::Recursion::RecursiveKnot => crate::lists::L13_RECURSIVE_KNOT,
                    crate::lists::Recursion::FiniteProducer => NO_RULE_REC,
                },
            ),
            (
                "ShortCircuit",
                if f.short_circuit.no() {
                    "no".to_string()
                } else {
                    format!("yes ({} node(s))", f.short_circuit.yes.len())
                },
                if f.short_circuit.no() {
                    NO_RULE_SC
                } else {
                    crate::lists::L5_LOOP_SHORTCIRCUIT
                },
            ),
        ];
        let advisory_from = format!(
            "{} ∧ {} ∧ {} ∧ {} ∧ {} ∧ {}{}",
            f.spine.name(),
            f.head.name(),
            f.reuse.name(),
            f.storage.name(),
            format_args!("{:?}", f.recursion),
            if f.streaming {
                "streaming"
            } else {
                "not-streaming"
            },
            if f.short_circuit.no() {
                ""
            } else {
                " ∧ short-circuits"
            },
        );
        let view = ListView {
            module: f.module.clone(),
            producer: f.producer,
            kind: f.kind,
            producer_name: f.producer_name.clone(),
            cells: f.cells.clone(),
            nil_terminated: f.nil_terminated,
            bound: f.bound.map(|b| format!("{}#{b}", m.binder(b).occ)),
            list_ty: f.list_ty.clone(),
            elem_ty: f.elem_ty.clone(),
            consumers,
            facts,
            traversals: f.traversals,
            streaming: f.streaming,
            advisory: f.rec,
            advisory_rule: f.rec_rule,
            advisory_reason: f.rec_reason.clone(),
            advisory_from,
            verified: v.list(f),
            successors: f.successors.clone(),
            escapes: f
                .escapes
                .iter()
                .map(|(why, detail, at)| {
                    if detail.is_empty() {
                        format!("{why} at node {at}")
                    } else {
                        format!("{why} ({detail}) at node {at}")
                    }
                })
                .collect(),
            locations: f.locations,
        };
        view.check(f);
        view
    }

    /// Every consumer of the flow appears exactly once in the view.
    pub fn check(&self, f: &ListFlow) {
        assert_eq!(
            self.consumers.len(),
            f.consumers.len(),
            "the list view of {} node {} must have one line per consumer",
            self.module,
            self.producer
        );
        let seen: BTreeSet<(ExprId, &str, &str)> = self
            .consumers
            .iter()
            .map(|c| (c.at, c.kind, c.what.as_str()))
            .collect();
        assert_eq!(
            seen.len(),
            self.consumers.len(),
            "every consumer must appear exactly once in the view"
        );
    }

    pub fn header(&self) -> String {
        format!(
            "{} node {} — {} flow{}{}, {} consumer(s), advisory {}",
            self.module,
            self.producer,
            self.kind.name(),
            if self.cells.is_empty() {
                String::new()
            } else {
                format!(", {} cell(s)", self.cells.len())
            },
            if self.producer_name.is_empty() {
                String::new()
            } else {
                format!(" ({})", self.producer_name)
            },
            self.consumers.len(),
            self.advisory.name()
        )
    }
}

fn consumer_line(m: &Module, c: &ListConsumer) -> ConsumerLine {
    let what = match &c.kind {
        ConsumerKind::ConsAlt {
            head_bound,
            head_forced,
            tail,
        } => format!(
            "a (:) alternative: head {}{}, tail {}",
            if *head_bound { "bound" } else { "not bound" },
            if *head_forced { " and forced" } else { "" },
            match tail {
                TailFate::Dropped => "dropped".to_string(),
                TailFate::Loop { call } => format!("handed back to the loop at node {call}"),
                TailFate::LoopIncremental { call } =>
                    format!("handed back lazily to the loop at node {call}"),
                TailFate::LoopConditional { call } =>
                    format!("handed back under a case to the loop at node {call}"),
                TailFate::Followed => "followed".to_string(),
            }
        ),
        ConsumerKind::Whnf { how } => format!("observed at WHNF ({how})"),
        ConsumerKind::Axiom { name, rule } => format!("the imported {name} [{rule}]"),
        ConsumerKind::NoAxiom { name, in_table } => format!(
            "the imported {name} ({})",
            if *in_table {
                "an entry that does not cover this argument"
            } else {
                "no axiom"
            }
        ),
        ConsumerKind::StoredIn { con } => format!("stored in {con}"),
        ConsumerKind::ConsedAsTail { cell } => format!("consed on as the tail of the cell {cell}"),
        ConsumerKind::PassedLocal { callee } => format!("handed to the local {callee}"),
        ConsumerKind::Escape { why } => format!("escapes: {why}"),
    };
    let _ = m;
    let name = consumer_name(&c.kind);
    let headline = format!(
        "node {:<7} {:<14} [{}]  spine {} / head {}{}{}{}{}",
        c.at,
        name,
        c.rule,
        c.spine.name(),
        c.head.name(),
        if c.streaming { ", streaming" } else { "" },
        if c.short_circuits {
            ", short-circuits"
        } else {
            ""
        },
        if c.aliases { ", aliases" } else { "" },
        if c.tail_derived {
            ", reached through another consumer's tail"
        } else {
            ""
        },
    );
    ConsumerLine {
        at: c.at,
        kind: name,
        rule: c.rule,
        spine: c.spine.name(),
        head: c.head.name(),
        streaming: c.streaming,
        short_circuits: c.short_circuits,
        aliases: c.aliases,
        tail_derived: c.tail_derived,
        what,
        headline,
    }
}

/// The rule that decided each fact, for the view. Where a fact is the
/// *absence* of any rule firing — `SinglePass` is "no `L14` and no `L15`",
/// `NotStored` is "no `L10` and no `L16`" — the view says exactly that
/// rather than naming a rule that did not fire.
const NO_RULE_REUSE: &str = "no L14/L15 fired";
const NO_RULE_STORAGE: &str = "no L10/L16 fired";
const NO_RULE_HEAD: &str = "no (:) alternative bound a head";
const NO_RULE_SC: &str = "no short-circuiting consumer";
const NO_RULE_REC: &str = "M1 does not call it a recursive value";

fn head_rule(f: &ListFlow) -> &'static str {
    match f.head {
        crate::lists::HeadDemand::Unknown => crate::lists::L9_NO_AXIOM,
        crate::lists::HeadDemand::None => NO_RULE_HEAD,
        _ => crate::lists::L3_HEAD_BOUND,
    }
}

fn reuse_rule(f: &ListFlow) -> &'static str {
    match f.reuse {
        crate::lists::Reuse::SharedTail { .. } => crate::lists::L14_SHARED_TAIL,
        crate::lists::Reuse::MultiPass(_) => crate::lists::L15_MULTIPASS,
        crate::lists::Reuse::Escapes(_) => crate::lists::L11_ESCAPE,
        crate::lists::Reuse::SinglePass => NO_RULE_REUSE,
    }
}

fn storage_rule(f: &ListFlow) -> &'static str {
    match f.storage {
        crate::lists::Storage::StoredIn(_) => crate::lists::L10_STORED,
        crate::lists::Storage::Captured => crate::lists::L16_CAPTURED,
        crate::lists::Storage::Returned => crate::flow::T6_RETURNED,
        crate::lists::Storage::NotStored => NO_RULE_STORAGE,
    }
}

//------------------------------------------------------------------------------
// The text view
//------------------------------------------------------------------------------

/// A text flow: the list view, plus everything M2.3d records on top of it.
#[derive(Debug, Clone, Serialize)]
pub struct TextView {
    pub module: String,
    pub producer: ExprId,
    /// The list view this one sits on.
    pub list: ListView,
    pub element_type_evidence: crate::text::ElementTypeEvidence,
    /// The selection rules that fired, with their nodes.
    pub selection: Vec<(&'static str, String)>,
    pub shape: crate::text::TextShape,
    pub shape_rule: &'static str,
    pub literal: bool,
    pub append_chain: Option<crate::text::AppendChain>,
    pub append_operand: bool,
    /// Per consumer: the class, the shape, the family, and whether the
    /// class was asserted by the text-head table rather than derived.
    pub consumers: Vec<String>,
    pub classes: Vec<(&'static str, usize)>,
    pub char_semantics_required: bool,
    pub char_reasons: Vec<String>,
    pub shared_tails: Vec<ExprId>,
    pub prefix_consumers: Vec<ExprId>,
    pub advisory: Advisory,
    pub advisory_rule: &'static str,
    pub advisory_reason: Option<String>,
    pub verified: Verified,
}

impl TextView {
    pub fn of(m: &Module, t: &TextFlow, lf: &ListFlow, v: &Verdicts) -> TextView {
        let consumers = t
            .consumers
            .iter()
            .map(|c| {
                format!(
                    "node {:<7} {:<14} class {:<14} [{}]{}{}",
                    c.at,
                    c.shape.name(),
                    c.class.name(),
                    c.rule,
                    c.family
                        .map(|f| format!(" family {}", f.name()))
                        .unwrap_or_default(),
                    if c.asserted {
                        format!(" (asserted; M2.3c said {})", c.list_rule)
                    } else {
                        format!(" (from {})", c.list_rule)
                    }
                )
            })
            .collect();
        TextView {
            module: t.module.clone(),
            producer: t.producer,
            list: ListView::of(m, lf, v),
            element_type_evidence: t.element_type_evidence,
            selection: t
                .selection
                .iter()
                .map(|e| (e.rule, evidence_note(m, e)))
                .collect(),
            shape: t.shape,
            shape_rule: t.shape_rule,
            literal: t.literal,
            append_chain: t.append_chain,
            append_operand: t.append_operand,
            consumers,
            classes: vec![
                ("CompleteOutput", t.complete),
                ("Prefix", t.prefix),
                ("Incremental", t.incremental),
                ("Retained", t.retained),
                ("Unknown", t.class_unknown),
            ],
            char_semantics_required: t.char_semantics_required,
            char_reasons: t
                .char_reasons
                .iter()
                .map(|(rule, why, at)| format!("{rule}: {why} at node {at}"))
                .collect(),
            shared_tails: t.shared_tails.clone(),
            prefix_consumers: t.prefix_consumers.clone(),
            advisory: t.advisory,
            advisory_rule: t.advisory_rule,
            advisory_reason: t.advisory_reason.clone(),
            verified: v.text(t),
        }
    }

    pub fn header(&self) -> String {
        format!(
            "{} node {} — text flow, {} by {}, shape {}, advisory {}",
            self.module,
            self.producer,
            self.list.kind.name(),
            self.element_type_evidence.name(),
            self.shape.name(),
            self.advisory.name()
        )
    }
}

//------------------------------------------------------------------------------
// Provenance: what the three proof objects say about one Core node
//------------------------------------------------------------------------------

/// Everything the M2.3 proof objects have to say about one node, in the
/// footer shape M2.1's Parsec proof and M2.2's tuple proof already use.
#[derive(Debug, Clone, Default, Serialize)]
pub struct NodeProof {
    pub node: ExprId,
    /// `field: OuterToken f1 …`, `list: cons chain …`, `text: …`.
    pub what: Option<String>,
    pub verdict: Option<String>,
    /// How this node takes part.
    pub role: Option<String>,
    pub facts: Vec<String>,
    pub consumers: Vec<String>,
    pub evidence: Vec<(&'static str, String)>,
}

impl NodeProof {
    pub fn is_empty(&self) -> bool {
        self.what.is_none() && self.role.is_none() && self.evidence.is_empty()
    }
}

/// Which M2.3 sites a node or a binder takes part in, precomputed once so
/// that `h2r show` can annotate every node it prints. Any of the three
/// censuses may be absent (`--no-fields` / `--no-lists` / `--no-text`),
/// exactly as the Parsec and tuple objects are.
pub struct Provenance<'a> {
    m: &'a Module,
    fields: Option<&'a crate::fields::Fields<'a>>,
    lists: Option<&'a crate::lists::Lists<'a>>,
    /// Text flows of this module, by producer node.
    text: HashMap<ExprId, &'a TextFlow>,
    v: &'a Verdicts,
    /// Construction node -> index into the field flows.
    con: HashMap<ExprId, usize>,
    /// A field binder -> (flow index, field).
    field_binders: HashMap<BinderId, Vec<(usize, u32)>>,
    /// Producer node -> index into the list flows.
    prod: HashMap<ExprId, usize>,
    /// A cell node -> (flow index, which cell).
    cells: HashMap<ExprId, Vec<(usize, usize)>>,
    /// A consumer node -> (flow index, consumer index).
    list_uses: HashMap<ExprId, Vec<(usize, usize)>>,
    /// A tail alias or the flow's own binder -> (flow index, what it is).
    list_binders: HashMap<BinderId, Vec<(usize, &'static str)>>,
    /// Emit the list footers. The list flows are indexed even when this is
    /// false, because a text flow *refines* one and is found through it —
    /// `--no-lists` suppresses the list footer, not the text one.
    list_footers: bool,
}

impl<'a> Provenance<'a> {
    pub fn of(
        m: &'a Module,
        fields: Option<&'a crate::fields::Fields<'a>>,
        lists: Option<&'a crate::lists::Lists<'a>>,
        text: &'a [TextFlow],
        v: &'a Verdicts,
        list_footers: bool,
    ) -> Provenance<'a> {
        let mut p = Provenance {
            m,
            fields,
            lists,
            text: HashMap::new(),
            v,
            con: HashMap::new(),
            field_binders: HashMap::new(),
            prod: HashMap::new(),
            cells: HashMap::new(),
            list_uses: HashMap::new(),
            list_binders: HashMap::new(),
            list_footers,
        };
        for t in text.iter().filter(|t| t.module == m.name) {
            p.text.insert(t.producer, t);
        }
        if let Some(fs) = fields {
            for (i, f) in fs.flows.iter().enumerate() {
                p.con.insert(f.construction, i);
                for o in &f.observations {
                    if let (Some(b), Some(idx)) = (o.binder, o.field)
                        && matches!(o.kind, ObsKind::FieldDemanded | ObsKind::FieldBoundUnused)
                    {
                        p.field_binders.entry(b).or_default().push((i, idx));
                    }
                }
            }
        }
        if let Some(ls) = lists {
            for (i, f) in ls.flows.iter().enumerate() {
                p.prod.insert(f.producer, i);
                for (k, c) in f.cells.iter().enumerate() {
                    p.cells.entry(*c).or_default().push((i, k));
                }
                if let Some(b) = f.bound {
                    p.list_binders.entry(b).or_default().push((i, "spine"));
                }
                for (ci, c) in f.consumers.iter().enumerate() {
                    if c.at != 0 {
                        p.list_uses.entry(c.at).or_default().push((i, ci));
                    }
                    if let ConsumerKind::ConsAlt { .. } = c.kind
                        && let Expr::Case { alts, .. } = m.expr(c.at)
                    {
                        for a in alts {
                            if a.binders.len() == 2 {
                                p.list_binders
                                    .entry(a.binders[0])
                                    .or_default()
                                    .push((i, "head"));
                                p.list_binders
                                    .entry(a.binders[1])
                                    .or_default()
                                    .push((i, "tail alias"));
                            }
                        }
                    }
                }
            }
        }
        p
    }

    fn field_flow(&self, i: usize) -> &FieldFlow {
        &self.fields.expect("field flows").flows[i]
    }

    fn list_flow(&self, i: usize) -> &ListFlow {
        &self.lists.expect("list flows").flows[i]
    }

    /// The inline mark `h2r show` writes next to a node.
    pub fn node_note(&self, id: ExprId) -> Option<String> {
        let mut parts: Vec<String> = Vec::new();
        if let Some(i) = self.con.get(&id) {
            let f = self.field_flow(*i);
            parts.push(format!(
                "{} construction, arity {}, {}",
                f.occ,
                f.arity,
                reps_of(f)
            ));
        }
        if !self.list_footers {
            return (!parts.is_empty()).then(|| parts.join("; "));
        }
        for (i, k) in self.cells.get(&id).into_iter().flatten() {
            let f = self.list_flow(*i);
            parts.push(format!("cell {} of {} list flow #{i}", k, f.kind.name()));
        }
        if let Some(i) = self.prod.get(&id) {
            let f = self.list_flow(*i);
            parts.push(format!(
                "list flow #{i} producer, {}{}",
                f.rec.name(),
                self.text
                    .get(&id)
                    .map(|t| format!(", text {}", t.advisory.name()))
                    .unwrap_or_default()
            ));
        }
        for (i, ci) in self.list_uses.get(&id).into_iter().flatten() {
            parts.push(format!(
                "{} of list flow #{i}",
                consumer_name(&self.list_flow(*i).consumers[*ci].kind)
            ));
        }
        (!parts.is_empty()).then(|| parts.join("; "))
    }

    /// The same for a binder.
    pub fn binder_note(&self, b: BinderId) -> Option<String> {
        let mut parts: Vec<String> = Vec::new();
        for (i, idx) in self.field_binders.get(&b).into_iter().flatten() {
            let f = self.field_flow(*i);
            let v = &f.verdicts[*idx as usize];
            parts.push(format!("field {idx} of {} ⇒ {}", f.occ, v.rep.name()));
        }
        if self.list_footers {
            for (i, what) in self.list_binders.get(&b).into_iter().flatten() {
                parts.push(format!("{what} of list flow #{i}"));
            }
        }
        (!parts.is_empty()).then(|| parts.join("; "))
    }

    /// Every footer this node earns: one per field construction, list flow
    /// or text flow it takes part in, as itself or as an occurrence.
    pub fn proofs_at(&self, node: ExprId) -> Vec<NodeProof> {
        let m = self.m;
        let mut out: Vec<NodeProof> = Vec::new();
        let mut field_flows: BTreeSet<usize> = BTreeSet::new();
        let mut list_flows: BTreeSet<usize> = BTreeSet::new();
        field_flows.extend(self.con.get(&node).copied());
        list_flows.extend(self.prod.get(&node).copied());
        list_flows.extend(self.cells.get(&node).into_iter().flatten().map(|(i, _)| *i));
        list_flows.extend(
            self.list_uses
                .get(&node)
                .into_iter()
                .flatten()
                .map(|(i, _)| *i),
        );
        // An occurrence of a field binder, a tail alias or a spine binder.
        for b in [m.resolve(m.strip(node)), binder_bound_here(m, node)]
            .into_iter()
            .flatten()
        {
            field_flows.extend(
                self.field_binders
                    .get(&b)
                    .into_iter()
                    .flatten()
                    .map(|(i, _)| *i),
            );
            list_flows.extend(
                self.list_binders
                    .get(&b)
                    .into_iter()
                    .flatten()
                    .map(|(i, _)| *i),
            );
        }
        for i in field_flows {
            out.push(self.field_proof(node, i));
        }
        for i in list_flows {
            if self.list_footers {
                out.push(self.list_proof(node, i));
            }
            let f = self.list_flow(i);
            if let Some(t) = self.text.get(&f.producer) {
                out.push(self.text_proof(node, t, f));
            }
        }
        out
    }

    fn field_proof(&self, node: ExprId, i: usize) -> NodeProof {
        let m = self.m;
        let f = self.field_flow(i);
        let mut p = NodeProof {
            node,
            what: Some(format!(
                "{} {} field(s), construction node {} ({})",
                f.occ,
                f.arity,
                f.construction,
                if f.program { "program" } else { "library" }
            )),
            ..Default::default()
        };
        let mut roles: Vec<String> = Vec::new();
        if self.con.get(&node) == Some(&i) {
            roles.push("the construction itself".to_string());
        }
        for b in [m.resolve(m.strip(node)), binder_bound_here(m, node)]
            .into_iter()
            .flatten()
        {
            for (fi, idx) in self.field_binders.get(&b).into_iter().flatten() {
                if *fi == i {
                    roles.push(format!(
                        "an occurrence of the binder field {idx} lands in ({}#{b})",
                        m.binder(b).occ
                    ));
                }
            }
        }
        roles.dedup();
        if !roles.is_empty() {
            p.role = Some(roles.join("; "));
        }
        for v in &f.verdicts {
            let status = self.v.field(&f.module, f.construction, v);
            p.facts.push(format!(
                "f{} demand {:?} / {:?} / {:?} ⇒ {} [verified: {}]{}",
                v.index,
                v.demand,
                v.strictness,
                v.recursion,
                v.rep.name(),
                status.name(),
                v.reason_key()
                    .map(|r| format!("  [{}: {r}]", v.rule))
                    .unwrap_or_else(|| if v.routes.is_empty() {
                        String::new()
                    } else {
                        format!("  [{}]", v.route_key())
                    })
            ));
            for e in &v.evidence {
                p.evidence.push((e.rule, evidence_note(m, e)));
            }
        }
        for o in &f.observations {
            p.consumers.push(
                describe_observation(m, o, o.field.unwrap_or(0))
                    .unwrap_or_else(|| format!("{} at node {}", o.rule, o.at)),
            );
        }
        for e in &f.evidence {
            p.evidence.push((e.rule, evidence_note(m, e)));
        }
        p
    }

    fn list_proof(&self, node: ExprId, i: usize) -> NodeProof {
        let m = self.m;
        let f = self.list_flow(i);
        let mut p = NodeProof {
            node,
            what: Some(format!(
                "{} #{i}{} at node {}{}",
                f.kind.name(),
                if f.cells.is_empty() {
                    String::new()
                } else {
                    format!(" ({} cell(s))", f.cells.len())
                },
                f.producer,
                if f.producer_name.is_empty() {
                    String::new()
                } else {
                    format!(" ({})", f.producer_name)
                }
            )),
            verdict: Some(format!(
                "advisory {} [{}] [verified: {}]{}",
                f.rec.name(),
                f.rec_rule,
                self.v.list(f).name(),
                f.rec_reason
                    .as_ref()
                    .map(|r| format!("  [{r}]"))
                    .unwrap_or_default()
            )),
            ..Default::default()
        };
        let mut roles: Vec<String> = Vec::new();
        if self.prod.get(&node) == Some(&i) {
            roles.push("the producer itself".to_string());
        }
        for (fi, k) in self.cells.get(&node).into_iter().flatten() {
            if *fi == i {
                roles.push(format!("cell {k} of the chain"));
            }
        }
        for (fi, ci) in self.list_uses.get(&node).into_iter().flatten() {
            if *fi == i {
                roles.push(format!(
                    "consumer: {}",
                    consumer_line(m, &f.consumers[*ci]).what
                ));
            }
        }
        for b in [m.resolve(m.strip(node)), binder_bound_here(m, node)]
            .into_iter()
            .flatten()
        {
            for (fi, what) in self.list_binders.get(&b).into_iter().flatten() {
                if *fi == i {
                    roles.push(format!("{what} ({}#{b})", m.binder(b).occ));
                }
            }
        }
        roles.dedup();
        if !roles.is_empty() {
            p.role = Some(roles.join("; "));
        }
        let view = ListView::of(m, f, self.v);
        for (name, value, rule) in &view.facts {
            p.facts.push(format!("{name} {value} [{rule}]"));
        }
        for c in &view.consumers {
            p.consumers.push(c.headline.clone());
        }
        for e in &f.evidence {
            p.evidence.push((e.rule, evidence_note(m, e)));
        }
        p
    }

    fn text_proof(&self, node: ExprId, t: &TextFlow, f: &ListFlow) -> NodeProof {
        let m = self.m;
        let mut p = NodeProof {
            node,
            what: Some(format!(
                "text flow over list flow at node {} — Char by {}, shape {}",
                t.producer,
                t.element_type_evidence.name(),
                t.shape.name()
            )),
            verdict: Some(format!(
                "advisory {} [{}] [verified: {}]{}",
                t.advisory.name(),
                t.advisory_rule,
                self.v.text(t).name(),
                t.advisory_reason
                    .as_ref()
                    .map(|r| format!("  [{r}]"))
                    .unwrap_or_default()
            )),
            ..Default::default()
        };
        let _ = f;
        p.facts.push(format!(
            "classes: {} complete / {} prefix / {} incremental / {} retained / {} unknown",
            t.complete, t.prefix, t.incremental, t.retained, t.class_unknown
        ));
        if let Some(a) = t.append_chain {
            p.facts.push(format!(
                "append chain of {} operand segment(s), {}, {} opaque",
                a.length,
                if a.all_literal {
                    "all literal"
                } else {
                    "not all literal"
                },
                a.opaque
            ));
        }
        if t.literal {
            p.facts
                .push("a string literal producer [X12-LITERAL]".into());
        }
        p.facts.push(format!(
            "char_semantics_required: {}{}",
            t.char_semantics_required,
            if t.char_reasons.is_empty() {
                String::new()
            } else {
                format!(
                    " ({})",
                    t.char_reasons
                        .iter()
                        .map(|(_, w, _)| w.as_str())
                        .collect::<Vec<_>>()
                        .join("; ")
                )
            }
        ));
        for c in &t.consumers {
            p.consumers.push(format!(
                "node {} {} class {} [{}]{}",
                c.at,
                c.shape.name(),
                c.class.name(),
                c.rule,
                if c.asserted { " (asserted)" } else { "" }
            ));
        }
        for e in t.selection.iter().chain(&t.evidence) {
            p.evidence.push((e.rule, evidence_note(m, e)));
        }
        p
    }
}

/// The binder a node *binds*, when it is a `Lam` or a `Case`.
fn binder_bound_here(m: &Module, node: ExprId) -> Option<BinderId> {
    match m.expr(node) {
        Expr::Lam { binder, .. } | Expr::Case { binder, .. } => Some(*binder),
        _ => None,
    }
}

/// A construction's field reps, joined for the inline mark.
fn reps_of(f: &FieldFlow) -> String {
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    for v in &f.verdicts {
        *counts.entry(v.rep.name()).or_default() += 1;
    }
    counts
        .into_iter()
        .map(|(r, n)| {
            if n == 1 {
                r.to_string()
            } else {
                format!("{r} {n}")
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}
