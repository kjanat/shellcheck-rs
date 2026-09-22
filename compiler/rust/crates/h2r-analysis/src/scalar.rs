//! The normalised scalar view: what the program looks like with one proven
//! tuple gone.
//!
//! [`crate::tuples`] proves *that* a tuple is transport. This module says
//! *what replaces it*, as an IR-level view — no Rust, no Core rewrite. The
//! construction's fields become named scalars `f0…f{n-1}`, and every
//! consumer of the flow becomes a binding over those scalars:
//!
//! * `case t of (a, b) -> e`  ⇒  `a := f0; b := f1; e`
//! * a lazy selector `case t of (_, s, _) -> s`  ⇒  `s := f1`
//! * a re-tupling  ⇒  the outer construction's fields *are* the inner's
//!   scalars, and the outer's own fate is printed beside it
//! * for a [`TupleFate::WorkerReturn`], the returning function's result
//!   becomes *n* scalar results and each call site binds them:
//!   `case (f x) of (a, s) -> e`  ⇒  `(a, s) := f x`
//!
//! Every line names the source node(s) and the rule that justifies it, and
//! the view is **complete**: every consumer on the flow is placed in
//! exactly one line, and every call site the flow proved is placed exactly
//! once — asserted, and reported as `0 unplaced` the way the recovered
//! Parsec graph reports its edges.
//!
//! Nothing here re-derives a verdict. The view reads the flow's own
//! consumer list and evidence; if the flow is not removable there is no
//! view to print.

use std::collections::{BTreeSet, HashMap, HashSet};

use h2r_core_ir::{Alt, AltCon, BinderId, Expr, ExprId, Module};
use serde::Serialize;

use crate::tuples::{
    Evidence, T2_SCRUTINISED, T3_SELECTED, T4_RETUPLE, T5_PASSED_LOCAL, T6_RETURNED,
    T7_CALL_RESULT, T12_NESTED, T13_PARSEC_CONT, T14_FORCED, TupleFate, TupleFlow, TupleUse,
    Tuples,
};

/// What one line of the view is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum LineKind {
    /// A field of the construction, as a named scalar.
    Scalar,
    /// The value crossing a boundary: a return, or a local callee's
    /// parameter being split.
    Hop,
    /// A call site of a function whose result became *n* scalar results.
    CallSite,
    /// A consumer that reads fields: the bindings it becomes.
    Binding,
    /// A consumer that disappears without binding anything.
    Note,
}

/// One line of the normalised view.
#[derive(Debug, Clone, Serialize)]
pub struct ViewLine {
    pub kind: LineKind,
    /// The rules that justify it, in the order they fired.
    pub rules: Vec<&'static str>,
    /// The Core nodes it reads.
    pub nodes: Vec<ExprId>,
    pub text: String,
    /// Index into [`TupleFlow::consumers`], when this line places one.
    pub consumer: Option<usize>,
    /// The call site this line places, when it places one.
    pub call_site: Option<ExprId>,
}

/// One field of the construction, as a scalar.
#[derive(Debug, Clone, Serialize)]
pub struct ScalarDef {
    pub index: u32,
    pub name: String,
    /// The Core node the field's value is.
    pub node: ExprId,
    /// A one-line rendering of that value.
    pub text: String,
}

/// The program with one tuple removed.
#[derive(Debug, Clone, Serialize)]
pub struct ScalarView {
    pub module: String,
    pub construction: ExprId,
    pub boxed: bool,
    pub arity: u32,
    /// The constructor occurrence, for the header only.
    pub con: String,
    pub fate: TupleFate,
    /// Did the independent verifier re-derive this verdict?
    pub verified: bool,
    pub scalars: Vec<ScalarDef>,
    pub lines: Vec<ViewLine>,
    /// Consumers placed, and call sites placed.
    pub consumers: usize,
    pub call_sites: usize,
    /// Consumers or call sites the view could not place. Asserted empty;
    /// carried so that the failure is printable rather than only a panic.
    pub unplaced: Vec<String>,
}

impl ScalarView {
    /// Every consumer and every call site is in exactly one line.
    pub fn check(&self) {
        assert!(
            self.unplaced.is_empty(),
            "scalar view of {} node {} left {} thing(s) unplaced: {:?}",
            self.module,
            self.construction,
            self.unplaced.len(),
            self.unplaced
        );
    }
}

/// A very short rendering of an expression, for a scalar's source column.
fn brief(m: &Module, id: ExprId) -> String {
    let node = m.strip(id);
    match m.expr(node) {
        Expr::Var { occ, .. } => occ.clone(),
        Expr::Lit(_) => "<literal>".to_string(),
        Expr::Lam { .. } => "\\… -> …".to_string(),
        Expr::Let { .. } => "let … in …".to_string(),
        Expr::Case { .. } => "case … of …".to_string(),
        Expr::App { .. } => {
            let (head, args) = m.spine(node);
            let h = match m.expr(m.strip(head)) {
                Expr::Var { occ, .. } => occ.clone(),
                _ => "…".to_string(),
            };
            format!("{h} {}", vec!["…"; args.len().min(3)].join(" "))
        }
        Expr::Type { pretty, .. } => format!("@{pretty}"),
        Expr::Coercion => "<coercion>".to_string(),
        Expr::Cast { .. } | Expr::Tick(_) => "…".to_string(),
    }
}

/// The single alternative of a tuple `case`, when it has one.
fn tuple_alt(m: &Module, case: ExprId) -> Option<&Alt> {
    let Expr::Case { alts, .. } = m.expr(case) else {
        return None;
    };
    alts.first()
        .filter(|a| alts.len() == 1 && matches!(a.con, AltCon::DataAlt { .. }))
}

fn binder_name(m: &Module, b: BinderId) -> String {
    format!("{}#{b}", m.binder(b).occ)
}

/// The nodes of every call site the flow proved ([`T7_CALL_RESULT`]).
fn call_sites(flow: &TupleFlow) -> Vec<ExprId> {
    let mut out: Vec<ExprId> = Vec::new();
    let mut seen: HashSet<ExprId> = HashSet::new();
    for e in &flow.evidence {
        if e.rule != T7_CALL_RESULT {
            continue;
        }
        for n in &e.nodes {
            if seen.insert(*n) {
                out.push(*n);
            }
        }
    }
    out
}

/// The evidence entry of `rule` that reads `node`, if there is one.
fn evidence_at<'a>(flow: &'a TupleFlow, rule: &str, node: ExprId) -> Option<&'a Evidence> {
    flow.evidence
        .iter()
        .find(|e| e.rule == rule && e.nodes.contains(&node))
}

/// The normalised scalar view of one removable flow.
///
/// `verified` is the independent verifier's verdict, which the header
/// prints and nothing here reads: a view is a view of what the census
/// proved, and whether a second walk agrees is a separate fact.
pub fn view(t: &Tuples<'_>, flow: &TupleFlow, verified: bool) -> ScalarView {
    let m = t.module;
    let names: Vec<String> = (0..flow.arity).map(|i| format!("f{i}")).collect();
    let joined = names.join(", ");
    let (head, _) = m.spine(flow.construction);
    let con = match m.expr(m.strip(head)) {
        Expr::Var { occ, .. } => occ.clone(),
        _ => String::new(),
    };

    let mut v = ScalarView {
        module: flow.module.clone(),
        construction: flow.construction,
        boxed: flow.boxed,
        arity: flow.arity,
        con,
        fate: flow.fate,
        verified,
        scalars: flow
            .fields
            .iter()
            .enumerate()
            .map(|(i, f)| ScalarDef {
                index: i as u32,
                name: names[i].clone(),
                node: *f,
                text: brief(m, *f),
            })
            .collect(),
        lines: Vec::new(),
        consumers: 0,
        call_sites: 0,
        unplaced: Vec::new(),
    };

    // Which call sites a consumer line folds into itself: a scrutiny whose
    // scrutinee *is* the call, which is the `(a, s) := f x` shape.
    let sites = call_sites(flow);
    let site_set: HashSet<ExprId> = sites.iter().copied().collect();
    let mut folded: HashSet<ExprId> = HashSet::new();
    let scrutinee_call = |case: ExprId| -> Option<ExprId> {
        let Expr::Case { scrut, .. } = m.expr(case) else {
            return None;
        };
        let root = m.spine_root(m.strip(*scrut));
        site_set.contains(&root).then_some(root)
    };

    for (ci, u) in flow.consumers.iter().enumerate() {
        match *u {
            TupleUse::Returned { function } => {
                let note = flow
                    .evidence
                    .iter()
                    .find(|e| e.rule == T6_RETURNED && e.binder == Some(function))
                    .map(|e| e.note.clone())
                    .unwrap_or_default();
                v.lines.push(ViewLine {
                    kind: LineKind::Hop,
                    rules: vec![T6_RETURNED],
                    nodes: Vec::new(),
                    text: format!(
                        "{} returns ({joined}) as {} scalar result(s) — {note}",
                        binder_name(m, function),
                        flow.arity
                    ),
                    consumer: Some(ci),
                    call_site: None,
                });
            }
            TupleUse::PassedTo {
                call,
                callee,
                param,
            } => {
                let rule = if evidence_at(flow, T13_PARSEC_CONT, call).is_some() {
                    T13_PARSEC_CONT
                } else {
                    T5_PASSED_LOCAL
                };
                v.lines.push(ViewLine {
                    kind: LineKind::Hop,
                    rules: vec![rule],
                    nodes: vec![call],
                    text: format!(
                        "parameter {param} of {} becomes {} scalar parameter(s); \
                         the call at node {call} passes {joined}",
                        binder_name(m, callee),
                        flow.arity
                    ),
                    consumer: Some(ci),
                    call_site: None,
                });
            }
            TupleUse::Scrutinised { case, .. } => {
                let alt = tuple_alt(m, case);
                let bound: Vec<String> = alt
                    .map(|a| a.binders.iter().map(|b| binder_name(m, *b)).collect())
                    .unwrap_or_default();
                let site = scrutinee_call(case);
                let (mut rules, mut nodes) = (vec![T2_SCRUTINISED], vec![case]);
                let text = match site {
                    Some(root) => {
                        folded.insert(root);
                        rules.insert(0, T7_CALL_RESULT);
                        nodes.insert(0, root);
                        format!(
                            "({}) := {} at node {root}   [the call returns {} scalar(s)]",
                            bound.join(", "),
                            brief(m, root),
                            flow.arity
                        )
                    }
                    None => bound
                        .iter()
                        .enumerate()
                        .map(|(i, b)| format!("{b} := {}", names[i]))
                        .collect::<Vec<_>>()
                        .join("; "),
                };
                v.lines.push(ViewLine {
                    kind: LineKind::Binding,
                    rules,
                    nodes,
                    text: format!("at node {case}: {text}"),
                    consumer: Some(ci),
                    call_site: site,
                });
            }
            TupleUse::Selected { case, field } => {
                let name = tuple_alt(m, case)
                    .and_then(|a| a.binders.get(field as usize))
                    .map(|b| binder_name(m, *b))
                    .unwrap_or_else(|| format!("_{field}"));
                let site = scrutinee_call(case);
                let (mut rules, mut nodes) = (vec![T3_SELECTED], vec![case]);
                let text = match site {
                    Some(root) => {
                        folded.insert(root);
                        rules.insert(0, T7_CALL_RESULT);
                        nodes.insert(0, root);
                        format!(
                            "{name} := result {field} of {} at node {root}",
                            brief(m, root)
                        )
                    }
                    None => format!("{name} := {}", names[field as usize]),
                };
                v.lines.push(ViewLine {
                    kind: LineKind::Binding,
                    rules,
                    nodes,
                    text: format!("at node {case}: {text}   [the lazy selector thunk goes too]"),
                    consumer: Some(ci),
                    call_site: site,
                });
            }
            TupleUse::Retupled { outer } => {
                let fate = t
                    .flow_at(outer)
                    .map(|o| format!("{:?}", o.fate))
                    .unwrap_or_else(|| "not in the population".into());
                v.lines.push(ViewLine {
                    kind: LineKind::Binding,
                    rules: vec![T4_RETUPLE],
                    nodes: vec![outer],
                    text: format!(
                        "at node {outer}: the field-wise copy's own fields are {joined} \
                         (that construction's fate: {fate})"
                    ),
                    consumer: Some(ci),
                    call_site: None,
                });
            }
            TupleUse::NestedIn { outer, field } => {
                let o = t.flow_at(outer);
                let fate = o
                    .map(|o| format!("{:?}", o.fate))
                    .unwrap_or_else(|| "not in the population".into());
                let through: Vec<String> = o
                    .into_iter()
                    .flat_map(|o| o.consumers.iter())
                    .filter_map(|u| match u {
                        TupleUse::Scrutinised { case, .. } | TupleUse::Selected { case, .. } => {
                            tuple_alt(m, *case).and_then(|a| a.binders.get(field as usize))
                        }
                        _ => None,
                    })
                    .map(|b| binder_name(m, *b))
                    .collect();
                v.lines.push(ViewLine {
                    kind: LineKind::Binding,
                    rules: vec![T12_NESTED],
                    nodes: vec![outer],
                    text: format!(
                        "at node {outer}: field {field} of a {fate} tuple — that box is gone too, \
                         so {joined} reach its readers directly ({})",
                        if through.is_empty() {
                            "no field binder".to_string()
                        } else {
                            format!("through {}", through.join(", "))
                        }
                    ),
                    consumer: Some(ci),
                    call_site: None,
                });
            }
            TupleUse::Forced { case } => {
                v.lines.push(ViewLine {
                    kind: LineKind::Note,
                    rules: vec![T14_FORCED],
                    nodes: vec![case],
                    text: format!(
                        "at node {case}: forced whole, no field read — \
                         forcing a constructor application is a no-op, the force disappears"
                    ),
                    consumer: Some(ci),
                    call_site: None,
                });
            }
            // A removable flow has none of these: each one records an
            // escape, which decides `Preserve` or `Unresolved`. Placed
            // anyway, so that a view is never silently incomplete.
            TupleUse::StoredIn { .. }
            | TupleUse::PassedToUnknown { .. }
            | TupleUse::Escapes { .. } => {
                v.unplaced.push(format!("{} at node {}", u.kind(), u.at()));
            }
        }
    }

    // Call sites no consumer folded in: the result is bound and read later.
    for root in &sites {
        if folded.contains(root) {
            continue;
        }
        v.lines.push(ViewLine {
            kind: LineKind::CallSite,
            rules: vec![T7_CALL_RESULT],
            nodes: vec![*root],
            text: format!(
                "at node {root}: ({joined}) := {} — {} scalar result(s) in place of the tuple",
                brief(m, *root),
                flow.arity
            ),
            consumer: None,
            call_site: Some(*root),
        });
    }

    // Completeness: every consumer and every call site placed exactly once.
    let placed: Vec<usize> = v.lines.iter().filter_map(|l| l.consumer).collect();
    let distinct: BTreeSet<usize> = placed.iter().copied().collect();
    if distinct.len() != placed.len() {
        v.unplaced.push("a consumer was placed twice".to_string());
    }
    for (ci, u) in flow.consumers.iter().enumerate() {
        if !distinct.contains(&ci) && !v.unplaced.iter().any(|x| x.contains(u.kind())) {
            v.unplaced
                .push(format!("unplaced {} at node {}", u.kind(), u.at()));
        }
    }
    let placed_sites: BTreeSet<ExprId> = v.lines.iter().filter_map(|l| l.call_site).collect();
    for root in &sites {
        if !placed_sites.contains(root) {
            v.unplaced
                .push(format!("unplaced call site at node {root}"));
        }
    }
    v.consumers = distinct.len();
    v.call_sites = placed_sites.len();
    // Read in the order the value moves: out of the producer, through the
    // call sites, into the bindings that read it.
    v.lines.sort_by_key(|l| match l.kind {
        LineKind::Scalar => 0,
        LineKind::Hop => 1,
        LineKind::CallSite => 2,
        LineKind::Binding => 3,
        LineKind::Note => 4,
    });
    v
}

//------------------------------------------------------------------------------
// Provenance of one node
//------------------------------------------------------------------------------

/// Everything the tuple proof object has to say about one Core node, in the
/// shape `h2r show` prints it (the same shape the Parsec proof uses).
#[derive(Debug, Clone, Default, Serialize)]
pub struct NodeProof {
    pub node: ExprId,
    /// `(,,) boxed, arity 3, construction node 5762 (flow #7)`.
    pub tuple: Option<String>,
    /// `WorkerReturn  [verified: yes]`, or the fate with its reason.
    pub fate: Option<String>,
    /// How this node takes part: the construction, an alias, a consumer.
    pub role: Option<String>,
    /// One line per consumer of the flow.
    pub consumers: Vec<String>,
    /// Rule id and what it says.
    pub evidence: Vec<(&'static str, String)>,
}

impl NodeProof {
    pub fn is_empty(&self) -> bool {
        self.tuple.is_none() && self.role.is_none() && self.evidence.is_empty()
    }
}

/// Which flows a node or a binder takes part in, precomputed once so that
/// `h2r show` can annotate every node it prints.
pub struct Provenance<'t, 'm> {
    t: &'t Tuples<'m>,
    /// Construction spine root -> flow index.
    con: HashMap<ExprId, usize>,
    /// A consumer's node -> (flow index, consumer index).
    uses: HashMap<ExprId, Vec<(usize, usize)>>,
    /// A binder the tuple is reachable under -> (flow index, what it is).
    binders: HashMap<BinderId, Vec<(usize, &'static str)>>,
    /// Verdicts of the independent verifier, by construction node. Empty
    /// when no verification was run.
    verified: HashSet<ExprId>,
}

impl<'t, 'm> Provenance<'t, 'm> {
    pub fn of(t: &'t Tuples<'m>, verified: HashSet<ExprId>) -> Provenance<'t, 'm> {
        let m = t.module;
        let mut p = Provenance {
            t,
            con: HashMap::new(),
            uses: HashMap::new(),
            binders: HashMap::new(),
            verified,
        };
        for (i, f) in t.flows.iter().enumerate() {
            p.con.insert(f.construction, i);
            if let Some(b) = f.bound {
                p.binders.entry(b).or_default().push((i, "alias"));
            }
            for (ci, u) in f.consumers.iter().enumerate() {
                let at = u.at();
                if at != 0 {
                    p.uses.entry(at).or_default().push((i, ci));
                }
                match u {
                    TupleUse::Returned { function } => {
                        p.binders.entry(*function).or_default().push((i, "returns"))
                    }
                    TupleUse::Scrutinised { case, .. } | TupleUse::Selected { case, .. } => {
                        if let Expr::Case { binder, .. } = m.expr(*case) {
                            p.binders
                                .entry(*binder)
                                .or_default()
                                .push((i, "case alias"));
                        }
                        if let Some(a) = tuple_alt(m, *case) {
                            for (k, b) in a.binders.iter().enumerate() {
                                p.binders.entry(*b).or_default().push((i, field_word(k)));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        p
    }

    fn flow(&self, i: usize) -> &TupleFlow {
        &self.t.flows[i]
    }

    fn header(&self, i: usize) -> String {
        let f = self.flow(i);
        let m = self.t.module;
        let (head, _) = m.spine(f.construction);
        let con = match m.expr(m.strip(head)) {
            Expr::Var { occ, .. } => occ.clone(),
            _ => String::new(),
        };
        format!(
            "{con} {}, arity {}, construction node {} (flow #{i})",
            if f.boxed { "boxed" } else { "unboxed" },
            f.arity,
            f.construction
        )
    }

    fn fate_line(&self, i: usize) -> String {
        let f = self.flow(i);
        match f.fate {
            TupleFate::ScalarReplace | TupleFate::WorkerReturn => format!(
                "{:?}  [verified: {}]",
                f.fate,
                if self.verified.contains(&f.construction) {
                    "yes"
                } else {
                    "no"
                }
            ),
            _ => match f.reason_key() {
                Some(r) => format!("{:?}  [{r}]", f.fate),
                None => format!("{:?}", f.fate),
            },
        }
    }

    /// A one-word inline mark for a node: what `h2r show` writes next to it.
    pub fn node_note(&self, id: ExprId) -> Option<String> {
        let mut parts: Vec<String> = Vec::new();
        if let Some(i) = self.con.get(&id) {
            let f = self.flow(*i);
            parts.push(format!(
                "tuple flow #{i} construction, arity {}, {:?}",
                f.arity, f.fate
            ));
        }
        for (i, ci) in self.uses.get(&id).into_iter().flatten() {
            parts.push(format!(
                "{} of tuple flow #{i}",
                self.flow(*i).consumers[*ci].kind()
            ));
        }
        (!parts.is_empty()).then(|| parts.join("; "))
    }

    /// The same for a binder: what the tuple is reachable under.
    pub fn binder_note(&self, b: BinderId) -> Option<String> {
        let parts: Vec<String> = self
            .binders
            .get(&b)?
            .iter()
            .map(|(i, what)| format!("{what} of tuple flow #{i}"))
            .collect();
        (!parts.is_empty()).then(|| parts.join("; "))
    }

    /// Every flow this node takes part in, as a construction, an alias, a
    /// consumer, or an occurrence of one.
    pub fn flows_at(&self, node: ExprId) -> Vec<usize> {
        let m = self.t.module;
        let mut out: BTreeSet<usize> = BTreeSet::new();
        out.extend(self.con.get(&node).copied());
        out.extend(self.uses.get(&node).into_iter().flatten().map(|(i, _)| *i));
        // An occurrence of an alias, a producer or a field binder.
        if let Some(b) = m.resolve(m.strip(node))
            && let Some(v) = self.binders.get(&b)
        {
            out.extend(v.iter().map(|(i, _)| *i));
        }
        // The binding site of one of those binders.
        if let Some(b) = binder_bound_here(m, node)
            && let Some(v) = self.binders.get(&b)
        {
            out.extend(v.iter().map(|(i, _)| *i));
        }
        out.into_iter().collect()
    }

    /// Everything proven about `node` for one flow, for the `h2r show`
    /// footer.
    pub fn proof_at(&self, node: ExprId, i: usize) -> NodeProof {
        let m = self.t.module;
        let f = self.flow(i);
        let mut p = NodeProof {
            node,
            tuple: Some(self.header(i)),
            fate: Some(self.fate_line(i)),
            ..Default::default()
        };
        let mut roles: Vec<String> = Vec::new();
        if self.con.get(&node) == Some(&i) {
            roles.push("the construction itself".to_string());
        }
        for (fi, ci) in self.uses.get(&node).into_iter().flatten() {
            if *fi == i {
                roles.push(format!("consumer: {}", describe(m, &f.consumers[*ci])));
            }
        }
        for b in [m.resolve(m.strip(node)), binder_bound_here(m, node)]
            .into_iter()
            .flatten()
        {
            for (fi, what) in self.binders.get(&b).into_iter().flatten() {
                if *fi == i {
                    roles.push(format!("{what} ({})", binder_name(m, b)));
                }
            }
        }
        roles.dedup();
        if !roles.is_empty() {
            p.role = Some(roles.join("; "));
        }
        for u in &f.consumers {
            p.consumers.push(describe(m, u));
        }
        for e in &f.evidence {
            let nodes = e
                .nodes
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            let b = match e.binder {
                Some(b) => format!(" [{}]", binder_name(m, b)),
                None => String::new(),
            };
            p.evidence
                .push((e.rule, format!("{} (node(s) {nodes}){b}", e.note)));
        }
        p
    }
}

/// The word for a field binder of a tuple match.
fn field_word(k: usize) -> &'static str {
    const W: [&str; 8] = [
        "field 0", "field 1", "field 2", "field 3", "field 4", "field 5", "field 6", "field 7",
    ];
    W.get(k).copied().unwrap_or("field")
}

/// The binder a node *binds*, when the node is a `Lam` or a `Case`: so that
/// asking about the lambda that returns the tuple finds its flow.
fn binder_bound_here(m: &Module, node: ExprId) -> Option<BinderId> {
    match m.expr(node) {
        Expr::Lam { binder, .. } | Expr::Case { binder, .. } => Some(*binder),
        _ => None,
    }
}

/// One consumer, as the footer prints it: what it is, where, and the rules.
fn describe(m: &Module, u: &TupleUse) -> String {
    match *u {
        TupleUse::Scrutinised { case, .. } => {
            format!("scrutinised at node {case} ({T2_SCRUTINISED})")
        }
        TupleUse::Selected { case, field } => {
            format!("field {field} selected on its own at node {case} ({T3_SELECTED})")
        }
        TupleUse::Returned { function } => format!(
            "returned from {} ({T6_RETURNED}) → its call sites ({T7_CALL_RESULT})",
            binder_name(m, function)
        ),
        TupleUse::PassedTo {
            call,
            callee,
            param,
        } => format!(
            "passed as argument {param} of {} at node {call} ({T5_PASSED_LOCAL})",
            binder_name(m, callee)
        ),
        TupleUse::Retupled { outer } => {
            format!("copied field by field into the construction at node {outer} ({T4_RETUPLE})")
        }
        TupleUse::NestedIn { outer, field } => {
            format!("field {field} of the removable tuple at node {outer} ({T12_NESTED})")
        }
        TupleUse::StoredIn { con } => {
            format!("stored in the constructor at node {con} (T9-STORED)")
        }
        TupleUse::Forced { case } => format!("forced whole at node {case} ({T14_FORCED})"),
        TupleUse::PassedToUnknown { call, why } => {
            format!("argument of the opaque call at node {call}: {why} (T10-OPAQUE-CALL)")
        }
        TupleUse::Escapes { at, why } => format!("escapes at node {at}: {why} (T11-ESCAPE)"),
    }
}
