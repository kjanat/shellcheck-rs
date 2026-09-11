//! Port of `ShellCheck.CFG` — Control Flow Graph construction from an AST.
//!
//! This is a faithful, dependency-light port of `src/ShellCheck/CFG.hs`. The
//! Haskell original uses `fgl` (`Data.Graph.Inductive`) for the graph and its
//! `Query.Dominators` for post-dominators. Here we hand-roll:
//!
//!   * a labeled directed graph ([`CFGraph`] / [`MutGraph`]) with adjacency,
//!   * a post-dominator algorithm ([`find_post_dominators`]) built from an
//!     iterative (Cooper-Harvey-Kennedy) dominator computation over the
//!     reversed graph — matching fgl's `dom`,
//!   * a topological sort ([`topsort`]) used by `renumber_topologically`.
//!
//! The graph-building monad (`RWS CFContext CFW Int`) is reproduced as the
//! [`Builder`] struct: `next` is the state (next node id), the four `CFW`
//! accumulators are the writer, and [`Ctx`] is the reader, saved/restored
//! around `local`-style scoping.
//!
//! Public entry point: [`build_graph`] (Haskell `buildGraph`).

use crate::ast::*;
use crate::astlib::get_literal_string;
use std::collections::{BTreeSet, HashMap, HashSet};

use regex::Regex;

/// Node id in the graph. Haskell `Node = Int`; all ids here are non-negative.
pub type Node = usize;

// ===========================================================================
// Data types (ported 1:1 from CFG.hs)
// ===========================================================================

/// Node labels in a Control Flow Graph (`data CFNode`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CFNode {
    /// A no-op node for structural purposes.
    CFStructuralNode,
    /// A no-op for graph inspection purposes.
    CFEntryPoint(String),
    /// Drop current prefix assignments.
    CFDropPrefixAssignments,
    /// A node with a certain effect on program state.
    CFApplyEffects(Vec<IdTagged<CFEffect>>),
    /// The execution of a command or function by literal string if possible.
    CFExecuteCommand(Option<String>),
    /// Execute a subshell (disjoint subgraph): reason, entry node, exit node.
    CFExecuteSubshell(String, Node, Node),
    /// Assignment of `$?`.
    CFSetExitCode(Id),
    /// The virtual 'exit' at the natural end of a subshell.
    CFImpliedExit,
    /// An exit statement resolvable at CFG build time.
    CFResolvedExit,
    /// An exit statement only resolvable at DFA time.
    CFUnresolvedExit,
    /// An unreachable node, serving as the unconnected end point of a range.
    CFUnreachable,
    /// Assignment of `$!`.
    CFSetBackgroundPid(Id),
}

/// Edge labels in a Control Flow Graph (`data CFEdge`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CFEdge {
    CFEErrExit,
    /// Regular control flow edge.
    CFEFlow,
    /// An edge that a human might think exists (e.g. backgrounded proc -> parent).
    CFEFalseFlow,
    /// An edge followed on exit.
    CFEExit,
}

/// Actions we track (`data CFEffect`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CFEffect {
    CFSetProps(Option<Scope>, String, BTreeSet<CFVariableProp>),
    CFUnsetProps(Option<Scope>, String, BTreeSet<CFVariableProp>),
    CFReadVariable(String),
    CFWriteVariable(String, CFValue),
    CFWriteGlobal(String, CFValue),
    CFWriteLocal(String, CFValue),
    CFWritePrefix(String, CFValue),
    CFDefineFunction(String, Id, Node, Node),
    CFUndefine(String),
    CFUndefineVariable(String),
    CFUndefineFunction(String),
    CFUndefineNameref(String),
    /// Usage implies that this is an array (e.g. it's expanded with index).
    CFHintArray(String),
    /// Operation implies that the variable will be defined (e.g. `[ -z "$var" ]`).
    CFHintDefined(String),
}

/// `data IdTagged a = IdTagged Id a`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdTagged<A> {
    pub id: Id,
    pub value: A,
}

impl<A> IdTagged<A> {
    pub fn new(id: Id, value: A) -> Self {
        IdTagged { id, value }
    }
}

/// Where a variable's value comes from (`data CFValue`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CFValue {
    /// The special 'uninitialized' value.
    CFValueUninitialized,
    /// An arbitrary array value.
    CFValueArray,
    /// An arbitrary string value.
    CFValueString,
    /// An arbitrary integer.
    CFValueInteger,
    /// Token `Id` concatenates and assigns the given parts.
    CFValueComputed(Id, Vec<CFStringPart>),
}

/// Simplified computed strings (`data CFStringPart`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CFStringPart {
    /// A known literal string value, like `foo`.
    CFStringLiteral(String),
    /// The contents of a variable, like `$foo` (may not be a string).
    CFStringVariable(String),
    /// A value that is unknown but an integer.
    CFStringInteger,
    /// An unknown string value, for things we can't handle.
    CFStringUnknown,
}

/// The properties of a variable (`data CFVariableProp`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CFVariableProp {
    CFVPExport,
    CFVPArray,
    CFVPAssociative,
    CFVPInteger,
}

/// `data Scope`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scope {
    GlobalScope,
    LocalScope,
    PrefixScope,
}

/// Options when generating CFG (`data CFGParameters`).
#[derive(Debug, Clone, Copy)]
pub struct CFGParameters {
    /// Whether the last element in a pipeline runs in the current shell.
    pub cf_lastpipe: bool,
    /// Whether all elements in a pipeline count towards the exit status.
    pub cf_pipefail: bool,
}

/// The result of building a CFG (`data CFGResult`).
#[derive(Debug, Clone)]
pub struct CFGResult {
    /// The graph itself.
    pub cf_graph: CFGraph,
    /// Map from Id to nominal start&end node (normal execution without exits).
    pub cf_id_to_range: HashMap<Id, (Node, Node)>,
    /// A set of all nodes belonging to an Id, recursively.
    pub cf_id_to_nodes: HashMap<Id, BTreeSet<Node>>,
    /// `cf_post_dominators[to]` lists all nodes that post-dominate `to`.
    /// Indexed by node id; holes (unused ids) are empty.
    pub cf_post_dominators: Vec<Vec<Node>>,
}

// ===========================================================================
// Graph representation (replaces fgl's Gr / mkGraph / nodes / edges)
// ===========================================================================

/// An immutable labeled directed multigraph. Mirrors `G.Gr CFNode CFEdge` for
/// the parts of the fgl interface the port relies on (`mkGraph`, `nodes`,
/// `edges`, `labNodes`, `labEdges`).
#[derive(Debug, Clone)]
pub struct CFGraph {
    pub nodes: Vec<(Node, CFNode)>,
    pub edges: Vec<(Node, Node, CFEdge)>,
}

impl CFGraph {
    /// `mkGraph nodes edges`.
    pub fn mk_graph(nodes: Vec<(Node, CFNode)>, edges: Vec<(Node, Node, CFEdge)>) -> CFGraph {
        CFGraph { nodes, edges }
    }

    /// Label of a node, if present.
    pub fn lab(&self, n: Node) -> Option<&CFNode> {
        self.nodes.iter().find(|(id, _)| *id == n).map(|(_, l)| l)
    }
}

/// A mutable adjacency-list graph used for the graph surgery required by
/// `inlineSubshells` / `safeUpdate` and the dominator computation.
#[derive(Debug, Clone)]
struct MutGraph {
    labels: HashMap<Node, CFNode>,
    // successors: succ[from] = [(to, label)]
    succ: HashMap<Node, Vec<(Node, CFEdge)>>,
    // predecessors: pred[to] = [(from, label)]
    pred: HashMap<Node, Vec<(Node, CFEdge)>>,
}

impl MutGraph {
    fn from(nodes: &[(Node, CFNode)], edges: &[(Node, Node, CFEdge)]) -> MutGraph {
        let mut g = MutGraph {
            labels: HashMap::new(),
            succ: HashMap::new(),
            pred: HashMap::new(),
        };
        for (n, l) in nodes {
            g.labels.insert(*n, l.clone());
            g.succ.entry(*n).or_default();
            g.pred.entry(*n).or_default();
        }
        for (from, to, label) in edges {
            g.succ.entry(*from).or_default().push((*to, *label));
            g.pred.entry(*to).or_default().push((*from, *label));
        }
        g
    }

    /// All node ids, ascending (mirrors PatriciaTree's `nodes`).
    fn node_list(&self) -> Vec<Node> {
        let mut v: Vec<Node> = self.labels.keys().copied().collect();
        v.sort_unstable();
        v
    }

    fn max_node(&self) -> Node {
        self.labels.keys().copied().max().unwrap_or(0)
    }

    /// `context g n` = (incoming, node, label, outgoing) with adjacency in
    /// `(neighbor, label)` form. Returns empty adjacency for a missing node.
    fn context(&self, n: Node) -> (Vec<(Node, CFEdge)>, Node, CFNode, Vec<(Node, CFEdge)>) {
        let incoming = self.pred.get(&n).cloned().unwrap_or_default();
        let outgoing = self.succ.get(&n).cloned().unwrap_or_default();
        let label = self
            .labels
            .get(&n)
            .cloned()
            .unwrap_or(CFNode::CFStructuralNode);
        (incoming, n, label, outgoing)
    }

    /// Remove a node and every edge touching it.
    fn del_node(&mut self, n: Node) {
        if let Some(outs) = self.succ.remove(&n) {
            for (to, _) in outs {
                if let Some(v) = self.pred.get_mut(&to) {
                    v.retain(|(m, _)| *m != n);
                }
            }
        }
        if let Some(ins) = self.pred.remove(&n) {
            for (from, _) in ins {
                if let Some(v) = self.succ.get_mut(&from) {
                    v.retain(|(m, _)| *m != n);
                }
            }
        }
        self.labels.remove(&n);
    }

    /// Insert a node with the given context (assumes it was just deleted).
    fn insert_context(
        &mut self,
        incoming: Vec<(Node, CFEdge)>,
        n: Node,
        label: CFNode,
        outgoing: Vec<(Node, CFEdge)>,
    ) {
        self.labels.insert(n, label);
        self.succ.entry(n).or_default();
        self.pred.entry(n).or_default();
        for (from, l) in incoming {
            self.succ.entry(from).or_default().push((n, l));
            self.pred.entry(n).or_default().push((from, l));
        }
        for (to, l) in outgoing {
            self.succ.entry(n).or_default().push((to, l));
            self.pred.entry(to).or_default().push((n, l));
        }
    }

    /// `ctx & (delNode node graph)` — replace a node's context wholesale.
    fn safe_update(
        &mut self,
        incoming: Vec<(Node, CFEdge)>,
        n: Node,
        label: CFNode,
        outgoing: Vec<(Node, CFEdge)>,
    ) {
        self.del_node(n);
        self.insert_context(incoming, n, label, outgoing);
    }

    /// `grev` — reverse every edge.
    fn grev(&mut self) {
        std::mem::swap(&mut self.succ, &mut self.pred);
    }
}

// ===========================================================================
// The graph-building "monad" (RWS) as a Builder
// ===========================================================================

/// A `(start, end)` node range. `data Range = Range Node Node`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range(pub Node, pub Node);

fn node_to_range(n: Node) -> Range {
    Range(n, n)
}

/// `CFW` — the writer output: (nodes, edges, id->range mapping, id->node assoc).
type CFW = (
    Vec<(Node, CFNode)>,
    Vec<(Node, Node, CFEdge)>,
    Vec<(Id, (Node, Node))>,
    Vec<(Id, Node)>,
);

/// The reader environment (`data CFContext`).
#[derive(Debug, Clone)]
struct Ctx {
    // cfIsCondition: set by asCondition but never read (kept for fidelity).
    is_condition: bool,
    is_function: bool,
    // cfLoopStack: defined but never read in CFG.hs (kept for fidelity).
    loop_stack: Vec<(Node, Node)>,
    token_stack: Vec<Id>,
    exit_target: Option<Node>,
    return_target: Option<Node>,
}

impl Ctx {
    fn new() -> Ctx {
        Ctx {
            is_condition: false,
            is_function: false,
            loop_stack: Vec::new(),
            token_stack: Vec::new(),
            exit_target: None,
            return_target: None,
        }
    }
}

/// The graph builder: RWS state (`next`) + writer (`nodes`/`edges`/`mapping`/
/// `assoc`) + reader (`ctx`).
struct Builder {
    next: Node,
    nodes: Vec<(Node, CFNode)>,
    edges: Vec<(Node, Node, CFEdge)>,
    mapping: Vec<(Id, (Node, Node))>,
    assoc: Vec<(Id, Node)>,
    ctx: Ctx,
    params: CFGParameters,
}

fn apply_single(id: Id, effect: CFEffect) -> CFNode {
    CFNode::CFApplyEffects(vec![IdTagged::new(id, effect)])
}

impl Builder {
    fn new(params: CFGParameters) -> Builder {
        Builder {
            next: 0,
            nodes: Vec::new(),
            edges: Vec::new(),
            mapping: Vec::new(),
            assoc: Vec::new(),
            ctx: Ctx::new(),
            params,
        }
    }

    // --- core primitives (newNode, link, registerNode, ...) ---

    fn new_node(&mut self, label: CFNode) -> Node {
        let n = self.next;
        self.next += 1;
        self.nodes.push((n, label));
        for c in &self.ctx.token_stack {
            self.assoc.push((*c, n));
        }
        n
    }

    fn new_node_range(&mut self, label: CFNode) -> Range {
        node_to_range(self.new_node(label))
    }

    fn new_structural_node(&mut self) -> Range {
        self.new_node_range(CFNode::CFStructuralNode)
    }

    fn none(&mut self) -> Range {
        self.new_structural_node()
    }

    fn link(&mut self, from: Node, to: Node, label: CFEdge) {
        self.edges.push((from, to, label));
    }

    fn register_node(&mut self, id: Id, r: Range) {
        self.mapping.push((id, (r.0, r.1)));
    }

    fn link_range_as(&mut self, label: CFEdge, a: Range, b: Range) -> Range {
        self.link(a.1, b.0, label);
        Range(a.0, b.1)
    }

    fn link_range(&mut self, a: Range, b: Range) -> Range {
        self.link_range_as(CFEdge::CFEFlow, a, b)
    }

    fn link_ranges(&mut self, ranges: &[Range]) -> Range {
        let mut it = ranges.iter();
        let first = *it.next().expect("Empty range");
        let mut acc = first;
        for r in it {
            acc = self.link_range(acc, *r);
        }
        acc
    }

    fn sequentially(&mut self, list: &[Token]) -> Range {
        let first = self.new_structural_node();
        let mut ranges = vec![first];
        for t in list {
            let r = self.build(t);
            ranges.push(r);
        }
        self.link_ranges(&ranges)
    }

    // --- scoping helpers (local / under / subshell / withFunctionScope) ---

    fn subshell(
        &mut self,
        id: Id,
        reason: &str,
        f: impl FnOnce(&mut Self) -> Range,
    ) -> Range {
        let start = self.new_node(CFNode::CFEntryPoint(format!(
            "Subshell Id {}: {}",
            id.0, reason
        )));
        let end = self.new_node(CFNode::CFStructuralNode);
        let saved_exit = self.ctx.exit_target;
        let saved_ret = self.ctx.return_target;
        self.ctx.exit_target = Some(end);
        self.ctx.return_target = Some(end);
        let middle = f(self);
        self.ctx.exit_target = saved_exit;
        self.ctx.return_target = saved_ret;
        let sr = node_to_range(start);
        let er = node_to_range(end);
        self.link_ranges(&[sr, middle, er]);
        self.new_node_range(CFNode::CFExecuteSubshell(reason.to_string(), start, end))
    }

    fn with_function_scope(&mut self, f: impl FnOnce(&mut Self) -> Range) -> Range {
        let end = self.new_node(CFNode::CFStructuralNode);
        let saved_ret = self.ctx.return_target;
        let saved_fn = self.ctx.is_function;
        self.ctx.return_target = Some(end);
        self.ctx.is_function = true;
        let body = f(self);
        self.ctx.return_target = saved_ret;
        self.ctx.is_function = saved_fn;
        let er = node_to_range(end);
        self.link_ranges(&[body, er])
    }

    fn as_condition(&mut self, f: impl FnOnce(&mut Self) -> Range) -> Range {
        let saved = self.ctx.is_condition;
        self.ctx.is_condition = true;
        let r = f(self);
        self.ctx.is_condition = saved;
        r
    }

    // --- buildRoot / build / build' ---

    fn build_root(&mut self, t: &Token) -> Range {
        self.ctx.token_stack.push(t.id);
        let entry = self.new_node_range(CFNode::CFEntryPoint("MAIN".to_string()));
        let implied_exit = self.new_node(CFNode::CFImpliedExit);
        let end = self.new_node(CFNode::CFStructuralNode);
        let saved_exit = self.ctx.exit_target;
        let saved_ret = self.ctx.return_target;
        self.ctx.exit_target = Some(end);
        self.ctx.return_target = Some(implied_exit);
        let start = self.build(t);
        self.ctx.exit_target = saved_exit;
        self.ctx.return_target = saved_ret;
        let range = self.link_ranges(&[
            entry,
            start,
            node_to_range(implied_exit),
            node_to_range(end),
        ]);
        self.register_node(t.id, range);
        self.ctx.token_stack.pop();
        range
    }

    fn build(&mut self, t: &Token) -> Range {
        self.ctx.token_stack.push(t.id);
        let range = self.build_prime(t);
        self.ctx.token_stack.pop();
        self.register_node(t.id, range);
        range
    }

    fn build_prime(&mut self, t: &Token) -> Range {
        use InnerToken::*;
        let id = t.id;
        match &*t.inner {
            T_Annotation { token, .. } => self.build(token),
            T_Script { commands, .. } => self.sequentially(commands),

            // (( var[x=1] = ... ))
            TA_Assignment { op, lhs, rhs } if matches!(&*lhs.inner, TA_Variable { .. }) => {
                let (name, indices) = match &*lhs.inner {
                    TA_Variable { name, indices } => (name.clone(), indices.clone()),
                    _ => unreachable!(),
                };
                let value = self.build(rhs);
                let subscript = self.sequentially(&indices);
                let read = if op == "=" {
                    self.none()
                } else {
                    self.new_node_range(apply_single(id, CFEffect::CFReadVariable(name.clone())))
                };
                let val = if indices.is_empty() {
                    CFValue::CFValueInteger
                } else {
                    CFValue::CFValueArray
                };
                let write =
                    self.new_node_range(apply_single(id, CFEffect::CFWriteVariable(name, val)));
                self.link_ranges(&[value, subscript, read, write])
            }
            TA_Assignment { lhs, rhs, .. } => {
                self.sequentially(&[lhs.clone(), rhs.clone()])
            }
            TA_Binary { lhs, rhs, .. } => self.sequentially(&[lhs.clone(), rhs.clone()]),
            TA_Expansion(list) => self.sequentially(list),
            TA_Sequence(list) => self.sequentially(list),
            TA_Parenthesis(t2) => self.build(t2),
            TA_Trinary { cond, then, els } => {
                let condition = self.build(cond);
                let ifthen = self.build(then);
                let elsethen = self.build(els);
                let end = self.new_structural_node();
                self.link_ranges(&[condition, ifthen, end]);
                self.link_ranges(&[condition, elsethen, end])
            }
            TA_Variable { name, indices } => {
                let subscript = self.sequentially(indices);
                let hint = if indices.is_empty() {
                    self.none()
                } else {
                    node_to_range(
                        self.new_node(apply_single(id, CFEffect::CFHintArray(name.clone()))),
                    )
                };
                let read = node_to_range(
                    self.new_node(apply_single(id, CFEffect::CFReadVariable(name.clone()))),
                );
                self.link_ranges(&[subscript, hint, read])
            }
            TA_Unary { op, operand }
                if matches!(&*operand.inner, TA_Variable { .. })
                    && (op.contains("--") || op.contains("++")) =>
            {
                let (name, indices) = match &*operand.inner {
                    TA_Variable { name, indices } => (name.clone(), indices.clone()),
                    _ => unreachable!(),
                };
                let subscript = self.sequentially(&indices);
                let read =
                    self.new_node_range(apply_single(id, CFEffect::CFReadVariable(name.clone())));
                let val = if indices.is_empty() {
                    CFValue::CFValueInteger
                } else {
                    CFValue::CFValueArray
                };
                let write =
                    self.new_node_range(apply_single(id, CFEffect::CFWriteVariable(name, val)));
                self.link_ranges(&[subscript, read, write])
            }
            TA_Unary { operand, .. } => self.build(operand),

            TC_And { typ: ConditionType::SingleBracket, lhs, rhs, .. } => {
                self.sequentially(&[lhs.clone(), rhs.clone()])
            }
            TC_And { typ: ConditionType::DoubleBracket, lhs, rhs, .. } => {
                let left = self.build(lhs);
                let right = self.build(rhs);
                let end = self.new_structural_node();
                self.link_ranges(&[left, right, end]);
                self.link_range(left, end)
            }
            TC_Binary { lhs, rhs, .. } => {
                let left = self.build(lhs);
                let right = self.build(rhs);
                self.link_range(left, right)
            }
            TC_Empty { .. } => self.new_structural_node(),
            TC_Group { token, .. } => self.build(token),
            TC_Nullary { token, .. } => self.build(token),
            TC_Or { typ: ConditionType::SingleBracket, lhs, rhs, .. } => {
                self.sequentially(&[lhs.clone(), rhs.clone()])
            }
            TC_Or { typ: ConditionType::DoubleBracket, lhs, rhs, .. } => {
                let left = self.build(lhs);
                let right = self.build(rhs);
                let end = self.new_structural_node();
                self.link_ranges(&[left, right, end]);
                self.link_range(left, end)
            }
            TC_Unary { token, .. } => self.build(token),

            T_Arithmetic(root) => {
                let exe = self.build(root);
                let status = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(exe, status)
            }
            T_AndIf { lhs, rhs } => {
                let left = self.build(lhs);
                let right = self.build(rhs);
                let end = self.new_structural_node();
                self.link_range(left, right);
                self.link_range(right, end);
                self.link_range(left, end)
            }
            T_Array(list) => self.sequentially(list),
            T_Assignment { .. } => self.build_assignment(None, t),
            T_Backgrounded(body) => {
                let start = self.new_structural_node();
                let fork = self.subshell(id, "backgrounding '&'", |b| b.build(body));
                let pid = self.new_node_range(CFNode::CFSetBackgroundPid(id));
                let status = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(start, fork);
                self.link_range_as(CFEdge::CFEFalseFlow, fork, pid);
                self.link_ranges(&[start, pid, status])
            }
            T_Backticked(body) => {
                self.subshell(id, "`..` expansion", |b| b.sequentially(body))
            }
            T_Banged(cmd) => {
                let main = self.build(cmd);
                let status = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(main, status)
            }
            T_BatsTest { body, .. } => {
                let status = self.new_node_range(apply_single(
                    id,
                    CFEffect::CFWriteVariable("status".to_string(), CFValue::CFValueInteger),
                ));
                let output = self.new_node_range(apply_single(
                    id,
                    CFEffect::CFWriteVariable("output".to_string(), CFValue::CFValueString),
                ));
                let main = self.build(body);
                self.link_ranges(&[status, output, main])
            }
            T_BraceExpansion(list) => self.sequentially(list),
            T_BraceGroup(body) => self.sequentially(body),

            T_CaseExpression { word, cases } if cases.is_empty() => self.build(word),
            T_CaseExpression { word, cases } => self.build_case(id, word, cases),

            T_Condition { token, .. } => {
                let cond = self.build(token);
                let status = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(cond, status)
            }
            T_CoProc { name, body } => {
                let maybe_name = match name {
                    Some(x) => get_literal_string(x),
                    None => Some("COPROC".to_string()),
                };
                let parent_node = match &maybe_name {
                    Some(s) => apply_single(
                        id,
                        CFEffect::CFWriteVariable(s.clone(), CFValue::CFValueArray),
                    ),
                    None => CFNode::CFStructuralNode,
                };
                let start = self.new_structural_node();
                let parent = self.new_node_range(parent_node);
                let child = self.subshell(id, "coproc", |b| b.build(body));
                let end = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(start, parent);
                self.link_range(start, child);
                self.link_range(parent, end);
                self.link_range_as(CFEdge::CFEFalseFlow, child, end);
                Range(start.0, end.1)
            }
            T_CoProcBody(t2) => self.build(t2),

            T_DollarArithmetic(arith) => self.build(arith),
            T_DollarDoubleQuoted(list) => self.sequentially(list),
            T_DollarSingleQuoted(_) => self.none(),
            T_DollarBracket(t2) => self.build(t2),
            T_DollarBraced { op, .. } => self.build_dollar_braced(id, op),
            T_DollarBraceCommandExpansion { list, .. } => self.sequentially(list),
            T_DoubleQuoted(list) => self.sequentially(list),
            T_DollarExpansion(body) => {
                self.subshell(id, "$(..) expansion", |b| b.sequentially(body))
            }
            T_Extglob { list, .. } => self.sequentially(list),

            T_FdRedirect { fd, target } if fd.starts_with('{') => {
                let name: String = fd[1..].chars().take_while(|c| *c != '}').collect();
                let expression = self.build(target);
                let effect = if is_closing_file_op(target) {
                    apply_single(id, CFEffect::CFReadVariable(name))
                } else {
                    apply_single(
                        id,
                        CFEffect::CFWriteVariable(name, CFValue::CFValueInteger),
                    )
                };
                let rw = self.new_node_range(effect);
                self.link_range(expression, rw)
            }
            T_FdRedirect { target, .. } => self.build(target),

            T_ForArithmetic { init, cond, step, body } => {
                let init_r = self.build(init);
                let cond_r = self.build(cond);
                let body_r = self.sequentially(body);
                let inc_r = self.build(step);
                let end = self.new_structural_node();
                self.link_ranges(&[init_r, cond_r, body_r, inc_r]);
                self.link_range(cond_r, end);
                self.link_range(inc_r, cond_r);
                Range(init_r.0, end.1)
            }
            T_ForIn { var, items, body } => self.for_in_helper(id, var, items, body),

            T_Function { name, body, .. } => {
                let saved_exit = self.ctx.exit_target;
                self.ctx.exit_target = None;
                let entry = self.new_node_range(CFNode::CFEntryPoint(format!("function {}", name)));
                let f = self.with_function_scope(|b| b.build(body));
                let range = self.link_range(entry, f);
                self.ctx.exit_target = saved_exit;
                let (entry_n, exit_n) = (range.0, range.1);
                let definition = self.new_node_range(apply_single(
                    id,
                    CFEffect::CFDefineFunction(name.clone(), id, entry_n, exit_n),
                ));
                let exe = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(definition, exe)
            }

            T_Glob(_) => self.none(),
            T_HereString(t2) => self.build(t2),
            T_HereDoc { body, .. } => self.sequentially(body),

            T_IfExpression { clauses, elses } => self.build_if(id, clauses, elses),
            T_Include(t2) => self.build(t2),
            T_IndexedElement { indices, value } => {
                let indices_r = self.sequentially(indices);
                let value_r = self.build(value);
                self.link_range(indices_r, value_r)
            }
            T_IoDuplicate { op, .. } => self.build(op),
            T_IoFile { op, file } => {
                let exp = self.build(file);
                let doesnt_do_much = self.build(op);
                self.link_range(exp, doesnt_do_much)
            }
            T_Literal(_) => self.none(),
            T_NormalWord(list) => self.sequentially(list),
            T_OrIf { lhs, rhs } => {
                let left = self.build(lhs);
                let right = self.build(rhs);
                let end = self.new_structural_node();
                self.link_range(left, right);
                self.link_range(right, end);
                self.link_range(left, end)
            }

            T_Pipeline { commands, .. } if commands.len() == 1 => self.build(&commands[0]),
            T_Pipeline { commands, .. } => self.build_pipeline(id, commands),

            T_ProcSub { op, list } => {
                let start = self.new_structural_node();
                let reason = format!("{}() process substitution", op);
                let body = self.subshell(id, &reason, |b| b.sequentially(list));
                let end = self.new_structural_node();
                self.link_range(start, body);
                self.link_range_as(CFEdge::CFEFalseFlow, body, end);
                self.link_range(start, end)
            }
            T_Redirecting { redirs, cmd } => {
                let redir = self.sequentially(redirs);
                let body = self.build(cmd);
                self.link_range(redir, body)
            }
            T_SelectIn { var, items, body } => self.for_in_helper(id, var, items, body),

            T_SimpleCommand { assignments, words } if words.is_empty() => {
                let assigns = self.sequentially(assignments);
                let status = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(assigns, status)
            }
            T_SimpleCommand { assignments, words } => {
                let literal = get_unquoted_literal(&words[0]);
                self.handle_command(id, assignments, words, literal)
            }

            T_SingleQuoted(_) => self.none(),
            T_SourceCommand { includer, included } => {
                let cmd = self.build(includer);
                let end = self.new_structural_node();
                let _ = end; // withReturn end is a no-op in CFG.hs
                let inline = self.build(included);
                self.link_range(cmd, inline);
                self.link_range(inline, end);
                Range(cmd.0, inline.1)
            }
            T_Subshell(body) => {
                let main = self.subshell(id, "explicit (..) subshell", |b| b.sequentially(body));
                let status = self.new_node_range(CFNode::CFSetExitCode(id));
                self.link_range(main, status)
            }
            T_UntilExpression { condition, body } => self.while_helper(id, condition, body),
            T_WhileExpression { condition, body } => self.while_helper(id, condition, body),

            T_CLOBBER
            | T_GREATAND
            | T_LESSAND
            | T_LESSGREAT
            | T_DGREAT
            | T_Greater
            | T_Less
            | T_ParamSubSpecialChar(_) => self.none(),

            // Everything else: the Haskell `error` line is stripped in release
            // builds, falling through to `none`.
            _ => self.none(),
        }
    }

    // --- compound builders ---

    fn build_dollar_braced(&mut self, id: Id, op: &Token) -> Range {
        let str = oversimplify_concat(op);
        let modifier = get_braced_modifier(&str);
        let reference = get_braced_reference(&str);
        let indices = get_index_references(&str);
        let offsets = get_offset_references(&str);
        let vals = self.build(op);
        let mut deps_list = vec![vals];
        for x in indices.iter().chain(offsets.iter()) {
            let r = node_to_range(
                self.new_node(apply_single(id, CFEffect::CFReadVariable(x.clone()))),
            );
            deps_list.push(r);
        }
        let deps = self.link_ranges(&deps_list);
        let read = node_to_range(
            self.new_node(apply_single(id, CFEffect::CFReadVariable(reference.clone()))),
        );
        let total_read = self.link_range(deps, read);
        if modifier.starts_with('=') || modifier.starts_with(":=") {
            let optional_assign = self.new_node_range(apply_single(
                id,
                CFEffect::CFWriteVariable(reference, CFValue::CFValueString),
            ));
            let result = self.new_structural_node();
            self.link_range(optional_assign, result);
            self.link_range(total_read, result)
        } else {
            total_read
        }
    }

    fn build_if(&mut self, id: Id, clauses: &[IfClause], elses: &[Token]) -> Range {
        let start = self.new_structural_node();
        // doBranches: fold over clauses, chaining conds; accumulate action ranges.
        let mut result: Vec<Range> = Vec::new();
        let mut cursor = start;
        for (conds, thens) in clauses {
            let cond = self.as_condition(|b| b.sequentially(conds));
            let action = self.sequentially(thens);
            self.link_range(cursor, cond);
            self.link_range(cond, action);
            result.push(action);
            cursor = cond;
        }
        // final else / implicit exit code
        let rest = if elses.is_empty() {
            self.new_node_range(CFNode::CFSetExitCode(id))
        } else {
            self.sequentially(elses)
        };
        self.link_range(cursor, rest);
        result.push(rest);
        let end = self.new_structural_node();
        for r in &result {
            self.link_range(*r, end);
        }
        Range(start.0, end.1)
    }

    fn build_pipeline(&mut self, id: Id, cmds: &[Token]) -> Range {
        let start = self.new_structural_node();
        let has_lastpipe = self.params.cf_lastpipe;
        let (leading, last) = self.build_pipe(id, has_lastpipe, cmds);
        let end = self.new_node_range(CFNode::CFSetExitCode(id));
        for c in &leading {
            self.link_range(start, *c);
        }
        for c in &leading {
            self.link_range_as(CFEdge::CFEFalseFlow, *c, end);
        }
        let mut chain = vec![start];
        chain.extend(last.iter().copied());
        chain.push(end);
        self.link_ranges(&chain)
    }

    fn build_pipe(&mut self, id: Id, lp: bool, cmds: &[Token]) -> (Vec<Range>, Vec<Range>) {
        if lp && cmds.len() == 1 {
            let last = self.build(&cmds[0]);
            return (Vec::new(), vec![last]);
        }
        if cmds.is_empty() {
            return (Vec::new(), Vec::new());
        }
        let this = self.subshell(id, "pipeline", |b| b.build(&cmds[0]));
        let (mut leading, last) = self.build_pipe(id, lp, &cmds[1..]);
        let mut result = vec![this];
        result.append(&mut leading);
        (result, last)
    }

    fn build_case(&mut self, _id: Id, word: &Token, cases: &[CaseClause]) -> Range {
        let start = self.new_structural_node();
        let token = self.build(word);
        // Build each branch: (typ, cond_range, body_range)
        let mut branches: Vec<(CaseType, Range, Range)> = Vec::new();
        for (typ, conds, body) in cases {
            let c = self.build_case_cond(conds);
            let b = self.sequentially(body);
            self.link_range(c, b);
            branches.push((*typ, c, b));
        }
        let end = self.new_structural_node();

        let first_cond = branches[0].1;
        let last_body = branches[branches.len() - 1].2;

        self.link_range(start, token);
        self.link_range(token, first_cond);

        // neighbors: zip branches (tail branches)
        for i in 0..branches.len() - 1 {
            let (typ, _cond, body) = branches[i];
            let (_, next_cond, next_body) = branches[i + 1];
            // Failure case
            self.link_range(_cond, next_cond);
            // After body
            match typ {
                CaseType::CaseBreak => {
                    self.link_range(body, end);
                }
                CaseType::CaseFallThrough => {
                    self.link_range(body, next_body);
                }
                CaseType::CaseContinue => {
                    self.link_range(body, next_cond);
                }
            }
        }
        self.link_range(last_body, end);

        if !cases.iter().any(|(_, conds, _)| has_catch_all(conds)) {
            self.link_range(token, end);
        }
        Range(start.0, end.1)
    }

    // for `a | b | c`, evaluate each in turn and allow short circuiting
    fn build_case_cond(&mut self, list: &[Token]) -> Range {
        let start = self.new_structural_node();
        let mut conds = Vec::new();
        for t in list {
            let r = self.build(t);
            conds.push(r);
        }
        let end = self.new_structural_node();
        let mut chain = vec![start];
        chain.extend(conds.iter().copied());
        self.link_ranges(&chain);
        for c in &conds {
            self.link_range(*c, end);
        }
        Range(start.0, end.1)
    }

    fn for_in_helper(&mut self, id: Id, name: &str, words: &[Token], body: &[Token]) -> Range {
        let entry = self.new_structural_node();
        let expansion = self.sequentially(words);
        let assignment_choice = self.new_structural_node();
        let assignments: Vec<Range> = if words.is_empty() || words.iter().any(will_split) {
            vec![self.new_node_range(apply_single(
                id,
                CFEffect::CFWriteVariable(name.to_string(), CFValue::CFValueString),
            ))]
        } else {
            words
                .iter()
                .map(|t| {
                    let parts = token_to_parts(t);
                    self.new_node_range(apply_single(
                        id,
                        CFEffect::CFWriteVariable(
                            name.to_string(),
                            CFValue::CFValueComputed(t.id, parts),
                        ),
                    ))
                })
                .collect()
        };
        let body_r = self.sequentially(body);
        let exit = self.new_structural_node();
        self.link_ranges(&[entry, expansion, assignment_choice]);
        for a in &assignments {
            self.link_ranges(&[assignment_choice, *a, body_r]);
        }
        self.link_range(body_r, exit);
        self.link_range(expansion, exit);
        self.link_range(body_r, assignment_choice);
        Range(entry.0, exit.1)
    }

    fn while_helper(&mut self, id: Id, cond: &[Token], body: &[Token]) -> Range {
        let cond_range = self.as_condition(|b| b.sequentially(cond));
        let body_range = self.sequentially(body);
        let end = self.new_node_range(CFNode::CFSetExitCode(id));
        self.link_range(cond_range, body_range);
        self.link_range(body_range, cond_range);
        self.link_range(cond_range, end)
    }

    // --- assignments ---

    fn build_assignment(&mut self, scope: Option<Scope>, t: &Token) -> Range {
        let op = match &*t.inner {
            InnerToken::T_Assignment { mode, var, indices, value } => {
                let expand = self.build(value);
                let index = self.sequentially(indices);
                let read = match mode {
                    AssignmentMode::Append => self.new_node_range(apply_single(
                        t.id,
                        CFEffect::CFReadVariable(var.clone()),
                    )),
                    AssignmentMode::Assign => self.none(),
                };
                let value_type = if indices.is_empty() {
                    assignment_value(t.id, *mode, var, value)
                } else {
                    CFValue::CFValueArray
                };
                let effect = match scope {
                    Some(Scope::PrefixScope) => CFEffect::CFWritePrefix(var.clone(), value_type),
                    Some(Scope::LocalScope) => CFEffect::CFWriteLocal(var.clone(), value_type),
                    Some(Scope::GlobalScope) => CFEffect::CFWriteGlobal(var.clone(), value_type),
                    None => CFEffect::CFWriteVariable(var.clone(), value_type),
                };
                let write = self.new_node_range(apply_single(t.id, effect));
                self.link_ranges(&[expand, index, read, write])
            }
            _ => self.none(),
        };
        self.register_node(t.id, op);
        op
    }

    // --- command dispatch (handleCommand) ---

    fn handle_command(
        &mut self,
        cmd_id: Id,
        vars: &[Token],
        words: &[Token],
        literal_cmd: Option<String>,
    ) -> Range {
        match literal_cmd.as_deref() {
            Some("exit") => self.regular_expansion(vars, words, |b| b.handle_exit()),
            Some("return") => self.regular_expansion(vars, words, |b| b.handle_return()),
            Some("unset") => {
                self.regular_expansion_with_status(vars, words, |b| b.handle_unset(words))
            }
            Some("declare") | Some("local") | Some("typeset") => self.handle_declare(words),
            Some("printf") => {
                self.regular_expansion_with_status(vars, words, |b| b.handle_printf(words))
            }
            Some("wait") => {
                self.regular_expansion_with_status(vars, words, |b| b.handle_wait(words))
            }
            Some("mapfile") | Some("readarray") => {
                self.regular_expansion_with_status(vars, words, |b| b.handle_mapfile(words))
            }
            Some("read") => {
                self.regular_expansion_with_status(vars, words, |b| b.handle_read(words))
            }
            Some("DEFINE_boolean") | Some("DEFINE_float") | Some("DEFINE_integer")
            | Some("DEFINE_string") => {
                self.regular_expansion_with_status(vars, words, |b| b.handle_define(words))
            }
            Some("builtin") => {
                if words.len() <= 1 {
                    self.handle_others(cmd_id, vars, words, literal_cmd)
                } else {
                    let lit = get_literal_string(&words[1]);
                    self.handle_command(words[1].id, vars, &words[1..], lit)
                }
            }
            Some("command") => {
                if words.len() <= 1 {
                    self.handle_others(cmd_id, vars, words, literal_cmd)
                } else {
                    let lit = get_literal_string(&words[1]);
                    self.handle_others(words[1].id, vars, &words[1..], lit)
                }
            }
            _ => self.handle_others(cmd_id, vars, words, literal_cmd),
        }
    }

    fn handle_others(
        &mut self,
        id: Id,
        vars: &[Token],
        args: &[Token],
        cmd: Option<String>,
    ) -> Range {
        self.regular_expansion(vars, args, |b| {
            let exe = b.new_node_range(CFNode::CFExecuteCommand(cmd));
            let status = b.new_node_range(CFNode::CFSetExitCode(id));
            b.link_range(exe, status)
        })
    }

    fn regular_expansion(
        &mut self,
        vars: &[Token],
        args: &[Token],
        p: impl FnOnce(&mut Self) -> Range,
    ) -> Range {
        let args_r = self.sequentially(args);
        let mut ranges = vec![args_r];
        for v in vars {
            let a = self.build_assignment(Some(Scope::PrefixScope), v);
            ranges.push(a);
        }
        let exe = p(self);
        ranges.push(exe);
        if !vars.is_empty() {
            let drop = self.new_node_range(CFNode::CFDropPrefixAssignments);
            ranges.push(drop);
        }
        self.link_ranges(&ranges)
    }

    fn regular_expansion_with_status(
        &mut self,
        vars: &[Token],
        args: &[Token],
        p: impl FnOnce(&mut Self) -> Range,
    ) -> Range {
        let cmd_id = args[0].id;
        let initial = self.regular_expansion(vars, args, p);
        let status = self.new_node_range(CFNode::CFSetExitCode(cmd_id));
        self.link_range(initial, status)
    }

    fn handle_exit(&mut self) -> Range {
        match self.ctx.exit_target {
            Some(target) => {
                let exit = self.new_node(CFNode::CFResolvedExit);
                self.link(exit, target, CFEdge::CFEExit);
                let unreachable = self.new_node(CFNode::CFUnreachable);
                Range(exit, unreachable)
            }
            None => {
                let exit = self.new_node(CFNode::CFUnresolvedExit);
                let unreachable = self.new_node(CFNode::CFUnreachable);
                Range(exit, unreachable)
            }
        }
    }

    fn handle_return(&mut self) -> Range {
        match self.ctx.return_target {
            None => panic!("ShellCheck internal error: missing return target"),
            Some(target) => {
                let ret = self.new_node(CFNode::CFStructuralNode);
                self.link(ret, target, CFEdge::CFEFlow);
                let unreachable = self.new_node(CFNode::CFUnreachable);
                Range(ret, unreachable)
            }
        }
    }

    fn handle_unset(&mut self, words: &[Token]) -> Range {
        let args = &words[1..];
        // pairs :: [(flagString, token)]
        let pairs: Vec<(String, Token)> = match get_gnu_opts("vfn", args) {
            Some(flags) => flags
                .into_iter()
                .map(|(s, (flag, _val))| (s, flag))
                .collect(),
            None => args.iter().map(|c| (String::new(), c.clone())).collect(),
        };
        let names: Vec<&(String, Token)> = pairs.iter().filter(|(s, _)| s.is_empty()).collect();
        let flag_names: Vec<&String> =
            pairs.iter().filter(|(s, _)| !s.is_empty()).map(|(s, _)| s).collect();
        let literal_names: Vec<(Token, String)> = names
            .iter()
            .filter_map(|(_, t)| get_literal_string(t).map(|s| (t.clone(), s)))
            .collect();

        let ctor: fn(String) -> CFEffect = if flag_names.iter().any(|s| *s == "n") {
            CFEffect::CFUndefineNameref
        } else if flag_names.iter().any(|s| *s == "v") {
            CFEffect::CFUndefineVariable
        } else if flag_names.iter().any(|s| *s == "f") {
            CFEffect::CFUndefineFunction
        } else {
            CFEffect::CFUndefine
        };
        let effects: Vec<IdTagged<CFEffect>> = literal_names
            .into_iter()
            .map(|(token, name)| IdTagged::new(token.id, ctor(name)))
            .collect();
        self.new_node_range(CFNode::CFApplyEffects(effects))
    }

    fn handle_declare(&mut self, words: &[Token]) -> Range {
        let cmd = &words[0];
        let args = &words[1..];
        let is_func = self.ctx.is_function;

        let opts: Vec<String> = get_generic_opts(args).into_iter().map(|(s, _)| s).collect();
        let associative = opts.iter().any(|s| s == "A");
        let array = opts.iter().any(|s| s == "a") || associative;
        let integer = opts.iter().any(|s| s == "i");
        let global = opts.iter().any(|s| s == "g");
        let export = opts.iter().any(|s| s == "x");

        let mut added_props: BTreeSet<CFVariableProp> = BTreeSet::new();
        if array {
            added_props.insert(CFVariableProp::CFVPArray);
        }
        if integer {
            added_props.insert(CFVariableProp::CFVPInteger);
        }
        if export {
            added_props.insert(CFVariableProp::CFVPExport);
        }
        if associative {
            added_props.insert(CFVariableProp::CFVPAssociative);
        }

        // find "ia" from `declare +i +a`
        let unset_options: String = args
            .iter()
            .filter_map(get_literal_string)
            .filter(|s| s.starts_with('+'))
            .flat_map(|s| s.chars().skip(1).collect::<Vec<_>>())
            .collect();
        let mut removed_props: BTreeSet<CFVariableProp> = BTreeSet::new();
        if unset_options.contains('i') {
            removed_props.insert(CFVariableProp::CFVPInteger);
        }
        if unset_options.contains('e') {
            removed_props.insert(CFVariableProp::CFVPExport);
        }

        let writer = |global: bool, is_func: bool| -> fn(String, CFValue) -> CFEffect {
            if global {
                CFEffect::CFWriteGlobal
            } else if is_func {
                CFEffect::CFWriteLocal
            } else {
                CFEffect::CFWriteVariable
            }
        };
        let scope = |global: bool, is_func: bool| -> Option<Scope> {
            if global {
                Some(Scope::GlobalScope)
            } else if is_func {
                Some(Scope::LocalScope)
            } else {
                None
            }
        };
        let w = writer(global, is_func);
        let sc = scope(global, is_func);

        // mconcat of per-arg (evaluated, assignments, added, removed)
        let mut evaluated: Vec<Token> = Vec::new();
        let mut assignments: Vec<IdTagged<CFEffect>> = Vec::new();
        let mut added: Vec<IdTagged<CFEffect>> = Vec::new();
        let mut removed: Vec<IdTagged<CFEffect>> = Vec::new();

        for a in args {
            match &*a.inner {
                InnerToken::T_Assignment { mode, var, indices, value } => {
                    evaluated.extend(indices.iter().cloned());
                    evaluated.push(value.clone());
                    let mut parts: Vec<CFStringPart> = Vec::new();
                    if *mode == AssignmentMode::Append {
                        parts.push(CFStringPart::CFStringVariable(var.clone()));
                    }
                    parts.extend(token_to_parts(value));
                    assignments.push(IdTagged::new(
                        a.id,
                        w(var.clone(), CFValue::CFValueComputed(value.id, parts)),
                    ));
                    if !added_props.is_empty() {
                        added.push(IdTagged::new(
                            a.id,
                            CFEffect::CFSetProps(sc, var.clone(), added_props.clone()),
                        ));
                    }
                    if !removed_props.is_empty() {
                        // NB: CFG.hs passes addedProps here (guarded by removedProps).
                        removed.push(IdTagged::new(
                            a.id,
                            CFEffect::CFUnsetProps(sc, var.clone(), added_props.clone()),
                        ));
                    }
                }
                _ => {
                    let literal = get_literal_string_def(a, "\0");
                    let is_known = !literal.contains('\0');
                    let m = var_assign_match(&literal);
                    let name = m.clone().unwrap_or_else(|| literal.clone());
                    evaluated.push(a.clone());
                    if !is_variable_name(&name) {
                        // (pre, [], [], [])
                    } else if m.is_some() && is_known {
                        let after_eq: String = {
                            let rest: String =
                                literal.chars().skip_while(|c| *c != '=').collect();
                            rest.chars().skip(1).collect()
                        };
                        assignments.push(IdTagged::new(
                            a.id,
                            w(
                                name.clone(),
                                CFValue::CFValueComputed(
                                    a.id,
                                    vec![CFStringPart::CFStringLiteral(after_eq)],
                                ),
                            ),
                        ));
                        added.push(IdTagged::new(
                            a.id,
                            CFEffect::CFSetProps(sc, name.clone(), added_props.clone()),
                        ));
                        removed.push(IdTagged::new(
                            a.id,
                            CFEffect::CFUnsetProps(sc, name.clone(), removed_props.clone()),
                        ));
                    } else if m.is_some() {
                        assignments
                            .push(IdTagged::new(a.id, w(name.clone(), CFValue::CFValueString)));
                        added.push(IdTagged::new(
                            a.id,
                            CFEffect::CFSetProps(sc, name.clone(), added_props.clone()),
                        ));
                        removed.push(IdTagged::new(
                            a.id,
                            CFEffect::CFUnsetProps(sc, name.clone(), removed_props.clone()),
                        ));
                    } else {
                        // e.g. declare -i x
                        added.push(IdTagged::new(
                            a.id,
                            CFEffect::CFSetProps(sc, name.clone(), added_props.clone()),
                        ));
                        removed.push(IdTagged::new(
                            a.id,
                            CFEffect::CFUnsetProps(sc, name.clone(), removed_props.clone()),
                        ));
                    }
                }
            }
        }

        let before = self.sequentially(&evaluated);
        let assignments_r = self.new_node_range(CFNode::CFApplyEffects(assignments));
        let added_r = if added.is_empty() {
            self.new_structural_node()
        } else {
            self.new_node_range(CFNode::CFApplyEffects(added))
        };
        let removed_r = if removed.is_empty() {
            self.new_structural_node()
        } else {
            self.new_node_range(CFNode::CFApplyEffects(removed))
        };
        let result = self.new_node_range(CFNode::CFSetExitCode(cmd.id));
        self.link_ranges(&[before, assignments_r, added_r, removed_r, result])
    }

    fn handle_printf(&mut self, words: &[Token]) -> Range {
        let args = &words[1..];
        let find_var = (|| {
            let flags = get_bsd_opts("v:", args)?;
            let (_flag, arg) = lookup("v", &flags)?;
            let name = get_literal_string(&arg)?;
            Some(IdTagged::new(
                arg.id,
                CFEffect::CFWriteVariable(name, CFValue::CFValueString),
            ))
        })();
        self.new_node_range(CFNode::CFApplyEffects(find_var.into_iter().collect()))
    }

    fn handle_wait(&mut self, words: &[Token]) -> Range {
        let args = &words[1..];
        let flags = get_generic_opts(args);
        let find_var = (|| {
            let (_flag, arg) = lookup("p", &flags)?;
            let name = get_literal_string(&arg)?;
            Some(IdTagged::new(
                arg.id,
                CFEffect::CFWriteVariable(name, CFValue::CFValueInteger),
            ))
        })();
        self.new_node_range(CFNode::CFApplyEffects(find_var.into_iter().collect()))
    }

    fn handle_mapfile(&mut self, words: &[Token]) -> Range {
        let cmd = &words[0];
        let args = &words[1..];
        let get_from_arg = || -> Option<(Id, String)> {
            let flags = get_gnu_opts(FLAGS_FOR_MAPFILE, args)?;
            let (_, arg) = lookup("", &flags)?;
            let name = get_literal_string(&arg)?;
            Some((arg.id, name))
        };
        let get_from_fallback = || -> Option<(Id, String)> {
            args.iter().rev().find_map(|c| {
                let name = get_literal_string(c)?;
                if is_variable_name(&name) {
                    Some((c.id, name))
                } else {
                    None
                }
            })
        };
        let (id, name) =
            get_from_arg().or_else(get_from_fallback).unwrap_or((cmd.id, "MAPFILE".to_string()));
        let effect = IdTagged::new(id, CFEffect::CFWriteVariable(name, CFValue::CFValueArray));
        self.new_node_range(CFNode::CFApplyEffects(vec![effect]))
    }

    fn handle_read(&mut self, words: &[Token]) -> Range {
        let cmd = &words[0];
        let args = &words[1..];

        let with_array = |flags: &[(String, (Token, Token))]| -> Option<Vec<IdTagged<CFEffect>>> {
            let (_, token) = lookup("a", flags)?;
            Some(match get_literal_string(&token) {
                Some(name) => vec![IdTagged::new(
                    token.id,
                    CFEffect::CFWriteVariable(name, CFValue::CFValueArray),
                )],
                None => Vec::new(),
            })
        };
        let with_fields = |flags: &[(String, (Token, Token))]| -> Vec<IdTagged<CFEffect>> {
            flags
                .iter()
                .filter_map(|(s, (t, _))| {
                    if !s.is_empty() {
                        return None;
                    }
                    let name = get_literal_string(t)?;
                    Some(IdTagged::new(
                        t.id,
                        CFEffect::CFWriteVariable(name, CFValue::CFValueString),
                    ))
                })
                .collect()
        };

        let main: Vec<IdTagged<CFEffect>> = match get_gnu_opts(FLAGS_FOR_READ, args) {
            Some(flags) => with_array(&flags).unwrap_or_else(|| with_fields(&flags)),
            None => {
                // fallback: trailing run of literal args (or REPLY)
                let mut names: Vec<(Id, String)> = Vec::new();
                for c in args.iter().rev() {
                    match get_literal_string(c) {
                        Some(s) => names.push((c.id, s)),
                        None => break,
                    }
                }
                names.reverse();
                let names_or_default = if names.is_empty() {
                    vec![(cmd.id, "REPLY".to_string())]
                } else {
                    names
                };
                let has_dash_a = get_generic_opts(args).iter().any(|(s, _)| s == "a");
                let value = if has_dash_a {
                    CFValue::CFValueArray
                } else {
                    CFValue::CFValueString
                };
                names_or_default
                    .into_iter()
                    .map(|(id, name)| {
                        IdTagged::new(id, CFEffect::CFWriteVariable(name, value.clone()))
                    })
                    .collect()
            }
        };
        self.new_node_range(CFNode::CFApplyEffects(main))
    }

    fn handle_define(&mut self, words: &[Token]) -> Range {
        let args = &words[1..];
        let find_var = (|| {
            let name = args.get(1)?;
            let str = get_literal_string(name)?;
            if !is_variable_name(&str) {
                return None;
            }
            Some(IdTagged::new(
                name.id,
                CFEffect::CFWriteVariable(str, CFValue::CFValueString),
            ))
        })();
        self.new_node_range(CFNode::CFApplyEffects(find_var.into_iter().collect()))
    }
}

// ===========================================================================
// buildGraph
// ===========================================================================

/// `buildGraph :: CFGParameters -> Token -> CFGResult`.
pub fn build_graph(params: CFGParameters, root: &Token) -> CFGResult {
    let mut builder = Builder::new(params);
    builder.build_root(root);
    let base: CFW = (builder.nodes, builder.edges, builder.mapping, builder.assoc);

    // renumberTopologically is commented out in CFG.hs; keep the same.
    let (nodes, edges, mapping, association) = remove_unnecessary_structural_nodes(base);

    let id_to_range: HashMap<Id, (Node, Node)> = {
        let mut m = HashMap::new();
        for (id, r) in &mapping {
            m.insert(*id, *r); // last write wins, like Data.Map.fromList
        }
        m
    };

    let only_real_edges: Vec<(Node, Node, CFEdge)> = edges
        .iter()
        .copied()
        .filter(|(_, _, e)| matches!(e, CFEdge::CFEFlow | CFEdge::CFEExit))
        .collect();

    let (_, main_exit) = *id_to_range.get(&root.id).expect("root range missing");

    let mut id_to_nodes: HashMap<Id, BTreeSet<Node>> = HashMap::new();
    for (id, n) in &association {
        id_to_nodes.entry(*id).or_default().insert(*n);
    }

    let post_dominators =
        find_post_dominators(main_exit, &nodes, &only_real_edges);

    CFGResult {
        cf_graph: CFGraph::mk_graph(nodes, edges),
        cf_id_to_range: id_to_range,
        cf_id_to_nodes: id_to_nodes,
        cf_post_dominators: post_dominators,
    }
}

// ===========================================================================
// Graph transforms on CFW (renumber / removeUnnecessaryStructuralNodes)
// ===========================================================================

fn remap_helper(m: &HashMap<Node, Node>, n: Node) -> Node {
    *m.get(&n).unwrap_or(&n)
}

fn remap_effect(m: &HashMap<Node, Node>, e: &IdTagged<CFEffect>) -> IdTagged<CFEffect> {
    match &e.value {
        CFEffect::CFDefineFunction(name, fid, start, end) => IdTagged::new(
            e.id,
            CFEffect::CFDefineFunction(
                name.clone(),
                *fid,
                remap_helper(m, *start),
                remap_helper(m, *end),
            ),
        ),
        _ => e.clone(),
    }
}

fn remap_node(m: &HashMap<Node, Node>, (node, label): &(Node, CFNode)) -> (Node, CFNode) {
    let new_label = match label {
        CFNode::CFApplyEffects(effects) => {
            CFNode::CFApplyEffects(effects.iter().map(|e| remap_effect(m, e)).collect())
        }
        CFNode::CFExecuteSubshell(s, a, b) => {
            CFNode::CFExecuteSubshell(s.clone(), remap_helper(m, *a), remap_helper(m, *b))
        }
        other => other.clone(),
    };
    (remap_helper(m, *node), new_label)
}

fn remap_edge(m: &HashMap<Node, Node>, (from, to, label): &(Node, Node, CFEdge)) -> (Node, Node, CFEdge) {
    (remap_helper(m, *from), remap_helper(m, *to), *label)
}

fn remap_graph(remap: &HashMap<Node, Node>, g: CFW) -> CFW {
    let (nodes, edges, mapping, assoc) = g;
    (
        nodes.iter().map(|n| remap_node(remap, n)).collect(),
        edges.iter().map(|e| remap_edge(remap, e)).collect(),
        mapping
            .iter()
            .map(|(id, (a, b))| (*id, (remap_helper(remap, *a), remap_helper(remap, *b))))
            .collect(),
        assoc.iter().map(|(id, n)| (*id, remap_helper(remap, *n))).collect(),
    )
}

/// Renumber the graph so there are no gaps in node numbers.
pub fn renumber_graph(g: CFW) -> CFW {
    let mut ids: Vec<Node> = g.0.iter().map(|(n, _)| *n).collect();
    ids.sort_unstable();
    let renumbering: HashMap<Node, Node> =
        ids.into_iter().enumerate().map(|(i, n)| (n, i)).collect();
    remap_graph(&renumbering, g)
}

/// Renumber the graph in topological order.
pub fn renumber_topologically(g: CFW) -> CFW {
    let order = topsort(&g.0, &g.1);
    let renumbering: HashMap<Node, Node> =
        order.into_iter().enumerate().map(|(i, n)| (n, i)).collect();
    remap_graph(&renumbering, g)
}

/// Collapse structural nodes that just form long chains like x->x->x.
pub fn remove_unnecessary_structural_nodes(g: CFW) -> CFW {
    let (nodes, edges, mapping, association) = g;

    let is_regular_edge = |e: &(Node, Node, CFEdge)| matches!(e.2, CFEdge::CFEFlow);
    let regular_edges: Vec<(Node, Node, CFEdge)> =
        edges.iter().copied().filter(is_regular_edge).collect();

    // NB: names mirror CFG.hs (swapped in the original).
    let mut in_degree: HashMap<Node, usize> = HashMap::new();
    let mut out_degree: HashMap<Node, usize> = HashMap::new();
    for (from, to, _) in &regular_edges {
        *in_degree.entry(*from).or_insert(0) += 1;
        *out_degree.entry(*to).or_insert(0) += 1;
    }
    let is_linear = |node: Node| {
        *in_degree.get(&node).unwrap_or(&0) == 1 && *out_degree.get(&node).unwrap_or(&0) == 1
    };

    let structural_nodes: HashSet<Node> = nodes
        .iter()
        .filter(|(_, l)| *l == CFNode::CFStructuralNode)
        .map(|(n, _)| *n)
        .collect();
    let candidate_nodes: HashSet<Node> =
        structural_nodes.iter().copied().filter(|n| is_linear(*n)).collect();

    // edgesToCollapse = Set of regular edges with both endpoints candidates.
    let mut edges_to_collapse: Vec<(Node, Node, CFEdge)> = regular_edges
        .iter()
        .copied()
        .filter(|(a, b, _)| candidate_nodes.contains(a) && candidate_nodes.contains(b))
        .collect();
    // Emulate S.fromList: dedup + sorted order (affects fromList "last wins").
    edges_to_collapse.sort_by(|x, y| (x.0, x.1, x.2).cmp(&(y.0, y.1, y.2)));
    edges_to_collapse.dedup();
    let edges_to_collapse_set: HashSet<(Node, Node, CFEdge)> =
        edges_to_collapse.iter().copied().collect();

    // remapping = fromList (map orderEdge edgesToCollapse): larger -> smaller.
    let mut remapping: HashMap<Node, Node> = HashMap::new();
    for (a, b, _) in &edges_to_collapse {
        let (k, v) = if a < b { (*b, *a) } else { (*a, *b) };
        remapping.insert(k, v); // last wins, matching sorted fromList
    }

    fn recursive_lookup(map: &HashMap<Node, Node>, mut node: Node) -> Node {
        while let Some(&x) = map.get(&node) {
            if x == node {
                break;
            }
            node = x;
        }
        node
    }
    let recursive_remapping: HashMap<Node, Node> = remapping
        .keys()
        .map(|c| (*c, recursive_lookup(&remapping, *c)))
        .collect();

    let filtered_nodes: Vec<(Node, CFNode)> = nodes
        .into_iter()
        .filter(|(n, _)| !recursive_remapping.contains_key(n))
        .collect();
    let filtered_edges: Vec<(Node, Node, CFEdge)> = edges
        .into_iter()
        .filter(|e| !edges_to_collapse_set.contains(e))
        .collect();

    remap_graph(
        &recursive_remapping,
        (filtered_nodes, filtered_edges, mapping, association),
    )
}

// ===========================================================================
// topsort (replaces fgl's topsort)
// ===========================================================================

/// Topological sort matching fgl's `topsort = reverse . postflatten . dff`:
/// DFS forest over nodes in ascending id order, successors in edge order,
/// reverse of the postorder.
pub fn topsort(nodes: &[(Node, CFNode)], edges: &[(Node, Node, CFEdge)]) -> Vec<Node> {
    let mut succ: HashMap<Node, Vec<Node>> = HashMap::new();
    for (n, _) in nodes {
        succ.entry(*n).or_default();
    }
    for (from, to, _) in edges {
        succ.entry(*from).or_default().push(*to);
    }
    let mut ids: Vec<Node> = nodes.iter().map(|(n, _)| *n).collect();
    ids.sort_unstable();

    let mut visited: HashSet<Node> = HashSet::new();
    let mut postorder: Vec<Node> = Vec::new();

    // iterative DFS producing postorder
    for &root in &ids {
        if visited.contains(&root) {
            continue;
        }
        // stack of (node, child index)
        let mut stack: Vec<(Node, usize)> = vec![(root, 0)];
        visited.insert(root);
        while let Some((node, idx)) = stack.pop() {
            let children = succ.get(&node).cloned().unwrap_or_default();
            if idx < children.len() {
                stack.push((node, idx + 1));
                let c = children[idx];
                if !visited.contains(&c) {
                    visited.insert(c);
                    stack.push((c, 0));
                }
            } else {
                postorder.push(node);
            }
        }
    }
    postorder.reverse();
    postorder
}

// ===========================================================================
// Post-dominators (replaces fgl's dom + inlineSubshells)
// ===========================================================================

fn find_terminal_nodes(g: &MutGraph) -> Vec<Node> {
    let mut out = Vec::new();
    for n in g.node_list() {
        match g.labels.get(&n) {
            Some(CFNode::CFUnresolvedExit) => out.push(n),
            Some(CFNode::CFApplyEffects(effects)) => {
                for e in effects {
                    if let CFEffect::CFDefineFunction(_, _, _start, end) = &e.value {
                        out.push(*end);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Change all subshell invocations to instead link directly to their contents.
fn inline_subshells(g: &mut MutGraph) {
    // Collect subshells with their (original) incoming/outgoing.
    let mut subs: Vec<(Node, CFNode, Node, Node, Vec<(Node, CFEdge)>, Vec<(Node, CFEdge)>)> =
        Vec::new();
    for n in g.node_list() {
        if let Some(CFNode::CFExecuteSubshell(_, start, end)) = g.labels.get(&n).cloned() {
            let (incoming, _, label, outgoing) = g.context(n);
            subs.push((n, label, start, end, incoming, outgoing));
        }
    }
    for (node, label, start, end, incoming, outgoing) in subs {
        // endToNexts safeUpdate first, then subshellToStart.
        let (end_incoming, _, end_label, _) = g.context(end);
        g.safe_update(end_incoming, end, end_label, outgoing);
        g.safe_update(incoming, node, label, vec![(start, CFEdge::CFEFlow)]);
    }
}

/// `findPostDominators mainexit graph` -> array (indexed by node) of the list
/// of post-dominators of each node.
fn find_post_dominators(
    mainexit: Node,
    nodes: &[(Node, CFNode)],
    only_real_edges: &[(Node, Node, CFEdge)],
) -> Vec<Vec<Node>> {
    let base = MutGraph::from(nodes, only_real_edges);
    let max_node = base.max_node();

    let mut inlined = base.clone();
    inline_subshells(&mut inlined);

    let terminals = find_terminal_nodes(&inlined);

    // context from the ORIGINAL (only-real-edges) graph, plus terminal edges.
    let (mut incoming, _, label, outgoing) = base.context(mainexit);
    for c in &terminals {
        incoming.push((*c, CFEdge::CFEFlow));
    }
    inlined.safe_update(incoming, mainexit, label, outgoing);

    // reverse and compute dominators from mainexit.
    inlined.grev();
    let post_doms = dom(&inlined, mainexit);

    let mut arr: Vec<Vec<Node>> = vec![Vec::new(); max_node + 1];
    for (node, doms) in post_doms {
        if node <= max_node {
            arr[node] = doms;
        }
    }
    arr
}

/// Dominators from `root`, following successor edges. Returns, for every node
/// in the graph, its dominator chain `[node, idom, ..., root]`. Nodes not
/// reachable from `root` get the full node set (matching fgl's `dom`).
fn dom(g: &MutGraph, root: Node) -> Vec<(Node, Vec<Node>)> {
    let all_nodes = g.node_list();

    // DFS from root over successors, produce postorder (reachable set).
    let mut visited: HashSet<Node> = HashSet::new();
    let mut postorder: Vec<Node> = Vec::new();
    if g.labels.contains_key(&root) {
        let mut stack: Vec<(Node, usize)> = vec![(root, 0)];
        visited.insert(root);
        while let Some((node, idx)) = stack.pop() {
            let children: Vec<Node> = g
                .succ
                .get(&node)
                .map(|v| v.iter().map(|(to, _)| *to).collect())
                .unwrap_or_default();
            if idx < children.len() {
                stack.push((node, idx + 1));
                let c = children[idx];
                if !visited.contains(&c) {
                    visited.insert(c);
                    stack.push((c, 0));
                }
            } else {
                postorder.push(node);
            }
        }
    }

    // Reverse postorder; assign numbers (root first).
    let mut rpo = postorder.clone();
    rpo.reverse();
    let mut number: HashMap<Node, usize> = HashMap::new();
    for (i, n) in rpo.iter().enumerate() {
        number.insert(*n, i);
    }

    // Cooper-Harvey-Kennedy iterative dominators.
    let mut idom: HashMap<Node, Node> = HashMap::new();
    idom.insert(root, root);

    let intersect = |mut a: Node, mut b: Node, idom: &HashMap<Node, Node>, number: &HashMap<Node, usize>| -> Node {
        while a != b {
            while number[&a] > number[&b] {
                a = idom[&a];
            }
            while number[&b] > number[&a] {
                b = idom[&b];
            }
        }
        a
    };

    let mut changed = true;
    while changed {
        changed = false;
        for &n in rpo.iter() {
            if n == root {
                continue;
            }
            let preds: Vec<Node> = g
                .pred
                .get(&n)
                .map(|v| v.iter().map(|(from, _)| *from).collect())
                .unwrap_or_default();
            let mut new_idom: Option<Node> = None;
            for &p in &preds {
                if !number.contains_key(&p) {
                    continue; // unreachable pred
                }
                if idom.contains_key(&p) {
                    new_idom = Some(match new_idom {
                        None => p,
                        Some(cur) => intersect(p, cur, &idom, &number),
                    });
                }
            }
            if let Some(ni) = new_idom {
                if idom.get(&n) != Some(&ni) {
                    idom.insert(n, ni);
                    changed = true;
                }
            }
        }
    }

    // Build result: chain for reachable nodes, all-nodes for unreachable.
    let mut result: Vec<(Node, Vec<Node>)> = Vec::new();
    for &n in &all_nodes {
        if number.contains_key(&n) {
            let mut chain = vec![n];
            let mut cur = n;
            while cur != root {
                cur = idom[&cur];
                chain.push(cur);
            }
            result.push((n, chain));
        } else {
            result.push((n, all_nodes.clone()));
        }
    }
    result
}

// ===========================================================================
// ASTLib helpers ported locally (CFG.hs relies on these)
// ===========================================================================

const FLAGS_FOR_READ: &str = "sreu:n:N:i:p:a:t:";
const FLAGS_FOR_MAPFILE: &str = "d:n:O:s:u:C:c:t";

pub(crate) fn is_variable_start_char(c: char) -> bool {
    c == '_' || c.is_ascii_lowercase() || c.is_ascii_uppercase()
}
pub(crate) fn is_variable_char(c: char) -> bool {
    is_variable_start_char(c) || c.is_ascii_digit()
}
pub(crate) fn is_special_variable_char(c: char) -> bool {
    "*@#?-$!".contains(c)
}

/// `isVariableName`.
pub(crate) fn is_variable_name(s: &str) -> bool {
    let mut it = s.chars();
    match it.next() {
        Some(x) => is_variable_start_char(x) && it.all(is_variable_char),
        None => false,
    }
}

/// `getLiteralStringDef def t` — non-literals contribute `def`.
pub(crate) fn get_literal_string_def(t: &Token, def: &str) -> String {
    crate::astlib::get_literal_string_ext(t, &|_| Some(def.to_string())).unwrap_or_default()
}

/// `getUnquotedLiteral`.
fn get_unquoted_literal(t: &Token) -> Option<String> {
    match &*t.inner {
        InnerToken::T_NormalWord(list) => {
            let mut out = String::new();
            for p in list {
                match &*p.inner {
                    InnerToken::T_Literal(s) => out.push_str(s),
                    _ => return None,
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// `oversimplify` (faithful to ASTLib).
pub(crate) fn oversimplify(t: &Token) -> Vec<String> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(l) => {
            let s: String = l.iter().flat_map(oversimplify).collect::<Vec<_>>().concat();
            vec![s]
        }
        T_DoubleQuoted(l) => {
            let s: String = l.iter().flat_map(oversimplify).collect::<Vec<_>>().concat();
            vec![s]
        }
        T_SingleQuoted(s) => vec![s.clone()],
        T_DollarBraced { .. } => vec!["${VAR}".to_string()],
        T_DollarArithmetic(_) => vec!["${VAR}".to_string()],
        T_DollarExpansion(_) => vec!["${VAR}".to_string()],
        T_Backticked(_) => vec!["${VAR}".to_string()],
        T_Glob(s) => vec![s.clone()],
        T_Pipeline { commands, .. } if commands.len() == 1 => oversimplify(&commands[0]),
        T_Literal(x) => vec![x.clone()],
        T_ParamSubSpecialChar(x) => vec![x.clone()],
        T_SimpleCommand { words, .. } => words.iter().flat_map(oversimplify).collect(),
        T_Redirecting { cmd, .. } => oversimplify(cmd),
        T_DollarSingleQuoted(s) => vec![s.clone()],
        T_Annotation { token, .. } => oversimplify(token),
        TA_Sequence(seq) if seq.len() == 1 && matches!(&*seq[0].inner, TA_Expansion(_)) => {
            match &*seq[0].inner {
                TA_Expansion(v) => v.iter().flat_map(oversimplify).collect(),
                _ => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}

pub(crate) fn oversimplify_concat(t: &Token) -> String {
    oversimplify(t).concat()
}

/// `getBracedReference`.
pub(crate) fn get_braced_reference(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let drop_prefix = |cs: &[char]| -> Vec<char> {
        if let Some(&c) = cs.first() {
            if c == '!' || c == '#' {
                return cs[1..].to_vec();
            }
        }
        cs.to_vec()
    };
    let no_prefix = drop_prefix(&chars);

    let take_name = |cs: &[char]| -> Option<String> {
        let name: String = cs.iter().take_while(|c| is_variable_char(**c)).collect();
        if name.is_empty() {
            None
        } else {
            Some(name)
        }
    };
    let get_special = |cs: &[char]| -> Option<String> {
        match cs.first() {
            Some(&c) if is_special_variable_char(c) => Some(c.to_string()),
            _ => None,
        }
    };
    // nameExpansion ('!':next:rest): e.g. ${!foo*}
    let name_expansion = |cs: &[char]| -> Option<String> {
        if cs.len() >= 2 && cs[0] == '!' {
            let next = cs[1];
            if !is_variable_char(next) {
                return None;
            }
            let rest = &cs[2..];
            let first = rest.iter().copied().find(|c| !is_variable_char(*c))?;
            if "*?@".contains(first) {
                return Some(String::new());
            }
        }
        None
    };

    name_expansion(&chars)
        .or_else(|| take_name(&no_prefix))
        .or_else(|| get_special(&no_prefix))
        .or_else(|| get_special(&chars))
        .unwrap_or_else(|| s.to_string())
}

/// `getBracedModifier`.
pub(crate) fn get_braced_modifier(s: &str) -> String {
    let var = get_braced_reference(s);
    let chars: Vec<char> = s.chars().collect();
    // dropModifier: candidates in list-monad order.
    let candidates: Vec<String> = match chars.first() {
        Some(&c) if c == '#' || c == '!' => {
            vec![chars[1..].iter().collect(), s.to_string()]
        }
        _ => vec![s.to_string()],
    };
    for a in candidates {
        if let Some(rest) = a.strip_prefix(&var) {
            return rest.to_string();
        }
    }
    String::new()
}

fn variable_name_regex() -> &'static Regex {
    use std::sync::OnceLock;
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| Regex::new(r"[_a-zA-Z][_a-zA-Z0-9]*").unwrap())
}

/// `getIndexReferences`.
pub(crate) fn get_index_references(s: &str) -> Vec<String> {
    use std::sync::OnceLock;
    static RE: OnceLock<Regex> = OnceLock::new();
    let re = RE.get_or_init(|| Regex::new(r"(\[.*\])").unwrap());
    match re.captures(s).and_then(|c| c.get(1)) {
        Some(m) => variable_name_regex()
            .find_iter(m.as_str())
            .map(|x| x.as_str().to_string())
            .collect(),
        None => Vec::new(),
    }
}

/// `getOffsetReferences`.
pub(crate) fn get_offset_references(mods: &str) -> Vec<String> {
    use std::sync::OnceLock;
    static RE: OnceLock<Regex> = OnceLock::new();
    let re = RE.get_or_init(|| Regex::new(r"^(\[.+\])? *:([^-=?+].*)").unwrap());
    match re.captures(mods).and_then(|c| c.get(2)) {
        Some(m) => variable_name_regex()
            .find_iter(m.as_str())
            .map(|x| x.as_str().to_string())
            .collect(),
        None => Vec::new(),
    }
}

/// `variableAssignRegex` match: group 1 of `^([_a-zA-Z][_a-zA-Z0-9]*)=`.
fn var_assign_match(s: &str) -> Option<String> {
    use std::sync::OnceLock;
    static RE: OnceLock<Regex> = OnceLock::new();
    let re = RE.get_or_init(|| Regex::new(r"^([_a-zA-Z][_a-zA-Z0-9]*)=").unwrap());
    re.captures(s).and_then(|c| c.get(1)).map(|m| m.as_str().to_string())
}

/// `isUnmodifiedParameterExpansion`.
fn is_unmodified_parameter_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { braced: false, .. } => true,
        InnerToken::T_DollarBraced { op, .. } => {
            let str = oversimplify_concat(op);
            get_braced_reference(&str) == str
        }
        _ => false,
    }
}

/// `tokenToParts`.
fn token_to_parts(t: &Token) -> Vec<CFStringPart> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(list) => list.iter().flat_map(token_to_parts).collect(),
        T_DoubleQuoted(list) => list.iter().flat_map(token_to_parts).collect(),
        T_SingleQuoted(str) => vec![CFStringPart::CFStringLiteral(str.clone())],
        T_Literal(str) => vec![CFStringPart::CFStringLiteral(str.clone())],
        T_DollarArithmetic(_) => vec![CFStringPart::CFStringInteger],
        T_DollarBracket(_) => vec![CFStringPart::CFStringInteger],
        T_DollarBraced { op, .. } if is_unmodified_parameter_expansion(t) => {
            let reference = get_braced_reference(&oversimplify_concat(op));
            vec![CFStringPart::CFStringVariable(reference)]
        }
        _ => match get_literal_string(t) {
            Some(s) => vec![CFStringPart::CFStringLiteral(s)],
            None => vec![CFStringPart::CFStringUnknown],
        },
    }
}

/// `f` from buildAssignment: value type of an unindexed assignment RHS.
fn assignment_value(id: Id, mode: AssignmentMode, var: &str, value: &Token) -> CFValue {
    match &*value.inner {
        InnerToken::T_NormalWord(_) | InnerToken::T_Literal(_) => {
            let mut parts = Vec::new();
            if mode == AssignmentMode::Append {
                parts.push(CFStringPart::CFStringVariable(var.to_string()));
            }
            parts.extend(token_to_parts(value));
            CFValue::CFValueComputed(id, parts)
        }
        InnerToken::T_Array(_) => CFValue::CFValueArray,
        _ => CFValue::CFValueString,
    }
}

/// `isClosingFileOp`.
fn is_closing_file_op(op: &Token) -> bool {
    match &*op.inner {
        InnerToken::T_IoDuplicate { op: inner_op, num } if num == "-" => {
            matches!(&*inner_op.inner, InnerToken::T_GREATAND | InnerToken::T_LESSAND)
        }
        _ => false,
    }
}

/// `willSplit`.
fn will_split(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => true,
        T_DollarExpansion(_) => true,
        T_Backticked(_) => true,
        T_BraceExpansion(_) => true,
        T_Glob(_) => true,
        T_Extglob { .. } => true,
        T_DoubleQuoted(l) => l.iter().any(will_become_multiple_args),
        T_NormalWord(l) => l.iter().any(will_split),
        _ => false,
    }
}

fn will_become_multiple_args(t: &Token) -> bool {
    will_concat_in_assignment(t) || {
        use InnerToken::*;
        match &*t.inner {
            T_Extglob { .. } => true,
            T_Glob(_) => true,
            T_BraceExpansion(_) => true,
            T_NormalWord(l) => l.iter().any(will_become_multiple_args),
            _ => false,
        }
    }
}

fn will_concat_in_assignment(t: &Token) -> bool {
    use InnerToken::*;
    match &*t.inner {
        T_DollarBraced { .. } => is_array_expansion(t),
        T_DoubleQuoted(parts) => parts.iter().any(will_concat_in_assignment),
        T_NormalWord(parts) => parts.iter().any(will_concat_in_assignment),
        _ => false,
    }
}

fn is_array_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let string = oversimplify_concat(op);
            string.starts_with('@')
                || (!string.starts_with('#') && string.contains("[@]"))
        }
        _ => false,
    }
}

// --- pseudoglob (for case catch-all detection) ---

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PseudoGlob {
    PGAny,
    PGMany,
    PGChar(char),
}

pub(crate) fn get_word_parts(t: &Token) -> Vec<Token> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(l) => l.iter().flat_map(get_word_parts).collect(),
        T_DoubleQuoted(l) => l.clone(),
        TA_Expansion(l) => l.iter().flat_map(get_word_parts).collect(),
        _ => vec![t.clone()],
    }
}

/// `wordToExactPseudoGlob` = `wordToPseudoGlob' True`.
fn word_to_exact_pseudo_glob(word: &Token) -> Option<Vec<PseudoGlob>> {
    fn f(x: &Token) -> Option<Vec<PseudoGlob>> {
        match &*x.inner {
            InnerToken::T_Literal(s) => Some(s.chars().map(PseudoGlob::PGChar).collect()),
            InnerToken::T_SingleQuoted(s) => Some(s.chars().map(PseudoGlob::PGChar).collect()),
            InnerToken::T_Glob(g) if g == "?" => Some(vec![PseudoGlob::PGAny]),
            InnerToken::T_Glob(g) if g == "*" => Some(vec![PseudoGlob::PGMany]),
            // exact = true: '[' globs and everything else fail.
            _ => None,
        }
    }
    // toGlob: the '~' branch requires not exact, so it never applies here.
    let parts = get_word_parts(word);
    let mut out = Vec::new();
    for p in &parts {
        out.extend(f(p)?);
    }
    Some(simplify_pseudo_glob(out))
}

fn simplify_pseudo_glob(list: Vec<PseudoGlob>) -> Vec<PseudoGlob> {
    fn order(s: &[PseudoGlob]) -> Vec<PseudoGlob> {
        let anys: Vec<PseudoGlob> =
            s.iter().copied().filter(|x| *x == PseudoGlob::PGAny).collect();
        let many: Vec<PseudoGlob> =
            s.iter().copied().filter(|x| *x == PseudoGlob::PGMany).collect();
        let mut out = anys;
        out.extend(many.into_iter().take(1));
        out
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < list.len() {
        if let PseudoGlob::PGChar(_) = list[i] {
            out.push(list[i]);
            i += 1;
        } else {
            let start = i;
            while i < list.len()
                && (list[i] == PseudoGlob::PGMany || list[i] == PseudoGlob::PGAny)
            {
                i += 1;
            }
            out.extend(order(&list[start..i]));
        }
    }
    out
}

/// `pseudoGlobIsSuperSetof`.
fn pseudo_glob_is_superset_of(x: &[PseudoGlob], y: &[PseudoGlob]) -> bool {
    match (x.first(), y.first()) {
        (Some(&xf), Some(&yf)) => match (xf, yf) {
            (PseudoGlob::PGMany, PseudoGlob::PGMany) => {
                pseudo_glob_is_superset_of(x, &y[1..])
            }
            (PseudoGlob::PGMany, _) => {
                pseudo_glob_is_superset_of(x, &y[1..])
                    || pseudo_glob_is_superset_of(&x[1..], y)
            }
            (_, PseudoGlob::PGMany) => false,
            (PseudoGlob::PGAny, _) => pseudo_glob_is_superset_of(&x[1..], &y[1..]),
            (_, PseudoGlob::PGAny) => false,
            (a, b) => a == b && pseudo_glob_is_superset_of(&x[1..], &y[1..]),
        },
        (None, None) => true,
        (Some(&PseudoGlob::PGMany), None) => pseudo_glob_is_superset_of(&x[1..], &[]),
        _ => false,
    }
}

fn has_catch_all(conds: &[Token]) -> bool {
    conds.iter().any(|c| {
        word_to_exact_pseudo_glob(c)
            .map(|pg| pseudo_glob_is_superset_of(&pg, &[PseudoGlob::PGMany]))
            .unwrap_or(false)
    })
}

// --- getOpts family ---

fn lookup(key: &str, flags: &[(String, (Token, Token))]) -> Option<(Token, Token)> {
    flags.iter().find(|(k, _)| k == key).map(|(_, v)| v.clone())
}

pub(crate) fn get_gnu_opts(spec: &str, args: &[Token]) -> Option<Vec<(String, (Token, Token))>> {
    get_opts(true, false, spec, &[], args)
}
pub(crate) fn get_bsd_opts(spec: &str, args: &[Token]) -> Option<Vec<(String, (Token, Token))>> {
    get_opts(false, false, spec, &[], args)
}

fn build_flag_map(spec: &str, longopts: &[(String, bool)]) -> HashMap<String, bool> {
    let mut m: HashMap<String, bool> = HashMap::new();
    m.insert(String::new(), false);
    let chars: Vec<char> = spec.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if i + 1 < chars.len() && chars[i + 1] == ':' {
            m.insert(c.to_string(), true);
            i += 2;
        } else {
            m.insert(c.to_string(), false);
            i += 1;
        }
    }
    for (name, takes) in longopts {
        m.insert(name.clone(), *takes);
    }
    m
}

fn get_opts(
    gnu: bool,
    arbitrary_long_opts: bool,
    spec: &str,
    longopts: &[(String, bool)],
    args: &[Token],
) -> Option<Vec<(String, (Token, Token))>> {
    let flag_map = build_flag_map(spec, longopts);
    fn list_to_args(list: &[Token]) -> Vec<(String, (Token, Token))> {
        list.iter().map(|x| (String::new(), (x.clone(), x.clone()))).collect()
    }

    fn short_to_opts(
        opts: &[char],
        token: &Token,
        args: &[Token],
        flag_map: &HashMap<String, bool>,
        gnu: bool,
        arbitrary: bool,
    ) -> Option<Vec<(String, (Token, Token))>> {
        if opts.is_empty() {
            return process(args, flag_map, gnu, arbitrary);
        }
        let c = opts[0];
        let rest = &opts[1..];
        let needs_arg = *flag_map.get(&c.to_string())?;
        if needs_arg && rest.is_empty() {
            let next = args.first()?;
            let rest_args = &args[1..];
            let mut more = process(rest_args, flag_map, gnu, arbitrary)?;
            let mut out = vec![(c.to_string(), (token.clone(), next.clone()))];
            out.append(&mut more);
            Some(out)
        } else if needs_arg {
            let mut more = process(args, flag_map, gnu, arbitrary)?;
            let mut out = vec![(c.to_string(), (token.clone(), token.clone()))];
            out.append(&mut more);
            Some(out)
        } else {
            let mut more = short_to_opts(rest, token, args, flag_map, gnu, arbitrary)?;
            let mut out = vec![(c.to_string(), (token.clone(), token.clone()))];
            out.append(&mut more);
            Some(out)
        }
    }

    fn process(
        args: &[Token],
        flag_map: &HashMap<String, bool>,
        gnu: bool,
        arbitrary: bool,
    ) -> Option<Vec<(String, (Token, Token))>> {
        if args.is_empty() {
            return Some(Vec::new());
        }
        let token = &args[0];
        let rest = &args[1..];
        let s = get_literal_string_def(token, "\0");
        if s == "--" {
            return Some(list_to_args(rest));
        }
        if let Some(word) = s.strip_prefix("--") {
            // span (/= '=')
            let (name, arg) = match word.find('=') {
                Some(idx) => (&word[..idx], &word[idx..]),
                None => (word, ""),
            };
            let needs_arg = if arbitrary {
                *flag_map.get(name).unwrap_or(&false)
            } else {
                *flag_map.get(name)?
            };
            if needs_arg && arg.is_empty() {
                if let Some(argtok) = rest.first() {
                    let rest2 = &rest[1..];
                    let mut more = process(rest2, flag_map, gnu, arbitrary)?;
                    let mut out =
                        vec![(name.to_string(), (token.clone(), argtok.clone()))];
                    out.append(&mut more);
                    Some(out)
                } else {
                    None
                }
            } else {
                let mut more = process(rest, flag_map, gnu, arbitrary)?;
                let mut out = vec![(name.to_string(), (token.clone(), token.clone()))];
                out.append(&mut more);
                Some(out)
            }
        } else if let Some(opts) = s.strip_prefix('-') {
            // `'-':opts -> shortToOpts opts token rest` (also covers bare "-").
            let opt_chars: Vec<char> = opts.chars().collect();
            short_to_opts(&opt_chars, token, rest, flag_map, gnu, arbitrary)
        } else if gnu {
            let mut more = process(rest, flag_map, gnu, arbitrary)?;
            let mut out = vec![(String::new(), (token.clone(), token.clone()))];
            out.append(&mut more);
            Some(out)
        } else {
            Some(list_to_args(args))
        }
    }

    process(args, &flag_map, gnu, arbitrary_long_opts)
}

/// `getGenericOpts`.
pub(crate) fn get_generic_opts(args: &[Token]) -> Vec<(String, (Token, Token))> {
    if args.is_empty() {
        return Vec::new();
    }
    let token = &args[0];
    let rest = &args[1..];
    let s = get_literal_string_def(token, "\0");
    if s == "--" {
        return rest.iter().map(|c| (String::new(), (c.clone(), c.clone()))).collect();
    }
    if let Some(word) = s.strip_prefix("--") {
        let name: String = word.chars().take_while(|c| *c != '\0' && *c != '=').collect();
        let mut out = vec![(name, (token.clone(), token.clone()))];
        out.extend(get_generic_opts(rest));
        return out;
    }
    if let Some(optstring) = s.strip_prefix('-') {
        // Only if not "--" (handled) — a bare "-" gives empty opts.
        let opts: String = optstring.chars().take_while(|c| *c != '\0').collect();
        let opt_chars: Vec<char> = opts.chars().collect();
        match rest.first() {
            Some(next) if get_literal_string_def(next, "\0").starts_with('-') => {
                let mut out: Vec<(String, (Token, Token))> = opt_chars
                    .iter()
                    .map(|c| (c.to_string(), (token.clone(), token.clone())))
                    .collect();
                out.extend(get_generic_opts(rest));
                out
            }
            Some(next) => {
                let remainder = &rest[1..];
                if let Some((last, initial)) = opt_chars.split_last() {
                    let mut out: Vec<(String, (Token, Token))> = initial
                        .iter()
                        .map(|c| (c.to_string(), (token.clone(), token.clone())))
                        .collect();
                    out.push((last.to_string(), (token.clone(), next.clone())));
                    out.extend(get_generic_opts(remainder));
                    out
                } else {
                    get_generic_opts(remainder)
                }
            }
            None => opt_chars
                .iter()
                .map(|c| (c.to_string(), (token.clone(), token.clone())))
                .collect(),
        }
    } else {
        let mut out = vec![(String::new(), (token.clone(), token.clone()))];
        out.extend(get_generic_opts(rest));
        out
    }
}

// ===========================================================================
// Tests (ported from CFG.hs prop_*)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn s() -> CFNode {
        CFNode::CFStructuralNode
    }

    #[test]
    fn prop_test_renumbering() {
        let before: CFW = (
            vec![(1, s()), (3, s()), (4, s()), (8, s())],
            vec![
                (1, 3, CFEdge::CFEFlow),
                (3, 4, CFEdge::CFEFlow),
                (4, 8, CFEdge::CFEFlow),
            ],
            vec![(Id(0), (3, 4))],
            vec![(Id(1), 3), (Id(2), 4)],
        );
        let after: CFW = (
            vec![(0, s()), (1, s()), (2, s()), (3, s())],
            vec![
                (0, 1, CFEdge::CFEFlow),
                (1, 2, CFEdge::CFEFlow),
                (2, 3, CFEdge::CFEFlow),
            ],
            vec![(Id(0), (1, 2))],
            vec![(Id(1), 1), (Id(2), 2)],
        );
        assert_eq!(after, renumber_graph(before));
    }

    #[test]
    fn prop_test_renumber_topologically() {
        let before: CFW = (
            vec![(4, s()), (2, s()), (3, s())],
            vec![(4, 2, CFEdge::CFEFlow), (2, 3, CFEdge::CFEFlow)],
            vec![(Id(0), (4, 2))],
            vec![],
        );
        let after: CFW = (
            vec![(0, s()), (1, s()), (2, s())],
            vec![(0, 1, CFEdge::CFEFlow), (1, 2, CFEdge::CFEFlow)],
            vec![(Id(0), (0, 1))],
            vec![],
        );
        assert_eq!(after, renumber_topologically(before));
    }

    #[test]
    fn prop_test_remove_structural() {
        let before: CFW = (
            vec![(1, s()), (2, s()), (3, s()), (4, s())],
            vec![
                (1, 2, CFEdge::CFEFlow),
                (2, 3, CFEdge::CFEFlow),
                (3, 4, CFEdge::CFEFlow),
            ],
            vec![(Id(0), (2, 3))],
            vec![(Id(0), 3)],
        );
        let after: CFW = (
            vec![(1, s()), (2, s()), (4, s())],
            vec![(1, 2, CFEdge::CFEFlow), (2, 4, CFEdge::CFEFlow)],
            vec![(Id(0), (2, 2))],
            vec![(Id(0), 2)],
        );
        assert_eq!(after, remove_unnecessary_structural_nodes(before));
    }

    #[test]
    fn cfg_smoke_build_graph() {
        // A small end-to-end build to ensure construction + post-dominators run.
        let out = crate::parser::parse_script("test.sh", "x=1\necho \"$x\"\n");
        let root = out.root.expect("parse produced a root");
        let params = CFGParameters { cf_lastpipe: false, cf_pipefail: false };
        let result = build_graph(params, &root);
        // The root's range must exist and its exit must be post-dominated by itself.
        let (_, main_exit) = result.cf_id_to_range[&root.id];
        assert!(main_exit < result.cf_post_dominators.len());
        assert!(result.cf_post_dominators[main_exit].contains(&main_exit));
        assert!(!result.cf_graph.nodes.is_empty());
    }

    #[test]
    fn cfg_smoke_complex_constructs() {
        // Exercise the full range of builders end-to-end without panicking.
        let scripts = [
            "f() { local x=1; echo \"$x\"; return 0; }\nf\n",
            "for i in a b c; do echo \"$i\"; done\n",
            "while read -r line; do echo \"$line\"; done\n",
            "case $x in foo) echo a;; *) exit 1;; esac\n",
            "( echo sub ) | grep x || true\n",
            "declare -i -x y=5; declare -A m; unset -v y\n",
            "x=$(echo hi) && echo \"${x:-default}\" &\n",
            "if [ -z \"$x\" ]; then echo empty; elif true; then echo mid; else echo full; fi\n",
            "mapfile -t arr < file; printf -v out '%s' done\n",
        ];
        let params = CFGParameters { cf_lastpipe: true, cf_pipefail: true };
        for src in scripts {
            let out = crate::parser::parse_script("test.sh", src);
            if let Some(root) = out.root {
                let result = build_graph(params, &root);
                // Post-dominator array is well-formed and covers the exit node.
                let (_, main_exit) = result.cf_id_to_range[&root.id];
                assert!(main_exit < result.cf_post_dominators.len());
                assert!(result.cf_post_dominators[main_exit].contains(&main_exit));
            }
        }
    }
}
