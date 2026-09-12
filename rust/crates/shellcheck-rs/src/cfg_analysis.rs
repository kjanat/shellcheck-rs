//! Port of `ShellCheck.CFGAnalysis` — Data Flow Analysis on a Control Flow Graph.
//!
//! This is a faithful, dependency-light port of `src/ShellCheck/CFGAnalysis.hs`.
//! The Haskell original runs the whole thing in `ST` with manually-passed
//! `STRef`s inside a `Ctx`. Here the `Ctx` is a plain mutable struct whose
//! methods take `&mut self`; the function/subshell stack lives in `Ctx::stack`,
//! and save/restore of the current input/output/node reproduces the fresh
//! `STRef`s that `withNewStackFrame` creates.
//!
//! Public entry point: [`analyze_control_flow`] (Haskell `analyzeControlFlow`).
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::ast::{Id, Token};
use crate::cfg::{
    CFEdge, CFEffect, CFGParameters, CFGraph, CFNode, CFStringPart, CFValue, CFVariableProp, Node,
    Scope, build_graph,
};
use crate::data::{INTERNAL_VARIABLES, SPECIAL_INTEGER_VARIABLES, VARIABLES_WITHOUT_SPACES};

// The number of iterations for DFA to stabilize
const ITERATION_COUNT: i64 = 1_000_000;
// Disable caching if there's this many iterations left (guards oscillation).
const FALLBACK_THRESHOLD: i64 = 10_000;
// The number of cache entries to keep per node
const CACHE_ENTRIES: usize = 10;

// ===========================================================================
// Externally-exposed lattice values
// ===========================================================================

/// Whether or not the value needs quoting (has spaces/globs), or we don't know.
///
/// Declaration order is the Haskell `Ord` order and must not change.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpaceStatus {
    SpaceStatusEmpty,
    SpaceStatusClean,
    SpaceStatusDirty,
}

/// Whether or not the value is an integer, or we don't know.
///
/// Declaration order is the Haskell `Ord` order and must not change
/// (`variableMayBeAssignedInteger` relies on `>= NumericalStatusMaybe`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumericalStatus {
    NumericalStatusUnknown,
    NumericalStatusEmpty,
    NumericalStatusMaybe,
    NumericalStatusDefinitely,
}

/// The set of possible sets of properties for this variable.
pub type VariableProperties = BTreeSet<BTreeSet<CFVariableProp>>;

/// The information about the value of a single variable.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableValue {
    /// For debugging only; censored to `None` in externally exposed states.
    pub literal_value: Option<String>,
    pub space_status: SpaceStatus,
    pub numerical_status: NumericalStatus,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableState {
    pub variable_value: VariableValue,
    pub variable_properties: VariableProperties,
}

/// The program state we expose externally.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramState {
    pub variables_in_scope: BTreeMap<String, VariableState>,
    pub exit_codes: BTreeSet<Id>,
    pub state_is_reachable: bool,
}

impl ProgramState {
    pub fn variables_in_scope(&self) -> &BTreeMap<String, VariableState> {
        &self.variables_in_scope
    }
    pub fn variable_value(&self, name: &str) -> Option<&VariableValue> {
        self.variables_in_scope.get(name).map(|s| &s.variable_value)
    }
    pub fn space_status(&self, name: &str) -> Option<SpaceStatus> {
        self.variables_in_scope
            .get(name)
            .map(|s| s.variable_value.space_status)
    }
    pub fn numerical_status(&self, name: &str) -> Option<NumericalStatus> {
        self.variables_in_scope
            .get(name)
            .map(|s| s.variable_value.numerical_status)
    }
    pub fn variable_properties(&self, name: &str) -> Option<&VariableProperties> {
        self.variables_in_scope
            .get(name)
            .map(|s| &s.variable_properties)
    }
    pub fn state_is_reachable(&self) -> bool {
        self.state_is_reachable
    }
    pub fn exit_codes(&self) -> &BTreeSet<Id> {
        &self.exit_codes
    }

    /// See if any execution path declares the variable an integer (`declare -i`).
    pub fn variable_may_be_declared_integer(&self, var: &str) -> Option<bool> {
        let value = self.variables_in_scope.get(var)?;
        Some(
            value
                .variable_properties
                .iter()
                .any(|s| s.contains(&CFVariableProp::CFVPInteger)),
        )
    }

    /// See if any execution path suggests the variable may contain an integer.
    pub fn variable_may_be_assigned_integer(&self, var: &str) -> Option<bool> {
        let value = self.variables_in_scope.get(var)?;
        Some(value.variable_value.numerical_status >= NumericalStatus::NumericalStatusMaybe)
    }
}

/// Free-function forms matching the Haskell exports.
pub fn variable_may_be_declared_integer(state: &ProgramState, var: &str) -> Option<bool> {
    state.variable_may_be_declared_integer(var)
}
pub fn variable_may_be_assigned_integer(state: &ProgramState, var: &str) -> Option<bool> {
    state.variable_may_be_assigned_integer(var)
}

/// The result of the data flow analysis.
#[derive(Debug, Clone)]
pub struct CFGAnalysis {
    pub graph: CFGraph,
    pub token_to_range: HashMap<Id, (Node, Node)>,
    pub token_to_nodes: HashMap<Id, BTreeSet<Node>>,
    pub post_dominators: Vec<Vec<Node>>,
    pub node_to_data: HashMap<Node, (ProgramState, ProgramState)>,
}

impl CFGAnalysis {
    /// Conveniently get the state before a token id.
    pub fn get_incoming_state(&self, id: Id) -> Option<ProgramState> {
        let (start, _end) = self.token_to_range.get(&id)?;
        self.node_to_data.get(start).map(|x| x.0.clone())
    }

    /// Conveniently get the state after a token id.
    pub fn get_outgoing_state(&self, id: Id) -> Option<ProgramState> {
        let (_start, end) = self.token_to_range.get(&id)?;
        self.node_to_data.get(end).map(|x| x.1.clone())
    }

    /// Whether `target` always unconditionally runs after `base`.
    pub fn does_post_dominate(&self, target: Id, base: Id) -> bool {
        (|| {
            let (_, base_end) = self.token_to_range.get(&base)?;
            let (target_start, _) = self.token_to_range.get(&target)?;
            let doms = self.post_dominators.get(*base_end)?;
            Some(doms.contains(target_start))
        })()
        .unwrap_or(false)
    }
}

// ===========================================================================
// Internal lattice/state types
// ===========================================================================

/// A function definition, or lack thereof.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum FunctionDefinition {
    FunctionUnknown,
    /// name, entry, exit
    FunctionDefinition(String, Node, Node),
}

/// The set of places a command name can point.
type FunctionValue = BTreeSet<FunctionDefinition>;

fn unknown_function_value() -> FunctionValue {
    let mut s = BTreeSet::new();
    s.insert(FunctionDefinition::FunctionUnknown);
    s
}

/// Dependencies on values, used to key the DFA cache.
// Variant names mirror the Haskell constructors DepState / DepProperties / ...
#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum StateDependency {
    DepState(Scope, String, VariableState),
    DepProperties(Scope, String, VariableProperties),
    DepFunction(String, FunctionValue),
    DepIsRecursive(Node, bool),
    DepExitCodes(BTreeSet<Id>),
}

/// A `Map` that keeps an integer version to quickly determine if it changed.
/// * Version -1 means unknown (presumably changed)
/// * Version 0 means empty
/// * Version N means equal to any other map with version N.
#[derive(Debug, Clone)]
struct VMap<V> {
    version: i64,
    storage: BTreeMap<String, V>,
}

impl<V: Clone> VMap<V> {
    fn empty() -> Self {
        VMap {
            version: 0,
            storage: BTreeMap::new(),
        }
    }
    fn lookup(&self, k: &str) -> Option<&V> {
        self.storage.get(k)
    }
    fn insert(&self, k: &str, v: V) -> Self {
        let mut s = self.storage.clone();
        s.insert(k.to_string(), v);
        VMap {
            version: -1,
            storage: s,
        }
    }
}

fn vm_is_quick_equal<V>(a: &VMap<V>, b: &VMap<V>) -> bool {
    a.version >= 0 && b.version >= 0 && a.version == b.version
}
fn vm_eq<V: PartialEq>(a: &VMap<V>, b: &VMap<V>) -> bool {
    vm_is_quick_equal(a, b) || a.storage == b.storage
}

/// The current state of data flow at a point in the program, possibly a diff.
#[derive(Debug, Clone)]
struct InternalState {
    version: i64,
    s_global_values: VMap<VariableState>,
    s_local_values: VMap<VariableState>,
    s_prefix_values: VMap<VariableState>,
    s_function_targets: VMap<FunctionValue>,
    s_exit_codes: Option<BTreeSet<Id>>,
    s_is_reachable: Option<bool>,
}

fn new_internal_state() -> InternalState {
    InternalState {
        version: 0,
        s_global_values: VMap::empty(),
        s_local_values: VMap::empty(),
        s_prefix_values: VMap::empty(),
        s_function_targets: VMap::empty(),
        s_exit_codes: None,
        s_is_reachable: None,
    }
}

fn modified(mut s: InternalState) -> InternalState {
    s.version = -1;
    s
}

fn unreachable_state() -> InternalState {
    let mut s = new_internal_state();
    s.s_is_reachable = Some(false);
    modified(s)
}

fn state_is_quick_equal(a: &InternalState, b: &InternalState) -> bool {
    a.version >= 0 && b.version >= 0 && a.version == b.version
}

fn state_is_slow_equal(a: &InternalState, b: &InternalState) -> bool {
    vm_eq(&a.s_global_values, &b.s_global_values)
        && vm_eq(&a.s_local_values, &b.s_local_values)
        && vm_eq(&a.s_prefix_values, &b.s_prefix_values)
        && vm_eq(&a.s_function_targets, &b.s_function_targets)
        && a.s_is_reachable == b.s_is_reachable
}

fn state_eq(a: &InternalState, b: &InternalState) -> bool {
    state_is_quick_equal(a, b) || state_is_slow_equal(a, b)
}

// --- Value abstractions ---

fn unknown_variable_value() -> VariableValue {
    VariableValue {
        literal_value: None,
        space_status: SpaceStatus::SpaceStatusDirty,
        numerical_status: NumericalStatus::NumericalStatusUnknown,
    }
}
fn empty_variable_value() -> VariableValue {
    VariableValue {
        literal_value: Some(String::new()),
        space_status: SpaceStatus::SpaceStatusEmpty,
        numerical_status: NumericalStatus::NumericalStatusEmpty,
    }
}
fn unknown_integer_value() -> VariableValue {
    VariableValue {
        literal_value: None,
        space_status: SpaceStatus::SpaceStatusClean,
        numerical_status: NumericalStatus::NumericalStatusDefinitely,
    }
}
fn default_properties() -> VariableProperties {
    let mut s = BTreeSet::new();
    s.insert(BTreeSet::new());
    s
}
fn unknown_variable_state() -> VariableState {
    VariableState {
        variable_value: unknown_variable_value(),
        variable_properties: default_properties(),
    }
}
fn unset_variable_state() -> VariableState {
    VariableState {
        variable_value: empty_variable_value(),
        variable_properties: default_properties(),
    }
}

fn add_properties(props: &BTreeSet<CFVariableProp>, state: &VariableState) -> VariableState {
    let new_props = state
        .variable_properties
        .iter()
        .map(|s| s.union(props).copied().collect())
        .collect();
    VariableState {
        variable_value: state.variable_value.clone(),
        variable_properties: new_props,
    }
}
fn remove_properties(props: &BTreeSet<CFVariableProp>, state: &VariableState) -> VariableState {
    let new_props = state
        .variable_properties
        .iter()
        .map(|s| s.difference(props).copied().collect())
        .collect();
    VariableState {
        variable_value: state.variable_value.clone(),
        variable_properties: new_props,
    }
}

fn merge_space_status(a: SpaceStatus, b: SpaceStatus) -> SpaceStatus {
    use SpaceStatus::*;
    match (a, b) {
        (SpaceStatusEmpty, y) => y,
        (x, SpaceStatusEmpty) => x,
        (SpaceStatusClean, SpaceStatusClean) => SpaceStatusClean,
        _ => SpaceStatusDirty,
    }
}
fn merge_numerical_status(a: NumericalStatus, b: NumericalStatus) -> NumericalStatus {
    use NumericalStatus::*;
    match (a, b) {
        (NumericalStatusDefinitely, NumericalStatusDefinitely) => NumericalStatusDefinitely,
        (NumericalStatusDefinitely, _) => NumericalStatusMaybe,
        (_, NumericalStatusDefinitely) => NumericalStatusMaybe,
        (NumericalStatusMaybe, _) => NumericalStatusMaybe,
        (_, NumericalStatusMaybe) => NumericalStatusMaybe,
        (NumericalStatusEmpty, NumericalStatusEmpty) => NumericalStatusEmpty,
        _ => NumericalStatusUnknown,
    }
}
fn merge_variable_value(a: &VariableValue, b: &VariableValue) -> VariableValue {
    VariableValue {
        literal_value: if a.literal_value == b.literal_value {
            a.literal_value.clone()
        } else {
            None
        },
        space_status: merge_space_status(a.space_status, b.space_status),
        numerical_status: merge_numerical_status(a.numerical_status, b.numerical_status),
    }
}
fn merge_variable_state(a: &VariableState, b: &VariableState) -> VariableState {
    VariableState {
        variable_value: merge_variable_value(&a.variable_value, &b.variable_value),
        variable_properties: a
            .variable_properties
            .union(&b.variable_properties)
            .cloned()
            .collect(),
    }
}

fn append_space_status(a: SpaceStatus, b: SpaceStatus) -> SpaceStatus {
    use SpaceStatus::*;
    match (a, b) {
        (SpaceStatusEmpty, _) => b,
        (_, SpaceStatusEmpty) => a,
        (SpaceStatusClean, SpaceStatusClean) => SpaceStatusClean,
        _ => SpaceStatusDirty,
    }
}
fn append_numerical_status(a: NumericalStatus, b: NumericalStatus) -> NumericalStatus {
    use NumericalStatus::*;
    match (a, b) {
        (NumericalStatusEmpty, x) => x,
        (x, NumericalStatusEmpty) => x,
        (NumericalStatusDefinitely, NumericalStatusDefinitely) => NumericalStatusDefinitely,
        (NumericalStatusUnknown, _) => NumericalStatusUnknown,
        (_, NumericalStatusUnknown) => NumericalStatusUnknown,
        _ => NumericalStatusMaybe,
    }
}
fn append_variable_value(a: &VariableValue, b: &VariableValue) -> VariableValue {
    VariableValue {
        literal_value: match (&a.literal_value, &b.literal_value) {
            (Some(x), Some(y)) => Some(format!("{}{}", x, y)),
            _ => None,
        },
        space_status: append_space_status(a.space_status, b.space_status),
        numerical_status: append_numerical_status(a.numerical_status, b.numerical_status),
    }
}

fn literal_to_space_status(s: &str) -> SpaceStatus {
    if s.is_empty() {
        SpaceStatus::SpaceStatusEmpty
    } else if s.chars().all(|c| !" \t\n*?[".contains(c)) {
        SpaceStatus::SpaceStatusClean
    } else {
        SpaceStatus::SpaceStatusDirty
    }
}
fn literal_to_numerical_status(s: &str) -> NumericalStatus {
    if s.is_empty() {
        return NumericalStatus::NumericalStatusEmpty;
    }
    let rest = s.strip_prefix('-').unwrap_or(s);
    if rest.chars().all(|c| c.is_ascii_digit()) {
        NumericalStatus::NumericalStatusDefinitely
    } else {
        NumericalStatus::NumericalStatusUnknown
    }
}
fn literal_to_variable_value(s: &str) -> VariableValue {
    VariableValue {
        literal_value: Some(s.to_string()),
        space_status: literal_to_space_status(s),
        numerical_status: literal_to_numerical_status(s),
    }
}

// --- state field mutators (all set version = -1 via `modified`) ---

fn insert_global(name: &str, val: VariableState, state: &InternalState) -> InternalState {
    let mut s = state.clone();
    s.s_global_values = s.s_global_values.insert(name, val);
    modified(s)
}
fn insert_local(name: &str, val: VariableState, state: &InternalState) -> InternalState {
    let mut s = state.clone();
    s.s_local_values = s.s_local_values.insert(name, val);
    modified(s)
}
fn insert_prefix(name: &str, val: VariableState, state: &InternalState) -> InternalState {
    let mut s = state.clone();
    s.s_prefix_values = s.s_prefix_values.insert(name, val);
    modified(s)
}
fn insert_function(name: &str, val: FunctionValue, state: &InternalState) -> InternalState {
    let mut s = state.clone();
    s.s_function_targets = s.s_function_targets.insert(name, val);
    modified(s)
}
fn set_exit_codes(set: BTreeSet<Id>, state: &InternalState) -> InternalState {
    let mut s = state.clone();
    s.s_exit_codes = Some(set);
    modified(s)
}
fn set_exit_code(id: Id, state: &InternalState) -> InternalState {
    let mut set = BTreeSet::new();
    set.insert(id);
    set_exit_codes(set, state)
}

fn get_variable_with_scope(s: &InternalState, name: &str) -> Option<(VariableState, Scope)> {
    if let Some(v) = s.s_prefix_values.lookup(name) {
        return Some((v.clone(), Scope::PrefixScope));
    }
    if let Some(v) = s.s_local_values.lookup(name) {
        return Some((v.clone(), Scope::LocalScope));
    }
    if let Some(v) = s.s_global_values.lookup(name) {
        return Some((v.clone(), Scope::GlobalScope));
    }
    None
}

// --- patch / vmPatch ---

fn vm_patch<V: Clone + PartialEq>(base: &VMap<V>, diff: &VMap<V>) -> VMap<V> {
    if base.version == 0 {
        return diff.clone();
    }
    if diff.version == 0 {
        return base.clone();
    }
    if vm_is_quick_equal(base, diff) {
        return diff.clone();
    }
    let mut s = base.storage.clone();
    for (k, v) in &diff.storage {
        s.insert(k.clone(), v.clone());
    }
    VMap {
        version: -1,
        storage: s,
    }
}

fn patch_state(base: &InternalState, diff: &InternalState) -> InternalState {
    if diff.version == 0 {
        return base.clone();
    }
    if base.version == 0 {
        return diff.clone();
    }
    if state_is_quick_equal(base, diff) {
        return diff.clone();
    }
    InternalState {
        version: -1,
        s_global_values: vm_patch(&base.s_global_values, &diff.s_global_values),
        s_local_values: vm_patch(&base.s_local_values, &diff.s_local_values),
        s_prefix_values: vm_patch(&base.s_prefix_values, &diff.s_prefix_values),
        s_function_targets: vm_patch(&base.s_function_targets, &diff.s_function_targets),
        s_exit_codes: diff
            .s_exit_codes
            .clone()
            .or_else(|| base.s_exit_codes.clone()),
        s_is_reachable: diff.s_is_reachable.or(base.s_is_reachable),
    }
}

// ===========================================================================
// Environment state (createEnvironmentState) + variable data
// ===========================================================================

fn create_environment_state() -> InternalState {
    let mut state = new_internal_state();

    let spaceless = VariableState {
        variable_value: VariableValue {
            literal_value: None,
            space_status: SpaceStatus::SpaceStatusClean,
            numerical_status: NumericalStatus::NumericalStatusUnknown,
        },
        variable_properties: default_properties(),
    };
    let integer = VariableState {
        variable_value: unknown_integer_value(),
        variable_properties: default_properties(),
    };

    for name in INTERNAL_VARIABLES {
        state = insert_global(name, unknown_variable_state(), &state);
    }
    for name in VARIABLES_WITHOUT_SPACES {
        state = insert_global(name, spaceless.clone(), &state);
    }
    for name in SPECIAL_INTEGER_VARIABLES {
        state = insert_global(name, integer.clone(), &state);
    }
    state
}

// ===========================================================================
// The DFA context
// ===========================================================================

/// Whenever a function (or subshell) is invoked, an entry is pushed.
#[derive(Debug, Clone)]
struct StackEntry {
    entry_point: Node,
    is_function_call: bool,
    call_site: Node,
    dependencies: BTreeSet<StateDependency>,
    stack_state: InternalState,
}

type StateMap = BTreeMap<Node, (InternalState, InternalState)>;

/// Which environment fallback reader to use for a single-map merge.
#[derive(Clone, Copy)]
enum VReader {
    Global,
    Variable,
}

struct Ctx {
    node: Node,
    input: InternalState,
    output: InternalState,
    stack: Vec<StackEntry>,
    counter: i64,
    cache: HashMap<Node, Vec<(BTreeSet<StateDependency>, InternalState)>>,
    enable_cache: bool,
    invocations: HashMap<Vec<Node>, (BTreeSet<StateDependency>, StateMap)>,
    // Graph adjacency, derived from CFGraph.
    labels: HashMap<Node, CFNode>,
    pred_flow: HashMap<Node, Vec<Node>>,
    succ_all: HashMap<Node, Vec<Node>>,
}

impl Ctx {
    fn new(graph: &CFGraph) -> Ctx {
        let mut labels = HashMap::new();
        for (n, l) in &graph.nodes {
            labels.insert(*n, l.clone());
        }
        let mut pred_flow: HashMap<Node, Vec<Node>> = HashMap::new();
        let mut succ_all: HashMap<Node, Vec<Node>> = HashMap::new();
        for (from, to, e) in &graph.edges {
            succ_all.entry(*from).or_default().push(*to);
            if *e == CFEdge::CFEFlow {
                pred_flow.entry(*to).or_default().push(*from);
            }
        }
        Ctx {
            node: 0,
            input: new_internal_state(),
            output: new_internal_state(),
            stack: Vec::new(),
            counter: 1,
            cache: HashMap::new(),
            enable_cache: true,
            invocations: HashMap::new(),
            labels,
            pred_flow,
            succ_all,
        }
    }

    fn next_version(&mut self) -> i64 {
        let n = self.counter;
        self.counter += 1;
        n
    }

    fn version_map<V: Clone>(&mut self, mut m: VMap<V>) -> VMap<V> {
        if m.version >= 0 {
            m
        } else {
            m.version = self.next_version();
            m
        }
    }

    fn version_state(&mut self, mut state: InternalState) -> InternalState {
        if state.version >= 0 {
            return state;
        }
        let self_v = self.next_version();
        state.version = self_v;
        state.s_global_values = self.version_map(state.s_global_values);
        state.s_local_values = self.version_map(state.s_local_values);
        state.s_function_targets = self.version_map(state.s_function_targets);
        state
    }

    // --- stack lookups (lookupStack' / peekStack) ---

    fn lookup_stack<V, G, D>(&mut self, function_only: bool, get: G, make_dep: D, def: V) -> V
    where
        V: Clone,
        G: Fn(&InternalState) -> Option<V>,
        D: Fn(&V) -> StateDependency,
    {
        if let Some(v) = get(&self.input) {
            return v;
        }
        let mut idxs: Vec<usize> = Vec::new();
        let mut result = def;
        // The Haskell stack has the newest frame at the head; our Vec pushes the
        // newest frame at the end, so walk it in reverse (newest first).
        for i in (0..self.stack.len()).rev() {
            if function_only && self.stack[i].is_function_call {
                break;
            }
            idxs.push(i);
            if let Some(v) = get(&self.stack[i].stack_state) {
                result = v;
                break;
            }
        }
        for i in idxs {
            let d = make_dep(&result);
            self.stack[i].dependencies.insert(d);
        }
        result
    }

    fn read_variable_with_scope(&mut self, name: &str) -> (VariableState, Scope) {
        let key = name.to_string();
        self.lookup_stack(
            false,
            |s| get_variable_with_scope(s, &key),
            |v: &(VariableState, Scope)| StateDependency::DepState(v.1, key.clone(), v.0.clone()),
            (unknown_variable_state(), Scope::GlobalScope),
        )
    }
    fn read_variable_properties_with_scope(&mut self, name: &str) -> (VariableProperties, Scope) {
        let key = name.to_string();
        self.lookup_stack(
            false,
            |s| get_variable_with_scope(s, &key).map(|(val, sc)| (val.variable_properties, sc)),
            |v: &(VariableProperties, Scope)| {
                StateDependency::DepProperties(v.1, key.clone(), v.0.clone())
            },
            (default_properties(), Scope::GlobalScope),
        )
    }
    fn read_variable(&mut self, name: &str) -> VariableState {
        self.read_variable_with_scope(name).0
    }
    fn read_variable_scope(&mut self, name: &str) -> Scope {
        self.read_variable_properties_with_scope(name).1
    }
    fn read_global(&mut self, name: &str) -> VariableState {
        let key = name.to_string();
        self.lookup_stack(
            false,
            |s| s.s_global_values.lookup(&key).cloned(),
            |v: &VariableState| {
                StateDependency::DepState(Scope::GlobalScope, key.clone(), v.clone())
            },
            unknown_variable_state(),
        )
    }
    fn read_global_properties(&mut self, name: &str) -> VariableProperties {
        let key = name.to_string();
        self.lookup_stack(
            false,
            |s| {
                s.s_global_values
                    .lookup(&key)
                    .map(|vs| vs.variable_properties.clone())
            },
            |v: &VariableProperties| {
                StateDependency::DepProperties(Scope::GlobalScope, key.clone(), v.clone())
            },
            default_properties(),
        )
    }
    fn read_local(&mut self, name: &str) -> VariableState {
        let key = name.to_string();
        self.lookup_stack(
            true,
            |s| s.s_local_values.lookup(&key).cloned(),
            |v: &VariableState| {
                StateDependency::DepState(Scope::LocalScope, key.clone(), v.clone())
            },
            unset_variable_state(),
        )
    }
    fn read_local_properties(&mut self, name: &str) -> VariableProperties {
        let key = name.to_string();
        self.lookup_stack(
            true,
            |s| {
                if let Some(vs) = s.s_local_values.lookup(&key) {
                    Some((vs.variable_properties.clone(), Scope::LocalScope))
                } else {
                    s.s_prefix_values
                        .lookup(&key)
                        .map(|vs| (vs.variable_properties.clone(), Scope::PrefixScope))
                }
            },
            |v: &(VariableProperties, Scope)| {
                StateDependency::DepProperties(v.1, key.clone(), v.0.clone())
            },
            (default_properties(), Scope::LocalScope),
        )
        .0
    }
    fn read_function(&mut self, name: &str) -> FunctionValue {
        let key = name.to_string();
        self.lookup_stack(
            false,
            |s| s.s_function_targets.lookup(&key).cloned(),
            |v: &FunctionValue| StateDependency::DepFunction(key.clone(), v.clone()),
            unknown_function_value(),
        )
    }
    fn read_exit_codes(&mut self) -> BTreeSet<Id> {
        self.lookup_stack(
            false,
            |s| s.s_exit_codes.clone(),
            |v: &BTreeSet<Id>| StateDependency::DepExitCodes(v.clone()),
            BTreeSet::new(),
        )
    }

    // --- peek (no dependency) ---

    fn peek_var_with_scope(
        &self,
        name: &str,
        def: (VariableState, Scope),
    ) -> (VariableState, Scope) {
        if let Some(v) = get_variable_with_scope(&self.input, name) {
            return v;
        }
        for s in self.stack.iter().rev() {
            if let Some(v) = get_variable_with_scope(&s.stack_state, name) {
                return v;
            }
        }
        def
    }
    fn peek_func(&self, name: &str) -> FunctionValue {
        if let Some(v) = self.input.s_function_targets.lookup(name) {
            return v.clone();
        }
        for s in self.stack.iter().rev() {
            if let Some(v) = s.stack_state.s_function_targets.lookup(name) {
                return v.clone();
            }
        }
        unknown_function_value()
    }
    fn peek_exit_codes(&self) -> BTreeSet<Id> {
        if let Some(v) = &self.input.s_exit_codes {
            return v.clone();
        }
        for s in self.stack.iter().rev() {
            if let Some(v) = &s.stack_state.s_exit_codes {
                return v.clone();
            }
        }
        BTreeSet::new()
    }

    // --- writes ---

    fn write_global(&mut self, name: &str, val: VariableState) {
        self.output = insert_global(name, val, &self.output);
    }
    fn write_local(&mut self, name: &str, val: VariableState) {
        self.output = insert_local(name, val, &self.output);
    }
    fn write_prefix(&mut self, name: &str, val: VariableState) {
        self.output = insert_prefix(name, val, &self.output);
    }
    fn write_function(&mut self, name: &str, val: FunctionDefinition) {
        let mut set = BTreeSet::new();
        set.insert(val);
        self.output = insert_function(name, set, &self.output);
    }
    fn write_variable(&mut self, name: &str, val: VariableState) {
        match self.read_variable_scope(name) {
            Scope::GlobalScope => self.write_global(name, val),
            Scope::LocalScope => self.write_local(name, val),
            // Prefixed variables actually become local variables.
            Scope::PrefixScope => self.write_local(name, val),
        }
    }
    fn update_variable_value(&mut self, name: &str, val: VariableValue) {
        let (props, scope) = self.read_variable_properties_with_scope(name);
        let vs = VariableState {
            variable_value: val,
            variable_properties: props,
        };
        match scope {
            Scope::GlobalScope => self.write_global(name, vs),
            Scope::LocalScope => self.write_local(name, vs),
            Scope::PrefixScope => self.write_local(name, vs),
        }
    }
    fn update_global_value(&mut self, name: &str, val: VariableValue) {
        let props = self.read_global_properties(name);
        self.write_global(
            name,
            VariableState {
                variable_value: val,
                variable_properties: props,
            },
        );
    }
    fn update_local_value(&mut self, name: &str, val: VariableValue) {
        let props = self.read_local_properties(name);
        self.write_local(
            name,
            VariableState {
                variable_value: val,
                variable_properties: props,
            },
        );
    }
    fn update_prefix_value(&mut self, name: &str, val: VariableValue) {
        self.write_prefix(
            name,
            VariableState {
                variable_value: val,
                variable_properties: default_properties(),
            },
        );
    }
    fn undefine_variable(&mut self, name: &str) {
        self.write_variable(name, unset_variable_state());
    }
    fn undefine_function(&mut self, name: &str) {
        self.write_function(name, FunctionDefinition::FunctionUnknown);
    }
}

impl Ctx {
    // --- value abstraction ---

    fn cf_value_to_variable_value(&mut self, val: &CFValue) -> VariableValue {
        match val {
            CFValue::CFValueArray => unknown_variable_value(),
            CFValue::CFValueComputed(_, parts) => {
                let mut acc = empty_variable_value();
                for part in parts {
                    let next = self.compute_value(part);
                    acc = append_variable_value(&acc, &next);
                }
                acc
            }
            CFValue::CFValueInteger => unknown_integer_value(),
            CFValue::CFValueString => unknown_variable_value(),
            CFValue::CFValueUninitialized => empty_variable_value(),
        }
    }

    fn compute_value(&mut self, part: &CFStringPart) -> VariableValue {
        match part {
            CFStringPart::CFStringLiteral(str) => literal_to_variable_value(str),
            CFStringPart::CFStringInteger => unknown_integer_value(),
            CFStringPart::CFStringUnknown => unknown_variable_value(),
            CFStringPart::CFStringVariable(name) => {
                let state = self.read_variable(name);
                let all_int = state
                    .variable_properties
                    .iter()
                    .all(|s| s.contains(&CFVariableProp::CFVPInteger));
                if all_int {
                    unknown_integer_value()
                } else {
                    state.variable_value
                }
            }
        }
    }

    // --- effect transfer ---

    fn transfer_effect(&mut self, effect: &CFEffect) {
        match effect {
            CFEffect::CFReadVariable(name) => {
                if name == "?" {
                    let _ = self.read_exit_codes();
                } else {
                    let _ = self.read_variable(name);
                }
            }
            CFEffect::CFWriteVariable(name, value) => {
                let val = self.cf_value_to_variable_value(value);
                self.update_variable_value(name, val);
            }
            CFEffect::CFWriteGlobal(name, value) => {
                let val = self.cf_value_to_variable_value(value);
                self.update_global_value(name, val);
            }
            CFEffect::CFWriteLocal(name, value) => {
                let val = self.cf_value_to_variable_value(value);
                self.update_local_value(name, val);
            }
            CFEffect::CFWritePrefix(name, value) => {
                let val = self.cf_value_to_variable_value(value);
                self.update_prefix_value(name, val);
            }
            CFEffect::CFSetProps(scope, name, props) => match scope {
                None => {
                    let state = self.read_variable(name);
                    self.write_variable(name, add_properties(props, &state));
                }
                Some(Scope::GlobalScope) => {
                    let state = self.read_global(name);
                    self.write_global(name, add_properties(props, &state));
                }
                Some(Scope::LocalScope) => {
                    let state = self.read_local(name);
                    self.write_local(name, add_properties(props, &state));
                }
                Some(Scope::PrefixScope) => {
                    let state = self.read_local(name);
                    self.write_local(name, add_properties(props, &state));
                }
            },
            CFEffect::CFUnsetProps(scope, name, props) => match scope {
                None => {
                    let state = self.read_variable(name);
                    self.write_variable(name, remove_properties(props, &state));
                }
                Some(Scope::GlobalScope) => {
                    let state = self.read_global(name);
                    self.write_global(name, remove_properties(props, &state));
                }
                Some(Scope::LocalScope) => {
                    let state = self.read_local(name);
                    self.write_local(name, remove_properties(props, &state));
                }
                Some(Scope::PrefixScope) => {
                    let state = self.read_local(name);
                    self.write_local(name, remove_properties(props, &state));
                }
            },
            CFEffect::CFUndefineVariable(name) => self.undefine_variable(name),
            CFEffect::CFUndefineFunction(name) => self.undefine_function(name),
            CFEffect::CFUndefine(name) => {
                self.undefine_variable(name);
                self.undefine_function(name);
            }
            CFEffect::CFDefineFunction(name, _id, entry, exit) => {
                self.write_function(
                    name,
                    FunctionDefinition::FunctionDefinition(name.clone(), *entry, *exit),
                );
            }
            CFEffect::CFUndefineNameref(name) => self.undefine_variable(name),
            CFEffect::CFHintArray(_) => {}
            CFEffect::CFHintDefined(_) => {}
        }
    }

    // --- merges (join) ---

    fn merge_maps_var(
        &mut self,
        kind: VReader,
        a: &VMap<VariableState>,
        b: &VMap<VariableState>,
    ) -> VMap<VariableState> {
        if vm_is_quick_equal(a, b) {
            return a.clone();
        }
        let keys: BTreeSet<String> = a.storage.keys().chain(b.storage.keys()).cloned().collect();
        let mut out = BTreeMap::new();
        for k in keys {
            let merged = match (a.storage.get(&k), b.storage.get(&k)) {
                (Some(x), Some(y)) => merge_variable_state(x, y),
                (Some(x), None) => {
                    let other = match kind {
                        VReader::Global => self.read_global(&k),
                        VReader::Variable => self.read_variable(&k),
                    };
                    merge_variable_state(x, &other)
                }
                (None, Some(y)) => {
                    let other = match kind {
                        VReader::Global => self.read_global(&k),
                        VReader::Variable => self.read_variable(&k),
                    };
                    merge_variable_state(&other, y)
                }
                (None, None) => unreachable!(),
            };
            out.insert(k, merged);
        }
        VMap {
            version: -1,
            storage: out,
        }
    }

    fn merge_maps_func(
        &mut self,
        a: &VMap<FunctionValue>,
        b: &VMap<FunctionValue>,
    ) -> VMap<FunctionValue> {
        if vm_is_quick_equal(a, b) {
            return a.clone();
        }
        let keys: BTreeSet<String> = a.storage.keys().chain(b.storage.keys()).cloned().collect();
        let mut out = BTreeMap::new();
        for k in keys {
            let merged = match (a.storage.get(&k), b.storage.get(&k)) {
                (Some(x), Some(y)) => x.union(y).cloned().collect(),
                (Some(x), None) => {
                    let other = self.read_function(&k);
                    x.union(&other).cloned().collect()
                }
                (None, Some(y)) => {
                    let other = self.read_function(&k);
                    other.union(y).cloned().collect()
                }
                (None, None) => unreachable!(),
            };
            out.insert(k, merged);
        }
        VMap {
            version: -1,
            storage: out,
        }
    }

    fn merge_maybes_exit(
        &mut self,
        a: &Option<BTreeSet<Id>>,
        b: &Option<BTreeSet<Id>>,
    ) -> Option<BTreeSet<Id>> {
        match (a, b) {
            (None, None) => None,
            (Some(v1), None) => {
                let r = self.read_exit_codes();
                Some(v1.union(&r).cloned().collect())
            }
            (None, Some(v2)) => {
                let r = self.read_exit_codes();
                Some(v2.union(&r).cloned().collect())
            }
            (Some(v1), Some(v2)) => Some(v1.union(v2).cloned().collect()),
        }
    }

    fn merge_state(&mut self, a: &InternalState, b: &InternalState) -> InternalState {
        // Kludge: temporarily blank the input so readVariable & friends don't
        // read from an intermediate state.
        let old = std::mem::replace(&mut self.input, new_internal_state());
        let x = self.do_merge(a, b);
        self.input = old;
        x
    }

    fn do_merge(&mut self, a: &InternalState, b: &InternalState) -> InternalState {
        match (a.s_is_reachable, b.s_is_reachable) {
            (Some(true), Some(false)) | (Some(false), Some(true)) => {
                panic!(
                    "ShellCheck internal error: Unexpected merge of reachable and unreachable state"
                );
            }
            (Some(false), Some(false)) => return unreachable_state(),
            _ => {}
        }
        if a.version >= 0 && b.version >= 0 && a.version == b.version {
            return a.clone();
        }
        let globals = self.merge_maps_var(VReader::Global, &a.s_global_values, &b.s_global_values);
        let locals = self.merge_maps_var(VReader::Variable, &a.s_local_values, &b.s_local_values);
        let prefix = self.merge_maps_var(VReader::Variable, &a.s_prefix_values, &b.s_prefix_values);
        let funcs = self.merge_maps_func(&a.s_function_targets, &b.s_function_targets);
        let exit = self.merge_maybes_exit(&a.s_exit_codes, &b.s_exit_codes);
        let reach = match (a.s_is_reachable, b.s_is_reachable) {
            (Some(x), Some(y)) => Some(x && y),
            _ => None,
        };
        InternalState {
            version: -1,
            s_global_values: globals,
            s_local_values: locals,
            s_prefix_values: prefix,
            s_function_targets: funcs,
            s_exit_codes: exit,
            s_is_reachable: reach,
        }
    }

    fn merge_states(&mut self, def: InternalState, list: &[InternalState]) -> InternalState {
        if list.is_empty() {
            return def;
        }
        let mut acc = list[0].clone();
        for x in &list[1..] {
            acc = self.merge_state(&acc, x);
        }
        acc
    }
    fn merge_states_nonempty(&mut self, list: &[InternalState]) -> InternalState {
        let mut acc = list[0].clone();
        for x in &list[1..] {
            acc = self.merge_state(&acc, x);
        }
        acc
    }

    // --- stack frame management ---

    fn patch_output(&mut self, diff: &InternalState) {
        self.output = patch_state(&self.output, diff);
    }

    fn with_new_stack_frame<R>(
        &mut self,
        node: Node,
        is_call: bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> (R, StackEntry) {
        let call_site = self.node;
        let state = self.output.clone();
        let entry = StackEntry {
            entry_point: node,
            is_function_call: is_call,
            call_site,
            dependencies: BTreeSet::new(),
            stack_state: state,
        };
        let saved_input = std::mem::replace(&mut self.input, new_internal_state());
        let saved_output = std::mem::replace(&mut self.output, new_internal_state());
        let saved_node = self.node;
        self.node = node;
        self.stack.push(entry);
        let x = f(self);
        let new_entry = self.stack.pop().unwrap();
        self.input = saved_input;
        self.output = saved_output;
        self.node = saved_node;
        (x, new_entry)
    }

    fn would_be_recursive(&mut self, node: Node) -> bool {
        let mut idxs: Vec<usize> = Vec::new();
        let mut res = false;
        for i in (0..self.stack.len()).rev() {
            idxs.push(i);
            if self.stack[i].entry_point == node {
                res = true;
                break;
            }
        }
        for i in idxs {
            self.stack[i]
                .dependencies
                .insert(StateDependency::DepIsRecursive(node, res));
        }
        res
    }

    fn register_flow_result(
        &mut self,
        entry: Node,
        states: &StateMap,
        deps: &BTreeSet<StateDependency>,
    ) {
        let current = self.node;
        let mut path = vec![entry, current];
        for s in self.stack.iter().rev() {
            path.push(s.call_site);
        }
        self.invocations
            .insert(path, (deps.clone(), states.clone()));
    }

    // --- cache ---

    fn fulfills_dependency(&self, entry: Node, dep: &StateDependency) -> bool {
        match dep {
            StateDependency::DepState(scope, name, val) => {
                let def = if *scope == Scope::GlobalScope {
                    (unknown_variable_state(), Scope::GlobalScope)
                } else {
                    (unset_variable_state(), Scope::LocalScope)
                };
                self.peek_var_with_scope(name, def) == (val.clone(), *scope)
            }
            StateDependency::DepProperties(scope, name, props) => {
                let def = if *scope == Scope::GlobalScope {
                    (unknown_variable_state(), Scope::GlobalScope)
                } else {
                    (unset_variable_state(), Scope::LocalScope)
                };
                let (state, s) = self.peek_var_with_scope(name, def);
                *scope == s && state.variable_properties == *props
            }
            StateDependency::DepFunction(name, val) => self.peek_func(name) == *val,
            StateDependency::DepIsRecursive(node, val) => {
                if *node == entry {
                    true
                } else {
                    *val == self.stack.iter().any(|f| f.entry_point == *node)
                }
            }
            StateDependency::DepExitCodes(val) => self.peek_exit_codes() == *val,
        }
    }

    fn fulfills_dependencies(&self, entry: Node, deps: &BTreeSet<StateDependency>) -> bool {
        deps.iter().all(|d| self.fulfills_dependency(entry, d))
    }

    fn get_cache(&mut self, node: Node) -> Option<InternalState> {
        if !self.enable_cache {
            return None;
        }
        let entries = self.cache.get(&node).cloned().unwrap_or_default();
        for (deps, value) in entries {
            if self.fulfills_dependencies(node, &deps) {
                return Some(value);
            }
        }
        None
    }

    fn run_cached(
        &mut self,
        node: Node,
        f: impl FnOnce(&mut Self) -> (BTreeSet<StateDependency>, InternalState),
    ) {
        match self.get_cache(node) {
            Some(v) => {
                self.patch_output(&v);
            }
            None => {
                let (deps, diff) = f(self);
                let old = self.cache.remove(&node).unwrap_or_default();
                let mut newlist = vec![(deps, diff.clone())];
                newlist.extend(old.into_iter().take(CACHE_ENTRIES));
                self.cache.insert(node, newlist);
                self.patch_output(&diff);
            }
        }
    }

    // --- transfer ---

    fn transfer(&mut self, label: &CFNode) {
        match label {
            CFNode::CFStructuralNode
            | CFNode::CFEntryPoint(_)
            | CFNode::CFImpliedExit
            | CFNode::CFResolvedExit => {}
            CFNode::CFExecuteCommand(cmd) => self.transfer_command(cmd.clone()),
            CFNode::CFExecuteSubshell(_reason, entry, exit) => {
                self.transfer_subshell(*entry, *exit)
            }
            CFNode::CFApplyEffects(effects) => {
                for e in effects {
                    self.transfer_effect(&e.value);
                }
            }
            CFNode::CFSetExitCode(id) => {
                self.output = set_exit_code(*id, &self.output);
            }
            CFNode::CFUnresolvedExit => self.patch_output(&unreachable_state()),
            CFNode::CFUnreachable => self.patch_output(&unreachable_state()),
            CFNode::CFSetBackgroundPid(_) => {}
            CFNode::CFDropPrefixAssignments => {
                let mut c = self.output.clone();
                c.s_prefix_values = VMap::empty();
                self.output = modified(c);
            }
        }
    }

    fn transfer_subshell(&mut self, entry: Node, exit: Node) {
        let initial = self.output.clone();
        self.run_cached(entry, move |s| s.subshell_recompute(entry, exit));
        let res_exit = self.output.s_exit_codes.clone();
        let mut newout = initial;
        newout.s_exit_codes = res_exit;
        self.output = newout;
    }

    fn subshell_recompute(
        &mut self,
        entry: Node,
        exit: Node,
    ) -> (BTreeSet<StateDependency>, InternalState) {
        let (states, frame) = self.with_new_stack_frame(entry, false, |s| s.dataflow(entry));
        let res = states
            .get(&exit)
            .map(|x| x.1.clone())
            .expect("ShellCheck internal error: Subshell has no exit");
        let deps = frame.dependencies;
        self.register_flow_result(entry, &states, &deps);
        (deps, res)
    }

    fn transfer_command(&mut self, name: Option<String>) {
        let name = match name {
            Some(n) => n,
            None => return,
        };
        let targets = self.read_function(&name);
        let funcs: Vec<FunctionDefinition> = targets.into_iter().collect();
        self.transfer_multiple(&funcs);
    }

    fn transfer_multiple(&mut self, funcs: &[FunctionDefinition]) {
        let original = self.output.clone();
        let mut branches = Vec::new();
        for f in funcs {
            self.output = original.clone();
            self.transfer_function_value(f);
            branches.push(self.output.clone());
        }
        let merged = self.merge_states(original.clone(), &branches);
        let patched = patch_state(&original, &merged);
        self.output = patched;
    }

    fn transfer_function_value(&mut self, fv: &FunctionDefinition) {
        match fv {
            FunctionDefinition::FunctionUnknown => {}
            FunctionDefinition::FunctionDefinition(_name, entry, exit) => {
                let (entry, exit) = (*entry, *exit);
                let is_recursive = self.would_be_recursive(entry);
                if is_recursive {
                    // TODO: Find a better strategy for recursion
                } else {
                    self.run_cached(entry, move |s| s.tfv_recompute(entry, exit));
                }
            }
        }
    }

    fn tfv_recompute(
        &mut self,
        entry: Node,
        exit: Node,
    ) -> (BTreeSet<StateDependency>, InternalState) {
        let (states, frame) = self.with_new_stack_frame(entry, true, |s| s.dataflow(entry));
        let deps = frame.dependencies;
        let res = match states.get(&exit) {
            Some((_input, output)) => {
                // Discard local variables.
                let mut o = output.clone();
                o.s_local_values = VMap::empty();
                modified(o)
            }
            None => unreachable_state(),
        };
        self.register_flow_result(entry, &states, &deps);
        (deps, res)
    }

    // --- the iterative DFA ---

    fn process(&mut self, states: &mut StateMap, node: Node) -> Vec<Node> {
        let incoming = self.pred_flow.get(&node).cloned().unwrap_or_default();
        let outgoing = self.succ_all.get(&node).cloned().unwrap_or_default();
        let label = self
            .labels
            .get(&node)
            .cloned()
            .unwrap_or(CFNode::CFStructuralNode);

        let inputs: Vec<InternalState> = incoming
            .iter()
            .filter_map(|c| states.get(c).map(|x| x.1.clone()))
            .filter(|c| c.s_is_reachable != Some(false))
            .collect();
        let input = if incoming.is_empty() {
            new_internal_state()
        } else if inputs.is_empty() {
            unreachable_state()
        } else {
            let mut it = inputs.into_iter();
            let mut acc = it.next().unwrap();
            for x in it {
                acc = self.merge_state(&acc, &x);
            }
            acc
        };

        self.input = input.clone();
        self.output = input.clone();
        self.node = node;
        self.transfer(&label);
        let new_output = self.output.clone();
        let result = if outgoing.len() >= 2 {
            self.version_state(new_output)
        } else {
            new_output
        };
        let old = states.get(&node).cloned();
        states.insert(node, (input, result.clone()));
        match old {
            None => outgoing,
            Some((_, old_output)) => {
                if state_eq(&old_output, &result) {
                    Vec::new()
                } else {
                    outgoing
                }
            }
        }
    }

    fn dataflow(&mut self, entry: Node) -> StateMap {
        let mut pending: BTreeSet<Node> = BTreeSet::new();
        pending.insert(entry);
        let mut states: StateMap = BTreeMap::new();
        let saved_in = self.input.clone();
        let saved_out = self.output.clone();
        let mut n = ITERATION_COUNT;
        loop {
            if n == 0 {
                panic!("ShellCheck internal error: DFA did not reach fix point");
            }
            if n == FALLBACK_THRESHOLD {
                self.enable_cache = false;
            }
            let next = match pending.iter().next().copied() {
                Some(x) => x,
                None => break,
            };
            pending.remove(&next);
            let nexts = self.process(&mut states, next);
            for x in nexts {
                pending.insert(x);
            }
            n -= 1;
        }
        self.input = saved_in;
        self.output = saved_out;
        states
    }

    fn run_root(&mut self, env: InternalState, entry: Node, exit: Node) -> InternalState {
        self.input = env.clone();
        self.output = env;
        self.node = entry;
        let (states, frame) = self.with_new_stack_frame(entry, false, |s| s.dataflow(entry));
        let deps = frame.dependencies;
        self.register_flow_result(entry, &states, &deps);
        states
            .get(&exit)
            .map(|x| x.1.clone())
            .expect("ShellCheck internal error: Missing exit state")
    }

    fn analyze_stragglers(&mut self, state: &InternalState, stragglers: &[FunctionDefinition]) {
        for def in stragglers {
            self.input = state.clone();
            self.output = state.clone();
            if let FunctionDefinition::FunctionDefinition(_, entry, _) = def {
                self.node = *entry;
            }
            self.transfer_function_value(def);
        }
    }
}

// ===========================================================================
// Top-level orchestration helpers
// ===========================================================================

fn insert_in(
    overwrite: bool,
    scope: Scope,
    name: &str,
    val: VariableState,
    state: &InternalState,
) -> InternalState {
    let exists = match scope {
        Scope::PrefixScope => state.s_prefix_values.lookup(name).is_some(),
        Scope::LocalScope => state.s_local_values.lookup(name).is_some(),
        Scope::GlobalScope => state.s_global_values.lookup(name).is_some(),
    };
    if overwrite || !exists {
        match scope {
            Scope::PrefixScope => insert_prefix(name, val, state),
            Scope::LocalScope => insert_local(name, val, state),
            Scope::GlobalScope => insert_global(name, val, state),
        }
    } else {
        state.clone()
    }
}

/// Create an InternalState that fulfills the given dependencies.
fn deps_to_state(deps: &BTreeSet<StateDependency>) -> InternalState {
    let mut state = new_internal_state();
    for dep in deps {
        state = match dep {
            StateDependency::DepFunction(name, val) => insert_function(name, val.clone(), &state),
            StateDependency::DepState(scope, name, val) => {
                insert_in(true, *scope, name, val.clone(), &state)
            }
            StateDependency::DepProperties(scope, name, props) => {
                let vs = VariableState {
                    variable_value: unknown_variable_value(),
                    variable_properties: props.clone(),
                };
                insert_in(false, *scope, name, vs, &state)
            }
            StateDependency::DepIsRecursive(_, _) => state,
            StateDependency::DepExitCodes(s) => set_exit_codes(s.clone(), &state),
        };
    }
    state
}

/// Get all the functions defined in an InternalState (keyed by entry node).
fn get_function_targets(state: &InternalState) -> BTreeMap<Node, FunctionDefinition> {
    let mut out = BTreeMap::new();
    for val in state.s_function_targets.storage.values() {
        for d in val {
            if let FunctionDefinition::FunctionDefinition(_, entry, _) = d {
                out.insert(*entry, d.clone());
            }
        }
    }
    out
}

fn internal_to_external(s: &InternalState) -> ProgramState {
    // M.unions [prefix, local, global] is left-biased (prefix wins).
    let mut flat: BTreeMap<String, VariableState> = BTreeMap::new();
    for (k, v) in &s.s_global_values.storage {
        flat.insert(k.clone(), v.clone());
    }
    for (k, v) in &s.s_local_values.storage {
        flat.insert(k.clone(), v.clone());
    }
    for (k, v) in &s.s_prefix_values.storage {
        flat.insert(k.clone(), v.clone());
    }
    // Censor the literal value to avoid introducing dependencies on it.
    for v in flat.values_mut() {
        v.variable_value.literal_value = None;
    }
    ProgramState {
        variables_in_scope: flat,
        exit_codes: s.s_exit_codes.clone().unwrap_or_default(),
        state_is_reachable: s.s_is_reachable.unwrap_or(true),
    }
}

fn node_range(g: &CFGraph) -> (Node, Node) {
    let mut mn = usize::MAX;
    let mut mx = 0usize;
    for (n, _) in &g.nodes {
        if *n < mn {
            mn = *n;
        }
        if *n > mx {
            mx = *n;
        }
    }
    (mn, mx)
}

/// The abstract-interpretation entry point (Haskell `analyzeControlFlow`).
pub fn analyze_control_flow(params: &CFGParameters, t: &Token) -> CFGAnalysis {
    let cfg = build_graph(*params, t);
    let (entry, exit) = *cfg
        .cf_id_to_range
        .get(&t.id)
        .expect("ShellCheck internal error: Missing root");

    let mut ctx = Ctx::new(&cfg.cf_graph);
    let env = create_environment_state();

    // Do a dataflow analysis starting on the root node.
    let exit_state = ctx.run_root(env.clone(), entry, exit);

    // All nodes we've touched.
    let mut invoked_nodes: BTreeSet<Node> = BTreeSet::new();
    for (_, m) in ctx.invocations.values() {
        for k in m.keys() {
            invoked_nodes.insert(*k);
        }
    }

    // Invoke all functions that were declared but not invoked (dead-code warnings).
    let declared = get_function_targets(&exit_state);
    let uninvoked: Vec<FunctionDefinition> = declared
        .iter()
        .filter(|(k, _)| !invoked_nodes.contains(*k))
        .map(|(_, v)| v.clone())
        .collect();

    let straggler_input = {
        let mut s = patch_state(&env, &exit_state);
        s.s_exit_codes = None;
        s
    };
    ctx.analyze_stragglers(&straggler_input, &uninvoked);

    // Round up all the states from all data flows.
    // groupByNode ∘ addDeps
    let mut grouped: BTreeMap<Node, Vec<(InternalState, InternalState)>> = BTreeMap::new();
    let invocations: Vec<(BTreeSet<StateDependency>, StateMap)> =
        ctx.invocations.values().cloned().collect();
    for (deps, m) in &invocations {
        let base = deps_to_state(deps);
        for (node, (a, b)) in m {
            let pa = patch_state(&base, a);
            let pb = patch_state(&base, b);
            grouped.entry(*node).or_default().push((pa, pb));
        }
    }

    // flattenByNode: merge all pre/post states per node.
    let mut invoked_states: StateMap = BTreeMap::new();
    for (node, list) in grouped {
        let pres: Vec<InternalState> = list.iter().map(|x| x.0.clone()).collect();
        let posts: Vec<InternalState> = list.iter().map(|x| x.1.clone()).collect();
        let pre = ctx.merge_states_nonempty(&pres);
        let post = ctx.merge_states_nonempty(&posts);
        invoked_states.insert(node, (pre, post));
    }

    // Fill in unreachable states for anything we didn't get to.
    let (mn, mx) = node_range(&cfg.cf_graph);
    let mut all_states: StateMap = BTreeMap::new();
    for n in mn..=mx {
        all_states.insert(n, (unreachable_state(), unreachable_state()));
    }
    for (n, v) in invoked_states {
        all_states.insert(n, v); // invoked wins
    }

    let mut node_to_data: HashMap<Node, (ProgramState, ProgramState)> = HashMap::new();
    for (n, (a, b)) in &all_states {
        node_to_data.insert(*n, (internal_to_external(a), internal_to_external(b)));
    }

    CFGAnalysis {
        graph: cfg.cf_graph,
        token_to_range: cfg.cf_id_to_range,
        token_to_nodes: cfg.cf_id_to_nodes,
        post_dominators: cfg.cf_post_dominators,
        node_to_data,
    }
}

// ===========================================================================
// Tests
//
// NB: CFGAnalysis.hs itself defines NO `prop_` tests (its `$quickCheckAll`
// collects zero properties — the checks that consume this analysis, e.g.
// SC2154/SC2086/SC2034, carry the prop_ tests, in Analytics.hs). These tests
// therefore exercise the ported abstract interpretation directly against the
// documented lattice semantics, via a faithful parse+analyze helper.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::InnerToken;
    use crate::parser::parse_script;

    fn analyze(src: &str) -> (CFGAnalysis, Token) {
        let out = parse_script("test.sh", src);
        let root = out.root.expect("parse produced a root");
        let params = CFGParameters {
            cf_lastpipe: false,
            cf_pipefail: false,
        };
        let a = analyze_control_flow(&params, &root);
        (a, root)
    }

    fn outgoing(src: &str) -> ProgramState {
        let (a, root) = analyze(src);
        a.get_outgoing_state(root.id)
            .expect("root has an outgoing state")
    }

    fn collect<'a>(t: &'a Token, out: &mut Vec<&'a Token>) {
        out.push(t);
        for c in t.children() {
            collect(c, out);
        }
    }

    /// Find the id of the first assignment to `var`.
    fn assignment_id(root: &Token, var: &str) -> Id {
        let mut all = Vec::new();
        collect(root, &mut all);
        for t in all {
            if let InnerToken::T_Assignment { var: v, .. } = &*t.inner {
                if v == var {
                    return t.id;
                }
            }
        }
        panic!("no assignment to {}", var);
    }

    /// Find ids of simple commands whose first literal word is `name`.
    fn command_ids(root: &Token, name: &str) -> Vec<Id> {
        let mut all = Vec::new();
        collect(root, &mut all);
        let mut out = Vec::new();
        for t in all {
            if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
                if let Some(w) = words.first() {
                    if crate::astlib::get_literal_string(w).as_deref() == Some(name) {
                        out.push(t.id);
                    }
                }
            }
        }
        out
    }

    #[test]
    fn clean_literal_assignment() {
        let st = outgoing("x=hello\n");
        assert_eq!(st.space_status("x"), Some(SpaceStatus::SpaceStatusClean));
        assert_eq!(
            st.numerical_status("x"),
            Some(NumericalStatus::NumericalStatusUnknown)
        );
    }

    #[test]
    fn integer_literal_assignment() {
        let st = outgoing("x=1\n");
        assert_eq!(st.space_status("x"), Some(SpaceStatus::SpaceStatusClean));
        assert_eq!(
            st.numerical_status("x"),
            Some(NumericalStatus::NumericalStatusDefinitely)
        );
        assert_eq!(st.variable_may_be_assigned_integer("x"), Some(true));
    }

    #[test]
    fn dirty_literal_assignment() {
        let st = outgoing("x='a b'\n");
        assert_eq!(st.space_status("x"), Some(SpaceStatus::SpaceStatusDirty));
        assert_eq!(st.variable_may_be_assigned_integer("x"), Some(false));
    }

    #[test]
    fn concatenation_space_status() {
        // "$x/literal" — x is dirty (unknown) so the whole is dirty.
        let st = outgoing("x=$1\ny=\"$x/foo\"\n");
        assert_eq!(st.space_status("y"), Some(SpaceStatus::SpaceStatusDirty));
    }

    #[test]
    fn unset_variable_becomes_empty() {
        let st = outgoing("x=1\nunset x\n");
        // undefineVariable resets to unsetVariableState (empty value).
        assert_eq!(st.space_status("x"), Some(SpaceStatus::SpaceStatusEmpty));
    }

    #[test]
    fn declare_integer_property() {
        let st = outgoing("declare -i x=5\n");
        assert_eq!(st.variable_may_be_declared_integer("x"), Some(true));
    }

    #[test]
    fn plain_assignment_not_declared_integer() {
        let st = outgoing("x=5\n");
        assert_eq!(st.variable_may_be_declared_integer("x"), Some(false));
    }

    #[test]
    fn function_global_side_effect() {
        // Calling f must propagate its global assignment to the caller.
        let st = outgoing("f() { g=5; }\nf\n");
        assert_eq!(
            st.numerical_status("g"),
            Some(NumericalStatus::NumericalStatusDefinitely)
        );
    }

    #[test]
    fn local_does_not_leak() {
        // A local variable in a function must not appear in the caller's scope.
        let st = outgoing("f() { local secret=1; }\nf\n");
        assert!(st.variables_in_scope().get("secret").is_none());
    }

    #[test]
    fn environment_variable_abstraction() {
        // Unwritten environment variables live in the stack, not node states,
        // so they are not listed in variablesInScope. But reading one flows its
        // abstraction: UID is spaceless (clean) in the environment, so `y=$UID`
        // yields a clean y, whereas an unknown var ($1) yields a dirty one.
        let st = outgoing("y=$UID\nz=$1\n");
        assert_eq!(st.space_status("y"), Some(SpaceStatus::SpaceStatusClean));
        assert_eq!(st.space_status("z"), Some(SpaceStatus::SpaceStatusDirty));
    }

    #[test]
    fn unreachable_after_exit() {
        let (a, root) = analyze("exit\nx=1\n");
        let id = assignment_id(&root, "x");
        let incoming = a.get_incoming_state(id).expect("has incoming state");
        assert!(!incoming.state_is_reachable());
    }

    #[test]
    fn reachable_normal_flow() {
        let (a, root) = analyze("x=1\n");
        let id = assignment_id(&root, "x");
        let incoming = a.get_incoming_state(id).expect("has incoming state");
        assert!(incoming.state_is_reachable());
    }

    #[test]
    fn post_domination_sequential() {
        // In `echo a; echo b`, the second command post-dominates the first.
        let (a, root) = analyze("echo a\necho b\n");
        let as_ = command_ids(&root, "echo");
        assert_eq!(as_.len(), 2);
        let (first, second) = (as_[0], as_[1]);
        assert!(a.does_post_dominate(second, first));
        // ... but the first does not post-dominate the second.
        assert!(!a.does_post_dominate(first, second));
    }

    #[test]
    fn post_domination_conditional() {
        // The body of an `if` does not post-dominate the condition.
        let (a, root) = analyze("if true\nthen\n  echo cond\nfi\necho after\n");
        let cond = command_ids(&root, "echo")[0];
        let after = command_ids(&root, "echo")[1];
        // `after` runs unconditionally after the conditional body.
        assert!(a.does_post_dominate(after, cond));
        assert!(!a.does_post_dominate(cond, after));
    }

    #[test]
    fn merge_of_branches() {
        // x is 1 on one branch, "a b" on the other -> dirty.
        let st = outgoing("if true; then x=1; else x='a b'; fi\n");
        assert_eq!(st.space_status("x"), Some(SpaceStatus::SpaceStatusDirty));
        // numeric: Definitely merged with Unknown -> Maybe (>= Maybe).
        assert_eq!(st.variable_may_be_assigned_integer("x"), Some(true));
    }
}
