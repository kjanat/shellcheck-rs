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

use crate::idhash::IdMap;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use im_rc::OrdMap;
use im_rc::ordmap::DiffItem;

use crate::ast::{Id, Token};
use crate::cfg::{
    CFEdge, CFEffect, CFGParameters, CFGraph, CFNode, CFStringPart, CFValue, CFVariableProp,
    InternalError, Node, Scope, build_graph,
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
    /// The value is empty.
    SpaceStatusEmpty,
    /// The value has no spaces or globs.
    SpaceStatusClean,
    /// The value may have spaces or globs.
    SpaceStatusDirty,
}

/// Whether or not the value is an integer, or we don't know.
///
/// Declaration order is the Haskell `Ord` order and must not change
/// (`variableMayBeAssignedInteger` relies on `>= NumericalStatusMaybe`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumericalStatus {
    /// Nothing is known about the value.
    NumericalStatusUnknown,
    /// The value is empty.
    NumericalStatusEmpty,
    /// The value may be an integer.
    NumericalStatusMaybe,
    /// The value is an integer.
    NumericalStatusDefinitely,
}

/// The set of possible sets of properties for this variable.
pub type VariableProperties = BTreeSet<BTreeSet<CFVariableProp>>;

/// The information about the value of a single variable.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableValue {
    /// For debugging only; censored to `None` in externally exposed states.
    pub literal_value: Option<String>,
    /// Whether the value needs quoting.
    pub space_status: SpaceStatus,
    /// Whether the value is an integer.
    pub numerical_status: NumericalStatus,
}

/// A variable's value and properties (`data VariableState`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VariableState {
    /// The variable's value.
    pub variable_value: VariableValue,
    /// The variable's possible property sets.
    pub variable_properties: VariableProperties,
}

/// The program state we expose externally.
///
/// Haskell builds a flat `variablesInScope` map per node (`internalToExternal`);
/// here the three scope maps are shared with the analysis states (cloning them
/// is O(1)) and a lookup resolves them by scope precedence, prefix over local
/// over global, which is what `M.unions [prefix, local, global]` does. The
/// literal value is censored when it is read out, as `internalToExternal` does.
///
/// Each scope map may carry a second layer: the dependency base of the
/// invocation the node was analysed in (`addDeps`). A node reached by one
/// invocation only does not materialise `patchState base s`; its scope maps
/// are `s`'s over the base's, resolved at lookup, so a lookup answers what the
/// patched state would.
#[derive(Debug, Clone)]
pub struct ProgramState {
    global_values: ScopeValues,
    local_values: ScopeValues,
    prefix_values: ScopeValues,
    /// The tokens whose exit code `$?` may hold.
    pub exit_codes: BTreeSet<Id>,
    /// Whether any execution path reaches this state.
    pub state_is_reachable: bool,
}

/// One scope's variables: a map, optionally over a base map it was patched
/// onto (`vmPatch base top`, i.e. `M.union top base`, resolved at lookup).
#[derive(Debug, Clone)]
struct ScopeValues {
    top: VMap<VariableState>,
    base: Option<VMap<VariableState>>,
}

impl ScopeValues {
    fn flat(map: &VMap<VariableState>) -> Self {
        Self {
            top: map.clone(),
            base: None,
        }
    }

    /// `vmPatch base diff` without building the union: the same cases as
    /// [`vm_patch`], with its last one (the left-biased union) left as two
    /// layers.
    fn patched(base: &VMap<VariableState>, diff: &VMap<VariableState>) -> Self {
        if base.version == 0 {
            return Self::flat(diff);
        }
        if diff.version == 0 {
            return Self::flat(base);
        }
        if vm_is_quick_equal(base, diff) {
            return Self::flat(diff);
        }
        Self {
            top: diff.clone(),
            base: Some(base.clone()),
        }
    }

    fn lookup(&self, name: &str) -> Option<&VariableState> {
        self.top
            .lookup(name)
            .or_else(|| self.base.as_ref().and_then(|b| b.lookup(name)))
    }

    /// The entries, base layer first, so that inserting them in order into a
    /// map leaves the top layer's value for a key in both.
    fn entries(&self) -> impl Iterator<Item = (&Rc<str>, &Rc<VariableState>)> {
        self.base.iter().flat_map(VMap::iter).chain(self.top.iter())
    }
}

impl ProgramState {
    /// The state of a variable (prefix, then local, then global scope), with
    /// the literal value left in; use [`variable_value`](Self::variable_value)
    /// to read the censored value.
    fn variable_state(&self, name: &str) -> Option<&VariableState> {
        self.prefix_values
            .lookup(name)
            .or_else(|| self.local_values.lookup(name))
            .or_else(|| self.global_values.lookup(name))
    }

    /// All variables in scope, flattened. O(variables): for tests and
    /// debugging, the checks look variables up by name.
    #[must_use]
    pub fn variables_in_scope(&self) -> BTreeMap<String, VariableState> {
        let mut flat: BTreeMap<String, VariableState> = BTreeMap::new();
        for scope in [&self.global_values, &self.local_values, &self.prefix_values] {
            for (k, v) in scope.entries() {
                flat.insert(k.to_string(), (**v).clone());
            }
        }
        for v in flat.values_mut() {
            v.variable_value.literal_value = None;
        }
        flat
    }
    /// The value of a variable in scope, with its literal value censored.
    #[must_use]
    pub fn variable_value(&self, name: &str) -> Option<VariableValue> {
        self.variable_state(name).map(|s| {
            // Censor the literal value to avoid introducing dependencies on it.
            let mut v = s.variable_value.clone();
            v.literal_value = None;
            v
        })
    }
    /// The space status of a variable in scope.
    #[must_use]
    pub fn space_status(&self, name: &str) -> Option<SpaceStatus> {
        self.variable_state(name)
            .map(|s| s.variable_value.space_status)
    }
    /// The numerical status of a variable in scope.
    #[must_use]
    pub fn numerical_status(&self, name: &str) -> Option<NumericalStatus> {
        self.variable_state(name)
            .map(|s| s.variable_value.numerical_status)
    }
    /// The possible property sets of a variable in scope.
    #[must_use]
    pub fn variable_properties(&self, name: &str) -> Option<&VariableProperties> {
        self.variable_state(name).map(|s| &s.variable_properties)
    }
    /// `stateIsReachable`.
    #[must_use]
    pub const fn state_is_reachable(&self) -> bool {
        self.state_is_reachable
    }
    /// `exitCodes`.
    #[must_use]
    pub const fn exit_codes(&self) -> &BTreeSet<Id> {
        &self.exit_codes
    }

    /// See if any execution path declares the variable an integer (`declare -i`).
    #[must_use]
    pub fn variable_may_be_declared_integer(&self, var: &str) -> Option<bool> {
        let value = self.variable_state(var)?;
        Some(
            value
                .variable_properties
                .iter()
                .any(|s| s.contains(&CFVariableProp::CFVPInteger)),
        )
    }

    /// See if any execution path suggests the variable may contain an integer.
    #[must_use]
    pub fn variable_may_be_assigned_integer(&self, var: &str) -> Option<bool> {
        let value = self.variable_state(var)?;
        Some(value.variable_value.numerical_status >= NumericalStatus::NumericalStatusMaybe)
    }
}

/// Free-function forms matching the Haskell exports.
#[must_use]
pub fn variable_may_be_declared_integer(state: &ProgramState, var: &str) -> Option<bool> {
    state.variable_may_be_declared_integer(var)
}
/// See if any execution path suggests the variable may contain an integer.
#[must_use]
pub fn variable_may_be_assigned_integer(state: &ProgramState, var: &str) -> Option<bool> {
    state.variable_may_be_assigned_integer(var)
}

/// The result of the data flow analysis.
#[derive(Debug, Clone)]
pub struct CFGAnalysis {
    /// The control flow graph.
    pub graph: CFGraph,
    /// Each token's nominal start and end node.
    pub token_to_range: IdMap<Id, (Node, Node)>,
    /// All nodes belonging to each token, recursively.
    pub token_to_nodes: IdMap<Id, BTreeSet<Node>>,
    /// The post-dominator relation.
    pub post_dominators: crate::cfg::PostDominators,
    /// The incoming and outgoing state of each node.
    pub node_to_data: IdMap<Node, (ProgramState, ProgramState)>,
}

impl CFGAnalysis {
    /// Conveniently get the state before a token id.
    #[must_use]
    pub fn get_incoming_state(&self, id: Id) -> Option<ProgramState> {
        let (start, _end) = self.token_to_range.get(&id)?;
        self.node_to_data.get(start).map(|x| x.0.clone())
    }

    /// Conveniently get the state after a token id.
    #[must_use]
    pub fn get_outgoing_state(&self, id: Id) -> Option<ProgramState> {
        let (_start, end) = self.token_to_range.get(&id)?;
        self.node_to_data.get(end).map(|x| x.1.clone())
    }

    /// Whether `target` always unconditionally runs after `base`.
    #[must_use]
    pub fn does_post_dominate(&self, target: Id, base: Id) -> bool {
        (|| {
            let (_, base_end) = self.token_to_range.get(&base)?;
            let (target_start, _) = self.token_to_range.get(&target)?;
            Some(self.post_dominators.contains(*base_end, *target_start))
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
///
/// The storage is a persistent ordered map (`Data.Map` in the original) with
/// reference-counted values: copying a state shares its maps, an insert copies
/// one path of the tree, and the values (with their nested property sets) are
/// shared between every state that holds them.
struct VMap<V> {
    version: i64,
    storage: OrdMap<Rc<str>, Rc<V>>,
}

impl<V> Clone for VMap<V> {
    fn clone(&self) -> Self {
        Self {
            version: self.version,
            storage: self.storage.clone(),
        }
    }
}

impl<V> std::fmt::Debug for VMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "VMap(v{}, {} entries)", self.version, self.storage.len())
    }
}

/// Value types whose empty maps share one allocation: `OrdMap::new` allocates
/// a node of its own, and there are an empty map or two in every state.
trait EmptyStorage: Sized {
    fn empty_storage() -> OrdMap<Rc<str>, Rc<Self>>;
}

macro_rules! shared_empty_storage {
    ($v:ty) => {
        impl EmptyStorage for $v {
            fn empty_storage() -> OrdMap<Rc<str>, Rc<Self>> {
                thread_local! {
                    static EMPTY: OrdMap<Rc<str>, Rc<$v>> = OrdMap::new();
                }
                EMPTY.with(|e| e.clone())
            }
        }
    };
}
shared_empty_storage!(VariableState);
shared_empty_storage!(FunctionValue);

impl<V: EmptyStorage> VMap<V> {
    fn empty() -> Self {
        Self {
            version: 0,
            storage: V::empty_storage(),
        }
    }
}

impl<V> VMap<V> {
    fn lookup(&self, k: &str) -> Option<&V> {
        self.storage.get(k).map(|v| &**v)
    }
    fn iter(&self) -> impl Iterator<Item = (&Rc<str>, &Rc<V>)> {
        self.storage.iter()
    }
    fn insert(&self, k: &str, v: V) -> Self {
        Self {
            version: -1,
            storage: self.storage.update(Rc::from(k), Rc::new(v)),
        }
    }
    /// A map built in one pass (`M.fromList`).
    fn from_entries(entries: impl IntoIterator<Item = (Rc<str>, Rc<V>)>) -> Self {
        Self {
            version: -1,
            storage: entries.into_iter().collect(),
        }
    }
}

const fn vm_is_quick_equal<V>(a: &VMap<V>, b: &VMap<V>) -> bool {
    a.version >= 0 && b.version >= 0 && a.version == b.version
}
fn vm_eq<V: Eq>(a: &VMap<V>, b: &VMap<V>) -> bool {
    // The slow path compares the trees, skipping every subtree they share.
    vm_is_quick_equal(a, b) || a.storage.ptr_eq(&b.storage) || a.storage == b.storage
}

/// `M.union pref other`: the union of two maps, preferring `pref`'s value for
/// keys in both. Costs O(m log n) for the smaller map's m entries.
/// (`OrdMap::union` is not usable: it keeps the other map's value when the
/// other map is the larger.)
fn union_left<K: Ord + Clone, V: Clone>(pref: &OrdMap<K, V>, other: &OrdMap<K, V>) -> OrdMap<K, V> {
    if pref.len() <= other.len() {
        let mut out = other.clone();
        for (k, v) in pref {
            out.insert(k.clone(), v.clone());
        }
        out
    } else {
        let mut out = pref.clone();
        for (k, v) in other {
            if !pref.contains_key(k) {
                out.insert(k.clone(), v.clone());
            }
        }
        out
    }
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

const fn modified(mut s: InternalState) -> InternalState {
    s.version = -1;
    s
}

fn unreachable_state() -> InternalState {
    let mut s = new_internal_state();
    s.s_is_reachable = Some(false);
    modified(s)
}

const fn state_is_quick_equal(a: &InternalState, b: &InternalState) -> bool {
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

const fn unknown_variable_value() -> VariableValue {
    VariableValue {
        literal_value: None,
        space_status: SpaceStatus::SpaceStatusDirty,
        numerical_status: NumericalStatus::NumericalStatusUnknown,
    }
}
const fn empty_variable_value() -> VariableValue {
    VariableValue {
        literal_value: Some(String::new()),
        space_status: SpaceStatus::SpaceStatusEmpty,
        numerical_status: NumericalStatus::NumericalStatusEmpty,
    }
}
const fn unknown_integer_value() -> VariableValue {
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

const fn merge_space_status(a: SpaceStatus, b: SpaceStatus) -> SpaceStatus {
    use SpaceStatus::{SpaceStatusClean, SpaceStatusDirty, SpaceStatusEmpty};
    match (a, b) {
        (SpaceStatusEmpty, y) => y,
        (x, SpaceStatusEmpty) => x,
        (SpaceStatusClean, SpaceStatusClean) => SpaceStatusClean,
        _ => SpaceStatusDirty,
    }
}
const fn merge_numerical_status(a: NumericalStatus, b: NumericalStatus) -> NumericalStatus {
    use NumericalStatus::{
        NumericalStatusDefinitely, NumericalStatusEmpty, NumericalStatusMaybe,
        NumericalStatusUnknown,
    };
    match (a, b) {
        (NumericalStatusDefinitely, NumericalStatusDefinitely) => NumericalStatusDefinitely,
        (NumericalStatusDefinitely | NumericalStatusMaybe, _)
        | (_, NumericalStatusDefinitely | NumericalStatusMaybe) => NumericalStatusMaybe,
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

const fn append_space_status(a: SpaceStatus, b: SpaceStatus) -> SpaceStatus {
    use SpaceStatus::{SpaceStatusClean, SpaceStatusDirty, SpaceStatusEmpty};
    match (a, b) {
        (SpaceStatusEmpty, _) => b,
        (_, SpaceStatusEmpty) => a,
        (SpaceStatusClean, SpaceStatusClean) => SpaceStatusClean,
        _ => SpaceStatusDirty,
    }
}
const fn append_numerical_status(a: NumericalStatus, b: NumericalStatus) -> NumericalStatus {
    use NumericalStatus::{
        NumericalStatusDefinitely, NumericalStatusEmpty, NumericalStatusMaybe,
        NumericalStatusUnknown,
    };
    match (a, b) {
        (NumericalStatusEmpty, x) | (x, NumericalStatusEmpty) => x,
        (NumericalStatusDefinitely, NumericalStatusDefinitely) => NumericalStatusDefinitely,
        (NumericalStatusUnknown, _) | (_, NumericalStatusUnknown) => NumericalStatusUnknown,
        _ => NumericalStatusMaybe,
    }
}
fn append_variable_value(a: &VariableValue, b: &VariableValue) -> VariableValue {
    VariableValue {
        literal_value: match (&a.literal_value, &b.literal_value) {
            (Some(x), Some(y)) => Some(format!("{x}{y}")),
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

fn vm_patch<V>(base: &VMap<V>, diff: &VMap<V>) -> VMap<V> {
    if base.version == 0 {
        return diff.clone();
    }
    if diff.version == 0 {
        return base.clone();
    }
    if vm_is_quick_equal(base, diff) {
        return diff.clone();
    }
    // `M.union diff base`, as the diff's values win.
    VMap {
        version: -1,
        storage: union_left(&diff.storage, &base.storage),
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

    // One pass instead of an insert (and a copy of the map) per variable.
    // Later lists win, as the successive inserts did.
    let unknown = Rc::new(unknown_variable_state());
    let spaceless = Rc::new(spaceless);
    let integer = Rc::new(integer);
    let mut entries: BTreeMap<&str, &Rc<VariableState>> = BTreeMap::new();
    for name in INTERNAL_VARIABLES {
        entries.insert(name, &unknown);
    }
    for name in VARIABLES_WITHOUT_SPACES {
        entries.insert(name, &spaceless);
    }
    for name in SPECIAL_INTEGER_VARIABLES {
        entries.insert(name, &integer);
    }
    state.s_global_values = VMap::from_entries(
        entries
            .into_iter()
            .map(|(k, v)| (Rc::from(k), Rc::clone(v))),
    );
    state = modified(state);
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
    cache: IdMap<Node, Vec<(BTreeSet<StateDependency>, InternalState)>>,
    enable_cache: bool,
    // Invocation paths determine the order of state merges, as in Haskell's
    // Data.Map. Randomized iteration must not decide state/version ordering.
    invocations: BTreeMap<Vec<Node>, (BTreeSet<StateDependency>, StateMap)>,
    // Graph adjacency, derived from CFGraph.
    labels: IdMap<Node, CFNode>,
    pred_flow: IdMap<Node, Vec<Node>>,
    succ_all: IdMap<Node, Vec<Node>>,
    /// The first internal error, after which the analysis is discarded.
    internal_error: Option<InternalError>,
}

impl Ctx {
    fn new(graph: &CFGraph) -> Self {
        let mut labels = IdMap::default();
        for (n, l) in &graph.nodes {
            labels.insert(*n, l.clone());
        }
        let mut pred_flow: IdMap<Node, Vec<Node>> = IdMap::default();
        let mut succ_all: IdMap<Node, Vec<Node>> = IdMap::default();
        for (from, to, e) in &graph.edges {
            succ_all.entry(*from).or_default().push(*to);
            if *e == CFEdge::CFEFlow {
                pred_flow.entry(*to).or_default().push(*from);
            }
        }
        Self {
            node: 0,
            input: new_internal_state(),
            output: new_internal_state(),
            stack: Vec::new(),
            counter: 1,
            cache: IdMap::default(),
            enable_cache: true,
            invocations: BTreeMap::new(),
            labels,
            pred_flow,
            succ_all,
            internal_error: None,
        }
    }

    fn fail(&mut self, what: &'static str) {
        self.internal_error.get_or_insert(InternalError(what));
    }

    const fn next_version(&mut self) -> i64 {
        let n = self.counter;
        self.counter += 1;
        n
    }

    const fn version_map<V: Clone>(&mut self, mut m: VMap<V>) -> VMap<V> {
        if m.version < 0 {
            m.version = self.next_version();
        }
        m
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
                s.s_local_values.lookup(&key).map_or_else(
                    || {
                        s.s_prefix_values
                            .lookup(&key)
                            .map(|vs| (vs.variable_properties.clone(), Scope::PrefixScope))
                    },
                    |vs| Some((vs.variable_properties.clone(), Scope::LocalScope)),
                )
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
            // Prefixed variables actually become local variables.
            Scope::LocalScope | Scope::PrefixScope => self.write_local(name, val),
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
            Scope::LocalScope | Scope::PrefixScope => self.write_local(name, vs),
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
            CFValue::CFValueArray | CFValue::CFValueString => unknown_variable_value(),
            CFValue::CFValueComputed(_, parts) => {
                let mut acc = empty_variable_value();
                for part in parts {
                    let next = self.compute_value(part);
                    acc = append_variable_value(&acc, &next);
                }
                acc
            }
            CFValue::CFValueInteger => unknown_integer_value(),
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
                Some(Scope::LocalScope | Scope::PrefixScope) => {
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
                Some(Scope::LocalScope | Scope::PrefixScope) => {
                    let state = self.read_local(name);
                    self.write_local(name, remove_properties(props, &state));
                }
            },
            CFEffect::CFUndefineVariable(name) | CFEffect::CFUndefineNameref(name) => {
                self.undefine_variable(name);
            }
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
            CFEffect::CFHintArray(_) | CFEffect::CFHintDefined(_) => {}
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
        // Merge key by key; a key that has the same value on both sides merges
        // to that value (the merge is idempotent), so only the keys where the
        // maps differ need work, and the diff skips the subtrees they share.
        let mut out = a.storage.clone();
        for item in a.storage.diff(&b.storage) {
            match item {
                // Only in b.
                DiffItem::Add(k, y) => {
                    let other = match kind {
                        VReader::Global => self.read_global(k),
                        VReader::Variable => self.read_variable(k),
                    };
                    out.insert(k.clone(), Rc::new(merge_variable_state(&other, y)));
                }
                // Only in a.
                DiffItem::Remove(k, x) => {
                    let other = match kind {
                        VReader::Global => self.read_global(k),
                        VReader::Variable => self.read_variable(k),
                    };
                    out.insert(k.clone(), Rc::new(merge_variable_state(x, &other)));
                }
                DiffItem::Update { old, new } => {
                    out.insert(old.0.clone(), Rc::new(merge_variable_state(old.1, new.1)));
                }
            }
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
        let mut out = a.storage.clone();
        for item in a.storage.diff(&b.storage) {
            match item {
                DiffItem::Add(k, y) => {
                    let other = self.read_function(k);
                    out.insert(k.clone(), Rc::new(other.union(y).cloned().collect()));
                }
                DiffItem::Remove(k, x) => {
                    let other = self.read_function(k);
                    out.insert(k.clone(), Rc::new(x.union(&other).cloned().collect()));
                }
                DiffItem::Update { old, new } => {
                    out.insert(
                        old.0.clone(),
                        Rc::new(old.1.union(new.1).cloned().collect()),
                    );
                }
            }
        }
        VMap {
            version: -1,
            storage: out,
        }
    }

    fn merge_maybes_exit(
        &mut self,
        a: Option<&BTreeSet<Id>>,
        b: Option<&BTreeSet<Id>>,
    ) -> Option<BTreeSet<Id>> {
        match (a, b) {
            (None, None) => None,
            (Some(v), None) | (None, Some(v)) => {
                let r = self.read_exit_codes();
                Some(v.union(&r).copied().collect())
            }
            (Some(v1), Some(v2)) => Some(v1.union(v2).copied().collect()),
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
                self.fail("Unexpected merge of reachable and unreachable state");
                return unreachable_state();
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
        let exit = self.merge_maybes_exit(a.s_exit_codes.as_ref(), b.s_exit_codes.as_ref());
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
        let Some((first, rest)) = list.split_first() else {
            self.fail("Null node states");
            return unreachable_state();
        };
        let mut acc = first.clone();
        for x in rest {
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
    ) -> (R, BTreeSet<StateDependency>) {
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
        let deps = self.stack.pop().map_or_else(
            || {
                self.fail("Missing stack frame");
                BTreeSet::new()
            },
            |new_entry| new_entry.dependencies,
        );
        self.input = saved_input;
        self.output = saved_output;
        self.node = saved_node;
        (x, deps)
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

    fn get_cache(&self, node: Node) -> Option<InternalState> {
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
        if let Some(v) = self.get_cache(node) {
            self.patch_output(&v);
        } else {
            let (deps, diff) = f(self);
            let old = self.cache.remove(&node).unwrap_or_default();
            let mut newlist = vec![(deps, diff.clone())];
            newlist.extend(old.into_iter().take(CACHE_ENTRIES));
            self.cache.insert(node, newlist);
            self.patch_output(&diff);
        }
    }

    // --- transfer ---

    fn transfer(&mut self, label: &CFNode) {
        match label {
            CFNode::CFStructuralNode
            | CFNode::CFEntryPoint(_)
            | CFNode::CFImpliedExit
            | CFNode::CFResolvedExit
            | CFNode::CFSetBackgroundPid(_) => {}
            CFNode::CFExecuteCommand(cmd) => self.transfer_command(cmd.clone()),
            CFNode::CFExecuteSubshell(_reason, entry, exit) => {
                self.transfer_subshell(*entry, *exit);
            }
            CFNode::CFApplyEffects(effects) => {
                for e in effects {
                    self.transfer_effect(&e.value);
                }
            }
            CFNode::CFSetExitCode(id) => {
                self.output = set_exit_code(*id, &self.output);
            }
            CFNode::CFUnresolvedExit | CFNode::CFUnreachable => {
                self.patch_output(&unreachable_state());
            }
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
        let (states, deps) = self.with_new_stack_frame(entry, false, |s| s.dataflow(entry));
        let res = states.get(&exit).map_or_else(
            || {
                self.fail("Subshell has no exit");
                unreachable_state()
            },
            |(_, res)| res.clone(),
        );
        self.register_flow_result(entry, &states, &deps);
        (deps, res)
    }

    fn transfer_command(&mut self, name: Option<String>) {
        let Some(name) = name else {
            return;
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
        let (states, deps) = self.with_new_stack_frame(entry, true, |s| s.dataflow(entry));
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

        let mut inputs = incoming
            .iter()
            .filter_map(|c| states.get(c).map(|x| x.1.clone()))
            .filter(|c| c.s_is_reachable != Some(false));
        let input = match inputs.next() {
            None if incoming.is_empty() => new_internal_state(),
            None => unreachable_state(),
            Some(first) => {
                let mut acc = first;
                for x in inputs {
                    acc = self.merge_state(&acc, &x);
                }
                acc
            }
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
                self.fail("DFA did not reach fix point");
            }
            if self.internal_error.is_some() {
                break;
            }
            if n == FALLBACK_THRESHOLD {
                self.enable_cache = false;
            }
            let Some(next) = pending.iter().next().copied() else {
                break;
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
        let (states, deps) = self.with_new_stack_frame(entry, false, |s| s.dataflow(entry));
        self.register_flow_result(entry, &states, &deps);
        states.get(&exit).map_or_else(
            || {
                self.fail("Missing exit state");
                unreachable_state()
            },
            |(_, res)| res.clone(),
        )
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

/// Create an `InternalState` that fulfills the given dependencies.
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

/// Get all the functions defined in an `InternalState` (keyed by entry node).
fn get_function_targets(state: &InternalState) -> BTreeMap<Node, FunctionDefinition> {
    let mut out = BTreeMap::new();
    for (_, val) in state.s_function_targets.iter() {
        for d in val.iter() {
            if let FunctionDefinition::FunctionDefinition(_, entry, _) = d {
                out.insert(*entry, d.clone());
            }
        }
    }
    out
}

fn internal_to_external(s: &InternalState) -> ProgramState {
    // O(1): the maps are shared, and `ProgramState` resolves them by scope
    // precedence and censors the literal value when a variable is read.
    ProgramState {
        global_values: ScopeValues::flat(&s.s_global_values),
        local_values: ScopeValues::flat(&s.s_local_values),
        prefix_values: ScopeValues::flat(&s.s_prefix_values),
        exit_codes: s.s_exit_codes.clone().unwrap_or_default(),
        state_is_reachable: s.s_is_reachable.unwrap_or(true),
    }
}

/// `internalToExternal (patchState base diff)` in O(1): the same cases as
/// [`patch_state`], with its last one (a per-map left-biased union) left as
/// two layers that a lookup resolves. The function targets are not part of
/// the external state, so they are not patched at all.
fn patched_to_external(base: &InternalState, diff: &InternalState) -> ProgramState {
    if diff.version == 0 {
        return internal_to_external(base);
    }
    if base.version == 0 || state_is_quick_equal(base, diff) {
        return internal_to_external(diff);
    }
    ProgramState {
        global_values: ScopeValues::patched(&base.s_global_values, &diff.s_global_values),
        local_values: ScopeValues::patched(&base.s_local_values, &diff.s_local_values),
        prefix_values: ScopeValues::patched(&base.s_prefix_values, &diff.s_prefix_values),
        exit_codes: diff
            .s_exit_codes
            .as_ref()
            .or(base.s_exit_codes.as_ref())
            .cloned()
            .unwrap_or_default(),
        state_is_reachable: diff.s_is_reachable.or(base.s_is_reachable).unwrap_or(true),
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
///
/// # Errors
///
/// When an invariant of the graph or of the analysis does not hold, where
/// upstream dies.
pub fn analyze_control_flow(
    params: &CFGParameters,
    t: &Token,
) -> Result<CFGAnalysis, InternalError> {
    let cfg = build_graph(*params, t)?;
    let Some(&(entry, exit)) = cfg.cf_id_to_range.get(&t.id) else {
        return Err(InternalError("Missing root"));
    };

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

    // Round up all the states from all data flows:
    // flattenByNode ∘ groupByNode ∘ addDeps, then internalToExternal.
    //
    // `addDeps` patches every state of an invocation onto that invocation's
    // dependency base. A node that occurs in one invocation only needs no
    // merge, so its patched state goes straight to `internalToExternal`, and
    // `patched_to_external` leaves the patch as two layers instead of building
    // the union (O(1) instead of O(|base| log n) per state). Nodes that occur
    // in several invocations are patched and merged as before, in the same
    // order, so the version counter sees the same merges.
    let invocations = std::mem::take(&mut ctx.invocations);
    let mut occurrences: IdMap<Node, usize> = IdMap::default();
    for (_, m) in invocations.values() {
        for node in m.keys() {
            *occurrences.entry(*node).or_default() += 1;
        }
    }

    let mut node_to_data: IdMap<Node, (ProgramState, ProgramState)> = IdMap::default();
    let mut grouped: BTreeMap<Node, Vec<(InternalState, InternalState)>> = BTreeMap::new();
    for (deps, m) in invocations.values() {
        let base = deps_to_state(deps);
        for (node, (a, b)) in m {
            if occurrences[node] == 1 {
                let data = (patched_to_external(&base, a), patched_to_external(&base, b));
                node_to_data.insert(*node, data);
            } else {
                let pa = patch_state(&base, a);
                let pb = patch_state(&base, b);
                grouped.entry(*node).or_default().push((pa, pb));
            }
        }
    }

    // flattenByNode: merge all pre/post states per node.
    for (node, list) in grouped {
        let pres: Vec<InternalState> = list.iter().map(|x| x.0.clone()).collect();
        let posts: Vec<InternalState> = list.iter().map(|x| x.1.clone()).collect();
        let pre = ctx.merge_states_nonempty(&pres);
        let post = ctx.merge_states_nonempty(&posts);
        node_to_data.insert(
            node,
            (internal_to_external(&pre), internal_to_external(&post)),
        );
    }

    if let Some(e) = ctx.internal_error {
        return Err(e);
    }

    // Fill in unreachable states for anything we didn't get to.
    let (mn, mx) = node_range(&cfg.cf_graph);
    let unreachable = internal_to_external(&unreachable_state());
    for n in mn..=mx {
        node_to_data
            .entry(n)
            .or_insert_with(|| (unreachable.clone(), unreachable.clone()));
    }

    Ok(CFGAnalysis {
        graph: cfg.cf_graph,
        token_to_range: cfg.cf_id_to_range,
        token_to_nodes: cfg.cf_id_to_nodes,
        post_dominators: cfg.cf_post_dominators,
        node_to_data,
    })
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

    #[test]
    fn an_internal_error_is_recorded_and_the_first_one_kept() {
        let out = parse_script("t.sh", "echo hi\n");
        let root = out.root.expect("parse produced a root");
        let params = CFGParameters {
            cf_lastpipe: false,
            cf_pipefail: false,
        };
        let cfg = build_graph(params, &root).expect("the graph builds");
        let mut ctx = Ctx::new(&cfg.cf_graph);
        let mut reachable = new_internal_state();
        reachable.s_is_reachable = Some(true);
        ctx.do_merge(&reachable, &unreachable_state());
        ctx.merge_states_nonempty(&[]);
        assert_eq!(
            ctx.internal_error,
            Some(InternalError(
                "Unexpected merge of reachable and unreachable state"
            ))
        );
        let mut fresh = Ctx::new(&cfg.cf_graph);
        fresh.merge_states_nonempty(&[]);
        assert_eq!(
            fresh.internal_error,
            Some(InternalError("Null node states"))
        );
    }

    fn analyze(src: &str) -> (CFGAnalysis, Token) {
        let out = parse_script("test.sh", src);
        let root = out.root.expect("parse produced a root");
        let params = CFGParameters {
            cf_lastpipe: false,
            cf_pipefail: false,
        };
        let a = analyze_control_flow(&params, &root).expect("the analysis succeeds");
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
            if let InnerToken::T_Assignment { var: v, .. } = &*t.inner
                && v == var
            {
                return t.id;
            }
        }
        panic!("no assignment to {var}");
    }

    /// Find ids of simple commands whose first literal word is `name`.
    fn command_ids(root: &Token, name: &str) -> Vec<Id> {
        let mut all = Vec::new();
        collect(root, &mut all);
        let mut out = Vec::new();
        for t in all {
            if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner
                && let Some(w) = words.first()
                && crate::ast_lib::get_literal_string(w).as_deref() == Some(name)
            {
                out.push(t.id);
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
        assert!(st.variable_value("secret").is_none());
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

    /// Every answer `ProgramState` gives, for the names in `names`.
    fn answers(st: &ProgramState, names: &[&str]) -> String {
        use std::fmt::Write as _;
        let mut out = format!(
            "reachable={} exit={:?} scope={:?}\n",
            st.state_is_reachable(),
            st.exit_codes(),
            st.variables_in_scope()
        );
        for n in names {
            writeln!(
                out,
                "{n}: {:?} {:?} {:?} {:?} {:?} {:?}",
                st.variable_value(n),
                st.space_status(n),
                st.numerical_status(n),
                st.variable_properties(n),
                st.variable_may_be_declared_integer(n),
                st.variable_may_be_assigned_integer(n),
            )
            .unwrap();
        }
        out
    }

    #[test]
    fn layered_patch_answers_like_the_patched_state() {
        let names = ["a", "b", "c", "d", "e", "missing"];
        let val = |s: &str| VariableState {
            variable_value: literal_to_variable_value(s),
            variable_properties: default_properties(),
        };
        let int_props = {
            let mut p = BTreeSet::new();
            p.insert(CFVariableProp::CFVPInteger);
            let mut ps = BTreeSet::new();
            ps.insert(p);
            ps
        };
        let mut deps = BTreeSet::new();
        deps.insert(StateDependency::DepState(
            Scope::GlobalScope,
            "a".into(),
            val("1"),
        ));
        deps.insert(StateDependency::DepState(
            Scope::GlobalScope,
            "b".into(),
            val("x y"),
        ));
        deps.insert(StateDependency::DepState(
            Scope::LocalScope,
            "c".into(),
            val(""),
        ));
        deps.insert(StateDependency::DepProperties(
            Scope::PrefixScope,
            "d".into(),
            int_props,
        ));
        deps.insert(StateDependency::DepExitCodes([Id(7)].into()));
        let base = deps_to_state(&deps);

        let diff = insert_global("a", val("a b"), &new_internal_state());
        let diff = insert_local("b", val("2"), &diff);
        let diff = insert_global("e", val("3"), &diff);
        let diff = insert_prefix("c", val("*"), &diff);
        let unreachable_diff = unreachable_state();
        let exits_diff = set_exit_code(Id(9), &insert_global("a", val("4"), &diff));

        for (b, d) in [
            (&base, &diff),
            (&base, &unreachable_diff),
            (&base, &exits_diff),
            (&base, &new_internal_state()),
            (&new_internal_state(), &diff),
            (&diff, &base),
        ] {
            assert_eq!(
                answers(&patched_to_external(b, d), &names),
                answers(&internal_to_external(&patch_state(b, d)), &names),
            );
        }
    }
}
