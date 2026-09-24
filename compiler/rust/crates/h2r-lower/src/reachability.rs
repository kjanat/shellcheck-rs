//! `Main.main`-rooted reachability over the whole closed world.
//!
//! # The question
//!
//! M2.4c found that **922** of the dump's top-level bindings have no
//! occurrence anywhere in it ([`h2r_analysis::dictflow::T_UNREACHABLE`]),
//! and 413 of the 558 unresolved class-op sites live in them. That is a
//! valid *dead subset* — under `W0` nothing can name those bindings, so
//! they cannot run — but it is **not** a rooted reachability set: a
//! binding referenced only by another unreachable binding is not in it,
//! and neither is a whole unreachable strongly-connected component.
//!
//! This module computes the rooted set. The nodes are the top-level
//! binding *pairs* of every module in the dump; the edges are the
//! references between them; the roots are `Main.main`; live is the
//! transitive closure and dead is the rest.
//!
//! # What identity means here
//!
//! A node is `(module index, BinderId)` — never a name. Names are
//! diagnostics ([`h2r_analysis`]'s level 6) and three top-level bindings
//! of `ShellCheck.AST` share the internal name `$_sys$$fTraversableInnerToken`.
//! An edge is established two ways and two ways only:
//!
//! * [`A2_EDGE_LOCAL`] — the resolver says the occurrence is
//!   [`Ref::Local`] of a binder whose *binding site* is [`BindSite::Top`].
//!   Lexical binder identity; the strongest evidence there is. This is
//!   the only way an internally-named top-level binding is ever reached.
//! * [`A3_EDGE_GLOBAL`] — the resolver says [`Ref::Global`], and the
//!   occurrence's stable name is the name of an *external* top-level
//!   binding of some in-world module. Format 5's linkage identity, the
//!   same index [`h2r_analysis::classops::World`] and
//!   [`h2r_analysis::dictflow::Program`] already build.
//!
//! An occurrence that resolves to a binder bound by a lambda, a `let`, a
//! `case` or an alternative is not an edge: it names something inside a
//! top-level binding, not a top-level binding.
//!
//! # What is *not* an edge
//!
//! A [`Ref::Global`] occurrence whose stable name no in-world top-level
//! binding claims is an **import reference** ([`A4_IMPORT`]): `base`,
//! `parsec`, `containers`, a data constructor's worker, a class-op
//! selector. It is recorded, with its occurrence count, separately for
//! live and for dead code — that count is the surface the lowering will
//! have to replace — but it is not a graph edge, because the definition
//! is not in the world.
//!
//! One case is neither: a stable name whose unit *and* module are those of
//! an in-world module, that no external top-level binding of that module
//! defines and that GHC does not mark as a data constructor or a class-op
//! selector. That is a **hole in the linkage** ([`A5_IN_WORLD_MISSING`]),
//! and it has its own category because it is not empty. The plugin
//! serialises the `CoreProgram` *before* GHC's `CoreTidy` pass, so a
//! top-level binding GHC has not yet externalised still carries its
//! internal name (`$_in$$wgetPath`) in its own module's dump, while a
//! *downstream* module — which read the already-tidied interface — refers
//! to it by the external name (`$…$ShellCheck.ASTLib$$wgetPath`). The two
//! names are the same binding and the closed world cannot see that they
//! are. The same gap is under every stable-name linkage in the compiler,
//! [`h2r_analysis::dictflow`]'s included; M3a is the first pass to measure
//! it.
//!
//! It is reported as its own population, with its occurrence count and
//! its referrers, and bounded by [`A11_MISSING_IMPACT`]: the closure is
//! re-run with every name-matched edge added, and the number of bindings
//! that would change verdict is published. Nothing here repairs the hole —
//! a name match is evidence level 6 and this milestone's verdicts rest on
//! the resolver.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use h2r_analysis::callee::split_stable_name;
use h2r_analysis::dictflow::{Program, is_external_name};
use h2r_core_ir::{BindSite, BinderId, Edge, Expr, ExprId, Module, Ref};
use serde::Serialize;

//------------------------------------------------------------------------------
// Rules
//------------------------------------------------------------------------------

/// **The closed world, inherited.** The modules of the dump are the whole
/// program and `Main.main` is its only root. This is
/// [`h2r_analysis::dictflow::W0_CLOSED_WORLD`] and
/// [`h2r_analysis::higher::H0_CLOSED_WORLD`] — an assumption about the
/// *build*, which no walk can prove — **cited, not re-asserted**. Every
/// `dead` verdict below is a claim about this world and nothing else.
/// Evidence: a stated assumption about the build (5).
pub const A0_CLOSED_WORLD: &str = "A0-CLOSED-WORLD";
/// **Root admission.** The root is the top-level binding of the dump's
/// `Main` module whose stable name is `$<that module's unit>$Main$main`,
/// found through the world's external top-level index. If there is not
/// exactly one, the analysis fails with a named reason rather than
/// guessing. Evidence: stable global identity (4) over lexical binder
/// identity (1).
pub const A1_ROOT_MAIN: &str = "A1-ROOT-MAIN";
/// **Intra-module edge.** A `Var` occurrence in the right-hand side of a
/// top-level binding that [`Module::resolve`] maps to a binder whose
/// [`Module::binding`] site is [`BindSite::Top`] is an edge to that
/// binding. The binding *site* decides, never the name: this is the only
/// rule that can reach an internally-named top-level binding, of which
/// three in `ShellCheck.AST` share one name. Evidence: lexical binder
/// identity (1).
pub const A2_EDGE_LOCAL: &str = "A2-EDGE-LOCAL";
/// **Inter-module edge.** A `Var` occurrence the resolver maps to
/// [`Ref::Global`] whose stable name is the name of an external top-level
/// binding of some in-world module is an edge to that binding. Evidence:
/// def-use over stable global identity (3), the same linkage
/// [`h2r_analysis::dictflow::W1_GLOBAL_CALLERS`] uses.
pub const A3_EDGE_GLOBAL: &str = "A3-EDGE-GLOBAL";
/// **Import classification.** A [`Ref::Global`] occurrence whose stable
/// name belongs to no in-world module is a reference to an import: the
/// definition is outside the world, so it is not a graph edge. Counted
/// per stable name, separately from live and from dead code. Evidence:
/// stable global identity (4).
pub const A4_IMPORT: &str = "A4-IMPORT";
/// **In-world missing.** A [`Ref::Global`] occurrence whose stable name's
/// unit *and* module are an in-world module's, that no external top-level
/// binding of that module defines, and that GHC's own `IdDetails` do not
/// mark as a data constructor or a class-op selector — a value the dump
/// should carry and does not. A hole in the dump; its own category,
/// expected empty and asserted. Evidence: stable global identity (4) over
/// GHC's own flags (5).
pub const A5_IN_WORLD_MISSING: &str = "A5-IN-WORLD-MISSING";
/// **Live.** The live set is the transitive closure of [`A2_EDGE_LOCAL`]
/// and [`A3_EDGE_GLOBAL`] edges from the [`A1_ROOT_MAIN`] roots, and
/// nothing else. Evidence: def-use reachability (3).
pub const A6_LIVE_CLOSURE: &str = "A6-LIVE-CLOSURE";
/// **Dead by no reference.** A top-level binding with no occurrence
/// anywhere in the closed world. This is exactly
/// [`h2r_analysis::dictflow::Program::is_unreachable_top`], the predicate
/// behind [`h2r_analysis::dictflow::T_UNREACHABLE`], called rather than
/// reimplemented so the two cannot drift. Evidence: def-use over the
/// closed world (3).
pub const A7_DEAD_NO_REFS: &str = "A7-DEAD-NO-REFS";
/// **Dead by only-dead referrers.** A top-level binding that *is*
/// referenced, but every top-level binding whose right-hand side
/// references it is itself dead. The population M2.4c's zero-reference
/// subset could not see. Evidence: def-use reachability (3).
pub const A8_DEAD_ONLY_FROM_DEAD: &str = "A8-DEAD-ONLY-FROM-DEAD";
/// **The witness.** Every live binding carries one *shortest* chain of
/// [`A2_EDGE_LOCAL`] / [`A3_EDGE_GLOBAL`] edges from a root to it, so the
/// verdict can be checked by hand from the report alone. Evidence: def-use
/// (3).
pub const A9_WITNESS: &str = "A9-WITNESS";
/// **The blast radius of a hole.** For an [`A5_IN_WORLD_MISSING`] name,
/// the top-level bindings of the named module whose *occurrence name*
/// matches, and whether adding those edges would move any verdict. This
/// is a **name** match — diagnostics, evidence level 6 — and exists only
/// to bound the damage a hole could do. No edge, no verdict and no count
/// in the accounting rests on it. Evidence: binder names (6).
pub const A11_MISSING_IMPACT: &str = "A11-MISSING-IMPACT";
/// **External identity is unique.** Every external stable name that an
/// in-world module's top-level binding carries is carried by *exactly one*
/// such binding. This is what makes [`A3_EDGE_GLOBAL`] an identity and not
/// a guess; it is the property [`RootError::NameCollisions`] refuses to
/// proceed without, and the count it refuses on is reported here rather
/// than left implicit. Evidence: a stated property of the dump, asserted
/// (5).
pub const A12_EXTERNAL_UNIQUE: &str = "A12-EXTERNAL-UNIQUE";
/// **A global occurrence never carries an internal name.** After CoreTidy a
/// top-level binder can still have an *internal* `Name`, whose stable
/// string (`$_in$…`, `$_sys$…`) is not unique — three top-level bindings of
/// `ShellCheck.AST` render as one. Such a binding is reachable only through
/// [`A2_EDGE_LOCAL`]. This rule asserts the converse: no occurrence the
/// resolver calls [`Ref::Global`] — one nothing in its module binds —
/// carries an internal stable name, so no global occurrence is ever matched
/// against a name that is not an identity. Evidence: stable global identity
/// (4).
pub const A13_GLOBAL_EXTERNAL: &str = "A13-GLOBAL-EXTERNAL";
/// **The accounting.** `top = live + dead` per module and in total, and
/// `dead = dead_no_refs + dead_only_from_dead`. Asserted, never assumed.
/// Evidence: a stated property of the proof object (5).
pub const A10_ACCOUNTING: &str = "A10-ACCOUNTING";

/// Every rule, with its meaning and evidence level.
pub const RULES: &[(&str, u8, &str)] = &[
    (
        A0_CLOSED_WORLD,
        5,
        "the dump is the whole program and Main.main is its only root (W0, inherited)",
    ),
    (
        A1_ROOT_MAIN,
        4,
        "the root is the one top-level binding of Main named $<unit>$Main$main",
    ),
    (
        A2_EDGE_LOCAL,
        1,
        "an occurrence resolving to a binder bound at top level is an edge to that binding",
    ),
    (
        A3_EDGE_GLOBAL,
        3,
        "a global occurrence whose stable name is an in-world top-level binding is an edge",
    ),
    (
        A4_IMPORT,
        4,
        "a global occurrence naming no in-world module is an import reference, not an edge",
    ),
    (
        A5_IN_WORLD_MISSING,
        4,
        "an in-world stable name with no binding and no GHC flag explaining it: a dump hole",
    ),
    (
        A6_LIVE_CLOSURE,
        3,
        "live is the transitive closure of A2/A3 edges from the A1 roots, and nothing else",
    ),
    (
        A7_DEAD_NO_REFS,
        3,
        "no occurrence anywhere in the closed world (dictflow's own T_UNREACHABLE predicate)",
    ),
    (
        A8_DEAD_ONLY_FROM_DEAD,
        3,
        "referenced, but every referring top-level binding is itself dead",
    ),
    (
        A9_WITNESS,
        3,
        "every live binding carries one shortest root-to-binding chain of edges",
    ),
    (
        A10_ACCOUNTING,
        5,
        "top = live + dead per module and in total; dead = no-refs + only-from-dead",
    ),
    (
        A11_MISSING_IMPACT,
        6,
        "a name-matched bound on what an A5 hole could cost; never a verdict",
    ),
    (
        A12_EXTERNAL_UNIQUE,
        5,
        "every external in-world stable name is defined by exactly one top-level binding",
    ),
    (
        A13_GLOBAL_EXTERNAL,
        4,
        "no Ref::Global occurrence carries an internal stable name",
    ),
];

/// The trusted inputs of this analysis: consulted, never verified, and
/// named on every report — including the independent verifier's, which
/// shares exactly these and the IR.
pub const TRUSTED: &[&str] = &[
    "W0-CLOSED-WORLD: the dump directory is the whole program (an assumption about the build)",
    "the module list: every *.core.json under the dump directory, and only those",
    "the root name: $<Main's unit>$Main$main",
    "the IR's resolver: Module::resolve, Module::binding, Module::occurrences (h2r-core-ir)",
    "GHC's own flags: isClassOp and the data-constructor record in the id table",
    "GHC's wired-in Ids with no source binding: WIRED_IN_WITHOUT_SOURCE",
];

/// GHC 9.6 defines these Ids only in `GHC.Types.Id.Make`, in a module whose source binds nothing by that name.
pub const WIRED_IN_WITHOUT_SOURCE: &[&str] = &["$ghc-prim$GHC.Magic$nospec"];

//------------------------------------------------------------------------------
// Nodes
//------------------------------------------------------------------------------

/// A node of the live graph: one top-level binding pair, identified by the
/// module it is in and the binder that binds it. Never by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct TopKey {
    pub module: u32,
    pub binder: BinderId,
}

/// A node, with the diagnostics a reader needs to check it by hand.
#[derive(Debug, Clone, Serialize)]
pub struct TopRef {
    #[serde(flatten)]
    pub key: TopKey,
    pub module_name: String,
    /// The binder's stable name. **Diagnostics only**; nothing is keyed by
    /// it except the [`A3_EDGE_GLOBAL`] index, which admits external names
    /// only.
    pub name: String,
    pub occ: String,
    /// Is the stable name one another module could refer to?
    pub external: bool,
    pub exported: bool,
}

/// Index into [`LiveSet::nodes`].
pub type NodeId = u32;

/// A root, with the rule that admitted it.
#[derive(Debug, Clone, Serialize)]
pub struct Root {
    pub node: NodeId,
    pub rule: &'static str,
}

/// A live binding and the shortest chain of edges that reaches it.
#[derive(Debug, Clone, Serialize)]
pub struct LiveBinding {
    pub node: NodeId,
    /// Root first, this binding last. A one-element path is a root.
    pub witness: Vec<NodeId>,
    pub rule: &'static str,
}

/// Why a binding is dead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum DeadReason {
    /// No occurrence anywhere in the closed world ([`A7_DEAD_NO_REFS`]).
    DeadNoReferences,
    /// Referenced, but only from dead code ([`A8_DEAD_ONLY_FROM_DEAD`]).
    DeadReferencedOnlyFromDead,
}

impl DeadReason {
    pub fn rule(self) -> &'static str {
        match self {
            DeadReason::DeadNoReferences => A7_DEAD_NO_REFS,
            DeadReason::DeadReferencedOnlyFromDead => A8_DEAD_ONLY_FROM_DEAD,
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            DeadReason::DeadNoReferences => "DeadNoReferences",
            DeadReason::DeadReferencedOnlyFromDead => "DeadReferencedOnlyFromDead",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct DeadBinding {
    pub node: NodeId,
    pub reason: DeadReason,
    /// The top-level bindings whose right-hand sides reference this one.
    /// Empty exactly when the reason is [`DeadReason::DeadNoReferences`];
    /// all of them are dead.
    pub referrers: Vec<NodeId>,
    pub rule: &'static str,
}

/// One edge of the live graph, with the rule that established it and how
/// many occurrences did. A pair of bindings joined by both rules — which
/// the dump does not in fact exhibit — would carry two entries, never one
/// merged entry with an unclear rule.
#[derive(Debug, Clone, Serialize)]
pub struct EdgeRef {
    pub from: NodeId,
    pub to: NodeId,
    pub occurrences: u32,
    pub rule: &'static str,
}

/// How often an external stable name is referenced, from live and from
/// dead code.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct ImportUse {
    pub from_live: u32,
    pub from_dead: u32,
}

/// A global occurrence naming an in-world module that no top-level binding
/// of that module defines: a name the closed world cannot link
/// ([`A5_IN_WORLD_MISSING`]).
#[derive(Debug, Clone, Serialize)]
pub struct Missing {
    pub name: String,
    pub in_module: String,
    pub occurrences: u32,
    /// The top-level bindings whose right-hand sides carry the occurrence.
    pub referrers: Vec<NodeId>,
    /// Whether any of those is live: a hole nothing live walks through
    /// cannot cost a verdict.
    pub referenced_from_live: bool,
    /// The modules of the live bindings that carry the occurrence.
    pub live_referrer_modules: Vec<String>,
    /// Top-level bindings of the named module whose **occurrence name**
    /// matches. A name match, evidence level 6, recorded under
    /// [`A11_MISSING_IMPACT`] to bound the damage — never to make an edge.
    pub candidates: Vec<NodeId>,
    pub candidates_dead: usize,
    pub rule: &'static str,
    pub impact_rule: &'static str,
}

/// The global occurrences an in-world stable name *does* explain: GHC's
/// own flags say the name is a data constructor's worker or a class-op
/// selector, neither of which is a Core top-level binding. Evidence, not a
/// verdict, and not a graph edge.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize)]
pub struct InWorldNonBindings {
    pub data_con_names: u32,
    pub data_con_occurrences: u32,
    pub class_op_names: u32,
    pub class_op_occurrences: u32,
    pub wired_in_names: u32,
    pub wired_in_occurrences: u32,
}

/// What the [`A5_IN_WORLD_MISSING`] names could cost, bounded under
/// [`A11_MISSING_IMPACT`]. Every field here is name-matched evidence; no
/// verdict reads one.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub struct MissingImpact {
    pub names: usize,
    pub occurrences: u32,
    pub names_referenced_from_live: usize,
    /// Distinct name-matched candidate bindings, over all the names.
    pub candidates: usize,
    pub candidates_dead: usize,
    /// How many bindings would become live if **every** name-matched edge
    /// were added to the graph. `0` means the hole costs no verdict.
    pub would_become_live: usize,
    /// Names for which no candidate binding exists at all: the defining
    /// module's dump carries no top-level binding of that occurrence name,
    /// so the name match finds nothing to bound with.
    pub names_without_candidate: usize,
    /// Where the [`A11_MISSING_IMPACT`] closure delta falls.
    pub would_become_live_by_module: BTreeMap<String, usize>,
    /// The **sound** bound, which needs no name at all: the modules some
    /// unlinkable name referenced from live code points into, and how many
    /// of their bindings the rooted analysis currently calls dead. Every
    /// one of those verdicts is conditional on the linkage.
    pub suspect_modules: Vec<String>,
    pub suspect_dead: usize,
}

//------------------------------------------------------------------------------
// Accounting
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Default, Serialize)]
pub struct ModuleAcct {
    pub module: String,
    pub top: usize,
    pub live: usize,
    pub dead_no_refs: usize,
    pub dead_only_from_dead: usize,
}

impl ModuleAcct {
    pub fn dead(&self) -> usize {
        self.dead_no_refs + self.dead_only_from_dead
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct Accounting {
    pub modules: Vec<ModuleAcct>,
    pub top: usize,
    pub live: usize,
    pub dead: usize,
    pub dead_no_refs: usize,
    pub dead_only_from_dead: usize,
    pub roots: usize,
    pub edges: usize,
    pub edges_local: usize,
    pub edges_global: usize,
    pub edge_occurrences: u64,
    /// Distinct external stable names referenced from anywhere.
    pub import_names: usize,
    pub import_occurrences_live: u64,
    pub import_occurrences_dead: u64,
    /// The size of [`h2r_analysis::dictflow::Program::is_unreachable_top`]'s
    /// set over the same population.
    pub zero_reference: usize,
    /// How many of those are **roots**. A program's entry point is not
    /// called by the program, so the root is zero-reference by
    /// construction and the gate is `zero-reference \\ roots ⊆ dead`, not
    /// `zero-reference ⊆ dead`.
    pub zero_reference_roots: usize,
    /// How many of those the rooted analysis calls live *and* is not a
    /// root. Must be 0: the subset gate.
    pub zero_reference_live: usize,
    /// Dead bindings the zero-reference subset does not contain: what the
    /// rooted analysis adds.
    pub additional_dead: usize,
    pub in_world_missing: usize,
    pub in_world_non_bindings: InWorldNonBindings,
    pub missing_impact: MissingImpact,
    /// [`A12_EXTERNAL_UNIQUE`]: how many distinct external stable names the
    /// in-world top-level bindings define, and how many of them two
    /// bindings claim. The second must be 0 — [`RootError::NameCollisions`]
    /// refuses to build the graph otherwise — and is reported, not assumed.
    pub external_names_defined: usize,
    pub external_name_collisions: usize,
    /// [`A13_GLOBAL_EXTERNAL`]: [`Ref::Global`] occurrences whose stable
    /// name is *internal*, by distinct name and by occurrence. Both must
    /// be 0.
    pub global_internal_names: usize,
    pub global_internal_occurrences: u64,
    /// The IR resolver's own guard, summed over the world: an occurrence
    /// that resolved lexically although its stable name is an external name
    /// of another module. Two Ids sharing one GHC unique. Must be 0.
    pub unique_collisions: usize,
}

impl Accounting {
    /// [`A10_ACCOUNTING`]. Returns every identity that does not hold. The
    /// [`A5_IN_WORLD_MISSING`] population is **reported**, not asserted:
    /// it is a property of the dump, not of this walk, and a hole that
    /// costs no verdict must not stop the milestone silently or loudly.
    pub fn check(&self) -> Vec<String> {
        let mut bad = Vec::new();
        if self.top != self.live + self.dead {
            bad.push(format!(
                "total: top {} != live {} + dead {}",
                self.top, self.live, self.dead
            ));
        }
        if self.dead != self.dead_no_refs + self.dead_only_from_dead {
            bad.push(format!(
                "total: dead {} != no-refs {} + only-from-dead {}",
                self.dead, self.dead_no_refs, self.dead_only_from_dead
            ));
        }
        for m in &self.modules {
            if m.top != m.live + m.dead() {
                bad.push(format!(
                    "{}: top {} != live {} + dead {}",
                    m.module,
                    m.top,
                    m.live,
                    m.dead()
                ));
            }
        }
        let st: usize = self.modules.iter().map(|m| m.top).sum();
        let sl: usize = self.modules.iter().map(|m| m.live).sum();
        let sd: usize = self.modules.iter().map(|m| m.dead()).sum();
        if (st, sl, sd) != (self.top, self.live, self.dead) {
            bad.push(format!(
                "per-module sums ({st}, {sl}, {sd}) != totals ({}, {}, {})",
                self.top, self.live, self.dead
            ));
        }
        if self.zero_reference_live != 0 {
            bad.push(format!(
                "{} zero-reference binding(s) are neither dead nor a root: the subset gate fails",
                self.zero_reference_live
            ));
        }
        let zero_dead = self.zero_reference - self.zero_reference_roots - self.zero_reference_live;
        if zero_dead + self.additional_dead != self.dead {
            bad.push(format!(
                "dead {} != zero-reference-and-dead {} + additional {}",
                self.dead, zero_dead, self.additional_dead
            ));
        }
        if self.unique_collisions != 0 {
            bail_unique(&mut bad, self.unique_collisions);
        }
        if self.external_name_collisions != 0 {
            bad.push(format!(
                "{} external stable name(s) are defined by more than one top-level \
                 binding: {} fails",
                self.external_name_collisions, A12_EXTERNAL_UNIQUE
            ));
        }
        if self.global_internal_names != 0 {
            bad.push(format!(
                "{} Ref::Global occurrence name(s) are internal, over {} occurrence(s): \
                 {} fails",
                self.global_internal_names, self.global_internal_occurrences, A13_GLOBAL_EXTERNAL
            ));
        }
        if self.edges != self.edges_local + self.edges_global {
            bad.push(format!(
                "edges {} != local {} + global {}",
                self.edges, self.edges_local, self.edges_global
            ));
        }
        bad
    }
}

/// One accounting failure, spelled out rather than inlined so the
/// [`Accounting::check`] arm stays one line.
fn bail_unique(bad: &mut Vec<String>, n: usize) {
    bad.push(format!(
        "{n} occurrence(s) resolved lexically although their stable name is an \
         external name of another module: two Ids share one GHC unique"
    ));
}

//------------------------------------------------------------------------------
// The proof object
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize)]
pub struct LiveSet {
    /// The modules of the world, in load order. A node's `module` indexes
    /// this.
    pub modules: Vec<String>,
    /// Every top-level binding of every module, in `(module, dump order)`.
    pub nodes: Vec<TopRef>,
    pub roots: Vec<Root>,
    pub live: Vec<LiveBinding>,
    pub dead: Vec<DeadBinding>,
    pub edges: Vec<EdgeRef>,
    /// External stable name → how often live and dead code reference it.
    pub imports: BTreeMap<String, ImportUse>,
    pub foreign: BTreeMap<String, ImportUse>,
    pub in_world_missing: Vec<Missing>,
    /// M2.4c's zero-reference set, recomputed with its own predicate. The
    /// subset gate crosses it with `dead`.
    pub zero_reference: Vec<NodeId>,
    pub accounting: Accounting,
    pub trusted: &'static [&'static str],
}

/// Why the analysis could not start. Never a guess.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RootError {
    NoMainModule,
    /// Several modules call themselves `Main`.
    AmbiguousMainModule(Vec<String>),
    /// No top-level binding of the `Main` module carries the root name.
    NoRootBinding(String),
    /// Several do. Cannot happen for an external name (the world asserts
    /// external names are unique), but it is checked rather than assumed.
    AmbiguousRootBinding(String, usize),
    /// Two distinct top-level bindings claim one external stable name.
    NameCollisions(Vec<String>),
}

impl std::fmt::Display for RootError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RootError::NoMainModule => {
                write!(f, "no module named Main in the dump: there is no root")
            }
            RootError::AmbiguousMainModule(ms) => {
                write!(f, "several modules named Main, in units {ms:?}")
            }
            RootError::NoRootBinding(n) => write!(
                f,
                "no top-level binding of Main is named {n}: the root cannot be admitted"
            ),
            RootError::AmbiguousRootBinding(n, k) => {
                write!(f, "{k} top-level bindings of Main are named {n}")
            }
            RootError::NameCollisions(ns) => {
                write!(f, "external stable names are not unique: {ns:?}")
            }
        }
    }
}

/// The stable name of the root, for a `Main` module in unit `unit`.
pub fn root_name(unit: &str) -> String {
    format!("${unit}$Main$main")
}

impl LiveSet {
    /// Build the live graph over the modules of the closed world.
    pub fn of_modules<'m>(
        modules: impl IntoIterator<Item = &'m Module>,
    ) -> Result<Self, RootError> {
        let modules: Vec<&Module> = modules.into_iter().collect();
        Build::new(&modules)?.run()
    }

    pub fn node(&self, n: NodeId) -> &TopRef {
        &self.nodes[n as usize]
    }

    /// `(module, stable name)` of a node — the pair a witness path is
    /// meant to be read as.
    pub fn named(&self, n: NodeId) -> (&str, &str) {
        let t = self.node(n);
        (t.module_name.as_str(), t.name.as_str())
    }

    /// Every node whose stable name is `name`. A name is not an identity,
    /// so this can return several; `--explain` says so rather than picking
    /// one.
    pub fn by_name(&self, name: &str) -> Vec<NodeId> {
        (0..self.nodes.len() as NodeId)
            .filter(|&n| self.nodes[n as usize].name == name)
            .collect()
    }

    /// The same, falling back to the occurrence name so a reader can ask
    /// for `doAnalysis` without spelling the unit out.
    pub fn by_name_or_occ(&self, name: &str) -> Vec<NodeId> {
        let exact = self.by_name(name);
        if !exact.is_empty() {
            return exact;
        }
        (0..self.nodes.len() as NodeId)
            .filter(|&n| self.nodes[n as usize].occ == name)
            .collect()
    }

    pub fn live_of(&self, n: NodeId) -> Option<&LiveBinding> {
        self.live
            .binary_search_by_key(&n, |l| l.node)
            .ok()
            .map(|i| &self.live[i])
    }

    pub fn dead_of(&self, n: NodeId) -> Option<&DeadBinding> {
        self.dead
            .binary_search_by_key(&n, |d| d.node)
            .ok()
            .map(|i| &self.dead[i])
    }

    pub fn is_live(&self, n: NodeId) -> bool {
        self.live_of(n).is_some()
    }

    /// Imports sorted by how often live code references them, then by
    /// name: the surface the lowering has to replace first.
    pub fn imports_by_live_use(&self) -> Vec<(&str, ImportUse)> {
        let mut v: Vec<(&str, ImportUse)> =
            self.imports.iter().map(|(k, &u)| (k.as_str(), u)).collect();
        v.sort_by(|a, b| b.1.from_live.cmp(&a.1.from_live).then(a.0.cmp(b.0)));
        v
    }

    /// The zero-reference bindings the rooted analysis does not call dead:
    /// the roots first (a program's entry point is not called by the
    /// program), then anything else, of which the gate asserts there is
    /// none.
    pub fn zero_reference_not_dead(&self) -> Vec<NodeId> {
        self.zero_reference
            .iter()
            .copied()
            .filter(|&n| self.is_live(n))
            .collect()
    }

    pub fn is_root(&self, n: NodeId) -> bool {
        self.roots.iter().any(|r| r.node == n)
    }

    /// The whole-program linkage of one **external** stable name: the single
    /// top-level binding that defines it, every binding that refers to it
    /// grouped by module and by the rule that made the edge, and its witness
    /// path if it is live.
    ///
    /// This is [`A12_EXTERNAL_UNIQUE`] made usable. The defining binding is
    /// found through the external-name index, never by a name heuristic, and
    /// an internal name is refused rather than answered: internal stable
    /// strings are not unique, so there is no single binding to point at.
    pub fn link(&self, name: &str) -> Result<Link, LinkError> {
        if !is_external_name(name) {
            return Err(LinkError::InternalName);
        }
        let hits = self.by_name(name);
        let node = match hits.as_slice() {
            [] => return Err(LinkError::NotFound),
            [n] => *n,
            many => return Err(LinkError::Ambiguous(many.len())),
        };
        let mut by: BTreeMap<(&str, &'static str), (usize, u32)> = BTreeMap::new();
        for e in self.edges.iter().filter(|e| e.to == node) {
            let slot = by
                .entry((self.node(e.from).module_name.as_str(), e.rule))
                .or_insert((0, 0));
            slot.0 += 1;
            slot.1 += e.occurrences;
        }
        let mut referrers: Vec<LinkRef> = by
            .into_iter()
            .map(|((module, rule), (bindings, occurrences))| LinkRef {
                module: module.to_string(),
                rule,
                bindings,
                occurrences,
            })
            .collect();
        referrers.sort_by(|a, b| {
            b.occurrences
                .cmp(&a.occurrences)
                .then(a.module.cmp(&b.module))
                .then(a.rule.cmp(b.rule))
        });
        Ok(Link {
            name: name.to_string(),
            node,
            referrers,
            witness: self.live_of(node).map(|l| l.witness.clone()),
            rule: A12_EXTERNAL_UNIQUE,
        })
    }
}

/// One group of references to a linked binding: how many top-level bindings
/// of one module name it, over how many occurrences, under which rule.
#[derive(Debug, Clone, Serialize)]
pub struct LinkRef {
    pub module: String,
    pub rule: &'static str,
    pub bindings: usize,
    pub occurrences: u32,
}

/// The answer to [`LiveSet::link`].
#[derive(Debug, Clone, Serialize)]
pub struct Link {
    pub name: String,
    pub node: NodeId,
    pub referrers: Vec<LinkRef>,
    /// Root first, this binding last, when it is live.
    pub witness: Option<Vec<NodeId>>,
    pub rule: &'static str,
}

/// Why a name has no single linkage. Never a guess.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkError {
    /// No top-level binding of the world carries the name.
    NotFound,
    /// The name is internal, so it is not an identity: several top-level
    /// bindings can render as one, and nothing links through it.
    InternalName,
    /// Two or more bindings claim one external name: [`A12_EXTERNAL_UNIQUE`]
    /// does not hold. [`LiveSet::of_modules`] refuses such a world, so this
    /// is a second line of defence, not an expected outcome.
    Ambiguous(usize),
}

//------------------------------------------------------------------------------
// Construction
//------------------------------------------------------------------------------

struct Build<'m> {
    modules: &'m [&'m Module],
    /// [`A12_EXTERNAL_UNIQUE`]: the size of the external-name index. The
    /// collision count is 0 by construction — [`Build::new`] refuses
    /// otherwise — and is reported beside it.
    external_names_defined: usize,
    nodes: Vec<TopRef>,
    /// `(module, binder) → node`.
    node_of: Vec<HashMap<BinderId, NodeId>>,
    /// External stable name → node. Only external names: the internal ones
    /// are not unique and nothing may be keyed by one.
    by_name: HashMap<&'m str, NodeId>,
    /// `(unit, module name)` of every module in the world.
    in_world: HashSet<(&'m str, &'m str)>,
    /// Module name → index, for [`A5_IN_WORLD_MISSING`].
    module_index: HashMap<&'m str, usize>,
    roots: Vec<Root>,
}

/// One target of one node's right-hand side, keyed so that the rule that
/// established it is part of the key.
type Target = (NodeId, &'static str);

impl<'m> Build<'m> {
    fn new(modules: &'m [&'m Module]) -> Result<Self, RootError> {
        let mut nodes: Vec<TopRef> = Vec::new();
        let mut node_of = vec![HashMap::new(); modules.len()];
        let mut by_name: HashMap<&str, NodeId> = HashMap::new();
        let mut collisions: BTreeSet<String> = BTreeSet::new();
        let mut in_world: HashSet<(&str, &str)> = HashSet::new();
        let mut module_index: HashMap<&str, usize> = HashMap::new();

        for (mi, m) in modules.iter().enumerate() {
            in_world.insert((m.unit.as_str(), m.name.as_str()));
            module_index.insert(m.name.as_str(), mi);
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    let n = nodes.len() as NodeId;
                    let external = is_external_name(&b.name);
                    nodes.push(TopRef {
                        key: TopKey {
                            module: mi as u32,
                            binder: pair.binder,
                        },
                        module_name: m.name.clone(),
                        name: b.name.clone(),
                        occ: b.occ.clone(),
                        external,
                        exported: b.exported.unwrap_or(false),
                    });
                    node_of[mi].insert(pair.binder, n);
                    if external && by_name.insert(b.name.as_str(), n).is_some() {
                        collisions.insert(b.name.clone());
                    }
                }
            }
        }
        if !collisions.is_empty() {
            return Err(RootError::NameCollisions(collisions.into_iter().collect()));
        }

        // A1: the root, found structurally through the world index.
        let mains: Vec<&&Module> = modules.iter().filter(|m| m.name == "Main").collect();
        let main = match mains.as_slice() {
            [] => return Err(RootError::NoMainModule),
            [m] => *m,
            _ => {
                return Err(RootError::AmbiguousMainModule(
                    mains.iter().map(|m| m.unit.clone()).collect(),
                ));
            }
        };
        let want = root_name(&main.unit);
        let hits: Vec<NodeId> = (0..nodes.len() as NodeId)
            .filter(|&n| nodes[n as usize].name == want)
            .collect();
        let roots = match hits.as_slice() {
            [] => return Err(RootError::NoRootBinding(want)),
            [n] => vec![Root {
                node: *n,
                rule: A1_ROOT_MAIN,
            }],
            many => return Err(RootError::AmbiguousRootBinding(want, many.len())),
        };

        Ok(Build {
            modules,
            external_names_defined: by_name.len(),
            nodes,
            node_of,
            by_name,
            in_world,
            module_index,
            roots,
        })
    }

    fn run(self) -> Result<LiveSet, RootError> {
        let n = self.nodes.len();
        // Out-edges per node, deduplicated by (target, rule) with an
        // occurrence count. BTreeMap, so the edge list is deterministic.
        let mut out: Vec<BTreeMap<Target, u32>> = vec![BTreeMap::new(); n];
        // The import and hole populations, per referring node, so they can
        // be split live/dead once the closure is known.
        let mut imports_at: Vec<BTreeMap<&str, u32>> = vec![BTreeMap::new(); n];
        let mut missing: BTreeMap<&str, MissingAcc> = BTreeMap::new();
        let mut non_bindings: BTreeMap<&str, (NonBinding, u32)> = BTreeMap::new();
        // A13: a Ref::Global occurrence whose own stable name is internal.
        // Expected empty, counted rather than assumed.
        let mut internal_at: Vec<BTreeMap<&str, u32>> = vec![BTreeMap::new(); n];

        for (ni, node) in self.nodes.iter().enumerate() {
            let m = self.modules[node.key.module as usize];
            let Some(rhs) = m.binding(node.key.binder).rhs else {
                continue;
            };
            for e in m.preorder(rhs) {
                let Expr::Var { name, .. } = m.expr(e) else {
                    continue;
                };
                match m.reference(e) {
                    // A2 — lexical, and the only way an internally-named
                    // top-level binding is ever reached.
                    Some(Ref::Local(b)) => {
                        if m.binding(b).site == BindSite::Top {
                            let to = self.node_of[node.key.module as usize][&b];
                            *out[ni].entry((to, A2_EDGE_LOCAL)).or_insert(0) += 1;
                        }
                    }
                    Some(Ref::Global) => {
                        if !is_external_name(name) {
                            *internal_at[ni].entry(name.as_str()).or_insert(0) += 1;
                        }
                        match self.by_name.get(name.as_str()) {
                            // A3
                            Some(&to) => *out[ni].entry((to, A3_EDGE_GLOBAL)).or_insert(0) += 1,
                            None => match self.classify_global(m, e, name) {
                                Global::Import(k) => *imports_at[ni].entry(k).or_insert(0) += 1,
                                Global::NonBinding { key, kind } => {
                                    let slot = non_bindings.entry(key).or_insert((kind, 0));
                                    slot.1 += 1;
                                }
                                Global::Missing { module } => {
                                    let slot = missing.entry(name.as_str()).or_insert(MissingAcc {
                                        module,
                                        occurrences: 0,
                                        referrers: BTreeSet::new(),
                                    });
                                    slot.occurrences += 1;
                                    slot.referrers.insert(ni as NodeId);
                                }
                            },
                        }
                    }
                    None => {}
                }
            }
        }

        // A6 — the closure, breadth-first, so the witness is shortest.
        let witness = closure(&self.roots, &out, n);

        // Reverse edges, for the dead reasons and for `--explain`.
        let mut referrers: Vec<BTreeSet<NodeId>> = vec![BTreeSet::new(); n];
        for (from, targets) in out.iter().enumerate() {
            for &(to, _) in targets.keys() {
                referrers[to as usize].insert(from as NodeId);
            }
        }

        let mut live: Vec<LiveBinding> = Vec::new();
        let mut dead: Vec<DeadBinding> = Vec::new();
        for i in 0..n {
            let id = i as NodeId;
            match &witness[i] {
                Some(w) => live.push(LiveBinding {
                    node: id,
                    witness: w.clone(),
                    rule: A9_WITNESS,
                }),
                None => {
                    let refs: Vec<NodeId> = referrers[i].iter().copied().collect();
                    let reason = if refs.is_empty() {
                        DeadReason::DeadNoReferences
                    } else {
                        DeadReason::DeadReferencedOnlyFromDead
                    };
                    dead.push(DeadBinding {
                        node: id,
                        reason,
                        referrers: refs,
                        rule: reason.rule(),
                    });
                }
            }
        }

        // Imports, split by the liveness of the referring binding.
        let mut imports: BTreeMap<String, ImportUse> = BTreeMap::new();
        for (i, at) in imports_at.iter().enumerate() {
            let is_live = witness[i].is_some();
            for (&k, &c) in at {
                let u = imports.entry(k.to_string()).or_default();
                if is_live {
                    u.from_live += c;
                } else {
                    u.from_dead += c;
                }
            }
        }

        // A5, and A11's bound on what it could cost. The candidate lookup
        // is by occurrence name inside the named module — a *name* match,
        // level 6, used only to answer "how much could this hole hide?".
        let mut occ_index: Vec<BTreeMap<&str, Vec<NodeId>>> =
            vec![BTreeMap::new(); self.modules.len()];
        for (i, t) in self.nodes.iter().enumerate() {
            occ_index[t.key.module as usize]
                .entry(t.occ.as_str())
                .or_default()
                .push(i as NodeId);
        }
        let mut in_world_missing: Vec<Missing> = Vec::new();
        let mut extra: Vec<BTreeMap<Target, u32>> = vec![BTreeMap::new(); n];
        for (name, acc) in &missing {
            let occ = split_stable_name(name).map(|(_, _, o)| o).unwrap_or("");
            let candidates: Vec<NodeId> = self
                .module_index
                .get(acc.module)
                .and_then(|&mi| occ_index[mi].get(occ))
                .cloned()
                .unwrap_or_default();
            let live_referrers: BTreeSet<&str> = acc
                .referrers
                .iter()
                .filter(|&&r| witness[r as usize].is_some())
                .map(|&r| self.nodes[r as usize].module_name.as_str())
                .collect();
            let referenced_from_live = !live_referrers.is_empty();
            let candidates_dead = candidates
                .iter()
                .filter(|&&c| witness[c as usize].is_none())
                .count();
            for &r in &acc.referrers {
                for &c in &candidates {
                    *extra[r as usize]
                        .entry((c, A11_MISSING_IMPACT))
                        .or_insert(0) += 1;
                }
            }
            in_world_missing.push(Missing {
                name: (*name).to_string(),
                in_module: acc.module.to_string(),
                occurrences: acc.occurrences,
                referrers: acc.referrers.iter().copied().collect(),
                referenced_from_live,
                live_referrer_modules: live_referrers.into_iter().map(|s| s.to_string()).collect(),
                candidates,
                candidates_dead,
                rule: A5_IN_WORLD_MISSING,
                impact_rule: A11_MISSING_IMPACT,
            });
        }
        // The sensitivity run: the same closure over `edges + name-matched
        // edges`. Its only output is a count.
        let repaired: Vec<BTreeMap<Target, u32>> = out
            .iter()
            .zip(extra.iter())
            .map(|(a, b)| {
                let mut c = a.clone();
                for (&k, &v) in b {
                    *c.entry(k).or_insert(0) += v;
                }
                c
            })
            .collect();
        let repaired_witness = closure(&self.roots, &repaired, n);
        let would_become_live: Vec<NodeId> = (0..n)
            .filter(|&i| witness[i].is_none() && repaired_witness[i].is_some())
            .map(|i| i as NodeId)
            .collect();

        let mut edges: Vec<EdgeRef> = Vec::new();
        for (from, targets) in out.iter().enumerate() {
            for (&(to, rule), &c) in targets {
                edges.push(EdgeRef {
                    from: from as NodeId,
                    to,
                    occurrences: c,
                    rule,
                });
            }
        }

        let zero = zero_reference_set(self.modules);
        let zero_nodes: Vec<NodeId> = zero
            .iter()
            .map(|k| self.node_of[k.module as usize][&k.binder])
            .collect();

        let mut accounting = self.accounting(
            &live,
            &dead,
            &edges,
            &imports,
            &in_world_missing,
            &non_bindings,
            &zero_nodes,
            &would_become_live,
        );
        accounting.external_names_defined = self.external_names_defined;
        accounting.external_name_collisions = 0; // Build::new refuses otherwise.
        let mut foreign: BTreeMap<String, ImportUse> = BTreeMap::new();
        for (i, at) in internal_at.iter().enumerate() {
            for (&name, &count) in at {
                let entry = foreign.entry(name.to_string()).or_default();
                if witness[i].is_some() {
                    entry.from_live += count;
                } else {
                    entry.from_dead += count;
                }
            }
        }
        accounting.global_internal_names = foreign.len();
        accounting.global_internal_occurrences = foreign
            .values()
            .map(|use_| u64::from(use_.from_live) + u64::from(use_.from_dead))
            .sum();
        accounting.unique_collisions = self
            .modules
            .iter()
            .map(|m| m.unique_collisions().len())
            .sum();
        Ok(LiveSet {
            modules: self.modules.iter().map(|m| m.name.clone()).collect(),
            nodes: self.nodes,
            roots: self.roots,
            live,
            dead,
            edges,
            imports,
            foreign,
            in_world_missing,
            zero_reference: zero_nodes,
            accounting,
            trusted: TRUSTED,
        })
    }

    /// What a [`Ref::Global`] occurrence that names no in-world top-level
    /// binding actually is. The stable name decides the module; GHC's own
    /// flags decide whether a name inside an in-world module can be
    /// explained without a binding.
    fn classify_global(&self, m: &'m Module, at: ExprId, name: &'m str) -> Global<'m> {
        let Some((unit, module, _)) = split_stable_name(name) else {
            // No unit and no module at all: an internal name on a global
            // occurrence. It links to nothing and belongs to no module.
            return Global::Import(name);
        };
        if !self.in_world.contains(&(unit, module)) {
            return Global::Import(name);
        }
        // An in-world module, and no top-level binding. GHC's id table is
        // the authority on why.
        let info = m.id_info(at);
        if info.is_some_and(|i| i.data_con.is_some()) {
            return Global::NonBinding {
                key: name,
                kind: NonBinding::DataCon,
            };
        }
        if info.is_some_and(|i| i.is_class_op) {
            return Global::NonBinding {
                key: name,
                kind: NonBinding::ClassOp,
            };
        }
        if WIRED_IN_WITHOUT_SOURCE.contains(&name) {
            return Global::NonBinding {
                key: name,
                kind: NonBinding::WiredIn,
            };
        }
        Global::Missing { module }
    }

    #[allow(clippy::too_many_arguments)]
    fn accounting(
        &self,
        live: &[LiveBinding],
        dead: &[DeadBinding],
        edges: &[EdgeRef],
        imports: &BTreeMap<String, ImportUse>,
        missing: &[Missing],
        non_bindings: &BTreeMap<&str, (NonBinding, u32)>,
        zero: &[NodeId],
        would_become_live: &[NodeId],
    ) -> Accounting {
        let mut a = Accounting {
            modules: self
                .modules
                .iter()
                .map(|m| ModuleAcct {
                    module: m.name.clone(),
                    ..Default::default()
                })
                .collect(),
            top: self.nodes.len(),
            live: live.len(),
            dead: dead.len(),
            roots: self.roots.len(),
            edges: edges.len(),
            edges_local: edges.iter().filter(|e| e.rule == A2_EDGE_LOCAL).count(),
            edges_global: edges.iter().filter(|e| e.rule == A3_EDGE_GLOBAL).count(),
            edge_occurrences: edges.iter().map(|e| e.occurrences as u64).sum(),
            import_names: imports.len(),
            import_occurrences_live: imports.values().map(|u| u.from_live as u64).sum(),
            import_occurrences_dead: imports.values().map(|u| u.from_dead as u64).sum(),
            in_world_missing: missing.len(),
            ..Default::default()
        };
        for t in &self.nodes {
            a.modules[t.key.module as usize].top += 1;
        }
        let live_set: HashSet<NodeId> = live.iter().map(|l| l.node).collect();
        for l in live {
            a.modules[self.nodes[l.node as usize].key.module as usize].live += 1;
        }
        for d in dead {
            let row = &mut a.modules[self.nodes[d.node as usize].key.module as usize];
            match d.reason {
                DeadReason::DeadNoReferences => {
                    row.dead_no_refs += 1;
                    a.dead_no_refs += 1;
                }
                DeadReason::DeadReferencedOnlyFromDead => {
                    row.dead_only_from_dead += 1;
                    a.dead_only_from_dead += 1;
                }
            }
        }
        for (kind, count) in non_bindings.values() {
            let totals = &mut a.in_world_non_bindings;
            let (names, occurrences) = match kind {
                NonBinding::DataCon => {
                    (&mut totals.data_con_names, &mut totals.data_con_occurrences)
                }
                NonBinding::ClassOp => {
                    (&mut totals.class_op_names, &mut totals.class_op_occurrences)
                }
                NonBinding::WiredIn => {
                    (&mut totals.wired_in_names, &mut totals.wired_in_occurrences)
                }
            };
            *names += 1;
            *occurrences += count;
        }
        let mut cands: BTreeSet<NodeId> = BTreeSet::new();
        for m in missing {
            a.missing_impact.occurrences += m.occurrences;
            if m.referenced_from_live {
                a.missing_impact.names_referenced_from_live += 1;
            }
            if m.candidates.is_empty() {
                a.missing_impact.names_without_candidate += 1;
            }
            cands.extend(m.candidates.iter().copied());
        }
        a.missing_impact.names = missing.len();
        a.missing_impact.candidates = cands.len();
        a.missing_impact.candidates_dead = cands.iter().filter(|c| !live_set.contains(c)).count();
        a.missing_impact.would_become_live = would_become_live.len();
        for &w in would_become_live {
            *a.missing_impact
                .would_become_live_by_module
                .entry(self.nodes[w as usize].module_name.clone())
                .or_insert(0) += 1;
        }
        let suspect: BTreeSet<&str> = missing
            .iter()
            .filter(|m| m.referenced_from_live)
            .map(|m| m.in_module.as_str())
            .collect();
        a.missing_impact.suspect_dead = dead
            .iter()
            .filter(|d| suspect.contains(self.nodes[d.node as usize].module_name.as_str()))
            .count();
        a.missing_impact.suspect_modules = suspect.into_iter().map(|s| s.to_string()).collect();

        // The subset gate: M2.4c's own predicate, crossed with the rooted
        // verdicts.
        let root_set: HashSet<NodeId> = self.roots.iter().map(|r| r.node).collect();
        a.zero_reference = zero.len();
        a.zero_reference_roots = zero.iter().filter(|z| root_set.contains(z)).count();
        a.zero_reference_live = zero
            .iter()
            .filter(|z| live_set.contains(z) && !root_set.contains(z))
            .count();
        let zero_dead = zero.iter().filter(|z| !live_set.contains(z)).count();
        a.additional_dead = dead.len() - zero_dead;
        a
    }
}

struct MissingAcc<'m> {
    module: &'m str,
    occurrences: u32,
    referrers: BTreeSet<NodeId>,
}

enum Global<'m> {
    /// A name outside the world.
    Import(&'m str),
    /// A name inside the world that GHC's own flags explain without a
    /// top-level binding.
    NonBinding { key: &'m str, kind: NonBinding },
    /// A name inside the world that nothing explains: a hole.
    Missing { module: &'m str },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NonBinding {
    DataCon,
    ClassOp,
    WiredIn,
}

/// [`A6_LIVE_CLOSURE`] and [`A9_WITNESS`] in one pass: breadth-first from
/// the roots over sorted adjacency, so the recorded path is a shortest one
/// and the result does not depend on hash order.
fn closure(roots: &[Root], out: &[BTreeMap<Target, u32>], n: usize) -> Vec<Option<Vec<NodeId>>> {
    let mut witness: Vec<Option<Vec<NodeId>>> = vec![None; n];
    let mut queue: VecDeque<NodeId> = VecDeque::new();
    for r in roots {
        if witness[r.node as usize].is_none() {
            witness[r.node as usize] = Some(vec![r.node]);
            queue.push_back(r.node);
        }
    }
    while let Some(x) = queue.pop_front() {
        let path = witness[x as usize].clone().expect("queued without a path");
        for &(to, _) in out[x as usize].keys() {
            if witness[to as usize].is_none() {
                let mut p = path.clone();
                p.push(to);
                witness[to as usize] = Some(p);
                queue.push_back(to);
            }
        }
    }
    witness
}

/// M2.4c's zero-reference set, computed by **its own predicate**
/// ([`Program::is_unreachable_top`]) over every top-level binding of the
/// world. Nothing here reimplements it; the two cannot drift.
pub fn zero_reference_set(modules: &[&Module]) -> BTreeSet<TopKey> {
    let p = Program::new(modules.iter().copied());
    let mut out = BTreeSet::new();
    for (mi, m) in modules.iter().enumerate() {
        for bind in &m.top {
            for pair in &bind.pairs {
                if p.is_unreachable_top(mi, pair.binder) {
                    out.insert(TopKey {
                        module: mi as u32,
                        binder: pair.binder,
                    });
                }
            }
        }
    }
    out
}

/// The flat top-level pair index a node lies in, by climbing to the
/// arena's root. Used by the verifier, which never walks a right-hand side
/// top-down.
pub fn enclosing_top_pair(m: &Module, node: ExprId) -> Option<usize> {
    let mut cur = node;
    while let Some(p) = m.parent[cur as usize] {
        cur = p;
    }
    match m.edge[cur as usize] {
        Edge::Top { pair } => Some(pair as usize),
        _ => None,
    }
}

/// The binder of every top-level pair of a module, in the flat order
/// [`Edge::Top`] indexes.
pub fn top_pair_binders(m: &Module) -> Vec<BinderId> {
    m.top
        .iter()
        .flat_map(|b| b.pairs.iter().map(|p| p.binder))
        .collect()
}
