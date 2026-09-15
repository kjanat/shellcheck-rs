//! A second, independent derivation of every **positive** M2.4 claim: the
//! class-op targets and bounded dictionary sets of [M2.4c](crate::dictflow),
//! its dictionary-erasure verdicts, and the higher-order representation
//! verdicts and clone plans of [M2.4d](crate::higher).
//!
//! The discipline is the one M2.2 stage 2 ([`crate::verify`]) set and M2.3e
//! ([`crate::verify_rep`]) repeated: a second implementation that **shares
//! nothing with the analyses it checks beyond the IR** and a short, named
//! list of trusted inputs; it re-derives every claim whose being wrong
//! would be a miscompile, and every disagreement is settled by fixing
//! whichever side is wrong. In particular this module does **not** use
//! [`crate::classops`]'s walk, [`crate::dictflow`], [`crate::higher`] or
//! [`crate::flow`]. It has its own closed-world index, its own dictionary
//! test, its own call-site enumeration, its own dispatch, its own two
//! fixpoints, its own totality domain with its own definition of *already
//! evaluated*, its own escape walk, its own type key and its own shape
//! classes.
//!
//! # Trusted inputs, named
//!
//! These are **consulted, not verified**. Nothing below may be read as a
//! check of them:
//!
//! 1. **The 17-class method-field table** ([`crate::classops::CLASSES`]).
//!    It is a level-5 axiom: dump format 5 carries neither a type nor an
//!    unfolding for a global, so a selector's `C a => …` type and its
//!    `case d of C:C … m … -> m` body are both absent and the field order
//!    cannot be derived from the dump at all. Re-asserting it here would
//!    be inventing a second unchecked assertion rather than checking the
//!    first, which is the argument M2.3e makes about the list axioms. The
//!    **data** is therefore shared; every *use* of it — which selector
//!    names which class, which field a method sits at, the `$pN<Class>`
//!    superclass reading, and the cross-check against the dictionary
//!    constructor's own `repArity` — is re-derived in this module.
//! 2. **`W0-CLOSED-WORLD` / `H0-CLOSED-WORLD`**: the 28 modules of the
//!    dump are the whole program. An assumption about the build; the dump
//!    cannot prove it, and this module cannot either.
//! 3. **GHC's own flags**: `isClassOpId` (through the id table's
//!    `isClassOp`), `isExportedId` (through a binder's `exported`), and
//!    the demand signatures' strictness bits. These are GHC's answers and
//!    this module reads them exactly as the analyses do — from the binder
//!    at a binding site, from the id table for an import.
//! 4. **The structured `Ty`** the plugin emits, and `TyCon` stable-name
//!    identity.
//!
//! Everything else — external-name identity, dictionary identity, producer
//! enumeration, dispatch, the union, totality, escape, shape classes,
//! capture types and clone tuples — is re-derived here from the arena.
//!
//! # Addressing, which is not sharing
//!
//! A claim has to *name* the thing it is about, and the names are IR
//! addresses: `Module` plus node id, `Module` plus [`BinderId`], a
//! constructor's stable name plus a value-field index. A dictionary
//! identity is addressed the way any dictionary built in the dump has to
//! be addressed — the module and node of its constructor application, or
//! the stable name of an imported dfun — and *which node that is* is
//! re-derived here. Agreeing on an address is not sharing a derivation.
//!
//! # What is re-derived, and why those
//!
//! | claim | a wrong one costs |
//! |---|---|
//! | `Exact(target)` | a call is redirected into the wrong instance's method |
//! | a bounded `DictSet` | an instance outside the set is dispatched at run time |
//! | `Erasable` / `ErasableWithClone` / `ErasableWithObligation` | a dictionary that is still needed — or a force that still has to happen — is deleted |
//! | `ExactClosure` / `TypeShapeUniform` / `FiniteClosureSet` / `CloneRequired` | one representation given to a slot two live closures disagree about |
//! | a clone plan | fewer specialisations than the call sites that exist |
//!
//! A wrong `Unresolved` or `Preserve` costs only coverage, so nothing here
//! re-derives those.
//!
//! Refusals are split the way [`crate::verify_rep`] splits them: an `X_`
//! refusal (`D`) says the analysis claimed something this derivation
//! refutes; a `C_` refusal is this derivation being blunter than the
//! analysis and costs coverage only.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use h2r_core_ir::{
    AltCon, BindSite, Binder, BinderId, BinderKind, DataConInfo, Edge, Expr, ExprId, IdInfo,
    Module, Ty,
};
use serde::Serialize;

/// **Trusted input 1.** The asserted 17-class method-field table. Only the
/// data is taken; every reading of it below is this module's own.
use crate::classops::{CLASSES, ClassSpec};

//------------------------------------------------------------------------------
// Refusal vocabulary
//------------------------------------------------------------------------------

// `X_` — the analysis claimed something this derivation refutes.
pub const X_SET_DIFFERS: &str = "the-re-derived-dictionary-set-is-a-different-set";
pub const X_TARGET_DIFFERS: &str = "the-re-derived-method-target-is-a-different-binding";
pub const X_NO_TARGET: &str = "Exact-claimed-but-this-walk-reaches-no-single-target";
pub const X_NOT_TOTAL: &str = "Erasable-claimed-but-the-producer-is-not-proven-total";
pub const X_ESCAPES: &str = "Erasable-claimed-but-the-dictionary-is-used-as-an-ordinary-value";
pub const X_INSTANCES_DIFFER: &str = "the-re-derived-instance-count-is-different";
pub const X_CLONES_DIFFER: &str = "the-re-derived-clone-tuple-count-is-different";
pub const X_SHARED_SLOT: &str = "one-representation-claimed-at-an-exported-or-valued-slot";
pub const X_OPAQUE_PRODUCER: &str = "one-representation-claimed-with-an-opaque-producer";
pub const X_CLASSES_DIFFER: &str = "the-re-derived-shape-class-count-is-different";
pub const X_PRODUCERS_DIFFER: &str = "the-re-derived-producer-set-is-a-different-set";
pub const X_NOT_A_PARAM_SLOT: &str = "CloneRequired-claimed-at-a-slot-that-is-not-a-parameter";
pub const X_NO_OBLIGATION: &str = "an-obligation-is-claimed-where-this-walk-proves-no-force";

// `C_` — this derivation declining: a coverage loss, never a claim.
pub const C_SET_TOP: &str = "this-walk-cannot-account-for-every-producer-here";
pub const C_NO_BOUNDARY: &str = "this-walk-collected-no-boundary-for-that-slot";
pub const C_NO_PARAM: &str = "this-walk-collected-no-dictionary-parameter-for-that-binder";
pub const C_NO_SITE: &str = "this-walk-collected-no-class-op-site-at-that-node";
pub const C_NO_VALUE: &str = "this-walk-collected-no-dictionary-value-with-that-key";
pub const C_NO_OWNER: &str = "this-walk-collected-no-owner-plan-for-that-function";
pub const C_CLASS_UNKNOWN: &str = "this-walk-cannot-name-the-class-of-that-selector";
pub const C_BUDGET: &str = "this-walk-exceeded-one-of-its-own-budgets";
pub const C_MODULE_MISSING: &str = "the-claim-names-a-module-this-walk-does-not-hold";

/// Is this refusal a coverage loss rather than a claim about the analysis?
/// Every `C_` reason above, and nothing else.
pub fn is_coverage_refusal(why: &str) -> bool {
    matches!(
        why,
        C_SET_TOP
            | C_NO_BOUNDARY
            | C_NO_PARAM
            | C_NO_SITE
            | C_NO_VALUE
            | C_NO_OWNER
            | C_CLASS_UNKNOWN
            | C_BUDGET
            | C_MODULE_MISSING
    )
}

//------------------------------------------------------------------------------
// Budgets — this walk's own, deliberately not the analyses'
//------------------------------------------------------------------------------

/// Fixpoint rounds before every unsettled node is forced to `Top`.
const ROUNDS: usize = 64;
/// Members of one abstract set before it collapses to `Top`.
const SET_CAP: usize = 32;
/// Expression steps in one evaluation.
const STEPS: usize = 8_000;
/// Nested dictionary-field reads.
const NEST: usize = 10;

//------------------------------------------------------------------------------
// Claims — plain data, so that nothing of the analyses reaches this module
//------------------------------------------------------------------------------

/// Which positive claim this is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ClaimKind {
    /// A class-op site whose method target M2.4c resolved exactly.
    SiteExact,
    /// A class-op site whose dictionary set M2.4c bounded.
    SiteBounded,
    /// A dictionary parameter whose set M2.4c bounded.
    ParamBounded,
    /// A dictionary value M2.4c calls `Erasable`.
    ValueErasure,
    /// A dictionary parameter M2.4c calls `Erasable`,
    /// `ErasableWithClone(n)` or `ErasableWithObligation`.
    ParamErasure,
    /// An owner-level dictionary clone plan.
    DictClonePlan,
    /// A higher-order boundary M2.4d calls `ExactClosure`,
    /// `TypeShapeUniform`, `CloneRequired(n)` or `FiniteClosureSet(n)`.
    HigherVerdict,
    /// An owner-level closure clone plan.
    ClosureClonePlan,
}

impl ClaimKind {
    pub fn name(self) -> &'static str {
        match self {
            ClaimKind::SiteExact => "class-op site Exact(target)",
            ClaimKind::SiteBounded => "class-op site bounded DictSet",
            ClaimKind::ParamBounded => "dictionary parameter bounded DictSet",
            ClaimKind::ValueErasure => "dictionary value erasure",
            ClaimKind::ParamErasure => "dictionary parameter erasure",
            ClaimKind::DictClonePlan => "dictionary clone plan",
            ClaimKind::HigherVerdict => "higher-order verdict",
            ClaimKind::ClosureClonePlan => "closure clone plan",
        }
    }
}

/// Which slot of the higher-order population a claim is about.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ClaimSlot {
    Param { binder: BinderId },
    Return { binder: BinderId },
    Field { con: String, index: usize },
}

/// What a claim is about, as an IR address.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Subject {
    Site { module: String, node: ExprId },
    Param { module: String, binder: BinderId },
    Value { key: String },
    DictOwner { module: String, owner: BinderId },
    Boundary { module: String, slot: ClaimSlot },
    ClosureOwner { module: String, owner: BinderId },
}

impl Subject {
    pub fn module(&self) -> &str {
        match self {
            Subject::Site { module, .. }
            | Subject::Param { module, .. }
            | Subject::DictOwner { module, .. }
            | Subject::Boundary { module, .. }
            | Subject::ClosureOwner { module, .. } => module,
            Subject::Value { .. } => "",
        }
    }
}

/// One positive M2.4 claim, as plain data.
#[derive(Debug, Clone, Serialize)]
pub struct Claim {
    pub kind: ClaimKind,
    pub subject: Subject,
    /// How the claim reads in a report.
    pub what: String,
    /// The dictionary identities, or the closure producer identities, the
    /// claim asserts reach the subject.
    pub keys: Vec<String>,
    /// The method target, for [`ClaimKind::SiteExact`].
    pub target: Option<String>,
    /// The verdict's own label.
    pub verdict: String,
    /// The cardinality the verdict carries: instances, shape classes, or
    /// planned clones.
    pub n: usize,
}

/// Why this walk will not re-derive a claim.
#[derive(Debug, Clone, Serialize)]
pub struct Refusal {
    pub why: &'static str,
    pub detail: String,
}

impl Refusal {
    fn new(why: &'static str, detail: impl Into<String>) -> Refusal {
        Refusal {
            why,
            detail: detail.into(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Disagreement {
    pub claim: Claim,
    pub refusal: Refusal,
}

/// One adversarial shape, counted in the real dump beside its hand-built
/// regression test, so that a test is never the only evidence a rule was
/// exercised.
#[derive(Debug, Clone, Serialize)]
pub struct ShapeRow {
    pub n: usize,
    pub name: &'static str,
    /// The verdict this shape must get.
    pub verdict: &'static str,
    /// A representative, `Module node N`, or `—` when the dump has none.
    pub at: String,
}

/// The verification, whole.
#[derive(Debug, Clone, Default, Serialize)]
pub struct Audit {
    pub checked: usize,
    pub agreed: usize,
    /// (kind, checked, re-derived, `D` refusals, `C` refusals).
    pub by_kind: Vec<(ClaimKind, usize, usize, usize, usize)>,
    pub disagreements: Vec<Disagreement>,
    pub shapes: Vec<ShapeRow>,
    /// This walk's own fixpoint rounds, for the report.
    pub dict_rounds: usize,
    pub tot_rounds: usize,
    pub closure_rounds: usize,
    /// `case` nodes this walk's totality transfer reached on a dictionary
    /// path, over every round. Zero means erasure can delete no force
    /// anywhere, for a stronger reason than every force being discharged.
    pub dict_case_nodes: usize,
    /// Clone plans with a **set-valued** tuple component: one call site
    /// whose argument is itself a multi-instance or multi-class parameter,
    /// which a monovariant fixpoint can only give as a set. While these are
    /// non-zero, a planned clone count is a **lower bound**.
    pub dict_plans_set_valued: usize,
    pub closure_plans_set_valued: usize,
    /// This walk's own population sizes, for the report.
    pub own_sites: usize,
    pub own_params: usize,
    pub own_values: usize,
    pub own_boundaries: usize,
}

impl Audit {
    /// Refusals that say an analysis claimed something this walk refutes.
    pub fn real_disagreements(&self) -> usize {
        self.disagreements
            .iter()
            .filter(|d| !is_coverage_refusal(d.refusal.why))
            .count()
    }
    /// Refusals that are only this walk declining.
    pub fn coverage_refusals(&self) -> usize {
        self.disagreements.len() - self.real_disagreements()
    }
}

//------------------------------------------------------------------------------
// This walk's own IR helpers
//
// Written out here rather than shared with the analyses, so that a mistake
// about what a value argument is, what a head's signature says, or which
// names are unique cannot be common to both sides.
//------------------------------------------------------------------------------

/// `$unit$Module$occ`, split. GHC's `nameStableString`.
fn parts(name: &str) -> Option<(&str, &str, &str)> {
    let rest = name.strip_prefix('$')?;
    let (unit, rest) = rest.split_once('$')?;
    let (module, occ) = rest.split_once('$')?;
    Some((unit, module, occ))
}

/// Is this name *external* — one another module could refer to, and the
/// only kind that is unique in the program?
///
/// GHC renders a name it has not externalised as `$_sys$<occ>` or
/// `$_in$<occ>`, with no unit and no module. A three-way split on `$` is
/// fooled whenever that `<occ>` itself contains one — `$_sys$poly_$j` reads
/// as unit `_sys`, module `poly_` — so the two pseudo-units are rejected
/// explicitly. Re-derived here; the count of collisions it prevents is
/// checked by [`World::collisions`].
fn external(name: &str) -> bool {
    match parts(name) {
        Some((unit, module, _)) => {
            !unit.is_empty() && !module.is_empty() && unit != "_sys" && unit != "_in"
        }
        None => false,
    }
}

/// A name GHC gives a dictionary: `$d…`, `$p…`, or `$f<Class><Type>` (a
/// dfun, whose name never ends in a digit — that suffix marks a worker or a
/// specialisation).
fn dictionary_name(occ: &str) -> bool {
    if occ.starts_with("$d") || occ.starts_with("$p") {
        return true;
    }
    occ.starts_with("$f") && !occ.ends_with(|c: char| c.is_ascii_digit())
}

/// The value arguments of a spine: everything that is not a type or a
/// coercion.
fn vargs(m: &Module, args: &[ExprId]) -> Vec<ExprId> {
    args.iter()
        .copied()
        .filter(|a| !matches!(m.expr(m.strip(*a)), Expr::Type { .. } | Expr::Coercion))
        .collect()
}

/// What is known about the head of a spine. **Trusted input 3**: the
/// `isClassOp` bit, the `exported` bit and the strictness bits are GHC's
/// own and are read from the authoritative source — the binder at its
/// binding site when the head is bound in this module, the id table when
/// it is an import.
#[derive(Debug, Clone, Copy)]
struct Sig<'m> {
    arity: u32,
    data_con: Option<&'m DataConInfo>,
    is_class_op: bool,
}

fn head_sig<'m>(m: &'m Module, head: ExprId) -> Option<Sig<'m>> {
    let Expr::Var { name, .. } = m.expr(head) else {
        return None;
    };
    if let Some(b) = m.resolve(head) {
        let binder: &Binder = m.binder(b);
        return Some(Sig {
            arity: binder.arity.unwrap_or(0),
            // A binder bound in this module is never a constructor and
            // never a class method: those are globals.
            data_con: None,
            is_class_op: false,
        });
    }
    let info: &IdInfo = m.ids.get(name)?;
    Some(Sig {
        arity: info.arity,
        data_con: info.data_con.as_ref(),
        is_class_op: info.is_class_op,
    })
}

/// The class table entry for a class type constructor's stable name.
fn class_spec_of_tycon(name: &str) -> Option<&'static ClassSpec> {
    let (_, module, occ) = parts(name)?;
    CLASSES
        .iter()
        .find(|c| c.module == module && c.class == occ)
}

/// The class a dictionary's structured type names, when the table carries
/// it. Re-derived from the head `TyCon` of the type — GHC type identity,
/// never a rendering.
fn class_of_ty(t: &Ty) -> Option<String> {
    let tc = t.tycon()?;
    class_spec_of_tycon(&tc.name)?;
    Some(tc.name.clone())
}

/// The class whose dictionary constructor this stable name is.
fn dict_con_spec(name: &str) -> Option<&'static ClassSpec> {
    let (_, module, occ) = parts(name)?;
    let class = occ.strip_prefix("C:")?;
    CLASSES
        .iter()
        .find(|c| c.class == class && c.module == module)
}

/// The class a selector belongs to and the dictionary field it reads,
/// re-derived from the table: a `$pN<Class>` selector names its class in
/// its own occurrence name and reads superclass field `N-1`, and a method
/// selector reads `supers + position`.
fn selector_field(module: &str, occ: &str) -> Option<(&'static ClassSpec, usize)> {
    if let Some(rest) = occ.strip_prefix("$p") {
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        let class = &rest[digits.len()..];
        let n: usize = digits.parse().ok()?;
        if n == 0 {
            return None;
        }
        let spec = CLASSES
            .iter()
            .find(|c| c.class == class && c.module == module)?;
        if n > spec.supers {
            return None;
        }
        return Some((spec, n - 1));
    }
    let spec = CLASSES
        .iter()
        .find(|c| c.module == module && c.methods.contains(&occ))?;
    let at = spec.methods.iter().position(|x| *x == occ)?;
    Some((spec, spec.supers + at))
}

//------------------------------------------------------------------------------
// The closed world, indexed by this walk
//------------------------------------------------------------------------------

/// One dictionary identity. The key is the address: `Module#node` of the
/// constructor application for a dictionary built in the dump, the stable
/// name for an imported dfun. **Never the binding's name** — a top-level
/// binder GHC has not externalised has an internal name that several
/// bindings of one module share.
#[derive(Debug, Clone)]
struct DictValue {
    key: String,
    binder: Option<BinderId>,
    mi: usize,
    node: ExprId,
    imported: bool,
    /// The dictionary parameters of the dfun that builds it, if any.
    params: Vec<BinderId>,
}

/// The dump, indexed for whole-program questions. Built here, from the
/// arena, and shared with no analysis.
pub struct World<'m> {
    modules: Vec<&'m Module>,
    /// External stable name → the top-level binding that defines it.
    tops: HashMap<String, (usize, BinderId, ExprId)>,
    /// External stable names two distinct top-level bindings claim.
    /// Asserted empty: *external ⇒ unique* is what makes the linkage table
    /// a linkage table.
    pub collisions: Vec<String>,
    /// Stable name → every *global* `Var` occurrence of it, anywhere.
    gvars: HashMap<String, Vec<(usize, ExprId)>>,
    lam_of: Vec<HashMap<BinderId, ExprId>>,
    top_of_rhs: Vec<HashMap<ExprId, BinderId>>,
    case_scrut: Vec<HashMap<BinderId, ExprId>>,
    /// An alt binder bound at a **dictionary** constructor's field: the
    /// scrutinee, the class, and the *value*-field index.
    dict_alt_field: Vec<HashMap<BinderId, (ExprId, &'static ClassSpec, usize)>>,
    /// An alt binder bound at any constructor's field: the constructor's
    /// stable name and the *value*-field index. A constructor application
    /// is indexed by its value arguments, and an alternative also binds the
    /// existential **type** binders, so the index is counted over the value
    /// binders alone.
    any_alt_field: Vec<HashMap<BinderId, (String, usize)>>,
    /// A dictionary-constructor application node → its dictionary key.
    con_key: Vec<HashMap<ExprId, String>>,
    /// Constructor stable name → every saturated application of it.
    con_apps: HashMap<String, Vec<(usize, ExprId)>>,
    values: BTreeMap<String, DictValue>,
}

impl<'m> World<'m> {
    pub fn new(modules: impl IntoIterator<Item = &'m Module>) -> World<'m> {
        let modules: Vec<&Module> = modules.into_iter().collect();
        let n = modules.len();
        let mut w = World {
            modules,
            tops: HashMap::new(),
            collisions: Vec::new(),
            gvars: HashMap::new(),
            lam_of: vec![HashMap::new(); n],
            top_of_rhs: vec![HashMap::new(); n],
            case_scrut: vec![HashMap::new(); n],
            dict_alt_field: vec![HashMap::new(); n],
            any_alt_field: vec![HashMap::new(); n],
            con_key: vec![HashMap::new(); n],
            con_apps: HashMap::new(),
            values: BTreeMap::new(),
        };
        w.index();
        w.index_dictionaries();
        w
    }

    fn m(&self, mi: usize) -> &'m Module {
        self.modules[mi]
    }

    pub fn module_index(&self, name: &str) -> Option<usize> {
        self.modules.iter().position(|m| m.name == name)
    }

    fn index(&mut self) {
        for mi in 0..self.modules.len() {
            let m = self.m(mi);
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    if external(&b.name) {
                        match self.tops.entry(b.name.clone()) {
                            std::collections::hash_map::Entry::Vacant(e) => {
                                e.insert((mi, pair.binder, pair.rhs));
                            }
                            std::collections::hash_map::Entry::Occupied(e) => {
                                if *e.get() != (mi, pair.binder, pair.rhs) {
                                    self.collisions.push(b.name.clone());
                                }
                            }
                        }
                    }
                    self.top_of_rhs[mi].insert(pair.rhs, pair.binder);
                }
            }
            for id in 0..m.exprs.len() as ExprId {
                match m.expr(id) {
                    Expr::Lam { binder, .. } => {
                        self.lam_of[mi].insert(*binder, id);
                    }
                    Expr::Var {
                        name, is_global, ..
                    } => {
                        if *is_global && m.resolve(id).is_none() {
                            self.gvars.entry(name.clone()).or_default().push((mi, id));
                        }
                    }
                    Expr::Case {
                        scrut,
                        binder,
                        alts,
                        ..
                    } => {
                        self.case_scrut[mi].insert(*binder, *scrut);
                        for alt in alts {
                            let AltCon::DataAlt { name, .. } = &alt.con else {
                                continue;
                            };
                            // Value-field index: type binders are skipped
                            // and do not advance it, because a constructor
                            // application is indexed by its value
                            // arguments alone.
                            let mut vi = 0usize;
                            let mut value_binders = 0usize;
                            for &bid in &alt.binders {
                                if m.binder(bid).kind != BinderKind::Tyvar {
                                    value_binders += 1;
                                }
                            }
                            let spec =
                                dict_con_spec(name).filter(|spec| spec.fields() == value_binders);
                            for &bid in &alt.binders {
                                if m.binder(bid).kind == BinderKind::Tyvar {
                                    continue;
                                }
                                self.any_alt_field[mi].insert(bid, (name.clone(), vi));
                                if let Some(spec) = spec {
                                    self.dict_alt_field[mi].insert(bid, (*scrut, spec, vi));
                                }
                                vi += 1;
                            }
                        }
                    }
                    _ => {}
                }
            }
            // Saturated constructor applications, by stable name.
            for id in 0..m.exprs.len() as ExprId {
                let is_app = matches!(m.expr(id), Expr::App { .. });
                if (!is_app && !matches!(m.expr(id), Expr::Var { .. })) || m.spine_root(id) != id {
                    continue;
                }
                let (head, args) = m.spine(id);
                let Some(dc) = head_sig(m, head).and_then(|s| s.data_con) else {
                    continue;
                };
                if vargs(m, &args).len() < dc.rep_arity as usize {
                    continue;
                }
                self.con_apps
                    .entry(dc.name.clone())
                    .or_default()
                    .push((mi, id));
            }
        }
    }

    /// Every dictionary identity in the closed world: the constructor
    /// application a top-level dictionary binding reduces to, every other
    /// saturated dictionary-constructor application, and every imported
    /// dfun with no binding here.
    fn index_dictionaries(&mut self) {
        for mi in 0..self.modules.len() {
            let m = self.m(mi);
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    let class = class_of_ty(m.binder_ty(pair.binder).fun_result());
                    if class.is_none() && !dictionary_name(&b.occ) {
                        continue;
                    }
                    let body = self.strip_lams(mi, pair.rhs);
                    if !self.is_dict_con_app(mi, body) {
                        continue;
                    }
                    let key = format!("{}#{body}", m.name);
                    self.con_key[mi].insert(body, key.clone());
                    self.values.insert(
                        key.clone(),
                        DictValue {
                            key,
                            binder: Some(pair.binder),
                            mi,
                            node: body,
                            imported: false,
                            params: self.lam_params(mi, pair.rhs),
                        },
                    );
                }
            }
        }
        for mi in 0..self.modules.len() {
            let m = self.m(mi);
            for id in 0..m.exprs.len() as ExprId {
                if !matches!(m.expr(id), Expr::App { .. }) || m.spine_root(id) != id {
                    continue;
                }
                if self.con_key[mi].contains_key(&id) || !self.is_dict_con_app(mi, id) {
                    continue;
                }
                let key = format!("{}#{id}", m.name);
                self.con_key[mi].insert(id, key.clone());
                self.values.insert(
                    key.clone(),
                    DictValue {
                        key,
                        binder: None,
                        mi,
                        node: id,
                        imported: false,
                        params: Vec::new(),
                    },
                );
            }
        }
        // An imported dfun: a global dictionary name with no binding here.
        // `$f<Class><Type>_$c<method>` is a *method* of one and `_$s…` a
        // specialisation of a method; neither is a dictionary.
        let mut imported: Vec<(String, usize, ExprId)> = Vec::new();
        for (name, occs) in &self.gvars {
            if self.tops.contains_key(name) {
                continue;
            }
            let Some((_, _, occ)) = parts(name) else {
                continue;
            };
            if !occ.starts_with("$f")
                || !dictionary_name(occ)
                || occ.contains("_$c")
                || occ.contains("_$s")
            {
                continue;
            }
            imported.push((name.clone(), occs[0].0, occs[0].1));
        }
        for (name, mi, node) in imported {
            self.values.insert(
                name.clone(),
                DictValue {
                    key: name.clone(),
                    binder: None,
                    mi,
                    node,
                    imported: true,
                    params: Vec::new(),
                },
            );
        }
    }

    /// Strip the manifest lambda chain, and the casts and ticks in it.
    fn strip_lams(&self, mi: usize, rhs: ExprId) -> ExprId {
        let m = self.m(mi);
        let mut cur = m.strip(rhs);
        while let Expr::Lam { body, .. } = m.expr(cur) {
            cur = m.strip(*body);
        }
        cur
    }

    /// Strip leading **type** lambdas only: a dictionary under `\@a ->` is
    /// the same dictionary at every type it is instantiated at, and nothing
    /// in this walk carries types through a dictionary expression.
    fn strip_ty_lams(&self, mi: usize, rhs: ExprId) -> ExprId {
        let m = self.m(mi);
        let mut cur = m.strip(rhs);
        while let Expr::Lam { binder, body } = m.expr(cur) {
            if m.binder(*binder).kind != BinderKind::Tyvar {
                break;
            }
            cur = m.strip(*body);
        }
        cur
    }

    /// The manifest value parameters of a right-hand side, in order.
    fn lam_params(&self, mi: usize, rhs: ExprId) -> Vec<BinderId> {
        let m = self.m(mi);
        let mut out = Vec::new();
        let mut cur = m.strip(rhs);
        while let Expr::Lam { binder, body } = m.expr(cur) {
            if m.binder(*binder).kind != BinderKind::Tyvar {
                out.push(*binder);
            }
            cur = m.strip(*body);
        }
        out
    }

    /// A saturated application of a class's dictionary constructor, with
    /// the table entry checked against the dump's own `repArity`.
    fn is_dict_con_app(&self, mi: usize, node: ExprId) -> bool {
        let m = self.m(mi);
        let (head, args) = m.spine(node);
        let Expr::Var { name, .. } = m.expr(head) else {
            return false;
        };
        let Some(spec) = dict_con_spec(name) else {
            return false;
        };
        let Some(dc) = head_sig(m, head).and_then(|s| s.data_con) else {
            return false;
        };
        dc.rep_arity as usize == spec.fields() && vargs(m, &args).len() >= spec.fields()
    }

    /// Every occurrence of a top-level binding, in every module: the local
    /// ones through the module's own binder, the rest by stable name.
    fn all_occurrences(&self, mi: usize, b: BinderId) -> Vec<(usize, ExprId)> {
        let m = self.m(mi);
        let mut out: Vec<(usize, ExprId)> = m.occurrences(b).iter().map(|&o| (mi, o)).collect();
        if m.binding(b).site == BindSite::Top
            && external(&m.binder(b).name)
            && let Some(g) = self.gvars.get(&m.binder(b).name)
        {
            out.extend(g.iter().copied());
        }
        out
    }
}

//------------------------------------------------------------------------------
// The abstract set
//------------------------------------------------------------------------------

/// A finite set of identities, or `Top` with the reason it is not bounded.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Set {
    Top(String),
    Fin(BTreeSet<String>),
}

impl Set {
    fn empty() -> Set {
        Set::Fin(BTreeSet::new())
    }
    fn one(k: &str) -> Set {
        Set::Fin([k.to_string()].into_iter().collect())
    }
    fn top(r: impl Into<String>) -> Set {
        Set::Top(r.into())
    }
    fn is_top(&self) -> bool {
        matches!(self, Set::Top(_))
    }
    fn keys(&self) -> BTreeSet<String> {
        match self {
            Set::Fin(s) => s.clone(),
            Set::Top(_) => BTreeSet::new(),
        }
    }
    fn reason(&self) -> Option<&str> {
        match self {
            Set::Top(r) => Some(r),
            _ => None,
        }
    }
    /// Monotone join; two `Top`s keep the lexicographically smaller reason
    /// so that a round's answer never depends on visit order.
    fn join(&mut self, other: &Set) {
        let joined = match (&*self, other) {
            (Set::Top(a), Set::Top(b)) => Set::Top(a.min(b).clone()),
            (Set::Top(a), _) => Set::Top(a.clone()),
            (_, Set::Top(b)) => Set::Top(b.clone()),
            (Set::Fin(a), Set::Fin(b)) => {
                let u: BTreeSet<String> = a.union(b).cloned().collect();
                if u.len() > SET_CAP {
                    Set::Top(R_BUDGET_SET.into())
                } else {
                    Set::Fin(u)
                }
            }
        };
        *self = joined;
    }
}

// This walk's own reasons. They are not compared with the analyses' — only
// the sets, the verdicts and the counts are.
const R_ANON: &str = "parameter-of-an-anonymous-lambda";
const R_VALUE_USE: &str = "function-used-as-a-value";
const R_PARTIAL: &str = "call-site-is-a-partial-application";
const R_UNREACHABLE: &str = "function-has-no-occurrence-in-the-closed-world";
const R_NOT_A_DICT: &str = "expression-is-not-a-dictionary";
const R_CON_FIELD: &str = "read-from-a-non-dictionary-constructor-field";
const R_UNKNOWN_CALL: &str = "produced-by-a-call-the-dump-cannot-see";
const R_HIGHER_ORDER: &str = "from-a-higher-order-parameter";
const R_DISPATCH_TAINTED: &str = "dispatched-from-a-site-with-an-unknown-dictionary";
const R_CLASS_UNKNOWN: &str = "class-not-in-the-class-table";
const R_NO_PRODUCER: &str = "no-producer-reaches-it";
/// The parameter sits behind a method no class-op site in the closed world
/// ever selects: nothing dispatches into it, so nothing reaches it.
const R_NEVER_DISPATCHED: &str = "the-method-behind-it-is-never-dispatched";
const R_BUDGET_SET: &str = "set-exceeded-this-walks-budget";
const R_BUDGET_ROUNDS: &str = "fixpoint-exceeded-this-walks-round-budget";
const R_BUDGET_STEPS: &str = "evaluation-exceeded-this-walks-step-budget";
const R_BUDGET_NEST: &str = "field-read-exceeded-this-walks-nesting-budget";
const R_METHOD_NOT_HERE: &str = "instance-method-not-in-the-dump";
const R_TABLE_MISMATCH: &str = "class-table-disagrees-with-repArity";
const R_NOT_A_CON: &str = "dictionary-is-not-a-constructor-application";
const R_NOT_A_FUNCTION: &str = "expression-is-not-a-function";
const R_OVER_APPLIED: &str = "over-applied";
const R_UNTRACKED_RETURN: &str = "return-slot-not-tracked";
const R_NO_CON_APPS: &str = "the-constructor-is-never-applied-in-the-closed-world";

//------------------------------------------------------------------------------
// Totality — its own lattice, its own transfer
//------------------------------------------------------------------------------

/// Whether deleting a dictionary computation would delete an evaluation.
/// `Total < Force < Unknown`, bottom `Total`, join `max`. **Not derived
/// from [`Set`]**: a bounded set says which dictionary an expression can
/// produce and says nothing about whether producing it terminates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Tot {
    Total,
    Force,
    Unknown,
}

/// A totality level with the force that witnesses it, when there is one:
/// the node whose evaluation erasure would delete, and the scrutinee that
/// would still have to be evaluated.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TotFact {
    level: Tot,
    witness: Option<(String, ExprId, ExprId)>,
}

impl TotFact {
    fn total() -> TotFact {
        TotFact {
            level: Tot::Total,
            witness: None,
        }
    }
    fn unknown() -> TotFact {
        TotFact {
            level: Tot::Unknown,
            witness: None,
        }
    }
    fn force(module: &str, at: ExprId, what: ExprId) -> TotFact {
        TotFact {
            level: Tot::Force,
            witness: Some((module.to_string(), at, what)),
        }
    }
    fn join(&mut self, other: &TotFact) {
        self.level = self.level.max(other.level);
        self.witness = match (&self.witness, &other.witness) {
            (Some(a), Some(b)) => Some(if a <= b { a.clone() } else { b.clone() }),
            (Some(a), None) => Some(a.clone()),
            (None, b) => b.clone(),
        };
    }
}

//------------------------------------------------------------------------------
// Part 1 — the dictionary flow, re-derived
//------------------------------------------------------------------------------

/// A method sitting at a dictionary field: the parameter behind it is fed
/// by whichever class-op site selects that field.
#[derive(Debug, Clone)]
struct DispatchSlot {
    dict: String,
    class: &'static str,
    field: usize,
    /// Which of the site's arguments *after* the dictionary feeds it.
    rest_index: usize,
}

#[derive(Debug, Clone, Default)]
struct Producers {
    top: Option<String>,
    calls: Vec<(usize, ExprId)>,
    slots: Vec<DispatchSlot>,
}

/// A dictionary parameter: one node of both fixpoints.
#[derive(Debug, Clone)]
struct DParam {
    mi: usize,
    binder: BinderId,
    module: String,
    owner_binder: Option<BinderId>,
    index: usize,
    producers: Producers,
    set: Set,
    tot: TotFact,
}

/// A class-op application site.
#[derive(Debug, Clone)]
struct DSite {
    mi: usize,
    module: String,
    node: ExprId,
    occ: String,
    spec: Option<&'static ClassSpec>,
    field: Option<usize>,
    dict: Option<ExprId>,
    rest: Vec<ExprId>,
    set: Set,
    /// The single method target, when there is one; the rendering is the
    /// address `Module#node name`.
    target: Result<Option<String>, String>,
}

/// Is this lambda binder a dictionary parameter? From the structured type
/// when the table names the class, and otherwise from GHC's own `$d`
/// naming of a dictionary binder.
fn dict_binder(m: &Module, b: BinderId) -> bool {
    let binder = m.binder(b);
    if binder.kind == BinderKind::Tyvar {
        return false;
    }
    class_of_ty(m.binder_ty(b)).is_some() || binder.occ.starts_with("$d")
}

/// The named function a lambda binder belongs to, and its index among that
/// function's manifest value parameters.
fn owner_of(w: &World, mi: usize, b: BinderId) -> (Option<BinderId>, usize) {
    let m = w.m(mi);
    let Some(&lam) = w.lam_of[mi].get(&b) else {
        return (None, 0);
    };
    let mut idx = 0usize;
    let mut cur = lam;
    loop {
        let Some(parent) = m.parent[cur as usize] else {
            return (w.top_of_rhs[mi].get(&cur).copied(), idx);
        };
        match m.edge[cur as usize] {
            Edge::LamBody if matches!(m.expr(parent), Expr::Lam { .. }) => {
                if let Expr::Lam { binder, .. } = m.expr(parent)
                    && m.binder(*binder).kind != BinderKind::Tyvar
                {
                    idx += 1;
                }
                cur = parent;
            }
            Edge::Cast | Edge::Tick => cur = parent,
            Edge::LetRhs { pair } => {
                return match m.expr(parent) {
                    Expr::Let { bind, .. } => (Some(bind.pairs[pair as usize].binder), idx),
                    _ => (None, idx),
                };
            }
            Edge::Top { .. } => return (w.top_of_rhs[mi].get(&cur).copied(), idx),
            _ => return (None, idx),
        }
    }
}

/// Is this occurrence a bare method field of a dictionary-constructor
/// application? Then whatever selects that field supplies the arguments.
fn method_slot(w: &World, mi: usize, occ: ExprId, index: usize) -> Option<DispatchSlot> {
    let m = w.m(mi);
    let mut cur = occ;
    while let Some(parent) = m.parent[cur as usize] {
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => cur = parent,
            Edge::AppArg => {
                let root = m.spine_root(parent);
                let key = w.con_key[mi].get(&root)?;
                let (head, args) = m.spine(root);
                let Expr::Var { name, .. } = m.expr(head) else {
                    return None;
                };
                let spec = dict_con_spec(name)?;
                let va = vargs(m, &args);
                let field = va.iter().position(|&a| m.strip(a) == m.strip(cur))?;
                // Only a *bare* field is positionally comparable with the
                // selecting site's arguments; a partial application at the
                // field shifts them.
                if m.strip(va[field]) != m.strip(occ) {
                    return None;
                }
                return Some(DispatchSlot {
                    dict: key.clone(),
                    class: spec.class,
                    field,
                    rest_index: index,
                });
            }
            _ => return None,
        }
    }
    None
}

/// Enumerate, over the whole closed world, what produces the `index`th
/// value argument of `owner`.
fn dict_producers(w: &World, mi: usize, owner: Option<BinderId>, index: usize) -> Producers {
    let mut out = Producers::default();
    let Some(f) = owner else {
        out.top = Some(R_ANON.into());
        return out;
    };
    let occs = w.all_occurrences(mi, f);
    if occs.is_empty() {
        out.top = Some(R_UNREACHABLE.into());
        return out;
    }
    for (omi, o) in occs {
        let om = w.m(omi);
        let root = om.spine_root(o);
        let (head, args) = om.spine(root);
        if root != o && om.strip(head) == om.strip(o) {
            match vargs(om, &args).get(index) {
                Some(&a) => out.calls.push((omi, a)),
                None => out.top = Some(R_PARTIAL.into()),
            }
            continue;
        }
        // Not a call. The one non-call use that still has an enumerable
        // caller set is a method field of a dictionary: its callers are
        // the class-op sites that select it.
        match method_slot(w, omi, o, index) {
            Some(slot) => out.slots.push(slot),
            None => {
                out.top = Some(R_VALUE_USE.into());
                return out;
            }
        }
    }
    out
}

fn collect_dict_params(w: &World) -> Vec<DParam> {
    let mut out = Vec::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Lam { binder, .. } = m.expr(id) else {
                continue;
            };
            let b = *binder;
            if !dict_binder(m, b) {
                continue;
            }
            let (owner, index) = owner_of(w, mi, b);
            out.push(DParam {
                mi,
                binder: b,
                module: m.name.clone(),
                owner_binder: owner,
                index,
                producers: dict_producers(w, mi, owner, index),
                set: Set::empty(),
                tot: TotFact::total(),
            });
        }
    }
    out
}

fn collect_dict_sites(w: &World) -> Vec<DSite> {
    let mut out = Vec::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for id in 0..m.exprs.len() as ExprId {
            let is_app = matches!(m.expr(id), Expr::App { .. });
            let is_var = matches!(m.expr(id), Expr::Var { .. });
            if (!is_app && !is_var) || m.spine_root(id) != id {
                continue;
            }
            let (head, args) = if is_app { m.spine(id) } else { (id, vec![]) };
            // **Trusted input 3**: GHC's own `isClassOpId`.
            if !head_sig(m, head).is_some_and(|s| s.is_class_op) {
                continue;
            }
            let Expr::Var { name, occ, .. } = m.expr(head) else {
                continue;
            };
            let sel_module = parts(name).map(|(_, md, _)| md).unwrap_or("");
            let sf = selector_field(sel_module, occ);
            let va = vargs(m, &args);
            out.push(DSite {
                mi,
                module: m.name.clone(),
                node: id,
                occ: occ.clone(),
                spec: sf.map(|(s, _)| s),
                field: sf.map(|(_, f)| f),
                dict: va.first().copied(),
                rest: va.iter().skip(1).copied().collect(),
                set: Set::empty(),
                target: Ok(None),
            });
        }
    }
    out
}

type DState = HashMap<(usize, BinderId), Set>;

/// What dictionaries the expression at `node` can be, under the current
/// state. A worklist over the expression graph; the only nesting is the
/// bounded one a dictionary **field** read needs.
fn dict_eval(w: &World, st: &DState, mi: usize, node: ExprId) -> Set {
    dict_eval_at(w, st, mi, node, 0)
}

fn dict_eval_at(w: &World, st: &DState, mi: usize, node: ExprId, nest: usize) -> Set {
    if nest > NEST {
        return Set::top(R_BUDGET_NEST);
    }
    let mut acc = Set::empty();
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work = vec![(mi, node)];
    let mut steps = 0usize;
    while let Some((mi, node)) = work.pop() {
        steps += 1;
        if steps > STEPS {
            return Set::top(R_BUDGET_STEPS);
        }
        if !seen.insert((mi, node)) {
            continue;
        }
        let m = w.m(mi);
        let inner = m.strip(node);
        let (head, args) = m.spine(inner);
        let va = vargs(m, &args);

        match m.expr(head) {
            Expr::Case { alts, .. } => {
                work.extend(alts.iter().map(|a| (mi, a.rhs)));
                continue;
            }
            Expr::Let { body, .. } => {
                work.push((mi, *body));
                continue;
            }
            Expr::Var { .. } => {}
            _ => {
                acc.join(&Set::top(R_NOT_A_DICT));
                continue;
            }
        }

        if let Some(key) = w.con_key[mi].get(&inner) {
            acc.join(&Set::one(key));
            continue;
        }

        if let Some(b) = m.resolve(head) {
            let bi = m.binding(b);
            match bi.site {
                BindSite::Lam => match st.get(&(mi, b)) {
                    Some(v) => acc.join(v),
                    None => acc.join(&Set::top(R_HIGHER_ORDER)),
                },
                BindSite::Let | BindSite::Top => match bi.rhs {
                    Some(rhs) if va.is_empty() => work.push((mi, w.strip_ty_lams(mi, rhs))),
                    Some(rhs) => work.push((mi, w.strip_lams(mi, rhs))),
                    None => acc.join(&Set::top(R_NOT_A_DICT)),
                },
                BindSite::CaseBinder => match w.case_scrut[mi].get(&b) {
                    Some(&scrut) => work.push((mi, scrut)),
                    None => acc.join(&Set::top(R_CON_FIELD)),
                },
                BindSite::AltBinder => match w.dict_alt_field[mi].get(&b) {
                    Some(&(scrut, spec, i)) => {
                        acc.join(&dict_field(w, st, mi, scrut, spec, i, nest));
                    }
                    None => acc.join(&Set::top(R_CON_FIELD)),
                },
            }
            continue;
        }

        let Expr::Var { name, occ, .. } = m.expr(head) else {
            unreachable!("the head is a Var here")
        };
        // A superclass selection out of another dictionary.
        if occ.starts_with("$p")
            && let Some(&d) = va.first()
        {
            let gm = parts(name).map(|(_, md, _)| md).unwrap_or("");
            match selector_field(gm, occ) {
                Some((spec, field)) => acc.join(&dict_field(w, st, mi, d, spec, field, nest)),
                None => acc.join(&Set::top(format!("{R_CLASS_UNKNOWN}({gm}.{occ})"))),
            }
            continue;
        }
        if let Some(&(wi, _, rhs)) = w.tops.get(name) {
            if va.is_empty() {
                work.push((wi, w.strip_ty_lams(wi, rhs)));
            } else {
                work.push((wi, w.strip_lams(wi, rhs)));
            }
            continue;
        }
        if w.values.contains_key(name) {
            acc.join(&Set::one(name));
            continue;
        }
        acc.join(&Set::top(R_UNKNOWN_CALL));
    }
    acc
}

/// Field `field` of whatever the expression at `node` evaluates to.
fn dict_field(
    w: &World,
    st: &DState,
    mi: usize,
    node: ExprId,
    spec: &'static ClassSpec,
    field: usize,
    nest: usize,
) -> Set {
    let base = dict_eval_at(w, st, mi, node, nest + 1);
    let keys = match &base {
        Set::Top(_) => return base,
        Set::Fin(k) => k.clone(),
    };
    let mut acc = Set::empty();
    for k in &keys {
        match field_expr(w, k, spec, field) {
            Ok((fmi, fnode)) => acc.join(&dict_eval_at(w, st, fmi, fnode, nest + 1)),
            Err(e) => acc.join(&Set::Top(e)),
        }
    }
    acc
}

/// The expression at field `field` of the dictionary `key`, in its module.
/// **The one place the class table is used to index a dictionary**, and the
/// entry is checked against that constructor's own `repArity` first.
fn field_expr(
    w: &World,
    key: &str,
    spec: &'static ClassSpec,
    field: usize,
) -> Result<(usize, ExprId), String> {
    let Some(v) = w.values.get(key) else {
        return Err(R_NOT_A_DICT.into());
    };
    if v.imported {
        let occ = parts(&v.key)
            .map(|(_, _, o)| o.to_string())
            .unwrap_or_else(|| v.key.clone());
        return Err(format!("{R_METHOD_NOT_HERE}({occ})"));
    }
    let m = w.m(v.mi);
    let (head, args) = m.spine(v.node);
    let Some(dc) = head_sig(m, head).and_then(|s| s.data_con) else {
        return Err(R_NOT_A_CON.into());
    };
    if dc.rep_arity as usize != spec.fields() {
        return Err(format!(
            "{R_TABLE_MISMATCH}({} has {} fields, the table says {})",
            spec.class,
            dc.rep_arity,
            spec.fields()
        ));
    }
    match vargs(m, &args).get(field) {
        Some(&f) => Ok((v.mi, f)),
        None => Err(R_NOT_A_CON.into()),
    }
}

/// The address of the binding a dictionary field holds, when the field
/// holds one thing: `Module#node name`.
fn target_at(w: &World, mi: usize, node: ExprId) -> Option<String> {
    let m = w.m(mi);
    let node = m.strip(node);
    match m.expr(node) {
        Expr::Var { name, .. } => Some(match m.resolve(node) {
            Some(b) => format!("{}#{} {}", m.name, node, m.binder(b).name),
            None => format!(
                "{}#{} {}",
                parts(name).map(|(_, md, _)| md).unwrap_or(""),
                node,
                name
            ),
        }),
        Expr::Lam { .. } | Expr::App { .. } => Some(format!("{}#{} ", m.name, node)),
        _ => None,
    }
}

/// The site's method target: the single binding every dictionary in the
/// set puts at the selected field, or the reason there is not one.
fn site_target(w: &World, s: &DSite) -> Result<Option<String>, String> {
    if s.dict.is_none() {
        return Err("partially-applied-selector".into());
    }
    let (Some(spec), Some(field)) = (s.spec, s.field) else {
        return Err(format!("{R_CLASS_UNKNOWN}({})", s.occ));
    };
    let keys = match &s.set {
        Set::Top(r) => return Err(r.clone()),
        Set::Fin(k) => k,
    };
    if keys.is_empty() {
        return Err(R_NO_PRODUCER.into());
    }
    let mut targets: Vec<String> = Vec::new();
    let mut bad: Vec<String> = Vec::new();
    for k in keys {
        match field_expr(w, k, spec, field) {
            Ok((fmi, fnode)) => match target_at(w, fmi, fnode) {
                Some(t) => {
                    if !targets.contains(&t) {
                        targets.push(t);
                    }
                }
                None => bad.push(R_NOT_A_DICT.into()),
            },
            Err(e) => bad.push(e),
        }
    }
    if !bad.is_empty() {
        bad.sort();
        bad.dedup();
        return Err(bad.join("; "));
    }
    match targets.len() {
        1 => Ok(Some(targets.pop().unwrap())),
        _ => Ok(None),
    }
}

type TState = HashMap<(usize, BinderId), TotFact>;

/// **This walk's own definition of *already evaluated*, and it is
/// deliberately narrower than M2.4c′'s.** A `case` deletes no evaluation
/// only if its scrutinee has already been evaluated where it stands: a
/// literal, a lambda, a saturated constructor application, a dfun, or a
/// variable a `case` has already bound (a case binder or an alternative
/// binder — it could not be named before the scrutinee was forced).
///
/// M2.4c′ additionally admits a variable GHC marks strict at its binder
/// that an enclosing `case` on that same binder dominates. That is a sound
/// clause, but it rests on a dominance walk this module would then be
/// re-running rather than checking, so it is left out: refusing it can only
/// make this walk find *more* forces than the analysis, which is the
/// conservative direction for a verifier. A disagreement caused by it would
/// therefore be this walk over-refusing, and is reported as one.
fn already_evaluated(w: &World, mi: usize, node: ExprId) -> bool {
    let m = w.m(mi);
    let inner = m.strip(node);
    let (head, args) = m.spine(inner);
    match m.expr(head) {
        Expr::Lit(_) | Expr::Lam { .. } => return true,
        Expr::Var { .. } => {}
        _ => return false,
    }
    if let Some(dc) = head_sig(m, head).and_then(|s| s.data_con) {
        return vargs(m, &args).len() >= dc.rep_arity as usize;
    }
    let Some(b) = m.resolve(head) else {
        return args.is_empty()
            && matches!(m.expr(head), Expr::Var { name, .. } if w.values.contains_key(name));
    };
    if !args.is_empty() {
        return false;
    }
    matches!(
        m.binding(b).site,
        BindSite::CaseBinder | BindSite::AltBinder
    )
}

/// The totality of a dictionary expression. Structurally the same walk as
/// [`dict_eval_at`] with a different transfer: where that one takes the
/// union over a `case`'s alternatives and forgets the scrutinee, this one
/// **keeps the scrutinee**, because reaching any alternative at all means
/// the scrutinee was evaluated.
#[allow(clippy::too_many_arguments)]
fn tot_eval(
    w: &World,
    st: &DState,
    ts: &TState,
    mi: usize,
    node: ExprId,
    nest: usize,
    cases: &std::cell::Cell<usize>,
) -> TotFact {
    if nest > NEST {
        return TotFact::unknown();
    }
    let mut acc = TotFact::total();
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work = vec![(mi, node)];
    let mut steps = 0usize;
    while let Some((mi, node)) = work.pop() {
        steps += 1;
        if steps > STEPS {
            return TotFact::unknown();
        }
        if !seen.insert((mi, node)) {
            continue;
        }
        let m = w.m(mi);
        let inner = m.strip(node);
        let (head, args) = m.spine(inner);
        let va = vargs(m, &args);

        match m.expr(head) {
            Expr::Case { scrut, alts, .. } => {
                cases.set(cases.get() + 1);
                if !already_evaluated(w, mi, *scrut) {
                    acc.join(&TotFact::force(&m.name, head, *scrut));
                }
                work.extend(alts.iter().map(|a| (mi, a.rhs)));
                continue;
            }
            Expr::Let { body, .. } => {
                work.push((mi, *body));
                continue;
            }
            Expr::Var { .. } => {}
            _ => {
                acc.join(&TotFact::unknown());
                continue;
            }
        }

        // A saturated dictionary-constructor application is a value.
        if w.con_key[mi].contains_key(&inner) {
            continue;
        }

        if let Some(b) = m.resolve(head) {
            let bi = m.binding(b);
            match bi.site {
                BindSite::Lam => match ts.get(&(mi, b)) {
                    Some(v) => acc.join(v),
                    None => acc.join(&TotFact::unknown()),
                },
                BindSite::Let | BindSite::Top => match bi.rhs {
                    Some(rhs) if va.is_empty() => work.push((mi, w.strip_ty_lams(mi, rhs))),
                    Some(rhs) => work.push((mi, w.strip_lams(mi, rhs))),
                    None => acc.join(&TotFact::unknown()),
                },
                BindSite::CaseBinder => match w.case_scrut[mi].get(&b) {
                    // Naming the case binder means the scrutinee was
                    // forced: the same force, at the same place.
                    Some(&scrut) => {
                        cases.set(cases.get() + 1);
                        if !already_evaluated(w, mi, scrut) {
                            acc.join(&TotFact::force(&m.name, head, scrut));
                        }
                        work.push((mi, scrut));
                    }
                    None => acc.join(&TotFact::unknown()),
                },
                BindSite::AltBinder => match w.dict_alt_field[mi].get(&b) {
                    Some(&(scrut, spec, i)) => {
                        acc.join(&tot_field(w, st, ts, mi, scrut, spec, i, nest, cases));
                    }
                    None => acc.join(&TotFact::unknown()),
                },
            }
            continue;
        }

        let Expr::Var { name, occ, .. } = m.expr(head) else {
            unreachable!("the head is a Var here")
        };
        if occ.starts_with("$p")
            && let Some(&d) = va.first()
        {
            let gm = parts(name).map(|(_, md, _)| md).unwrap_or("");
            match selector_field(gm, occ) {
                Some((spec, field)) => {
                    acc.join(&tot_field(w, st, ts, mi, d, spec, field, nest, cases))
                }
                None => acc.join(&TotFact::unknown()),
            }
            continue;
        }
        if let Some(&(wi, _, rhs)) = w.tops.get(name) {
            if va.is_empty() {
                work.push((wi, w.strip_ty_lams(wi, rhs)));
            } else {
                work.push((wi, w.strip_lams(wi, rhs)));
            }
            continue;
        }
        if w.values.contains_key(name) {
            // A dfun, applied or not, is a value.
            continue;
        }
        acc.join(&TotFact::unknown());
    }
    acc
}

/// Superclass selection is total exactly when the dictionary it selects out
/// of is total and every field expression it can reach is.
#[allow(clippy::too_many_arguments)]
fn tot_field(
    w: &World,
    st: &DState,
    ts: &TState,
    mi: usize,
    node: ExprId,
    spec: &'static ClassSpec,
    field: usize,
    nest: usize,
    cases: &std::cell::Cell<usize>,
) -> TotFact {
    let mut acc = tot_eval(w, st, ts, mi, node, nest + 1, cases);
    if acc.level == Tot::Unknown {
        return acc;
    }
    let keys = match dict_eval_at(w, st, mi, node, nest + 1) {
        Set::Top(_) => return TotFact::unknown(),
        Set::Fin(k) => k,
    };
    for k in &keys {
        match field_expr(w, k, spec, field) {
            Ok((fmi, fnode)) => acc.join(&tot_eval(w, st, ts, fmi, fnode, nest + 1, cases)),
            Err(_) => acc.join(&TotFact::unknown()),
        }
    }
    acc
}

/// This walk's erasure verdict for one dictionary value or parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
enum EVerdict {
    Erasable,
    WithObligation,
    WithClone(usize),
    Preserve(String),
    Unresolved(String),
}

impl EVerdict {
    fn label(&self) -> &'static str {
        match self {
            EVerdict::Erasable => "Erasable",
            EVerdict::WithObligation => "ErasableWithObligation",
            EVerdict::WithClone(_) => "ErasableWithClone",
            EVerdict::Preserve(_) => "Preserve",
            EVerdict::Unresolved(_) => "Unresolved",
        }
    }
}

/// One owner-level clone plan, re-derived.
#[derive(Debug, Clone)]
struct OwnerPlan {
    /// How many dictionary or function-valued parameters the owner has.
    params: usize,
    tuples: usize,
    set_valued: usize,
    refused: Option<String>,
}

/// Part 1 and Part 2, as this walk derives them.
pub struct DictDerived {
    params: Vec<DParam>,
    sites: Vec<DSite>,
    /// Per-parameter erasure verdict, in `params` order.
    param_verdict: Vec<EVerdict>,
    /// Per-value erasure verdict, keyed by dictionary identity.
    value_verdict: BTreeMap<String, EVerdict>,
    /// Per-owning-function dictionary clone plan.
    owner_plans: BTreeMap<(usize, BinderId), OwnerPlan>,
    param_at: HashMap<(usize, BinderId), usize>,
    site_at: HashMap<(usize, ExprId), usize>,
    pub rounds: usize,
    pub tot_rounds: usize,
    /// `case` nodes the totality walk reached on a dictionary path.
    pub tot_cases: usize,
}

type Dispatch<'a> = HashMap<(&'a str, usize), Vec<(usize, &'a Vec<ExprId>)>>;

/// The dispatch index for one round: which site arguments reach which field
/// of which dictionary, and which `(class, field)` no bounded set covers.
fn dispatch_of<'a>(
    sites: &'a [DSite],
    sets: &'a [Set],
) -> (Dispatch<'a>, HashSet<(&'static str, usize)>) {
    let mut dispatch: Dispatch = HashMap::new();
    let mut tainted: HashSet<(&'static str, usize)> = HashSet::new();
    for (s, set) in sites.iter().zip(sets) {
        let (Some(spec), Some(field)) = (s.spec, s.field) else {
            continue;
        };
        match set {
            Set::Top(_) => {
                tainted.insert((spec.class, field));
            }
            Set::Fin(keys) => {
                for k in keys {
                    dispatch
                        .entry((k.as_str(), field))
                        .or_default()
                        .push((s.mi, &s.rest));
                }
            }
        }
    }
    (dispatch, tainted)
}

impl DictDerived {
    pub fn of_world(w: &World) -> DictDerived {
        let mut params = collect_dict_params(w);
        let mut sites = collect_dict_sites(w);
        let mut state: DState = params
            .iter()
            .map(|x| ((x.mi, x.binder), Set::empty()))
            .collect();

        // ---- Fixpoint one: the dictionary sets.
        let mut rounds = 0usize;
        loop {
            rounds += 1;
            let sets: Vec<Set> = sites
                .iter()
                .map(|s| match s.dict {
                    Some(d) => dict_eval(w, &state, s.mi, d),
                    None => Set::top(R_NOT_A_DICT),
                })
                .collect();
            let (dispatch, tainted) = dispatch_of(&sites, &sets);
            let mut changed = false;
            let mut next = state.clone();
            for x in &params {
                let mut acc = Set::empty();
                if let Some(r) = &x.producers.top {
                    acc.join(&Set::Top(r.clone()));
                }
                for &(cmi, arg) in &x.producers.calls {
                    acc.join(&dict_eval(w, &state, cmi, arg));
                }
                for slot in &x.producers.slots {
                    if tainted.contains(&(slot.class, slot.field)) {
                        acc.join(&Set::top(R_DISPATCH_TAINTED));
                        continue;
                    }
                    let Some(callers) = dispatch.get(&(slot.dict.as_str(), slot.field)) else {
                        continue;
                    };
                    for (cmi, rest) in callers {
                        match rest.get(slot.rest_index) {
                            Some(&a) => acc.join(&dict_eval(w, &state, *cmi, a)),
                            None => acc.join(&Set::top(R_PARTIAL)),
                        }
                    }
                }
                let slot = next.get_mut(&(x.mi, x.binder)).unwrap();
                if *slot != acc {
                    *slot = acc;
                    changed = true;
                }
            }
            state = next;
            if !changed {
                break;
            }
            if rounds >= ROUNDS {
                for v in state.values_mut() {
                    if !v.is_top() {
                        v.join(&Set::top(R_BUDGET_ROUNDS));
                    }
                }
                break;
            }
        }
        for x in &mut params {
            x.set = state[&(x.mi, x.binder)].clone();
            if let Set::Fin(s) = &x.set
                && s.is_empty()
            {
                // A parameter no producer reaches is not bounded: under
                // the closed world nothing names it, or nothing ever
                // dispatches the method it sits behind.
                x.set = Set::top(if x.producers.slots.is_empty() {
                    R_NO_PRODUCER
                } else {
                    R_NEVER_DISPATCHED
                });
            }
        }
        let state: DState = params
            .iter()
            .map(|x| ((x.mi, x.binder), x.set.clone()))
            .collect();
        for s in &mut sites {
            s.set = match s.dict {
                Some(d) => dict_eval(w, &state, s.mi, d),
                None => Set::top(R_NOT_A_DICT),
            };
            s.target = site_target(w, s);
        }

        // ---- Fixpoint two: totality. It shares the settled dictionary
        // sets only to resolve dispatch; its lattice and its transfer are
        // its own.
        let settled: Vec<Set> = sites.iter().map(|s| s.set.clone()).collect();
        let (dispatch, tainted) = dispatch_of(&sites, &settled);
        let mut ts: TState = params
            .iter()
            .map(|x| ((x.mi, x.binder), TotFact::total()))
            .collect();
        // **M2.4c′'s instrumented claim, re-derived.** How many `case`
        // nodes the totality walk reaches on a dictionary path at all. The
        // milestone asserts the answer is zero on this dump — GHC floats
        // every dictionary out of every scrutinee — and that is a stronger
        // statement than `MustPreserveForce == 0`, which a wide enough
        // definition of *already evaluated* could also produce.
        let cases = std::cell::Cell::new(0usize);
        let mut tot_rounds = 0usize;
        loop {
            tot_rounds += 1;
            let mut changed = false;
            let mut next = ts.clone();
            for x in &params {
                let mut acc = TotFact::total();
                if x.producers.top.is_some() {
                    acc.join(&TotFact::unknown());
                }
                for &(cmi, arg) in &x.producers.calls {
                    acc.join(&tot_eval(w, &state, &ts, cmi, arg, 0, &cases));
                }
                for slot in &x.producers.slots {
                    if tainted.contains(&(slot.class, slot.field)) {
                        acc.join(&TotFact::unknown());
                        continue;
                    }
                    let Some(callers) = dispatch.get(&(slot.dict.as_str(), slot.field)) else {
                        continue;
                    };
                    for (cmi, rest) in callers {
                        match rest.get(slot.rest_index) {
                            Some(&a) => acc.join(&tot_eval(w, &state, &ts, *cmi, a, 0, &cases)),
                            None => acc.join(&TotFact::unknown()),
                        }
                    }
                }
                let slot = next.get_mut(&(x.mi, x.binder)).unwrap();
                if *slot != acc {
                    *slot = acc;
                    changed = true;
                }
            }
            ts = next;
            if !changed {
                break;
            }
            if tot_rounds >= ROUNDS {
                for v in ts.values_mut() {
                    v.join(&TotFact::unknown());
                }
                break;
            }
        }
        for x in &mut params {
            x.tot = ts[&(x.mi, x.binder)].clone();
        }
        let tot_cases = cases.get();

        // ---- Part 2: erasure, from facts recorded separately.
        let dict_args: HashSet<(usize, ExprId)> = sites
            .iter()
            .filter_map(|s| s.dict.map(|d| (s.mi, w.m(s.mi).strip(d))))
            .collect();

        let mut value_verdict: BTreeMap<String, EVerdict> = BTreeMap::new();
        for v in w.values.values() {
            let verdict = match value_escape(w, v, &dict_args) {
                Some(h) => EVerdict::Preserve(h),
                None if v.imported => EVerdict::Erasable,
                None => {
                    // The instance is determined only if the dfun's own
                    // dictionary parameters are.
                    let unknown = v.params.iter().any(|b| {
                        params
                            .iter()
                            .any(|x| x.mi == v.mi && x.binder == *b && x.set.is_top())
                    });
                    if unknown {
                        EVerdict::Unresolved("argument-dictionary-unresolved".into())
                    } else {
                        EVerdict::Erasable
                    }
                }
            };
            value_verdict.insert(v.key.clone(), verdict);
        }

        let mut param_verdict = Vec::with_capacity(params.len());
        for x in &params {
            let escapes = param_escape(w, x, &dict_args);
            let instances = x.set.keys().len();
            let verdict = match escapes {
                Some(h) => EVerdict::Preserve(h),
                None => match &x.set {
                    Set::Top(r) => EVerdict::Unresolved(r.clone()),
                    Set::Fin(_) if instances == 0 => EVerdict::Unresolved(R_NO_PRODUCER.into()),
                    Set::Fin(_) => match x.tot.level {
                        Tot::Total if instances == 1 => EVerdict::Erasable,
                        Tot::Total => EVerdict::WithClone(instances),
                        Tot::Force if x.tot.witness.is_some() => EVerdict::WithObligation,
                        Tot::Force => EVerdict::Preserve("erasure-would-delete-a-force".into()),
                        Tot::Unknown => EVerdict::Preserve("totality-unknown".into()),
                    },
                },
            };
            param_verdict.push(verdict);
        }

        let owner_plans = dict_owner_plans(w, &state, &params, &param_verdict);

        let param_at = params
            .iter()
            .enumerate()
            .map(|(i, x)| ((x.mi, x.binder), i))
            .collect();
        let site_at = sites
            .iter()
            .enumerate()
            .map(|(i, s)| ((s.mi, s.node), i))
            .collect();

        DictDerived {
            params,
            sites,
            param_verdict,
            value_verdict,
            owner_plans,
            param_at,
            site_at,
            rounds,
            tot_rounds,
            tot_cases,
        }
    }
}

//------------------------------------------------------------------------------
// Escape — the `K11` question, re-derived
//------------------------------------------------------------------------------

/// How one occurrence of a dictionary is used.
enum DictUse {
    /// Dispatch, a dictionary argument of a callee's dictionary parameter,
    /// a field of a dictionary constructor, or a `case` that takes the
    /// dictionary apart: none of these needs it to survive as a value.
    Dictionary,
    /// Used as an ordinary value; the holder that keeps it alive.
    Escape(String),
}

fn value_escape(w: &World, v: &DictValue, dict_args: &HashSet<(usize, ExprId)>) -> Option<String> {
    let mut occs: Vec<(usize, ExprId)> = Vec::new();
    if v.imported
        && let Some(g) = w.gvars.get(&v.key)
    {
        occs.extend(g.iter().copied());
    }
    if let Some(b) = v.binder {
        occs.extend(w.all_occurrences(v.mi, b));
    }
    if occs.is_empty() && !v.imported {
        // A dictionary built inline: its one use is where it stands.
        occs.push((v.mi, v.node));
    }
    escape_from(w, &occs, dict_args)
}

fn param_escape(w: &World, x: &DParam, dict_args: &HashSet<(usize, ExprId)>) -> Option<String> {
    let occs: Vec<(usize, ExprId)> = w
        .m(x.mi)
        .occurrences(x.binder)
        .iter()
        .map(|&o| (x.mi, o))
        .collect();
    escape_from(w, &occs, dict_args)
}

/// The first of these occurrences that is an ordinary-value use.
fn escape_from(
    w: &World,
    occs: &[(usize, ExprId)],
    dict_args: &HashSet<(usize, ExprId)>,
) -> Option<String> {
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work: Vec<(usize, ExprId)> = occs.to_vec();
    let mut steps = 0usize;
    while let Some((mi, o)) = work.pop() {
        steps += 1;
        if steps > STEPS {
            return Some(R_BUDGET_STEPS.into());
        }
        if !seen.insert((mi, o)) {
            continue;
        }
        match dict_use(w, mi, o, dict_args, &mut work) {
            DictUse::Dictionary => {}
            DictUse::Escape(h) => return Some(h),
        }
    }
    None
}

fn dict_use(
    w: &World,
    mi: usize,
    occ: ExprId,
    dict_args: &HashSet<(usize, ExprId)>,
    work: &mut Vec<(usize, ExprId)>,
) -> DictUse {
    let m = w.m(mi);
    if dict_args.contains(&(mi, m.strip(occ))) {
        return DictUse::Dictionary;
    }
    let mut cur = occ;
    while let Some(parent) = m.parent[cur as usize] {
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => cur = parent,
            // A `case` on a dictionary takes it apart; it does not need it
            // to survive as a value.
            Edge::CaseScrut => return DictUse::Dictionary,
            Edge::AppArg => {
                let root = m.spine_root(parent);
                let (head, args) = m.spine(root);
                let va = vargs(m, &args);
                let pos = va.iter().position(|&a| m.strip(a) == m.strip(cur));
                if head_sig(m, head).is_some_and(|s| s.is_class_op) {
                    return if pos == Some(0) {
                        DictUse::Dictionary
                    } else {
                        DictUse::Escape(format!("a method argument ({} node {root})", m.name))
                    };
                }
                if let Expr::Var { name, .. } = m.expr(head)
                    && dict_con_spec(name).is_some()
                {
                    return DictUse::Dictionary;
                }
                let callee = match m.resolve(head) {
                    Some(b) => Some((mi, b)),
                    None => match m.expr(head) {
                        Expr::Var { name, .. } => w.tops.get(name).map(|&(wi, b, _)| (wi, b)),
                        _ => None,
                    },
                };
                let Some((cmi, cb)) = callee else {
                    return DictUse::Escape(format!(
                        "passed to a callee outside the dump ({} node {root})",
                        m.name
                    ));
                };
                let cm = w.m(cmi);
                if cm.binding(cb).site == BindSite::Lam {
                    return DictUse::Escape(format!(
                        "passed to a higher-order parameter ({} node {root})",
                        m.name
                    ));
                }
                let Some(rhs) = cm.binding(cb).rhs else {
                    return DictUse::Escape(format!(
                        "passed to a callee with no body ({} node {root})",
                        m.name
                    ));
                };
                let ps = w.lam_params(cmi, rhs);
                return match pos.and_then(|i| ps.get(i)) {
                    Some(&pb) if dict_binder(cm, pb) => DictUse::Dictionary,
                    _ => DictUse::Escape(format!(
                        "passed to a non-dictionary parameter ({} node {root})",
                        m.name
                    )),
                };
            }
            Edge::LetRhs { pair } => {
                let Expr::Let { bind, .. } = m.expr(parent) else {
                    return DictUse::Escape(format!("an unreadable binding ({})", m.name));
                };
                let b = bind.pairs[pair as usize].binder;
                for &o in m.occurrences(b) {
                    work.push((mi, o));
                }
                return DictUse::Dictionary;
            }
            Edge::Top { .. } => {
                let Some(&b) = w.top_of_rhs[mi].get(&cur) else {
                    return DictUse::Escape(format!("a top-level right-hand side ({})", m.name));
                };
                for o in w.all_occurrences(mi, b) {
                    work.push(o);
                }
                return DictUse::Dictionary;
            }
            _ => {
                return DictUse::Escape(format!(
                    "used as an ordinary value ({} node {parent})",
                    m.name
                ));
            }
        }
    }
    match w.top_of_rhs[mi].get(&cur) {
        Some(&b) => {
            for o in w.all_occurrences(mi, b) {
                work.push(o);
            }
            DictUse::Dictionary
        }
        None => DictUse::Escape(format!("a bare right-hand side ({})", m.name)),
    }
}

//------------------------------------------------------------------------------
// Owner-level dictionary clone planning, re-enumerated
//------------------------------------------------------------------------------

/// A function's clones are its **distinct call-site assignment tuples** —
/// one tuple per call site, deduplicated — and neither the sum nor the
/// product of the per-parameter cardinalities. A call site that cannot be
/// enumerated refuses the owner's plan rather than guessing a number.
fn dict_owner_plans(
    w: &World,
    st: &DState,
    params: &[DParam],
    verdicts: &[EVerdict],
) -> BTreeMap<(usize, BinderId), OwnerPlan> {
    let mut groups: BTreeMap<(usize, BinderId), Vec<usize>> = BTreeMap::new();
    let mut wanted: BTreeSet<(usize, BinderId)> = BTreeSet::new();
    for (i, x) in params.iter().enumerate() {
        let Some(f) = x.owner_binder else { continue };
        groups.entry((x.mi, f)).or_default().push(i);
        if matches!(verdicts[i], EVerdict::WithClone(_)) {
            wanted.insert((x.mi, f));
        }
    }
    let mut out = BTreeMap::new();
    for key in &wanted {
        let (mi, f) = *key;
        let arg_indices: Vec<usize> = groups[key].iter().map(|&i| params[i].index).collect();
        let mut tuples: BTreeSet<Vec<String>> = BTreeSet::new();
        let mut set_valued: BTreeSet<Vec<String>> = BTreeSet::new();
        let mut refused: Option<String> = None;
        for (omi, o) in w.all_occurrences(mi, f) {
            let om = w.m(omi);
            let root = om.spine_root(o);
            let (head, args) = om.spine(root);
            if root == o || om.strip(head) != om.strip(o) {
                refused = Some(R_VALUE_USE.into());
                break;
            }
            let va = vargs(om, &args);
            let mut tuple = Vec::with_capacity(arg_indices.len());
            let mut many = 0usize;
            for &ai in &arg_indices {
                match va.get(ai) {
                    Some(&a) => match dict_eval(w, st, omi, a) {
                        Set::Fin(k) if !k.is_empty() => {
                            if k.len() > 1 {
                                many += 1;
                            }
                            tuple.push(k.into_iter().collect::<Vec<_>>().join("|"));
                        }
                        other => {
                            refused = Some(other.reason().unwrap_or(R_NO_PRODUCER).to_string());
                            break;
                        }
                    },
                    None => {
                        refused = Some(R_PARTIAL.into());
                        break;
                    }
                }
            }
            if refused.is_some() {
                break;
            }
            if many > 0 {
                set_valued.insert(tuple.clone());
            }
            tuples.insert(tuple);
        }
        out.insert(
            *key,
            OwnerPlan {
                params: arg_indices.len(),
                tuples: tuples.len(),
                set_valued: set_valued.len(),
                refused,
            },
        );
    }
    out
}

//------------------------------------------------------------------------------
// Part 3 — higher-order representation agreement, re-derived
//------------------------------------------------------------------------------

/// Is this a function type — a `FunTy`, or a `ForAllTy` over one?
fn fun_ty(t: &Ty) -> bool {
    let mut cur = t;
    loop {
        match cur {
            Ty::ForAll { body, .. } => cur = body,
            Ty::Fun { .. } => return true,
            _ => return false,
        }
    }
}

/// The result type after `n` value arrows, looking through `forall`s.
/// `None` when the type has fewer than `n` arrows: the binder's type and
/// its manifest lambda chain disagree, which is not a thing to guess about.
fn result_after(t: &Ty, n: usize) -> Option<&Ty> {
    let mut cur = t;
    let mut left = n;
    loop {
        match cur {
            Ty::ForAll { body, .. } => cur = body,
            Ty::Fun { res, .. } if left > 0 => {
                left -= 1;
                cur = res;
            }
            _ => return if left == 0 { Some(cur) } else { None },
        }
    }
}

/// A canonical key for a structured type. `forall`-bound variables are
/// written as their binding depth, so two alpha-variants agree; a *free*
/// variable is written with its GHC unique, which is **not** an identity —
/// see [`type_key_free`], which is what decides whether a key may be
/// shared. Iterative: a signature can be long.
fn type_key(t: &Ty) -> String {
    enum Step<'a> {
        T(&'a Ty, usize),
        S(&'static str),
        Pop,
    }
    let mut out = String::new();
    let mut bound: Vec<&str> = Vec::new();
    let mut work = vec![Step::T(t, 0)];
    while let Some(step) = work.pop() {
        match step {
            Step::S(s) => out.push_str(s),
            Step::Pop => {
                bound.pop();
            }
            Step::T(t, depth) => {
                bound.truncate(depth);
                match t {
                    Ty::Var(v) => match bound.iter().rposition(|b| *b == v.unique) {
                        Some(i) => out.push_str(&format!("#{}", bound.len() - 1 - i)),
                        None => out.push_str(&format!("~{}", v.unique)),
                    },
                    Ty::Con { tycon, args } => {
                        out.push_str(&format!("T{{{}", tycon.name));
                        work.push(Step::S("}"));
                        for a in args.iter().rev() {
                            work.push(Step::T(a, depth));
                            work.push(Step::S(" "));
                        }
                    }
                    Ty::App { fun, arg } => {
                        out.push_str("@{");
                        work.push(Step::S("}"));
                        work.push(Step::T(arg, depth));
                        work.push(Step::S(" "));
                        work.push(Step::T(fun, depth));
                    }
                    Ty::Fun { mult, arg, res } => {
                        out.push_str(">{");
                        work.push(Step::S("}"));
                        work.push(Step::T(res, depth));
                        work.push(Step::S(" "));
                        work.push(Step::T(arg, depth));
                        work.push(Step::S(" "));
                        work.push(Step::T(mult, depth));
                    }
                    Ty::ForAll { binder, body } => {
                        out.push_str("!{");
                        bound.push(binder.unique.as_str());
                        work.push(Step::Pop);
                        work.push(Step::S("}"));
                        work.push(Step::T(body, depth + 1));
                    }
                    Ty::Lit { kind, text } => out.push_str(&format!("K{{{kind}:{text}}}")),
                    Ty::Opaque { pretty } => out.push_str(&format!("Q{{{pretty}}}")),
                }
            }
        }
    }
    out
}

/// Does this type mention a type variable nothing inside it binds? Such a
/// variable is bound somewhere in the enclosing *term*, and a GHC unique is
/// neither module- nor scope-qualified, so its key identifies nothing.
fn type_key_free(t: &Ty) -> bool {
    let mut bound: Vec<&str> = Vec::new();
    let mut work: Vec<(&Ty, usize)> = vec![(t, 0)];
    while let Some((t, depth)) = work.pop() {
        bound.truncate(depth);
        match t {
            Ty::Var(v) => {
                if !bound.iter().any(|b| *b == v.unique) {
                    return true;
                }
            }
            Ty::Con { args, .. } => work.extend(args.iter().map(|a| (a, depth))),
            Ty::App { fun, arg } => {
                work.push((fun, depth));
                work.push((arg, depth));
            }
            Ty::Fun { mult, arg, res } => {
                work.push((mult, depth));
                work.push((arg, depth));
                work.push((res, depth));
            }
            Ty::ForAll { binder, body } => {
                bound.truncate(depth);
                bound.push(binder.unique.as_str());
                work.push((body, depth + 1));
            }
            Ty::Lit { .. } | Ty::Opaque { .. } => {}
        }
    }
    false
}

/// The key a captured type contributes to a shape class. A closed type is
/// its [`type_key`], which two producers may share; a type carrying a free
/// type variable gets a key **private to its producer** and merges with
/// nothing, not even with a textually equal key in another closure.
fn capture_key(t: &Ty, producer: &str) -> String {
    let k = type_key(t);
    if type_key_free(t) {
        format!("<{producer}>{k}")
    } else {
        k
    }
}

/// What kind of thing a closure producer is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PKind {
    Lambda,
    Partial,
    KnownFunction,
    ImportedFunction,
    FieldRead,
    ImportedCall,
}

/// The representation a producer needs.
#[derive(Debug, Clone, PartialEq, Eq)]
enum PShape {
    Known {
        arity: usize,
        captures: Vec<String>,
    },
    /// The environment is not visible: equal to nothing, **not even to
    /// another opaque shape**, so it is identified by its own producer.
    Opaque {
        why: &'static str,
        producer: String,
    },
}

impl PShape {
    fn class(&self) -> String {
        match self {
            PShape::Known { arity, captures } => format!("{arity}/[{}]", captures.join("|")),
            PShape::Opaque { producer, .. } => format!("opaque:{producer}"),
        }
    }
    fn is_opaque(&self) -> bool {
        matches!(self, PShape::Opaque { .. })
    }
    fn short(&self) -> String {
        match self {
            PShape::Known { arity, captures } => format!("{arity}/{}", captures.len()),
            PShape::Opaque { .. } => "opaque".into(),
        }
    }
}

#[derive(Debug, Clone)]
struct HProducer {
    key: String,
    module: String,
    node: ExprId,
    shape: PShape,
}

/// One function-valued slot.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum HSlot {
    Param { mi: usize, binder: BinderId },
    Field { con: String, index: usize },
    Return { mi: usize, binder: BinderId },
}

/// This walk's higher-order verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
enum HVerdict {
    Exact,
    Uniform,
    Clone(usize),
    Finite(usize),
    Preserve(String),
    Unresolved(String),
}

impl HVerdict {
    fn label(&self) -> &'static str {
        match self {
            HVerdict::Exact => "ExactClosure",
            HVerdict::Uniform => "TypeShapeUniform",
            HVerdict::Clone(_) => "CloneRequired",
            HVerdict::Finite(_) => "FiniteClosureSet",
            HVerdict::Preserve(_) => "Preserve",
            HVerdict::Unresolved(_) => "Unresolved",
        }
    }
}

#[derive(Debug, Clone, Default)]
struct HSources {
    top: Option<String>,
    exprs: Vec<(usize, ExprId)>,
}

/// A boundary before the fixpoint has run.
struct HRaw {
    slot: HSlot,
    mi: usize,
    owner_binder: Option<BinderId>,
    index: usize,
    module: String,
    exported: bool,
    valued: bool,
    sources: HSources,
}

/// A boundary after it.
struct HBoundary {
    slot: HSlot,
    module: String,
    exported: bool,
    valued: bool,
    set: Set,
    producers: Vec<HProducer>,
    enumerated: bool,
    classes: usize,
    verdict: HVerdict,
}

/// The closures found while evaluating, gathered as the fixpoint runs.
struct HCtx<'a, 'm> {
    w: &'a World<'m>,
    found: std::cell::RefCell<BTreeMap<String, (usize, ExprId, PKind)>>,
}

impl HCtx<'_, '_> {
    fn note(&self, key: &str, mi: usize, node: ExprId, kind: PKind) {
        self.found
            .borrow_mut()
            .entry(key.to_string())
            .or_insert((mi, node, kind));
    }
}

/// Is any occurrence of this function something other than the head of a
/// saturated call? Then no slot of it can be rewritten without seeing that
/// use too.
fn used_as_value(w: &World, mi: usize, f: BinderId) -> bool {
    let m = w.m(mi);
    let Some(rhs) = m.binding(f).rhs else {
        return true;
    };
    let need = w.lam_params(mi, rhs).len();
    if need == 0 {
        return true;
    }
    for (omi, o) in w.all_occurrences(mi, f) {
        let om = w.m(omi);
        let root = om.spine_root(o);
        if root == o {
            return true;
        }
        let (head, args) = om.spine(root);
        if om.strip(head) != om.strip(o) || vargs(om, &args).len() < need {
            return true;
        }
    }
    false
}

/// Every syntactic return point of a right-hand side, with the number of
/// value arguments that had to be supplied to reach it.
fn return_points(m: &Module, rhs: ExprId) -> Vec<(ExprId, usize)> {
    let mut leaves = Vec::new();
    let mut work = vec![(rhs, 0usize)];
    let mut seen: HashSet<(ExprId, usize)> = HashSet::new();
    while let Some((raw, depth)) = work.pop() {
        let id = m.strip(raw);
        if !seen.insert((id, depth)) {
            continue;
        }
        match m.expr(id) {
            Expr::Lam { binder, body } => {
                let value = usize::from(m.binder(*binder).kind != BinderKind::Tyvar);
                work.push((*body, depth + value));
            }
            Expr::Case { alts, .. } => work.extend(alts.iter().map(|a| (a.rhs, depth))),
            Expr::Let { body, .. } => work.push((*body, depth)),
            _ => leaves.push((id, depth)),
        }
    }
    leaves
}

/// What produces the `index`th value argument of `owner`, over the whole
/// closed world.
fn closure_param_sources(w: &World, mi: usize, owner: Option<BinderId>, index: usize) -> HSources {
    let mut out = HSources::default();
    let Some(f) = owner else {
        out.top = Some(R_ANON.into());
        return out;
    };
    let m = w.m(mi);
    let need = m
        .binding(f)
        .rhs
        .map(|rhs| w.lam_params(mi, rhs).len())
        .unwrap_or(0);
    let occs = w.all_occurrences(mi, f);
    if occs.is_empty() {
        out.top = Some(R_UNREACHABLE.into());
        return out;
    }
    for (omi, o) in occs {
        let om = w.m(omi);
        let root = om.spine_root(o);
        if root == o {
            out.top = Some(R_VALUE_USE.into());
            return out;
        }
        let (head, args) = om.spine(root);
        if om.strip(head) != om.strip(o) {
            out.top = Some(R_VALUE_USE.into());
            return out;
        }
        let va = vargs(om, &args);
        if va.len() < need {
            out.top = Some(R_PARTIAL.into());
            return out;
        }
        match va.get(index) {
            Some(&a) => out.exprs.push((omi, a)),
            None => out.top = Some(R_PARTIAL.into()),
        }
    }
    out
}

fn collect_closure_params(w: &World) -> Vec<HRaw> {
    let mut out = Vec::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Lam { binder, .. } = m.expr(id) else {
                continue;
            };
            let b = *binder;
            if m.binder(b).kind == BinderKind::Tyvar || !fun_ty(m.binder_ty(b)) {
                continue;
            }
            let (owner, index) = owner_of(w, mi, b);
            let (exported, valued) = match owner {
                Some(f) => (
                    m.binding(f).site == BindSite::Top && m.binder(f).exported == Some(true),
                    used_as_value(w, mi, f),
                ),
                None => (false, true),
            };
            out.push(HRaw {
                slot: HSlot::Param { mi, binder: b },
                mi,
                owner_binder: owner,
                index,
                module: m.name.clone(),
                exported,
                valued,
                sources: closure_param_sources(w, mi, owner, index),
            });
        }
    }
    out
}

fn collect_closure_fields(w: &World) -> Vec<HRaw> {
    let mut fields: BTreeMap<(String, usize), Vec<(usize, BinderId)>> = BTreeMap::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for (b, (con, i)) in &w.any_alt_field[mi] {
            if fun_ty(m.binder_ty(*b)) {
                fields.entry((con.clone(), *i)).or_default().push((mi, *b));
            }
        }
    }
    let mut out = Vec::new();
    for ((con, index), mut binders) in fields {
        binders.sort();
        let mut sources = HSources::default();
        match w.con_apps.get(&con) {
            None => sources.top = Some(R_NO_CON_APPS.into()),
            Some(apps) => {
                for &(ami, root) in apps {
                    let am = w.m(ami);
                    let (_, args) = am.spine(root);
                    match vargs(am, &args).get(index) {
                        Some(&a) => sources.exprs.push((ami, a)),
                        None => sources.top = Some(R_PARTIAL.into()),
                    }
                }
            }
        }
        let module = parts(&con)
            .map(|(_, md, _)| md.to_string())
            .unwrap_or_default();
        out.push(HRaw {
            slot: HSlot::Field {
                con: con.clone(),
                index,
            },
            mi: binders.first().map(|(mi, _)| *mi).unwrap_or(0),
            owner_binder: None,
            index,
            module,
            // A constructor's fields are shared by every module that can
            // build or match it: the rewrite never owns such a slot alone.
            exported: true,
            valued: false,
            sources,
        });
    }
    out
}

fn collect_closure_returns(w: &World) -> Vec<HRaw> {
    let mut out = Vec::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for b in 0..m.binders.len() as BinderId {
            let bi = m.binding(b);
            if !matches!(bi.site, BindSite::Top | BindSite::Let) {
                continue;
            }
            let Some(rhs) = bi.rhs else { continue };
            if m.binder(b).kind == BinderKind::Tyvar {
                continue;
            }
            let ps = w.lam_params(mi, rhs);
            if ps.is_empty() {
                continue;
            }
            let Some(res) = result_after(m.binder_ty(b), ps.len()) else {
                continue;
            };
            if !fun_ty(res) {
                continue;
            }
            let leaves = return_points(m, rhs);
            let depth = leaves.iter().map(|(_, d)| *d).max().unwrap_or(0);
            let mut sources = HSources::default();
            for (leaf, d) in &leaves {
                if *d == depth {
                    sources.exprs.push((mi, *leaf));
                }
            }
            if depth != ps.len() {
                sources.top = Some(R_NOT_A_FUNCTION.into());
            }
            out.push(HRaw {
                slot: HSlot::Return { mi, binder: b },
                mi,
                owner_binder: None,
                index: 0,
                module: m.name.clone(),
                exported: bi.site == BindSite::Top && m.binder(b).exported == Some(true),
                valued: used_as_value(w, mi, b),
                sources,
            });
        }
    }
    out
}

type HState = HashMap<HSlot, Set>;

/// What closures the expression at `node` can be, under the current state.
fn closure_eval(c: &HCtx, st: &HState, mi: usize, node: ExprId) -> Set {
    let w = c.w;
    let mut acc = Set::empty();
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work = vec![(mi, node)];
    let mut steps = 0usize;
    while let Some((mi, node)) = work.pop() {
        steps += 1;
        if steps > STEPS {
            return Set::top(R_BUDGET_STEPS);
        }
        if !seen.insert((mi, node)) {
            continue;
        }
        let m = w.m(mi);
        let inner = m.strip(node);
        let (head, args) = m.spine(inner);
        let va = vargs(m, &args);

        match m.expr(head) {
            Expr::Case { alts, .. } if va.is_empty() => {
                work.extend(alts.iter().map(|a| (mi, a.rhs)));
                continue;
            }
            Expr::Let { body, .. } if va.is_empty() => {
                work.push((mi, *body));
                continue;
            }
            // A manifest lambda: the closure is this node.
            Expr::Lam { .. } if va.is_empty() => {
                let key = format!("{}#{head}", m.name);
                c.note(&key, mi, head, PKind::Lambda);
                acc.join(&Set::one(&key));
                continue;
            }
            Expr::Var { .. } => {}
            _ => {
                acc.join(&Set::top(R_NOT_A_FUNCTION));
                continue;
            }
        }

        if let Some(b) = m.resolve(head) {
            let bi = m.binding(b);
            match bi.site {
                BindSite::Lam => {
                    if !va.is_empty() {
                        acc.join(&Set::top(R_HIGHER_ORDER));
                    } else {
                        match st.get(&HSlot::Param { mi, binder: b }) {
                            Some(v) => acc.join(v),
                            None => acc.join(&Set::top(R_HIGHER_ORDER)),
                        }
                    }
                }
                BindSite::Let | BindSite::Top => match bi.rhs {
                    Some(rhs) => {
                        closure_apply(c, st, mi, mi, b, rhs, inner, &va, &mut acc, &mut work)
                    }
                    None => acc.join(&Set::top(R_NOT_A_FUNCTION)),
                },
                BindSite::CaseBinder => match w.case_scrut[mi].get(&b) {
                    Some(&scrut) if va.is_empty() => work.push((mi, scrut)),
                    _ => acc.join(&Set::top(R_NOT_A_FUNCTION)),
                },
                // A closure read back out of a constructor field is a
                // genuine run-time closure, identified by the field.
                BindSite::AltBinder => match w.any_alt_field[mi].get(&b) {
                    Some((con, i)) => {
                        let key = format!("field:{con}#{i}");
                        c.note(&key, mi, head, PKind::FieldRead);
                        acc.join(&Set::one(&key));
                    }
                    None => acc.join(&Set::top(R_NOT_A_FUNCTION)),
                },
            }
            continue;
        }

        let Expr::Var { name, .. } = m.expr(head) else {
            unreachable!("the head is a Var here")
        };
        if let Some(&(wi, wb, rhs)) = w.tops.get(name) {
            closure_apply(c, st, mi, wi, wb, rhs, inner, &va, &mut acc, &mut work);
            continue;
        }
        let sig = head_sig(m, head);
        if sig.and_then(|s| s.data_con).is_some() {
            acc.join(&Set::top(R_NOT_A_FUNCTION));
            continue;
        }
        let arity = sig.map(|s| s.arity as usize).unwrap_or(0);
        if va.is_empty() && arity > 0 {
            // An imported function used as a value: a static function with
            // no environment.
            c.note(name, mi, head, PKind::ImportedFunction);
            acc.join(&Set::one(name));
        } else if va.is_empty() {
            acc.join(&Set::top(R_UNKNOWN_CALL));
        } else if va.len() < arity {
            let key = format!("{}#{inner}", m.name);
            c.note(&key, mi, inner, PKind::Partial);
            acc.join(&Set::one(&key));
        } else {
            // A closure returned by a call into a library.
            let key = format!("{}#{inner}", m.name);
            c.note(&key, mi, inner, PKind::ImportedCall);
            acc.join(&Set::one(&key));
        }
    }
    acc
}

/// A spine whose head is a function bound in the dump.
#[allow(clippy::too_many_arguments)]
fn closure_apply(
    c: &HCtx,
    st: &HState,
    cmi: usize,
    fmi: usize,
    fb: BinderId,
    rhs: ExprId,
    inner: ExprId,
    va: &[ExprId],
    acc: &mut Set,
    work: &mut Vec<(usize, ExprId)>,
) {
    let w = c.w;
    let fm = w.m(fmi);
    let ps = w.lam_params(fmi, rhs);
    let n = va.len();
    if ps.is_empty() {
        // An alias: the binder *is* its right-hand side.
        if n == 0 {
            work.push((fmi, rhs));
        } else {
            acc.join(&Set::top(R_NOT_A_FUNCTION));
        }
        return;
    }
    if n == 0 {
        let lam = fm.strip(rhs);
        let key = format!("{}#{lam}", fm.name);
        c.note(&key, fmi, lam, PKind::KnownFunction);
        acc.join(&Set::one(&key));
    } else if n < ps.len() {
        // A partial application: a closure over the arguments supplied. It
        // lives in the module the *call* is in, not the callee's.
        let key = format!("{}#{inner}", w.m(cmi).name);
        c.note(&key, cmi, inner, PKind::Partial);
        acc.join(&Set::one(&key));
    } else if n == ps.len() {
        match st.get(&HSlot::Return {
            mi: fmi,
            binder: fb,
        }) {
            Some(v) => acc.join(v),
            None => acc.join(&Set::top(R_UNTRACKED_RETURN)),
        }
    } else {
        acc.join(&Set::top(R_OVER_APPLIED));
    }
}

/// The local binders a lambda's body reads that the lambda does not bind:
/// its captured environment.
fn captures(m: &Module, lam: ExprId) -> Vec<BinderId> {
    let mut bound: HashSet<BinderId> = HashSet::new();
    for id in m.preorder(lam) {
        match m.expr(id) {
            Expr::Lam { binder, .. } => {
                bound.insert(*binder);
            }
            Expr::Let { bind, .. } => {
                for pr in &bind.pairs {
                    bound.insert(pr.binder);
                }
            }
            Expr::Case { binder, alts, .. } => {
                bound.insert(*binder);
                for a in alts {
                    bound.extend(a.binders.iter().copied());
                }
            }
            _ => {}
        }
    }
    let mut free: BTreeSet<BinderId> = BTreeSet::new();
    for id in m.preorder(lam) {
        if let Some(b) = m.resolve(id)
            && !bound.contains(&b)
            && m.binding(b).site != BindSite::Top
            && m.binder(b).kind != BinderKind::Tyvar
        {
            free.insert(b);
        }
    }
    free.into_iter().collect()
}

/// How many value arguments the head of a spine takes before it does work.
fn head_value_arity(w: &World, mi: usize, head: ExprId) -> usize {
    let m = w.m(mi);
    if let Some(b) = m.resolve(head)
        && let Some(rhs) = m.binding(b).rhs
    {
        let n = w.lam_params(mi, rhs).len();
        if n > 0 {
            return n;
        }
    }
    if let Expr::Var { name, .. } = m.expr(head)
        && let Some(&(wi, _, rhs)) = w.tops.get(name)
    {
        let n = w.lam_params(wi, rhs).len();
        if n > 0 {
            return n;
        }
    }
    head_sig(m, head).map(|s| s.arity as usize).unwrap_or(0)
}

/// The type key of an argument expression. Only a *variable* carries a
/// type here — binders do, expressions do not — so anything else gets a key
/// unique to its node and can never merge with another producer's.
fn arg_key(w: &World, mi: usize, a: ExprId, producer: &str) -> String {
    let m = w.m(mi);
    let inner = m.strip(a);
    match m.resolve(inner) {
        Some(b) => capture_key(m.binder_ty(b), producer),
        None => format!("?{}#{inner}", m.name),
    }
}

/// The shape of a producer: its arity and the ordered types it captures.
fn shape_of(w: &World, mi: usize, node: ExprId, kind: PKind, key: &str) -> PShape {
    let m = w.m(mi);
    match kind {
        PKind::FieldRead => PShape::Opaque {
            why: "a closure read back from a constructor field",
            producer: key.to_string(),
        },
        PKind::ImportedCall => PShape::Opaque {
            why: "a closure returned by a call the dump cannot see",
            producer: key.to_string(),
        },
        PKind::ImportedFunction => PShape::Known {
            arity: head_sig(m, node).map(|s| s.arity as usize).unwrap_or(0),
            captures: Vec::new(),
        },
        PKind::Lambda | PKind::KnownFunction => PShape::Known {
            arity: w.lam_params(mi, node).len(),
            captures: captures(m, node)
                .iter()
                .map(|b| capture_key(m.binder_ty(*b), key))
                .collect(),
        },
        PKind::Partial => {
            let (head, args) = m.spine(node);
            let va = vargs(m, &args);
            PShape::Known {
                arity: head_value_arity(w, mi, head).saturating_sub(va.len()),
                captures: va.iter().map(|&a| arg_key(w, mi, a, key)).collect(),
            }
        }
    }
}

/// The verdict, from the two facts kept apart.
///
/// **Sharing is decided before agreement.** How well the producers the dump
/// can see agree says nothing about code outside the rewrite that names the
/// same slot, so an exported slot, a slot on a function used as a value, and
/// a slot an opaque producer reaches are `Preserve` however well the
/// visible producers agree.
fn closure_judge(r: &HRaw, set: &Set, ps: &[HProducer], classes: usize) -> HVerdict {
    if let Set::Top(t) = set {
        return HVerdict::Unresolved(t.clone());
    }
    if ps.is_empty() {
        return HVerdict::Unresolved(R_NO_PRODUCER.into());
    }
    if let Some(o) = ps.iter().find(|x| x.shape.is_opaque()) {
        let why = match &o.shape {
            PShape::Opaque { why, .. } => *why,
            _ => unreachable!(),
        };
        return HVerdict::Preserve(format!("{why} ({} node {})", o.module, o.node));
    }
    if r.exported {
        return HVerdict::Preserve(format!("an exported slot ({})", r.module));
    }
    if r.valued {
        return HVerdict::Preserve(format!(
            "a slot of a function used as a value ({})",
            r.module
        ));
    }
    if ps.len() == 1 {
        return HVerdict::Exact;
    }
    if classes <= 1 {
        return HVerdict::Uniform;
    }
    // Only a *parameter* of a local function that is neither exported nor
    // used as a value can be cloned: every call site of it is visible.
    if matches!(r.slot, HSlot::Param { .. }) {
        return HVerdict::Clone(classes);
    }
    HVerdict::Finite(ps.len())
}

/// The higher-order half, as this walk derives it.
pub struct HigherDerived {
    boundaries: Vec<HBoundary>,
    at: HashMap<(String, HSlot), usize>,
    /// Per-owning-function closure clone plan.
    owner_plans: BTreeMap<(usize, BinderId), OwnerPlan>,
    pub rounds: usize,
}

impl HigherDerived {
    pub fn of_world(w: &World) -> HigherDerived {
        let mut raws: Vec<HRaw> = collect_closure_params(w);
        raws.extend(collect_closure_fields(w));
        raws.extend(collect_closure_returns(w));
        let c = HCtx {
            w,
            found: std::cell::RefCell::new(BTreeMap::new()),
        };
        let mut state: HState = raws
            .iter()
            .map(|r| (r.slot.clone(), Set::empty()))
            .collect();

        let mut rounds = 0usize;
        loop {
            rounds += 1;
            let mut changed = false;
            let mut next = state.clone();
            for r in &raws {
                let mut acc = Set::empty();
                if let Some(t) = &r.sources.top {
                    acc.join(&Set::Top(t.clone()));
                }
                for &(smi, node) in &r.sources.exprs {
                    acc.join(&closure_eval(&c, &state, smi, node));
                }
                let slot = next.get_mut(&r.slot).unwrap();
                if *slot != acc {
                    *slot = acc;
                    changed = true;
                }
            }
            state = next;
            if !changed {
                break;
            }
            if rounds >= ROUNDS {
                for v in state.values_mut() {
                    if !v.is_top() {
                        v.join(&Set::top(R_BUDGET_ROUNDS));
                    }
                }
                break;
            }
        }

        // The producers the walk found, resolved once the sets have settled.
        let found = c.found.borrow().clone();
        let producers: BTreeMap<String, HProducer> = found
            .iter()
            .map(|(key, (mi, node, kind))| {
                (
                    key.clone(),
                    HProducer {
                        key: key.clone(),
                        module: w.m(*mi).name.clone(),
                        node: *node,
                        shape: shape_of(w, *mi, *node, *kind, key),
                    },
                )
            })
            .collect();

        let mut boundaries = Vec::new();
        for r in &raws {
            let set = state[&r.slot].clone();
            let mut ps: Vec<HProducer> = set
                .keys()
                .iter()
                .filter_map(|k| producers.get(k).cloned())
                .collect();
            ps.sort_by(|a, b| a.key.cmp(&b.key));
            let enumerated = !set.is_top() && !set.keys().is_empty();
            let mut classes: Vec<String> = ps.iter().map(|x| x.shape.class()).collect();
            classes.sort();
            classes.dedup();
            let n_classes = if enumerated { classes.len() } else { 0 };
            let verdict = closure_judge(r, &set, &ps, n_classes);
            boundaries.push(HBoundary {
                slot: r.slot.clone(),
                module: r.module.clone(),
                exported: r.exported,
                valued: r.valued,
                set,
                producers: ps,
                enumerated,
                classes: n_classes,
                verdict,
            });
        }

        let owner_plans = closure_owner_plans(&c, &state, &raws, &boundaries, &producers);

        let at = boundaries
            .iter()
            .enumerate()
            .map(|(i, b)| ((b.module.clone(), b.slot.clone()), i))
            .collect();

        HigherDerived {
            boundaries,
            at,
            owner_plans,
            rounds,
        }
    }
}

/// Clone plans per **owning function**: the distinct call-site
/// shape-assignment tuples of its function-valued parameters, deduplicated.
fn closure_owner_plans(
    c: &HCtx,
    st: &HState,
    raws: &[HRaw],
    boundaries: &[HBoundary],
    producers: &BTreeMap<String, HProducer>,
) -> BTreeMap<(usize, BinderId), OwnerPlan> {
    let w = c.w;
    let mut groups: BTreeMap<(usize, BinderId), Vec<usize>> = BTreeMap::new();
    let mut wanted: BTreeSet<(usize, BinderId)> = BTreeSet::new();
    for (i, r) in raws.iter().enumerate() {
        let Some(f) = r.owner_binder else { continue };
        if !matches!(r.slot, HSlot::Param { .. }) {
            continue;
        }
        groups.entry((r.mi, f)).or_default().push(i);
        if boundaries
            .iter()
            .any(|b| b.slot == r.slot && matches!(b.verdict, HVerdict::Clone(_)))
        {
            wanted.insert((r.mi, f));
        }
    }

    // The shape classes a settled producer set stands for, rendered.
    let component = |set: &Set| -> Result<(String, bool), String> {
        if let Set::Top(t) = set {
            return Err(t.clone());
        }
        let mut ks: BTreeSet<String> = BTreeSet::new();
        for k in set.keys() {
            match producers.get(&k) {
                Some(x) => {
                    ks.insert(x.shape.short());
                }
                None => return Err(R_NO_PRODUCER.into()),
            }
        }
        if ks.is_empty() {
            return Err(R_NO_PRODUCER.into());
        }
        let many = ks.len() > 1;
        Ok((ks.into_iter().collect::<Vec<_>>().join("|"), many))
    };

    let mut out = BTreeMap::new();
    for key in &wanted {
        let (mi, f) = *key;
        let arg_indices: Vec<usize> = groups[key].iter().map(|&i| raws[i].index).collect();
        let mut tuples: BTreeSet<Vec<String>> = BTreeSet::new();
        let mut set_valued: BTreeSet<Vec<String>> = BTreeSet::new();
        let mut refused: Option<String> = None;
        for (omi, o) in w.all_occurrences(mi, f) {
            let om = w.m(omi);
            let root = om.spine_root(o);
            let (head, args) = om.spine(root);
            if root == o || om.strip(head) != om.strip(o) {
                refused = Some(R_VALUE_USE.into());
                break;
            }
            let va = vargs(om, &args);
            let mut tuple = Vec::with_capacity(arg_indices.len());
            let mut many = 0usize;
            for &ai in &arg_indices {
                let Some(&a) = va.get(ai) else {
                    refused = Some(R_PARTIAL.into());
                    break;
                };
                match component(&closure_eval(c, st, omi, a)) {
                    Ok((rendered, multi)) => {
                        if multi {
                            many += 1;
                        }
                        tuple.push(rendered);
                    }
                    Err(why) => {
                        refused = Some(why);
                        break;
                    }
                }
            }
            if refused.is_some() {
                break;
            }
            if many > 0 {
                set_valued.insert(tuple.clone());
            }
            tuples.insert(tuple);
        }
        out.insert(
            *key,
            OwnerPlan {
                params: arg_indices.len(),
                tuples: tuples.len(),
                set_valued: set_valued.len(),
                refused,
            },
        );
    }
    out
}

//------------------------------------------------------------------------------
// Checking the claims
//------------------------------------------------------------------------------

/// How a `Top` set is classified when the analysis claims a bounded one.
///
/// A `Top` here says only that **this** walk could not account for every
/// producer, which is this walk being blunter than the analysis and costs
/// coverage. What would be a disagreement is naming a producer the analysis
/// does not have, and that is [`X_SET_DIFFERS`]; every such refusal was
/// looked at individually rather than waved through.
fn top_refusal(reason: &str) -> Refusal {
    if reason.starts_with("set-exceeded")
        || reason.starts_with("fixpoint-exceeded")
        || reason.starts_with("evaluation-exceeded")
        || reason.starts_with("field-read-exceeded")
    {
        Refusal::new(C_BUDGET, reason)
    } else {
        Refusal::new(C_SET_TOP, reason)
    }
}

fn keys_line(k: &BTreeSet<String>) -> String {
    k.iter().cloned().collect::<Vec<_>>().join(", ")
}

impl DictDerived {
    fn check_site_exact(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let Subject::Site { module, node } = &c.subject else {
            return Err(Refusal::new(C_NO_SITE, "not a site claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        let Some(&i) = self.site_at.get(&(mi, *node)) else {
            return Err(Refusal::new(C_NO_SITE, format!("{module} node {node}")));
        };
        let s = &self.sites[i];
        if s.spec.is_none() {
            return Err(Refusal::new(C_CLASS_UNKNOWN, s.occ.clone()));
        }
        match &s.target {
            Ok(Some(t)) => {
                if Some(t) == c.target.as_ref() {
                    Ok(())
                } else {
                    Err(Refusal::new(
                        X_TARGET_DIFFERS,
                        format!("{t} vs {}", c.target.clone().unwrap_or_default()),
                    ))
                }
            }
            Ok(None) => Err(Refusal::new(
                X_NO_TARGET,
                "the bounded set reaches more than one method binding",
            )),
            Err(_) if s.set.is_top() => Err(top_refusal(s.set.reason().unwrap_or(""))),
            Err(r) => Err(Refusal::new(X_NO_TARGET, r.clone())),
        }
    }

    fn check_site_bounded(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let Subject::Site { module, node } = &c.subject else {
            return Err(Refusal::new(C_NO_SITE, "not a site claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        let Some(&i) = self.site_at.get(&(mi, *node)) else {
            return Err(Refusal::new(C_NO_SITE, format!("{module} node {node}")));
        };
        same_set(&self.sites[i].set, &c.keys)
    }

    fn check_param_bounded(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let x = self.param(w, c)?;
        same_set(&x.set, &c.keys)
    }

    fn param<'a>(&'a self, w: &World, c: &Claim) -> Result<&'a DParam, Refusal> {
        let Subject::Param { module, binder } = &c.subject else {
            return Err(Refusal::new(C_NO_PARAM, "not a parameter claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        match self.param_at.get(&(mi, *binder)) {
            Some(&i) => Ok(&self.params[i]),
            None => Err(Refusal::new(
                C_NO_PARAM,
                format!("{module} binder {binder}"),
            )),
        }
    }

    fn check_value_erasure(&self, c: &Claim) -> Result<(), Refusal> {
        let Subject::Value { key } = &c.subject else {
            return Err(Refusal::new(C_NO_VALUE, "not a value claim"));
        };
        let Some(v) = self.value_verdict.get(key) else {
            return Err(Refusal::new(C_NO_VALUE, key.clone()));
        };
        match v {
            EVerdict::Erasable if c.verdict == "Erasable" => Ok(()),
            EVerdict::Preserve(h) => Err(Refusal::new(X_ESCAPES, h.clone())),
            EVerdict::Unresolved(r) => Err(top_refusal(r)),
            other => Err(Refusal::new(
                X_INSTANCES_DIFFER,
                format!("{} vs {}", other.label(), c.verdict),
            )),
        }
    }

    fn check_param_erasure(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let Subject::Param { module, binder } = &c.subject else {
            return Err(Refusal::new(C_NO_PARAM, "not a parameter claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        let Some(&i) = self.param_at.get(&(mi, *binder)) else {
            return Err(Refusal::new(
                C_NO_PARAM,
                format!("{module} binder {binder}"),
            ));
        };
        let mine = &self.param_verdict[i];
        let x = &self.params[i];
        match (mine, c.verdict.as_str()) {
            (EVerdict::Erasable, "Erasable") => Ok(()),
            (EVerdict::WithClone(n), "ErasableWithClone") => {
                if *n == c.n {
                    Ok(())
                } else {
                    Err(Refusal::new(
                        X_INSTANCES_DIFFER,
                        format!("{n} instances here, {} claimed", c.n),
                    ))
                }
            }
            (EVerdict::WithObligation, "ErasableWithObligation") => Ok(()),
            (EVerdict::Erasable, "ErasableWithObligation") => Err(Refusal::new(
                X_NO_OBLIGATION,
                "this walk proves the producers total",
            )),
            (EVerdict::Preserve(h), _) if x.tot.level == Tot::Total => {
                Err(Refusal::new(X_ESCAPES, h.clone()))
            }
            (EVerdict::Preserve(h), _) => Err(Refusal::new(X_NOT_TOTAL, h.clone())),
            (EVerdict::Unresolved(r), _) => Err(top_refusal(r)),
            (EVerdict::WithClone(n), "Erasable") => Err(Refusal::new(
                X_INSTANCES_DIFFER,
                format!("{n} instances here, one claimed"),
            )),
            (a, b) => Err(Refusal::new(
                X_INSTANCES_DIFFER,
                format!("{} vs {b}", a.label()),
            )),
        }
    }

    fn check_clone_plan(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let Subject::DictOwner { module, owner } = &c.subject else {
            return Err(Refusal::new(C_NO_OWNER, "not an owner claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        check_plan(self.owner_plans.get(&(mi, *owner)), c)
    }
}

/// Does this walk's set have exactly the members the claim asserts?
fn same_set(set: &Set, keys: &[String]) -> Result<(), Refusal> {
    match set {
        Set::Top(r) => Err(top_refusal(r)),
        Set::Fin(mine) => {
            let theirs: BTreeSet<String> = keys.iter().cloned().collect();
            if *mine == theirs {
                Ok(())
            } else {
                Err(Refusal::new(
                    X_SET_DIFFERS,
                    format!("{{{}}} vs {{{}}}", keys_line(mine), keys_line(&theirs)),
                ))
            }
        }
    }
}

fn check_plan(plan: Option<&OwnerPlan>, c: &Claim) -> Result<(), Refusal> {
    let Some(p) = plan else {
        return Err(Refusal::new(C_NO_OWNER, c.what.clone()));
    };
    if let Some(r) = &p.refused {
        return Err(Refusal::new(C_NO_OWNER, format!("refused here: {r}")));
    }
    if p.tuples == c.n {
        Ok(())
    } else {
        Err(Refusal::new(
            X_CLONES_DIFFER,
            format!("{} distinct tuples here, {} claimed", p.tuples, c.n),
        ))
    }
}

impl HigherDerived {
    fn boundary(&self, w: &World, c: &Claim) -> Result<&HBoundary, Refusal> {
        let Subject::Boundary { module, slot } = &c.subject else {
            return Err(Refusal::new(C_NO_BOUNDARY, "not a boundary claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        let key = match slot {
            ClaimSlot::Param { binder } => HSlot::Param {
                mi,
                binder: *binder,
            },
            ClaimSlot::Return { binder } => HSlot::Return {
                mi,
                binder: *binder,
            },
            ClaimSlot::Field { con, index } => HSlot::Field {
                con: con.clone(),
                index: *index,
            },
        };
        match self.at.get(&(module.clone(), key)) {
            Some(&i) => Ok(&self.boundaries[i]),
            None => Err(Refusal::new(C_NO_BOUNDARY, c.what.clone())),
        }
    }

    fn check_verdict(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let b = self.boundary(w, c)?;
        // The producer set first: a verdict about producers that are not
        // these producers is not the same verdict.
        same_set(&b.set, &c.keys)?;
        match (&b.verdict, c.verdict.as_str()) {
            (HVerdict::Exact, "ExactClosure") => Ok(()),
            (HVerdict::Uniform, "TypeShapeUniform") => Ok(()),
            (HVerdict::Clone(n), "CloneRequired") => {
                if *n == c.n {
                    Ok(())
                } else {
                    Err(Refusal::new(
                        X_CLASSES_DIFFER,
                        format!("{n} shape classes here, {} claimed", c.n),
                    ))
                }
            }
            (HVerdict::Finite(n), "FiniteClosureSet") => {
                if *n == c.n {
                    Ok(())
                } else {
                    Err(Refusal::new(
                        X_CLASSES_DIFFER,
                        format!("{n} producers here, {} claimed", c.n),
                    ))
                }
            }
            (HVerdict::Preserve(h), _) => {
                let opaque = b.producers.iter().any(|p| p.shape.is_opaque());
                Err(Refusal::new(
                    if opaque {
                        X_OPAQUE_PRODUCER
                    } else {
                        X_SHARED_SLOT
                    },
                    h.clone(),
                ))
            }
            (HVerdict::Unresolved(r), _) => Err(top_refusal(r)),
            (HVerdict::Finite(_), "CloneRequired") => Err(Refusal::new(
                X_NOT_A_PARAM_SLOT,
                "this walk does not call that slot a parameter",
            )),
            (a, bl) => Err(Refusal::new(
                X_PRODUCERS_DIFFER,
                format!("{} vs {bl}", a.label()),
            )),
        }
    }

    fn check_clone_plan(&self, w: &World, c: &Claim) -> Result<(), Refusal> {
        let Subject::ClosureOwner { module, owner } = &c.subject else {
            return Err(Refusal::new(C_NO_OWNER, "not an owner claim"));
        };
        let Some(mi) = w.module_index(module) else {
            return Err(Refusal::new(C_MODULE_MISSING, module.clone()));
        };
        check_plan(self.owner_plans.get(&(mi, *owner)), c)
    }
}

//------------------------------------------------------------------------------
// The adversarial shapes, counted in the real dump
//------------------------------------------------------------------------------

/// Each shape has a hand-built regression test in `tests.rs` **and** a
/// count here, so that a test is never the only evidence a rule was
/// exercised. Every row is read off this walk's own derivation, never off
/// the analyses'.
fn shapes(w: &World, dd: &DictDerived, hd: &HigherDerived) -> Vec<ShapeRow> {
    let mut out: Vec<ShapeRow> = Vec::new();
    let mut row = |name: &'static str, verdict: &'static str, hits: Vec<String>| {
        out.push(ShapeRow {
            n: hits.len(),
            name,
            verdict,
            at: hits.first().cloned().unwrap_or_else(|| "—".into()),
        });
    };
    let lam_node = |x: &DParam| -> String {
        match w.lam_of[x.mi].get(&x.binder) {
            Some(n) => format!("{} node {n}", x.module),
            None => format!("{} binder {}", x.module, x.binder),
        }
    };

    // 1 — a bounded dictionary identity whose producer is not total.
    row(
        "1  bounded dictionary identity, producer not proven total",
        "never Erasable",
        dd.params
            .iter()
            .filter(|x| !x.set.is_top() && !x.set.keys().is_empty() && x.tot.level == Tot::Force)
            .map(lam_node)
            .collect(),
    );
    // 2 — one dictionary parameter reaching two or more instances.
    row(
        "2  one dictionary parameter, two or more instances",
        "FiniteSet(n) / ErasableWithClone(n)",
        dd.params
            .iter()
            .filter(|x| x.set.keys().len() >= 2)
            .map(lam_node)
            .collect(),
    );
    // 3 — a dictionary used as an ordinary value *and* for a selector.
    let dict_args: HashSet<(usize, ExprId)> = dd
        .sites
        .iter()
        .filter_map(|s| s.dict.map(|d| (s.mi, w.m(s.mi).strip(d))))
        .collect();
    row(
        "3  a dictionary used as a value and as a selector's dictionary",
        "Preserve; the method target is unaffected",
        dd.params
            .iter()
            .enumerate()
            .filter(|(i, x)| {
                matches!(dd.param_verdict[*i], EVerdict::Preserve(_))
                    && w.m(x.mi)
                        .occurrences(x.binder)
                        .iter()
                        .any(|&o| dict_args.contains(&(x.mi, w.m(x.mi).strip(o))))
            })
            .map(|(_, x)| lam_node(x))
            .collect(),
    );
    // 4 — a dictionary parameter whose totality cannot be decided.
    row(
        "4  a dictionary parameter of unknown totality",
        "Unresolved / Preserve(totality)",
        dd.params
            .iter()
            .filter(|x| x.tot.level == Tot::Unknown)
            .map(lam_node)
            .collect(),
    );
    // 5 — superclass selection.
    row(
        "5  a superclass selector site ($pN<Class>)",
        "follows to the superclass instance",
        dd.sites
            .iter()
            .filter(|s| s.occ.starts_with("$p"))
            .map(|s| format!("{} node {}", s.module, s.node))
            .collect(),
    );
    // 6 — a dictionary parameter reached only through dispatch: an
    // instance method's own dictionary, and a default method's.
    row(
        "6  a dictionary parameter fed through dispatch",
        "terminates; the fixpoint is monotone",
        dd.params
            .iter()
            .filter(|x| !x.producers.slots.is_empty())
            .map(lam_node)
            .collect(),
    );
    // 7 — a partially applied class op.
    row(
        "7  a partially applied class-op selector",
        "recorded, no target claimed",
        dd.sites
            .iter()
            .filter(|s| s.dict.is_none())
            .map(|s| format!("{} node {}", s.module, s.node))
            .collect(),
    );
    // 8 — an exported or valued higher-order slot whose visible producers
    // nevertheless agree.
    row(
        "8  an exported or valued function slot whose producers do agree",
        "Preserve, decided before agreement",
        hd.boundaries
            .iter()
            .filter(|b| {
                (b.exported || b.valued)
                    && b.enumerated
                    && !b.producers.iter().any(|p| p.shape.is_opaque())
                    && (b.producers.len() == 1 || b.classes == 1)
            })
            .map(|b| format!("{} {}", b.module, slot_label(&b.slot)))
            .collect(),
    );
    // 9 — two opaque producers at one slot.
    row(
        "9  a slot two opaque producers reach",
        "two classes: opaque unifies with nothing",
        hd.boundaries
            .iter()
            .filter(|b| b.producers.iter().filter(|p| p.shape.is_opaque()).count() >= 2)
            .map(|b| format!("{} {}", b.module, slot_label(&b.slot)))
            .collect(),
    );
    // 10 — a capture type carrying a free type variable.
    let mut free_tyvar: Vec<String> = Vec::new();
    for b in &hd.boundaries {
        for p in &b.producers {
            if let PShape::Known { captures, .. } = &p.shape
                && captures.iter().any(|k| k.starts_with('<'))
            {
                free_tyvar.push(format!("{} node {}", p.module, p.node));
            }
        }
    }
    free_tyvar.sort();
    free_tyvar.dedup();
    row(
        "10 a capture type with a free type variable",
        "a producer-private key: unifies with nothing",
        free_tyvar,
    );
    // 11 — an alternative binding an existential type binder before a
    // value field, and the function-typed fields behind one.
    let mut existential: Vec<String> = Vec::new();
    let mut existential_fn: Vec<String> = Vec::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Case { alts, .. } = m.expr(id) else {
                continue;
            };
            for alt in alts {
                let mut seen_ty = false;
                let mut any = false;
                for &b in &alt.binders {
                    if m.binder(b).kind == BinderKind::Tyvar {
                        seen_ty = true;
                        continue;
                    }
                    if seen_ty {
                        any = true;
                        if fun_ty(m.binder_ty(b)) {
                            existential_fn.push(format!("{} node {id}", m.name));
                        }
                    }
                }
                if any {
                    existential.push(format!("{} node {id}", m.name));
                }
            }
        }
    }
    row(
        "11 a value field bound after an existential type binder",
        "value-field indexing, not raw binder position",
        existential,
    );
    row(
        "11a … and the field is function-typed",
        "pairs with the constructor's value argument",
        existential_fn,
    );
    // 12 — a multi-parameter owner planned from joint call-site tuples.
    row(
        "12 an owner with two or more slots, planned jointly",
        "clones = distinct call-site tuples",
        hd.owner_plans
            .iter()
            .chain(dd.owner_plans.iter())
            .filter(|(_, p)| p.params >= 2 && p.refused.is_none())
            .map(|((mi, f), p)| {
                format!(
                    "{} {} ({} slots, {} tuples)",
                    w.m(*mi).name,
                    w.m(*mi).binder(*f).occ,
                    p.params,
                    p.tuples
                )
            })
            .collect(),
    );
    // 13 — one formal receiving closures of several representations.
    row(
        "13 several representations at one slot, at a local",
        "CloneRequired",
        hd.boundaries
            .iter()
            .filter(|b| matches!(b.verdict, HVerdict::Clone(_)))
            .map(|b| format!("{} {}", b.module, slot_label(&b.slot)))
            .collect(),
    );
    row(
        "13a … the same, at an exported or valued slot",
        "Preserve",
        hd.boundaries
            .iter()
            .filter(|b| {
                b.classes >= 2
                    && (b.exported || b.valued)
                    && matches!(b.verdict, HVerdict::Preserve(_))
            })
            .map(|b| format!("{} {}", b.module, slot_label(&b.slot)))
            .collect(),
    );
    // 14 — a finite closure set.
    row(
        "14 a finite closure set at a slot no clone can serve",
        "FiniteClosureSet(n)",
        hd.boundaries
            .iter()
            .filter(|b| matches!(b.verdict, HVerdict::Finite(_)))
            .map(|b| format!("{} {}", b.module, slot_label(&b.slot)))
            .collect(),
    );
    // 15 — a closure that *looks* like a Parsec continuation. Nothing here
    // reads the name: the shape class is arity and captures, so a
    // three-argument `cok`-named lambda is classed exactly as any other
    // three-argument lambda, and this walk claims no role for it.
    let mut parsec_shaped: Vec<String> = Vec::new();
    for mi in 0..w.modules.len() {
        let m = w.m(mi);
        for b in 0..m.binders.len() as BinderId {
            let occ = &m.binder(b).occ;
            if !(occ.starts_with("cok")
                || occ.starts_with("eok")
                || occ.starts_with("cerr")
                || occ.starts_with("eerr"))
            {
                continue;
            }
            let Some(rhs) = m.binding(b).rhs else {
                continue;
            };
            if w.lam_params(mi, rhs).len() == 3 {
                parsec_shaped.push(format!("{} node {rhs}", m.name));
            }
        }
    }
    row(
        "15 a three-argument closure named like a Parsec continuation",
        "arity and captures decide; no name is read",
        parsec_shaped,
    );
    out
}

fn slot_label(s: &HSlot) -> String {
    match s {
        HSlot::Param { binder, .. } => format!("parameter binder {binder}"),
        HSlot::Return { binder, .. } => format!("return binder {binder}"),
        HSlot::Field { con, index } => format!(
            "field {index} of {}",
            parts(con).map(|(_, _, o)| o).unwrap_or(con)
        ),
    }
}

//------------------------------------------------------------------------------
// The entry point
//------------------------------------------------------------------------------

/// Re-derive every claim, independently, and report what did not come back.
pub fn verify(modules: &[&Module], claims: &[Claim]) -> Audit {
    let w = World::new(modules.iter().copied());
    assert!(
        w.collisions.is_empty(),
        "external stable names are not unique: {:?}",
        w.collisions
    );
    let dd = DictDerived::of_world(&w);
    let hd = HigherDerived::of_world(&w);

    let mut a = Audit {
        dict_rounds: dd.rounds,
        tot_rounds: dd.tot_rounds,
        closure_rounds: hd.rounds,
        dict_case_nodes: dd.tot_cases,
        dict_plans_set_valued: dd.owner_plans.values().filter(|p| p.set_valued > 0).count(),
        closure_plans_set_valued: hd.owner_plans.values().filter(|p| p.set_valued > 0).count(),
        own_sites: dd.sites.len(),
        own_params: dd.params.len(),
        own_values: dd.value_verdict.len(),
        own_boundaries: hd.boundaries.len(),
        ..Default::default()
    };
    let mut by: BTreeMap<ClaimKind, (usize, usize, usize, usize)> = BTreeMap::new();
    for c in claims {
        let r = match c.kind {
            ClaimKind::SiteExact => dd.check_site_exact(&w, c),
            ClaimKind::SiteBounded => dd.check_site_bounded(&w, c),
            ClaimKind::ParamBounded => dd.check_param_bounded(&w, c),
            ClaimKind::ValueErasure => dd.check_value_erasure(c),
            ClaimKind::ParamErasure => dd.check_param_erasure(&w, c),
            ClaimKind::DictClonePlan => dd.check_clone_plan(&w, c),
            ClaimKind::HigherVerdict => hd.check_verdict(&w, c),
            ClaimKind::ClosureClonePlan => hd.check_clone_plan(&w, c),
        };
        let e = by.entry(c.kind).or_insert((0, 0, 0, 0));
        e.0 += 1;
        a.checked += 1;
        match r {
            Ok(()) => {
                e.1 += 1;
                a.agreed += 1;
            }
            Err(refusal) => {
                if is_coverage_refusal(refusal.why) {
                    e.3 += 1;
                } else {
                    e.2 += 1;
                }
                a.disagreements.push(Disagreement {
                    claim: c.clone(),
                    refusal,
                });
            }
        }
    }
    a.by_kind = by
        .into_iter()
        .map(|(k, (n, ok, d, c))| (k, n, ok, d, c))
        .collect();
    a.shapes = shapes(&w, &dd, &hd);
    a
}
