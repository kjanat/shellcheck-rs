//! Whole-program dictionary propagation, and — as a **separate** proof
//! object — whether the dictionaries can be erased.
//!
//! # The closed-world assumption, stated
//!
//! The 28 modules in the dump are **the entire program**. `Main.main` is
//! the only root: nothing outside the dump calls into ShellCheck's library
//! modules, there is no plugin interface, no `dlopen`, no Template Haskell
//! left after `striptests`, and the `prop_*` corpus (the only other
//! importer of these modules) is removed from a production build. This is
//! [`W0_CLOSED_WORLD`], and it is an **assumption**, asserted here and in
//! the README, not something the dump can prove. Everything below depends
//! on it: without it, an exported function's dictionary parameter has an
//! unbounded producer set and nothing in Part 1 resolves.
//!
//! Under it, every function's dictionary parameter *does* have an
//! enumerable producer set — the union over **all** call sites in **all**
//! modules, found by stable name through the global occurrences of the
//! function ([`W1_GLOBAL_CALLERS`]) — unless the function is also used as a
//! value somewhere, which makes the set unenumerable exactly as
//! [`crate::boundary`] found for tuples.
//!
//! # Part 1 — the fixpoint
//!
//! Dictionary **values** are dfun applications, dictionary-constructor
//! applications, and superclass selections thereof ([`W2_DICT_VALUE`]).
//! Dictionary **parameters** accumulate the union of what reaches them,
//! across modules ([`W3_PARAM_UNION`]). **Dispatch** ([`W4_DISPATCH`]): a
//! class-op site whose dictionary set is known selects, per dictionary,
//! the method in that dictionary's field; where that method is a separate
//! global binding in the dump (`$fTraversableInnerToken_$ctraverse` and
//! its kin), the dispatch supplies its arguments, so the method's *own*
//! dictionary parameters receive what the site passes and propagation
//! continues through dispatch.
//!
//! The analysis is **monovariant** ([`W5_MONOVARIANT`]): one abstract
//! value per dictionary identity, one set per parameter, no call-string
//! context. That loses precision (a dfun applied to two different argument
//! dictionaries has one identity here) and never soundness — the set at a
//! parameter is always a superset of what can reach it at run time.
//!
//! Anything the walk cannot account for **taints** ([`W6_TAINT`]): an
//! unknown producer, a dictionary read from a non-dictionary constructor
//! field, a dictionary returned by a call the dump cannot see, a function
//! used as a value. A tainted set is `Top(reason)` and every site
//! downstream of it is `Unresolved(reason)`. A class-op site whose
//! dictionary is `Top` could select **any** instance of its class,
//! including one outside the dump, so every method sitting at that class's
//! field index is tainted too: that is how the taint crosses dispatch.
//!
//! # Part 2 — erasure agreement
//!
//! **KNOWN METHOD TARGET ≠ REMOVABLE DICTIONARY.** This is the exact
//! analogue of M2.2.1's *locally removable ≠ globally composable*: Part 1
//! says which method runs, and says nothing whatever about whether the
//! dictionary itself can disappear. A dictionary with a single known
//! instance may still be stored in a constructor, handed to an imported
//! callee, or forced where erasure would move the divergence. The verdicts
//! in [`Erasure`] are computed from facts recorded **separately** from
//! Part 1 — evaluation ([`E1_TOTAL`]), representation agreement at every
//! boundary the dictionary crosses ([`E2_AGREE`], [`E3_CLONE`]) and escape
//! ([`E4_ESCAPE`]) — and the two questions are crossed, never collapsed,
//! in the 3×4 matrix ([`Accounting::matrix`]), whose `Exact` × `Preserve`
//! cell ([`E5_PRESERVED_DISPATCH`]) is the population that keeps a
//! run-time dictionary even though its target is known.
//!
//! # Budgets
//!
//! Stated, and exceeding one produces `Unresolved`, never a guess:
//! [`ROUND_BUDGET`] fixpoint rounds, [`SET_CAP`] dictionaries in one set,
//! [`EVAL_BUDGET`] expression steps per evaluation and [`NEST_CAP`] nested
//! field reads.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use h2r_core_ir::{AltCon, BindSite, BinderId, BinderKind, Edge, Expr, ExprId, Module};
use serde::Serialize;

use crate::callee::{is_dictionary_name, split_stable_name};
use crate::classops::{CLASSES, ClassSpec, class_ty, selector_class};
use crate::scope::Scope;
use crate::shape::value_args;

//------------------------------------------------------------------------------
// Rules
//------------------------------------------------------------------------------

/// **The closed world.** The 28 modules of the dump are the whole program
/// and `Main.main` is its only root, so every call site of every function
/// is in the dump. Evidence: a stated assumption about the build (5) — not
/// derived from the dump, and everything in Part 1 rests on it.
pub const W0_CLOSED_WORLD: &str = "W0-CLOSED-WORLD";
/// **Callers.** The call sites of a top-level function are its occurrences
/// in every module of the closed world, found by stable name. Evidence:
/// def-use over stable global identity (3).
pub const W1_GLOBAL_CALLERS: &str = "W1-GLOBAL-CALLERS";
/// **Values.** A dictionary value is a saturated dictionary-constructor
/// application, a dfun (applied or not) or a superclass selection of one.
/// Evidence: structural saturation (2) over `DataConInfo` (4).
pub const W2_DICT_VALUE: &str = "W2-DICT-VALUE";
/// **Parameters.** A dictionary parameter holds the union of the
/// dictionaries that reach it over all call sites in the closed world.
/// Evidence: def-use dataflow (3).
pub const W3_PARAM_UNION: &str = "W3-PARAM-UNION";
/// **Dispatch.** A class-op site with a known dictionary set selects, per
/// dictionary, the method at the class's field index; where that method is
/// a binding in the dump, the site's remaining arguments are that
/// binding's actual arguments, so its own dictionary parameters are fed
/// from the dispatch. Evidence: def-use through the class table (3).
pub const W4_DISPATCH: &str = "W4-DISPATCH";
/// **Monovariance.** One abstract value per dictionary identity and one
/// set per parameter, with no calling context: an over-approximation by
/// construction. Evidence: a stated property of the analysis (5).
pub const W5_MONOVARIANT: &str = "W5-MONOVARIANT";
/// **Taint.** A dictionary from a source the closed world cannot account
/// for makes the set `Top`, and every site it reaches `Unresolved`; a
/// class-op site with a `Top` dictionary taints every method at that
/// class's field index, because any instance could be selected there.
/// Evidence: def-use (3).
pub const W6_TAINT: &str = "W6-TAINT";
/// **Budget.** A walk that exceeds a stated budget is `Unresolved`, never
/// a guess. Evidence: structural (2).
pub const W7_BUDGET: &str = "W7-BUDGET";

/// **The two questions are separate.** A known method target is **not** a
/// removable dictionary: Part 1's outcome and Part 2's verdict are
/// computed from different facts and reported as different objects.
/// Evidence: a stated property of the proof object (5).
pub const E0_SEPARATE: &str = "E0-SEPARATE";
/// **Evaluation.** Replacing `classOp d x` by `method x` can only change
/// behaviour if `d` could be bottom and the selector forced it; a
/// dictionary-constructor application or a dfun application is a value, so
/// a parameter all of whose producers are such values is total and erasure
/// cannot move divergence earlier. A parameter GHC records as strict is
/// forced at entry already. Evidence: compiler axiom (5) over GHC's own
/// demand information (4).
pub const E1_TOTAL: &str = "E1-TOTAL";
/// **Representation agreement.** Every producer that reaches a boundary a
/// dictionary crosses — a parameter, a return, a constructor field — must
/// request the same erased form, i.e. the same instance. Evidence:
/// def-use over the whole-program producer sets (3).
pub const E2_AGREE: &str = "E2-AGREE";
/// **Clone.** Producers that disagree at a function that is never used as
/// a value can be served by one specialised clone per instance. Evidence:
/// def-use (3); the clones are counted, never made.
pub const E3_CLONE: &str = "E3-CLONE";
/// **Escape.** The dictionary is used as an ordinary value — stored in a
/// constructor that is not a dictionary constructor, passed to a callee
/// the dump cannot see, or returned from a function used as a value — so
/// it must be preserved, and the holder is named. Evidence: def-use (3).
pub const E4_ESCAPE: &str = "E4-ESCAPE";
/// **A preserved dispatch.** A site whose method target is `Exact` but
/// whose dictionary is `Preserve` still dispatches at run time on a
/// dictionary that still exists. Counted explicitly so the two questions
/// never collapse. Evidence: structural (2).
pub const E5_PRESERVED_DISPATCH: &str = "E5-PRESERVED-DISPATCH";

/// Every rule, with its meaning and evidence level.
pub const RULES: &[(&str, u8, &str)] = &[
    (
        W0_CLOSED_WORLD,
        5,
        "the dump is the whole program and Main.main is its only root (assumption)",
    ),
    (
        W1_GLOBAL_CALLERS,
        3,
        "a function's call sites are its occurrences in every module, by stable name",
    ),
    (
        W2_DICT_VALUE,
        2,
        "a dictionary value is a dict-con application, a dfun, or a superclass selection",
    ),
    (
        W3_PARAM_UNION,
        3,
        "a dictionary parameter is the union over all call sites in the closed world",
    ),
    (
        W4_DISPATCH,
        3,
        "dispatch feeds the selected method's own dictionary parameters",
    ),
    (
        W5_MONOVARIANT,
        5,
        "one abstract value per dictionary identity, no calling context",
    ),
    (
        W6_TAINT,
        3,
        "an unaccountable source taints the set and every site downstream",
    ),
    (
        W7_BUDGET,
        2,
        "a walk over budget is Unresolved, never a guess",
    ),
    (
        E0_SEPARATE,
        5,
        "a known method target is NOT a removable dictionary: separate verdicts",
    ),
    (
        E1_TOTAL,
        5,
        "erasure moves no divergence when every producer is a total dictionary value",
    ),
    (
        E2_AGREE,
        3,
        "every producer at a boundary must request the same erased form",
    ),
    (
        E3_CLONE,
        3,
        "disagreeing producers at a never-a-value function cost one clone per instance",
    ),
    (
        E4_ESCAPE,
        3,
        "the dictionary is used as an ordinary value: preserve it, and name the holder",
    ),
    (
        E5_PRESERVED_DISPATCH,
        2,
        "an Exact target on a Preserve dictionary is still a run-time dispatch",
    ),
];

// Taint / unresolved reasons.
pub const T_USED_AS_A_VALUE: &str = "function-used-as-a-value";
pub const T_PARTIAL_CALL: &str = "call-site-is-a-partial-application";
pub const T_NO_CALLERS: &str = "function-has-no-call-site-in-the-closed-world";
/// The function has no occurrence anywhere in the closed world: under
/// [`W0_CLOSED_WORLD`] nothing can name it, so it is dead and the site
/// never runs. A non-answer, but a different one.
pub const T_UNREACHABLE: &str = "function-is-unreachable-in-the-closed-world";
/// The method sits in a dictionary field that no class-op site in the
/// closed world ever selects: the method is never dispatched.
pub const T_NEVER_DISPATCHED: &str = "method-is-never-dispatched-in-the-closed-world";
pub const T_ANON_LAMBDA: &str = "dictionary-parameter-of-an-anonymous-lambda";
pub const T_CON_FIELD: &str = "dictionary-read-from-a-non-dictionary-constructor-field";
pub const T_UNKNOWN_CALL: &str = "dictionary-returned-by-a-call-the-dump-cannot-see";
pub const T_HIGHER_ORDER: &str = "dictionary-from-a-higher-order-parameter";
pub const T_NOT_A_DICT_EXPR: &str = "dictionary-expression-is-not-a-dictionary";
pub const T_DISPATCH_TAINTED: &str = "dispatched-from-a-site-with-an-unknown-dictionary";
pub const T_METHOD_FIELD_PARTIAL: &str = "method-field-is-a-partial-application";
pub const T_RECURSIVE: &str = "recursive-dictionary";
pub const T_CLASS_UNKNOWN: &str = "class-not-in-the-class-table";
pub const T_NO_PRODUCER: &str = "no-producer-reaches-the-parameter";
pub const U_METHOD_NOT_IN_DUMP: &str = "instance-method-not-in-the-dump";
pub const U_NOT_A_CON: &str = "dictionary-is-not-a-constructor-application";
pub const U_TABLE_MISMATCH: &str = "class-table-disagrees-with-the-dump";
pub const B_ROUNDS: &str = "fixpoint-exceeded-the-round-budget";
pub const B_SET: &str = "dictionary-set-exceeded-the-budget";
pub const B_EVAL: &str = "evaluation-exceeded-the-step-budget";
pub const B_NEST: &str = "field-read-exceeded-the-nesting-budget";

/// Fixpoint rounds before every unstable parameter is forced to `Top`.
pub const ROUND_BUDGET: usize = 40;
/// Dictionaries in one abstract set before it collapses to `Top`.
pub const SET_CAP: usize = 32;
/// Expression steps in one evaluation.
pub const EVAL_BUDGET: usize = 4000;
/// Nested dictionary-field reads (superclass chains, field selections).
pub const NEST_CAP: usize = 8;

//------------------------------------------------------------------------------
// The abstract domain
//------------------------------------------------------------------------------

/// What a dictionary expression can be: a finite set of dictionary
/// identities, or `Top` with the reason it could not be bounded.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum DictSet {
    Top(String),
    Set(BTreeSet<String>),
}

impl DictSet {
    pub fn empty() -> DictSet {
        DictSet::Set(BTreeSet::new())
    }
    pub fn one(key: &str) -> DictSet {
        DictSet::Set([key.to_string()].into_iter().collect())
    }
    pub fn is_top(&self) -> bool {
        matches!(self, DictSet::Top(_))
    }
    pub fn reason(&self) -> Option<&str> {
        match self {
            DictSet::Top(r) => Some(r),
            _ => None,
        }
    }
    pub fn keys(&self) -> &BTreeSet<String> {
        match self {
            DictSet::Set(s) => s,
            DictSet::Top(_) => EMPTY.get_or_init(BTreeSet::new),
        }
    }
    /// Monotone join. Two `Top`s keep the lexicographically smaller
    /// reason, so a round's result never depends on visit order.
    pub fn join(&mut self, other: &DictSet) {
        let joined = match (&*self, other) {
            (DictSet::Top(a), DictSet::Top(b)) => DictSet::Top(a.min(b).clone()),
            (DictSet::Top(a), _) => DictSet::Top(a.clone()),
            (_, DictSet::Top(b)) => DictSet::Top(b.clone()),
            (DictSet::Set(a), DictSet::Set(b)) => {
                let u: BTreeSet<String> = a.union(b).cloned().collect();
                if u.len() > SET_CAP {
                    DictSet::Top(B_SET.into())
                } else {
                    DictSet::Set(u)
                }
            }
        };
        *self = joined;
    }
}

static EMPTY: std::sync::OnceLock<BTreeSet<String>> = std::sync::OnceLock::new();

/// One dictionary identity in the closed world.
#[derive(Debug, Clone, Serialize)]
pub struct DictVal {
    /// The identity of this dictionary. `Module#node` of the constructor
    /// application for every dictionary built in the dump, and the stable
    /// name for an imported dfun. **Not** the binding's name: a top-level
    /// binder that GHC has not externalised has an *internal* name
    /// (`$_sys$$fTraversableInnerToken`), and three distinct bindings in
    /// `ShellCheck.AST` share that one. Nothing here keys by it.
    pub key: String,
    /// The binding's name, for the report only.
    pub name: String,
    #[serde(skip)]
    pub binder: Option<BinderId>,
    pub module: String,
    /// The dictionary-constructor application, when it is in the dump.
    pub node: ExprId,
    #[serde(skip)]
    pub mi: usize,
    /// The dfun's binding is not in the dump: the instance is named, its
    /// method bodies are not readable.
    pub imported: bool,
    /// The class, when the table knows it.
    pub class: Option<String>,
    /// Dictionary parameters of the dfun that builds it, if any.
    #[serde(skip)]
    pub params: Vec<BinderId>,
}

//------------------------------------------------------------------------------
// The program
//------------------------------------------------------------------------------

/// The closed world, indexed for whole-program questions. Built
/// independently of [`crate::classops::World`] — the producer sets here
/// are enumerated from the IR's own occurrences, not from that walk.
pub struct Program<'m> {
    pub modules: Vec<&'m Module>,
    scopes: Vec<Scope<'m>>,
    /// Stable name → the top-level binding that defines it.
    tops: HashMap<String, (usize, BinderId, ExprId)>,
    /// Stable name → every *global* `Var` occurrence of it, anywhere.
    gvars: HashMap<String, Vec<(usize, ExprId)>>,
    lam_of: Vec<HashMap<BinderId, ExprId>>,
    top_of_rhs: Vec<HashMap<ExprId, BinderId>>,
    case_scrut: Vec<HashMap<BinderId, ExprId>>,
    alt_field: Vec<HashMap<BinderId, (ExprId, &'static ClassSpec, usize)>>,
    /// A dictionary-constructor application node → its dictionary key.
    con_key: Vec<HashMap<ExprId, String>>,
    /// Every dictionary identity, by key.
    pub values: BTreeMap<String, DictVal>,
}

impl<'m> Program<'m> {
    pub fn new(modules: impl IntoIterator<Item = &'m Module>) -> Program<'m> {
        let modules: Vec<&Module> = modules.into_iter().collect();
        let n = modules.len();
        let scopes: Vec<Scope> = modules.iter().map(|m| Scope::new(m)).collect();
        let mut p = Program {
            modules,
            scopes,
            tops: HashMap::new(),
            gvars: HashMap::new(),
            lam_of: vec![HashMap::new(); n],
            top_of_rhs: vec![HashMap::new(); n],
            case_scrut: vec![HashMap::new(); n],
            alt_field: vec![HashMap::new(); n],
            con_key: vec![HashMap::new(); n],
            values: BTreeMap::new(),
        };
        p.index();
        p
    }

    fn m(&self, mi: usize) -> &'m Module {
        self.modules[mi]
    }
    fn s(&self, mi: usize) -> &Scope<'m> {
        &self.scopes[mi]
    }

    fn index(&mut self) {
        for mi in 0..self.modules.len() {
            let m = self.m(mi);
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    // Only an *external* name can be referred to from
                    // another module, and only an external name is
                    // unique: keep the rest out of the linkage table.
                    if is_external_name(&b.name) {
                        self.tops
                            .entry(b.name.clone())
                            .or_insert((mi, pair.binder, pair.rhs));
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
                            let Some(spec) = dict_con_spec(name) else {
                                continue;
                            };
                            if alt.binders.len() != spec.fields() {
                                continue;
                            }
                            for (i, &bid) in alt.binders.iter().enumerate() {
                                self.alt_field[mi].insert(bid, (*scrut, spec, i));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        // Dictionary identities. A top-level dictionary binding claims the
        // constructor application its right-hand side reduces to; every
        // other saturated dictionary-constructor application gets an
        // identity of its own.
        for mi in 0..self.modules.len() {
            let m = self.m(mi);
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    let class = class_ty(m.binder_ty(pair.binder).fun_result());
                    if class.is_none() && !is_dictionary_name(&b.occ) {
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
                        DictVal {
                            key,
                            name: b.name.clone(),
                            binder: Some(pair.binder),
                            module: m.name.clone(),
                            node: body,
                            mi,
                            imported: false,
                            class,
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
                let (head, _) = m.spine(id);
                let class = match m.expr(head) {
                    Expr::Var { name, .. } => dict_con_spec(name).map(|c| c.class.to_string()),
                    _ => None,
                };
                self.values.insert(
                    key.clone(),
                    DictVal {
                        key,
                        name: String::new(),
                        binder: None,
                        module: m.name.clone(),
                        node: id,
                        mi,
                        imported: false,
                        class,
                        params: Vec::new(),
                    },
                );
            }
        }
        // Imported dictionaries: a global with a dictionary name and no
        // binding in the dump.
        let mut imported: Vec<(String, usize, ExprId)> = Vec::new();
        for (name, occs) in &self.gvars {
            if self.tops.contains_key(name) {
                continue;
            }
            let Some((_, _, occ)) = split_stable_name(name) else {
                continue;
            };
            // `$f<Class><Type>` is a dfun; `$f<Class><Type>_$c<method>` is
            // one of its *methods*, and `_$s…` a specialisation of one.
            // Neither is a dictionary.
            if !occ.starts_with("$f")
                || !is_dictionary_name(occ)
                || occ.contains("_$c")
                || occ.contains("_$s")
            {
                continue;
            }
            let (mi, node) = occs[0];
            imported.push((name.clone(), mi, node));
        }
        for (name, mi, node) in imported {
            let module = split_stable_name(&name)
                .map(|(_, md, _)| md.to_string())
                .unwrap_or_default();
            self.values.insert(
                name.clone(),
                DictVal {
                    key: name.clone(),
                    name,
                    binder: None,
                    module,
                    node,
                    mi,
                    imported: true,
                    class: None,
                    params: Vec::new(),
                },
            );
        }
    }

    /// Strip the manifest lambda chain (and casts/ticks) from a body.
    fn strip_lams(&self, mi: usize, rhs: ExprId) -> ExprId {
        let m = self.m(mi);
        let mut cur = m.strip(rhs);
        while let Expr::Lam { body, .. } = m.expr(cur) {
            cur = m.strip(*body);
        }
        cur
    }

    /// Strip leading *type* lambdas only: `\@a -> d` is the dictionary
    /// `d` at every type it is instantiated at, and the analysis carries no
    /// types, so a type application is transparent here.
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

    fn is_dict_con_app(&self, mi: usize, node: ExprId) -> bool {
        let m = self.m(mi);
        let (head, args) = m.spine(node);
        let Expr::Var { name, .. } = m.expr(head) else {
            return false;
        };
        let Some(spec) = dict_con_spec(name) else {
            return false;
        };
        let Some(dc) = self.s(mi).head_sig(head).and_then(|x| x.data_con) else {
            return false;
        };
        dc.rep_arity as usize == spec.fields()
            && value_args(self.s(mi), &args).len() >= spec.fields()
    }

    /// Every occurrence of a top-level binding, in every module of the
    /// closed world ([`W1_GLOBAL_CALLERS`]): the local ones through the
    /// module's own binder, the rest by stable name.
    fn all_occurrences(&self, mi: usize, b: BinderId) -> Vec<(usize, ExprId)> {
        let m = self.m(mi);
        let mut out: Vec<(usize, ExprId)> = m.occurrences(b).iter().map(|&o| (mi, o)).collect();
        if m.binding(b).site == BindSite::Top
            && is_external_name(&m.binder(b).name)
            && let Some(g) = self.gvars.get(&m.binder(b).name)
        {
            out.extend(g.iter().copied());
        }
        out
    }
}

/// Is this an *external* name — one another module could refer to, and
/// one that is unique in the program? GHC gives a top-level binder it has
/// not externalised an internal name (`$_in$…`, `$_sys$…`), and those are
/// **not** unique: `ShellCheck.AST` has three distinct top-level bindings
/// whose name is `$_sys$$fTraversableInnerToken`. Nothing here is keyed by
/// one.
pub(crate) fn is_external_name(name: &str) -> bool {
    split_stable_name(name).is_some_and(|(u, md, _)| !u.is_empty() && !md.is_empty())
}

/// The class whose dictionary constructor this stable name is.
fn dict_con_spec(name: &str) -> Option<&'static ClassSpec> {
    let (_, module, occ) = split_stable_name(name)?;
    let class = occ.strip_prefix("C:")?;
    CLASSES
        .iter()
        .find(|c| c.class == class && c.module == module)
}

//------------------------------------------------------------------------------
// Parameters and producers
//------------------------------------------------------------------------------

/// A dictionary parameter: one node of the fixpoint.
#[derive(Debug, Clone, Serialize)]
pub struct Param {
    pub module: String,
    #[serde(skip)]
    pub mi: usize,
    #[serde(skip)]
    pub binder: BinderId,
    pub occ: String,
    /// The function the parameter belongs to, and its index among that
    /// function's manifest value parameters.
    pub owner: String,
    pub index: usize,
    pub exported: bool,
    /// The class, when the type gives it.
    pub class: Option<String>,
    /// GHC records the parameter as strict at its binder.
    pub known_strict: bool,
    /// Where the values that reach it come from.
    #[serde(skip)]
    pub producers: Producers,
    /// The fixpoint's answer.
    pub set: DictSet,
}

/// A method sitting at field `field` of the dictionary `dict`: its callers
/// are the class-op sites that select that field.
#[derive(Debug, Clone)]
pub struct DispatchSlot {
    pub dict: String,
    pub class: &'static str,
    pub field: usize,
    /// Which of the site's value arguments feeds this parameter: the
    /// dictionary is argument 0, so parameter `i` is argument `i + 1`.
    pub arg_index: usize,
}

#[derive(Debug, Clone, Default)]
pub struct Producers {
    /// A producer the closed world cannot account for.
    pub top: Option<String>,
    /// Direct call sites: the actual argument at each.
    pub calls: Vec<(usize, ExprId)>,
    /// Dispatch slots: the parameter is fed by whichever site selects it.
    pub slots: Vec<DispatchSlot>,
}

//------------------------------------------------------------------------------
// Sites
//------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct MethodTarget {
    pub module: String,
    pub occ: String,
    pub name: String,
    pub node: ExprId,
}

#[derive(Debug, Clone, Serialize)]
pub enum Outcome {
    Exact(MethodTarget),
    FiniteSet(Vec<MethodTarget>),
    Unresolved(String),
}

impl Outcome {
    pub fn label(&self) -> &'static str {
        match self {
            Outcome::Exact(_) => "Exact",
            Outcome::FiniteSet(_) => "FiniteSet",
            Outcome::Unresolved(_) => "Unresolved",
        }
    }
    fn row(&self) -> usize {
        match self {
            Outcome::Exact(_) => 0,
            Outcome::FiniteSet(_) => 1,
            Outcome::Unresolved(_) => 2,
        }
    }
}

/// One class-op application site, re-derived whole-program.
#[derive(Debug, Clone, Serialize)]
pub struct Site {
    pub module: String,
    #[serde(skip)]
    pub mi: usize,
    pub node: ExprId,
    pub selector: String,
    pub method: String,
    pub class: String,
    #[serde(skip)]
    pub spec: Option<&'static ClassSpec>,
    pub field: Option<usize>,
    #[serde(skip)]
    pub dict: Option<ExprId>,
    /// The site's value arguments after the dictionary.
    #[serde(skip)]
    pub rest: Vec<ExprId>,
    pub set: DictSet,
    pub outcome: Outcome,
    /// The erasure verdict of the dictionary this site dispatches on.
    pub dict_verdict: Verdict,
}

//------------------------------------------------------------------------------
// Erasure
//------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Verdict {
    Erasable,
    /// One specialised clone per instance; the count is the number of
    /// instances, never made, only counted.
    ErasableWithClone(usize),
    /// The dictionary must stay: the holder is named.
    Preserve(String),
    Unresolved(String),
}

impl Verdict {
    pub fn label(&self) -> &'static str {
        match self {
            Verdict::Erasable => "Erasable",
            Verdict::ErasableWithClone(_) => "ErasableWithClone",
            Verdict::Preserve(_) => "Preserve",
            Verdict::Unresolved(_) => "Unresolved",
        }
    }
    fn col(&self) -> usize {
        match self {
            Verdict::Erasable => 0,
            Verdict::ErasableWithClone(_) => 1,
            Verdict::Preserve(_) => 2,
            Verdict::Unresolved(_) => 3,
        }
    }
}

/// The erasure verdict of one dictionary value or parameter, with the
/// facts it was computed from — recorded separately from Part 1.
#[derive(Debug, Clone, Serialize)]
pub struct Erasure {
    pub what: String,
    pub module: String,
    /// `value` or `parameter`.
    pub kind: &'static str,
    /// Every producer is a total dictionary value ([`E1_TOTAL`]).
    pub producers_total: bool,
    /// GHC already forces it at entry, so erasure moves no divergence.
    pub known_strict: bool,
    /// The instances that must agree at this boundary.
    pub instances: usize,
    /// It is used somewhere as an ordinary value ([`E4_ESCAPE`]).
    pub escapes: Option<String>,
    pub verdict: Verdict,
}

//------------------------------------------------------------------------------
// The analysis
//------------------------------------------------------------------------------

#[derive(Debug, Default, Serialize)]
pub struct Accounting {
    pub sites: usize,
    pub exact: usize,
    pub finite: usize,
    pub unresolved: usize,
    pub rounds: usize,
    pub round_budget_hit: bool,
    pub params: usize,
    pub values: usize,
    /// Sites whose *dictionary* set the fixpoint bounded, whatever became
    /// of the method target: the instance is known even where the method
    /// body is not in the dump.
    pub dict_known: usize,
    /// Sites whose dictionary set is bounded, by its size.
    pub instances: BTreeMap<usize, usize>,
    /// Parameters whose set the fixpoint bounded.
    pub params_bounded: usize,
    /// class → (sites, exact, finite, unresolved)
    pub by_class: BTreeMap<String, (usize, usize, usize, usize)>,
    pub reasons: BTreeMap<String, usize>,
    /// Taint sources, by reason, over the parameters.
    pub taints: BTreeMap<String, usize>,
    /// value verdict counts, in [`Verdict`] order.
    pub value_verdicts: [usize; 4],
    pub param_verdicts: [usize; 4],
    pub value_clones: usize,
    pub param_clones: usize,
    /// (target outcome) × (dictionary verdict).
    pub matrix: [[usize; 4]; 3],
    pub erasure_reasons: BTreeMap<String, usize>,
}

impl Accounting {
    /// values = Erasable + WithClone + Preserve + Unresolved; parameters
    /// likewise; sites = the 3×4 matrix; and the outcome partition.
    pub fn check(&self) -> Result<(), String> {
        if self.exact + self.finite + self.unresolved != self.sites {
            return Err(format!(
                "sites {} != {} + {} + {}",
                self.sites, self.exact, self.finite, self.unresolved
            ));
        }
        if self.value_verdicts.iter().sum::<usize>() != self.values {
            return Err(format!(
                "values {} != {:?}",
                self.values, self.value_verdicts
            ));
        }
        if self.param_verdicts.iter().sum::<usize>() != self.params {
            return Err(format!(
                "parameters {} != {:?}",
                self.params, self.param_verdicts
            ));
        }
        let m: usize = self.matrix.iter().flatten().sum();
        if m != self.sites {
            return Err(format!("matrix {m} != sites {}", self.sites));
        }
        Ok(())
    }

    pub fn preserved_dispatch(&self) -> usize {
        self.matrix[0][2] + self.matrix[1][2]
    }
}

/// The whole-program dictionary flow: the fixpoint, the re-derived site
/// outcomes, and — separately — the erasure verdicts.
pub struct DictFlow {
    pub sites: Vec<Site>,
    pub params: Vec<Param>,
    pub values: Vec<Erasure>,
    pub param_erasure: Vec<Erasure>,
    pub rounds: usize,
    pub round_budget_hit: bool,
}

/// The fixpoint state: one set per parameter.
type State = HashMap<(usize, BinderId), DictSet>;

/// `(dictionary, field)` → the class-op sites that select it, each with
/// the module it sits in and the value arguments it supplies after the
/// dictionary.
type DispatchIndex<'a> = HashMap<(&'a str, usize), Vec<(usize, &'a Vec<ExprId>)>>;

impl DictFlow {
    pub fn of_modules<'a>(modules: impl IntoIterator<Item = &'a Module>) -> DictFlow {
        let p = Program::new(modules);
        Self::of_program(&p)
    }

    pub fn of_program(p: &Program) -> DictFlow {
        let mut params = collect_params(p);
        let mut sites = collect_sites(p);
        let mut state: State = params
            .iter()
            .map(|x| ((x.mi, x.binder), DictSet::empty()))
            .collect();

        let mut rounds = 0usize;
        let mut hit = false;
        loop {
            rounds += 1;
            // Every site's dictionary set, under the current state.
            let sets: Vec<DictSet> = sites
                .iter()
                .map(|s| match s.dict {
                    Some(d) => eval(p, &state, s.mi, d),
                    None => DictSet::Top(T_NOT_A_DICT_EXPR.into()),
                })
                .collect();
            // The dispatch index: which site arguments reach which field
            // of which dictionary, and which (class, field) is tainted.
            let mut dispatch: DispatchIndex = HashMap::new();
            let mut tainted: HashSet<(&str, usize)> = HashSet::new();
            for (s, set) in sites.iter().zip(&sets) {
                let (Some(spec), Some(field)) = (s.spec, s.field) else {
                    continue;
                };
                match set {
                    DictSet::Top(_) => {
                        tainted.insert((spec.class, field));
                    }
                    DictSet::Set(keys) => {
                        for k in keys {
                            dispatch
                                .entry((k.as_str(), field))
                                .or_default()
                                .push((s.mi, &s.rest));
                        }
                    }
                }
            }

            let mut changed = false;
            let mut next = state.clone();
            for x in &params {
                let mut acc = DictSet::empty();
                if let Some(r) = &x.producers.top {
                    acc.join(&DictSet::Top(r.clone()));
                }
                for &(cmi, arg) in &x.producers.calls {
                    let v = eval(p, &state, cmi, arg);
                    acc.join(&v);
                }
                for slot in &x.producers.slots {
                    if tainted.contains(&(slot.class, slot.field)) {
                        acc.join(&DictSet::Top(T_DISPATCH_TAINTED.into()));
                        continue;
                    }
                    let Some(callers) = dispatch.get(&(slot.dict.as_str(), slot.field)) else {
                        continue;
                    };
                    for (cmi, rest) in callers {
                        match rest.get(slot.arg_index.wrapping_sub(1)) {
                            Some(&a) => {
                                let v = eval(p, &state, *cmi, a);
                                acc.join(&v);
                            }
                            None => acc.join(&DictSet::Top(T_PARTIAL_CALL.into())),
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
            if rounds >= ROUND_BUDGET {
                hit = true;
                for v in state.values_mut() {
                    if !v.is_top() {
                        v.join(&DictSet::Top(B_ROUNDS.into()));
                    }
                }
                break;
            }
        }

        for x in &mut params {
            x.set = state[&(x.mi, x.binder)].clone();
            if let DictSet::Set(s) = &x.set
                && s.is_empty()
            {
                x.set = DictSet::Top(if x.producers.slots.is_empty() {
                    T_NO_PRODUCER.to_string()
                } else {
                    T_NEVER_DISPATCHED.to_string()
                });
            }
        }
        // `params` now holds the fixpoint; re-read state from it so the
        // site evaluation below sees the settled sets.
        let state: State = params
            .iter()
            .map(|x| ((x.mi, x.binder), x.set.clone()))
            .collect();
        for s in &mut sites {
            s.set = match s.dict {
                Some(d) => eval(p, &state, s.mi, d),
                None => DictSet::Top(T_NOT_A_DICT_EXPR.into()),
            };
            s.outcome = outcome_of(p, s);
        }

        // Part 2, from facts recorded separately.
        let (values, param_erasure) = erasure(p, &params, &sites);
        let pv: HashMap<(usize, BinderId), Verdict> = params
            .iter()
            .zip(&param_erasure)
            .map(|(x, e)| ((x.mi, x.binder), e.verdict.clone()))
            .collect();
        let vv: HashMap<&str, &Verdict> = values
            .iter()
            .map(|e| (e.what.as_str(), &e.verdict))
            .collect();
        for s in &mut sites {
            s.dict_verdict = site_dict_verdict(p, s, &pv, &vv);
        }

        DictFlow {
            sites,
            params,
            values,
            param_erasure,
            rounds,
            round_budget_hit: hit,
        }
    }

    pub fn accounting(&self) -> Accounting {
        let mut a = Accounting {
            sites: self.sites.len(),
            params: self.params.len(),
            values: self.values.len(),
            rounds: self.rounds,
            round_budget_hit: self.round_budget_hit,
            ..Default::default()
        };
        for s in &self.sites {
            let class = if s.class.is_empty() {
                "?".to_string()
            } else {
                s.class.clone()
            };
            let row = a.by_class.entry(class).or_default();
            row.0 += 1;
            match &s.outcome {
                Outcome::Exact(_) => {
                    a.exact += 1;
                    row.1 += 1;
                }
                Outcome::FiniteSet(_) => {
                    a.finite += 1;
                    row.2 += 1;
                }
                Outcome::Unresolved(r) => {
                    a.unresolved += 1;
                    row.3 += 1;
                    *a.reasons.entry(reason_head(r)).or_default() += 1;
                }
            }
            a.matrix[s.outcome.row()][s.dict_verdict.col()] += 1;
            if let DictSet::Set(k) = &s.set
                && !k.is_empty()
            {
                a.dict_known += 1;
                *a.instances.entry(k.len()).or_default() += 1;
            }
        }
        for x in &self.params {
            if !x.set.is_top() {
                a.params_bounded += 1;
            }
            if let DictSet::Top(r) = &x.set {
                *a.taints.entry(reason_head(r)).or_default() += 1;
            }
        }
        for (list, counts, clones) in [
            (&self.values, &mut a.value_verdicts, &mut a.value_clones),
            (
                &self.param_erasure,
                &mut a.param_verdicts,
                &mut a.param_clones,
            ),
        ] {
            for e in list {
                counts[e.verdict.col()] += 1;
                match &e.verdict {
                    Verdict::ErasableWithClone(n) => *clones += n,
                    Verdict::Preserve(r) | Verdict::Unresolved(r) => {
                        *a.erasure_reasons.entry(reason_head(r)).or_default() += 1;
                    }
                    Verdict::Erasable => {}
                }
            }
        }
        a
    }
}

/// The kind of a reason, for grouping: everything before a `;` and before
/// a parenthesised witness, which names a node and so is never the group.
fn reason_head(r: &str) -> String {
    let r = r.split(';').next().unwrap_or(r);
    r.split(" (").next().unwrap_or(r).trim().to_string()
}

//------------------------------------------------------------------------------
// Collecting the fixpoint's nodes
//------------------------------------------------------------------------------

fn is_dict_binder(m: &Module, b: BinderId) -> Option<Option<String>> {
    let binder = m.binder(b);
    if binder.kind == BinderKind::Tyvar {
        return None;
    }
    let class = class_ty(m.binder_ty(b));
    if class.is_none() && !binder.occ.starts_with("$d") {
        return None;
    }
    Some(class)
}

fn collect_params(p: &Program) -> Vec<Param> {
    let mut out = Vec::new();
    for mi in 0..p.modules.len() {
        let m = p.m(mi);
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Lam { binder, .. } = m.expr(id) else {
                continue;
            };
            let Some(class) = is_dict_binder(m, *binder) else {
                continue;
            };
            let b = *binder;
            let (owner, index) = owner_of(p, mi, b);
            let (owner_name, exported) = match owner {
                Some(f) => (
                    m.binder(f).occ.clone(),
                    m.binding(f).site == BindSite::Top && m.binder(f).exported == Some(true),
                ),
                None => (String::new(), false),
            };
            out.push(Param {
                module: m.name.clone(),
                mi,
                binder: b,
                occ: m.binder(b).occ.clone(),
                owner: owner_name,
                index,
                exported,
                class,
                known_strict: m.binder(b).demand.as_ref().is_some_and(|d| d.strict),
                producers: producers_of(p, mi, owner, index),
                set: DictSet::empty(),
            });
        }
    }
    out
}

/// The named function a lambda binder belongs to, and the binder's index
/// among that function's manifest value parameters.
fn owner_of(p: &Program, mi: usize, b: BinderId) -> (Option<BinderId>, usize) {
    let m = p.m(mi);
    let Some(&lam) = p.lam_of[mi].get(&b) else {
        return (None, 0);
    };
    let mut idx = 0usize;
    let mut cur = lam;
    loop {
        let Some(parent) = m.parent[cur as usize] else {
            return (p.top_of_rhs[mi].get(&cur).copied(), idx);
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
            Edge::Top { .. } => return (p.top_of_rhs[mi].get(&cur).copied(), idx),
            _ => return (None, idx),
        }
    }
}

/// Enumerate, over the whole closed world, what produces the `index`th
/// value argument of `owner`.
fn producers_of(p: &Program, mi: usize, owner: Option<BinderId>, index: usize) -> Producers {
    let mut out = Producers::default();
    let Some(f) = owner else {
        out.top = Some(T_ANON_LAMBDA.into());
        return out;
    };
    let m = p.m(mi);
    let occs = p.all_occurrences(mi, f);
    if occs.is_empty() {
        out.top = Some(if m.binding(f).site == BindSite::Top {
            T_UNREACHABLE.into()
        } else {
            T_NO_CALLERS.to_string()
        });
        return out;
    }
    for (omi, o) in occs {
        let om = p.m(omi);
        let root = om.spine_root(o);
        let (head, args) = om.spine(root);
        let vargs = value_args(p.s(omi), &args);
        if root != o && om.strip(head) == om.strip(o) {
            match vargs.get(index) {
                Some(&a) => out.calls.push((omi, a)),
                None => out.top = Some(T_PARTIAL_CALL.into()),
            }
            continue;
        }
        // Not a call. The one use that is still enumerable is a method
        // field of a dictionary: its callers are the dispatch sites.
        match method_slot(p, omi, o, index) {
            Some(slot) => out.slots.push(slot),
            None => {
                out.top = Some(T_USED_AS_A_VALUE.into());
                return out;
            }
        }
    }
    out
}

/// Is this occurrence a method field of a dictionary-constructor
/// application? Then the parameter at `index` is fed by whichever class-op
/// site selects that field.
fn method_slot(p: &Program, mi: usize, occ: ExprId, index: usize) -> Option<DispatchSlot> {
    let m = p.m(mi);
    let mut cur = occ;
    while let Some(parent) = m.parent[cur as usize] {
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => cur = parent,
            Edge::AppArg => {
                let root = m.spine_root(parent);
                let key = p.con_key[mi].get(&root)?;
                let (head, args) = m.spine(root);
                let Expr::Var { name, .. } = m.expr(head) else {
                    return None;
                };
                let spec = dict_con_spec(name)?;
                let vargs = value_args(p.s(mi), &args);
                let field = vargs.iter().position(|&a| m.strip(a) == m.strip(cur))?;
                // Only a *bare* field is positionally comparable to the
                // site's arguments; a partial application shifts them.
                if m.strip(vargs[field]) != m.strip(occ) {
                    return None;
                }
                return Some(DispatchSlot {
                    dict: key.clone(),
                    class: spec.class,
                    field,
                    arg_index: index + 1,
                });
            }
            _ => return None,
        }
    }
    None
}

fn collect_sites(p: &Program) -> Vec<Site> {
    let mut out = Vec::new();
    for mi in 0..p.modules.len() {
        let m = p.m(mi);
        let s = p.s(mi);
        for id in 0..m.exprs.len() as ExprId {
            let is_app = matches!(m.expr(id), Expr::App { .. });
            let is_var = matches!(m.expr(id), Expr::Var { .. });
            if (!is_app && !is_var) || m.spine_root(id) != id {
                continue;
            }
            let (head, args) = if is_app { m.spine(id) } else { (id, vec![]) };
            if !s.head_sig(head).is_some_and(|x| x.is_class_op) {
                continue;
            }
            let Expr::Var { name, occ, .. } = m.expr(head) else {
                continue;
            };
            let (_, sel_module, _) = split_stable_name(name).unwrap_or(("", "", ""));
            let spec = selector_class(sel_module, occ);
            let vargs = value_args(s, &args);
            out.push(Site {
                module: m.name.clone(),
                mi,
                node: id,
                selector: name.clone(),
                method: occ.clone(),
                class: spec
                    .map(|(c, _, _)| c.class.to_string())
                    .unwrap_or_default(),
                spec: spec.map(|(c, _, _)| c),
                field: spec.map(|(_, f, _)| f),
                dict: vargs.first().copied(),
                rest: vargs.iter().skip(1).copied().collect(),
                set: DictSet::empty(),
                outcome: Outcome::Unresolved(String::new()),
                dict_verdict: Verdict::Unresolved(String::new()),
            });
        }
    }
    out
}

//------------------------------------------------------------------------------
// Evaluating a dictionary expression
//------------------------------------------------------------------------------

fn eval(p: &Program, st: &State, mi: usize, node: ExprId) -> DictSet {
    eval_nested(p, st, mi, node, 0)
}

/// A worklist over the expression graph: every successor of a dictionary
/// expression is pushed, never recursed into, except for the bounded
/// nesting a dictionary-*field* read needs ([`NEST_CAP`]).
fn eval_nested(p: &Program, st: &State, mi: usize, node: ExprId, nest: usize) -> DictSet {
    if nest > NEST_CAP {
        return DictSet::Top(B_NEST.into());
    }
    let mut acc = DictSet::empty();
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work = vec![(mi, node)];
    let mut steps = 0usize;
    while let Some((mi, node)) = work.pop() {
        steps += 1;
        if steps > EVAL_BUDGET {
            return DictSet::Top(B_EVAL.into());
        }
        if !seen.insert((mi, node)) {
            continue;
        }
        let m = p.m(mi);
        let s = p.s(mi);
        let inner = m.strip(node);
        let (head, args) = m.spine(inner);
        let vargs = value_args(s, &args);

        match m.expr(head) {
            Expr::Case { alts, .. } => {
                for alt in alts {
                    work.push((mi, alt.rhs));
                }
                continue;
            }
            Expr::Let { body, .. } => {
                work.push((mi, *body));
                continue;
            }
            Expr::Var { .. } => {}
            _ => {
                acc.join(&DictSet::Top(T_NOT_A_DICT_EXPR.into()));
                continue;
            }
        }

        // A dictionary value.
        if let Some(key) = p.con_key[mi].get(&inner) {
            acc.join(&DictSet::one(key));
            continue;
        }

        if let Some(b) = m.resolve(head) {
            let bi = m.binding(b);
            match bi.site {
                BindSite::Lam => match st.get(&(mi, b)) {
                    Some(v) => acc.join(v),
                    None => acc.join(&DictSet::Top(T_HIGHER_ORDER.into())),
                },
                BindSite::Let | BindSite::Top => match bi.rhs {
                    Some(rhs) if vargs.is_empty() => work.push((mi, p.strip_ty_lams(mi, rhs))),
                    Some(rhs) => work.push((mi, p.strip_lams(mi, rhs))),
                    None => acc.join(&DictSet::Top(T_NOT_A_DICT_EXPR.into())),
                },
                BindSite::CaseBinder => match p.case_scrut[mi].get(&b) {
                    Some(&scrut) => work.push((mi, scrut)),
                    None => acc.join(&DictSet::Top(T_CON_FIELD.into())),
                },
                BindSite::AltBinder => match p.alt_field[mi].get(&b) {
                    Some(&(scrut, spec, i)) => {
                        acc.join(&read_field(p, st, mi, scrut, spec, i, nest));
                    }
                    None => acc.join(&DictSet::Top(T_CON_FIELD.into())),
                },
            }
            continue;
        }

        // A global.
        let Expr::Var { name, occ, .. } = m.expr(head) else {
            unreachable!()
        };
        if occ.starts_with("$p")
            && let Some(&d) = vargs.first()
        {
            let (_, gm, _) = split_stable_name(name).unwrap_or(("", "", ""));
            match selector_class(gm, occ) {
                Some((spec, field, _)) => {
                    acc.join(&read_field(p, st, mi, d, spec, field, nest));
                }
                None => acc.join(&DictSet::Top(format!("{T_CLASS_UNKNOWN}({gm}.{occ})"))),
            }
            continue;
        }
        if let Some(&(wi, _, rhs)) = p.tops.get(name) {
            if vargs.is_empty() {
                work.push((wi, p.strip_ty_lams(wi, rhs)));
            } else {
                work.push((wi, p.strip_lams(wi, rhs)));
            }
            continue;
        }
        if p.values.contains_key(name) {
            acc.join(&DictSet::one(name));
            continue;
        }
        acc.join(&DictSet::Top(T_UNKNOWN_CALL.into()));
    }
    acc
}

/// Field `field` of whatever the expression at `node` evaluates to.
fn read_field(
    p: &Program,
    st: &State,
    mi: usize,
    node: ExprId,
    spec: &'static ClassSpec,
    field: usize,
    nest: usize,
) -> DictSet {
    let base = eval_nested(p, st, mi, node, nest + 1);
    let keys = match &base {
        DictSet::Top(_) => return base,
        DictSet::Set(k) => k.clone(),
    };
    let mut acc = DictSet::empty();
    for k in &keys {
        match field_expr(p, k, spec, field) {
            Ok((fmi, fnode)) => acc.join(&eval_nested(p, st, fmi, fnode, nest + 1)),
            Err(e) => acc.join(&DictSet::Top(e)),
        }
    }
    acc
}

/// The expression sitting at field `field` of a dictionary, in its module.
fn field_expr(
    p: &Program,
    key: &str,
    spec: &'static ClassSpec,
    field: usize,
) -> Result<(usize, ExprId), String> {
    let Some(v) = p.values.get(key) else {
        return Err(T_NOT_A_DICT_EXPR.into());
    };
    if v.imported {
        return Err(format!(
            "{U_METHOD_NOT_IN_DUMP}({})",
            split_stable_name(&v.key)
                .map(|(_, _, o)| o.to_string())
                .unwrap_or_else(|| v.key.clone())
        ));
    }
    let m = p.m(v.mi);
    let (head, args) = m.spine(v.node);
    let Some(dc) = p.s(v.mi).head_sig(head).and_then(|x| x.data_con) else {
        return Err(U_NOT_A_CON.into());
    };
    if dc.rep_arity as usize != spec.fields() {
        return Err(format!(
            "{U_TABLE_MISMATCH}({} has {} fields, table says {})",
            spec.class,
            dc.rep_arity,
            spec.fields()
        ));
    }
    let vargs = value_args(p.s(v.mi), &args);
    match vargs.get(field) {
        Some(&f) => Ok((v.mi, f)),
        None => Err(U_NOT_A_CON.into()),
    }
}

fn outcome_of(p: &Program, s: &Site) -> Outcome {
    if s.dict.is_none() {
        return Outcome::Unresolved("partially-applied-selector".into());
    }
    let (Some(spec), Some(field)) = (s.spec, s.field) else {
        return Outcome::Unresolved(format!("{T_CLASS_UNKNOWN}({})", s.method));
    };
    let keys = match &s.set {
        DictSet::Top(r) => return Outcome::Unresolved(r.clone()),
        DictSet::Set(k) => k,
    };
    if keys.is_empty() {
        return Outcome::Unresolved(T_NO_PRODUCER.into());
    }
    let mut targets: Vec<MethodTarget> = Vec::new();
    let mut bad: Vec<String> = Vec::new();
    for k in keys {
        match field_expr(p, k, spec, field) {
            Ok((fmi, fnode)) => match target_of(p, fmi, fnode) {
                Some(t) => {
                    if !targets.contains(&t) {
                        targets.push(t)
                    }
                }
                None => bad.push(T_NOT_A_DICT_EXPR.into()),
            },
            Err(e) => bad.push(e),
        }
    }
    if !bad.is_empty() {
        bad.sort();
        bad.dedup();
        return Outcome::Unresolved(bad.join("; "));
    }
    match targets.len() {
        1 => Outcome::Exact(targets.pop().unwrap()),
        _ => Outcome::FiniteSet(targets),
    }
}

fn target_of(p: &Program, mi: usize, node: ExprId) -> Option<MethodTarget> {
    let m = p.m(mi);
    let node = m.strip(node);
    match m.expr(node) {
        Expr::Var { name, occ, .. } => Some(match m.resolve(node) {
            Some(b) => MethodTarget {
                module: m.name.clone(),
                occ: m.binder(b).occ.clone(),
                name: m.binder(b).name.clone(),
                node,
            },
            None => MethodTarget {
                module: split_stable_name(name)
                    .map(|(_, md, _)| md.to_string())
                    .unwrap_or_default(),
                occ: occ.clone(),
                name: name.clone(),
                node,
            },
        }),
        Expr::Lam { .. } | Expr::App { .. } => Some(MethodTarget {
            module: m.name.clone(),
            occ: String::new(),
            name: String::new(),
            node,
        }),
        _ => None,
    }
}

//------------------------------------------------------------------------------
// Part 2 — erasure agreement
//------------------------------------------------------------------------------

/// How a dictionary occurrence is used.
enum Use {
    /// Dispatch, a dictionary argument of a dfun, a dictionary field, or a
    /// `case` that takes the dictionary apart: none of these needs the
    /// dictionary to survive as a value.
    Dictionary,
    /// Used as an ordinary value; the holder.
    Escape(String),
}

fn erasure(p: &Program, params: &[Param], sites: &[Site]) -> (Vec<Erasure>, Vec<Erasure>) {
    let dict_args: HashSet<(usize, ExprId)> = sites
        .iter()
        .filter_map(|s| s.dict.map(|d| (s.mi, p.m(s.mi).strip(d))))
        .collect();
    let mut values = Vec::new();
    for v in p.values.values() {
        let escapes = escape_of_value(p, v, &dict_args);
        let verdict = if let Some(h) = &escapes {
            Verdict::Preserve(h.clone())
        } else if v.imported {
            Verdict::Erasable
        } else {
            // The instance is only determined if the dfun's own dictionary
            // parameters are.
            let unknown = v.params.iter().any(|b| {
                params
                    .iter()
                    .any(|x| x.mi == v.mi && x.binder == *b && x.set.is_top())
            });
            if unknown {
                Verdict::Unresolved("argument-dictionary-unresolved".into())
            } else {
                Verdict::Erasable
            }
        };
        values.push(Erasure {
            what: if v.name.is_empty() || v.name == v.key {
                v.key.clone()
            } else {
                format!("{} ({})", v.name, v.key)
            },
            module: v.module.clone(),
            kind: "value",
            // A saturated dictionary-constructor application is a value.
            producers_total: true,
            known_strict: false,
            instances: 1,
            escapes,
            verdict,
        });
    }

    let mut pe = Vec::new();
    for x in params {
        let escapes = escape_of_param(p, x, &dict_args);
        let instances = x.set.keys().len();
        let total = !x.set.is_top();
        let verdict = if let Some(h) = &escapes {
            Verdict::Preserve(h.clone())
        } else {
            match &x.set {
                DictSet::Top(r) => Verdict::Unresolved(r.clone()),
                DictSet::Set(_) if instances == 1 => Verdict::Erasable,
                DictSet::Set(_) if instances == 0 => Verdict::Unresolved(T_NO_PRODUCER.to_string()),
                // Producers disagree. The function is never used as a
                // value — that is what kept the set finite — so one clone
                // per instance carries the erased representation.
                DictSet::Set(_) => Verdict::ErasableWithClone(instances),
            }
        };
        pe.push(Erasure {
            what: format!("{}.{}#{}", x.owner, x.occ, x.index),
            module: x.module.clone(),
            kind: "parameter",
            producers_total: total,
            known_strict: x.known_strict,
            instances,
            escapes,
            verdict,
        });
    }
    (values, pe)
}

fn escape_of_value(
    p: &Program,
    v: &DictVal,
    dict_args: &HashSet<(usize, ExprId)>,
) -> Option<String> {
    let mut occs: Vec<(usize, ExprId)> = Vec::new();
    if v.imported
        && let Some(g) = p.gvars.get(&v.key)
    {
        occs.extend(g.iter().copied());
    }
    if let Some(b) = v.binder {
        occs.extend(p.all_occurrences(v.mi, b));
    }
    if occs.is_empty() && !v.imported {
        // A dictionary built inline: its one use is where it sits.
        occs.push((v.mi, v.node));
    }
    escape_of(p, &occs, dict_args)
}

fn escape_of_param(p: &Program, x: &Param, dict_args: &HashSet<(usize, ExprId)>) -> Option<String> {
    let occs: Vec<(usize, ExprId)> = p
        .m(x.mi)
        .occurrences(x.binder)
        .iter()
        .map(|&o| (x.mi, o))
        .collect();
    escape_of(p, &occs, dict_args)
}

/// The first of these occurrences that is an ordinary-value use, with the
/// holder that keeps the dictionary alive ([`E4_ESCAPE`]).
fn escape_of(
    p: &Program,
    occs: &[(usize, ExprId)],
    dict_args: &HashSet<(usize, ExprId)>,
) -> Option<String> {
    let mut seen: HashSet<(usize, ExprId)> = HashSet::new();
    let mut work: Vec<(usize, ExprId)> = occs.to_vec();
    let mut steps = 0usize;
    while let Some((mi, o)) = work.pop() {
        steps += 1;
        if steps > EVAL_BUDGET {
            return Some(B_EVAL.into());
        }
        if !seen.insert((mi, o)) {
            continue;
        }
        match classify_use(p, mi, o, dict_args, &mut work) {
            Use::Dictionary => {}
            Use::Escape(h) => return Some(h),
        }
    }
    None
}

fn classify_use(
    p: &Program,
    mi: usize,
    occ: ExprId,
    dict_args: &HashSet<(usize, ExprId)>,
    work: &mut Vec<(usize, ExprId)>,
) -> Use {
    let m = p.m(mi);
    let s = p.s(mi);
    if dict_args.contains(&(mi, m.strip(occ))) {
        return Use::Dictionary;
    }
    let mut cur = occ;
    while let Some(parent) = m.parent[cur as usize] {
        match m.edge[cur as usize] {
            Edge::Cast | Edge::Tick => cur = parent,
            Edge::CaseScrut => return Use::Dictionary,
            Edge::AppArg => {
                let root = m.spine_root(parent);
                let (head, args) = m.spine(root);
                let vargs = value_args(s, &args);
                let pos = vargs.iter().position(|&a| m.strip(a) == m.strip(cur));
                // Dispatch: the dictionary argument of a class-op site.
                if s.head_sig(head).is_some_and(|x| x.is_class_op) {
                    return if pos == Some(0) {
                        Use::Dictionary
                    } else {
                        Use::Escape(format!("a method argument ({} node {root})", m.name))
                    };
                }
                // A field of a dictionary constructor.
                if let Expr::Var { name, .. } = m.expr(head)
                    && dict_con_spec(name).is_some()
                {
                    return Use::Dictionary;
                }
                // A dictionary argument of a callee in the closed world.
                let callee = match m.resolve(head) {
                    Some(b) => Some((mi, b)),
                    None => match m.expr(head) {
                        Expr::Var { name, .. } => p.tops.get(name).map(|&(wi, b, _)| (wi, b)),
                        _ => None,
                    },
                };
                let Some((cmi, cb)) = callee else {
                    return Use::Escape(format!(
                        "passed to a callee outside the dump ({} node {root})",
                        m.name
                    ));
                };
                let cm = p.m(cmi);
                if cm.binding(cb).site == BindSite::Lam {
                    return Use::Escape(format!(
                        "passed to a higher-order parameter ({} node {root})",
                        m.name
                    ));
                }
                let Some(rhs) = cm.binding(cb).rhs else {
                    return Use::Escape(format!(
                        "passed to a callee with no body ({} node {root})",
                        m.name
                    ));
                };
                let params = p.lam_params(cmi, rhs);
                return match pos.and_then(|i| params.get(i)) {
                    Some(&pb) if is_dict_binder(cm, pb).is_some() => Use::Dictionary,
                    _ => Use::Escape(format!(
                        "passed to a non-dictionary parameter ({} node {root})",
                        m.name
                    )),
                };
            }
            Edge::LetRhs { pair } => {
                // Bound to an alias: its own uses decide.
                let Expr::Let { bind, .. } = m.expr(parent) else {
                    return Use::Escape(format!("an unreadable binding ({})", m.name));
                };
                let b = bind.pairs[pair as usize].binder;
                for &o in m.occurrences(b) {
                    work.push((mi, o));
                }
                return Use::Dictionary;
            }
            Edge::Top { .. } => {
                let Some(&b) = p.top_of_rhs[mi].get(&cur) else {
                    return Use::Escape(format!("a top-level right-hand side ({})", m.name));
                };
                for o in p.all_occurrences(mi, b) {
                    work.push(o);
                }
                return Use::Dictionary;
            }
            _ => {
                return Use::Escape(format!(
                    "used as an ordinary value ({} node {parent})",
                    m.name
                ));
            }
        }
    }
    // The occurrence is the whole right-hand side of a top-level
    // binding: an alias, whose own occurrences decide.
    match p.top_of_rhs[mi].get(&cur) {
        Some(&b) => {
            for o in p.all_occurrences(mi, b) {
                work.push(o);
            }
            Use::Dictionary
        }
        None => Use::Escape(format!("a bare right-hand side ({})", m.name)),
    }
}

/// The erasure verdict of the dictionary a site dispatches on: the
/// parameter's when the dictionary argument is one, the value's when it is
/// a single known dictionary, and `Unresolved` otherwise.
fn site_dict_verdict(
    p: &Program,
    s: &Site,
    pv: &HashMap<(usize, BinderId), Verdict>,
    vv: &HashMap<&str, &Verdict>,
) -> Verdict {
    let Some(d) = s.dict else {
        return Verdict::Unresolved("partially-applied-selector".into());
    };
    let m = p.m(s.mi);
    let inner = m.strip(d);
    if let Some(b) = m.resolve(inner)
        && m.binding(b).site == BindSite::Lam
        && let Some(v) = pv.get(&(s.mi, b))
    {
        return v.clone();
    }
    if let DictSet::Set(keys) = &s.set
        && keys.len() == 1
        && let Some(v) = vv.get(keys.iter().next().unwrap().as_str())
    {
        return (*v).clone();
    }
    match &s.set {
        DictSet::Top(r) => Verdict::Unresolved(r.clone()),
        DictSet::Set(_) => Verdict::Unresolved("dictionary-is-not-one-boundary".into()),
    }
}
