//! The closed-world class-op census: which instance and which method can run
//! at each dictionary-dispatch site.
//!
//! This answers **one** question — *which method can run here?* — and
//! deliberately not the next one, *can the dictionary disappear?* A known
//! method target is not a removable dictionary: the dictionary may still be
//! forced, stored, or handed to a callee this dump cannot see. The facts
//! that bear on that ([`EvalFacts`]) are recorded here as observations,
//! with no verdict attached.
//!
//! # The population
//!
//! Every application spine whose head is a class-op selector — GHC's own
//! `isClassOpId`, read through [`crate::scope::Scope::head_sig`], not a
//! name ([`K0_CLASSOP_SITE`]). Superclass selectors (`$p1Ord`) are class
//! ops too, so superclass selection is both a member of the population and
//! a dictionary *source*, and one mechanism handles both.
//!
//! The [residual-laziness census](crate::laziness) counts a subset of these:
//! the sites that receive at least one non-trivial argument in a lazy or
//! unknown position. Every such census site is an argument of exactly one
//! population site, and [`Census::census_map`] asserts it.
//!
//! # What is recovered
//!
//! For each site: the class and method; the dictionary argument; the
//! dictionary's *origin*, followed through lexical aliases, dfun
//! applications, superclass selections, dictionary-constructor fields and
//! the parameters of local functions (the union over their call sites); and
//! the method targets those origins select.
//!
//! # What the dump cannot answer
//!
//! An imported dfun (`$fShowInt`) is a global with no unfolding in the
//! dump: the *instance* is known exactly, the method body is not in the
//! closed world. Such a site is [`Outcome::Unresolved`] with the instance
//! named — never guessed.
//!
//! # The class table
//!
//! One thing is not derivable from the dump: which *field* of a dictionary
//! a selector reads. Class-op selectors are globals, and the dump carries
//! no type and no unfolding for a global, so neither the selector's type
//! (`C a => …`) nor its `case d of C:C … m …` body is available. The field
//! order is therefore asserted, per class, in [`CLASSES`] — a library
//! axiom in the style of [`crate::lists::axioms`] — and every use of it is
//! cross-checked against the dictionary constructor's own `DataConInfo`
//! from the dump ([`K3_CLASS_TABLE`]). A class that is not in the table, or
//! whose entry disagrees with the dump, resolves to nothing.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use h2r_core_ir::{BindSite, Binder, BinderId, Edge, Expr, ExprId, Module, Ty};
use serde::Serialize;

use crate::callee::split_stable_name;
use crate::scope::Scope;
use crate::shape::value_args;

//------------------------------------------------------------------------------
// Rules
//------------------------------------------------------------------------------

/// The head of the application spine is a class-op selector. Evidence:
/// GHC's own `isClassOpId`, carried per global id in the dump (5); the
/// spine is structural (2). The selector's *name* is a diagnostic only.
pub const K0_CLASSOP_SITE: &str = "K0-CLASSOP-SITE";
/// The first value argument of a class-op application is the dictionary: a
/// selector has type `C a => method`, so every value argument but the first
/// belongs to the method. Evidence: structural shape (2).
pub const K1_DICT_ARG: &str = "K1-DICT-ARG";
/// The class is the head `TyCon` of the dictionary argument's type.
/// Evidence: GHC type identity (4) — the structured `Ty`, not a rendering.
/// Available whenever the dictionary is a binder in this module or a
/// top-level binding somewhere in the closed world.
pub const K2_DICT_TYPE: &str = "K2-DICT-TYPE";
/// The method's field index within the dictionary comes from the asserted
/// class table [`CLASSES`], cross-checked against the dictionary
/// constructor's `repArity` in the dump. Evidence: library axiom (5) over
/// GHC's `DataConInfo` (4).
pub const K3_CLASS_TABLE: &str = "K3-CLASS-TABLE";
/// `$pN<Class>` is the Nth superclass selector of `<Class>`: field index
/// N-1. Evidence: GHC's naming convention for superclass selectors (1),
/// cross-checked against the dictionary's own type (4) wherever that type
/// is available.
pub const K4_SUPERCLASS_SEL: &str = "K4-SUPERCLASS-SEL";
/// A dictionary bound by a `let` or a top-level binding is followed to its
/// right-hand side. Evidence: def-use over the IR's lexical resolution (3).
pub const K5_ALIAS: &str = "K5-ALIAS";
/// A global dictionary reference whose top-level binding is somewhere in
/// the closed world is followed to that binding; a dfun applied to
/// argument dictionaries binds its parameters to them one level deep.
/// Evidence: def-use across modules over stable global identity (3).
pub const K6_DFUN: &str = "K6-DFUN";
/// A saturated application of a class's dictionary constructor is a
/// dictionary whose superclass and method fields are its value arguments,
/// in the class table's order. Evidence: structural saturation (2) over
/// `DataConInfo` (4).
pub const K7_DICT_CON: &str = "K7-DICT-CON";
/// A dictionary parameter of a local function receives the union of the
/// dictionaries passed at its call sites. Claimed only when the function
/// cannot be named outside this module (not exported) and *every*
/// occurrence of it is a direct call supplying that parameter. Evidence:
/// def-use (3).
pub const K8_PARAM_UNION: &str = "K8-PARAM-UNION";
/// The method target is the dictionary's field at the method's index.
/// Evidence: structural (2) over [`K3_CLASS_TABLE`] and [`K7_DICT_CON`].
pub const K9_METHOD_FIELD: &str = "K9-METHOD-FIELD";
/// A class-op selector is a strict field selection (`\d -> case d of C:C …
/// m … -> m`), so applying one to a dictionary forces it. Evidence:
/// compiler axiom (5). An observation, not a verdict.
pub const K10_FORCED: &str = "K10-FORCED";
/// The dictionary is used somewhere as an ordinary value — an occurrence
/// that is not the dictionary argument of a class-op site. Evidence:
/// def-use (3). An observation, not a verdict.
pub const K11_DICT_ESCAPES: &str = "K11-DICT-ESCAPES";
/// The selector is applied to no value argument at all: the selector is
/// itself the value. Evidence: structural (2).
pub const K12_PARTIAL: &str = "K12-PARTIAL";

/// Every rule, with its meaning and evidence level.
pub const RULES: &[(&str, u8, &str)] = &[
    (
        K0_CLASSOP_SITE,
        5,
        "the spine head is a class-op selector (GHC isClassOpId)",
    ),
    (
        K1_DICT_ARG,
        2,
        "the first value argument of a class-op application is the dictionary",
    ),
    (
        K2_DICT_TYPE,
        4,
        "the class is the head TyCon of the dictionary's structured type",
    ),
    (
        K3_CLASS_TABLE,
        5,
        "the method's field index from the asserted class table, checked against repArity",
    ),
    (
        K4_SUPERCLASS_SEL,
        1,
        "$pN<Class> selects superclass field N-1 of <Class>",
    ),
    (
        K5_ALIAS,
        3,
        "a let-/top-bound dictionary is followed to its right-hand side",
    ),
    (
        K6_DFUN,
        3,
        "a global dictionary is followed to its binding in the closed world",
    ),
    (
        K7_DICT_CON,
        2,
        "a saturated dictionary-constructor application is a dictionary",
    ),
    (
        K8_PARAM_UNION,
        3,
        "a local function's dictionary parameter is the union over its call sites",
    ),
    (
        K9_METHOD_FIELD,
        2,
        "the method target is the dictionary's field at the method's index",
    ),
    (
        K10_FORCED,
        5,
        "a class-op application forces its dictionary (strict field selection)",
    ),
    (
        K11_DICT_ESCAPES,
        3,
        "the dictionary is also used as an ordinary value",
    ),
    (
        K12_PARTIAL,
        2,
        "the selector is applied to no value argument: the selector is the value",
    ),
];

// Unresolved reasons.
pub const U_IMPORTED_DFUN: &str = "instance-method-not-in-the-dump";
pub const U_EXPORTED_PARAM: &str = "dictionary-parameter-of-an-exported-function";
pub const U_PARAM_NOT_CALLED: &str = "dictionary-parameter-of-a-function-used-as-a-value";
pub const U_PARAM_NO_CALLS: &str = "dictionary-parameter-with-no-visible-call-site";
/// The function is reached only by dispatch: it is a method field of a
/// dictionary, so its callers are the class-op sites that select it — the
/// closed-world dispatch propagation this milestone does not attempt.
pub const U_PARAM_DISPATCH: &str = "dictionary-parameter-reached-only-through-dispatch";
pub const U_ANON_LAMBDA: &str = "dictionary-parameter-of-an-anonymous-lambda";
pub const U_FROM_FIELD: &str = "dictionary-read-from-a-constructor-field";
pub const U_UNKNOWN_CALL: &str = "dictionary-returned-by-an-unknown-call";
pub const U_CLASS_UNKNOWN: &str = "class-not-in-the-class-table";
pub const U_CLASS_MISMATCH: &str = "class-table-disagrees-with-the-dump";
pub const U_METHOD_UNKNOWN: &str = "method-not-in-the-class-table";
pub const U_NOT_A_DICT: &str = "first-value-argument-is-not-a-dictionary";
pub const U_PARTIAL: &str = "partially-applied-selector";
pub const U_RECURSIVE: &str = "recursive-dictionary";
pub const U_BUDGET: &str = "origin-walk-exceeded-the-budget";
pub const U_NOT_A_CON: &str = "dictionary-is-not-a-constructor-application";
pub const U_LOCAL_APPLIED: &str = "locally-bound-dictionary-function-applied";
pub const U_NO_ORIGIN: &str = "no-dictionary-origin";

//------------------------------------------------------------------------------
// The class table
//------------------------------------------------------------------------------

/// One class: where its selectors live, its dictionary constructor, how
/// many superclass fields come first, and its methods in field order.
#[derive(Debug, Clone, Copy)]
pub struct ClassSpec {
    /// Module of the class and of its selectors, as in a stable name.
    pub module: &'static str,
    pub class: &'static str,
    pub con: &'static str,
    pub supers: usize,
    pub methods: &'static [&'static str],
}

impl ClassSpec {
    pub fn fields(&self) -> usize {
        self.supers + self.methods.len()
    }
    pub fn method_index(&self, occ: &str) -> Option<usize> {
        self.methods
            .iter()
            .position(|m| *m == occ)
            .map(|i| self.supers + i)
    }
}

/// The asserted class table. Field order is base-4.18 / GHC 9.6, and every
/// use of an entry is checked against the dictionary constructor's
/// `repArity` in the dump before it is believed.
pub const CLASSES: &[ClassSpec] = &[
    ClassSpec {
        module: "GHC.Base",
        class: "Functor",
        con: "C:Functor",
        supers: 0,
        methods: &["fmap", "<$"],
    },
    ClassSpec {
        module: "GHC.Base",
        class: "Applicative",
        con: "C:Applicative",
        supers: 1,
        methods: &["pure", "<*>", "liftA2", "*>", "<*"],
    },
    ClassSpec {
        module: "GHC.Base",
        class: "Monad",
        con: "C:Monad",
        supers: 1,
        methods: &[">>=", ">>", "return"],
    },
    ClassSpec {
        module: "GHC.Base",
        class: "Semigroup",
        con: "C:Semigroup",
        supers: 0,
        methods: &["<>", "sconcat", "stimes"],
    },
    ClassSpec {
        module: "GHC.Base",
        class: "Monoid",
        con: "C:Monoid",
        supers: 1,
        methods: &["mempty", "mappend", "mconcat"],
    },
    ClassSpec {
        module: "GHC.Classes",
        class: "Eq",
        con: "C:Eq",
        supers: 0,
        methods: &["==", "/="],
    },
    ClassSpec {
        module: "GHC.Classes",
        class: "Ord",
        con: "C:Ord",
        supers: 1,
        methods: &["compare", "<", "<=", ">", ">=", "max", "min"],
    },
    ClassSpec {
        module: "GHC.Show",
        class: "Show",
        con: "C:Show",
        supers: 0,
        methods: &["showsPrec", "show", "showList"],
    },
    ClassSpec {
        module: "GHC.Num",
        class: "Num",
        con: "C:Num",
        supers: 0,
        methods: &["+", "-", "*", "negate", "abs", "signum", "fromInteger"],
    },
    ClassSpec {
        module: "Data.Foldable",
        class: "Foldable",
        con: "C:Foldable",
        supers: 0,
        methods: &[
            "fold", "foldMap", "foldMap'", "foldr", "foldr'", "foldl", "foldl'", "foldr1",
            "foldl1", "toList", "null", "length", "elem", "maximum", "minimum", "sum", "product",
        ],
    },
    ClassSpec {
        module: "Data.Traversable",
        class: "Traversable",
        con: "C:Traversable",
        supers: 2,
        methods: &["traverse", "sequenceA", "mapM", "sequence"],
    },
    ClassSpec {
        module: "GHC.Exception.Type",
        class: "Exception",
        con: "C:Exception",
        supers: 2,
        methods: &["toException", "fromException", "displayException"],
    },
    ClassSpec {
        module: "Control.Monad.IO.Class",
        class: "MonadIO",
        con: "C:MonadIO",
        supers: 1,
        methods: &["liftIO"],
    },
    ClassSpec {
        module: "Control.Monad.State.Class",
        class: "MonadState",
        con: "C:MonadState",
        supers: 1,
        methods: &["get", "put", "state"],
    },
    ClassSpec {
        module: "Control.Monad.Reader.Class",
        class: "MonadReader",
        con: "C:MonadReader",
        supers: 1,
        methods: &["ask", "local", "reader"],
    },
    ClassSpec {
        module: "Control.Monad.Writer.Class",
        class: "MonadWriter",
        con: "C:MonadWriter",
        supers: 2,
        methods: &["writer", "tell", "listen", "pass"],
    },
    ClassSpec {
        module: "ShellCheck.Fixer",
        class: "Ranged",
        con: "C:Ranged",
        supers: 0,
        methods: &["start", "end", "overlap", "setRange"],
    },
];

/// The class a selector belongs to, and the field it reads.
pub(crate) fn selector_class(
    module: &str,
    occ: &str,
) -> Option<(&'static ClassSpec, usize, &'static str)> {
    // A superclass selector names its class in its own occurrence name.
    if let Some(rest) = occ.strip_prefix("$p") {
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        let class = &rest[digits.len()..];
        if let Ok(n) = digits.parse::<usize>()
            && n >= 1
            && let Some(spec) = CLASSES
                .iter()
                .find(|c| c.class == class && c.module == module)
            && n <= spec.supers
        {
            return Some((spec, n - 1, K4_SUPERCLASS_SEL));
        }
        return None;
    }
    let spec = CLASSES
        .iter()
        .find(|c| c.module == module && c.methods.contains(&occ))?;
    Some((spec, spec.method_index(occ)?, K3_CLASS_TABLE))
}

/// The class table entry for a class TyCon's stable name.
pub(crate) fn class_of_tycon(name: &str) -> Option<&'static ClassSpec> {
    let (_, module, occ) = split_stable_name(name)?;
    CLASSES
        .iter()
        .find(|c| c.module == module && c.class == occ)
}

//------------------------------------------------------------------------------
// The closed world
//------------------------------------------------------------------------------

/// Every module in the dump, indexed by the stable names of its top-level
/// bindings. This is what makes a *global* dictionary reference followable:
/// `$fShowToken` is an import in `ShellCheck.Analytics` and a top-level
/// binding in `ShellCheck.AST`, and the closed world has both.
pub struct World<'m> {
    pub modules: Vec<&'m Module>,
    /// Keyed by **stable name**, and only for bindings whose name is
    /// external — the only names another module can refer to, and the only
    /// ones that are unique. A top-level binder GHC has not externalised
    /// has an *internal* name (`$_sys$$fTraversableInnerToken`) that three
    /// distinct bindings of `ShellCheck.AST` share; admitting those here
    /// would silently make one of them stand for the others. This is the
    /// discipline [`crate::dictflow::Program`] already applies, and the
    /// collisions it would have hidden are counted in
    /// [`World::name_collisions`] and asserted to be none.
    tops: HashMap<String, (usize, BinderId, ExprId)>,
    /// External stable names that two distinct top-level bindings claim.
    /// Asserted empty when the world is built.
    pub name_collisions: Vec<String>,
    lam_of: Vec<HashMap<BinderId, ExprId>>,
    top_of_rhs: Vec<HashMap<ExprId, BinderId>>,
}

impl<'m> World<'m> {
    pub fn new(modules: impl IntoIterator<Item = &'m Module>) -> World<'m> {
        let modules: Vec<&Module> = modules.into_iter().collect();
        let mut tops: HashMap<String, (usize, BinderId, ExprId)> = HashMap::new();
        let mut name_collisions: Vec<String> = Vec::new();
        let mut lam_of = Vec::with_capacity(modules.len());
        let mut top_of_rhs = Vec::with_capacity(modules.len());
        for (mi, m) in modules.iter().enumerate() {
            let mut rhs_map = HashMap::new();
            for bind in &m.top {
                for pair in &bind.pairs {
                    let b = m.binder(pair.binder);
                    // Only an external name is referable from another
                    // module, and only an external name is unique.
                    if crate::dictflow::is_external_name(&b.name) {
                        match tops.entry(b.name.clone()) {
                            std::collections::hash_map::Entry::Vacant(e) => {
                                e.insert((mi, pair.binder, pair.rhs));
                            }
                            std::collections::hash_map::Entry::Occupied(e) => {
                                if *e.get() != (mi, pair.binder, pair.rhs) {
                                    name_collisions.push(b.name.clone());
                                }
                            }
                        }
                    }
                    rhs_map.insert(pair.rhs, pair.binder);
                }
            }
            let mut lams = HashMap::new();
            for id in 0..m.exprs.len() as ExprId {
                if let Expr::Lam { binder, .. } = m.expr(id) {
                    lams.insert(*binder, id);
                }
            }
            lam_of.push(lams);
            top_of_rhs.push(rhs_map);
        }
        assert!(
            name_collisions.is_empty(),
            "external stable names are not unique: {name_collisions:?}"
        );
        World {
            modules,
            tops,
            name_collisions,
            lam_of,
            top_of_rhs,
        }
    }

    fn m(&self, mi: usize) -> &'m Module {
        self.modules[mi]
    }
}

//------------------------------------------------------------------------------
// Dictionary sources
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum SourceKind {
    /// A top-level binding whose type is a class constraint: a dfun.
    Dfun,
    /// A dfun *applied* at a use site, building an instance dictionary.
    /// In the closed world when the dfun's binding is in the dump; named
    /// but unreadable otherwise.
    DfunApp,
    /// A `$p…` superclass selector application.
    SuperclassSel,
    /// A saturated application of a class's dictionary constructor.
    DictCon,
    /// A local (`let`) binding whose type is a class constraint.
    LocalDict,
    /// A lambda parameter whose type is a class constraint.
    DictParam,
    /// A case/alt binder whose type is a class constraint.
    DictFromField,
}

/// One dictionary source in the closed world.
#[derive(Debug, Clone, Serialize)]
pub struct Source {
    pub kind: SourceKind,
    pub module: String,
    pub occ: String,
    /// Stable name, for a top-level binding.
    pub name: String,
    pub node: ExprId,
    pub class: Option<String>,
    /// The instance head as GHC rendered the binding's type.
    pub ty: String,
    /// Is the binding in the dump (so its fields can be read)?
    pub in_world: bool,
    /// The class was *not* identified from the type: this source is here
    /// because its name is a dictionary name, which is a diagnostic (1),
    /// not a proof. True for every class the table does not carry.
    pub by_name: bool,
}

//------------------------------------------------------------------------------
// Origins and targets
//------------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum OriginKind {
    /// A dictionary-constructor application reached in the closed world.
    DictCon,
    /// A dfun whose binding is not in the dump: the instance is known, the
    /// method body is not.
    ImportedDfun,
}

/// One dictionary the site's dictionary argument can be.
#[derive(Debug, Clone, Serialize)]
pub struct Origin {
    pub kind: OriginKind,
    /// The module the dictionary lives in.
    pub module: String,
    /// The `C:Class` application, or the imported dfun's reference node.
    pub node: ExprId,
    /// The dfun or constructor that built it.
    pub name: String,
    /// How it was reached, outermost step first.
    pub chain: Vec<String>,
    pub depth: usize,
    /// dfun parameters bound to actual arguments one level deep.
    #[serde(skip)]
    subst: Vec<(BinderId, usize, ExprId)>,
    #[serde(skip)]
    mi: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TargetKind {
    /// A top-level binding, named by its stable name.
    GlobalBinding,
    /// A local lambda.
    LocalLambda,
    /// A partial application or other known closure expression.
    KnownClosure,
    /// A local binding that is not a lambda.
    LocalBinding,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Target {
    pub kind: TargetKind,
    pub module: String,
    pub occ: String,
    pub name: String,
    pub node: ExprId,
}

#[derive(Debug, Clone, Serialize)]
pub enum Outcome {
    Exact(Target),
    FiniteSet(Vec<Target>),
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
}

/// Dictionary-evaluation observations. Facts, no verdict: whether the
/// dictionary can disappear is M2.4c's question, not this one.
#[derive(Debug, Clone, Copy, Default, Serialize)]
pub struct EvalFacts {
    /// The selector application forces the dictionary ([`K10_FORCED`]).
    pub forces_dictionary: bool,
    /// The dictionary argument is a variable with no strictness recorded on
    /// its binder: nothing here says it is not bottom.
    pub dict_could_be_bottom: bool,
    /// The dictionary's binder is strict at its binding site.
    pub dict_known_strict: bool,
    /// The dictionary is also used somewhere that is not the dictionary
    /// argument of a class-op site ([`K11_DICT_ESCAPES`]).
    pub dict_used_as_value: bool,
    /// One such use, for the report.
    pub dict_value_use: Option<ExprId>,
}

/// One class-op application site.
#[derive(Debug, Clone, Serialize)]
pub struct Site {
    pub module: String,
    pub node: ExprId,
    /// The selector's stable name.
    pub selector: String,
    pub method: String,
    /// The class TyCon's stable name, when the dictionary's type gives it.
    pub class: Option<String>,
    /// The class as the table names it.
    pub class_occ: String,
    pub n_value_args: usize,
    pub dict_arg: Option<ExprId>,
    /// The field index the selector reads.
    pub field: Option<usize>,
    pub origins: Vec<Origin>,
    pub outcome: Outcome,
    /// Longest origin chain followed for this site.
    pub depth: usize,
    pub facts: EvalFacts,
    pub rules: Vec<&'static str>,
    /// This site is also a dictionary source (a superclass selection).
    pub is_superclass_sel: bool,
}

//------------------------------------------------------------------------------
// The census
//------------------------------------------------------------------------------

#[derive(Debug, Default, Serialize)]
pub struct Census {
    pub sites: Vec<Site>,
    pub sources: Vec<Source>,
    /// Class-table entries whose field count disagrees with the dump.
    pub table_mismatches: Vec<String>,
    /// Census sites (the 294) that did not map onto a population site.
    pub unmapped_census: Vec<(String, ExprId)>,
    pub census_sites: usize,
    pub census_mapped: usize,
    /// A module or class filter has been applied: the population is a
    /// subset and the census mapping is not asserted over it.
    pub filtered: bool,
}

const BUDGET: usize = 400;

impl Census {
    pub fn of_world(world: &World) -> Census {
        let mut census = Census::default();
        for mi in 0..world.modules.len() {
            census.add_module(world, mi);
        }
        census
            .sources
            .sort_by(|a, b| (a.kind, &a.module, a.node).cmp(&(b.kind, &b.module, b.node)));
        census
    }

    /// Population and the census mapping in one step.
    pub fn of_modules<'a>(modules: impl IntoIterator<Item = &'a Module>) -> (Census, World<'a>) {
        let world = World::new(modules);
        let mut census = Census::of_world(&world);
        census.map_census(&world);
        (census, world)
    }

    /// Relate the residual-laziness census's class-op residue to the
    /// population: every such argument site is an argument of exactly one
    /// population site.
    fn map_census(&mut self, world: &World) {
        let lz = crate::laziness::Census::of_modules(world.modules.iter().copied());
        let pop: HashSet<(&str, ExprId)> = self
            .sites
            .iter()
            .map(|s| (s.module.as_str(), s.node))
            .collect();
        for a in &lz.args {
            if a.callee.resolution != crate::callee::Resolution::ClassOp
                || !a.position.escapes()
                || a.shape != crate::shape::ArgShape::Computation
            {
                continue;
            }
            self.census_sites += 1;
            if pop.contains(&(a.module.as_str(), a.app)) {
                self.census_mapped += 1;
            } else {
                self.unmapped_census.push((a.module.clone(), a.app));
            }
        }
    }

    /// Restrict the report to one module and/or one class. The closed
    /// world is *not* restricted — resolution still sees every module —
    /// so this changes what is shown, never what is provable.
    pub fn filter(&mut self, module: Option<&str>, class: Option<&str>) {
        if module.is_none() && class.is_none() {
            return;
        }
        self.filtered = true;
        self.sites.retain(|s| {
            module.is_none_or(|m| s.module == m) && class.is_none_or(|c| s.class_occ == c)
        });
        self.sources
            .retain(|s| module.is_none_or(|m| s.module == m));
    }

    fn add_module(&mut self, world: &World, mi: usize) {
        let m = world.m(mi);
        let s = Scope::new(m);
        self.collect_sources(world, mi, &s);
        for id in 0..m.exprs.len() as ExprId {
            if !matches!(m.expr(id), Expr::App { .. }) || m.spine_root(id) != id {
                continue;
            }
            let (head, args) = m.spine(id);
            let Some(sig) = s.head_sig(head) else {
                continue;
            };
            if !sig.is_class_op {
                continue;
            }
            let Expr::Var { name, occ, .. } = m.expr(head) else {
                continue;
            };
            let site = self.site(world, mi, &s, id, name.clone(), occ.clone(), &args);
            self.sites.push(site);
        }
        // A bare class-op occurrence that is not applied at all is the
        // selector used as a value; there is no dictionary to follow.
        for id in 0..m.exprs.len() as ExprId {
            if !matches!(m.expr(id), Expr::Var { .. }) || m.spine_root(id) != id {
                continue;
            }
            if !s.head_sig(id).is_some_and(|x| x.is_class_op) {
                continue;
            }
            let Expr::Var { name, occ, .. } = m.expr(id) else {
                continue;
            };
            let (_, module, _) = split_stable_name(name).unwrap_or(("", "", ""));
            let spec = selector_class(module, occ);
            self.sites.push(Site {
                module: m.name.clone(),
                node: id,
                selector: name.clone(),
                method: occ.clone(),
                class: None,
                class_occ: spec
                    .map(|(c, _, _)| c.class.to_string())
                    .unwrap_or_default(),
                n_value_args: 0,
                dict_arg: None,
                field: spec.map(|(_, f, _)| f),
                origins: Vec::new(),
                outcome: Outcome::Unresolved(U_PARTIAL.into()),
                depth: 0,
                facts: EvalFacts::default(),
                rules: vec![K0_CLASSOP_SITE, K12_PARTIAL],
                is_superclass_sel: occ.starts_with("$p"),
            });
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn site(
        &mut self,
        world: &World,
        mi: usize,
        s: &Scope,
        node: ExprId,
        selector: String,
        occ: String,
        args: &[ExprId],
    ) -> Site {
        let m = world.m(mi);
        let vargs = value_args(s, args);
        let (_, sel_module, _) = split_stable_name(&selector).unwrap_or(("", "", ""));
        let spec = selector_class(sel_module, &occ);
        let mut rules = vec![K0_CLASSOP_SITE];
        let mut site = Site {
            module: m.name.clone(),
            node,
            selector: selector.clone(),
            method: occ.clone(),
            class: None,
            class_occ: spec
                .map(|(c, _, _)| c.class.to_string())
                .unwrap_or_default(),
            n_value_args: vargs.len(),
            dict_arg: vargs.first().copied(),
            field: spec.map(|(_, f, _)| f),
            origins: Vec::new(),
            outcome: Outcome::Unresolved(U_PARTIAL.into()),
            depth: 0,
            facts: EvalFacts::default(),
            rules: Vec::new(),
            is_superclass_sel: occ.starts_with("$p"),
        };
        let Some(&dict) = vargs.first() else {
            rules.push(K12_PARTIAL);
            site.rules = rules;
            return site;
        };
        rules.push(K1_DICT_ARG);
        site.facts.forces_dictionary = true;
        rules.push(K10_FORCED);

        // The class, from the dictionary's structured type where the dump
        // has one: level 4, and a cross-check on the table.
        let dict_ty = self.dict_ty(world, mi, dict);
        if let Some(tc) = dict_ty.as_ref().and_then(|t| t.tycon()) {
            site.class = Some(tc.name.to_string());
            rules.push(K2_DICT_TYPE);
        }
        let Some((spec, field, rule)) = spec else {
            site.outcome = Outcome::Unresolved(format!("{U_CLASS_UNKNOWN}({sel_module}.{occ})"));
            site.rules = rules;
            return site;
        };
        rules.push(rule);
        if let Some(name) = &site.class
            && class_of_tycon(name).map(|c| c.class) != Some(spec.class)
        {
            site.outcome = Outcome::Unresolved(format!(
                "{U_CLASS_MISMATCH}(table {} vs dump {name})",
                spec.class
            ));
            site.rules = rules;
            return site;
        }
        self.eval_facts(world, mi, dict, &mut site);
        if site.facts.dict_used_as_value {
            rules.push(K11_DICT_ESCAPES);
        }

        // Follow the dictionary.
        let mut origins = Vec::new();
        let mut unresolved = Vec::new();
        let mut seen = HashSet::new();
        let mut budget = BUDGET;
        self.follow(
            world,
            mi,
            dict,
            0,
            &mut Vec::new(),
            &mut origins,
            &mut unresolved,
            &mut seen,
            &mut budget,
        );
        site.depth = origins.iter().map(|o| o.depth).max().unwrap_or(0);
        for o in &origins {
            match o.kind {
                OriginKind::DictCon => {
                    if !rules.contains(&K7_DICT_CON) {
                        rules.push(K7_DICT_CON)
                    }
                }
                OriginKind::ImportedDfun => {}
            }
            for c in &o.chain {
                for (tag, r) in [
                    ("alias", K5_ALIAS),
                    ("global", K6_DFUN),
                    ("dfun", K6_DFUN),
                    ("param", K8_PARAM_UNION),
                    ("superclass", K4_SUPERCLASS_SEL),
                ] {
                    if c.starts_with(tag) && !rules.contains(&r) {
                        rules.push(r);
                    }
                }
            }
        }

        // The method target of each origin.
        let mut targets: Vec<Target> = Vec::new();
        for o in &origins {
            match self.target(world, o, spec, field) {
                Ok(t) => {
                    if !targets.contains(&t) {
                        targets.push(t)
                    }
                }
                Err(e) => unresolved.push(e),
            }
        }
        if !targets.is_empty() {
            rules.push(K9_METHOD_FIELD);
        }
        site.outcome = if !unresolved.is_empty() {
            unresolved.sort();
            unresolved.dedup();
            Outcome::Unresolved(unresolved.join("; "))
        } else if targets.len() == 1 {
            Outcome::Exact(targets.pop().unwrap())
        } else if targets.is_empty() {
            Outcome::Unresolved(U_NO_ORIGIN.into())
        } else {
            Outcome::FiniteSet(targets)
        };
        site.origins = origins;
        site.rules = rules;
        site
    }

    /// The structured type of a dictionary expression, when the dump has
    /// one: the binder of a local, or the top-level binder of a global that
    /// is bound somewhere in the closed world.
    fn dict_ty(&self, world: &World, mi: usize, node: ExprId) -> Option<Ty> {
        let m = world.m(mi);
        let (head, args) = m.spine(m.strip(node));
        if let Some(b) = m.resolve(head) {
            if args.is_empty() {
                return Some(m.binder_ty(b).clone());
            }
            return Some(m.binder_ty(b).fun_result().clone());
        }
        let Expr::Var { name, .. } = m.expr(head) else {
            return None;
        };
        let (wi, b, _) = world.tops.get(name)?;
        let ty = world.m(*wi).binder_ty(*b);
        Some(if args.is_empty() {
            ty.clone()
        } else {
            ty.fun_result().clone()
        })
    }

    fn eval_facts(&self, world: &World, mi: usize, dict: ExprId, site: &mut Site) {
        let m = world.m(mi);
        let (head, args) = m.spine(m.strip(dict));
        let Some(b) = m.resolve(head) else { return };
        if !args.is_empty() {
            return;
        }
        let binder = m.binder(b);
        match binder.demand.as_ref() {
            Some(d) if d.strict => site.facts.dict_known_strict = true,
            _ => site.facts.dict_could_be_bottom = true,
        }
        // Is the dictionary used anywhere but as a class-op dictionary?
        for &occ in m.occurrences(b) {
            if self.is_dict_arg_of_classop(world, mi, occ) {
                continue;
            }
            site.facts.dict_used_as_value = true;
            site.facts.dict_value_use = Some(occ);
            break;
        }
    }

    /// Is this occurrence the dictionary argument of a class-op site — the
    /// one use of a dictionary that is dispatch rather than a value use?
    fn is_dict_arg_of_classop(&self, world: &World, mi: usize, occ: ExprId) -> bool {
        let m = world.m(mi);
        let s = Scope::new(m);
        let mut cur = occ;
        while let Some(p) = m.parent[cur as usize] {
            match m.edge[cur as usize] {
                Edge::Cast | Edge::Tick => cur = p,
                Edge::AppArg => {
                    let (head, args) = m.spine(m.spine_root(p));
                    if !s.head_sig(head).is_some_and(|x| x.is_class_op) {
                        return false;
                    }
                    return value_args(&s, &args).first().map(|&a| m.strip(a))
                        == Some(m.strip(cur));
                }
                _ => return false,
            }
        }
        false
    }

    //--------------------------------------------------------------------------
    // Following a dictionary to its origins
    //--------------------------------------------------------------------------

    /// Follow a dictionary expression to the dictionaries it can be.
    /// `seen` is the set of nodes on the *current path*, so a diamond is
    /// not mistaken for a cycle; a genuine cycle stops the walk.
    #[allow(clippy::too_many_arguments)]
    fn follow(
        &self,
        world: &World,
        mi: usize,
        node: ExprId,
        depth: usize,
        chain: &mut Vec<String>,
        out: &mut Vec<Origin>,
        un: &mut Vec<String>,
        seen: &mut HashSet<(usize, ExprId)>,
        budget: &mut usize,
    ) {
        self.follow_inner(world, mi, node, depth, chain, out, un, seen, budget);
        seen.remove(&(mi, node));
    }

    #[allow(clippy::too_many_arguments)]
    fn follow_inner(
        &self,
        world: &World,
        mi: usize,
        node: ExprId,
        depth: usize,
        chain: &mut Vec<String>,
        out: &mut Vec<Origin>,
        un: &mut Vec<String>,
        seen: &mut HashSet<(usize, ExprId)>,
        budget: &mut usize,
    ) {
        if *budget == 0 {
            un.push(U_BUDGET.into());
            return;
        }
        *budget -= 1;
        if !seen.insert((mi, node)) {
            un.push(U_RECURSIVE.into());
            return;
        }
        let m = world.m(mi);
        let s = Scope::new(m);
        let inner = m.strip(node);
        let (head, args) = m.spine(inner);
        let vargs = value_args(&s, &args);

        match m.expr(head) {
            Expr::Case { alts, .. } => {
                for alt in alts.clone() {
                    chain.push("case-alternative".into());
                    self.follow(world, mi, alt.rhs, depth + 1, chain, out, un, seen, budget);
                    chain.pop();
                }
                return;
            }
            Expr::Let { body, .. } => {
                let body = *body;
                chain.push("let-body".into());
                self.follow(world, mi, body, depth + 1, chain, out, un, seen, budget);
                chain.pop();
                return;
            }
            Expr::Var { .. } => {}
            _ => {
                un.push(U_NOT_A_CON.into());
                return;
            }
        }

        // A saturated dictionary-constructor application is a dictionary.
        if let Some(dc) = s.head_sig(head).and_then(|x| x.data_con)
            && vargs.len() >= dc.rep_arity as usize
        {
            let Expr::Var { name, occ, .. } = m.expr(head) else {
                unreachable!()
            };
            out.push(Origin {
                kind: OriginKind::DictCon,
                module: m.name.clone(),
                node: inner,
                name: name.clone(),
                chain: {
                    let mut c = chain.clone();
                    c.push(format!("dictionary-constructor {occ}"));
                    c
                },
                depth,
                subst: Vec::new(),
                mi,
            });
            return;
        }

        if let Some(b) = m.resolve(head) {
            self.follow_local(world, mi, b, &vargs, depth, chain, out, un, seen, budget);
            return;
        }

        // A global.
        let Expr::Var { name, occ, .. } = m.expr(head) else {
            unreachable!()
        };
        // A superclass selector applied to a dictionary.
        if occ.starts_with("$p")
            && let Some(&d) = vargs.first()
        {
            let (_, gmodule, _) = split_stable_name(name).unwrap_or(("", "", ""));
            let Some((spec, field, _)) = selector_class(gmodule, occ) else {
                un.push(format!("{U_CLASS_UNKNOWN}({gmodule}.{occ})"));
                return;
            };
            let mut inner_out = Vec::new();
            chain.push(format!("superclass {occ}"));
            self.follow(
                world,
                mi,
                d,
                depth + 1,
                chain,
                &mut inner_out,
                un,
                seen,
                budget,
            );
            chain.pop();
            for o in &inner_out {
                match self.field_of(world, o, spec, field) {
                    Ok((fmi, fnode)) => {
                        chain.push(format!("superclass {occ}"));
                        self.follow(world, fmi, fnode, depth + 2, chain, out, un, seen, budget);
                        chain.pop();
                    }
                    Err(e) => un.push(e),
                }
            }
            return;
        }
        // A global binding that is in the dump.
        if let Some(&(wi, b, rhs)) = world.tops.get(name) {
            chain.push(format!("global {occ}"));
            if vargs.is_empty() {
                self.follow(world, wi, rhs, depth + 1, chain, out, un, seen, budget);
            } else {
                self.follow_dfun(
                    world,
                    wi,
                    b,
                    rhs,
                    mi,
                    &vargs,
                    depth + 1,
                    chain,
                    out,
                    un,
                    seen,
                    budget,
                );
            }
            chain.pop();
            return;
        }
        // A global with no binding in the dump.
        un.push(format!("{U_IMPORTED_DFUN}({occ})"));
        out.push(Origin {
            kind: OriginKind::ImportedDfun,
            module: split_stable_name(name)
                .map(|(_, md, _)| md.to_string())
                .unwrap_or_default(),
            node: head,
            name: name.clone(),
            chain: chain.clone(),
            depth,
            subst: Vec::new(),
            mi,
        });
    }

    /// A dfun applied to argument dictionaries: bind its value parameters
    /// to the actual arguments, one level deep, and read its body.
    #[allow(clippy::too_many_arguments)]
    fn follow_dfun(
        &self,
        world: &World,
        wi: usize,
        _b: BinderId,
        rhs: ExprId,
        caller: usize,
        vargs: &[ExprId],
        depth: usize,
        chain: &mut Vec<String>,
        out: &mut Vec<Origin>,
        un: &mut Vec<String>,
        seen: &mut HashSet<(usize, ExprId)>,
        budget: &mut usize,
    ) {
        let dm = world.m(wi);
        // Strip the lambda chain, collecting value parameters.
        let mut params: Vec<BinderId> = Vec::new();
        let mut cur = dm.strip(rhs);
        while let Expr::Lam { binder, body } = dm.expr(cur) {
            if dm.binder(*binder).kind != h2r_core_ir::BinderKind::Tyvar {
                params.push(*binder);
            }
            cur = dm.strip(*body);
        }
        let subst: Vec<(BinderId, usize, ExprId)> = params
            .iter()
            .zip(vargs)
            .map(|(&p, &a)| (p, caller, a))
            .collect();
        let before = out.len();
        self.follow(world, wi, cur, depth, chain, out, un, seen, budget);
        for o in out[before..].iter_mut() {
            o.subst = subst.clone();
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn follow_local(
        &self,
        world: &World,
        mi: usize,
        b: BinderId,
        vargs: &[ExprId],
        depth: usize,
        chain: &mut Vec<String>,
        out: &mut Vec<Origin>,
        un: &mut Vec<String>,
        seen: &mut HashSet<(usize, ExprId)>,
        budget: &mut usize,
    ) {
        let m = world.m(mi);
        let bi = m.binding(b);
        match bi.site {
            BindSite::Let | BindSite::Top => {
                let Some(rhs) = bi.rhs else {
                    un.push(U_NOT_A_CON.into());
                    return;
                };
                if vargs.is_empty() {
                    chain.push(format!("alias {}", m.binder(b).occ));
                    self.follow(world, mi, rhs, depth + 1, chain, out, un, seen, budget);
                    chain.pop();
                } else {
                    chain.push(format!("dfun {}", m.binder(b).occ));
                    self.follow_dfun(
                        world,
                        mi,
                        b,
                        rhs,
                        mi,
                        vargs,
                        depth + 1,
                        chain,
                        out,
                        un,
                        seen,
                        budget,
                    );
                    chain.pop();
                }
            }
            BindSite::Lam => self.follow_param(world, mi, b, depth, chain, out, un, seen, budget),
            BindSite::CaseBinder => {
                // `case d of wild { … }`: the binder is the scrutinee.
                let Some(scrut) = self.case_scrut_of(m, b) else {
                    un.push(U_FROM_FIELD.into());
                    return;
                };
                chain.push("case-binder".into());
                self.follow(world, mi, scrut, depth + 1, chain, out, un, seen, budget);
                chain.pop();
            }
            BindSite::AltBinder => {
                match self.alt_field_of(m, b) {
                    // `case d of C:Class … f … -> …`: the binder is field
                    // `i` of whatever `d` is.
                    Some((scrut, spec, i)) => {
                        let mut inner_out = Vec::new();
                        chain.push(format!("dictionary-field {}#{i}", spec.con));
                        self.follow(
                            world,
                            mi,
                            scrut,
                            depth + 1,
                            chain,
                            &mut inner_out,
                            un,
                            seen,
                            budget,
                        );
                        chain.pop();
                        for o in &inner_out {
                            match self.field_of(world, o, spec, i) {
                                Ok((fmi, fnode)) => {
                                    chain.push(format!("dictionary-field {}#{i}", spec.con));
                                    self.follow(
                                        world,
                                        fmi,
                                        fnode,
                                        depth + 2,
                                        chain,
                                        out,
                                        un,
                                        seen,
                                        budget,
                                    );
                                    chain.pop();
                                }
                                Err(e) => un.push(e),
                            }
                        }
                    }
                    None => un.push(U_FROM_FIELD.into()),
                }
            }
        }
    }

    /// If `b` is bound by an alternative of a `case` over a *dictionary*
    /// constructor, the scrutinee, the class and the field index.
    fn alt_field_of(&self, m: &Module, b: BinderId) -> Option<(ExprId, &'static ClassSpec, usize)> {
        for id in 0..m.exprs.len() as ExprId {
            let Expr::Case { scrut, alts, .. } = m.expr(id) else {
                continue;
            };
            for alt in alts {
                let Some(i) = alt.binders.iter().position(|x| *x == b) else {
                    continue;
                };
                let h2r_core_ir::AltCon::DataAlt { name, .. } = &alt.con else {
                    return None;
                };
                let (_, module, occ) = split_stable_name(name)?;
                let class = occ.strip_prefix("C:")?;
                let spec = CLASSES
                    .iter()
                    .find(|c| c.class == class && c.module == module)?;
                if i >= spec.fields() || alt.binders.len() != spec.fields() {
                    return None;
                }
                return Some((*scrut, spec, i));
            }
        }
        None
    }

    fn case_scrut_of(&self, m: &Module, b: BinderId) -> Option<ExprId> {
        for id in 0..m.exprs.len() as ExprId {
            if let Expr::Case { scrut, binder, .. } = m.expr(id)
                && *binder == b
            {
                return Some(*scrut);
            }
        }
        None
    }

    /// A dictionary parameter: the union over the call sites of the
    /// function whose parameter it is ([`K8_PARAM_UNION`]).
    #[allow(clippy::too_many_arguments)]
    fn follow_param(
        &self,
        world: &World,
        mi: usize,
        b: BinderId,
        depth: usize,
        chain: &mut Vec<String>,
        out: &mut Vec<Origin>,
        un: &mut Vec<String>,
        seen: &mut HashSet<(usize, ExprId)>,
        budget: &mut usize,
    ) {
        let m = world.m(mi);
        let Some(&lam) = world.lam_of[mi].get(&b) else {
            un.push(U_ANON_LAMBDA.into());
            return;
        };
        // Climb the lambda chain, counting value parameters to our left.
        let mut idx = 0usize;
        let mut cur = lam;
        let owner = loop {
            let Some(p) = m.parent[cur as usize] else {
                break world.top_of_rhs[mi].get(&cur).copied();
            };
            match m.edge[cur as usize] {
                Edge::LamBody if matches!(m.expr(p), Expr::Lam { .. }) => {
                    if let Expr::Lam { binder, .. } = m.expr(p)
                        && m.binder(*binder).kind != h2r_core_ir::BinderKind::Tyvar
                    {
                        idx += 1;
                    }
                    cur = p;
                }
                Edge::Cast | Edge::Tick => cur = p,
                Edge::LetRhs { pair } => {
                    break match m.expr(p) {
                        Expr::Let { bind, .. } => Some(bind.pairs[pair as usize].binder),
                        _ => None,
                    };
                }
                _ => break None,
            }
        };
        let Some(f) = owner else {
            un.push(U_ANON_LAMBDA.into());
            return;
        };
        let fb: &Binder = m.binder(f);
        if m.binding(f).site == BindSite::Top && fb.exported == Some(true) {
            un.push(U_EXPORTED_PARAM.into());
            return;
        }
        let occs = m.occurrences(f);
        if occs.is_empty() {
            un.push(U_PARAM_NO_CALLS.into());
            return;
        }
        let s = Scope::new(m);
        let mut actuals = Vec::new();
        for &occ in occs {
            let root = m.spine_root(occ);
            let (head, args) = m.spine(root);
            let va = value_args(&s, &args);
            if root == occ || m.strip(head) != m.strip(occ) || va.len() <= idx {
                un.push(format!("{}({})", self.non_call_reason(&s, occ), fb.occ));
                return;
            }
            let a = va[idx];
            actuals.push(a);
        }
        for a in actuals {
            chain.push(format!("param {}#{idx}", fb.occ));
            self.follow(world, mi, a, depth + 1, chain, out, un, seen, budget);
            chain.pop();
        }
    }

    //--------------------------------------------------------------------------
    // Fields and targets
    //--------------------------------------------------------------------------

    /// Why an occurrence of a function is not a call site we can read a
    /// dictionary argument off. The distinction that matters: an
    /// occurrence that is a *method field of a dictionary* is reached only
    /// through dispatch, which is the analysis this milestone does not do.
    fn non_call_reason(&self, s: &Scope, occ: ExprId) -> &'static str {
        let m = s.m;
        // Climb out of any casts to the position the occurrence sits in.
        let mut cur = occ;
        while let Some(p) = m.parent[cur as usize] {
            match m.edge[cur as usize] {
                Edge::Cast | Edge::Tick => cur = p,
                Edge::AppArg => {
                    let (head, args) = m.spine(m.spine_root(p));
                    if let Some(dc) = s.head_sig(head).and_then(|x| x.data_con)
                        && value_args(s, &args).len() >= dc.rep_arity as usize
                        && matches!(m.expr(head), Expr::Var { occ, .. } if occ.starts_with("C:"))
                    {
                        return U_PARAM_DISPATCH;
                    }
                    return U_PARAM_NOT_CALLED;
                }
                _ => return U_PARAM_NOT_CALLED,
            }
        }
        U_PARAM_NOT_CALLED
    }

    /// The `field`th field of a resolved dictionary, in its module.
    fn field_of(
        &self,
        world: &World,
        o: &Origin,
        spec: &ClassSpec,
        field: usize,
    ) -> Result<(usize, ExprId), String> {
        if o.kind == OriginKind::ImportedDfun {
            return Err(format!("{U_IMPORTED_DFUN}({})", occ_of(&o.name)));
        }
        let m = world.m(o.mi);
        let s = Scope::new(m);
        let (head, args) = m.spine(o.node);
        let Some(dc) = s.head_sig(head).and_then(|x| x.data_con) else {
            return Err(U_NOT_A_CON.into());
        };
        if dc.rep_arity as usize != spec.fields() {
            return Err(format!(
                "{U_CLASS_MISMATCH}({} has {} fields, table says {})",
                spec.class,
                dc.rep_arity,
                spec.fields()
            ));
        }
        let vargs = value_args(&s, &args);
        let Some(&f) = vargs.get(field) else {
            return Err(U_NOT_A_CON.into());
        };
        // A field that is one of the dfun's own parameters is the actual
        // argument at the application that built this dictionary.
        let stripped = m.strip(f);
        if let Some(b) = m.resolve(stripped)
            && let Some((_, cmi, actual)) = o.subst.iter().find(|(p, _, _)| *p == b)
        {
            return Ok((*cmi, *actual));
        }
        Ok((o.mi, f))
    }

    fn target(
        &self,
        world: &World,
        o: &Origin,
        spec: &ClassSpec,
        field: usize,
    ) -> Result<Target, String> {
        let (fmi, fnode) = self.field_of(world, o, spec, field)?;
        let m = world.m(fmi);
        let node = m.strip(fnode);
        match m.expr(node) {
            Expr::Var { name, occ, .. } => {
                if let Some(b) = m.resolve(node) {
                    let site = m.binding(b);
                    let kind = match site.site {
                        BindSite::Top => TargetKind::GlobalBinding,
                        BindSite::Let => {
                            let is_lam = site
                                .rhs
                                .is_some_and(|r| matches!(m.expr(m.strip(r)), Expr::Lam { .. }));
                            if is_lam {
                                TargetKind::LocalLambda
                            } else {
                                TargetKind::LocalBinding
                            }
                        }
                        _ => TargetKind::LocalBinding,
                    };
                    Ok(Target {
                        kind,
                        module: m.name.clone(),
                        occ: m.binder(b).occ.clone(),
                        name: m.binder(b).name.clone(),
                        node,
                    })
                } else {
                    Ok(Target {
                        kind: TargetKind::GlobalBinding,
                        module: split_stable_name(name)
                            .map(|(_, md, _)| md.to_string())
                            .unwrap_or_default(),
                        occ: occ.clone(),
                        name: name.clone(),
                        node,
                    })
                }
            }
            Expr::Lam { .. } => Ok(Target {
                kind: TargetKind::LocalLambda,
                module: m.name.clone(),
                occ: String::new(),
                name: String::new(),
                node,
            }),
            Expr::App { .. } => {
                let (h, _) = m.spine(node);
                let occ = match m.expr(h) {
                    Expr::Var { occ, .. } => occ.clone(),
                    _ => String::new(),
                };
                Ok(Target {
                    kind: TargetKind::KnownClosure,
                    module: m.name.clone(),
                    occ,
                    name: String::new(),
                    node,
                })
            }
            _ => Err(U_UNKNOWN_CALL.into()),
        }
    }

    //--------------------------------------------------------------------------
    // Dictionary sources
    //--------------------------------------------------------------------------

    fn collect_sources(&mut self, world: &World, mi: usize, s: &Scope) {
        let m = world.m(mi);
        for bind in &m.top {
            for pair in &bind.pairs {
                let b = m.binder(pair.binder);
                let class = class_ty(m.binder_ty(pair.binder).fun_result());
                if class.is_none() && !crate::callee::is_dictionary_name(&b.occ) {
                    continue;
                }
                let (head, args) = m.spine(m.strip(pair.rhs));
                let is_con = s
                    .head_sig(head)
                    .and_then(|x| x.data_con)
                    .is_some_and(|dc| value_args(s, &args).len() >= dc.rep_arity as usize);
                self.sources.push(Source {
                    kind: if is_con && !b.occ.starts_with("$f") {
                        SourceKind::DictCon
                    } else {
                        SourceKind::Dfun
                    },
                    module: m.name.clone(),
                    occ: b.occ.clone(),
                    name: b.name.clone(),
                    node: pair.rhs,
                    by_name: class.is_none(),
                    class,
                    ty: b.ty_pretty.clone(),
                    in_world: true,
                });
            }
        }
        for id in 0..m.exprs.len() as ExprId {
            match m.expr(id) {
                Expr::Let { bind, .. } => {
                    for pair in &bind.pairs {
                        let b = m.binder(pair.binder);
                        let class = class_ty(m.binder_ty(pair.binder));
                        if class.is_none() && !b.occ.starts_with("$d") {
                            continue;
                        }
                        self.sources.push(Source {
                            kind: SourceKind::LocalDict,
                            module: m.name.clone(),
                            occ: b.occ.clone(),
                            name: String::new(),
                            node: pair.rhs,
                            by_name: class.is_none(),
                            class,
                            ty: b.ty_pretty.clone(),
                            in_world: true,
                        });
                    }
                }
                Expr::Lam { binder, .. } => {
                    let b = m.binder(*binder);
                    let class = class_ty(m.binder_ty(*binder));
                    if class.is_none() && !b.occ.starts_with("$d") {
                        continue;
                    }
                    self.sources.push(Source {
                        kind: SourceKind::DictParam,
                        module: m.name.clone(),
                        occ: b.occ.clone(),
                        name: String::new(),
                        node: id,
                        by_name: class.is_none(),
                        class,
                        ty: b.ty_pretty.clone(),
                        in_world: true,
                    });
                }
                Expr::Case { alts, .. } => {
                    for alt in alts {
                        for &bid in &alt.binders {
                            let b = m.binder(bid);
                            let class = class_ty(m.binder_ty(bid));
                            if class.is_none() && !b.occ.starts_with("$d") {
                                continue;
                            }
                            self.sources.push(Source {
                                kind: SourceKind::DictFromField,
                                module: m.name.clone(),
                                occ: b.occ.clone(),
                                name: String::new(),
                                node: id,
                                by_name: class.is_none(),
                                class,
                                ty: b.ty_pretty.clone(),
                                in_world: true,
                            });
                        }
                    }
                }
                Expr::App { .. } => {
                    if m.spine_root(id) != id {
                        continue;
                    }
                    let (head, args) = m.spine(id);
                    let Expr::Var {
                        name,
                        occ,
                        is_global,
                        ..
                    } = m.expr(head)
                    else {
                        continue;
                    };
                    if !*is_global {
                        continue;
                    }
                    // A superclass selection, or an imported dfun applied.
                    let (_, gm, _) = split_stable_name(name).unwrap_or(("", "", ""));
                    // A dfun application is recognised by the *type* of the
                    // binding it names wherever the closed world has it
                    // (level 4); for an import there is no type in the
                    // dump, and the name is all there is (level 1).
                    let is_dfun = match world.tops.get(name) {
                        Some(&(wi, b, _)) => {
                            class_ty(world.m(wi).binder_ty(b).fun_result()).is_some()
                        }
                        None => crate::callee::is_dictionary_name(occ) && occ.starts_with("$f"),
                    };
                    let kind = if occ.starts_with("$p") && selector_class(gm, occ).is_some() {
                        SourceKind::SuperclassSel
                    } else if is_dfun && !value_args(s, &args).is_empty() {
                        SourceKind::DfunApp
                    } else {
                        continue;
                    };
                    self.sources.push(Source {
                        kind,
                        module: m.name.clone(),
                        occ: occ.clone(),
                        name: name.clone(),
                        node: id,
                        class: None,
                        by_name: !world.tops.contains_key(name),
                        ty: String::new(),
                        in_world: world.tops.contains_key(name),
                    });
                }
                _ => {}
            }
        }
    }

    //--------------------------------------------------------------------------
    // Accounting
    //--------------------------------------------------------------------------

    pub fn accounting(&self) -> Accounting {
        let mut a = Accounting {
            population: self.sites.len(),
            census_sites: self.census_sites,
            census_mapped: self.census_mapped,
            filtered: self.filtered,
            ..Default::default()
        };
        for s in &self.sites {
            match &s.outcome {
                Outcome::Exact(_) => a.exact += 1,
                Outcome::FiniteSet(_) => a.finite += 1,
                Outcome::Unresolved(r) => {
                    a.unresolved += 1;
                    *a.reasons.entry(reason_head(r)).or_default() += 1;
                }
            }
            let class = if s.class_occ.is_empty() {
                "?".to_string()
            } else {
                s.class_occ.clone()
            };
            let row = a.by_class.entry(class).or_default();
            row.0 += 1;
            match &s.outcome {
                Outcome::Exact(_) => row.1 += 1,
                Outcome::FiniteSet(_) => row.2 += 1,
                Outcome::Unresolved(_) => row.3 += 1,
            }
            *a.depths.entry(s.depth).or_default() += 1;
            if s.facts.forces_dictionary {
                a.forces += 1;
            }
            if s.facts.dict_could_be_bottom {
                a.could_be_bottom += 1;
            }
            if s.facts.dict_known_strict {
                a.known_strict += 1;
            }
            if s.facts.dict_used_as_value {
                a.used_as_value += 1;
            }
            if s.n_value_args == 0 {
                a.partial += 1;
            }
            match &s.outcome {
                Outcome::Exact(t) => *a.targets.entry(t.kind).or_default() += 1,
                Outcome::FiniteSet(ts) => {
                    for t in ts {
                        *a.targets.entry(t.kind).or_default() += 1;
                    }
                }
                Outcome::Unresolved(_) => {}
            }
        }
        for s in &self.sources {
            *a.sources.entry(s.kind).or_default() += 1;
            if s.by_name {
                a.sources_by_name += 1;
            }
            if !s.in_world {
                a.sources_outside_the_dump += 1;
            }
        }
        a
    }
}

fn occ_of(name: &str) -> String {
    split_stable_name(name)
        .map(|(_, _, o)| o.to_string())
        .unwrap_or_else(|| name.to_string())
}

/// The first parenthesis-free head of an unresolved reason, for grouping.
fn reason_head(r: &str) -> String {
    r.split(';').next().unwrap_or(r).trim().to_string()
}

/// Is this type a class constraint — a `TyConApp` of a class the table
/// knows? Level 4 on the structured type; the table decides classhood.
pub(crate) fn class_ty(t: &Ty) -> Option<String> {
    let tc = t.tycon()?;
    class_of_tycon(&tc.name)?;
    Some(tc.name.to_string())
}

#[derive(Debug, Default, Serialize)]
pub struct Accounting {
    pub population: usize,
    pub exact: usize,
    pub finite: usize,
    pub unresolved: usize,
    pub partial: usize,
    pub census_sites: usize,
    pub census_mapped: usize,
    pub filtered: bool,
    pub forces: usize,
    pub could_be_bottom: usize,
    pub known_strict: usize,
    pub used_as_value: usize,
    pub reasons: BTreeMap<String, usize>,
    /// class → (sites, exact, finite, unresolved)
    pub by_class: BTreeMap<String, (usize, usize, usize, usize)>,
    pub depths: BTreeMap<usize, usize>,
    pub targets: BTreeMap<TargetKind, usize>,
    pub sources: BTreeMap<SourceKind, usize>,
    /// Dictionary sources admitted on their *name* because the class table
    /// does not carry their class: a diagnostic, not a proof.
    pub sources_by_name: usize,
    /// Dictionary sources whose binding is not in the dump.
    pub sources_outside_the_dump: usize,
}

impl Accounting {
    /// population = Exact + FiniteSet + Unresolved, and every census site
    /// maps onto a population site.
    pub fn check(&self) -> Result<(), String> {
        if self.exact + self.finite + self.unresolved != self.population {
            return Err(format!(
                "population {} != {} + {} + {}",
                self.population, self.exact, self.finite, self.unresolved
            ));
        }
        if !self.filtered && self.census_mapped != self.census_sites {
            return Err(format!(
                "{} of {} census sites mapped",
                self.census_mapped, self.census_sites
            ));
        }
        Ok(())
    }
}

/// Class-table entries whose field count disagrees with a dictionary
/// constructor in the dump. Empty is the expected answer.
pub fn check_table(world: &World) -> Vec<String> {
    let mut out = BTreeSet::new();
    for m in &world.modules {
        for (name, info) in &m.ids {
            let Some(dc) = &info.data_con else { continue };
            if !info.occ.starts_with("C:") {
                continue;
            }
            let Some((_, module, occ)) = split_stable_name(name) else {
                continue;
            };
            let class = occ.trim_start_matches("C:");
            let Some(spec) = CLASSES
                .iter()
                .find(|c| c.class == class && c.module == module)
            else {
                continue;
            };
            if dc.rep_arity as usize != spec.fields() {
                out.insert(format!(
                    "{}.{}: dump says {} fields, table says {}",
                    module,
                    class,
                    dc.rep_arity,
                    spec.fields()
                ));
            }
        }
    }
    out.into_iter().collect()
}
