//! GHC Core as dumped by `h2r-plugin`, flattened into an arena.
//!
//! Core's `App` spines and `Let` chains nest deeply enough that recursive
//! walkers are a liability, so the nested JSON is flattened once on load —
//! iteratively — and every pass afterwards works on indices with explicit
//! worklists. Parent links and the edge each node hangs off are recorded so
//! path queries (is this occurrence under a lambda? in which case branch?)
//! are cheap.

pub mod pretty;
pub mod raw;

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use serde::Deserialize;

pub use raw::{
    AltCon, Binder, BinderKind, DataConInfo, Demand, DmdSig, IdInfo, Lit, OccInfo, TyConId, TyId,
    TyVarId,
};

pub type ExprId = u32;
pub type BinderId = u32;

/// The stable name of GHC's list type constructor. GHC 9.6 calls it `List`;
/// the dump is the authority and this is what it carries.
pub const LIST_TYCON: &str = "$ghc-prim$GHC.Types$List";
/// The stable name of `Char`.
pub const CHAR_TYCON: &str = "$ghc-prim$GHC.Types$Char";

/// A GHC `Type`, structurally.
///
/// This is the identity a type-based fact should rest on: `TyConApp` with a
/// stable `TyCon` name is GHC type compatibility, where a comparison of
/// GHC's *rendering* of the same type is textual and can be defeated by a
/// synonym, a shadowed name or a type variable instantiated out of sight.
///
/// Synonyms are expanded by the plugin (`expandTypeSynonyms`), so `String`
/// and `FilePath` both arrive here as `Con List [Con Char []]`. The
/// unexpanded rendering is kept next to every use of a type
/// ([`Binder::ty_pretty`], [`Expr::Type`]`::pretty`) for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Var(TyVarId),
    Con {
        tycon: TyConId,
        args: Vec<Ty>,
    },
    App {
        fun: Box<Ty>,
        arg: Box<Ty>,
    },
    Fun {
        mult: Box<Ty>,
        arg: Box<Ty>,
        res: Box<Ty>,
    },
    ForAll {
        binder: TyVarId,
        body: Box<Ty>,
    },
    Lit {
        kind: String,
        text: String,
    },
    /// A `CastTy` or `CoercionTy`, kept only as GHC rendered it.
    Opaque {
        pretty: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    Top,
    Application,
    Argument,
    Atom,
}

impl Ty {
    /// The type constructor at the head of a `TyConApp`, if this is one.
    pub fn tycon(&self) -> Option<&TyConId> {
        match self {
            Ty::Con { tycon, .. } => Some(tycon),
            _ => None,
        }
    }

    /// The arguments of a `TyConApp`; empty for anything else.
    pub fn args(&self) -> &[Ty] {
        match self {
            Ty::Con { args, .. } => args,
            _ => &[],
        }
    }

    /// Is this the type constructor `name`, applied to anything?
    pub fn is_tycon(&self, name: &str) -> bool {
        self.tycon().is_some_and(|t| t.name == name)
    }

    /// Is this a type *variable*? Nothing may be concluded from a type that
    /// is one: it is instantiated somewhere this module cannot see.
    pub fn is_ty_var(&self) -> bool {
        matches!(self, Ty::Var(_))
    }

    /// `Char`.
    pub fn is_char(&self) -> bool {
        self.is_tycon(CHAR_TYCON) && self.args().is_empty()
    }

    /// The element type of a list, if this is one.
    pub fn list_elem(&self) -> Option<&Ty> {
        match self {
            Ty::Con { tycon, args } if tycon.name == LIST_TYCON && args.len() == 1 => {
                Some(&args[0])
            }
            _ => None,
        }
    }

    /// Is this a list whose element type satisfies `elem`? `[Char]` is
    /// `ty.is_list_of(&|e| e.is_char())`.
    pub fn is_list_of(&self, elem: &dyn Fn(&Ty) -> bool) -> bool {
        self.list_elem().is_some_and(elem)
    }

    /// The argument types of an arrow chain, outermost first, looking
    /// through `forall`s. The result type is [`Ty::fun_result`]. Both are
    /// iterative: a signature can be long.
    pub fn fun_args(&self) -> Vec<&Ty> {
        let mut out = Vec::new();
        let mut cur = self;
        loop {
            match cur {
                Ty::Fun { arg, res, .. } => {
                    out.push(&**arg);
                    cur = res;
                }
                Ty::ForAll { body, .. } => cur = body,
                _ => return out,
            }
        }
    }

    /// What an arrow chain returns once every argument is supplied.
    pub fn fun_result(&self) -> &Ty {
        let mut cur = self;
        loop {
            match cur {
                Ty::Fun { res, .. } | Ty::ForAll { body: res, .. } => cur = res,
                _ => return cur,
            }
        }
    }

    pub fn render(&self) -> String {
        self.render_at(Precedence::Top)
    }

    fn render_at(&self, context: Precedence) -> String {
        let (text, precedence) = match self {
            Ty::Var(var) => (var.occ.clone(), Precedence::Atom),
            Ty::Con { tycon, args } if tycon.name == LIST_TYCON && args.len() == 1 => {
                (format!("[{}]", args[0].render()), Precedence::Atom)
            }
            Ty::Con { tycon, args } if tycon.occ.starts_with("(#") && !args.is_empty() => {
                let fields = &args[args.len() / 2..];
                let fields: Vec<_> = fields.iter().map(Ty::render).collect();
                (format!("(# {} #)", fields.join(", ")), Precedence::Atom)
            }
            Ty::Con { tycon, args } if tycon.occ.starts_with("(,") => {
                let fields: Vec<_> = args.iter().map(Ty::render).collect();
                (format!("({})", fields.join(", ")), Precedence::Atom)
            }
            Ty::Con { tycon, args } if args.is_empty() => (tycon.occ.clone(), Precedence::Atom),
            Ty::Con { tycon, args } => {
                let mut text = tycon.occ.clone();
                for arg in args {
                    text.push(' ');
                    text.push_str(&arg.render_at(Precedence::Argument));
                }
                (text, Precedence::Application)
            }
            Ty::App { fun, arg } => (
                format!(
                    "{} {}",
                    fun.render_at(Precedence::Application),
                    arg.render_at(Precedence::Argument)
                ),
                Precedence::Application,
            ),
            Ty::Fun { arg, res, .. } => (
                format!(
                    "{} -> {}",
                    arg.render_at(Precedence::Application),
                    res.render_at(Precedence::Top)
                ),
                Precedence::Top,
            ),
            Ty::ForAll { binder, body } => (
                format!("forall {}. {}", binder.occ, body.render()),
                Precedence::Top,
            ),
            Ty::Lit { text, .. } => (text.clone(), Precedence::Atom),
            Ty::Opaque { pretty } => (format!("({pretty})"), Precedence::Atom),
        };
        if precedence < context {
            format!("({text})")
        } else {
            text
        }
    }

    /// Alpha-equivalence: the same type up to the names of bound type
    /// variables. Bound variables are alpha-mapped here; **free type
    /// variables are compared by GHC unique and are not scope-identified**.
    /// A unique is not unique in an optimised dump (see
    /// [`Module::resolve_scopes`]), and format 5 carries no lexical
    /// identity for a *type* variable, so two free tyvars from different
    /// scopes can share a unique and compare equal. That is why this must
    /// not be used for any proof that is sensitive to free type variables
    /// until a later dump format carries lexical type-variable identity;
    /// every current caller compares closed or same-scope types.
    ///
    /// Iterative, over an explicit worklist, and over the *structured*
    /// type — the textual `alpha_normalise` M2.1 uses on rendered types is
    /// the thing this exists to replace.
    pub fn alpha_eq(&self, other: &Ty) -> bool {
        // Pairs still to compare, plus the bound-variable correspondence in
        // force at each, as a depth into `bound`.
        let mut work: Vec<(&Ty, &Ty, usize)> = vec![(self, other, 0)];
        // (left unique, right unique) pairs introduced by `forall`s.
        let mut bound: Vec<(&str, &str)> = Vec::new();
        while let Some((a, b, depth)) = work.pop() {
            bound.truncate(depth);
            match (a, b) {
                (Ty::Var(x), Ty::Var(y)) => {
                    let corr = bound
                        .iter()
                        .rev()
                        .find(|(l, r)| *l == x.unique || *r == y.unique);
                    match corr {
                        Some((l, r)) => {
                            if *l != x.unique || *r != y.unique {
                                return false;
                            }
                        }
                        None if x.unique != y.unique => return false,
                        None => {}
                    }
                }
                (
                    Ty::Con {
                        tycon: t1,
                        args: a1,
                    },
                    Ty::Con {
                        tycon: t2,
                        args: a2,
                    },
                ) => {
                    if t1.name != t2.name || a1.len() != a2.len() {
                        return false;
                    }
                    work.extend(a1.iter().zip(a2).map(|(x, y)| (x, y, depth)));
                }
                (Ty::App { fun: f1, arg: x1 }, Ty::App { fun: f2, arg: x2 }) => {
                    work.push((f1, f2, depth));
                    work.push((x1, x2, depth));
                }
                (
                    Ty::Fun {
                        mult: m1,
                        arg: a1,
                        res: r1,
                    },
                    Ty::Fun {
                        mult: m2,
                        arg: a2,
                        res: r2,
                    },
                ) => {
                    work.push((m1, m2, depth));
                    work.push((a1, a2, depth));
                    work.push((r1, r2, depth));
                }
                (
                    Ty::ForAll {
                        binder: v1,
                        body: b1,
                    },
                    Ty::ForAll {
                        binder: v2,
                        body: b2,
                    },
                ) => {
                    bound.push((v1.unique.as_str(), v2.unique.as_str()));
                    work.push((b1, b2, depth + 1));
                }
                (Ty::Lit { kind: k1, text: t1 }, Ty::Lit { kind: k2, text: t2 }) => {
                    if k1 != k2 || t1 != t2 {
                        return false;
                    }
                }
                (Ty::Opaque { pretty: p1 }, Ty::Opaque { pretty: p2 }) => {
                    if p1 != p2 {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Var {
        unique: String,
        name: String,
        occ: String,
        is_global: bool,
    },
    Lit(Lit),
    App {
        fun: ExprId,
        arg: ExprId,
    },
    Lam {
        binder: BinderId,
        body: ExprId,
    },
    Let {
        bind: Bind,
        body: ExprId,
    },
    Case {
        scrut: ExprId,
        binder: BinderId,
        /// The `case`'s result type, structurally.
        ty: TyId,
        /// …and as GHC rendered it.
        ty_pretty: String,
        alts: Vec<Alt>,
    },
    /// `Cast e co`. A coercion has no runtime content — this evaluates as `e`
    /// does — so what it carries is the two types the coercion relates and its
    /// role. Whether erasing it preserves the representation is the consumer's
    /// question, and these are the evidence for answering it. `None` on a dump
    /// taken before the plugin emitted them.
    Cast {
        expr: ExprId,
        from: Option<TyId>,
        to: Option<TyId>,
        role: Option<String>,
    },
    Tick(ExprId),
    /// A type argument: structurally, and as GHC rendered it.
    Type {
        ty: TyId,
        pretty: String,
    },
    Coercion,
}

#[derive(Debug, Clone)]
pub struct Bind {
    pub recursive: bool,
    pub pairs: Vec<Pair>,
}

#[derive(Debug, Clone)]
pub struct Pair {
    pub binder: BinderId,
    pub rhs: ExprId,
    /// GHC's `exprIsHNF`: the RHS is already a value.
    pub whnf: bool,
    /// GHC's `exprIsTrivial`: a variable, literal or type.
    pub trivial: bool,
    /// GHC's `exprIsCheap`: safe to duplicate work-wise.
    pub cheap: bool,
    /// GHC's `exprOkForSpeculation`: cannot diverge or have effects, and is
    /// cheap — safe to evaluate eagerly.
    pub ok_for_spec: bool,
}

#[derive(Debug, Clone)]
pub struct Alt {
    pub con: AltCon,
    pub binders: Vec<BinderId>,
    pub rhs: ExprId,
}

/// How a node hangs off its parent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edge {
    /// A top-level RHS; `pair` indexes into the flattened top-level pairs.
    Top {
        pair: u32,
    },
    AppFun,
    AppArg,
    LamBody,
    LetRhs {
        pair: u32,
    },
    LetBody,
    CaseScrut,
    CaseAlt {
        alt: u32,
    },
    Cast,
    Tick,
}

/// How a binder is bound. Recorded once per binder; a binder occurs at
/// exactly one binding site, so no scoping is involved.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub enum BindSite {
    Top,
    Let,
    Lam,
    CaseBinder,
    AltBinder,
}

/// Where and how a binder is bound.
#[derive(Debug, Clone, Copy)]
pub struct BindInfo {
    pub site: BindSite,
    pub binder: BinderId,
    /// The right-hand side, for let- and top-level-bound ids.
    pub rhs: Option<ExprId>,
}

/// What a `Var` occurrence refers to. This is the *identity* of a variable
/// in the IR; the GHC unique is kept for diagnostics only, and is never an
/// identity and never a key — linkage against the imported-id table goes
/// through the stable name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ref {
    /// Bound in this module, by this binder.
    Local(BinderId),
    /// An import: **nothing in this module lexically binds it**, whatever
    /// GHC's `isGlobal` bit says about the occurrence. The occurrence's
    /// **stable name** — unit, module and occurrence, as of dump format 5
    /// — is the key into [`Module::ids`]; the unique is not, and is never
    /// a key anywhere.
    Global,
}

/// A unique collision: an occurrence that resolved **lexically** to an
/// in-scope binder although its own stable name is an external name of a
/// *different* module — so it is an import that a local binder's GHC
/// unique has captured. Two distinct Ids would be sharing one unique.
///
/// This is the guard that the `isGlobal` test in [`Module::resolve_scopes`]
/// used to provide as a side effect. It is stated on the *name* the
/// occurrence already carries, against this module's own identity; nothing
/// here is keyed by a unique. The population is expected to be empty and is
/// reported on every dump (`h2r stats`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UniqueCollision {
    /// The `Var` node.
    pub occurrence: ExprId,
    /// The in-scope binder that captured it.
    pub binder: BinderId,
}

/// Split a dump-format-5 stable name `$unit$Module$occ` into its three
/// parts. `None` for a name GHC rendered without a unit and a module.
pub fn split_stable_name(name: &str) -> Option<(&str, &str, &str)> {
    let rest = name.strip_prefix('$')?;
    let (unit, rest) = rest.split_once('$')?;
    let (module, occ) = rest.split_once('$')?;
    Some((unit, module, occ))
}

/// GHC's `nameStableString` renders a *non-external* name as `$_sys$<occ>`
/// or `$_in$<occ>`, with no unit and no module. When that `<occ>` itself
/// contains a `$` the three-way split reads `_sys` as a unit, so the two
/// pseudo-units are rejected by name.
pub fn is_internal_unit(unit: &str) -> bool {
    unit == "_sys" || unit == "_in"
}

/// Is this an *external* name — one another module could refer to, and the
/// only kind that is unique in the program? An internal name is not: three
/// top-level bindings of `ShellCheck.AST` are called
/// `$_sys$$fTraversableInnerToken`. Nothing anywhere may be keyed by one.
pub fn is_external_name(name: &str) -> bool {
    split_stable_name(name)
        .is_some_and(|(u, md, _)| !u.is_empty() && !md.is_empty() && !is_internal_unit(u))
}

#[derive(Debug)]
pub struct Module {
    /// Which dump contract this module was read under: 5 (pre-CoreTidy) or
    /// 6 (post-CoreTidy). **Reported, never branched on** — `h2r stats`
    /// prints it so a report says what it read.
    pub format: u32,
    pub name: String,
    pub unit: String,
    /// Facts about the Ids this module refers to that GHC handed us as
    /// `GlobalId`s with an *external* `Name`, keyed by stable name. Read it
    /// through [`Module::id_info`], never by unique.
    ///
    /// Since the dump is taken after `CoreTidy`, the module's **own**
    /// now-external top-level binders can appear here too, when the module
    /// references them. Those entries are redundant, not harmful: such an
    /// occurrence resolves lexically ([`Ref::Local`]), and the binder — not
    /// the table — is what every signature is read from.
    pub ids: HashMap<String, IdInfo>,
    pub constructors: Vec<raw::ConstructorInfo>,
    /// The module's types, rebuilt from the dump's hash-consed table.
    /// Binders and `Type` nodes index into this.
    pub types: Vec<Ty>,
    pub exprs: Vec<Expr>,
    pub binders: Vec<Binder>,
    pub parent: Vec<Option<ExprId>>,
    pub edge: Vec<Edge>,
    pub top: Vec<Bind>,
    /// Binding site of every binder, indexed by [`BinderId`].
    binding: Vec<BindInfo>,
    /// What every `Var` occurrence refers to, indexed by [`ExprId`].
    /// `None` at a node that is not a `Var`.
    refs: Vec<Option<Ref>>,
    /// Occurrences of every binder, in pre-order, indexed by [`BinderId`].
    occurrences: Vec<Vec<ExprId>>,
    /// See [`UniqueCollision`]. Expected empty; asserted, never assumed.
    unique_collisions: Vec<UniqueCollision>,
}

impl Module {
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id as usize]
    }

    /// The literal at a node, when the node is one.
    pub fn expr_lit(&self, id: ExprId) -> Option<&Lit> {
        match self.expr(id) {
            Expr::Lit(lit) => Some(lit),
            _ => None,
        }
    }

    pub fn binder(&self, id: BinderId) -> &Binder {
        &self.binders[id as usize]
    }

    /// A type from the module's table.
    pub fn ty(&self, id: TyId) -> &Ty {
        &self.types[id as usize]
    }

    /// A binder's type, structurally.
    pub fn binder_ty(&self, id: BinderId) -> &Ty {
        self.ty(self.binders[id as usize].ty)
    }

    /// Direct children, in evaluation-ish order.
    pub fn children(&self, id: ExprId) -> Vec<ExprId> {
        match self.expr(id) {
            Expr::App { fun, arg } => vec![*fun, *arg],
            Expr::Lam { body, .. } => vec![*body],
            Expr::Let { bind, body } => {
                let mut v: Vec<ExprId> = bind.pairs.iter().map(|p| p.rhs).collect();
                v.push(*body);
                v
            }
            Expr::Case { scrut, alts, .. } => {
                let mut v = vec![*scrut];
                v.extend(alts.iter().map(|a| a.rhs));
                v
            }
            Expr::Cast { expr: e, .. } | Expr::Tick(e) => vec![*e],
            Expr::Var { .. } | Expr::Lit(_) | Expr::Type { .. } | Expr::Coercion => vec![],
        }
    }

    /// Pre-order traversal of the subtree at `root`, iterative.
    pub fn preorder(&self, root: ExprId) -> Preorder<'_> {
        Preorder {
            module: self,
            stack: vec![root],
        }
    }

    /// The path from `id` up to the root, nearest ancestor first.
    pub fn ancestors(&self, id: ExprId) -> impl Iterator<Item = ExprId> + '_ {
        let mut cur = self.parent[id as usize];
        std::iter::from_fn(move || {
            let here = cur?;
            cur = self.parent[here as usize];
            Some(here)
        })
    }

    /// Look through casts and ticks.
    pub fn strip(&self, mut id: ExprId) -> ExprId {
        loop {
            match self.expr(id) {
                Expr::Cast { expr: e, .. } | Expr::Tick(e) => id = *e,
                _ => return id,
            }
        }
    }

    /// Decompose an application spine into head and arguments (casts and
    /// ticks around the head are looked through).
    pub fn spine(&self, id: ExprId) -> (ExprId, Vec<ExprId>) {
        let mut args = Vec::new();
        let mut cur = self.strip(id);
        while let Expr::App { fun, arg } = self.expr(cur) {
            args.push(*arg);
            cur = self.strip(*fun);
        }
        args.reverse();
        (cur, args)
    }

    /// The root of the application spine `id` belongs to: the outermost
    /// `App` that reaches `id` through fun positions, looking through the
    /// casts and ticks the simplifier leaves *inside* spines. This is the
    /// exact converse of [`Module::spine`]: `spine(spine_root(id))` is the
    /// whole spine `id` sits in, and a node is a spine root iff it is its
    /// own `spine_root`.
    pub fn spine_root(&self, id: ExprId) -> ExprId {
        let mut root = id;
        let mut cur = id;
        while let Some(p) = self.parent[cur as usize] {
            match self.edge[cur as usize] {
                Edge::AppFun if matches!(self.expr(p), Expr::App { .. }) => {
                    cur = p;
                    root = p;
                }
                // A cast between two `App`s does not break the spine, but a
                // cast under anything else is where the spine ends.
                Edge::Cast | Edge::Tick => cur = p,
                _ => break,
            }
        }
        root
    }

    //--------------------------------------------------------------------------
    // Variable identity
    //--------------------------------------------------------------------------

    /// What the `Var` at `id` refers to; `None` if `id` is not a `Var`.
    pub fn reference(&self, id: ExprId) -> Option<Ref> {
        self.refs[id as usize]
    }

    /// The binder a `Var` occurrence is bound by, or `None` for an import
    /// (or a node that is not a `Var`). **The** way to identify a variable.
    pub fn resolve(&self, id: ExprId) -> Option<BinderId> {
        match self.refs[id as usize] {
            Some(Ref::Local(b)) => Some(b),
            _ => None,
        }
    }

    /// Where a binder is bound.
    pub fn binding(&self, b: BinderId) -> BindInfo {
        self.binding[b as usize]
    }

    /// The binding site of the variable at `head`, if it is bound here.
    pub fn binding_of(&self, head: ExprId) -> Option<BindInfo> {
        self.resolve(head).map(|b| self.binding(b))
    }

    /// Every occurrence of a binder, in pre-order.
    pub fn occurrences(&self, b: BinderId) -> &[ExprId] {
        &self.occurrences[b as usize]
    }

    /// The occurrences an import's stable name says should not have
    /// resolved lexically — see [`UniqueCollision`]. Expected empty.
    pub fn unique_collisions(&self) -> &[UniqueCollision] {
        &self.unique_collisions
    }

    /// Record where every binder is bound. One pass over the arena; a
    /// binder occurs at exactly one site, so no scoping is involved.
    fn index_binding_sites(&mut self) {
        let mut binding = vec![
            BindInfo {
                site: BindSite::Lam,
                binder: 0,
                rhs: None,
            };
            self.binders.len()
        ];
        let mut put = |b: BinderId, site: BindSite, rhs: Option<ExprId>| {
            binding[b as usize] = BindInfo {
                site,
                binder: b,
                rhs,
            };
        };
        for bind in &self.top {
            for p in &bind.pairs {
                put(p.binder, BindSite::Top, Some(p.rhs));
            }
        }
        for e in &self.exprs {
            match e {
                Expr::Lam { binder, .. } => put(*binder, BindSite::Lam, None),
                Expr::Let { bind, .. } => {
                    for p in &bind.pairs {
                        put(p.binder, BindSite::Let, Some(p.rhs));
                    }
                }
                Expr::Case { binder, alts, .. } => {
                    put(*binder, BindSite::CaseBinder, None);
                    for a in alts {
                        for b in &a.binders {
                            put(*b, BindSite::AltBinder, None);
                        }
                    }
                }
                _ => {}
            }
        }
        self.binding = binding;
    }

    /// Resolve every `Var` occurrence to the binder that actually binds it.
    ///
    /// This is the only place in the compiler that compares a local unique
    /// string, and the reason it has to exist: **uniques are not unique in
    /// an optimised dump**. GHC's simplifier renames a binder only when it
    /// would clash with the in-scope set, so inlining duplicates a term
    /// without freshening it — optimised Core is uniquely *scoped*, not
    /// globally unique. `ShellCheck.Parser` alone has 41,874 binders over
    /// 8,257 distinct uniques, one of which names 1,269 different binders.
    /// Everything downstream keys by [`BinderId`].
    ///
    /// Iterative: an explicit stack of enter/bind/unbind operations, so the
    /// (very deep) Core is never recursed over. The module's top-level
    /// binders are the outermost scope.
    ///
    /// **Lexical binding decides locality, not GHC's `isGlobalId` bit.** An
    /// in-scope binder wins whatever the occurrence's `isGlobal` flag says:
    /// after `CoreTidy` — which is the point the dump is taken at, see
    /// `compiler/h2r-plugin/src/H2R/CorePlugin.hs` — every top-level binder
    /// is rebuilt as a `GlobalId`, so an occurrence of a module's own
    /// top-level binding carries `isGlobal = true` and is nonetheless
    /// lexically bound here. Only an occurrence with no in-scope binder at
    /// all is an import, and resolves to [`Ref::Global`]. The flag stays in
    /// the JSON and in [`Expr::Var`] as a GHC diagnostic fact and is never
    /// the local-vs-import identity decision.
    ///
    /// The `isGlobal` test this replaced was also what kept an *import*
    /// from being captured by a same-unique local binder, so the guard it
    /// used to provide is re-established explicitly and counted:
    /// [`Module::unique_collisions`].
    fn resolve_scopes(&mut self) {
        enum Op<'a> {
            Enter(ExprId),
            Bind(BinderId),
            Unbind(&'a str),
        }
        let mut refs: Vec<Option<Ref>> = vec![None; self.exprs.len()];
        let mut occurrences: Vec<Vec<ExprId>> = vec![Vec::new(); self.binders.len()];
        let mut env: HashMap<&str, Vec<BinderId>> = HashMap::new();
        let mut stack: Vec<Op> = Vec::new();
        let mut collisions: Vec<UniqueCollision> = Vec::new();
        for bind in &self.top {
            for p in &bind.pairs {
                env.entry(self.binders[p.binder as usize].unique.as_str())
                    .or_default()
                    .push(p.binder);
            }
        }
        for bind in self.top.iter().rev() {
            for p in bind.pairs.iter().rev() {
                stack.push(Op::Enter(p.rhs));
            }
        }
        let unique = |b: BinderId| self.binders[b as usize].unique.as_str();
        while let Some(op) = stack.pop() {
            let id = match op {
                Op::Bind(b) => {
                    env.entry(unique(b)).or_default().push(b);
                    continue;
                }
                Op::Unbind(u) => {
                    if let Some(v) = env.get_mut(u) {
                        v.pop();
                    }
                    continue;
                }
                Op::Enter(id) => id,
            };
            match &self.exprs[id as usize] {
                Expr::Var {
                    unique: u, name, ..
                } => {
                    let r = match env.get(u.as_str()).and_then(|v| v.last()) {
                        Some(b) => Ref::Local(*b),
                        None => Ref::Global,
                    };
                    refs[id as usize] = Some(r);
                    if let Ref::Local(b) = r {
                        occurrences[b as usize].push(id);
                        // The collision guard. A lexically resolved
                        // occurrence whose own stable name is external and
                        // names some *other* module is an import that a
                        // local binder's unique has captured: two distinct
                        // Ids sharing one unique. Nothing here is keyed by
                        // a unique — the test is on the name the occurrence
                        // already carries against this module's identity.
                        if let Some((unit, module, _)) = split_stable_name(name)
                            && is_external_name(name)
                            && (unit != self.unit || module != self.name)
                        {
                            collisions.push(UniqueCollision {
                                occurrence: id,
                                binder: b,
                            });
                        }
                    }
                }
                Expr::App { fun, arg } => {
                    stack.push(Op::Enter(*arg));
                    stack.push(Op::Enter(*fun));
                }
                Expr::Lam { binder, body } => {
                    stack.push(Op::Unbind(unique(*binder)));
                    stack.push(Op::Enter(*body));
                    stack.push(Op::Bind(*binder));
                }
                Expr::Let { bind, body } => {
                    for p in &bind.pairs {
                        stack.push(Op::Unbind(unique(p.binder)));
                    }
                    stack.push(Op::Enter(*body));
                    if bind.recursive {
                        // A recursive group is in scope in its own RHSs.
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Enter(p.rhs));
                        }
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Bind(p.binder));
                        }
                    } else {
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Bind(p.binder));
                        }
                        for p in bind.pairs.iter().rev() {
                            stack.push(Op::Enter(p.rhs));
                        }
                    }
                }
                Expr::Case {
                    scrut,
                    binder,
                    alts,
                    ..
                } => {
                    stack.push(Op::Unbind(unique(*binder)));
                    for alt in alts.iter().rev() {
                        for b in &alt.binders {
                            stack.push(Op::Unbind(unique(*b)));
                        }
                        stack.push(Op::Enter(alt.rhs));
                        for b in alt.binders.iter().rev() {
                            stack.push(Op::Bind(*b));
                        }
                    }
                    stack.push(Op::Bind(*binder));
                    stack.push(Op::Enter(*scrut));
                }
                Expr::Cast { expr: e, .. } | Expr::Tick(e) => stack.push(Op::Enter(*e)),
                Expr::Lit(_) | Expr::Type { .. } | Expr::Coercion => {}
            }
        }
        self.refs = refs;
        self.occurrences = occurrences;
        self.unique_collisions = collisions;
    }

    /// Is `b` in scope at `occ`? Walks up from the occurrence and asks each
    /// enclosing binding construct whether it binds `b` in the edge we came
    /// through — the definition of lexical scope, independent of the
    /// resolver, so it can be used to check it.
    pub fn binder_in_scope(&self, occ: ExprId, b: BinderId) -> bool {
        let mut child = occ;
        while let Some(p) = self.parent[child as usize] {
            let edge = self.edge[child as usize];
            match (self.expr(p), edge) {
                (Expr::Lam { binder, .. }, Edge::LamBody) if *binder == b => return true,
                (Expr::Let { bind, .. }, Edge::LetBody)
                    if bind.pairs.iter().any(|x| x.binder == b) =>
                {
                    return true;
                }
                // A recursive group is in scope in its own right-hand sides.
                (Expr::Let { bind, .. }, Edge::LetRhs { .. })
                    if bind.recursive && bind.pairs.iter().any(|x| x.binder == b) =>
                {
                    return true;
                }
                (Expr::Case { binder, alts, .. }, Edge::CaseAlt { alt })
                    if *binder == b || alts[alt as usize].binders.contains(&b) =>
                {
                    return true;
                }
                _ => {}
            }
            child = p;
        }
        self.top
            .iter()
            .flat_map(|x| x.pairs.iter())
            .any(|p| p.binder == b)
    }

    /// Occurrences whose resolved binder does not lexically scope over them.
    /// Always empty for a well-formed module; the check exists so that a
    /// resolution that merges disjoint scopes cannot pass unnoticed.
    pub fn scoping_violations(&self) -> Vec<(ExprId, BinderId)> {
        let mut bad = Vec::new();
        for id in 0..self.exprs.len() as ExprId {
            if let Some(Ref::Local(b)) = self.reference(id)
                && !self.binder_in_scope(id, b)
            {
                bad.push((id, b));
            }
        }
        bad
    }

    /// Facts about the *imported* Id a `Var` refers to, if the plugin
    /// recorded any. Only defined for an occurrence the resolver classified
    /// as [`Ref::Global`] — an occurrence nothing in this module binds. For
    /// anything bound here, read the binder: it is the authoritative source
    /// and, for a module-local name, the only one.
    pub fn id_info(&self, id: ExprId) -> Option<&IdInfo> {
        match (self.expr(id), self.reference(id)) {
            (Expr::Var { name, .. }, Some(Ref::Global)) => self.ids.get(name),
            _ => None,
        }
    }

    pub fn from_raw(raw: raw::RawModule) -> Result<Self> {
        if !raw::FORMATS_ACCEPTED.contains(&raw.format) {
            bail!(
                "module {} has dump format {}, and only {:?} load: re-extract \
                 with the current plugin (`. ~/.ghcup/env; \
                 ./compiler/extract.sh`), which emits format {}. Format 5 is \
                 the pre-CoreTidy program, format 6 the post-CoreTidy one; \
                 both key the id table by stable name and carry structured \
                 types, and neither is guessed at.",
                raw.module,
                raw.format,
                raw::FORMATS_ACCEPTED,
                raw::FORMAT
            );
        }
        let types = build_types(&raw.types)?;
        let mut b = Builder::default();
        let mut top = Vec::with_capacity(raw.binds.len());
        let mut top_pair: u32 = 0;
        for bind in raw.binds {
            top.push(b.bind(bind, None, |_| {
                let e = Edge::Top { pair: top_pair };
                top_pair += 1;
                e
            }));
        }
        b.drain();
        let mut m = Module {
            format: raw.format,
            name: raw.module,
            unit: raw.unit,
            ids: raw.ids,
            constructors: raw.constructors,
            types,
            exprs: b
                .exprs
                .into_iter()
                .map(|e| e.expect("unfilled slot"))
                .collect(),
            binders: b.binders,
            parent: b.parent,
            edge: b.edge,
            top,
            binding: Vec::new(),
            refs: Vec::new(),
            occurrences: Vec::new(),
            unique_collisions: Vec::new(),
        };
        m.index_binding_sites();
        m.resolve_scopes();
        Ok(m)
    }

    /// Every type index a node carries must name an entry of this module's
    /// table. A dump that violates it is refused at [`Module::load`] rather
    /// than indexed out of bounds wherever the node is first read — which is
    /// how a plugin that dumped a type it had not interned first showed up.
    ///
    /// This guards the dump boundary. A module built in a test from JSON goes
    /// through [`Module::from_raw`] directly and is not checked: a fixture
    /// declares only the types it reads.
    fn check_type_references(&self) -> Result<()> {
        let bound = self.types.len() as TyId;
        let check = |id: Option<TyId>, what: &str, node: ExprId| -> Result<()> {
            match id {
                Some(id) if id >= bound => bail!(
                    "module {}: node {node}'s {what} type index {id} is past the \
                     table's {bound} entries",
                    self.name
                ),
                _ => Ok(()),
            }
        };
        for (node, expr) in self.exprs.iter().enumerate() {
            let node = node as ExprId;
            match expr {
                Expr::Cast { from, to, .. } => {
                    check(*from, "cast source", node)?;
                    check(*to, "cast target", node)?;
                }
                Expr::Case { ty, .. } | Expr::Type { ty, .. } => {
                    check(Some(*ty), "result", node)?;
                }
                _ => {}
            }
        }
        for (index, binder) in self.binders.iter().enumerate() {
            if binder.ty >= bound {
                bail!(
                    "module {}: binder {index}'s type index {} is past the \
                     table's {bound} entries",
                    self.name,
                    binder.ty
                );
            }
        }
        Ok(())
    }

    pub fn load(path: &Path) -> Result<Self> {
        let bytes =
            std::fs::read(path).with_context(|| format!("reading Core dump {}", path.display()))?;
        let mut de = serde_json::Deserializer::from_slice(&bytes);
        // Real Core nests far past serde_json's default limit of 128. The
        // deserialiser is still recursive, hence `with_big_stack`; it is the
        // only recursion left in the pipeline.
        de.disable_recursion_limit();
        let raw = raw::RawModule::deserialize(&mut de)
            .with_context(|| format!("parsing Core dump {}", path.display()))?;
        let module = Self::from_raw(raw)?;
        module
            .check_type_references()
            .with_context(|| format!("reading Core dump {}", path.display()))?;
        Ok(module)
    }
}

pub struct Preorder<'a> {
    module: &'a Module,
    stack: Vec<ExprId>,
}

impl Iterator for Preorder<'_> {
    type Item = ExprId;

    fn next(&mut self) -> Option<ExprId> {
        let id = self.stack.pop()?;
        let kids = self.module.children(id);
        self.stack.extend(kids.into_iter().rev());
        Some(id)
    }
}

/// Flattens raw expressions off an explicit stack. Slots are reserved when a
/// parent is processed, so children are always filled after their parent and
/// no raw node is ever visited recursively — including on drop, since each
/// raw node is destructured and its boxes moved out before it goes away.
#[derive(Default)]
struct Builder {
    exprs: Vec<Option<Expr>>,
    binders: Vec<Binder>,
    parent: Vec<Option<ExprId>>,
    edge: Vec<Edge>,
    work: Vec<(raw::RawExpr, ExprId)>,
}

impl Builder {
    fn reserve(&mut self, parent: Option<ExprId>, edge: Edge) -> ExprId {
        let id = self.exprs.len() as ExprId;
        self.exprs.push(None);
        self.parent.push(parent);
        self.edge.push(edge);
        id
    }

    fn binder(&mut self, b: Binder) -> BinderId {
        let id = self.binders.len() as BinderId;
        self.binders.push(b);
        id
    }

    fn push(&mut self, raw: raw::RawExpr, parent: Option<ExprId>, edge: Edge) -> ExprId {
        let id = self.reserve(parent, edge);
        self.work.push((raw, id));
        id
    }

    fn bind(
        &mut self,
        bind: raw::RawBind,
        parent: Option<ExprId>,
        mut edge: impl FnMut(u32) -> Edge,
    ) -> Bind {
        let pairs = bind
            .pairs
            .into_iter()
            .enumerate()
            .map(|(i, p)| {
                let binder = self.binder(p.binder);
                let rhs = self.push(p.rhs, parent, edge(i as u32));
                Pair {
                    binder,
                    rhs,
                    whnf: p.whnf,
                    trivial: p.trivial,
                    cheap: p.cheap,
                    ok_for_spec: p.ok_for_spec,
                }
            })
            .collect();
        Bind {
            recursive: bind.recursive,
            pairs,
        }
    }

    fn drain(&mut self) {
        while let Some((raw, id)) = self.work.pop() {
            let p = Some(id);
            let expr = match raw {
                raw::RawExpr::Var {
                    name,
                    occ,
                    unique,
                    is_global,
                } => Expr::Var {
                    unique,
                    name,
                    occ,
                    is_global,
                },
                raw::RawExpr::Lit { lit } => Expr::Lit(lit),
                raw::RawExpr::App { fun, arg } => {
                    let fun = self.push(*fun, p, Edge::AppFun);
                    let arg = self.push(*arg, p, Edge::AppArg);
                    Expr::App { fun, arg }
                }
                raw::RawExpr::Lam { binder, body } => {
                    let binder = self.binder(binder);
                    let body = self.push(*body, p, Edge::LamBody);
                    Expr::Lam { binder, body }
                }
                raw::RawExpr::Let { bind, body } => {
                    let bind = self.bind(bind, p, |i| Edge::LetRhs { pair: i });
                    let body = self.push(*body, p, Edge::LetBody);
                    Expr::Let { bind, body }
                }
                raw::RawExpr::Case {
                    scrut,
                    binder,
                    ty,
                    ty_pretty,
                    alts,
                } => {
                    let scrut = self.push(*scrut, p, Edge::CaseScrut);
                    let binder = self.binder(binder);
                    let alts = alts
                        .into_iter()
                        .enumerate()
                        .map(|(i, a)| Alt {
                            con: a.con,
                            binders: a.binders.into_iter().map(|b| self.binder(b)).collect(),
                            rhs: self.push(a.rhs, p, Edge::CaseAlt { alt: i as u32 }),
                        })
                        .collect();
                    Expr::Case {
                        scrut,
                        binder,
                        ty,
                        ty_pretty,
                        alts,
                    }
                }
                raw::RawExpr::Cast {
                    expr,
                    from,
                    to,
                    role,
                } => Expr::Cast {
                    expr: self.push(*expr, p, Edge::Cast),
                    from,
                    to,
                    role: role.clone(),
                },
                raw::RawExpr::Tick { expr } => Expr::Tick(self.push(*expr, p, Edge::Tick)),
                raw::RawExpr::Type { ty, pretty } => Expr::Type { ty, pretty },
                raw::RawExpr::Coercion => Expr::Coercion,
            };
            self.exprs[id as usize] = Some(expr);
        }
    }
}

/// Rebuild the module's types from the dump's flat, hash-consed table.
///
/// One forward pass, no recursion: the plugin interns a node only after its
/// children, so every child index is smaller than its parent's and is
/// already built by the time it is needed. An index that is not — a
/// corrupt or hand-written dump — is an error rather than a panic.
fn build_types(raw: &[raw::RawTy]) -> Result<Vec<Ty>> {
    let mut out: Vec<Ty> = Vec::with_capacity(raw.len());
    for (i, t) in raw.iter().enumerate() {
        let get = |j: &TyId| -> Result<Ty> {
            out.get(*j as usize)
                .cloned()
                .ok_or_else(|| anyhow::anyhow!("type table entry {i} refers forward to {j}"))
        };
        out.push(match t {
            raw::RawTy::TyVar { name, occ, unique } => Ty::Var(TyVarId {
                name: name.clone(),
                occ: occ.clone(),
                unique: unique.clone(),
            }),
            raw::RawTy::TyConApp { tycon, args } => Ty::Con {
                tycon: tycon.clone(),
                args: args.iter().map(&get).collect::<Result<Vec<_>>>()?,
            },
            raw::RawTy::AppTy { fun, arg } => Ty::App {
                fun: Box::new(get(fun)?),
                arg: Box::new(get(arg)?),
            },
            raw::RawTy::FunTy { mult, arg, res } => Ty::Fun {
                mult: Box::new(get(mult)?),
                arg: Box::new(get(arg)?),
                res: Box::new(get(res)?),
            },
            raw::RawTy::ForAllTy { binder, body } => Ty::ForAll {
                binder: binder.clone(),
                body: Box::new(get(body)?),
            },
            raw::RawTy::LitTy { lit_kind, lit } => Ty::Lit {
                kind: lit_kind.clone(),
                text: lit.clone(),
            },
            raw::RawTy::Opaque { pretty } => Ty::Opaque {
                pretty: pretty.clone(),
            },
        });
    }
    Ok(out)
}

/// Load every `*.core.json` under `dir`, sorted by module name.
pub fn load_dir(dir: &Path) -> Result<Vec<Module>> {
    let mut paths: Vec<PathBuf> = walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.to_string_lossy().ends_with(".core.json"))
        .collect();
    paths.sort();
    if paths.is_empty() {
        bail!("no *.core.json dumps under {}", dir.display());
    }

    let mut modules = Vec::with_capacity(paths.len());
    for path in paths {
        modules.push(Module::load(&path)?);
    }
    modules.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(modules)
}

/// A program's modules and the library modules loaded beside it.
pub struct Dumps {
    pub modules: Vec<Module>,
    /// Names of the modules that came from a library directory.
    pub libraries: BTreeSet<String>,
}

impl Dumps {
    pub fn is_library(&self, module: usize) -> bool {
        self.libraries.contains(&self.modules[module].name)
    }
}

/// Load a program's dumps together with the dumps of libraries compiled
/// beside it, as one world. A module name two directories both define is an
/// error: modules are told apart by name.
pub fn load_dirs(dir: &Path, with: &[PathBuf]) -> Result<Dumps> {
    let mut modules = load_dir(dir)?;
    let mut libraries = BTreeSet::new();
    for library in with {
        let loaded = load_dir(library)?;
        libraries.extend(loaded.iter().map(|module| module.name.clone()));
        modules.extend(loaded);
    }
    modules.sort_by(|a, b| a.name.cmp(&b.name));
    if let Some(pair) = modules.windows(2).find(|pair| pair[0].name == pair[1].name) {
        bail!("module {} is defined by more than one dump", pair[0].name);
    }
    Ok(Dumps { modules, libraries })
}

/// Run `f` on a thread with a large stack.
///
/// Only JSON deserialisation still recurses; everything after it is
/// worklist-driven. This keeps that one recursion from overflowing.
pub fn with_big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> Result<T> {
    const STACK: usize = 1 << 30; // 1 GiB, lazily committed
    std::thread::Builder::new()
        .name("h2r-deep".into())
        .stack_size(STACK)
        .spawn(f)
        .context("spawning worker thread")?
        .join()
        .map_err(|payload| anyhow::anyhow!("worker thread panicked: {}", panic_message(&*payload)))
}

pub fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    payload
        .downcast_ref::<&str>()
        .map(|message| (*message).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "a non-string panic payload".into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binder(occ: &str, uniq: &str) -> serde_json::Value {
        serde_json::json!({
            "kind": "id", "name": occ, "occ": occ, "unique": uniq, "type": "T", "ty": 0,
            "arity": 0, "callArity": 0, "exported": false,
            "dmdSig": {"args": [], "diverges": false, "pretty": ""},
            "cprSig": "", "demand": {"strict": false, "absent": false, "usedOnce": false, "pretty": "L"},
            "occInfo": {"kind": "many", "tailCalled": false}, "oneShot": false,
            "details": "", "hasUnfolding": false, "isJoinPoint": false, "isDataCon": false
        })
    }

    fn var(occ: &str, uniq: &str) -> serde_json::Value {
        serde_json::json!({"node": "Var", "name": occ, "occ": occ, "unique": uniq, "isGlobal": false})
    }

    /// let x = f a in case p of { A -> x; B -> g x }
    fn sample() -> raw::RawModule {
        let rhs = serde_json::json!({"node": "App", "fun": var("f", "f"), "arg": var("a", "a")});
        let body = serde_json::json!({
            "node": "Case", "scrut": var("p", "p"), "binder": binder("wild", "w"), "type": "R", "ty": 0,
            "alts": [
                {"con": {"kind": "DataAlt", "name": "A", "occ": "A", "tag": 1}, "binders": [], "rhs": var("x", "x")},
                {"con": {"kind": "DataAlt", "name": "B", "occ": "B", "tag": 2}, "binders": [],
                 "rhs": {"node": "App", "fun": var("g", "g"), "arg": var("x", "x")}}
            ]
        });
        let m = serde_json::json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": {},
            "types": [{"kind": "TyConApp",
                       "tycon": {"name": "$main$M$T", "occ": "T", "unique": "T"},
                       "args": []}],
            "binds": [{"rec": false, "pairs": [{
                "binder": binder("top", "t"),
                "rhs": {"node": "Let", "bind": {"rec": false, "pairs": [{
                    "binder": binder("x", "x"), "rhs": rhs,
                    "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
                }]}, "body": body},
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}]
        });
        serde_json::from_value(m).unwrap()
    }

    #[test]
    fn flattens_with_parents_and_edges() {
        let m = Module::from_raw(sample()).unwrap();
        // Let, App(f a) = 3, Case = 1, p, x, App(g x) = 3  => 1 + 3 + 1 + 1 + 1 + 3 = 10
        assert_eq!(m.exprs.len(), 10);
        let let_id = m.top[0].pairs[0].rhs;
        assert!(matches!(m.expr(let_id), Expr::Let { .. }));
        assert_eq!(m.parent[let_id as usize], None);
        assert_eq!(m.edge[let_id as usize], Edge::Top { pair: 0 });

        let Expr::Let { bind, body } = m.expr(let_id) else {
            unreachable!()
        };
        let rhs = bind.pairs[0].rhs;
        assert_eq!(m.parent[rhs as usize], Some(let_id));
        assert_eq!(m.edge[rhs as usize], Edge::LetRhs { pair: 0 });
        assert_eq!(m.edge[*body as usize], Edge::LetBody);

        let Expr::Case { alts, .. } = m.expr(*body) else {
            unreachable!()
        };
        assert_eq!(m.edge[alts[1].rhs as usize], Edge::CaseAlt { alt: 1 });

        // Every node is reachable exactly once from the root.
        let mut seen: Vec<ExprId> = m.preorder(let_id).collect();
        seen.sort();
        assert_eq!(seen, (0..10).collect::<Vec<_>>());

        // Spine decomposition.
        let (head, args) = m.spine(rhs);
        assert!(matches!(m.expr(head), Expr::Var { occ, .. } if occ == "f"));
        assert_eq!(args.len(), 1);

        // Ancestors of the `x` in branch B: App, Case, Let.
        let x_in_b = m.children(alts[1].rhs)[1];
        let anc: Vec<_> = m.ancestors(x_in_b).collect();
        assert_eq!(anc, vec![alts[1].rhs, *body, let_id]);
    }

    /// Two disjoint scopes whose binders share a unique — what optimised
    /// Core is full of, because GHC freshens a binder only when it would
    /// clash with the *in-scope* set. Each occurrence must resolve to the
    /// binder of its own scope.
    ///
    /// The naive alternative (a unique -> binder map) is built here too, so
    /// the test has teeth: it fails the scope check, which is the bug this
    /// resolution exists to prevent.
    #[test]
    fn disjoint_scopes_sharing_a_unique_resolve_separately() {
        // case p of
        //   A -> let x@u = f a in x
        //   B -> let x@u = f a in x        -- same unique, different binder
        let arm = || {
            serde_json::json!({"node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("x", "u"),
                "rhs": {"node": "App", "fun": var("f", "f"), "arg": var("a", "a")},
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}, "body": var("x", "u")})
        };
        let body = serde_json::json!({
            "node": "Case", "scrut": var("p", "p"), "binder": binder("wild", "w"), "type": "R", "ty": 0,
            "alts": [
                {"con": {"kind": "DataAlt", "name": "A", "occ": "A", "tag": 1}, "binders": [], "rhs": arm()},
                {"con": {"kind": "DataAlt", "name": "B", "occ": "B", "tag": 2}, "binders": [], "rhs": arm()}
            ]
        });
        let raw = serde_json::json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": {},
            "types": [{"kind": "TyConApp",
                       "tycon": {"name": "$main$M$T", "occ": "T", "unique": "T"},
                       "args": []}],
            "binds": [{"rec": false, "pairs": [{
                "binder": binder("top", "t"), "rhs": body,
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}]
        });
        let m = Module::from_raw(serde_json::from_value(raw).unwrap()).unwrap();

        assert!(m.scoping_violations().is_empty());

        // The two `x` binders share a unique and are different binders,
        // each with exactly one occurrence — not one binder with two.
        let lets: Vec<BinderId> = m
            .exprs
            .iter()
            .filter_map(|e| match e {
                Expr::Let { bind, .. } => Some(bind.pairs[0].binder),
                _ => None,
            })
            .collect();
        assert_eq!(lets.len(), 2);
        assert_ne!(lets[0], lets[1]);
        assert_eq!(m.binder(lets[0]).unique, m.binder(lets[1]).unique);
        assert_eq!(m.occurrences(lets[0]).len(), 1);
        assert_eq!(m.occurrences(lets[1]).len(), 1);
        assert!(m.binder_in_scope(m.occurrences(lets[0])[0], lets[0]));
        assert!(!m.binder_in_scope(m.occurrences(lets[0])[0], lets[1]));

        // Keying by unique instead (last writer wins, as a HashMap does)
        // sends at least one occurrence to a binder from a disjoint scope.
        let mut by_unique: HashMap<&str, BinderId> = HashMap::new();
        for e in &m.exprs {
            if let Expr::Let { bind, .. } = e {
                for p in &bind.pairs {
                    by_unique.insert(m.binder(p.binder).unique.as_str(), p.binder);
                }
            }
        }
        let naive_violations = (0..m.exprs.len() as ExprId)
            .filter(|id| matches!(m.reference(*id), Some(Ref::Local(_))))
            .filter_map(|id| match m.expr(id) {
                Expr::Var { unique, .. } => by_unique.get(unique.as_str()).map(|b| (id, *b)),
                _ => None,
            })
            .filter(|(id, b)| !m.binder_in_scope(*id, *b))
            .count();
        assert!(
            naive_violations > 0,
            "the unique-keyed lookup this replaces must fail the same check"
        );
    }

    /// A `Var` with an explicit `isGlobal` and a stable name of this
    /// module's own — what every occurrence of a module-local top-level
    /// binding looks like once `CoreTidy` has globalised the binders.
    fn gvar(name: &str, occ: &str, uniq: &str) -> serde_json::Value {
        serde_json::json!({"node": "Var", "name": name, "occ": occ, "unique": uniq, "isGlobal": true})
    }

    /// One top-level binding `top`, whose right-hand side is `body`.
    fn one_top(body: serde_json::Value) -> raw::RawModule {
        let raw = serde_json::json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": {},
            "types": [{"kind": "TyConApp",
                       "tycon": {"name": "$main$M$T", "occ": "T", "unique": "T"},
                       "args": []}],
            "binds": [{"rec": false, "pairs": [{
                "binder": binder("top", "t"), "rhs": body,
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}]
        });
        serde_json::from_value(raw).unwrap()
    }

    /// **Lexical binding decides locality, not `isGlobalId`.** An
    /// occurrence GHC flagged `isGlobal` that a binder in scope binds is
    /// that binder's, because after `CoreTidy` every top-level binder is a
    /// `GlobalId` and the dump is taken there.
    #[test]
    fn an_is_global_occurrence_with_an_in_scope_binder_is_local() {
        // let x@u = f a in x@u, with the occurrence flagged isGlobal.
        let m = Module::from_raw(one_top(serde_json::json!({
            "node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("x", "u"),
                "rhs": {"node": "App", "fun": var("f", "f"), "arg": var("a", "a")},
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]},
            "body": gvar("$main$M$x", "x", "u")
        })))
        .unwrap();
        let Expr::Let { bind, body } = m.expr(m.top[0].pairs[0].rhs) else {
            unreachable!()
        };
        let x = bind.pairs[0].binder;
        assert_eq!(m.reference(*body), Some(Ref::Local(x)));
        assert_eq!(m.occurrences(x), &[*body]);
        assert!(m.scoping_violations().is_empty());
        assert!(m.unique_collisions().is_empty());
    }

    /// …and the same occurrence with **no** binder in scope is an import.
    #[test]
    fn an_is_global_occurrence_without_an_in_scope_binder_is_global() {
        let m = Module::from_raw(one_top(gvar("$base$GHC.Base$id", "id", "u"))).unwrap();
        let body = m.top[0].pairs[0].rhs;
        assert_eq!(m.reference(body), Some(Ref::Global));
        assert!(m.unique_collisions().is_empty());
    }

    /// A module's own top-level binder, referenced from another top-level
    /// right-hand side by its post-tidy external name: an `A2` edge, not an
    /// `A3` one, and not a collision.
    #[test]
    fn a_reference_to_an_own_top_level_binding_resolves_lexically() {
        let raw = serde_json::json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": {},
            "types": [{"kind": "TyConApp",
                       "tycon": {"name": "$main$M$T", "occ": "T", "unique": "T"},
                       "args": []}],
            "binds": [
                {"rec": false, "pairs": [{
                    "binder": binder("f", "f1"), "rhs": var("a", "a"),
                    "whnf": false, "trivial": false, "cheap": false, "okForSpec": false}]},
                {"rec": false, "pairs": [{
                    "binder": binder("g", "g1"), "rhs": gvar("$main$M$f", "f", "f1"),
                    "whnf": false, "trivial": false, "cheap": false, "okForSpec": false}]}
            ]
        });
        let m = Module::from_raw(serde_json::from_value(raw).unwrap()).unwrap();
        let f = m.top[0].pairs[0].binder;
        let g_rhs = m.top[1].pairs[0].rhs;
        assert_eq!(m.reference(g_rhs), Some(Ref::Local(f)));
        assert_eq!(m.binding(f).site, BindSite::Top);
        assert!(m.unique_collisions().is_empty());
    }

    /// **The collision guard.** An occurrence whose stable name is an
    /// external name of *another* module cannot legitimately be bound
    /// here; if a local binder's unique captures it, that is a unique
    /// collision between an import and a local, and it is counted.
    #[test]
    fn the_collision_guard_fires_on_an_import_captured_by_a_local() {
        // let x@u = f a in <$base$GHC.Base$id>@u  -- an import's name on
        // an occurrence whose unique the local `x` owns.
        let m = Module::from_raw(one_top(serde_json::json!({
            "node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("x", "u"),
                "rhs": {"node": "App", "fun": var("f", "f"), "arg": var("a", "a")},
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]},
            "body": gvar("$base$GHC.Base$id", "id", "u")
        })))
        .unwrap();
        let Expr::Let { bind, body } = m.expr(m.top[0].pairs[0].rhs) else {
            unreachable!()
        };
        assert_eq!(
            m.unique_collisions(),
            &[UniqueCollision {
                occurrence: *body,
                binder: bind.pairs[0].binder
            }]
        );
        // An *internal* name resolving locally is not a collision: it
        // names nothing outside this module and claims no other module.
        let m2 = Module::from_raw(one_top(serde_json::json!({
            "node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("x", "u"),
                "rhs": var("a", "a"),
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]},
            "body": gvar("$_in$x", "x", "u")
        })))
        .unwrap();
        assert!(m2.unique_collisions().is_empty());
    }

    #[test]
    fn rejects_other_formats() {
        let mut raw = sample();
        raw.format = 1;
        assert!(Module::from_raw(raw).is_err());
    }

    /// The previous format is rejected, and the message says what to do
    /// about it rather than only that a number did not match.
    #[test]
    fn rejects_the_previous_format_with_an_actionable_message() {
        let mut raw = sample();
        raw.format = 4;
        let err = Module::from_raw(raw).unwrap_err().to_string();
        assert!(err.contains("dump format 4"), "{err}");
        assert!(err.contains("extract.sh"), "{err}");
    }

    //--------------------------------------------------------------------------
    // Structured types
    //--------------------------------------------------------------------------

    fn con(name: &str, args: Vec<Ty>) -> Ty {
        Ty::Con {
            tycon: TyConId {
                name: name.to_string(),
                occ: name.rsplit('$').next().unwrap().to_string(),
                unique: name.to_string(),
            },
            args,
        }
    }

    fn tv(u: &str) -> TyVarId {
        TyVarId {
            name: format!("$_in${u}"),
            occ: u.to_string(),
            unique: u.to_string(),
        }
    }

    fn char_ty() -> Ty {
        con(CHAR_TYCON, vec![])
    }

    fn list_ty(e: Ty) -> Ty {
        con(LIST_TYCON, vec![e])
    }

    #[test]
    fn rendering_brackets_only_where_precedence_needs_it() {
        let int = con("$ghc-prim$GHC.Types$Int", vec![]);
        let maybe = |t| con("$base$GHC.Maybe$Maybe", vec![t]);
        let arrow = |arg, res| Ty::Fun {
            mult: Box::new(con("$ghc-prim$GHC.Types$Many", vec![])),
            arg: Box::new(arg),
            res: Box::new(res),
        };
        let pair = con(
            "$ghc-prim$GHC.Tuple.Prim$(,)",
            vec![list_ty(char_ty()), maybe(maybe(int.clone()))],
        );
        assert_eq!(pair.render(), "([Char], Maybe (Maybe Int))");
        let higher = arrow(arrow(int.clone(), int.clone()), maybe(int.clone()));
        assert_eq!(higher.render(), "(Int -> Int) -> Maybe Int");
        assert_eq!(maybe(higher).render(), "Maybe ((Int -> Int) -> Maybe Int)");
        let rep = con("$ghc-prim$GHC.Types$LiftedRep", vec![]);
        let unboxed = con(
            "$ghc-prim$GHC.Prim$(#,#)",
            vec![rep.clone(), rep, int.clone(), char_ty()],
        );
        assert_eq!(unboxed.render(), "(# Int, Char #)");
    }

    #[test]
    fn a_list_of_char_is_recognised_by_tycon_not_by_spelling() {
        let s = list_ty(char_ty());
        assert!(s.is_list_of(&|e| e.is_char()));
        assert!(s.list_elem().unwrap().is_char());
        assert_eq!(s.tycon().unwrap().name, LIST_TYCON);

        // A different `TyCon` that merely *renders* the same way is not it.
        let impostor = con("$some-pkg$Other$List", vec![char_ty()]);
        assert!(!impostor.is_list_of(&|e| e.is_char()));
        // …and neither is a list of something else, or a bare `Char`.
        assert!(!list_ty(Ty::Var(tv("a"))).is_list_of(&|e| e.is_char()));
        assert!(!char_ty().is_list_of(&|e| e.is_char()));
        assert!(Ty::Var(tv("a")).is_ty_var());
        assert!(!s.is_ty_var());
    }

    #[test]
    fn fun_args_peels_arrows_and_foralls() {
        // forall a. a -> [Char] -> Int
        let int = con("$ghc-prim$GHC.Types$Int", vec![]);
        let arrow = |a: Ty, r: Ty| Ty::Fun {
            mult: Box::new(con("$ghc-prim$GHC.Types$Many", vec![])),
            arg: Box::new(a),
            res: Box::new(r),
        };
        let t = Ty::ForAll {
            binder: tv("a"),
            body: Box::new(arrow(
                Ty::Var(tv("a")),
                arrow(list_ty(char_ty()), int.clone()),
            )),
        };
        let args = t.fun_args();
        assert_eq!(args.len(), 2);
        assert!(args[0].is_ty_var());
        assert!(args[1].is_list_of(&|e| e.is_char()));
        assert_eq!(*t.fun_result(), int);
        assert!(int.fun_args().is_empty());
    }

    #[test]
    fn alpha_equivalence_is_up_to_bound_variable_names_only() {
        let mk = |u: &str| Ty::ForAll {
            binder: tv(u),
            body: Box::new(list_ty(Ty::Var(tv(u)))),
        };
        assert!(mk("a").alpha_eq(&mk("b")), "bound names do not matter");
        assert!(!mk("a").alpha_eq(&list_ty(Ty::Var(tv("a")))));

        // Free variables are *not* interchangeable: they are bound
        // somewhere this type does not reach.
        assert!(!list_ty(Ty::Var(tv("a"))).alpha_eq(&list_ty(Ty::Var(tv("b")))));
        assert!(list_ty(Ty::Var(tv("a"))).alpha_eq(&list_ty(Ty::Var(tv("a")))));

        // forall a b. (a, b) is not forall a b. (b, a).
        let pair = |x: &str, y: &str| Ty::ForAll {
            binder: tv("a"),
            body: Box::new(Ty::ForAll {
                binder: tv("b"),
                body: Box::new(con(
                    "$ghc-prim$GHC.Tuple.Prim$(,)",
                    vec![Ty::Var(tv(x)), Ty::Var(tv(y))],
                )),
            }),
        };
        assert!(pair("a", "b").alpha_eq(&pair("a", "b")));
        assert!(!pair("a", "b").alpha_eq(&pair("b", "a")));
        assert!(!char_ty().alpha_eq(&list_ty(char_ty())));
    }

    /// The type table is a DAG with every child before its parent, so it
    /// rebuilds in one forward pass. A dump that violates that is an error,
    /// not a panic and not a silently wrong type.
    #[test]
    fn a_forward_reference_in_the_type_table_is_an_error() {
        let bad: Vec<raw::RawTy> = serde_json::from_value(serde_json::json!([
            {"kind": "TyConApp",
             "tycon": {"name": LIST_TYCON, "occ": "List", "unique": "3Q"},
             "args": [1]},
            {"kind": "TyConApp",
             "tycon": {"name": CHAR_TYCON, "occ": "Char", "unique": "3g"},
             "args": []}
        ]))
        .unwrap();
        let err = build_types(&bad).unwrap_err().to_string();
        assert!(err.contains("refers forward"), "{err}");
    }
}
