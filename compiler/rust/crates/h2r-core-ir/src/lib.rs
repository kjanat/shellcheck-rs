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

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use serde::Deserialize;

pub use raw::{AltCon, Binder, BinderKind, DataConInfo, Demand, DmdSig, IdInfo, Lit, OccInfo};

pub type ExprId = u32;
pub type BinderId = u32;

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
        ty: String,
        alts: Vec<Alt>,
    },
    Cast(ExprId),
    Tick(ExprId),
    Type(String),
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
/// in the IR; the GHC unique is kept for diagnostics and for linking against
/// the imported-id table, and is never an identity anywhere else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ref {
    /// Bound in this module, by this binder.
    Local(BinderId),
    /// An import: nothing in this module binds it. The unique on the
    /// occurrence is the key into [`Module::ids`].
    Global,
}

#[derive(Debug)]
pub struct Module {
    pub name: String,
    pub unit: String,
    pub ids: HashMap<String, IdInfo>,
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
}

impl Module {
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id as usize]
    }

    pub fn binder(&self, id: BinderId) -> &Binder {
        &self.binders[id as usize]
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
            Expr::Cast(e) | Expr::Tick(e) => vec![*e],
            Expr::Var { .. } | Expr::Lit(_) | Expr::Type(_) | Expr::Coercion => vec![],
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
                Expr::Cast(e) | Expr::Tick(e) => id = *e,
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
    /// binders are the outermost scope; module-level binders are `LocalId`s
    /// all the way through the Core pipeline, so an occurrence flagged
    /// `isGlobal` is an import and resolves to [`Ref::Global`].
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
                    unique: u,
                    is_global,
                    ..
                } => {
                    let r = match env.get(u.as_str()).and_then(|v| v.last()) {
                        Some(b) if !*is_global => Ref::Local(*b),
                        _ => Ref::Global,
                    };
                    refs[id as usize] = Some(r);
                    if let Ref::Local(b) = r {
                        occurrences[b as usize].push(id);
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
                Expr::Cast(e) | Expr::Tick(e) => stack.push(Op::Enter(*e)),
                Expr::Lit(_) | Expr::Type(_) | Expr::Coercion => {}
            }
        }
        self.refs = refs;
        self.occurrences = occurrences;
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
    /// as [`Ref::Global`]: the id table is keyed by unique and populated
    /// from occurrences, so for a local it may name a different binder
    /// altogether. For a local, read the binder.
    pub fn id_info(&self, id: ExprId) -> Option<&IdInfo> {
        match (self.expr(id), self.reference(id)) {
            (Expr::Var { unique, .. }, Some(Ref::Global)) => self.ids.get(unique),
            _ => None,
        }
    }

    pub fn from_raw(raw: raw::RawModule) -> Result<Self> {
        if raw.format != raw::FORMAT {
            bail!(
                "module {} has dump format {}, expected {}",
                raw.module,
                raw.format,
                raw::FORMAT
            );
        }
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
            name: raw.module,
            unit: raw.unit,
            ids: raw.ids,
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
        };
        m.index_binding_sites();
        m.resolve_scopes();
        Ok(m)
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
        Self::from_raw(raw)
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
                        alts,
                    }
                }
                raw::RawExpr::Cast { expr } => Expr::Cast(self.push(*expr, p, Edge::Cast)),
                raw::RawExpr::Tick { expr } => Expr::Tick(self.push(*expr, p, Edge::Tick)),
                raw::RawExpr::Type { ty } => Expr::Type(ty),
                raw::RawExpr::Coercion => Expr::Coercion,
            };
            self.exprs[id as usize] = Some(expr);
        }
    }
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
        .map_err(|_| anyhow::anyhow!("worker thread panicked"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binder(occ: &str, uniq: &str) -> serde_json::Value {
        serde_json::json!({
            "kind": "id", "name": occ, "occ": occ, "unique": uniq, "type": "T",
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
            "node": "Case", "scrut": var("p", "p"), "binder": binder("wild", "w"), "type": "R",
            "alts": [
                {"con": {"kind": "DataAlt", "name": "A", "occ": "A", "tag": 1}, "binders": [], "rhs": var("x", "x")},
                {"con": {"kind": "DataAlt", "name": "B", "occ": "B", "tag": 2}, "binders": [],
                 "rhs": {"node": "App", "fun": var("g", "g"), "arg": var("x", "x")}}
            ]
        });
        let m = serde_json::json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": {},
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
            "node": "Case", "scrut": var("p", "p"), "binder": binder("wild", "w"), "type": "R",
            "alts": [
                {"con": {"kind": "DataAlt", "name": "A", "occ": "A", "tag": 1}, "binders": [], "rhs": arm()},
                {"con": {"kind": "DataAlt", "name": "B", "occ": "B", "tag": 2}, "binders": [], "rhs": arm()}
            ]
        });
        let raw = serde_json::json!({
            "format": raw::FORMAT, "module": "M", "unit": "main", "ids": {},
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

    #[test]
    fn rejects_other_formats() {
        let mut raw = sample();
        raw.format = 1;
        assert!(Module::from_raw(raw).is_err());
    }
}
