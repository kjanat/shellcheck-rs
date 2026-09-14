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

    /// Facts about the Id a `Var` refers to, if the plugin recorded any.
    pub fn id_info(&self, id: ExprId) -> Option<&IdInfo> {
        match self.expr(id) {
            Expr::Var { unique, .. } => self.ids.get(unique),
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
        Ok(Module {
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
        })
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

    #[test]
    fn rejects_other_formats() {
        let mut raw = sample();
        raw.format = 1;
        assert!(Module::from_raw(raw).is_err());
    }
}
