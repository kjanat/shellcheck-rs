//! Deserialisation of the GHC Core JSON emitted by `h2r-plugin`.
//!
//! This mirrors, one-to-one, what the plugin writes after GHC's full
//! optimisation pipeline has run. Nothing here interprets Core yet; it is the
//! shared input format for the later strictness-normalisation and codegen
//! passes.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct CoreModule {
    pub format: u32,
    pub module: String,
    pub unit: String,
    pub binds: Vec<Bind>,
}

#[derive(Debug, Deserialize)]
pub struct Bind {
    #[serde(rename = "rec")]
    pub recursive: bool,
    pub pairs: Vec<Pair>,
}

#[derive(Debug, Deserialize)]
pub struct Pair {
    pub binder: Binder,
    pub rhs: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BinderKind {
    Id,
    Tyvar,
}

/// A Core binder. The `Id`-only fields are `None` for type variables.
#[derive(Debug, Deserialize)]
pub struct Binder {
    pub kind: BinderKind,
    pub name: String,
    pub occ: String,
    pub unique: String,
    #[serde(rename = "type")]
    pub ty: String,

    pub arity: Option<u32>,
    #[serde(rename = "callArity")]
    pub call_arity: Option<u32>,
    pub exported: Option<bool>,
    /// GHC's demand signature, e.g. `<1L><S!P(L)>`. The backend reads this to
    /// decide whether a parameter can be passed eagerly.
    #[serde(rename = "dmdSig")]
    pub dmd_sig: Option<String>,
    #[serde(rename = "cprSig")]
    pub cpr_sig: Option<String>,
    /// How *this* binder is demanded at its binding site.
    pub demand: Option<String>,
    #[serde(rename = "occInfo")]
    pub occ_info: Option<String>,
    pub details: Option<String>,
    #[serde(rename = "hasUnfolding")]
    pub has_unfolding: Option<bool>,
    #[serde(rename = "isJoinPoint")]
    pub is_join_point: Option<bool>,
    #[serde(rename = "isDataCon")]
    pub is_data_con: Option<bool>,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "node")]
pub enum Expr {
    Var {
        name: String,
        occ: String,
        unique: String,
        #[serde(rename = "isGlobal")]
        is_global: bool,
    },
    Lit {
        lit: Lit,
    },
    App {
        fun: Box<Expr>,
        arg: Box<Expr>,
    },
    Lam {
        binder: Binder,
        body: Box<Expr>,
    },
    Let {
        bind: Bind,
        body: Box<Expr>,
    },
    Case {
        scrut: Box<Expr>,
        binder: Binder,
        #[serde(rename = "type")]
        ty: String,
        alts: Vec<Alt>,
    },
    Cast {
        expr: Box<Expr>,
    },
    Tick {
        expr: Box<Expr>,
    },
    Type {
        #[serde(rename = "type")]
        ty: String,
    },
    Coercion,
}

#[derive(Debug, Deserialize)]
pub struct Alt {
    pub con: AltCon,
    pub binders: Vec<Binder>,
    pub rhs: Expr,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind")]
pub enum AltCon {
    DataAlt {
        name: String,
        occ: String,
        tag: String,
    },
    LitAlt {
        lit: Lit,
    },
    #[serde(rename = "DEFAULT")]
    Default,
}

#[derive(Debug, Deserialize)]
pub struct Lit {
    pub kind: String,
    pub pretty: String,
}

impl Expr {
    /// The Core constructor name, for histograms and debugging.
    pub fn node_name(&self) -> &'static str {
        match self {
            Expr::Var { .. } => "Var",
            Expr::Lit { .. } => "Lit",
            Expr::App { .. } => "App",
            Expr::Lam { .. } => "Lam",
            Expr::Let { .. } => "Let",
            Expr::Case { .. } => "Case",
            Expr::Cast { .. } => "Cast",
            Expr::Tick { .. } => "Tick",
            Expr::Type { .. } => "Type",
            Expr::Coercion => "Coercion",
        }
    }

    /// Pre-order walk over every subexpression, including those inside `let`
    /// bindings and case alternatives.
    pub fn visit(&self, f: &mut impl FnMut(&Expr)) {
        f(self);
        match self {
            Expr::App { fun, arg } => {
                fun.visit(f);
                arg.visit(f);
            }
            Expr::Lam { body, .. } => body.visit(f),
            Expr::Let { bind, body } => {
                for pair in &bind.pairs {
                    pair.rhs.visit(f);
                }
                body.visit(f);
            }
            Expr::Case { scrut, alts, .. } => {
                scrut.visit(f);
                for alt in alts {
                    alt.rhs.visit(f);
                }
            }
            Expr::Cast { expr } | Expr::Tick { expr } => expr.visit(f),
            Expr::Var { .. } | Expr::Lit { .. } | Expr::Type { .. } | Expr::Coercion => {}
        }
    }
}

impl CoreModule {
    /// Every binder bound anywhere in the module, top level or nested.
    pub fn visit_binders(&self, f: &mut impl FnMut(&Binder)) {
        for bind in &self.binds {
            for pair in &bind.pairs {
                f(&pair.binder);
                pair.rhs.visit(&mut |e| match e {
                    Expr::Lam { binder, .. } | Expr::Case { binder, .. } => f(binder),
                    Expr::Let { bind, .. } => {
                        for pair in &bind.pairs {
                            f(&pair.binder);
                        }
                    }
                    _ => {}
                });
            }
        }
    }

    /// Core from real code nests far deeper than serde_json's default limit of
    /// 128 (long `App` spines, in particular), so the limit is lifted here.
    /// Callers must run on a thread with a generous stack; see
    /// [`with_big_stack`].
    pub fn load(path: &Path) -> Result<Self> {
        let bytes = std::fs::read(path)
            .with_context(|| format!("reading Core dump {}", path.display()))?;
        let mut de = serde_json::Deserializer::from_slice(&bytes);
        de.disable_recursion_limit();
        Self::deserialize(&mut de).with_context(|| format!("parsing Core dump {}", path.display()))
    }
}

/// Load every `*.core.json` under `dir`, sorted by module name.
pub fn load_dir(dir: &Path) -> Result<Vec<CoreModule>> {
    let mut paths: Vec<PathBuf> = walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.into_path())
        .filter(|p| p.to_string_lossy().ends_with(".core.json"))
        .collect();
    paths.sort();

    let mut modules = Vec::with_capacity(paths.len());
    for path in paths {
        modules.push(CoreModule::load(&path)?);
    }
    modules.sort_by(|a, b| a.module.cmp(&b.module));
    Ok(modules)
}

/// Run `f` on a thread with a large stack.
///
/// Core `App` spines and `Let` chains nest deeply enough that deserialising,
/// walking, or even dropping a module can exhaust a default 8 MiB stack.
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
