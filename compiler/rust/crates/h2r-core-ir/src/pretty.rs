//! A compact, depth-limited rendering of Core subtrees with node ids, for
//! reading the census' explanations against the actual Core.

use std::fmt::Write;

use crate::{AltCon, Expr, ExprId, Module};

pub struct Pretty<'a> {
    pub module: &'a Module,
    /// Subtrees deeper than this are elided.
    pub max_depth: usize,
    /// Show `[#id]` markers on every node.
    pub ids: bool,
    /// Optional inline annotation for a node, printed after its id marker.
    /// Used by `h2r show` to mark the nodes a proof object has something to
    /// say about; the pretty-printer itself knows nothing about them.
    #[allow(clippy::type_complexity)]
    pub note: Option<&'a dyn Fn(ExprId) -> Option<String>>,
    /// The same for a lambda's parameters, printed after the binder name.
    #[allow(clippy::type_complexity)]
    pub binder_note: Option<&'a dyn Fn(crate::BinderId) -> Option<String>>,
}

impl<'a> Pretty<'a> {
    pub fn plain(module: &'a Module, max_depth: usize) -> Pretty<'a> {
        Pretty {
            module,
            max_depth,
            ids: true,
            note: None,
            binder_note: None,
        }
    }
}

impl Pretty<'_> {
    pub fn render(&self, root: ExprId) -> String {
        let mut out = String::new();
        self.expr(&mut out, root, 0, 0);
        out
    }

    fn tag(&self, id: ExprId) -> String {
        let mark = match self.note.and_then(|f| f(id)) {
            Some(n) => format!("{{{n}}}"),
            None => String::new(),
        };
        if self.ids {
            format!("[#{id}]{mark}")
        } else {
            mark
        }
    }

    fn param(&self, b: crate::BinderId) -> String {
        match self.binder_note.and_then(|f| f(b)) {
            Some(n) => format!("{{{n}}}"),
            None => String::new(),
        }
    }

    fn nl(out: &mut String, indent: usize) {
        out.push('\n');
        for _ in 0..indent {
            out.push_str("  ");
        }
    }

    // Recursion here is bounded by `max_depth`, not by the tree.
    fn expr(&self, out: &mut String, id: ExprId, indent: usize, depth: usize) {
        let m = self.module;
        if depth > self.max_depth {
            let _ = write!(out, "…{}", self.tag(id));
            return;
        }
        match m.expr(id) {
            Expr::Var { occ, .. } => {
                let _ = write!(out, "{occ}{}", self.tag(id));
            }
            Expr::Lit(l) => {
                let _ = write!(out, "{}{}", l.pretty, self.tag(id));
            }
            Expr::Type { pretty: t, .. } => {
                let _ = write!(out, "@({t})");
            }
            Expr::Coercion => out.push_str("@~"),
            Expr::Cast(e) => {
                out.push('(');
                self.expr(out, *e, indent, depth + 1);
                let _ = write!(out, " `cast`){}", self.tag(id));
            }
            Expr::Tick(e) => self.expr(out, *e, indent, depth),
            Expr::App { .. } => {
                let (head, args) = m.spine(id);
                let _ = write!(out, "({}", self.tag(id));
                self.expr(out, head, indent, depth + 1);
                for a in args {
                    if matches!(m.expr(m.strip(a)), Expr::Type { .. } | Expr::Coercion) {
                        continue;
                    }
                    out.push(' ');
                    self.expr(out, a, indent + 1, depth + 1);
                }
                out.push(')');
            }
            Expr::Lam { .. } => {
                let mut params = Vec::new();
                let mut cur = id;
                while let Expr::Lam { binder, body } = m.expr(cur) {
                    let b = m.binder(*binder);
                    if b.kind == crate::BinderKind::Id {
                        let one = if b.one_shot == Some(true) { "¹" } else { "" };
                        params.push(format!("{}{one}{}", b.occ, self.param(*binder)));
                    }
                    cur = *body;
                }
                let _ = write!(out, "\\{}{} ->", params.join(" "), self.tag(id));
                Self::nl(out, indent + 1);
                self.expr(out, cur, indent + 1, depth + 1);
            }
            Expr::Let { bind, body } => {
                let kw = if bind.recursive { "letrec" } else { "let" };
                let _ = write!(out, "{kw}{}", self.tag(id));
                for p in &bind.pairs {
                    let b = m.binder(p.binder);
                    Self::nl(out, indent + 1);
                    let dmd = b.demand.as_ref().map(|d| d.pretty.as_str()).unwrap_or("");
                    let jp = if b.is_join_point == Some(true) {
                        "join "
                    } else {
                        ""
                    };
                    let _ = write!(out, "{jp}{} {{dmd={dmd}}} = ", b.occ);
                    self.expr(out, p.rhs, indent + 2, depth + 1);
                }
                Self::nl(out, indent);
                out.push_str("in ");
                self.expr(out, *body, indent, depth + 1);
            }
            Expr::Case {
                scrut,
                binder,
                alts,
                ..
            } => {
                let _ = write!(out, "case{} ", self.tag(id));
                self.expr(out, *scrut, indent + 1, depth + 1);
                let _ = write!(out, " of {} {{", m.binder(*binder).occ);
                for (i, alt) in alts.iter().enumerate() {
                    Self::nl(out, indent + 1);
                    let con = match &alt.con {
                        AltCon::DataAlt { occ, .. } => occ.clone(),
                        AltCon::LitAlt { lit } => lit.pretty.clone(),
                        AltCon::Default => "_".into(),
                    };
                    let bs: Vec<_> = alt
                        .binders
                        .iter()
                        .map(|b| m.binder(*b).occ.as_str())
                        .collect();
                    let _ = write!(out, "[alt {i}] {con} {} ->", bs.join(" "));
                    Self::nl(out, indent + 2);
                    self.expr(out, alt.rhs, indent + 2, depth + 1);
                }
                Self::nl(out, indent);
                out.push('}');
            }
        }
    }
}
