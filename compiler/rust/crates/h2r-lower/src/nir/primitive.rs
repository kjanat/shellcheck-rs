//! Small explicit external primitive table. Lexical resolution takes precedence
//! over spelling. GHC's well-typed Core is trusted for primitive signatures.

use h2r_core_ir::{Expr, ExprId, Module, Ty, TyConId};

use super::IntBinary;

pub(super) fn is_int(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Int#" && args.is_empty())
}

pub(super) fn int_literal(lit: &h2r_core_ir::Lit) -> Result<i64, String> {
    if lit.kind != "number" {
        return Err("Int# alternative requires a numeric literal".into());
    }
    lit.pretty
        .strip_suffix('#')
        .ok_or("unsupported Int# alternative spelling")?
        .parse()
        .map_err(|_| "Int# alternative must be a signed 64-bit decimal".into())
}

pub(super) fn resolve(module: &Module, head: ExprId) -> Option<IntBinary> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    // id_info only returns metadata for lexically unresolved global references.
    let info = module.id_info(head)?;
    if info.name != *name || info.arity != 2 || info.details != "[PrimOp]" {
        return None;
    }
    match name.as_str() {
        "$ghc-prim$GHC.Prim$+#" => Some(IntBinary::Add),
        "$ghc-prim$GHC.Prim$-#" => Some(IntBinary::Subtract),
        "$ghc-prim$GHC.Prim$*#" => Some(IntBinary::Multiply),
        "$ghc-prim$GHC.Prim$==#" => Some(IntBinary::Equal),
        "$ghc-prim$GHC.Prim$/=#" => Some(IntBinary::NotEqual),
        "$ghc-prim$GHC.Prim$<#" => Some(IntBinary::Less),
        "$ghc-prim$GHC.Prim$<=#" => Some(IntBinary::LessEqual),
        "$ghc-prim$GHC.Prim$>#" => Some(IntBinary::Greater),
        "$ghc-prim$GHC.Prim$>=#" => Some(IntBinary::GreaterEqual),
        _ => None,
    }
}

pub(super) fn signature() -> Ty {
    let con = |name: &str, occ: &str| Ty::Con {
        tycon: TyConId {
            name: name.into(),
            occ: occ.into(),
            unique: String::new(),
        },
        args: vec![],
    };
    let int = con("$ghc-prim$GHC.Prim$Int#", "Int#");
    let arrow = |res| Ty::Fun {
        mult: Box::new(con("$ghc-prim$GHC.Types$Many", "Many")),
        arg: Box::new(int.clone()),
        res: Box::new(res),
    };
    arrow(arrow(int.clone()))
}
