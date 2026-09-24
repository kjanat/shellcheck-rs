//! Exact built-in Int constructor evidence; not a general constructor fallback.
use h2r_core_ir::{AltCon, Expr, ExprId, Module, Ty, TyConId};

pub(crate) const INT: &str = "$ghc-prim$GHC.Types$Int";
pub(crate) const CONSTRUCTOR: &str = "$ghc-prim$GHC.Types$I#";

pub(crate) fn is_int(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == INT && args.is_empty())
}

pub(super) fn resolves(module: &Module, head: ExprId) -> bool {
    let Expr::Var { name, .. } = module.expr(head) else {
        return false;
    };
    let Some(info) = module.id_info(head) else {
        return false;
    };
    name == CONSTRUCTOR
        && info.name == *name
        && info.arity == 1
        && info.details == "[DataCon]"
        && info.data_con.as_ref().is_some_and(|dc| {
            dc.name == CONSTRUCTOR
                && dc.tag == 1
                && dc.rep_arity == 1
                && dc.strict_fields.len() == 1
        })
}

pub(super) fn alternative(con: &AltCon) -> bool {
    matches!(con, AltCon::DataAlt { name, tag: 1, .. } if name == CONSTRUCTOR)
}

pub(super) fn signature() -> Ty {
    let Ty::Fun { mult, arg, .. } = super::primitive::signature() else {
        unreachable!()
    };
    Ty::Fun {
        mult,
        arg,
        res: Box::new(Ty::Con {
            tycon: TyConId {
                name: INT.into(),
                occ: "Int".into(),
                unique: Default::default(),
            },
            args: vec![],
        }),
    }
}
