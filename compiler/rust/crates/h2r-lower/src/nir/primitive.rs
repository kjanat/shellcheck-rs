//! Small explicit external primitive table. Lexical resolution takes precedence
//! over spelling. GHC's well-typed Core is trusted for primitive signatures.
//!
//! Each entry asserts the primop's exact GHC signature. The builder lowers the
//! arguments *at* those asserted types and checks the result against the
//! asserted result type, so in well-typed Core a site that passes those checks
//! pins the primop's type exactly. A spelling alone concludes nothing: the
//! occurrence must also resolve to an unbound global whose `IdInfo` says
//! `[PrimOp]` at the asserted arity.

use h2r_core_ir::{Expr, ExprId, Module, Ty, TyConId};

use super::{CharCompare, IntBinary};

pub(super) const INT: &str = "$ghc-prim$GHC.Prim$Int#";
pub(super) const CHAR: &str = "$ghc-prim$GHC.Prim$Char#";
pub(super) const WORD: &str = "$ghc-prim$GHC.Prim$Word#";

fn con(name: &str, occ: &str) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: name.into(),
            occ: occ.into(),
            unique: String::new(),
        },
        args: vec![],
    }
}

fn arrow(arg: Ty, res: Ty) -> Ty {
    Ty::Fun {
        mult: Box::new(con("$ghc-prim$GHC.Types$Many", "Many")),
        arg: Box::new(arg),
        res: Box::new(res),
    }
}

pub(super) fn int_ty() -> Ty {
    con(INT, "Int#")
}

pub(super) fn char_ty() -> Ty {
    con(CHAR, "Char#")
}

pub(super) fn word_ty() -> Ty {
    con(WORD, "Word#")
}

pub(super) fn is_word(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == WORD && args.is_empty())
}

pub(super) fn is_int(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == INT && args.is_empty())
}

pub(super) fn is_char(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == CHAR && args.is_empty())
}

/// An unboxed scalar this backend carries in a machine word. `Char#` is a
/// Unicode code point, which is why it shares the carrier but not the
/// operations: nothing here adds two characters.
pub(super) fn is_scalar(ty: &Ty) -> bool {
    is_int(ty) || is_char(ty) || is_word(ty)
}

/// The bits of a `Word#` literal, which the word carrier holds as an `i64`.
pub(super) fn word_literal(lit: &h2r_core_ir::Lit) -> Result<i64, String> {
    u64::try_from(lit.number("Word")?)
        .map(u64::cast_signed)
        .map_err(|error| format!("Word# literal does not fit an unsigned 64-bit word: {error}"))
}

/// The value of an `Int#` literal, read from the dump's exact value and its
/// `LitNumType`. GHC's rendering is a diagnostic and is never parsed.
pub(super) fn int_literal(lit: &h2r_core_ir::Lit) -> Result<i64, String> {
    i64::try_from(lit.number("Int")?)
        .map_err(|error| format!("Int# literal does not fit a signed 64-bit word: {error}"))
}

/// The code point of a `Char#` literal. GHC's `Char#` is a Unicode code point,
/// and a surrogate or an out-of-range value is not one.
pub(super) fn char_literal(lit: &h2r_core_ir::Lit) -> Result<u32, String> {
    let codepoint = lit.char_codepoint()?;
    char::from_u32(codepoint).ok_or("Char# literal is not a Unicode code point")?;
    Ok(codepoint)
}

/// An unboxed literal at the carrier the enclosing type demands. The value
/// comes from the dump's exact field; the carrier decides which field.
pub(super) fn scalar_literal(ty: &Ty, lit: &h2r_core_ir::Lit) -> Result<i64, String> {
    if is_int(ty) {
        int_literal(lit)
    } else if is_char(ty) {
        Ok(i64::from(char_literal(lit)?))
    } else if is_word(ty) {
        word_literal(lit)
    } else {
        Err("literal requires an unboxed scalar carrier".into())
    }
}

/// One supported primitive operation, with the exact signature GHC gives it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Prim {
    /// `Int# -> Int# -> Int#`. Comparisons produce 0 or 1; arithmetic wraps.
    Int(IntBinary),
    /// `Char# -> Char# -> Int#`. Code-point order, which is `Ord Char`.
    Char(CharCompare),
    /// `ord# :: Char# -> Int#`.
    Ord,
    /// `chr# :: Int# -> Char#`. Unchecked, exactly as GHC's is.
    Chr,
    /// `Word# -> Word# -> Int#`, unsigned.
    Word(CharCompare),
    /// `int2Word# :: Int# -> Word#`.
    IntToWord,
}

impl Prim {
    pub(super) fn arity(self) -> u32 {
        match self {
            Prim::Int(_) | Prim::Char(_) | Prim::Word(_) => 2,
            Prim::Ord | Prim::Chr | Prim::IntToWord => 1,
        }
    }

    pub(super) fn signature(self) -> Ty {
        match self {
            Prim::Int(_) => arrow(int_ty(), arrow(int_ty(), int_ty())),
            Prim::Char(_) => arrow(char_ty(), arrow(char_ty(), int_ty())),
            Prim::Ord => arrow(char_ty(), int_ty()),
            Prim::Chr => arrow(int_ty(), char_ty()),
            Prim::Word(_) => arrow(word_ty(), arrow(word_ty(), int_ty())),
            Prim::IntToWord => arrow(int_ty(), word_ty()),
        }
    }
}

pub(super) fn resolve(module: &Module, head: ExprId) -> Option<Prim> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    // id_info only returns metadata for lexically unresolved global references.
    let info = module.id_info(head)?;
    if info.name != *name || info.details != "[PrimOp]" {
        return None;
    }
    let prim = match name.as_str() {
        "$ghc-prim$GHC.Prim$+#" => Prim::Int(IntBinary::Add),
        "$ghc-prim$GHC.Prim$-#" => Prim::Int(IntBinary::Subtract),
        "$ghc-prim$GHC.Prim$*#" => Prim::Int(IntBinary::Multiply),
        "$ghc-prim$GHC.Prim$==#" => Prim::Int(IntBinary::Equal),
        "$ghc-prim$GHC.Prim$/=#" => Prim::Int(IntBinary::NotEqual),
        "$ghc-prim$GHC.Prim$<#" => Prim::Int(IntBinary::Less),
        "$ghc-prim$GHC.Prim$<=#" => Prim::Int(IntBinary::LessEqual),
        "$ghc-prim$GHC.Prim$>#" => Prim::Int(IntBinary::Greater),
        "$ghc-prim$GHC.Prim$>=#" => Prim::Int(IntBinary::GreaterEqual),
        "$ghc-prim$GHC.Prim$eqChar#" => Prim::Char(CharCompare::Equal),
        "$ghc-prim$GHC.Prim$neChar#" => Prim::Char(CharCompare::NotEqual),
        "$ghc-prim$GHC.Prim$ltChar#" => Prim::Char(CharCompare::Less),
        "$ghc-prim$GHC.Prim$leChar#" => Prim::Char(CharCompare::LessEqual),
        "$ghc-prim$GHC.Prim$gtChar#" => Prim::Char(CharCompare::Greater),
        "$ghc-prim$GHC.Prim$geChar#" => Prim::Char(CharCompare::GreaterEqual),
        "$ghc-prim$GHC.Prim$ord#" => Prim::Ord,
        "$ghc-prim$GHC.Prim$chr#" => Prim::Chr,
        "$ghc-prim$GHC.Prim$uncheckedIShiftL#" => Prim::Int(IntBinary::ShiftLeft),
        "$ghc-prim$GHC.Prim$uncheckedIShiftRA#" => Prim::Int(IntBinary::ShiftRightArithmetic),
        "$ghc-prim$GHC.Prim$leWord#" => Prim::Word(CharCompare::LessEqual),
        "$ghc-prim$GHC.Prim$int2Word#" => Prim::IntToWord,
        _ => return None,
    };
    (info.arity == prim.arity()).then_some(prim)
}

pub(super) fn signature() -> Ty {
    Prim::Int(IntBinary::Add).signature()
}

#[cfg(test)]
mod tests {
    use super::*;
    use h2r_core_ir::Lit;

    #[test]
    fn a_literal_is_read_at_the_carrier_its_type_demands() {
        assert_eq!(scalar_literal(&int_ty(), &Lit::int(-7)), Ok(-7));
        assert_eq!(scalar_literal(&char_ty(), &Lit::character('A')), Ok(65));
        assert_eq!(
            scalar_literal(&char_ty(), &Lit::character('\u{1d11e}')),
            Ok(0x1d11e)
        );
        // Each carrier reads its own field, so the other kind is refused
        // rather than reinterpreted.
        assert!(scalar_literal(&int_ty(), &Lit::character('A')).is_err());
        assert!(scalar_literal(&char_ty(), &Lit::int(65)).is_err());
        assert!(scalar_literal(&char_ty(), &Lit::string(b"A")).is_err());
    }

    #[test]
    fn an_int_literal_must_be_an_int_of_machine_width() {
        // The LitNumType decides the width; the spelling never does.
        let wide = Lit {
            num_type: Some("Word64".into()),
            ..Lit::int(1)
        };
        assert!(int_literal(&wide).is_err());
        let overflowing = Lit {
            value: Some("9223372036854775808".into()),
            ..Lit::int(0)
        };
        assert!(int_literal(&overflowing).is_err());
        assert_eq!(int_literal(&Lit::int(i64::MIN)), Ok(i64::MIN));
        assert_eq!(int_literal(&Lit::int(i64::MAX)), Ok(i64::MAX));
    }

    #[test]
    fn a_char_literal_must_be_a_code_point() {
        let surrogate = Lit {
            codepoint: Some(0xd800),
            ..Lit::character('a')
        };
        assert!(char_literal(&surrogate).is_err());
        let past_the_end = Lit {
            codepoint: Some(0x110000),
            ..Lit::character('a')
        };
        assert!(char_literal(&past_the_end).is_err());
        assert_eq!(char_literal(&Lit::character('\0')), Ok(0));
        assert_eq!(char_literal(&Lit::character('\u{10ffff}')), Ok(0x10ffff));
    }
}
