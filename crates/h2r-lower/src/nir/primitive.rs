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

use super::{CharCompare, IntBinary, Machine, World, data};

pub(super) const INT: &str = "$ghc-prim$GHC.Prim$Int#";
pub(super) const CHAR: &str = "$ghc-prim$GHC.Prim$Char#";
pub(super) const WORD: &str = "$ghc-prim$GHC.Prim$Word#";
pub(super) const ADDR: &str = "$ghc-prim$GHC.Prim$Addr#";
pub(super) const WORD8: &str = "$ghc-prim$GHC.Prim$Word8#";
pub(super) const STATE: &str = "$ghc-prim$GHC.Prim$State#";
pub(super) const MUT_VAR: &str = "$ghc-prim$GHC.Prim$MutVar#";
pub(super) const REAL_WORLD: &str = "$ghc-prim$GHC.Prim$RealWorld";
pub(super) const BYTE_ARRAY: &str = "$ghc-prim$GHC.Prim$ByteArray#";
pub(super) const MUTABLE_BYTE_ARRAY: &str = "$ghc-prim$GHC.Prim$MutableByteArray#";
pub(super) const ARRAY: &str = "$ghc-prim$GHC.Prim$Array#";
pub(super) const MUTABLE_ARRAY: &str = "$ghc-prim$GHC.Prim$MutableArray#";

fn con(name: &str, occ: &str) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: name.into(),
            occ: occ.into(),
            unique: Default::default(),
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

pub(super) fn addr_ty() -> Ty {
    con(ADDR, "Addr#")
}

pub(super) fn word8_ty() -> Ty {
    con(WORD8, "Word8#")
}

pub(super) fn is_word8(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == WORD8 && args.is_empty())
}

pub(super) fn state_ty(state: Ty) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: STATE.into(),
            occ: "State#".into(),
            unique: Default::default(),
        },
        args: vec![state],
    }
}

pub(super) fn is_state(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == STATE && args.len() == 1)
}

pub(super) fn real_world_ty() -> Ty {
    con(REAL_WORLD, "RealWorld")
}

pub(super) fn mut_var_ty(levity: Ty, state: Ty, element: Ty) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: MUT_VAR.into(),
            occ: "MutVar#".into(),
            unique: Default::default(),
        },
        args: vec![levity, state, element],
    }
}

pub(super) fn is_mut_var(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == MUT_VAR && args.len() == 3)
}

pub(super) fn bytes_ty() -> Ty {
    con(BYTE_ARRAY, "ByteArray#")
}

pub(super) fn mutable_bytes_ty(state: Ty) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: MUTABLE_BYTE_ARRAY.into(),
            occ: "MutableByteArray#".into(),
            unique: Default::default(),
        },
        args: vec![state],
    }
}

pub(super) fn array_ty(levity: Ty, element: Ty) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: ARRAY.into(),
            occ: "Array#".into(),
            unique: Default::default(),
        },
        args: vec![levity, element],
    }
}

pub(super) fn mutable_array_ty(levity: Ty, state: Ty, element: Ty) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: MUTABLE_ARRAY.into(),
            occ: "MutableArray#".into(),
            unique: Default::default(),
        },
        args: vec![levity, state, element],
    }
}

pub(super) fn array_element(ty: &Ty) -> Option<&Ty> {
    match ty {
        Ty::Con { tycon, args } if tycon.name == ARRAY && args.len() == 2 => Some(&args[1]),
        Ty::Con { tycon, args } if tycon.name == MUTABLE_ARRAY && args.len() == 3 => Some(&args[2]),
        _ => None,
    }
}

pub(super) fn is_bytes(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if (tycon.name == BYTE_ARRAY && args.is_empty())
        || (tycon.name == MUTABLE_BYTE_ARRAY && args.len() == 1))
}

pub(super) fn is_addr(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == ADDR && args.is_empty())
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
    is_int(ty) || is_char(ty) || is_word(ty) || is_word8(ty) || is_state(ty)
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
    } else if is_word8(ty) {
        u8::try_from(lit.number("Word8")?)
            .map(i64::from)
            .map_err(|error| format!("Word8# literal does not fit an unsigned byte: {error}"))
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
    Negate,
    WordBinary(IntBinary),
    WordToInt,
    IndexChar,
    PlusAddr,
    Machine(Machine),
}

impl Machine {
    const ALL: [Machine; 57] = [
        Machine::XorWord,
        Machine::OrWord,
        Machine::NotWord,
        Machine::NotInt,
        Machine::XorInt,
        Machine::QuotRemInt,
        Machine::Word8ToWord,
        Machine::WordToWord8,
        Machine::IndexWord8Addr,
        Machine::ShiftLeftWord,
        Machine::ShiftRightWord,
        Machine::ShiftRightLogicalInt,
        Machine::PlusWord,
        Machine::TimesWord,
        Machine::QuotWord,
        Machine::RemWord,
        Machine::QuotRemWord,
        Machine::QuotRemWord2,
        Machine::PlusWord2,
        Machine::TimesWord2,
        Machine::AddWordC,
        Machine::SubWordC,
        Machine::AddIntC,
        Machine::SubIntC,
        Machine::MulIntMayOflo,
        Machine::TimesInt2,
        Machine::Clz,
        Machine::Ctz,
        Machine::PopCnt,
        Machine::NewMutVar,
        Machine::ReadMutVar,
        Machine::WriteMutVar,
        Machine::Raise,
        Machine::RaiseDivZero,
        Machine::RaiseUnderflow,
        Machine::RaiseOverflow,
        Machine::NoDuplicate,
        Machine::NewByteArray,
        Machine::ReadWordArray,
        Machine::WriteWordArray,
        Machine::IndexWordArray,
        Machine::ReadIntArray,
        Machine::WriteIntArray,
        Machine::IndexIntArray,
        Machine::SizeofByteArray,
        Machine::GetSizeofMutableByteArray,
        Machine::ShrinkMutableByteArray,
        Machine::UnsafeFreezeByteArray,
        Machine::CopyByteArray,
        Machine::CopyMutableByteArray,
        Machine::SetByteArray,
        Machine::NewArray,
        Machine::ReadArray,
        Machine::WriteArray,
        Machine::IndexArray,
        Machine::UnsafeFreezeArray,
        Machine::UnsafeThawArray,
    ];

    fn name(self) -> &'static str {
        match self {
            Machine::XorWord => "xor#",
            Machine::OrWord => "or#",
            Machine::NotWord => "not#",
            Machine::NotInt => "notI#",
            Machine::XorInt => "xorI#",
            Machine::QuotRemInt => "quotRemInt#",
            Machine::Word8ToWord => "word8ToWord#",
            Machine::WordToWord8 => "wordToWord8#",
            Machine::IndexWord8Addr => "indexWord8OffAddr#",
            Machine::ShiftLeftWord => "uncheckedShiftL#",
            Machine::ShiftRightWord => "uncheckedShiftRL#",
            Machine::ShiftRightLogicalInt => "uncheckedIShiftRL#",
            Machine::PlusWord => "plusWord#",
            Machine::TimesWord => "timesWord#",
            Machine::QuotWord => "quotWord#",
            Machine::RemWord => "remWord#",
            Machine::QuotRemWord => "quotRemWord#",
            Machine::QuotRemWord2 => "quotRemWord2#",
            Machine::PlusWord2 => "plusWord2#",
            Machine::TimesWord2 => "timesWord2#",
            Machine::AddWordC => "addWordC#",
            Machine::SubWordC => "subWordC#",
            Machine::AddIntC => "addIntC#",
            Machine::SubIntC => "subIntC#",
            Machine::MulIntMayOflo => "mulIntMayOflo#",
            Machine::TimesInt2 => "timesInt2#",
            Machine::Clz => "clz#",
            Machine::Ctz => "ctz#",
            Machine::PopCnt => "popCnt#",
            Machine::NewMutVar => "newMutVar#",
            Machine::ReadMutVar => "readMutVar#",
            Machine::WriteMutVar => "writeMutVar#",
            Machine::Raise => "raise#",
            Machine::RaiseDivZero => "raiseDivZero#",
            Machine::RaiseUnderflow => "raiseUnderflow#",
            Machine::RaiseOverflow => "raiseOverflow#",
            Machine::AbsentError => "absentError",
            Machine::NoDuplicate => "noDuplicate#",
            Machine::Memcpy => "memcpy",
            Machine::RealWorld => "realWorld#",
            Machine::NewByteArray => "newByteArray#",
            Machine::ReadWordArray => "readWordArray#",
            Machine::WriteWordArray => "writeWordArray#",
            Machine::IndexWordArray => "indexWordArray#",
            Machine::ReadIntArray => "readIntArray#",
            Machine::WriteIntArray => "writeIntArray#",
            Machine::IndexIntArray => "indexIntArray#",
            Machine::SizeofByteArray => "sizeofByteArray#",
            Machine::GetSizeofMutableByteArray => "getSizeofMutableByteArray#",
            Machine::ShrinkMutableByteArray => "shrinkMutableByteArray#",
            Machine::UnsafeFreezeByteArray => "unsafeFreezeByteArray#",
            Machine::CopyByteArray => "copyByteArray#",
            Machine::CopyMutableByteArray => "copyMutableByteArray#",
            Machine::SetByteArray => "setByteArray#",
            Machine::NewArray => "newArray#",
            Machine::ReadArray => "readArray#",
            Machine::WriteArray => "writeArray#",
            Machine::IndexArray => "indexArray#",
            Machine::UnsafeFreezeArray => "unsafeFreezeArray#",
            Machine::UnsafeThawArray => "unsafeThawArray#",
        }
    }

    fn type_arity(self) -> usize {
        match self {
            Machine::XorWord
            | Machine::OrWord
            | Machine::NotWord
            | Machine::NotInt
            | Machine::XorInt
            | Machine::QuotRemInt
            | Machine::Word8ToWord
            | Machine::WordToWord8
            | Machine::IndexWord8Addr
            | Machine::ShiftLeftWord
            | Machine::ShiftRightWord
            | Machine::ShiftRightLogicalInt
            | Machine::PlusWord
            | Machine::TimesWord
            | Machine::QuotWord
            | Machine::RemWord
            | Machine::QuotRemWord
            | Machine::QuotRemWord2
            | Machine::PlusWord2
            | Machine::TimesWord2
            | Machine::AddWordC
            | Machine::SubWordC
            | Machine::AddIntC
            | Machine::SubIntC
            | Machine::MulIntMayOflo
            | Machine::TimesInt2
            | Machine::Clz
            | Machine::Ctz
            | Machine::PopCnt
            | Machine::RealWorld
            | Machine::IndexWordArray
            | Machine::IndexIntArray
            | Machine::SizeofByteArray
            | Machine::Memcpy => 0,
            Machine::NewByteArray
            | Machine::ReadWordArray
            | Machine::WriteWordArray
            | Machine::ReadIntArray
            | Machine::WriteIntArray
            | Machine::GetSizeofMutableByteArray
            | Machine::ShrinkMutableByteArray
            | Machine::UnsafeFreezeByteArray
            | Machine::CopyByteArray
            | Machine::CopyMutableByteArray
            | Machine::SetByteArray
            | Machine::AbsentError
            | Machine::NoDuplicate => 1,
            Machine::IndexArray
            | Machine::RaiseDivZero
            | Machine::RaiseUnderflow
            | Machine::RaiseOverflow => 2,
            Machine::NewMutVar
            | Machine::ReadMutVar
            | Machine::WriteMutVar
            | Machine::NewArray
            | Machine::ReadArray
            | Machine::WriteArray
            | Machine::UnsafeFreezeArray
            | Machine::UnsafeThawArray => 3,
            Machine::Raise => 4,
        }
    }

    fn shape(self, t: &[Ty]) -> Option<(Vec<Ty>, Vec<Ty>)> {
        if t.len() != self.type_arity() {
            return None;
        }
        Some(match self {
            Machine::XorWord => (vec![word_ty(), word_ty()], vec![word_ty()]),
            Machine::OrWord => (vec![word_ty(), word_ty()], vec![word_ty()]),
            Machine::NotWord => (vec![word_ty()], vec![word_ty()]),
            Machine::NotInt => (vec![int_ty()], vec![int_ty()]),
            Machine::XorInt => (vec![int_ty(), int_ty()], vec![int_ty()]),
            Machine::QuotRemInt => (vec![int_ty(), int_ty()], vec![int_ty(), int_ty()]),
            Machine::Word8ToWord => (vec![word8_ty()], vec![word_ty()]),
            Machine::WordToWord8 => (vec![word_ty()], vec![word8_ty()]),
            Machine::IndexWord8Addr => (vec![addr_ty(), int_ty()], vec![word8_ty()]),
            Machine::ShiftLeftWord => (vec![word_ty(), int_ty()], vec![word_ty()]),
            Machine::ShiftRightWord => (vec![word_ty(), int_ty()], vec![word_ty()]),
            Machine::ShiftRightLogicalInt => (vec![int_ty(), int_ty()], vec![int_ty()]),
            Machine::PlusWord => (vec![word_ty(), word_ty()], vec![word_ty()]),
            Machine::TimesWord => (vec![word_ty(), word_ty()], vec![word_ty()]),
            Machine::QuotWord => (vec![word_ty(), word_ty()], vec![word_ty()]),
            Machine::RemWord => (vec![word_ty(), word_ty()], vec![word_ty()]),
            Machine::QuotRemWord => (vec![word_ty(), word_ty()], vec![word_ty(), word_ty()]),
            Machine::QuotRemWord2 => (
                vec![word_ty(), word_ty(), word_ty()],
                vec![word_ty(), word_ty()],
            ),
            Machine::PlusWord2 => (vec![word_ty(), word_ty()], vec![word_ty(), word_ty()]),
            Machine::TimesWord2 => (vec![word_ty(), word_ty()], vec![word_ty(), word_ty()]),
            Machine::AddWordC => (vec![word_ty(), word_ty()], vec![word_ty(), int_ty()]),
            Machine::SubWordC => (vec![word_ty(), word_ty()], vec![word_ty(), int_ty()]),
            Machine::AddIntC => (vec![int_ty(), int_ty()], vec![int_ty(), int_ty()]),
            Machine::SubIntC => (vec![int_ty(), int_ty()], vec![int_ty(), int_ty()]),
            Machine::MulIntMayOflo => (vec![int_ty(), int_ty()], vec![int_ty()]),
            Machine::TimesInt2 => (vec![int_ty(), int_ty()], vec![int_ty(), int_ty(), int_ty()]),
            Machine::Clz => (vec![word_ty()], vec![word_ty()]),
            Machine::Ctz => (vec![word_ty()], vec![word_ty()]),
            Machine::PopCnt => (vec![word_ty()], vec![word_ty()]),
            Machine::NewMutVar => (
                vec![t[1].clone(), state_ty(t[2].clone())],
                vec![
                    state_ty(t[2].clone()),
                    mut_var_ty(t[0].clone(), t[2].clone(), t[1].clone()),
                ],
            ),
            Machine::ReadMutVar => (
                vec![
                    mut_var_ty(t[0].clone(), t[1].clone(), t[2].clone()),
                    state_ty(t[1].clone()),
                ],
                vec![state_ty(t[1].clone()), t[2].clone()],
            ),
            Machine::WriteMutVar => (
                vec![
                    mut_var_ty(t[0].clone(), t[1].clone(), t[2].clone()),
                    t[2].clone(),
                    state_ty(t[1].clone()),
                ],
                vec![state_ty(t[1].clone())],
            ),
            Machine::Raise => (vec![], vec![t[3].clone()]),
            Machine::RaiseDivZero | Machine::RaiseUnderflow | Machine::RaiseOverflow => {
                (vec![], vec![t[1].clone()])
            }
            Machine::AbsentError => (vec![addr_ty()], vec![t[0].clone()]),
            Machine::NoDuplicate => (vec![state_ty(t[0].clone())], vec![state_ty(t[0].clone())]),
            Machine::Memcpy => (
                vec![
                    mutable_bytes_ty(real_world_ty()),
                    mutable_bytes_ty(real_world_ty()),
                    int_ty(),
                    state_ty(real_world_ty()),
                ],
                vec![state_ty(real_world_ty()), addr_ty()],
            ),
            Machine::RealWorld => (vec![], vec![state_ty(real_world_ty())]),
            Machine::NewByteArray => (
                vec![int_ty(), state_ty(t[0].clone())],
                vec![state_ty(t[0].clone()), mutable_bytes_ty(t[0].clone())],
            ),
            Machine::ReadWordArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone()), word_ty()],
            ),
            Machine::WriteWordArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    word_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone())],
            ),
            Machine::IndexWordArray => (vec![bytes_ty(), int_ty()], vec![word_ty()]),
            Machine::IndexIntArray => (vec![bytes_ty(), int_ty()], vec![int_ty()]),
            Machine::ReadIntArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone()), int_ty()],
            ),
            Machine::WriteIntArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone())],
            ),
            Machine::SizeofByteArray => (vec![bytes_ty()], vec![int_ty()]),
            Machine::GetSizeofMutableByteArray => (
                vec![mutable_bytes_ty(t[0].clone()), state_ty(t[0].clone())],
                vec![state_ty(t[0].clone()), int_ty()],
            ),
            Machine::ShrinkMutableByteArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone())],
            ),
            Machine::UnsafeFreezeByteArray => (
                vec![mutable_bytes_ty(t[0].clone()), state_ty(t[0].clone())],
                vec![state_ty(t[0].clone()), bytes_ty()],
            ),
            Machine::CopyByteArray => (
                vec![
                    bytes_ty(),
                    int_ty(),
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone())],
            ),
            Machine::CopyMutableByteArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone())],
            ),
            Machine::SetByteArray => (
                vec![
                    mutable_bytes_ty(t[0].clone()),
                    int_ty(),
                    int_ty(),
                    int_ty(),
                    state_ty(t[0].clone()),
                ],
                vec![state_ty(t[0].clone())],
            ),
            Machine::NewArray => (
                vec![int_ty(), t[1].clone(), state_ty(t[2].clone())],
                vec![
                    state_ty(t[2].clone()),
                    mutable_array_ty(t[0].clone(), t[2].clone(), t[1].clone()),
                ],
            ),
            Machine::ReadArray => (
                vec![
                    mutable_array_ty(t[0].clone(), t[1].clone(), t[2].clone()),
                    int_ty(),
                    state_ty(t[1].clone()),
                ],
                vec![state_ty(t[1].clone()), t[2].clone()],
            ),
            Machine::WriteArray => (
                vec![
                    mutable_array_ty(t[0].clone(), t[1].clone(), t[2].clone()),
                    int_ty(),
                    t[2].clone(),
                    state_ty(t[1].clone()),
                ],
                vec![state_ty(t[1].clone())],
            ),
            Machine::IndexArray => (
                vec![array_ty(t[0].clone(), t[1].clone()), int_ty()],
                vec![t[1].clone()],
            ),
            Machine::UnsafeFreezeArray => (
                vec![
                    mutable_array_ty(t[0].clone(), t[1].clone(), t[2].clone()),
                    state_ty(t[1].clone()),
                ],
                vec![state_ty(t[1].clone()), array_ty(t[0].clone(), t[2].clone())],
            ),
            Machine::UnsafeThawArray => (
                vec![array_ty(t[0].clone(), t[1].clone()), state_ty(t[2].clone())],
                vec![
                    state_ty(t[2].clone()),
                    mutable_array_ty(t[0].clone(), t[2].clone(), t[1].clone()),
                ],
            ),
        })
    }

    fn operand_count(self) -> usize {
        match self {
            Machine::Raise
            | Machine::RaiseDivZero
            | Machine::RaiseUnderflow
            | Machine::RaiseOverflow => 1,
            _ => self
                .shape(&vec![int_ty(); self.type_arity()])
                .map_or(0, |(operands, _)| operands.len()),
        }
    }

    pub(super) fn operands(self, types: &[Ty]) -> Option<Vec<Ty>> {
        self.shape(types).map(|(operands, _)| operands)
    }

    pub(super) fn results(self, types: &[Ty]) -> Option<Vec<Ty>> {
        self.shape(types).map(|(_, results)| results)
    }

    pub(super) fn returns_tuple(self, types: &[Ty]) -> bool {
        self == Machine::IndexArray
            || self
                .results(types)
                .is_some_and(|results| results.len() != 1)
    }

    pub(super) fn signature_at(
        self,
        world: &World<'_>,
        types: &[Ty],
        result: &Ty,
    ) -> Result<Ty, String> {
        let (Some(operands), Some(results)) = (self.operands(types), self.results(types)) else {
            return Err("a primop applied to other type arguments than it quantifies".into());
        };
        let returned = match results.as_slice() {
            [one] if !self.returns_tuple(types) => one.clone(),
            many => {
                let fields = data::unboxed_tuple_fields(world, result)?
                    .ok_or("a primop with several results returns an unboxed tuple")?;
                if fields.len() != many.len()
                    || fields
                        .iter()
                        .zip(many)
                        .any(|(field, expected)| !field.alpha_eq(expected))
                {
                    return Err("a primop's unboxed tuple has other components".into());
                }
                result.clone()
            }
        };
        Ok(operands
            .into_iter()
            .rev()
            .fold(returned, |res, operand| arrow(operand, res)))
    }
}

impl Prim {
    pub(super) fn arity(self) -> u32 {
        match self {
            Prim::Int(_)
            | Prim::Char(_)
            | Prim::Word(_)
            | Prim::WordBinary(_)
            | Prim::IndexChar
            | Prim::PlusAddr => 2,
            Prim::Ord | Prim::Chr | Prim::IntToWord | Prim::WordToInt | Prim::Negate => 1,
            Prim::Machine(machine) => machine.operand_count() as u32,
        }
    }

    pub(super) fn signature_at(
        self,
        world: &World<'_>,
        types: &[Ty],
        result: &Ty,
    ) -> Result<Ty, String> {
        if let Prim::Machine(machine) = self {
            return machine.signature_at(world, types, result);
        }
        if !types.is_empty() {
            return Err("a monomorphic primop takes no type arguments".into());
        }
        Ok(match self {
            Prim::Int(_) => arrow(int_ty(), arrow(int_ty(), int_ty())),
            Prim::Char(_) => arrow(char_ty(), arrow(char_ty(), int_ty())),
            Prim::Ord => arrow(char_ty(), int_ty()),
            Prim::Chr => arrow(int_ty(), char_ty()),
            Prim::Word(_) => arrow(word_ty(), arrow(word_ty(), int_ty())),
            Prim::IntToWord => arrow(int_ty(), word_ty()),
            Prim::Negate => arrow(int_ty(), int_ty()),
            Prim::WordBinary(_) => arrow(word_ty(), arrow(word_ty(), word_ty())),
            Prim::WordToInt => arrow(word_ty(), int_ty()),
            Prim::IndexChar => arrow(addr_ty(), arrow(int_ty(), char_ty())),
            Prim::PlusAddr => arrow(addr_ty(), arrow(int_ty(), addr_ty())),
            Prim::Machine(machine) => machine.signature_at(world, types, result)?,
        })
    }
}

const ABSENT_ERROR: &str = "$ghc-prim$GHC.Prim.Panic$absentError";

const MEMCPY: &str = "MutableByteArray# RealWorld -> MutableByteArray# RealWorld -> Int# -> State# RealWorld -> (# State# RealWorld, Addr# #)";

fn foreign_call(name: &str) -> Option<(&str, String)> {
    let inner = name
        .strip_prefix("$_in${__ffi_static_ccall_")?
        .strip_suffix('}')?;
    let inner = inner
        .strip_prefix("safe ")
        .or_else(|| inner.strip_prefix("unsafe "))?;
    let (target, ty) = inner.split_once(" :: ")?;
    let label = target.split_once(' ').map_or(target, |(label, _)| label);
    let symbol = label.rsplit_once(':')?.1;
    Some((symbol, ty.split_whitespace().collect::<Vec<_>>().join(" ")))
}

pub(super) fn resolve(module: &Module, head: ExprId) -> Option<Prim> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    if module.reference(head) == Some(h2r_core_ir::Ref::Global)
        && module.id_info(head).is_none()
        && foreign_call(name).is_some_and(|(symbol, ty)| symbol == "memcpy" && ty == MEMCPY)
    {
        return Some(Prim::Machine(Machine::Memcpy));
    }
    // id_info only returns metadata for lexically unresolved global references.
    let info = module.id_info(head)?;
    if info.name != *name {
        return None;
    }
    if name == ABSENT_ERROR && info.details.is_empty() {
        let prim = Prim::Machine(Machine::AbsentError);
        return (info.arity == prim.arity()).then_some(prim);
    }
    if info.details != "[PrimOp]" {
        return None;
    }
    let prim =
        match name.as_str() {
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
            "$ghc-prim$GHC.Prim$ltWord#" => Prim::Word(CharCompare::Less),
            "$ghc-prim$GHC.Prim$gtWord#" => Prim::Word(CharCompare::Greater),
            "$ghc-prim$GHC.Prim$geWord#" => Prim::Word(CharCompare::GreaterEqual),
            "$ghc-prim$GHC.Prim$eqWord#" => Prim::Word(CharCompare::Equal),
            "$ghc-prim$GHC.Prim$neWord#" => Prim::Word(CharCompare::NotEqual),
            "$ghc-prim$GHC.Prim$int2Word#" => Prim::IntToWord,
            "$ghc-prim$GHC.Prim$andI#" => Prim::Int(IntBinary::And),
            "$ghc-prim$GHC.Prim$orI#" => Prim::Int(IntBinary::Or),
            "$ghc-prim$GHC.Prim$quotInt#" => Prim::Int(IntBinary::Quot),
            "$ghc-prim$GHC.Prim$remInt#" => Prim::Int(IntBinary::Rem),
            "$ghc-prim$GHC.Prim$negateInt#" => Prim::Negate,
            "$ghc-prim$GHC.Prim$minusWord#" => Prim::WordBinary(IntBinary::Subtract),
            "$ghc-prim$GHC.Prim$and#" => Prim::WordBinary(IntBinary::And),
            "$ghc-prim$GHC.Prim$word2Int#" => Prim::WordToInt,
            "$ghc-prim$GHC.Prim$indexCharOffAddr#" => Prim::IndexChar,
            "$ghc-prim$GHC.Prim$plusAddr#" => Prim::PlusAddr,
            other => Prim::Machine(Machine::ALL.into_iter().find(|machine| {
                other.strip_prefix("$ghc-prim$GHC.Prim$") == Some(machine.name())
            })?),
        };
    (info.arity == prim.arity()).then_some(prim)
}

pub(super) fn signature() -> Ty {
    arrow(int_ty(), arrow(int_ty(), int_ty()))
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
