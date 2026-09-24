//! Haskell string literals.
//!
//! A source string is not a value in Core. It is an `Addr#` literal pointing at
//! NUL-terminated bytes, applied to one of `GHC.CString`'s unpackers, which
//! walks those bytes into a lazy `[Char]`. GHC picks the unpacker from the
//! literal's contents: `unpackCString#` when every character is ASCII 1..127,
//! and `unpackCStringUtf8#` otherwise, whose bytes are modified UTF-8 (a NUL
//! inside the string is the overlong `C0 80`).
//!
//! Only the saturated application is recognised, so the literal never becomes a
//! value on its own: this backend has no `Addr#` carrier and no pointer
//! arithmetic, and an `Addr#` anywhere else is refused. The decoders below
//! reproduce `GHC.CString`'s own arithmetic rather than Rust's UTF-8 handling,
//! because GHC's does not validate and accepts forms Rust's would reject.

use h2r_core_ir::{Expr, ExprId, Module, Ty, TyConId};

/// Which `GHC.CString` unpacker a literal is handed to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Encoding {
    /// `unpackCString#`: one byte, one character, code points 1..255.
    Latin1,
    /// `unpackCStringUtf8#`: modified UTF-8, decoded without validation.
    Utf8,
}

/// One supported unpacker, with the exact GHC signature it is checked against.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unpacker {
    pub encoding: Encoding,
    /// `unpackAppendCString#` takes the list to append to; `unpackCString#`
    /// ends at `[]`.
    pub appends: bool,
}

impl Unpacker {
    pub fn arity(self) -> u32 {
        if self.appends { 2 } else { 1 }
    }

    /// `Addr# -> [Char]`, or `Addr# -> [Char] -> [Char]`.
    pub fn signature(self) -> Ty {
        let result = string_ty();
        let body = if self.appends {
            arrow(result.clone(), result)
        } else {
            result
        };
        arrow(addr_ty(), body)
    }
}

fn con(name: &str, occ: &str, args: Vec<Ty>) -> Ty {
    Ty::Con {
        tycon: TyConId {
            name: name.into(),
            occ: occ.into(),
            unique: Default::default(),
        },
        args,
    }
}

fn arrow(arg: Ty, res: Ty) -> Ty {
    Ty::Fun {
        mult: Box::new(con("$ghc-prim$GHC.Types$Many", "Many", vec![])),
        arg: Box::new(arg),
        res: Box::new(res),
    }
}

pub fn addr_ty() -> Ty {
    con("$ghc-prim$GHC.Prim$Addr#", "Addr#", vec![])
}

pub fn char_ty() -> Ty {
    con(h2r_core_ir::CHAR_TYCON, "Char", vec![])
}

/// `[Char]`, which is what every one of these unpackers returns.
pub fn string_ty() -> Ty {
    con(h2r_core_ir::LIST_TYCON, "List", vec![char_ty()])
}

pub fn is_addr(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Addr#" && args.is_empty())
}

/// Resolve an unbound global occurrence to an unpacker.
///
/// The occurrence must be a global this world cannot link, whose `IdInfo` is
/// its own and says it is an ordinary Id rather than a primop or a class
/// operation. Its *arity* is deliberately not checked: for an imported Id with
/// no unfolding GHC records whatever this compilation inferred, which is 0
/// under `-O0` and 1 under `-O1` for the same function, so it is a fact about
/// the dump and not about `unpackCString#`.
///
/// What carries the weight instead is the site. The caller requires the spine
/// to be saturated at this unpacker's own argument count, its address argument
/// to be a string literal, and its result to be `[Char]`; in well-typed Core
/// that pins the signature asserted here.
pub fn resolve(module: &Module, head: ExprId) -> Option<Unpacker> {
    let Expr::Var { name, .. } = module.expr(head) else {
        return None;
    };
    let info = module.id_info(head)?;
    if info.name != *name || !info.details.is_empty() {
        return None;
    }
    let unpacker = match name.as_str() {
        "$ghc-prim$GHC.CString$unpackCString#" => Unpacker {
            encoding: Encoding::Latin1,
            appends: false,
        },
        "$ghc-prim$GHC.CString$unpackCStringUtf8#" => Unpacker {
            encoding: Encoding::Utf8,
            appends: false,
        },
        "$ghc-prim$GHC.CString$unpackAppendCString#" => Unpacker {
            encoding: Encoding::Latin1,
            appends: true,
        },
        "$ghc-prim$GHC.CString$unpackAppendCStringUtf8#" => Unpacker {
            encoding: Encoding::Utf8,
            appends: true,
        },
        _ => return None,
    };
    Some(unpacker)
}

/// The code points a literal denotes under one encoding, reproducing
/// `GHC.CString`'s own walk, which never validates.
///
/// A `LitString`'s bytes are the string's own; the NUL the unpackers stop at
/// is added when the code generator lays them out, so the end of the array is
/// the end of the string here. An embedded NUL still ends it, which is why
/// GHC encodes one inside a literal as the overlong `C0 80` instead.
///
/// A truncated multi-byte sequence at the end is a malformed literal here
/// rather than a read past the end, which is what GHC would do.
pub fn decode(bytes: &[u8], encoding: Encoding) -> Result<Vec<u32>, String> {
    let mut out = Vec::new();
    let mut at = 0;
    while at < bytes.len() {
        let first = bytes[at];
        if first == 0 {
            return Ok(out);
        }
        if encoding == Encoding::Latin1 {
            out.push(u32::from(first));
            at += 1;
            continue;
        }
        // GHC subtracts the leading byte's marker and each continuation byte's
        // 0x80, then shifts. A byte that cannot start a sequence, or one that
        // is not a continuation, would make that arithmetic negative; GHC never
        // emits either, and guessing what it would mean is not this pass' job.
        let (width, lead) = match first {
            0x00..=0x7f => (1, u32::from(first)),
            0xc0..=0xdf => (2, u32::from(first) - 0xc0),
            0xe0..=0xef => (3, u32::from(first) - 0xe0),
            0xf0..=0xf7 => (4, u32::from(first) - 0xf0),
            _ => return Err("string literal has a byte that starts no UTF-8 sequence".into()),
        };
        let rest = bytes
            .get(at + 1..at + width)
            .ok_or("string literal ends inside a multi-byte sequence")?;
        if rest.iter().any(|byte| !(0x80..=0xbf).contains(byte)) {
            return Err("string literal has a malformed UTF-8 continuation byte".into());
        }
        let codepoint = rest
            .iter()
            .fold(lead, |acc, byte| (acc << 6) + (u32::from(*byte) - 0x80));
        out.push(codepoint);
        at += width;
    }
    Ok(out)
}

/// The string literal an unpacker's address argument denotes: the literal
/// itself, or a top-level binding whose right-hand side is one. GHC's full
/// laziness floats a literal out to its own `Addr#` binding, so the common
/// shape is the second.
pub fn address_literal<'a>(
    world: &super::World<'a>,
    module_index: usize,
    source: ExprId,
) -> Option<&'a h2r_core_ir::Lit> {
    let module = world.at(module_index).ok()?;
    let string = |lit: &'a h2r_core_ir::Lit| (lit.kind == "string").then_some(lit);
    if let Expr::Lit(lit) = module.expr(source) {
        return string(lit);
    }
    let (owner, binder) = match module.reference(source) {
        Some(h2r_core_ir::Ref::Local(binder))
            if matches!(module.binding(binder).site, h2r_core_ir::BindSite::Top) =>
        {
            (module_index, binder)
        }
        Some(h2r_core_ir::Ref::Global) => {
            let Expr::Var { name, .. } = module.expr(source) else {
                return None;
            };
            super::linkage::imported_top(world, name).ok()?
        }
        _ => return None,
    };
    let owner_module = world.at(owner).ok()?;
    let mut rhs = owner_module
        .top
        .iter()
        .flat_map(|bind| &bind.pairs)
        .find(|pair| pair.binder == binder)
        .map(|pair| pair.rhs)?;
    while let Expr::Tick(body) = owner_module.expr(rhs) {
        rhs = *body;
    }
    match owner_module.expr(rhs) {
        Expr::Lit(lit) => string(lit),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latin1_takes_one_byte_per_character_and_stops_at_the_terminator() {
        assert_eq!(decode(b"hi\0", Encoding::Latin1).unwrap(), vec![104, 105]);
        assert!(decode(b"\0rest\0", Encoding::Latin1).unwrap().is_empty());
        assert_eq!(decode(b"\xff", Encoding::Latin1).unwrap(), vec![255]);
        // GHC's bytes carry no terminator; the array's end is the string's end.
        assert_eq!(decode(b"hi", Encoding::Latin1).unwrap(), vec![104, 105]);
    }

    #[test]
    fn utf8_decodes_every_width_and_ghc_s_overlong_nul() {
        // é, €, 𝄞: two, three and four bytes.
        assert_eq!(
            decode("é€𝄞\0".as_bytes(), Encoding::Utf8).unwrap(),
            vec![0xe9, 0x20ac, 0x1d11e]
        );
        // GHC encodes an embedded NUL as C0 80, which is not valid UTF-8 and
        // which Rust's own decoder rejects; this one must accept it.
        assert_eq!(
            decode(b"a\xc0\x80b\0", Encoding::Utf8).unwrap(),
            vec![0x61, 0x00, 0x62]
        );
        assert!(decode(b"\xe2\x82", Encoding::Utf8).is_err());
        assert!(decode(b"\x80", Encoding::Utf8).is_err());
    }

    #[test]
    fn an_unpacker_s_signature_is_the_one_ghc_gives_it() {
        let plain = Unpacker {
            encoding: Encoding::Latin1,
            appends: false,
        };
        let appending = Unpacker {
            encoding: Encoding::Utf8,
            appends: true,
        };
        assert_eq!(plain.signature(), arrow(addr_ty(), string_ty()));
        assert_eq!(
            appending.signature(),
            arrow(addr_ty(), arrow(string_ty(), string_ty()))
        );
        assert_eq!((plain.arity(), appending.arity()), (1, 2));
    }
}
