//! `Addr` arithmetic and bounds through an installed literal table. The table
//! is process-global, so every test here shares one.
use std::panic::catch_unwind;

use h2r_rt::{Addr, install_literals};

static LITERALS: [&[u8]; 3] = [b"abc\0", b"", b"xyz\0"];

fn install() {
    install_literals(&LITERALS);
}

#[test]
fn indexing_and_plus_follow_the_literal() {
    install();
    let first = Addr::literal(0);
    assert_eq!(first.index_word8(0), i64::from(b'a'));
    assert_eq!(first.index_char(2), i64::from(b'c'));
    assert_eq!(first.index_word8(3), 0);
    let moved = first.plus(2);
    assert_eq!(moved.index_word8(0), i64::from(b'c'));
    assert_eq!(moved.index_word8(-2), i64::from(b'a'));
    assert_eq!(moved.plus(-1).index_word8(0), i64::from(b'b'));
    // Another literal is a different address with its own offset.
    assert_eq!(Addr::literal(2).plus(1).index_word8(1), i64::from(b'z'));
    // `Addr` is a plain copyable handle.
    let copy = moved;
    assert_eq!(copy.index_word8(0), moved.index_word8(0));
    assert_eq!(std::mem::size_of::<Addr>(), 8);
}

#[test]
fn reading_outside_a_literal_panics() {
    install();
    let outcome = |f: fn()| catch_unwind(f).is_err();
    assert!(outcome(|| {
        Addr::literal(0).index_word8(4);
    }));
    assert!(outcome(|| {
        Addr::literal(0).index_word8(-1);
    }));
    assert!(outcome(|| {
        Addr::literal(1).index_word8(0);
    }));
    assert!(outcome(|| {
        Addr::literal(3).index_word8(0);
    }));
    assert!(outcome(|| {
        Addr::literal(0).plus(-1);
    }));
    assert!(outcome(|| {
        Addr::literal(0).plus(i64::MAX);
    }));
    assert!(outcome(|| {
        Addr::literal(0).plus(i64::from(u32::MAX) + 1);
    }));
}

#[test]
fn installing_twice() {
    install();
    // The same table again is a no-op.
    install();
    // A different table is a bug.
    static OTHER: [&[u8]; 1] = [b"other\0"];
    assert!(catch_unwind(|| install_literals(&OTHER)).is_err());
    // And the first table is still the one in force.
    assert_eq!(Addr::literal(0).index_word8(1), i64::from(b'b'));
}
