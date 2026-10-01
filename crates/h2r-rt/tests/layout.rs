//! Sizes of the value representations, pinned so a change is deliberate.
//! Lower a number when a representation shrinks; never raise one silently.
use std::mem::size_of;

use h2r_rt::{Closure, Data, Field, Int, Node};

#[test]
fn value_sizes() {
    // Shared cells are thin pointers to one allocation holding count, value and code.
    assert!(size_of::<Int>() <= 8, "Int is {}", size_of::<Int>());
    assert!(size_of::<Data>() <= 8, "Data is {}", size_of::<Data>());
    assert!(
        size_of::<Closure>() <= 8,
        "Closure is {}",
        size_of::<Closure>()
    );
    // Field is bounded by its largest payload (every payload is 8 bytes: Addr is a u32 literal
    // index and a u32 offset) plus a tag.
    assert!(size_of::<Field>() <= 16, "Field is {}", size_of::<Field>());
    // A node: a pointer to its constructor (8) + inline fields (3 x Field + tag).
    assert!(size_of::<Node>() <= 64, "Node is {}", size_of::<Node>());
    assert_eq!(size_of::<Node>(), 56, "Node is {}", size_of::<Node>());
    eprintln!(
        "Int {} Data {} Closure {} Field {} Node {}",
        size_of::<Int>(),
        size_of::<Data>(),
        size_of::<Closure>(),
        size_of::<Field>(),
        size_of::<Node>()
    );
}
