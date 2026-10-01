//! Sizes of the value representations, pinned so a change is deliberate.
//! Lower a number when a representation shrinks; never raise one silently.
use std::mem::size_of;

use h2r_rt::{Closure, Data, Field, Int, Node};

#[test]
fn value_sizes() {
    // Shared cells are fat pointers today (Rc<Lazy<T, dyn Code<T>>>): 16 bytes.
    assert!(size_of::<Int>() <= 16, "Int is {}", size_of::<Int>());
    assert!(size_of::<Data>() <= 16, "Data is {}", size_of::<Data>());
    assert!(size_of::<Closure>() <= 16, "Closure is {}", size_of::<Closure>());
    // Field is bounded by its largest payload (a 16-byte cell or the 24-byte Addr) plus a tag.
    assert!(size_of::<Field>() <= 32, "Field is {}", size_of::<Field>());
    // A node: constructor name (16) + inline fields (3 x Field + tag).
    assert!(size_of::<Node>() <= 112, "Node is {}", size_of::<Node>());
    eprintln!(
        "Int {} Data {} Closure {} Field {} Node {}",
        size_of::<Int>(),
        size_of::<Data>(),
        size_of::<Closure>(),
        size_of::<Field>(),
        size_of::<Node>()
    );
}
