//! Allocation budgets for the runtime's primitives.
//!
//! These are the fast feedback loop for representation work: a change to how
//! cells, closures or nodes are laid out shows up here in seconds, instead of
//! after the 25-minute rebuild of the generated ShellCheck crates. Each test
//! pins the number of heap allocations an operation may make; lower it when
//! an improvement lands, never raise it without saying why in the commit.
//!
//! Run: `cargo test -p h2r-rt --test alloc`

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use h2r_rt::{Closure, Constructor, Data, Field, Int, Step};

/// The constructors these tests build; the tags only have to differ.
fn constructor(name: &str) -> &'static Constructor {
    static C: Constructor = Constructor { name: "C", tag: 0 };
    static NIL: Constructor = Constructor { name: "[]", tag: 1 };
    static CONS: Constructor = Constructor { name: ":", tag: 2 };
    match name {
        "C" => &C,
        "[]" => &NIL,
        ":" => &CONS,
        other => panic!("no constructor {other}"),
    }
}

struct Counting;

static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

static LOCK: Mutex<()> = Mutex::new(());

/// Allocations and bytes made while running `f`, per iteration of `n`.
/// The counters are global, so measurements take turns.
fn measure(n: usize, mut f: impl FnMut()) -> (usize, usize) {
    let _serial = LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    f(); // warm anything lazily initialised
    let (a0, b0) = (
        ALLOCATIONS.load(Ordering::Relaxed),
        BYTES.load(Ordering::Relaxed),
    );
    for _ in 0..n {
        f();
    }
    let (a1, b1) = (
        ALLOCATIONS.load(Ordering::Relaxed),
        BYTES.load(Ordering::Relaxed),
    );
    ((a1 - a0) / n, (b1 - b0) / n)
}

thread_local! { static SINK: Cell<i64> = const { Cell::new(0) }; }

fn k_add((captured,): &(i64,), arguments: Vec<Field>) -> Field {
    Field::Int64(captured + arguments[0].int64())
}

fn j_add((captured,): &(i64,), arguments: Vec<Field>) -> Step<i64> {
    Step::Done(captured + arguments[0].int64())
}

fn k_add2((captured,): &(i64,), arguments: Vec<Field>) -> Field {
    Field::Int64(captured + arguments[0].int64() + arguments[1].int64())
}

#[test]
fn ready_constructor_is_one_allocation() {
    let (allocations, _) = measure(1000, || {
        let node = Data::ready(constructor("C"), [Field::Int64(1), Field::Char(2)]);
        SINK.with(|s| s.set(s.get() + node.force().fields.len() as i64));
    });
    assert_eq!(allocations, 1, "a ready two-field node is one cell");
}

#[test]
fn thunk_to_ready_node_is_two_allocations() {
    let (allocations, _) = measure(1000, || {
        let node = Data::defer_to(|| Data::ready(constructor("C"), [Field::Int64(1)]));
        SINK.with(|s| s.set(s.get() + node.force().fields.len() as i64));
    });
    eprintln!("thunk -> ready node: {allocations} allocations");
    assert!(
        allocations <= 2,
        "thunk -> ready node made {allocations} allocations"
    );
}

/// One link of a chain of `n` indirections ending in a ready node.
fn chain(n: u32) -> Data {
    if n == 0 {
        Data::ready(constructor("C"), [Field::Int64(1)])
    } else {
        Data::defer_to(move || chain(n - 1))
    }
}

/// `chase` keeps the cells it passes through in a `Vec` only for those that
/// someone else still holds. An unshared chain must not allocate it: the cost
/// of forcing is exactly one cell per link plus the final node.
#[test]
fn an_unshared_chain_allocates_one_cell_per_link_and_no_bookkeeping() {
    let (allocations, _) = measure(1000, || {
        let head = chain(8);
        SINK.with(|s| s.set(s.get() + head.force().fields.len() as i64));
    });
    eprintln!("chain of 8 thunks -> ready node: {allocations} allocations");
    assert!(
        allocations <= 9,
        "a chain of 8 thunks made {allocations} allocations"
    );
}

/// A cell in the middle of a chain that something else holds does need the
/// `Vec` (its value is memoised for its other holder): one more allocation
/// than the cells themselves, and the other holder sees the value afterwards.
#[test]
fn a_shared_cell_in_a_chain_costs_exactly_the_bookkeeping_vector() {
    let (allocations, _) = measure(1000, || {
        let middle = chain(4);
        let held = middle.clone();
        let head = Data::defer_to(move || middle);
        SINK.with(|s| s.set(s.get() + head.force().fields.len() as i64));
        assert!(held.is_evaluated());
    });
    eprintln!("head -> shared chain of 4: {allocations} allocations");
    // head, four links and the node, plus the vector.
    assert!(
        allocations <= 7,
        "a shared chain made {allocations} allocations"
    );
}

#[test]
fn a_delayed_int_is_two_allocations() {
    fn incremented(a: i64) -> Int {
        Int::ready(a + 1)
    }
    let (allocations, _) = measure(1000, || {
        let thunk: Int = h2r_rt::delay1(incremented, (std::hint::black_box(1),));
        SINK.with(|s| s.set(s.get() + thunk.force()));
    });
    eprintln!("delay1 thunk -> ready int: {allocations} allocations");
    assert!(
        allocations <= 2,
        "a delayed int made {allocations} allocations"
    );
}

#[test]
fn bind_and_saturated_apply_budget() {
    let (allocations, _) = measure(1000, || {
        let closure = Closure::bind(1, k_add, (40,));
        let result = closure.apply(vec![Field::Int64(2)]);
        SINK.with(|s| s.set(s.get() + result.int64()));
    });
    // The cell (captures and function pointer live in its code tail) and the
    // caller's argument vector.
    eprintln!("bind + apply: {allocations} allocations");
    assert!(
        allocations <= 2,
        "bind + apply made {allocations} allocations"
    );
}

#[test]
fn bind_entering_and_entered_apply_budget() {
    let (allocations, _) = measure(1000, || {
        let closure = Closure::bind_entering(1, k_add, j_add, (40,));
        match closure.apply_tail(vec![Field::Int64(2)]) {
            h2r_rt::Tail::Enter(step) => SINK.with(|s| s.set(s.get() + step.run())),
            h2r_rt::Tail::Value(_) => panic!("a saturated call with an entry was applied"),
        }
    });
    eprintln!("bind_entering + apply_tail: {allocations} allocations");
    assert!(
        allocations <= 2,
        "bind_entering + apply_tail made {allocations} allocations"
    );
}

#[test]
fn partial_application_budget() {
    let (allocations, _) = measure(1000, || {
        let closure = Closure::bind(2, k_add2, (40,));
        let partial = closure.apply(vec![Field::Int64(1)]).closure();
        let result = partial.apply(vec![Field::Int64(1)]);
        SINK.with(|s| s.set(s.get() + result.int64()));
    });
    // bind (1) + first args vec, which becomes the partial's `supplied` + partial
    // cell + second args vec + merged vec
    eprintln!("partial application: {allocations} allocations");
    assert!(
        allocations <= 5,
        "partial application made {allocations} allocations"
    );
}

#[test]
fn ready_int_is_one_allocation() {
    let (allocations, _) = measure(1000, || {
        let n = Int::ready(7);
        SINK.with(|s| s.set(s.get() + n.force()));
    });
    assert_eq!(allocations, 1);
}

#[test]
fn cons_list_is_one_allocation_per_cell() {
    let (allocations, bytes) = measure(100, || {
        let mut list = Data::ready(constructor("[]"), []);
        for c in 0..100 {
            list = Data::ready(constructor(":"), [Field::Char(c), Field::Data(list)]);
        }
        let mut walked = 0;
        let mut cur = list;
        loop {
            let node = cur.force();
            if node.constructor.name == "[]" {
                break;
            }
            walked += node.fields[0].char_code();
            let next = node.fields[1].data();
            cur = next;
        }
        SINK.with(|s| s.set(s.get() + walked));
    });
    eprintln!("cons list of 100: {allocations} allocations");
    assert!(
        allocations <= 101,
        "one cell per cons plus the nil, got {allocations}"
    );
    // Bytes per character of a String today; the representation work lowers this.
    // (A ready cell's code is zero bytes: count + vtable + the 64-byte node.)
    let per_cell = bytes / 101;
    assert!(per_cell <= 80, "a cons cell costs {per_cell} bytes");
    eprintln!("cons cell: {per_cell} bytes");
}
