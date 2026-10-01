//! Deterministic microbenchmark driver for the runtime's hot paths.
//!
//! `ops <scenario> <n>` runs one scenario `n` times and prints a checksum so
//! nothing is optimised away. It is meant to run under callgrind, where the
//! instruction count is deterministic: `scripts/rt-instrs.sh` runs each
//! scenario with `n = 0` and with `n` and divides the difference, which
//! cancels process start-up and setup. Only the public `h2r_rt` API is used,
//! and each scenario stands for one bucket of the profile in `PERF.md`.
//!
//! Run by hand: `cargo run --release -p h2r-rt --example ops -- apply 1000`

use std::hint::black_box;

/// The allocator of the compiled program, so every Ir/op below includes the
/// allocator cost the real binary pays (see `crates/h2r-alloc`).
#[global_allocator]
static ALLOCATOR: h2r_alloc::Allocator = h2r_alloc::Allocator;

use h2r_rt::{Closure, Constructor, Data, Field, Int, delay1};

/// Constructors as the emitter writes them: one `static` per name, with a
/// program-wide tag; matches switch on the tag and names are for diagnostics.
static NIL: Constructor = Constructor { name: "[]", tag: 0 };
static CONS: Constructor = Constructor { name: ":", tag: 1 };
static LEAF: Constructor = Constructor {
    name: "Leaf",
    tag: 2,
};
/// The five-constructor family of the `match` scenario, as the emitter sees a
/// sum type.
static FAMILY: [Constructor; 5] = [
    Constructor {
        name: "Alpha",
        tag: 3,
    },
    Constructor {
        name: "Beta",
        tag: 4,
    },
    Constructor {
        name: "Gamma",
        tag: 5,
    },
    Constructor {
        name: "Delta",
        tag: 6,
    },
    Constructor {
        name: "Epsilon",
        tag: 7,
    },
];

fn k_add((captured,): &(i64,), arguments: Vec<Field>) -> Field {
    Field::Int64(captured + arguments[0].int64())
}

fn k_add2((captured,): &(i64,), arguments: Vec<Field>) -> Field {
    Field::Int64(captured + arguments[0].int64() + arguments[1].int64())
}

/// One link of the indirection chain: forcing it yields the next link.
fn countdown(n: u64) -> Data {
    if n == 0 {
        Data::ready(&NIL, [])
    } else {
        Data::defer_to(move || countdown(n - 1))
    }
}

fn incremented(a: i64) -> Int {
    Int::ready(a + 1)
}

/// Profile bucket: lazy machinery, `chase` and `Shared::force`. A chain of `n`
/// indirections is forced once; the stack stays constant.
fn thunk_chain(n: u64) -> i64 {
    let head = countdown(n);
    head.force().constructor.name.len() as i64
}

/// Profile bucket: `delayN` thunks (17.8 M in the profile): allocation,
/// forcing and drop glue of a one-capture thunk.
fn thunk_each(n: u64) -> i64 {
    let mut sum = 0;
    for i in 0..n as i64 {
        let thunk: Int = delay1(incremented, (black_box(i),));
        sum += thunk.force();
    }
    sum
}

/// Profile bucket: `Closure::bind` plus a saturated `Closure::apply` with its
/// argument vector.
fn apply(n: u64) -> i64 {
    let mut sum = 0;
    for i in 0..n as i64 {
        let closure = Closure::bind(1, k_add, (black_box(i),));
        sum += closure.apply(vec![Field::Int64(2)]).int64();
    }
    sum
}

/// Profile bucket: partial application, the `Partial` cell and the merged
/// argument vector.
fn apply_partial(n: u64) -> i64 {
    let mut sum = 0;
    for i in 0..n as i64 {
        let closure = Closure::bind(2, k_add2, (black_box(i),));
        let partial = closure.apply(vec![Field::Int64(1)]).closure();
        sum += partial.apply(vec![Field::Int64(2)]).int64();
    }
    sum
}

/// Profile bucket: `Data::ready` (2.6 M constructors) and the recursive drop
/// glue of a list. `n` cons cells are built and dropped; keep `n` modest, the
/// drop recurses.
fn cons(n: u64) -> i64 {
    let mut list = Data::ready(&NIL, []);
    for c in 0..n as i64 {
        list = Data::ready(&CONS, [Field::Char(black_box(c)), Field::Data(list)]);
    }
    black_box(&list);
    n as i64
}

/// Profile bucket: pattern-match dispatch. Forces a node and switches on its
/// constructor tag exactly as `emit.rs` does (`let node = v.force();
/// match node.constructor.tag { .. }`); before WP4 this compared names.
fn matches(n: u64) -> i64 {
    let nodes: Vec<Data> = FAMILY.iter().map(|c| Data::ready(c, [])).collect();
    let mut sum = 0;
    let mut which = 0;
    for _ in 0..n {
        let v = &nodes[black_box(which)];
        which = if which + 1 == nodes.len() {
            0
        } else {
            which + 1
        };
        let node = v.force();
        sum += match node.constructor.tag {
            3 => 1,
            4 => 2,
            5 => 3,
            6 => 4,
            7 => 5,
            _ => panic!("invalid constructor family"),
        };
    }
    sum
}

/// Profile bucket: `Field::data` (3.2 % of the profile) on an evaluated
/// `Field::Deferred`, the shape of a lazily built constructor field.
fn deferred_data(n: u64) -> i64 {
    let field = Field::defer_to(|| Field::Data(Data::ready(&LEAF, [Field::Int64(7)])));
    field.force();
    let mut sum = 0;
    for _ in 0..n {
        let data = black_box(&field).data();
        sum += data.force().fields.len() as i64;
    }
    sum
}

fn main() {
    let usage =
        "usage: ops <thunk-chain|thunk-each|apply|apply-partial|cons|match|deferred-data> <n>";
    let mut args = std::env::args().skip(1);
    let (Some(scenario), Some(n)) = (args.next(), args.next()) else {
        eprintln!("{usage}");
        std::process::exit(2);
    };
    let Ok(n) = n.parse::<u64>() else {
        eprintln!("{usage}");
        std::process::exit(2);
    };
    let checksum = match scenario.as_str() {
        "thunk-chain" => thunk_chain(n),
        "thunk-each" => thunk_each(n),
        "apply" => apply(n),
        "apply-partial" => apply_partial(n),
        "cons" => cons(n),
        "match" => matches(n),
        "deferred-data" => deferred_data(n),
        _ => {
            eprintln!("{usage}");
            std::process::exit(2);
        }
    };
    println!("{checksum}");
}
