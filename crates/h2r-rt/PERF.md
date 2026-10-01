# Runtime performance: facts, invariants, and how to work on it

This is the working guide for making the compiled ShellCheck faster. It is written so that someone (or a cheaper model) who has not read the whole runtime can pick up one work package, verify it in seconds, and hand it back with evidence. Read all of it before touching `src/lib.rs`.

## Where the time goes (measured)

Callgrind on the compiled ShellCheck checking a 150-line script (7.6 G instructions, h2r-compiler @ `1e14647`):

| bucket                                               |    share | what it is                                   |
| ---------------------------------------------------- | -------: | -------------------------------------------- |
| mimalloc alloc/free                                  |    ~22 % | 76 M allocations for one small script        |
| `Rc` drop chains (Node, ClosureCode, Field, Vec)     |    ~16 % | freeing those allocations                    |
| lazy machinery (`chase`, `Data::force`, node copies) |    ~13 % | mostly fixed by `6199812`                    |
| `Closure::apply` + argument vectors                  |     ~7 % |                                              |
| constructor-name `memcmp`                            |     ~1 % | pattern matches compare `&'static str`       |
| generated code proper                                | the rest | not the bottleneck; opt-level 3 measured 0 % |

Dynamic counts behind the 76 M allocations:

| source                          |  count |       allocations each |
| ------------------------------- | -----: | ---------------------: |
| `delayN` thunks (`f_` wrappers) | 17.8 M |                      1 |
| `Closure::bind`                 |  7.5 M |         1 (WP3; was 2) |
| `apply_later` thunks            |  5.5 M | 1 + the argument `Vec` |
| `Closure::apply`                |  2.4 M |       1–2 `Vec<Field>` |
| `Data::ready` (constructors)    |  2.6 M |                      1 |

The gap to GHC is ~19×. GHC wins on exactly these things: a bump allocator, a generational GC, 24-byte cons cells, pointer tagging. We cannot copy the GC, so the lever is **fewer and smaller allocations**.

## Representation today (`cargo test -p h2r-rt --test layout` prints it)

| type                              | bytes | why                                                                                                   |
| --------------------------------- | ----: | ----------------------------------------------------------------------------------------------------- |
| `Data`, `Int`, `Closure`          |     8 | `Shared<T>`: one thin pointer to one allocation (WP1, `f11d5f6`)                                      |
| `Field`                           |    16 | tag + largest payload; every payload is 8 bytes (`Addr` is a `u32` literal index + `u32` offset, WP2) |
| `Node`                            |    64 | `&'static str` constructor (16) + `Fields` (3 inline `Field`s + tag)                                  |
| one `String` character (`:` cell) |    80 | 16-byte header + `Node`; a ready cell's code tail is zero-sized                                       |

`cargo test -p h2r-rt --test alloc` prints the allocation counts per primitive and pins them. Every improvement lowers a number there.

### Landed

| package                                            | commit    | small (150 lines) | medium (1500 lines) | peak RSS medium |
| -------------------------------------------------- | --------- | ----------------- | ------------------- | --------------- |
| chase move-out, apply fast path, direct tail calls | `6199812` | −4 %              | −8 %                | =               |
| WP1 thin cells                                     | `f11d5f6` | −16 % (±9)        | −12 % (±4)          | 1355 → 1252 MiB |

(Each row against the binary before it, same machine, hyperfine -N, 10 runs; output byte-identical to the GHC oracle on the conformance gate.)

## Invariants you must keep

1. **Demand.** A block function `b_<instance>_<block>` runs only when its result is demanded to WHNF. Block bodies force things; running one early is a semantic change (it can diverge or throw where Haskell would not). The emitter relies on this; the runtime must never call generated code speculatively (`map_list` and friends defer every application).
2. **Sharing.** A `Shared<T>` cell is evaluated at most once and every holder sees the same value. `shares_with` is observable (tests use it). Knot-tying (`pending()` + `fill()`) must keep working: a cell can be created empty, handed out, and filled later.
3. **Re-entrancy is `<<loop>>`.** Forcing a cell whose code is already running must panic, not recurse or return garbage.
4. **Constant stack for indirection chains.** `tests::a_million_indirections_force_in_constant_stack`. Tail calls within a recursive group return thunks on purpose (that is the trampoline); do not "optimise" that away in the runtime.
5. **Field tags are exact.** `Field::Char` vs `Field::Int64` and the panics in `Field::int()`, `data()`, `closure()` are how miscompiles surface. Keep them.
6. **Drop is recursive today.** Long lists drop recursively; the program runs on a big stack (`on_program_stack`). Do not make drop deeper.
7. **Do not retain.** A forwarding/indirection scheme that keeps an extra cell alive per value was tried (`c1d8448`) and cost +57 % peak memory and +17 % time. Values live inline in their cell.

## Verification loops, cheapest first

```sh
# 1. seconds: unit tests, allocation budgets, layout pins
cargo test -p h2r-rt
# 2. two minutes: unsafe code must be clean under Miri (nightly has the component).
#    One test opens a file (hence no isolation); the knot test
#    `a_pending_dynamic_value_ties_a_knot` builds a reference cycle on purpose,
#    so its two allocations leak by design. Run with leaks ignored; the
#    million-indirection test is too slow interpreted, run it natively.
MIRIFLAGS='-Zmiri-disable-isolation -Zmiri-ignore-leaks' \
  cargo +nightly miri test -p h2r-rt -- --skip a_million_indirections
#    If you added unsafe code, also run once WITHOUT -Zmiri-ignore-leaks: the
#    only leaks allowed are the two from that knot test.
# 3. a minute and a half: the emitter's tests, if the emitter changed
cargo test -p h2r-lower
# 4. ~25 min: rebuild the compiled ShellCheck (run alone; never concurrently with tests)
CI=1 cargo build --release --locked -p rshellcheck
# 5. 2 min: conformance gate against the GHC-built oracle (0 differences required)
cargo run --release -p h2r-conformance -- gate \
  --candidate target/release/rshellcheck \
  --oracle <path to the GHC shellcheck built by the hs-shellcheck layer>
# 6. A/B timing against the previous binary with hyperfine -N; peak RSS via wait4
# 7. 10 min: cargo test --workspace
```

Steps 1–3 are the loop for a work package. Steps 4–7 happen once per package, by whoever integrates, and never overlap with each other.

## Work packages

Each has a spec, an acceptance list, and no emitter change unless stated. Do them in order; each is independently landable.

### WP1 Thin shared cells (the primitive everything else builds on)

**Goal.** `Shared<T>` becomes a thin 8-byte pointer to one allocation that holds the refcount, the value cell and the (unsized) code tail, replacing `Rc<Lazy<T, dyn Code<T>>>`. `Data`, `Int`, `Closure`, `Field::Deferred` go from 16 to 8 bytes; `Field` can then shrink (WP2).

**Design.** A hand-rolled `ThinRc<T>` in a new module `cell.rs`:

```rust
#[repr(C)]
struct Header<T> {
    strong: Cell<usize>,
    vtable: &'static CellVTable<T>, // enter / fill / drop_code / layout of the tail
    value: OnceCell<T>,
}
// allocation = Header<T> followed, at the tail's alignment, by the concrete code C
```

`ThinRc<T>` is `NonNull<Header<T>>`. Construction is generic over the concrete `C: Code<T>` (as `Lazy::step`, `pending`, `ready` are today) and writes the vtable for that `C`. `enter`/`fill` dispatch through the vtable with a pointer to the tail. Drop decrements, runs the value's and the tail's destructors, deallocates with the recorded layout. Single-threaded (`!Send`, `!Sync`), like `Rc`. No `Weak` is needed anywhere (grep: none used).

**Acceptance.**

- `cargo test -p h2r-rt` green, including the million-indirection and `<<loop>>` tests unchanged.
- `cargo +nightly miri test -p h2r-rt` clean.
- `tests/layout.rs`: `Data`, `Int`, `Closure` are 8 bytes (update the pins).
- `tests/alloc.rs`: no allocation count rises.
- `size_of::<Field>()` does not grow.
- Public API of `Data`/`Int`/`Closure`/`Field`/`Lazy` unchanged; the emitter must not need changes (`cargo test -p h2r-lower` green).

### WP2 `Field` to 16 bytes

**Landed (numbers above).** The emitter writes one deduplicated `static LITERALS` into the entry crate and every emitted entry function (`main` of the print/lint drivers, each `pub fn` of the typed API, `emit_program`'s `main`) starts with `h2r_rt::install_literals(&LITERALS)`; reading an `Addr` before that panics. Original spec: needs WP1. The remaining 24-byte payload was `Addr { &'static [u8], usize }`. Replace it with an 8-byte handle: a `u32` index into a literal table the emitter writes (`static LITERALS: &[&[u8]]`) plus a `u32` offset. Emitter change: collect literals, emit the table, `HAddr::literal(index)`. Acceptance: `Field` is 16 bytes, `Node` ≤ 72, cons cell ≤ 96 bytes, conformance gate 0 differences.

### WP3 Single-allocation closures (landed in the working tree, not yet timed)

Needs WP1. A ready closure's captures and `k_` function pointer live in the cell's code tail (a `Code<ClosureCode>` impl whose `enter` is unreachable), so `Closure::bind` is one allocation. `ClosureCode.code` becomes an enum: `Inline` (call through the tail), `Partial { parent: Closure }` for partial application. Acceptance: `bind + apply` ≤ 2 allocations, partial ≤ 5, all tests, Miri.

**As built.** `Closure::bind`/`bind_entering` allocate the cell only: the value is `ClosureCode { arity, entry, kind: Inline }` and the code tail is `Bound<Captures> { code, captures }` (plus `enter` for `BoundEntering`), called through two new vtable slots (`Code::call`, `Code::call_enter`, default `unreachable!`) that `Shared::call`/`call_enter` dispatch. `Closure::ready`/`entering` keep any Rust closure, but inline in the tail (`Boxed<F>`), so they no longer allocate a second time either. A partial application is a small ready cell (`Evaluated` tail) with `Kind::Partial { parent, supplied }`, where `parent` is always the cell with the code (partials of partials are flattened) and the first arguments' vector becomes `supplied` as it is. A thunk that turns out to be a closure (`defer_to`, `pending` + `fill`) still chases `Indirect` links; because the value of a code cell refers to the cell itself and cannot be copied into the thunk, `chase` asks the source cell's code (`Code::shares` / `Code::share`, one `Option` check in the vtable) and the thunk gets `Kind::Forward(cell with the code)`. Dropping a closure drops its captures with the cell, once.

### WP4 Constructor tags

Emitter assigns a `u32` per constructor name; `Node` gains `tag`, matches switch on it, names stay for diagnostics and the runtime's `*Names` structs. Emitter + runtime. Small win (~1–2 %), enables jump tables.

### WP5 Strings as a packed intrinsic

The big one; needs a census first: how many `:` nodes come from `unpack_string`/`append_list`/generated `Data::ready(":")`. Add counters behind a `stats` feature, rebuild, run on the corpus, then design.

## Hand-back format

For a work package, report: the diff; the before/after lines from `tests/alloc.rs` and `tests/layout.rs`; Miri's result; which invariant you had to think hardest about and why it still holds. Do not run step 4–7 yourself unless asked: the integrator does, one at a time.
