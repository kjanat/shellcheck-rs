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
| `Node`                            |    56 | `&'static Constructor` (8: name + `u32` tag) + `Fields` (3 inline `Field`s + tag)                     |
| one `String` character (`:` cell) |    72 | 16-byte header + `Node`; a ready cell's code tail is zero-sized                                       |

`cargo test -p h2r-rt --test alloc` prints the allocation counts per primitive and pins them. Every improvement lowers a number there.

### Landed

| package                                                     | commit               | small (150 lines) | medium (1500 lines) | peak RSS medium |
| ----------------------------------------------------------- | -------------------- | ----------------- | ------------------- | --------------- |
| chase move-out, apply fast path, direct tail calls          | `6199812`            | −4 %              | −8 %                | =               |
| WP1 thin cells                                              | `f11d5f6`            | −16 % (±9)        | −12 % (±4)          | 1355 → 1252 MiB |
| WP3 one-allocation closures + WP2 Field 16 bytes            | `ddccda5`, `13871e9` | −17 % (±14)       | −14 % (±3)          | 1252 → 861 MiB  |
| WP7 direct call when forced next + WP6 Args (reverted)      | `9749e67`, `a2de2f8` | −5 % (±12)        | +2 % … +7 % (±5)    | =               |
| WP7 alone (WP6 reverted)                                    | `fa6ee0b`            | −2 % (±11)        | −2 % (±3)           | =               |
| WP8 plain `mi_malloc` for ≤16-byte alignment                | `9985548`            | −3 % (±14)        | −8 % (±3)           | 861 → 779 MiB   |
| WP4 constructor tags                                        | `640db5a`            | = (±16)           | = (±8)              | 779 → 769 MiB   |
| WP11 thunk path + WP12 constructor cell (microbench-driven) | `13eaa30`, `e1e5d55` | −16 % (±13)       | −10 % (±4)          | =               |
| WP10 call path (microbench-driven)                          | `fab9d15`            | −4 % (±14)        | −6 % (±5)           | =               |

(Each row against the binary before it, same machine, hyperfine -N, 10 runs; output byte-identical to the GHC oracle on the conformance gate.)

The WP6+WP7 row is a wash in wall time but **+4.2 % instructions** (5.34 G → 5.57 G, callgrind, same script). The allocator shrank by 0.19 G, yet the `Args` small-vector added about 0.44 G: `Args::push` 113 M and `From<[Field; N]>` 78 M as out-of-line calls, `take_front`/`into_vec`/`Vec::extend(Args::IntoIter)` 82 M, and `memcpy` up 78 M from moving a 72-byte `Args` by value through `apply`, the vtable `call` slot and the `k_` shims (a `Vec` is 24 bytes). WP6 was reverted in `fa6ee0b`; WP7 stays (it is roughly neutral in instructions and does not raise any count).

WP7 alone: 5.34 G → 5.26 G instructions (−1.5 %). WP8: 5.26 G → **4.71 G (−10.5 %)**; the `mi_theap_malloc_aligned`/`_generic`/`_overalloc` entries are gone and the allocator is now `mi_free` 8.5 %, `_mi_theap_malloc_zero` 7.6 %, `mi_malloc` 2.7 %, `_mi_malloc_generic` 0.9 %: about 19.6 % of the run, down from 26 %. WP4 (`640db5a`): 4.71 G → **4.57 G (−2.8 %)**; the constructor-name `memcmp` is gone, `Node` is 56 bytes, and the microbench `match` row went 43 → 32 Ir/op. WP11 + WP12 (`e1e5d55`): 4.57 G → **3.99 G (−12.8 %)**, the first packages driven entirely by the microbench (thunk-each 270 → 225, thunk-chain 161 → 110, cons 168 → 123 Ir/op under mimalloc): `chase<Node>` 4.2 → 2.5 %, `force` 3.2 → 2.1 %, the `OnceCell` drop glue entries are gone, allocator share 19.6 → 22 % of a smaller total. WP10 (`fab9d15`): 3.99 G → **3.74 G (−6.2 %)**; `Closure::apply` 4.5 % → `apply_general` 2.5 %, `drop_glue::<ClosureCode>` gone (`drop_kind` 0.7 %). Cumulative since the first profile: 7.58 G → 3.74 G, **−51 %**, output byte-identical at every step. The allocator is now 27 % of what is left (count-driven: see WP13).

### Profile after WP1–WP3 (`e156aea`, same 150-line script)

5.34 G instructions (was 7.58 G). Allocator ~26 %, drop glue ~8 %, `chase<Node>` 4 %, `Closure::apply` 4.3 %, `Field::data` 3.2 %, `Shared<Node>::force` 2.9 %, constructor-name `memcmp` 1.4 %. Allocation *sizes* are now small; the remaining lever is allocation *count*: the `delayN` thunks (17.8 M) and the `Vec<Field>` built for every unknown call (`apply` 2.4 M + `apply_later` 5.5 M).

## Invariants you must keep

1. **Demand.** A block function `b_<instance>_<block>` runs only when its result is demanded to WHNF. Block bodies force things; running one early is a semantic change (it can diverge or throw where Haskell would not). The emitter relies on this; the runtime must never call generated code speculatively (`map_list` and friends defer every application).
2. **Sharing.** A `Shared<T>` cell is evaluated at most once and every holder sees the same value. `shares_with` is observable (tests use it). Knot-tying (`pending()` + `fill()`) must keep working: a cell can be created empty, handed out, and filled later.
3. **Re-entrancy is `<<loop>>`.** Forcing a cell whose code is already running must panic, not recurse or return garbage.
4. **Constant stack for indirection chains.** `tests::a_million_indirections_force_in_constant_stack`. Tail calls within a recursive group return thunks on purpose (that is the trampoline); do not "optimise" that away in the runtime.
5. **Field tags are exact.** `Field::Char` vs `Field::Int64` and the panics in `Field::int()`, `data()`, `closure()` are how miscompiles surface. Keep them.
6. **Drop is recursive today.** Long lists drop recursively; the program runs on a big stack (`on_program_stack`). Do not make drop deeper.
7. **Do not retain.** A forwarding/indirection scheme that keeps an extra cell alive per value was tried (`c1d8448`) and cost +57 % peak memory and +17 % time. Values live inline in their cell.
8. **mimalloc's fast path is cheap: about 60 instructions for a malloc/free pair.** Replacing one small heap allocation with a by-value small-vector was tried (`a2de2f8`, reverted in `fa6ee0b`) and cost +4 % instructions: the copies and the out-of-line push/convert calls outweighed the saved allocation. A representation change must remove *work* (fewer calls, fewer bytes touched), not only a `malloc`; check with callgrind on the compiled program, not only with the allocation counters.

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

### Microbench (`scripts/rt-instrs.sh`)

A deterministic instruction-count number for the runtime's hot paths in about 10 seconds, instead of the 25-minute rebuild. `crates/h2r-rt/examples/ops.rs` runs one scenario `n` times using only the public API; the script runs it under callgrind with `n = 0` and with `n`, and prints `(Ir_n - Ir_0) / n`, the instructions per operation. Callgrind counts do not depend on machine load, so repeated runs agree exactly (two runs on `e8e6be9` matched to the last digit in every scenario; the limit is 0.1 %). Needs `valgrind`; builds with `cargo build --release -p h2r-rt --example ops` and respects `CARGO_TARGET_DIR`.

```sh
scripts/rt-instrs.sh                  # all scenarios
scripts/rt-instrs.sh apply cons       # some of them
mise run rt:instrs                    # same, through mise
```

Each scenario stands for one bucket of the profile above. `Ir/op` includes the loop's own overhead and the drop of what the operation made, but not process start-up or the scenario's one-time setup (the `n = 0` run cancels those). It is the runtime built as a library at `opt-level 3`, so inlining into emitted code is not modelled: use it to rank changes, then confirm on the compiled program (step 4 onward), as invariant 8 says.

| scenario        | what one operation is                                             |         n | Ir/op |
| --------------- | ----------------------------------------------------------------- | --------: | ----: |
| `thunk-chain`   | one indirection in a chain forced once (`chase`, constant stack)  |   100 000 |   123 |
| `thunk-each`    | `delay1` thunk returning `Int`, created and forced                |   100 000 |   225 |
| `apply`         | `Closure::bind` (one capture) and a saturated `apply`             |   100 000 |   355 |
| `apply-partial` | `bind`, `apply` to one of two arguments, `apply` to the other     |   100 000 |   956 |
| `cons`          | one `Data::ready(":", ..)` cell built, then the list dropped      |    10 000 |   168 |
| `match`         | `force` and a five-arm `match` on the constructor tag, as emitted | 1 000 000 |    26 |
| `deferred-data` | `Field::data()` on an evaluated `Field::Deferred`                 | 1 000 000 |    49 |

(Measured on `13eaa30` plus the `h2r-alloc` crate (`44ec7c4`), with the example on the same mimalloc allocator as the binary. The first table, on `e8e6be9`, ran on glibc's malloc, about 140 instructions per malloc/free pair against mimalloc's ~20, and read 251 / 445 / 545 / 1 418 / 413 / 43 / 55; those numbers mislead about anything allocation-heavy and are superseded. Since then WP4 took `match` 43 → 32 → 26 and WP11 took the thunk rows from 161 / 270 to 123 / 225 under mimalloc.)

Baseline measured on `e8e6be9` (the head before WP9), rustc 1.98.1 release profile, valgrind 3.22.0, x86-64. Re-measure before and after your change and quote both lines in the hand-back. `cons` keeps `n` at 10 000 because dropping a list is recursive (invariant 6); do not raise it past what the 8 MiB main-thread stack takes.

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

**As built.** The runtime has `pub struct Constructor { name: &'static str, tag: u32 }` (`PartialEq`/`Eq` by tag, `Debug`/`Display` by name) and `Node { constructor: &'static Constructor, fields }`: `Node` is 56 bytes (`tests/layout.rs` pins exactly 56 and keeps the `<= 64` bound; `Data`/`Int`/`Closure` stay 8 and `Field` 16, so a `:` cell is 72 bytes). Every `*Names`/`Truth`/`Orderings`/`CallStackNames` field is a `&'static Constructor`; runtime checks (`cell.constructor == names.nil`) compare tags and panics print `.name`. The runtime itself hardcodes no constructor (the one `":"` was in a test); unit tests build theirs from a `fixtures` module. The emitter has a `Constructors` interner (next to `Literals`) that numbers every constructor name densely in first-use order, one instance per emission (`prepare`, or `emit_program`), so all crates of a program agree. A crate cannot name another crate's static and the runtime is pasted per crate, so nothing relies on addresses: every crate (the entry crate and each `emit_entry_split` member, the single-crate output and `emit_library`) ends with private `static C_<tag>: HConstructor = HConstructor { name, tag }` for exactly the tags its text mentions (found by scanning the generated text for `C_` followed by a number; a test pins that the runtime text never spells one). `HData::ready(&C_<tag>, ..)`, `HListNames { cons: &C_a, .. }` and friends use the statics; `match_data`, the `dataToTag#` arm, the `isTrue`/`Maybe`/`Either` readers and the `show` helpers switch on or compare `node.constructor.tag` with integer literals (catch-all arms and their panics kept, now printing `node.constructor`). Not timed here (the rebuild is the integrator's). Two things to know when timing: tags are first-use numbers, so a change to the program's constructor set can renumber, and therefore rebuild, every crate in the content-hash cache; and a match is a jump table only where rustc finds its tags dense, which the interner makes likely (tags start at 0) but a family's arms are only a subset of the program's constructors.

### WP6 Argument vectors without heap allocation (tried, reverted)

Every call through a closure builds a `Vec<Field>` (`vec![...]` in the emitted code, `a: Vec<HField>` in the `k_` shims, `Vec<Field>` throughout `apply`/`apply_tail`/`apply_later`/`apply_step`/`Partial`). A small-vector `Args` with inline capacity 4 (72 bytes, `Len` niche as the tag, spill to `Vec` on the fifth push, `Box<[Field]>` for a partial application's supplied arguments) was built in `a2de2f8`. The counters did what the spec asked (`bind + apply` 2 → 1 allocation, partial 5 → 3, Miri clean) and the compiled program got **slower by 4.2 % in instructions** (see the Landed table), so it was reverted in `fa6ee0b`. Reasons, from the profile: the 72-byte value is moved through three layers per call, the push/from/take_front helpers were not inlined into the emitted crates (they live in the pasted-in runtime module, where `#[inline]` would have been needed), and `apply` still converted back to a `Vec` in the partial path. If this is picked up again: keep the by-value type at 24 or 32 bytes (inline capacity 1, since `From<[Field; 1]>` was the hot constructor), mark every helper `#[inline]`, remove every `into_vec`, and prove the instruction count on the compiled program before the gate.

### WP7 Call the entry block directly when the result is forced next

A non-tail `CallTop` whose result is the scrutinee of the very next `MatchData`, or the operand of the very next `Force`, allocates a thunk that is forced immediately. Emit `b_<target>_<entry>(args)` instead of `f_<target>(args)` for those sites (7 % of call sites statically). Same stack shape as forcing the thunk, so no group check is needed; keep `f_` for zero-argument calls (CAFs). Emitter only; add a test that such a site emits `b_` and an unforced one still emits `f_`.

### WP8 Call mimalloc the way C does (landed, `9985548`)

Found from the callgrind call tree, not from the counters: `mi_theap_malloc_zero_aligned_at_generic` was called 3.0 M times and 2.9 M of those went on to `_overalloc`. The `mimalloc` crate routes every Rust allocation through `mi_malloc_aligned`, and mimalloc v3 (what `libmimalloc-sys` 0.1.49 builds by default) takes that function's fast path only when the size class is a power of two, so every 48-, 72- or 80-byte block, which is a cons cell and most thunks, paid about 70 extra instructions and landed in a larger size class. `crates/rshellcheck/src/main.rs` now has a `GlobalAlloc` that calls `mi_malloc`/`mi_zalloc`/`mi_realloc` when the layout's alignment is at most 16 and at most its size (what `malloc` guarantees; mimalloc rounds small size classes to multiples of 16) and the aligned entry points otherwise. Binary crate only, so it needs no compiler rebuild: `cargo build --release -p rshellcheck` relinks in seconds. Lesson for the next person: read the call tree (`callgrind_annotate --tree=both --inclusive=yes`) under the allocator, not only the flat profile.

### WP10 The call path, by the microbench

`apply` costs 355 Ir/op and `apply-partial` 956 under mimalloc (545 and 1 418 were glibc numbers): a `bind` (one cell), a `vec![..]` for the argument, the `apply` dispatch, the call, and dropping both. Profile the example itself (`valgrind --tool=callgrind target/release/examples/ops apply 100000` then `callgrind_annotate`) and take out what is not the call: `Shared` header writes that the caller re-does, `split()` re-checking an already evaluated code cell, `Field::closure`/`int64` tag checks on the hot path that could be one match, `Vec` capacity checks, drop glue that runs through `OnceCell` state tests for cells that are known evaluated. Keep `Vec<Field>` as the argument carrier (WP6 shows why). Acceptance: `apply` ≤ 270 Ir/op and `apply-partial` ≤ 720 on the microbench (mimalloc), `tests/alloc.rs` budgets not above today's, `cargo test -p h2r-rt`, Miri clean if any `unsafe` moved, `cargo test -p h2r-lower` if an emitted shape changed. Report the before/after microbench table.

**As built.** `apply` 352 → **234** Ir/op and `apply-partial` 948 → **710** (targets ≤ 270 and ≤ 720, both reached), measured with `scripts/rt-instrs.sh` on `72c7b68` and on the final tree, mimalloc, same machine; no scenario got worse:

| scenario        | before (`72c7b68`) | after |
| --------------- | -----------------: | ----: |
| `thunk-chain`   |                110 |   110 |
| `thunk-each`    |                225 |   225 |
| `apply`         |                352 |   234 |
| `apply-partial` |                948 |   710 |
| `cons`          |                123 |   123 |
| `match`         |                 26 |    26 |
| `deferred-data` |                 47 |    47 |

One harness change is part of the "after": `examples/ops.rs` now marks each scenario function `#[inline(never)]`. They were all inlined into `main`, so the register allocation of one scenario moved another's count by an instruction (an `apply` change made `thunk-each` read 226, a spare `mov` in the loop, with no runtime code involved). With the scenarios apart the "before" tree reads 351 / 947 for the two rows that moved and the same as above for the rest; the table quotes the original harness for "before" (what `72c7b68` prints) and the new one for "after".

Profile first (`apply`, per op, before): `Closure::apply` 71, `main` 60 (the `vec!`), `mi_free` 46 and `mi_malloc` 54 (two allocations, two frees: the allocator is not ours), `k_add` 44, `drop_glue::<ClosureCode>` 23, `ClosureCode::inline` 19 (out of line, with its `assert` and `try_from`), `Block::free` 10, `drop_glue::<Field>` 10, `Field::int64` 8. `apply-partial` spent most of its extra on `apply` doing everything for every call, `Vec::extend(iter().cloned())` (36 Ir for one cloned field) and the `ClosureCode`/`Kind` glue (a `Partial` drop was 44).

What each change was and bought (`apply` / `apply-partial`, each measured in turn on the tree before it):

- **`ClosureCode(Kind)`, `repr(u8)`, `arity`/`entry` inside the variants, and a saturated-call fast path.** The old `ClosureCode { arity, entry, kind }` hid `Kind`'s discriminant in the capacity word of `supplied` (about ten instructions to decode on every call and drop). `Kind` is now `repr(u8)` (`Inline { entry, arity }`, `Partial { entry, arity, parent, supplied }`, `Forward`), 40 bytes, so the discriminant is a byte at offset 0. `apply` is `#[inline]` and does only `force()`, a tag compare and the arity compare before `self.0.call(arguments)`; everything else is `#[inline(never)] apply_general` (a thunk that turned out to be a closure, a partial application, too few arguments) and `apply_over` (too many, the old loop). 352 → 271 / 948 → 891.
- **`ClosureCode`'s drop is a test in line.** `ClosureCode` holds a `ManuallyDrop<Kind>` and `impl Drop` checks `Inline` (owns nothing) and calls an out-of-line `drop_kind` otherwise, so `Block::free`'s drop of the value is a compare, not a call into the enum's glue. Plus `#[inline]` on `Field::int64`. 271 → 239 / 891 → 852.
- **`call_with` and `partial` `#[inline(always)]` into `apply_general`** (as out-of-line functions the argument vector was copied through two more frames): 852 → 803. Kept out of line, measured again at the end: 750 and 751.
- **`drop_kind` drops the supplied arguments with `drop_field`** (the helper `Fields` uses: no call for an integer or character, an inline decrement for a cell) and then frees the vector: 785 → 776.
- **`joined(supplied, arguments, capacity)`**: the merged argument vector of a call through a partial application is one allocation, the supplied fields cloned with a plain loop (`extend_from_slice` and `Vec::extend(iter().cloned())` both went through an out-of-line `Cloned::fold`, 36 Ir for one field: 803 → 785) and the arguments moved with `copy_nonoverlapping` (`unsafe`, below); a single argument, the usual last one of a partial application, is a 16-byte move and not a call to `memcpy` (−11), and the capacity passed is the arity (a `u32`), so `Vec::with_capacity` needs no multiplication-overflow check (−10); 776 → 728 together.
- **The forced `ClosureCode` is passed on.** `apply` already holds it, so `apply_general` takes it and `decode`s it (`Closure::decode` is the old `resolve` + `split` in one match, `split` is `decode(self, self.0.force())`), rather than forcing and matching again in the out-of-line function: 751 → 738.
- **`Field::closure` is `#[inline]` and its thunk case is out of line** (`closure_other`, as `deferred_data` for `data()`): 728 → 712 (`apply` +2 from layout). In the pasted-in runtime LLVM decides inlining itself; the hint is what the example, a separate crate, needs, and the real binary gets no worse.

Tried and not kept (each measured): `Vec::extend(arguments)` for the arguments instead of `append`/the copy (+37 on `apply-partial`: the `IntoIter` and its drop); a `debug_assert!` instead of the `assert!` in `joined` (+6, the optimiser lost the bound); an `Int64` fast path in the clone loop (−2: microbench-specific, not worth a branch); `call_with` or `partial` out of line after the other changes (+22 / +23).

Not done: the `Block` for a partial application is still written from a stack copy of its 40-byte `ClosureCode` (about 10 Ir, same cause as WP12's `Node`); a second argument vector is still allocated for a call through a partial application (`apply-partial` is 5 allocations, as pinned: the bind, the caller's vector, which the partial application adopts, the partial cell, the caller's second vector, the merged vector) because the callee's `Vec<Field>` shape is fixed (WP6).

Double force: the fast path forces the cell to test it and the general path forces again. A thunk's code runs once (the second `force` is a load of the memoised value, and `Forward` is decoded without a third), so invariant 2 holds; the cost is one load on the slow path only. Invariants: 1 (nothing speculative: `apply` calls code only for a saturated call and `apply_over` calls it only for arguments it was given), 2 and 3 as above, 5 (`Field::closure`/`int64` keep their tags and panics), 6 (`drop_kind` is not deeper than the glue it replaces: the partial application's fields and parent are dropped one after another), 8 (every change removed calls or bytes touched, and the `joined` and `drop_kind` ones were measured against the safe version first). `tests/alloc.rs` counts are unchanged (`bind + apply` 2, partial 5); `tests/layout.rs` unchanged.

Unsafe: two places in `lib.rs`, each with a `SAFETY` comment: `joined` (writes `count + moved` fields into a vector with that much room, then moves the arguments' fields and zeroes their vector's length so they are dropped once, by the merged vector; a panic in a clone, there is none, would leak and not double-drop) and `drop_kind` (the length of `supplied` is set to zero before its fields are dropped one by one, then the vector and the parent). `ClosureCode`'s `Drop` itself is safe code (a tag test and a call). Miri: clean with `-Zmiri-ignore-leaks` (60 unit tests, `alloc` 10, `layout` 1) and without it the only leaks are the two of `a_pending_dynamic_value_ties_a_knot`; two tests were added (`a_partial_application_holds_each_supplied_argument_once`, which counts a reference-counted field across clone, saturate and drop through three partial applications, and `too_many_arguments_for_a_partial_application_apply_the_result_to_the_rest`). The emitted shapes (`bind`, `bind_entering`, `apply`, `apply_tail`, `apply_later`, `apply_step`, the `k_` shim) are untouched; `cargo test -p h2r-lower` passes. Not timed on the compiled program (the integrator's rebuild).

### WP11 The thunk path, by the microbench

`thunk-each` cost 445 Ir/op (create a one-capture `delay1`, force it, drop it) and `thunk-chain` 251 per indirection on glibc; 270 and 161 under mimalloc. Per step that is a `Block` allocation and free (about 40 together under mimalloc), the `Once` enter/fill handshake, the `OnceCell` write and the `chase` loop with its `pending` `Vec` (allocated only when a cell is shared, check that it really stays unallocated in the common path), then drop glue through `OnceCell<Node>`/`OnceCell<ClosureCode>`, which is 5 % of the whole program. Same method as WP10: profile the example, remove re-checks. Acceptance: `thunk-each` ≤ 320 and `thunk-chain` ≤ 190 Ir/op, allocation counts unchanged, constant-stack test still passes, Miri clean (this is `cell.rs`, it will involve `unsafe`), `cargo test -p h2r-rt`.

**As built.** `thunk-each` 445 → **400** and `thunk-chain` 251 → **217** Ir/op: the acceptance numbers (≤ 320 and ≤ 190) are **not reached, and cannot be with this microbench**, for a reason found only by profiling it: `scripts/rt-instrs.sh` builds the example against **glibc malloc** (the real binary uses mimalloc through `rshellcheck`'s `GlobalAlloc`), and under glibc one malloc/free pair is about 140 Ir (`malloc` 45, `free` 28 + `_int_free` 54, the `__rust_alloc`/`__rdl_alloc`/`__rust_dealloc` wrappers about 20). `thunk-each` makes two (the thunk, and the fresh `Int` its body returns, which `chase` moves out of and frees), so 286 of its 445 instructions were the allocator before this package and 286 of 400 are now; 320 would leave 34 Ir for creating, entering, forcing, memoising and freeing, and the whole remaining runtime path is about 110. `thunk-chain` has one pair per link (140 of 251, now 140 of 217; 190 would leave 50). The numbers that the targets were meant to express are the ones with the allocator the program runs with, so the same two scenarios were also measured (scratch crate, not committed) with the example linked against `libmimalloc-sys` through the same `natural()`-alignment `GlobalAlloc` as `rshellcheck`: **`thunk-each` 270 → 225 (−17 %), `thunk-chain` 161 → 123 (−24 %)**; both were already under the glibc targets before the change. Removing an allocation is the only way to go further and was out of scope (`tests/alloc.rs` pins two allocations for a thunk that returns a fresh cell, and the emitted entry returns that cell, not a value).

| scenario        | before (`1e96e8a`) | after | what moved it                                                           |
| --------------- | -----------------: | ----: | ----------------------------------------------------------------------- |
| `thunk-chain`   |                251 |   217 | inline `free` −20, `Entered` out-parameter −14                          |
| `thunk-each`    |                445 |   400 | `chase` bookkeeping guard −21, `force_slow` fast path −23, `Entered` −1 |
| `apply`         |                545 |   535 | `Slot` (−20 against `OnceCell`), the rest of the force path             |
| `apply-partial` |              1 418 | 1 405 | as `apply`                                                              |
| `cons`          |                412 |   411 |                                                                         |
| `match`         |                 32 |    26 | `Shared::force` is the one-load fast path, the slow path is out of line |
| `deferred-data` |                 55 |    49 | as `match`                                                              |

(Same machine and tool versions as the baseline; the `after` column is the final tree, the "what moved it" column is each change measured in turn on `thunk-each`/`thunk-chain`. Under mimalloc, all seven, before → after: `thunk-chain` 161 → 123, `thunk-each` 270 → 225, `apply` 364 → 355, `apply-partial` 968 → 956, `cons` 169 → 168, `match` 32 → 26, `deferred-data` 55 → 49.)

What each change was, and what it bought:

- **`chase` no longer constructs and drains its `pending` vector when it is empty** (`if !pending.is_empty()` around the `for`): `into_iter` plus its `Drop` was 21 Ir for a loop over nothing. The vector itself was never allocated (it is `Vec::new()`); `tests/alloc.rs` now pins that: `an_unshared_chain_allocates_one_cell_per_link_and_no_bookkeeping` (a chain of 8 makes 9 allocations, one per cell), and `a_shared_cell_in_a_chain_costs_exactly_the_bookkeeping_vector` (a cell in the chain that another handle holds costs exactly one more, and that handle sees the value). `a_delayed_int_is_two_allocations` pins the `thunk-each` shape. −21 on `thunk-each`.
- **`Shared::force` is `get()` or `force_slow()`.** The first is the one-load fast path that is inlined everywhere; the slow path (enter, then take the value, then memoise) is `#[inline(never)]`. It also handles the common indirection itself: a thunk whose body ended in a fresh, already evaluated cell takes that cell's value in place (`take_evaluated`, shared with `chase` through `value_of_evaluated`) instead of calling `chase`, whose prologue saves six registers and sets up the vector. −23 on `thunk-each`, and `match`/`deferred-data` −6 because the inlined fast path got smaller. `chase` still runs for every other chain, so the constant-stack test is untouched.
- **`Block::free` is written out instead of `drop(Box::from_raw(..))`**: the value is tested in line and dropped only if there is one, then the code is dropped in place, then `dealloc` with `Layout::new::<Block<T, C>>()` (what `Box` used). The `Box` glue called `drop_glue::<Option<Node>>` out of line even for the `None` of a thunk `chase` moved through: 14 Ir per link. −20 on `thunk-chain`, nothing on `i64` cells.
- **`Entered`: the vtable's `enter` no longer returns `Option<Thunk<T>>` by value.** A `Thunk<Node>` is 64 bytes and every hop of `chase` copied it to read an 8-byte `Indirect`; now `enter` writes a value through an out pointer (`MaybeUninit<T>` the caller owns) and returns `Entered::{Looping, Value, Indirect(Shared)}`, 16 bytes in registers. The `Code::enter` trait method is unchanged (`Block::enter` converts). −14 on `thunk-chain`; a `Value` result is no longer copied through the `Option<Thunk<T>>` temporary.
- **`Slot<T>`, the header's value cell**: an `UnsafeCell<Option<T>>` (the layout of `OnceCell<T>`) whose `settle` looks at the state once and writes in place. It buys nothing on `thunk-each`/`thunk-chain` (the optimiser had already merged `get_or_init`'s checks for `i64` and `Node`) but 20 Ir on `apply` and 24 on `apply-partial`, where `T` is `ClosureCode` and `get_or_init` was not inlined; kept for that. `OnceCell::get_or_init` semantics are kept: the first value wins, so a `fill` that races an evaluation cannot overwrite a value a `&T` already points at.

Tried and not kept: nothing was reverted for cost, but a safe `Slot(OnceCell<T>)` was measured against the `UnsafeCell` one (see above) and lost on the `apply` scenarios, and writing a `Thunk::Value` result straight into the cell's own slot from `enter` was considered and not built (it would memoise cells that `chase` deliberately leaves unmemoised, an extra 56-byte copy for the one-hop case). Not done because the microbench cannot see it: moving the value from the fresh cell into the thunk's slot directly (one copy of the 56-byte `Node` instead of two) is worth about 8 Ir per `Data` thunk, about 0.14 G of the 4.57 G profile (17.8 M thunks).

Unsafe: the file's `unsafe` is now in five places (the vtable casts, the free of a block, the shared reference to the header, `take_unique`, `Slot`); each has a `SAFETY` comment and Miri passes (see the hand-back). Public names are unchanged; the emitter pastes `cell.rs` as before (`cargo test -p h2r-lower` green).

### WP12 Building and dropping a constructor cell, by the microbench

`cons` costs 168 Ir/op under mimalloc (412 was a glibc number) to build one `Data::ready(":", [c, rest])` and drop it later. A ready cell should be one allocation written once: look at `Shared::ready_with`, `Fields::from([Field; 2])`, the `Evaluated` tail and the free path (`Block<Node, Evaluated>::free` is 0.6 % of the program on its own), and at `drop_glue::<OnceCell<Node>>` (3.6 % of the program). Acceptance: `cons` ≤ 125 Ir/op (mimalloc), `Node` stays ≤ 64 bytes and the alloc pins hold, Miri clean, `cargo test -p h2r-rt`.

**As built.** `cons` 168 → **123** Ir/op (≤ 125 reached), measured with `scripts/rt-instrs.sh` on `3995f92` and on the final tree, mimalloc, same machine; nothing else got worse:

| scenario        | before (`3995f92`) | after |
| --------------- | -----------------: | ----: |
| `thunk-chain`   |                123 |   110 |
| `thunk-each`    |                225 |   225 |
| `apply`         |                355 |   352 |
| `apply-partial` |                956 |   948 |
| `cons`          |                168 |   123 |
| `match`         |                 26 |    26 |
| `deferred-data` |                 49 |    47 |

Profile first (`cons`, per cell, before): `drop_glue::<Option<Node>>` 45, the Rust side of `main` (build the 72-byte block on the stack, copy it to the heap) 30, `drop_glue::<Field>` 18, `Block::free` 10, mimalloc 22 (`mi_free`) + 27 (`mi_malloc`, `_mi_theap_malloc_zero`). The free path was 73 of the 168 and is where the instructions went; the allocator (about 50) is not ours.

What each change was and bought (`cons` unless noted, each measured in turn on the tree before it):

- **`Fields` drops itself** (`impl Drop for Fields`; the inline arrays and the vector are `ManuallyDrop`). The compiler's glue for `Option<Node>` was a 7-register prologue, a jump table and a loop with an unwinding cleanup per array; the hand-written drop drops the fields one after another and skips the call into `Field`'s glue for the two payloads that own nothing (`Int64`, `Char`: a string is nearly all of these). 168 → 154. A field whose drop panics now leaks the later ones instead of dropping them during the unwind: memory only, and nothing in the runtime drops a panicking value.
- **`Block::free` tests the slot and drops the `T` inside**, not `drop_in_place::<Slot<T>>` behind a second `is_some` (the `Option<T>` glue was an out-of-line call for the `Some` too). 154 → 152 on `cons`, and **123 → 111 on `thunk-chain`**, where the last node of the chain is freed through it.
- **The vector of `Many` out of line and cold** (`ManuallyDrop<Vec<Field>>`, `drop_many`): its drop loop was inlined into every node's glue and cost the 4-field case nothing but a call. 151 → 140.
- **The `Data` arm of `drop_field` inline** (`Shared`'s `Drop`: decrement, and the vtable `free` on zero) instead of a call into `Field`'s glue and its jump table. 140 → 135.
- **`Shared::alloc` allocates, then writes** (`std::alloc::alloc` and `ptr::write` of the fields) instead of `Box::new(Block { .. })`, which assembled the 72-byte block on the stack and copied it. The block is still written from the stack copy of its `Node`; see below. 135 → 133, `thunk-chain` 111 → 109, `apply-partial` 954 → 948.
- **`Fields::drop` handles `Zero` and `Two` inline and sends the rest out of line** (`drop_other`), so the match is two compares and not a jump table. 133 → 131.
- **A head that owns nothing leaves the tail as a tail call.** `Two` with an `Int64`/`Char` first field (every `:` of a string) drops its second field as the last thing the function does, so `drop_glue::<Node>` has no stack frame on that path (no pushes, a jump into the next `free`); a head that may own something goes through `drop_two` out of line. 131 → **123**. It also inlined the now-small glue into `Block::free`, which made the optimiser assemble the empty slot of a thunk on the stack and copy it (`thunk-chain` 109 → 118); writing the block's header, slot and code **field by field** (`alloc_block`, `alloc`, `alloc_empty`) fixed that: `thunk-chain` 118 → 110.
- **`deferred_data` out of line** (`Field::data` on a field that is still a thunk). The earlier `alloc` change made `data()` carry the allocation's registers and frame on its hot (already evaluated) path: `deferred-data` 49 → 51. Moving the thunk-making branch into an `#[inline(never)]` function gave 47, better than before.

Tried and not kept (each measured, each reverted): building the `Node` **after** the allocation so that it is written once into the heap, by a closure (`ready_from`), by `settle`, and by writing through a pointer to the slot (`Data::ready` with a `vacant_ready`), each with and without destructuring `From<[Field; N]>`: `cons` 143, 146, 158, 138 and 139 against 133 at the time. rustc builds the `Fields` enum from the array by value through two or three stack copies that LLVM does not fold (they copy the enum's padding word as part of a 36-byte move that is not aligned with the array's own stores), and every shape that put the allocation first only added copies; the single 56-byte copy from the stack that remains costs about 10 Ir of the 123 and is the part of "written once" this package did not get. A loop over the fields as a slice instead of the match (+2), putting `Two` first in an `if let` (0), and specialising `Block<Node, _>::free` with `TypeId` to inline the node's drop into it (0 on the microbench, and code bloat in every `Block<Node, Once<closure>>` instantiation, of which a program has thousands): not kept.

Latent bug found on the way, fixed before it landed: the first version of `impl Drop for Fields` dropped the `Many` vector and then left it to the compiler's glue as well; a `fields_drop_tests` module (arities 0 to 6, every kind of `Field`, a long list) pins that each field is dropped exactly once.

Invariants: 6 (drop is recursive) is unchanged in depth: per cell it is the same chain of calls (`Shared::drop`, the vtable `free`, the node's glue), the glue's frame went from seven saved registers to none on the `:` path, and a list of 5 000 cells drops in the test. `tests/alloc.rs` counts are the same (`:` cell 72 bytes, 1 allocation; thunk to ready node 2; `bind + apply` 2; partial 5) and `tests/layout.rs` still reads `Node` 56, `Field` 16, `Data` 8. `Fields` is still the same enum with the same variant names and `Deref<Target = [Field]>`, but its payloads are now `ManuallyDrop<..>`: the emitter only writes `node.fields[i]` and `HData::ready(&C_n, [..])`, never a `Fields` variant, so `emit.rs` is unchanged (`cargo test -p h2r-lower` passes, and the runtime pasted as one source file compiles). Unsafe: `cell.rs` has one more place (the field-by-field write of a fresh block, with a `SAFETY` comment) and `Fields::drop` and its helpers in `lib.rs` (documented there). Miri: clean with `-Zmiri-ignore-leaks`, and without it the only leaks are the two of `a_pending_dynamic_value_ties_a_knot` (`cargo +nightly miri test -p h2r-rt`, 58 unit tests, `alloc` 10, `layout` 1). Not timed on the compiled program (the integrator's rebuild).

For WP10–WP12 the integrator rebuilds once with all three, gates, and times; the microbench is the fast loop and its numbers are the acceptance.

### WP13 Allocation census by emitter site

After WP1–WP12 the allocator is ~22 % of a 3.99 G run and every allocation is small and cheap (~20 instructions per malloc/free pair); what is left is the *count*. The old table (76 M allocations: `delayN` 17.8 M, `bind` 7.5 M, `apply_later` 5.5 M, `apply` 2.4 M, `Data::ready` 2.6 M) came from callgrind call counts and does not say *which emitter sites* make the thunks or how many are forced at all. Build the census: a `stats` cargo feature on `h2r-rt` with per-kind counters (`delayN` by N, `apply_later`, `bind`, `bind_entering`, partial applications, `Data::ready` by arity, `Field::defer_to`, and for every thunk whether it was forced, moved out unique, shared, or dropped unforced), printed at exit when the feature is on; plus an emitter-side static census (`h2r-lower`: how many `DelayBlock` sites by origin rule and by what they wrap: a call, a `case`, a `let`, a lazy argument of an external, an `f_` wrapper) written as a table to stderr under an env var. Acceptance: feature off changes nothing (microbench rows identical, `cargo test -p h2r-rt`); feature on prints the table; the integrator rebuilds once with the feature, runs the 150-line and 1500-line scripts, and pastes both tables here. The next packages are chosen from them: the kind with the largest "created but dropped unforced" count is the first target (a thunk nobody forces should not be allocated: the emitter can often prove the demand, or the runtime can defer the allocation), then the largest "forced exactly once by its creator" kind (a candidate for evaluating in place instead of allocating).

**As built.** Runtime side: `h2r-rt` has a `stats` feature (`src/stats.rs`, off by default; with it off the microbench rows are unchanged: thunk-chain 110, thunk-each 225, apply 234, apply-partial 710, cons 123, match 26, deferred-data 47 Ir/op). The counters are thread-local `Cell<u64>`s; the program thread flushes them into process totals when `on_program_stack` ends, and `on_program_stack` prints the table to stderr after joining it (once per process for `rshellcheck`, which wraps its whole run in one call; the Lint driver's generated `main` does the same). It counts `delayN`/`stepN` by N, `Int/Data/Closure/Field::defer_to`, `apply_later`, `apply_step`, `bind`, `bind_entering`, boxed `Closure::ready/entering`, partial applications, `apply`/`apply_general`/`apply_over`, `Data::ready` by arity (0, 1, 2, 3, 4+), `Field::data` of a thunk, and per cell kind (Int, Data, Closure, Field, other): thunks made (`Shared::step`, every thunk whatever made it), pending cells, evaluated cells, first force of a unique or a shared cell, entered by `chase` (held once: moved through and never memoised, or shared: memoised), freed still holding code (a thunk nobody forced: `unforced`, with its share of those created), and values moved out unique or cloned from an evaluated cell. A thunk is counted by the kind of its cell, not by the emitter site that made it: the join with sites is the static table below. Emitter side: `H2R_CENSUS=1` at emit time makes `h2r-lower` print, to the build script's stderr, tables of `delayed()` sites by where they are written (`DelayBlock` instruction, `f_` wrapper of a lifted result, `f_` wrapper of a CAF, looping tail call, looping tail `case` arm, looping tail jump), by origin (site / rule / Core form: `App` of a global or of a local, `Case`, `Let`, `Var`, ...), by what first uses a `DelayBlock` thunk (argument of a top-level, local or unknown call, constructor field, captured by a closure, lazy argument of an external or primitive, returned, ...), by number of captured arguments, with counts of sites and of captured arguments, and `HData::ready` sites by arity and by origin; sites, not executions. **To turn it on for the compiled program** (do not run it for anything but the census; it is the 25-minute build): `H2R_CENSUS=1 CARGO_INCREMENTAL=0 cargo build --release -p rshellcheck --features stats -vv 2>&1 | tee census-build.log` (the `stats` feature of `rshellcheck` forwards to `shellcheck-core/stats`; `shellcheck-core`'s `build.rs` then compiles the generated crates with `--cfg feature="stats"` through `h2r_lower::build::Rustc::with_stats`, into a build directory of its own because the flags are part of the fingerprint; `H2R_STATS=1` in the environment does the same without the cargo feature, and `build.rs` reruns when either variable changes). The emitter census is in `census-build.log` under the `shellcheck-core` build script (without `-vv`, in `target/release/build/shellcheck-core-*/stderr`); it prints whenever the build script runs (a new feature set or a changed `H2R_CENSUS` reruns it; if cargo says the crate is fresh, `touch crates/shellcheck-core/build.rs`). The runtime census is on stderr of every run of the stats binary: `target/release/rshellcheck script.sh 2> census-run.txt >/dev/null`, for the 150-line and the 1500-line scripts. A normal build (no feature, no variable) is untouched. Unit tests: `cargo test -p h2r-rt --features stats` (one `delay1` thunk made and forced moves exactly `DELAY+1`, `DEFER_TO`, `CREATED`, `FORCED_UNIQUE`, `EVALUATED` and `MOVED_UNIQUE`; unforced, shared and chased cells; `Data::ready` arities; the flush at the end of `on_program_stack`) and the emitter test `the_emitter_census_runs_and_names_every_category_it_saw`. Not run: `cargo build -p rshellcheck` (so `crates/shellcheck-core/build.rs`, which has a few lines more, is untested beyond reading).

### WP5 Strings as a packed intrinsic

The big one; needs a census first: how many `:` nodes come from `unpack_string`/`append_list`/generated `Data::ready(":")`. Add counters behind a `stats` feature, rebuild, run on the corpus, then design.

## Hand-back format

For a work package, report: the diff; the before/after lines from `tests/alloc.rs` and `tests/layout.rs`; Miri's result; which invariant you had to think hardest about and why it still holds. Do not run step 4–7 yourself unless asked: the integrator does, one at a time.
