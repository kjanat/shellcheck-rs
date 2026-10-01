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

| package                                                | commit               | small (150 lines) | medium (1500 lines) | peak RSS medium |
| ------------------------------------------------------ | -------------------- | ----------------- | ------------------- | --------------- |
| chase move-out, apply fast path, direct tail calls     | `6199812`            | −4 %              | −8 %                | =               |
| WP1 thin cells                                         | `f11d5f6`            | −16 % (±9)        | −12 % (±4)          | 1355 → 1252 MiB |
| WP3 one-allocation closures + WP2 Field 16 bytes       | `ddccda5`, `13871e9` | −17 % (±14)       | −14 % (±3)          | 1252 → 861 MiB  |
| WP7 direct call when forced next + WP6 Args (reverted) | `9749e67`, `a2de2f8` | −5 % (±12)        | +2 % … +7 % (±5)    | =               |
| WP7 alone (WP6 reverted)                               | `fa6ee0b`            | −2 % (±11)        | −2 % (±3)           | =               |
| WP8 plain `mi_malloc` for ≤16-byte alignment           | `9985548`            | −3 % (±14)        | −8 % (±3)           | 861 → 779 MiB   |

(Each row against the binary before it, same machine, hyperfine -N, 10 runs; output byte-identical to the GHC oracle on the conformance gate.)

The WP6+WP7 row is a wash in wall time but **+4.2 % instructions** (5.34 G → 5.57 G, callgrind, same script). The allocator shrank by 0.19 G, yet the `Args` small-vector added about 0.44 G: `Args::push` 113 M and `From<[Field; N]>` 78 M as out-of-line calls, `take_front`/`into_vec`/`Vec::extend(Args::IntoIter)` 82 M, and `memcpy` up 78 M from moving a 72-byte `Args` by value through `apply`, the vtable `call` slot and the `k_` shims (a `Vec` is 24 bytes). WP6 was reverted in `fa6ee0b`; WP7 stays (it is roughly neutral in instructions and does not raise any count).

WP7 alone: 5.34 G → 5.26 G instructions (−1.5 %). WP8: 5.26 G → **4.71 G (−10.5 %)**; the `mi_theap_malloc_aligned`/`_generic`/`_overalloc` entries are gone and the allocator is now `mi_free` 8.5 %, `_mi_theap_malloc_zero` 7.6 %, `mi_malloc` 2.7 %, `_mi_malloc_generic` 0.9 %: about 19.6 % of the run, down from 26 %.

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

| scenario        | what one operation is                                              |         n | Ir/op |
| --------------- | ------------------------------------------------------------------ | --------: | ----: |
| `thunk-chain`   | one indirection in a chain forced once (`chase`, constant stack)   |   100 000 |   251 |
| `thunk-each`    | `delay1` thunk returning `Int`, created and forced                 |   100 000 |   445 |
| `apply`         | `Closure::bind` (one capture) and a saturated `apply`              |   100 000 |   545 |
| `apply-partial` | `bind`, `apply` to one of two arguments, `apply` to the other      |   100 000 | 1 418 |
| `cons`          | one `Data::ready(":", ..)` cell built, then the list dropped       |    10 000 |   413 |
| `match`         | `force` and a five-arm `match` on the constructor name, as emitted | 1 000 000 |    43 |
| `deferred-data` | `Field::data()` on an evaluated `Field::Deferred`                  | 1 000 000 |    55 |

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

### WP5 Strings as a packed intrinsic

The big one; needs a census first: how many `:` nodes come from `unpack_string`/`append_list`/generated `Data::ready(":")`. Add counters behind a `stats` feature, rebuild, run on the corpus, then design.

## Hand-back format

For a work package, report: the diff; the before/after lines from `tests/alloc.rs` and `tests/layout.rs`; Miri's result; which invariant you had to think hardest about and why it still holds. Do not run step 4–7 yourself unless asked: the integrator does, one at a time.
