<a name="idtop"></a>

# 5 H2R runtime performance

The compiled ShellCheck was ~19–20× slower than GHC's binary when the work started and is ~8× slower now. This page summarises the programme; PERF.md on the branch holds every spec, measurement and as-built paragraph (WP1–WP18, ~570 lines).

## 5.1 Where the time went

*Callgrind, 150-line script, `1e14647`: 7.6 G instructions.*

| bucket                                                      |                               share |
| ----------------------------------------------------------- | ----------------------------------: |
| mimalloc alloc/free (76 M allocations for one small script) |                               ~22 % |
| `Rc` drop chains (Node, ClosureCode, Field, Vec)            |                               ~16 % |
| lazy machinery (`chase`, `Data::force`, node copies)        |                               ~13 % |
| `Closure::apply` + argument vectors                         |                                ~7 % |
| constructor-name `memcmp`                                   |                                ~1 % |
| generated code proper                                       | the rest (opt-level 3 measured 0 %) |

Allocation sources: `delayN` thunks (`f_` wrappers) 17.8 M, `Closure::bind` 7.5 M, `apply_later` thunks 5.5 M (+ the argument `Vec`), `Closure::apply` 2.4 M, `Data::ready` constructors 2.6 M. GHC wins on a bump allocator, a generational GC, 24-byte cons cells and pointer tagging; the lever available here is **fewer and smaller allocations**.

**[⬆ Top](#idtop)**

## 5.2 Representation

*Printed by `cargo test -p h2r-rt --test layout`.*

`Data`/`Int`/`Closure` are 8 bytes (`Shared<T>`: one thin pointer to one allocation); `Field` is 16 bytes (tag + 8-byte payload; `Addr` is a `u32` literal index + `u32` offset); `Node` is 56 bytes (`&'static Constructor` with name + `u32` tag, `Fields` with 3 inline `Field`s); a `String` character cell is 72 bytes. `tests/alloc.rs` pins allocation counts per primitive.

**[⬆ Top](#idtop)**

## 5.3 Landed packages

*Each row vs the binary before it, hyperfine -N 10 runs, byte-identical output on the gate.*

| package                                                     | commit               | small | medium | peak RSS medium |
| ----------------------------------------------------------- | -------------------- | ----: | -----: | --------------- |
| chase move-out, apply fast path, direct tail calls          | `6199812`            |  −4 % |   −8 % | =               |
| WP1 thin shared cells                                       | `f11d5f6`            | −16 % |  −12 % | 1355 → 1252 MiB |
| WP3 one-allocation closures + WP2 Field 16 bytes            | `ddccda5`, `13871e9` | −17 % |  −14 % | 1252 → 861 MiB  |
| WP7 direct call when forced next                            | `9749e67`            |  −2 % |   −2 % | =               |
| WP8 plain `mi_malloc` for ≤ 16-byte alignment               | `9985548`            |  −3 % |   −8 % | 861 → 779 MiB   |
| WP4 constructor tags (`u32` switch instead of `memcmp`)     | `640db5a`            |     = |      = | 779 → 769 MiB   |
| WP11 thunk path + WP12 constructor cell (microbench-driven) | `13eaa30`, `e1e5d55` | −16 % |  −10 % | =               |
| WP10 call path (microbench-driven)                          | `fab9d15`            |  −4 % |   −6 % | =               |
| WP14 loops instead of trampolines (emitter)                 | `25bc483`            |  −7 % |   −8 % | 767 → 789 MiB   |

Instruction counts on the small script: 7.58 G → 5.34 G (WP1–3) → 5.26 G (WP7) → 4.71 G (WP8) → 4.57 G (WP4) → 3.99 G (WP11+12) → 3.74 G (WP10) → **3.45 G (WP14), −54 % cumulative**. On CI's bench the compiled program went from ~20× to ~8× slower than upstream.

**Negative results, kept on record:** WP6 (argument lists as an inline small-vector instead of a `Vec`) cost +4.2 % instructions and was reverted (`fa6ee0b`): the copies and out-of-line push/convert calls outweighed the saved malloc, because mimalloc's fast path is ~60 instructions per malloc/free pair. WP15 (apply the callee directly when forced next) was withdrawn: its premise was wrong, `apply_later` is the tail-call trampoline, not a forced-next call. An earlier forwarding/indirection scheme (`c1d8448`) cost +57 % peak memory and +17 % time and was replaced by moving values out of dying cells (`6199812`).

**[⬆ Top](#idtop)**

## 5.4 Invariants

*Must hold for every change.*

1. **Demand**: a block function `b_<instance>_<block>` runs only when its result is demanded to WHNF; the runtime never calls generated code speculatively.
2. **Sharing**: a `Shared<T>` cell evaluates at most once; `shares_with` is observable; knot-tying (`pending()` + `fill()`) must keep working.
3. **Re-entrancy is `<<loop>>`**: forcing a running cell panics.
4. **Constant stack for indirection chains** (`a_million_indirections_force_in_constant_stack`); tail calls within a recursive group return thunks on purpose (that is the trampoline).
5. **Field tags are exact**; the panics in `Field::int()/data()/closure()` are how miscompiles surface.
6. **Drop is recursive today**; the program runs on a big stack; do not make drop deeper.
7. **Do not retain** an extra cell per value (see `c1d8448`).
8. **A representation change must remove work, not only a malloc**; check with callgrind on the compiled program, not only the allocation counters.

**[⬆ Top](#idtop)**

## 5.5 Instruments built for the programme

- **Microbench** `scripts/rt-instrs.sh` / `mise run rt:instrs` (WP9): `crates/h2r-rt/examples/ops.rs` runs one scenario `n` times; callgrind with `n = 0` and `n` gives `Ir/op`, deterministic to the digit. Scenarios: thunk-chain, thunk-each, apply, apply-partial, cons, match, deferred-data. Current rows (mimalloc, `h2r-alloc`): 110 / 225 / 234 / 710 / 123 / 26 / 47 Ir/op. The first table was measured on glibc malloc and misleads for anything allocation-heavy; always compare under the same allocator.
- **Allocation census** (WP13, `a484874`): runtime counters behind the `stats` feature (`cargo build --release -p rshellcheck --features stats`, `H2R_CENSUS=1`), printing thunk fates per cell kind at exit. Finding: 51 % of thunks were trampoline hops → WP14.
- **Site-attributed census** (WP17a, `a683676`): every emitter `delayed()` site and the tail `apply_later` site get a dense `u32` id; the cell header carries it only with `stats`; at exit the top 40 sites by unforced and by created count are printed with the emitter rule and Core form that made them. Non-stats emission text is byte-identical (pinned by a test).

**[⬆ Top](#idtop)**

## 5.6 What the census said

*WP17a results, `a683676`.*

After WP14 the looping-tail hops fell from 3.75 M to 0.25 M on the small script (36 M → 3.2 M on medium). What remains splits into three kinds, **each worth ~2 % of the run**:

- *Never forced* (13 % of thunks): one site, `nodeChecksToTreeCheck` b4 in Analytics (a `case` thunk per AST node per check), is 15 % of them; parsec's `satisfy` b2 error-message continuations another 20 %; `setExpectErrors`, `composeAnalyzers`, lazy `StateT`/`ReaderT` binds the rest. All are lazy arguments or constructor fields whose body is an `App` or `Case`; GHC's demand analysis left them lazy because they are used on the error path, so the emitter cannot evaluate them eagerly without a per-site safety argument. ~70 M of 3.45 G.
- *`f_` wrapper thunks chased at once* (0.65 M / 6.1 M): a known function called through a closure allocates two cells where one would do → **WP18** (closure shims call `b_` directly), ~2 %.
- *Tail-apply hops* (1.8 M / 17 M): the CPS trampoline through unknown closures → **WP16** (a non-allocating tail apply; changes every block signature), ~3 %.

Everything else is the model itself: 2.7 M constructor cells, 2.1 M closures, 2.4 M argument vectors per small run are what the Core says the program does. GHC pays ~3 instructions to allocate each and nothing to free; this runtime pays ~20 + 20 plus a refcount per reference. **The incremental programme reached its floor at ~2 % per package.** The remaining ~8× to GHC is representation: unboxed strict fields, packed strings (WP5), an arena or a real GC. That is a redesign, not a work package for a cheap agent.

**[⬆ Top](#idtop)**

## 5.7 Verification loops

*Cheapest first.*

1. `cargo test -p h2r-rt` (seconds). 2. Miri (2 min). 3. `cargo test -p h2r-lower` if the emitter changed (1.5 min). 4. **Rebuild the compiled ShellCheck (25–35 min, alone, never concurrently with tests or measurements).** 5. `h2r-conformance gate` (2 min, 0 differences). 6. A/B with hyperfine -N and wait4 RSS (`mise run perf:ab`). 7. `cargo test --workspace` (10 min). Steps 1–3 are a work package's loop; 4–7 happen once per package by the integrator and never overlap.

Hand-back format for a package: the diff; before/after lines from `tests/alloc.rs` and `tests/layout.rs`; Miri's result; which invariant needed the most thought and why it still holds.

**[⬆ Top](#idtop)**

<a name="idend"></a>
