//! The allocator the compiled program runs on, shared with the microbench.
//!
//! `crates/rshellcheck` installs [`Allocator`] as its global allocator, and
//! `crates/h2r-rt/examples/ops.rs` installs the same one so the instruction
//! counts of `scripts/rt-instrs.sh` are paid by the allocator the real binary
//! uses (glibc's malloc costs about 140 instructions per malloc/free pair,
//! mimalloc's fast path about 20; a microbench on the wrong one misleads).

use std::alloc::{GlobalAlloc, Layout};

/// mimalloc, called the way C calls it.
///
/// The `mimalloc` crate routes every allocation through `mi_malloc_aligned`,
/// and mimalloc v3 takes that function's fast path only for power-of-two size
/// classes: a 48-, 72- or 80-byte block (a cons cell, most thunks, a three- or
/// five-field argument vector) goes through the over-allocating generic path
/// instead, about 70 extra instructions and a larger size class each time,
/// which was 4.6 % of the instructions of a run. `malloc` itself guarantees
/// 16-byte alignment for any block at least that large (mimalloc rounds its
/// small size classes to multiples of 16), so a layout that needs no more than
/// that uses the plain entry points; only an over-aligned layout, or one
/// smaller than its alignment, pays for alignment.
pub struct Allocator;

impl Allocator {
    const MAX_ALIGN: usize = 16;

    #[inline]
    fn natural(align: usize, size: usize) -> bool {
        align <= Self::MAX_ALIGN && align <= size
    }
}

unsafe impl GlobalAlloc for Allocator {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = if Self::natural(layout.align(), layout.size()) {
            unsafe { libmimalloc_sys::mi_malloc(layout.size()) }
        } else {
            unsafe { libmimalloc_sys::mi_malloc_aligned(layout.size(), layout.align()) }
        };
        p.cast()
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = if Self::natural(layout.align(), layout.size()) {
            unsafe { libmimalloc_sys::mi_zalloc(layout.size()) }
        } else {
            unsafe { libmimalloc_sys::mi_zalloc_aligned(layout.size(), layout.align()) }
        };
        p.cast()
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        unsafe { libmimalloc_sys::mi_free(ptr.cast()) }
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let p = if Self::natural(layout.align(), new_size) {
            unsafe { libmimalloc_sys::mi_realloc(ptr.cast(), new_size) }
        } else {
            unsafe { libmimalloc_sys::mi_realloc_aligned(ptr.cast(), new_size, layout.align()) }
        };
        p.cast()
    }
}
