//! The lazy cell: a thin, single-threaded, reference-counted, call-by-need
//! binding.
//!
//! A [`Shared<T>`] is one pointer (8 bytes) to one allocation:
//!
//! ```text
//!   Block<T, C>  (repr(C), allocated once)
//!   +-------------------------------+
//!   | strong: Cell<usize>           |  \
//!   | vtable: &'static VTable<T>    |   > Header<T>: everything that does
//!   | value:  OnceCell<T>           |  /  not depend on the code type C
//!   +-------------------------------+
//!   | code:   C                     |  the concrete code object, any size
//!   +-------------------------------+
//! ```
//!
//! The pointer addresses the `Header<T>`, whose layout is the same for every
//! `C`, so the strong count and the value are reached without knowing `C`.
//! Operations that need `C` (enter the code, fill it, free the block) go
//! through the hand-written `VTable`, whose functions are instantiated per
//! `C` and cast the pointer back to `Block<T, C>`. This is `Rc<Lazy<T, dyn
//! Code<T>>>` with the trait object's vtable moved from a fat pointer into the
//! allocation, and the unused weak count dropped.
//!
//! All of the `unsafe` in this crate is in this file, in four places: the
//! cast from `Header<T>` back to `Block<T, C>` in the vtable functions, the
//! free of a block, the shared reference to the header, and `take_unique`.

use std::cell::{Cell, OnceCell};
use std::fmt;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// A call-by-need binding that lives on the stack or in a field rather than
/// behind a pointer. [`Shared`] is the heap form the runtime uses.
pub struct Lazy<T, C: ?Sized = dyn Code<T>> {
    value: OnceCell<T>,
    code: C,
}

pub type Deferred<T> = Box<dyn FnOnce() -> Thunk<T>>;

pub trait Code<T> {
    fn enter(&self) -> Option<Thunk<T>>;
    fn fill(&self, code: Deferred<T>) -> bool;
}

/// The code of a binding that is already evaluated: nothing, and no bytes.
pub struct Evaluated;

impl<T> Code<T> for Evaluated {
    fn enter(&self) -> Option<Thunk<T>> {
        None
    }
    fn fill(&self, _: Deferred<T>) -> bool {
        false
    }
}

pub struct Once<F>(Cell<Option<F>>);

impl<T, F: FnOnce() -> Thunk<T>> Code<T> for Once<F> {
    fn enter(&self) -> Option<Thunk<T>> {
        self.0.take().map(|f| f())
    }
    fn fill(&self, _: Deferred<T>) -> bool {
        false
    }
}

pub struct Pending<T>(Cell<Option<Deferred<T>>>);

impl<T> Code<T> for Pending<T> {
    fn enter(&self) -> Option<Thunk<T>> {
        self.0.take().map(|f| f())
    }
    fn fill(&self, code: Deferred<T>) -> bool {
        self.0.replace(Some(code)).is_none()
    }
}

pub enum Thunk<T> {
    Value(T),
    Indirect(Shared<T>),
}

impl<T: 'static> Lazy<T> {
    /// Defer `f` until the value is first demanded.
    pub fn new(f: impl FnOnce() -> T + 'static) -> Lazy<T, impl Code<T> + 'static> {
        Self::step(move || Thunk::Value(f()))
    }

    pub fn step(f: impl FnOnce() -> Thunk<T> + 'static) -> Lazy<T, impl Code<T> + 'static> {
        Lazy {
            value: OnceCell::new(),
            code: Once(Cell::new(Some(f))),
        }
    }

    pub fn pending() -> Lazy<T, impl Code<T> + 'static> {
        Lazy {
            value: OnceCell::new(),
            code: Pending(Cell::new(None)),
        }
    }

    /// An already-evaluated binding; the common case after strictness analysis.
    pub fn ready(value: T) -> Lazy<T, impl Code<T> + 'static> {
        Lazy {
            value: OnceCell::from(value),
            code: Evaluated,
        }
    }
}

impl<T, C: Code<T> + ?Sized> Lazy<T, C> {
    pub fn fill(&self, f: impl FnOnce() -> Thunk<T> + 'static) {
        assert!(
            self.value.get().is_none() && self.code.fill(Box::new(f)),
            "h2r-rt: a recursive binding filled twice"
        );
    }

    /// Whether the binding has already been forced.
    pub fn is_evaluated(&self) -> bool {
        self.value.get().is_some()
    }
}

impl<T: Clone + 'static, C: Code<T> + ?Sized> Lazy<T, C> {
    /// Force to WHNF, memoising the result.
    ///
    /// Panics on re-entrant forcing, which is this runtime's `<<loop>>`.
    pub fn force(&self) -> &T {
        if let Some(v) = self.value.get() {
            return v;
        }
        let entered = self
            .code
            .enter()
            .expect("h2r-rt: re-entrant force (<<loop>>)");
        let value = match entered {
            Thunk::Value(value) => value,
            Thunk::Indirect(next) => chase(next),
        };
        self.value.get_or_init(|| value)
    }
}

impl<T: fmt::Debug, C: ?Sized> fmt::Debug for Lazy<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value.get() {
            Some(v) => write!(f, "Lazy({v:?})"),
            None => write!(f, "Lazy(<thunk>)"),
        }
    }
}

/// Everything in a block that does not depend on its code type, at offset 0.
#[repr(C)]
struct Header<T> {
    strong: Cell<usize>,
    /// Points at a promoted `'static` constant (`Block::VTABLE`); a raw
    /// pointer rather than `&'static` so `T` needs no `'static` bound here.
    vtable: NonNull<VTable<T>>,
    value: OnceCell<T>,
}

/// A header followed by its concrete code. `repr(C)` pins the header at
/// offset 0 and the code after it, which is what makes the casts between
/// `*Header<T>` and `*Block<T, C>` valid.
#[repr(C)]
struct Block<T, C> {
    header: Header<T>,
    code: C,
}

/// The operations that need the concrete code type, instantiated per `C`.
///
/// Each takes the pointer a `Shared<T>` holds. Every function is `unsafe`
/// with one contract: the pointer came from `Shared::alloc::<C>` for the `C`
/// this vtable was built for, and (for `free`) no other `Shared` to the block
/// remains.
struct VTable<T> {
    enter: unsafe fn(NonNull<Header<T>>) -> Option<Thunk<T>>,
    fill: unsafe fn(NonNull<Header<T>>, Deferred<T>) -> bool,
    free: unsafe fn(NonNull<Header<T>>),
}

impl<T: 'static, C: Code<T> + 'static> Block<T, C> {
    const VTABLE: &'static VTable<T> = &VTable {
        enter: Self::enter,
        fill: Self::fill,
        free: Self::free,
    };

    /// # Safety
    /// `header` points to a live `Block<T, C>` (the vtable contract above).
    unsafe fn code<'a>(header: NonNull<Header<T>>) -> &'a C {
        // SAFETY: by the contract the allocation is a `Block<T, C>` and the
        // pointer, derived from that whole allocation, may be used to reach
        // the code field. Only the code field is borrowed, so this does not
        // overlap any `&Header` a caller holds, and `C: Code` mutates only
        // through interior mutability.
        unsafe { &(*header.cast::<Block<T, C>>().as_ptr()).code }
    }

    unsafe fn enter(header: NonNull<Header<T>>) -> Option<Thunk<T>> {
        // SAFETY: the contract of the vtable.
        unsafe { Self::code(header) }.enter()
    }

    unsafe fn fill(header: NonNull<Header<T>>, code: Deferred<T>) -> bool {
        // SAFETY: the contract of the vtable.
        unsafe { Self::code(header) }.fill(code)
    }

    unsafe fn free(header: NonNull<Header<T>>) {
        // SAFETY: the allocation was made by `Box::new(Block<T, C>)`, the
        // count has reached zero so this is the last pointer, and the layout
        // `Box` frees with is exactly the one it allocated with. Dropping the
        // box runs the destructors of the header's value and of the code.
        drop(unsafe { Box::from_raw(header.cast::<Block<T, C>>().as_ptr()) });
    }
}

/// A thunk shared across several owners, for recursive or graph-shaped values.
///
/// Like `Rc`, and for the same reason (`NonNull` plus non-atomic counts), it
/// is neither `Send` nor `Sync`.
pub struct Shared<T> {
    ptr: NonNull<Header<T>>,
    owns: PhantomData<T>,
}

pub fn shared<T: 'static>(f: impl FnOnce() -> T + 'static) -> Shared<T> {
    Shared::new(f)
}

impl<T: 'static> Shared<T> {
    fn alloc<C: Code<T> + 'static>(value: OnceCell<T>, code: C) -> Self {
        let block = Box::new(Block {
            header: Header {
                strong: Cell::new(1),
                vtable: NonNull::from(Block::<T, C>::VTABLE),
                value,
            },
            code,
        });
        Shared {
            // Derived from the whole `Block`, so it may later be cast back.
            ptr: NonNull::from(Box::leak(block)).cast(),
            owns: PhantomData,
        }
    }

    /// Defer `f` until the value is first demanded.
    pub fn new(f: impl FnOnce() -> T + 'static) -> Self {
        Self::step(move || Thunk::Value(f()))
    }

    pub fn step(f: impl FnOnce() -> Thunk<T> + 'static) -> Self {
        Self::alloc(OnceCell::new(), Once(Cell::new(Some(f))))
    }

    /// An empty cell, filled later by [`Shared::fill`] to tie a knot.
    pub fn pending() -> Self {
        Self::alloc(OnceCell::new(), Pending(Cell::new(None)))
    }

    /// An already-evaluated cell; its code is zero bytes.
    pub fn ready(value: T) -> Self {
        Self::alloc(OnceCell::from(value), Evaluated)
    }

    pub fn fill(&self, f: impl FnOnce() -> Thunk<T> + 'static) {
        assert!(
            self.get().is_none() && {
                // SAFETY: `ptr` is a live block made by `alloc` with this vtable.
                unsafe { (self.header().vtable().fill)(self.ptr, Box::new(f)) }
            },
            "h2r-rt: a recursive binding filled twice"
        );
    }
}

impl<T> Header<T> {
    fn vtable(&self) -> &VTable<T> {
        // SAFETY: `alloc` stored a pointer to a `'static` constant, which is
        // never freed or mutated.
        unsafe { self.vtable.as_ref() }
    }
}

impl<T> Shared<T> {
    /// Run the code. `None` means it is running or has run: a `<<loop>>`.
    fn enter(&self) -> Thunk<T> {
        // SAFETY: as in `fill`.
        unsafe { (self.header().vtable().enter)(self.ptr) }
            .expect("h2r-rt: re-entrant force (<<loop>>)")
    }

    fn header(&self) -> &Header<T> {
        // SAFETY: `ptr` addresses a live block while any `Shared` to it
        // exists, and `self` is one. Only the header is borrowed, and the
        // header is mutated only through `Cell`/`OnceCell` or while the count
        // is one (`take_unique`).
        unsafe { self.ptr.as_ref() }
    }

    pub fn get(&self) -> Option<&T> {
        self.header().value.get()
    }

    /// Whether the binding has already been forced.
    pub fn is_evaluated(&self) -> bool {
        self.get().is_some()
    }

    pub fn ptr_eq(a: &Self, b: &Self) -> bool {
        a.ptr == b.ptr
    }

    pub fn strong_count(&self) -> usize {
        self.header().strong.get()
    }

    /// Move the value out if nothing else can see this cell, leaving it empty.
    fn take_unique(&mut self) -> Option<T> {
        if self.strong_count() != 1 {
            return None;
        }
        // SAFETY: the count is one and we hold `&mut self`, so no other
        // `Shared` exists, and a `&T` from `get`/`force` borrows a `Shared`,
        // so none is live. The `&mut` covers only the value field.
        unsafe { (*self.ptr.as_ptr()).value.take() }
    }
}

impl<T: Clone + 'static> Shared<T> {
    /// Force to WHNF, memoising the result.
    ///
    /// Panics on re-entrant forcing, which is this runtime's `<<loop>>`.
    pub fn force(&self) -> &T {
        if let Some(v) = self.get() {
            return v;
        }
        let value = match self.enter() {
            Thunk::Value(value) => value,
            Thunk::Indirect(next) => chase(next),
        };
        self.header().value.get_or_init(|| value)
    }
}

impl<T> Clone for Shared<T> {
    fn clone(&self) -> Self {
        let strong = &self.header().strong;
        let count = strong.get().wrapping_add(1);
        if count == 0 {
            std::process::abort();
        }
        strong.set(count);
        Shared {
            ptr: self.ptr,
            owns: PhantomData,
        }
    }
}

impl<T> Drop for Shared<T> {
    fn drop(&mut self) {
        let header = self.header();
        let count = header.strong.get() - 1;
        header.strong.set(count);
        if count == 0 {
            // `free` deallocates the header, so the function is read first.
            let free = header.vtable().free;
            // SAFETY: the last `Shared` is going away, and the block was made
            // by `alloc` for the code type this vtable is for.
            unsafe { free(self.ptr) }
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Shared<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get() {
            Some(v) => write!(f, "Shared({v:?})"),
            None => write!(f, "Shared(<thunk>)"),
        }
    }
}

/// Follow a chain of indirections to its value, without recursion.
///
/// The value ends up in every cell on the chain that anyone else can still
/// reach; a cell only this chase holds is about to die, so its value is moved
/// out rather than copied, and it is not memoised at all. That keeps the
/// common case, a fresh thunk that evaluated to a fresh node, free of the
/// per-field reference-count traffic a copy costs. (Forwarding the outer cell
/// to the inner one instead was tried and measured: it keeps both cells alive,
/// which cost 17 % of time and 57 % of peak memory on a 1500-line script.)
#[inline(never)]
fn chase<T: Clone + 'static>(first: Shared<T>) -> T {
    let mut pending = Vec::new();
    let mut current = first;
    let value = loop {
        if current.is_evaluated() {
            break match current.take_unique() {
                Some(value) => value,
                None => current.get().expect("checked above").clone(),
            };
        }
        match current.enter() {
            Thunk::Value(value) => {
                if current.strong_count() > 1 {
                    pending.push(current);
                }
                break value;
            }
            Thunk::Indirect(next) => {
                if current.strong_count() > 1 {
                    pending.push(current);
                }
                current = next;
            }
        }
    };
    for cell in pending {
        cell.header().value.get_or_init(|| value.clone());
    }
    value
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    /// Counts its own drops.
    #[derive(Clone)]
    struct Probe(Rc<Cell<u32>>);

    impl Drop for Probe {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    #[test]
    fn a_shared_cell_is_one_thin_pointer() {
        assert_eq!(std::mem::size_of::<Shared<i64>>(), 8);
        assert_eq!(std::mem::size_of::<Shared<[u64; 40]>>(), 8);
        assert_eq!(std::mem::size_of::<Option<Shared<i64>>>(), 8);
    }

    #[test]
    fn an_unforced_cell_drops_its_code_once_with_its_last_owner() {
        let drops = Rc::new(Cell::new(0));
        let captured = Probe(drops.clone());
        let cell = Shared::new(move || {
            let _ = &captured;
            1_i64
        });
        let second = cell.clone();
        assert_eq!(cell.strong_count(), 2);
        drop(cell);
        assert_eq!(drops.get(), 0);
        drop(second);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    fn a_forced_cell_drops_its_value_with_its_last_owner() {
        let drops = Rc::new(Cell::new(0));
        let value = Probe(drops.clone());
        let cell = Shared::new(move || value);
        let other = cell.clone();
        let _ = cell.force();
        assert_eq!(drops.get(), 0);
        drop(cell);
        assert_eq!(drops.get(), 0);
        drop(other);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    fn a_ready_cell_refuses_a_fill() {
        let cell = Shared::ready(5_i64);
        assert!(cell.is_evaluated());
        assert_eq!(*cell.force(), 5);
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            cell.fill(|| Thunk::Value(6));
        }));
        assert!(refused.is_err());
    }

    #[test]
    fn code_larger_and_more_aligned_than_the_header_is_reached_correctly() {
        #[repr(align(64))]
        struct Wide([u8; 100]);
        let wide = Wide([7; 100]);
        let cell = Shared::new(move || i64::from(wide.0[99]) + i64::from(wide.0[0]));
        assert_eq!(*cell.force(), 14);
        let wide = Wide([3; 100]);
        let unforced = Shared::new(move || i64::from(wide.0[50]));
        assert_eq!(*unforced.clone().force(), 3);
        assert_eq!(*unforced.force(), 3);
    }

    #[test]
    fn a_pending_cell_is_filled_once_and_forced_through_the_fill() {
        let cell: Shared<i64> = Shared::pending();
        let alias = cell.clone();
        cell.fill(|| Thunk::Value(9));
        assert!(!alias.is_evaluated());
        assert_eq!(*alias.force(), 9);
        assert!(Shared::ptr_eq(&cell, &alias));
    }
}
