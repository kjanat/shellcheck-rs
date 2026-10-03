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
//!   | value:  Slot<T>               |  /  not depend on the code type C
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
//! All of the `unsafe` for cells is in this file, in six places: the
//! cast from `Header<T>` back to `Block<T, C>` in the vtable functions, the
//! allocation of a block (written field by field), the free of a block, the
//! shared reference to the header, `take_unique`, and the value `Slot` (the
//! one place that writes the memoised value). `Fields::drop` in `lib.rs` is
//! the one other, and does not touch a cell.

use std::cell::{Cell, OnceCell, UnsafeCell};
use std::fmt;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

use super::{Field, Step};

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

    /// Call the code as a function body. The tail of a closure cell holds its
    /// captures and function pointers, and the closure's value says how to use
    /// them. Only such tails override this; the cell that holds one is created
    /// already evaluated, so `enter` is never reached for it.
    fn call(&self, _arguments: Vec<Field>) -> Field {
        unreachable!("h2r-rt: this cell's code is not a function body")
    }

    /// As [`Code::call`], for the entry that continues as a tail call.
    fn call_enter(&self, _arguments: Vec<Field>) -> Step<i64> {
        unreachable!("h2r-rt: this cell's code has no entry")
    }

    /// Whether the value of an evaluated cell with this code is not a plain
    /// value: it refers to the cell itself (a closure's value says "my code is
    /// my tail"), so it cannot be moved or cloned into another cell. Such a
    /// cell's value is given to others by [`Code::share`] instead.
    fn shares() -> bool
    where
        Self: Sized,
    {
        false
    }

    /// The value another cell gets when it evaluates to this one (see
    /// `chase`). Called only when `shares()`; `cell` is the cell holding `self`.
    fn share(&self, _cell: &Shared<T>) -> T {
        unreachable!("h2r-rt: this cell's code does not share by reference")
    }

    /// Census only: 1 if this is `Once` code not yet run, 2 if it is `Pending`
    /// code that was filled and not yet run, else 0.
    #[cfg(feature = "stats")]
    fn holds_code(&self) -> u8 {
        0
    }
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
    #[cfg(feature = "stats")]
    fn holds_code(&self) -> u8 {
        let code = self.0.take();
        let held = code.is_some();
        self.0.set(code);
        u8::from(held)
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
    #[cfg(feature = "stats")]
    fn holds_code(&self) -> u8 {
        let code = self.0.take();
        let held = code.is_some();
        self.0.set(code);
        2 * u8::from(held)
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
    value: Slot<T>,
    /// Census only (`stats`): the emitter site that made this thunk
    /// (`stats::NO_SITE` for any other cell). Last, so that the fields above
    /// keep their offsets; it costs one word per cell with the feature on and
    /// nothing with it off.
    #[cfg(feature = "stats")]
    site: Cell<u32>,
}

/// The memoised value of a cell: a `OnceCell<T>` with the one operation the
/// force path needs, [`Slot::settle`], which looks at the state once.
/// (`OnceCell::get_or_init` checks, calls an out-of-line cold function, and
/// checks again before it stores.) Same layout as `OnceCell<T>`.
struct Slot<T>(UnsafeCell<Option<T>>);

impl<T> Slot<T> {
    #[inline(always)]
    fn get(&self) -> Option<&T> {
        // SAFETY: the option is written only by `settle` (while it is `None`,
        // so no reference into it exists) and by `take` (which needs `&mut`);
        // a shared reference to its contents is therefore never invalidated
        // while the slot is borrowed.
        unsafe { (*self.0.get()).as_ref() }
    }

    /// Store `value` unless the slot is already filled (the first value wins,
    /// as in `OnceCell::get_or_init`), and return what the slot holds.
    #[inline(always)]
    fn settle(&self, value: T) -> &T {
        let slot = self.0.get();
        // SAFETY: `slot` is valid. If it is `Some` we only read it. If it is
        // `None`, nothing borrows from it (`get` hands out references only
        // to a `Some`), so writing the value in place is unobserved.
        unsafe {
            if (*slot).is_none() {
                slot.write(Some(value));
            }
            (*slot).as_ref().unwrap_unchecked()
        }
    }

    fn take(&mut self) -> Option<T> {
        self.0.get_mut().take()
    }
}

/// A header followed by its concrete code. `repr(C)` pins the header at
/// offset 0 and the code after it, which is what makes the casts between
/// `*Header<T>` and `*Block<T, C>` valid.
#[repr(C)]
struct Block<T, C> {
    header: Header<T>,
    code: C,
}

/// What entering a cell's code produced. A value is not carried in this enum
/// (a `Thunk<Node>` is 64 bytes and every hop would copy it): the vtable
/// function writes it through the pointer the caller passed.
enum Entered<T> {
    /// The code is running or has run: a `<<loop>>`.
    Looping,
    /// The value was written to the `out` slot.
    Value,
    Indirect(Shared<T>),
}

/// The vtable function behind [`Code::share`].
type Share<T> = unsafe fn(NonNull<Header<T>>) -> T;

/// The operations that need the concrete code type, instantiated per `C`.
///
/// Each takes the pointer a `Shared<T>` holds. Every function is `unsafe`
/// with one contract: the pointer came from `Shared::alloc::<C>` for the `C`
/// this vtable was built for, and (for `free`) no other `Shared` to the block
/// remains.
struct VTable<T> {
    enter: unsafe fn(NonNull<Header<T>>, *mut T) -> Entered<T>,
    fill: unsafe fn(NonNull<Header<T>>, Deferred<T>) -> bool,
    call: unsafe fn(NonNull<Header<T>>, Vec<Field>) -> Field,
    call_enter: unsafe fn(NonNull<Header<T>>, Vec<Field>) -> Step<i64>,
    /// Present only for code with `Code::shares`.
    share: Option<Share<T>>,
    free: unsafe fn(NonNull<Header<T>>),
}

impl<T: 'static, C: Code<T> + 'static> Block<T, C> {
    const fn table(share: Option<Share<T>>) -> VTable<T> {
        VTable {
            enter: Self::enter,
            fill: Self::fill,
            call: Self::call,
            call_enter: Self::call_enter,
            share,
            free: Self::free,
        }
    }

    const VTABLE: &'static VTable<T> = &Self::table(None);
    const SHARING: &'static VTable<T> = &Self::table(Some(Self::share));

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

    /// # Safety
    /// The vtable contract, and `out` is valid for writing a `T`.
    unsafe fn enter(header: NonNull<Header<T>>, out: *mut T) -> Entered<T> {
        // SAFETY: the contract of the vtable.
        match unsafe { Self::code(header) }.enter() {
            None => Entered::Looping,
            Some(Thunk::Value(value)) => {
                // SAFETY: `out` is valid for writes, by the contract.
                unsafe { out.write(value) };
                Entered::Value
            }
            Some(Thunk::Indirect(next)) => Entered::Indirect(next),
        }
    }

    unsafe fn fill(header: NonNull<Header<T>>, code: Deferred<T>) -> bool {
        // SAFETY: the contract of the vtable.
        unsafe { Self::code(header) }.fill(code)
    }

    unsafe fn call(header: NonNull<Header<T>>, arguments: Vec<Field>) -> Field {
        // SAFETY: the contract of the vtable.
        unsafe { Self::code(header) }.call(arguments)
    }

    unsafe fn call_enter(header: NonNull<Header<T>>, arguments: Vec<Field>) -> Step<i64> {
        // SAFETY: the contract of the vtable.
        unsafe { Self::code(header) }.call_enter(arguments)
    }

    unsafe fn share(header: NonNull<Header<T>>) -> T {
        // A borrowed handle: it must not decrement the count when it goes.
        let cell = std::mem::ManuallyDrop::new(Shared {
            ptr: header,
            owns: PhantomData,
        });
        // SAFETY: the contract of the vtable.
        unsafe { Self::code(header) }.share(&cell)
    }

    unsafe fn free(header: NonNull<Header<T>>) {
        let block = header.cast::<Block<T, C>>().as_ptr();
        // SAFETY: the contract of the vtable: the block is live until the
        // `dealloc` below, and `holds_code` only reads the code.
        #[cfg(feature = "stats")]
        match unsafe { Self::code(header) }.holds_code() {
            1 => {
                super::stats::bump_kind::<T>(super::stats::DROPPED_UNFORCED);
                // SAFETY: as above, the header is live until the `dealloc`.
                let site = unsafe { header.as_ref() }.site.get();
                super::stats::bump_site(site, super::stats::SITE_UNFORCED);
            }
            2 => super::stats::bump_kind::<T>(super::stats::DROPPED_PENDING),
            _ => {}
        }
        // SAFETY: the allocation was made by `alloc_block` with the layout of
        // a `Block<T, C>`, the count has reached zero so this is the last
        // pointer, and the layout given back is that same one. Each field is
        // dropped once, in place, before the memory goes. The value is tested
        // here, in line, because most cells that die never memoised one (a
        // thunk that `chase` moved through) and the drop glue of `Option<T>`
        // is an out-of-line call even for `None`.
        unsafe {
            if let Some(value) = (*block).header.value.0.get_mut() {
                std::ptr::drop_in_place(value);
            }
            std::ptr::drop_in_place(&raw mut (*block).code);
            std::alloc::dealloc(block.cast(), std::alloc::Layout::new::<Block<T, C>>());
        }
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
    /// Allocate a block and write everything but the value slot, which the
    /// caller must write (see `alloc` and `alloc_empty`) before the block is
    /// used.
    ///
    /// The fields are written one by one rather than as a `Block` value, which
    /// the optimiser sometimes assembles on the stack and copies.
    #[inline(always)]
    fn alloc_block<C: Code<T> + 'static>(code: C) -> NonNull<Block<T, C>> {
        let layout = std::alloc::Layout::new::<Block<T, C>>();
        // SAFETY: the layout has a non-zero size (the header is not empty).
        let block = unsafe { std::alloc::alloc(layout) }.cast::<Block<T, C>>();
        let Some(block) = NonNull::new(block) else {
            std::alloc::handle_alloc_error(layout)
        };
        let vtable = if C::shares() {
            Block::<T, C>::SHARING
        } else {
            Block::<T, C>::VTABLE
        };
        // SAFETY: `block` is a fresh allocation of the layout of a
        // `Block<T, C>`, so it is valid and aligned for these writes, each
        // field is written once, and nothing else refers to it. `free` gives
        // the same layout back.
        unsafe {
            let block = block.as_ptr();
            (&raw mut (*block).header.strong).write(Cell::new(1));
            (&raw mut (*block).header.vtable).write(NonNull::from(vtable));
            #[cfg(feature = "stats")]
            (&raw mut (*block).header.site).write(Cell::new(super::stats::NO_SITE));
            (&raw mut (*block).code).write(code);
        }
        block
    }

    /// The handle for a block whose every field has been written.
    ///
    /// # Safety
    /// All of `block`'s fields are initialised, including the value slot.
    #[inline(always)]
    unsafe fn handle<C>(block: NonNull<Block<T, C>>) -> Self {
        Shared {
            // Derived from the whole allocation, so it may later be cast back.
            ptr: block.cast(),
            owns: PhantomData,
        }
    }

    /// A cell holding `value`.
    #[inline(always)]
    fn alloc<C: Code<T> + 'static>(value: T, code: C) -> Self {
        let block = Self::alloc_block(code);
        // SAFETY: the slot is the one field `alloc_block` left unwritten.
        unsafe {
            (&raw mut (*block.as_ptr()).header.value).write(Slot(UnsafeCell::new(Some(value))));
            Self::handle(block)
        }
    }

    /// A cell with no value yet.
    #[inline(always)]
    fn alloc_empty<C: Code<T> + 'static>(code: C) -> Self {
        let block = Self::alloc_block(code);
        // SAFETY: the slot is the one field `alloc_block` left unwritten.
        unsafe {
            (&raw mut (*block.as_ptr()).header.value).write(Slot(UnsafeCell::new(None)));
            Self::handle(block)
        }
    }

    /// Defer `f` until the value is first demanded.
    pub fn new(f: impl FnOnce() -> T + 'static) -> Self {
        Self::step(move || Thunk::Value(f()))
    }

    pub fn step(f: impl FnOnce() -> Thunk<T> + 'static) -> Self {
        let cell = Self::alloc_empty(Once(Cell::new(Some(f))));
        #[cfg(feature = "stats")]
        {
            super::stats::bump_kind::<T>(super::stats::CREATED);
            let site = super::stats::take_site();
            cell.header().site.set(site);
            super::stats::bump_site(site, super::stats::SITE_CREATED);
        }
        cell
    }

    /// An empty cell, filled later by [`Shared::fill`] to tie a knot.
    pub fn pending() -> Self {
        #[cfg(feature = "stats")]
        super::stats::bump_kind::<T>(super::stats::PENDING);
        Self::alloc_empty(Pending(Cell::new(None)))
    }

    /// An already-evaluated cell; its code is zero bytes.
    pub fn ready(value: T) -> Self {
        #[cfg(feature = "stats")]
        super::stats::bump_kind::<T>(super::stats::EVALUATED);
        Self::alloc(value, Evaluated)
    }

    /// An already-evaluated cell whose code tail is `code`, kept for
    /// [`Shared::call`]. The value says how to use the tail; the cell is never
    /// entered, so `code.enter` is unreachable.
    pub fn ready_with<C: Code<T> + 'static>(value: T, code: C) -> Self {
        #[cfg(feature = "stats")]
        super::stats::bump_kind::<T>(super::stats::EVALUATED);
        Self::alloc(value, code)
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
    /// Run the code. A value comes back in `out`, initialised exactly when
    /// the result is [`Entered::Value`]. Panics on a `<<loop>>`.
    #[inline(always)]
    fn enter(&self, out: &mut MaybeUninit<T>) -> Entered<T> {
        // SAFETY: as in `fill`; `out` is valid for writing a `T`.
        match unsafe { (self.header().vtable().enter)(self.ptr, out.as_mut_ptr()) } {
            Entered::Looping => panic!("h2r-rt: re-entrant force (<<loop>>)"),
            entered => entered,
        }
    }

    /// Call this cell's code tail as a function body (see [`Code::call`]).
    pub fn call(&self, arguments: Vec<Field>) -> Field {
        // SAFETY: as in `fill`.
        unsafe { (self.header().vtable().call)(self.ptr, arguments) }
    }

    /// Call this cell's code tail as a function entry (see [`Code::call_enter`]).
    pub fn call_enter(&self, arguments: Vec<Field>) -> Step<i64> {
        // SAFETY: as in `fill`.
        unsafe { (self.header().vtable().call_enter)(self.ptr, arguments) }
    }

    /// For code with `Code::shares`, the value to give another cell that
    /// evaluates to this one; `None` for every other cell.
    fn share(&self) -> Option<T> {
        let share = self.header().vtable().share?;
        // SAFETY: as in `fill`; the vtable has `share` only for code that
        // asked for it.
        Some(unsafe { share(self.ptr) })
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
    #[inline]
    pub fn force(&self) -> &T {
        match self.get() {
            Some(v) => v,
            None => self.force_slow(),
        }
    }

    /// Run the code of a cell that has no value yet and memoise the result.
    #[inline(never)]
    fn force_slow(&self) -> &T {
        #[cfg(feature = "stats")]
        {
            let shared = self.strong_count() > 1;
            super::stats::bump_kind::<T>(if shared {
                super::stats::FORCED_SHARED
            } else {
                super::stats::FORCED_UNIQUE
            });
            super::stats::bump_site(
                self.header().site.get(),
                if shared {
                    super::stats::SITE_FORCED_SHARED
                } else {
                    super::stats::SITE_FORCED_UNIQUE
                },
            );
        }
        let mut out = MaybeUninit::uninit();
        let value = match self.enter(&mut out) {
            // SAFETY: `Value` means the code wrote `out`.
            Entered::Value => unsafe { out.assume_init() },
            // The common indirection is a fresh, already-evaluated cell (a
            // thunk whose body ended in a constructor): take its value here,
            // and keep the loop for chains.
            Entered::Indirect(next) if next.is_evaluated() => take_evaluated(next),
            Entered::Indirect(next) => chase(next),
            Entered::Looping => unreachable!("`enter` panics instead"),
        };
        self.header().value.settle(value)
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

/// The value of an evaluated cell: moved out if nothing else holds the cell,
/// handed over by reference for a closure's cell, copied otherwise.
#[inline(always)]
fn value_of_evaluated<T: Clone + 'static>(cell: &mut Shared<T>) -> T {
    match cell.share() {
        Some(value) => value,
        None => match cell.take_unique() {
            Some(value) => {
                #[cfg(feature = "stats")]
                super::stats::bump_kind::<T>(super::stats::MOVED_UNIQUE);
                value
            }
            None => {
                #[cfg(feature = "stats")]
                super::stats::bump_kind::<T>(super::stats::COPIED);
                cell.get().expect("evaluated").clone()
            }
        },
    }
}

/// [`value_of_evaluated`] for a handle that is not used again.
#[inline(always)]
fn take_evaluated<T: Clone + 'static>(mut cell: Shared<T>) -> T {
    value_of_evaluated(&mut cell)
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
            // `current` is dropped after the memoising loop below, as before.
            break value_of_evaluated(&mut current);
        }
        let mut out = MaybeUninit::uninit();
        #[cfg(feature = "stats")]
        {
            let shared = current.strong_count() > 1;
            super::stats::bump_kind::<T>(if shared {
                super::stats::CHASED_SHARED
            } else {
                super::stats::CHASED_UNIQUE
            });
            super::stats::bump_site(
                current.header().site.get(),
                if shared {
                    super::stats::SITE_CHASED_SHARED
                } else {
                    super::stats::SITE_CHASED_UNIQUE
                },
            );
        }
        match current.enter(&mut out) {
            Entered::Value => {
                if current.strong_count() > 1 {
                    pending.push(current);
                }
                // SAFETY: `Value` means the code wrote `out`.
                break unsafe { out.assume_init() };
            }
            Entered::Indirect(next) => {
                if current.strong_count() > 1 {
                    pending.push(current);
                }
                current = next;
            }
            Entered::Looping => unreachable!("`enter` panics instead"),
        }
    };
    if !pending.is_empty() {
        for cell in pending {
            cell.header().value.settle(value.clone());
        }
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

    /// The census header (`stats`) is one word larger and nothing else about
    /// it moves; without the feature the header is exactly what the pins in
    /// `PERF.md` say (a `:` cell is 72 bytes: 16 + the 56-byte `Node`).
    #[test]
    fn the_site_in_the_header_exists_only_with_the_census() {
        let plain = 2 * std::mem::size_of::<usize>() + std::mem::size_of::<Option<i64>>();
        assert_eq!(plain, 32);
        let expected = if cfg!(feature = "stats") {
            plain + std::mem::size_of::<usize>()
        } else {
            plain
        };
        assert_eq!(std::mem::size_of::<Header<i64>>(), expected);
        assert_eq!(std::mem::size_of::<Block<i64, Evaluated>>(), expected);
    }
}
