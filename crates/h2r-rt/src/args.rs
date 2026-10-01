//! Argument vectors for calls through a closure.
//!
//! Almost every call has one to three arguments, so [`Args`] keeps up to
//! [`INLINE`] of them inside the value itself (`Field` is 16 bytes, so 64 bytes
//! of buffer) and moves to a heap `Vec<Field>` only when a fifth is added. A
//! call through a closure therefore allocates nothing for its arguments.
//!
//! ```text
//!   Args = enum
//!     Inline { len: 0..=4, buf: [MaybeUninit<Field>; 4] }   buf[..len] is initialised
//!     Heap(Vec<Field>)                                    any length
//! ```
//!
//! The `unsafe` here is the inline buffer, and only that. The invariant is
//! one sentence: in `Inline`, exactly the slots `buf[..len]` hold a live
//! `Field` and the others are never read. `Inline`'s `Drop` drops those slots
//! and no others; every operation that moves a slot out lowers `len` (or
//! hands the slot to a new owner) before anything can panic.

use std::fmt;
use std::mem::MaybeUninit;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::slice::SliceIndex;

use super::Field;

/// How many arguments are kept without a heap allocation.
pub const INLINE: usize = 4;

/// The number of initialised inline slots. An enum rather than a `u8` so that
/// `Repr` can tell its variants apart by the unused values of this byte
/// instead of a tag of its own: that keeps `Args` at 72 bytes, not 80.
#[derive(Clone, Copy)]
#[repr(u8)]
enum Len {
    L0,
    L1,
    L2,
    L3,
    L4,
}

impl Len {
    const fn of(n: usize) -> Len {
        match n {
            0 => Len::L0,
            1 => Len::L1,
            2 => Len::L2,
            3 => Len::L3,
            4 => Len::L4,
            _ => panic!("h2r-rt: inline argument length out of range"),
        }
    }
}

struct Inline {
    /// `buf[..len]` is initialised, the rest is not. At most `INLINE`.
    len: Len,
    buf: [MaybeUninit<Field>; INLINE],
}

impl Inline {
    const fn new() -> Self {
        Inline {
            len: Len::L0,
            buf: [const { MaybeUninit::uninit() }; INLINE],
        }
    }

    fn len(&self) -> usize {
        self.len as usize
    }

    fn as_slice(&self) -> &[Field] {
        // SAFETY: `buf[..len]` is initialised (the type's invariant), and
        // `MaybeUninit<Field>` has the layout of `Field`.
        unsafe { std::slice::from_raw_parts(self.buf.as_ptr().cast::<Field>(), self.len()) }
    }

    fn as_mut_slice(&mut self) -> &mut [Field] {
        // SAFETY: as in `as_slice`; the borrow is unique.
        unsafe { std::slice::from_raw_parts_mut(self.buf.as_mut_ptr().cast::<Field>(), self.len()) }
    }

    /// Append; the caller has checked that there is room.
    fn push(&mut self, field: Field) {
        let at = self.len();
        assert!(at < INLINE, "h2r-rt: inline argument buffer overflow");
        self.buf[at] = MaybeUninit::new(field);
        self.len = Len::of(at + 1);
    }

    /// Remove and return the first element, shifting the rest down.
    fn pop_front(&mut self) -> Option<Field> {
        let len = self.len();
        if len == 0 {
            return None;
        }
        // Lower `len` first: the slots in `1..len` are moved below, the slot
        // at `0` is read out, and nothing between here and the end can panic.
        self.len = Len::L0;
        let base = self.buf.as_mut_ptr();
        // SAFETY: slot 0 was initialised (`len >= 1`) and is read exactly once;
        // slots `1..len` are initialised and are moved to `0..len - 1`, after
        // which slot `len - 1` is logically uninitialised and outside the new
        // `len`. `ptr::copy` handles the overlap.
        let first = unsafe {
            let first = base.cast::<Field>().read();
            std::ptr::copy(base.add(1), base, len - 1);
            first
        };
        self.len = Len::of(len - 1);
        Some(first)
    }

    /// Move the first `n` elements out into a new buffer, closing the gap.
    fn take_front(&mut self, n: usize) -> Inline {
        let len = self.len();
        assert!(n <= len, "h2r-rt: taking more arguments than there are");
        let mut front = Inline::new();
        // Lower `len` first so a panic (there is none) could only leak.
        self.len = Len::L0;
        let base = self.buf.as_mut_ptr();
        // SAFETY: slots `0..n` are initialised and move to `front`, which
        // takes ownership of them (its `len` is raised to match); slots
        // `n..len` are initialised and move down to `0..len - n`. The source
        // and the destination buffers are distinct, and `ptr::copy` handles
        // the overlap within `self`.
        unsafe {
            std::ptr::copy_nonoverlapping(base, front.buf.as_mut_ptr(), n);
            std::ptr::copy(base.add(n), base, len - n);
        }
        front.len = Len::of(n);
        self.len = Len::of(len - n);
        front
    }
}

impl Drop for Inline {
    fn drop(&mut self) {
        // SAFETY: exactly `buf[..len]` is initialised, and `drop_in_place`
        // runs each element's destructor once. `len` is left as it is, but
        // the value is being destroyed and cannot be observed again.
        unsafe { std::ptr::drop_in_place(self.as_mut_slice()) }
    }
}

enum Repr {
    Inline(Inline),
    Heap(Vec<Field>),
}

/// A small vector of call arguments: up to four inline, a `Vec` beyond that.
pub struct Args(Repr);

impl Args {
    pub const fn new() -> Self {
        Args(Repr::Inline(Inline::new()))
    }

    /// Room for `capacity` arguments: inline if they fit, otherwise one heap
    /// allocation of exactly that size.
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= INLINE {
            Self::new()
        } else {
            Args(Repr::Heap(Vec::with_capacity(capacity)))
        }
    }

    pub fn len(&self) -> usize {
        match &self.0 {
            Repr::Inline(inline) => inline.len(),
            Repr::Heap(vec) => vec.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether the arguments live on the heap rather than inline.
    pub fn spilled(&self) -> bool {
        matches!(self.0, Repr::Heap(_))
    }

    pub fn as_slice(&self) -> &[Field] {
        match &self.0 {
            Repr::Inline(inline) => inline.as_slice(),
            Repr::Heap(vec) => vec,
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [Field] {
        match &mut self.0 {
            Repr::Inline(inline) => inline.as_mut_slice(),
            Repr::Heap(vec) => vec,
        }
    }

    pub fn push(&mut self, field: Field) {
        match &mut self.0 {
            Repr::Inline(inline) if inline.len() < INLINE => inline.push(field),
            Repr::Inline(_) => {
                // The fifth argument: move to the heap. `take` leaves `self`
                // empty and valid while the old buffer is emptied into the Vec.
                let old = std::mem::take(self);
                let mut vec = Vec::with_capacity(2 * INLINE);
                vec.extend(old);
                vec.push(field);
                self.0 = Repr::Heap(vec);
            }
            Repr::Heap(vec) => vec.push(field),
        }
    }

    /// Append clones of `fields`.
    pub fn extend_from_slice(&mut self, fields: &[Field]) {
        self.reserve(fields.len());
        for field in fields {
            self.push(field.clone());
        }
    }

    /// Make room for `additional` more arguments with at most one allocation.
    fn reserve(&mut self, additional: usize) {
        let wanted = self.len() + additional;
        if wanted <= INLINE {
            return;
        }
        match &mut self.0 {
            Repr::Inline(_) => {
                let old = std::mem::take(self);
                let mut vec = Vec::with_capacity(wanted);
                vec.extend(old);
                self.0 = Repr::Heap(vec);
            }
            Repr::Heap(vec) => vec.reserve(additional),
        }
    }

    /// Take the first `n` arguments out as their own `Args` and keep the rest,
    /// in order, in `self`. Panics if there are fewer than `n`.
    pub fn take_front(&mut self, n: usize) -> Args {
        assert!(
            n <= self.len(),
            "h2r-rt: taking more arguments than there are"
        );
        match &mut self.0 {
            Repr::Inline(inline) => Args(Repr::Inline(inline.take_front(n))),
            Repr::Heap(vec) => {
                if n <= INLINE {
                    // The taken prefix is inline; the rest keeps its `Vec`.
                    let mut front = Inline::new();
                    for field in vec.drain(..n) {
                        front.push(field);
                    }
                    Args(Repr::Inline(front))
                } else {
                    Args(Repr::Heap(vec.drain(..n).collect()))
                }
            }
        }
    }

    pub fn into_vec(self) -> Vec<Field> {
        match self.0 {
            Repr::Heap(vec) => vec,
            Repr::Inline(_) => {
                let mut vec = Vec::with_capacity(self.len());
                vec.extend(self);
                vec
            }
        }
    }

    /// The arguments as an exactly-sized slice on the heap.
    pub fn into_boxed_slice(self) -> Box<[Field]> {
        self.into_vec().into_boxed_slice()
    }
}

impl Default for Args {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Args {
    type Target = [Field];
    fn deref(&self) -> &[Field] {
        self.as_slice()
    }
}

impl DerefMut for Args {
    fn deref_mut(&mut self) -> &mut [Field] {
        self.as_mut_slice()
    }
}

impl<I: SliceIndex<[Field]>> Index<I> for Args {
    type Output = I::Output;
    fn index(&self, index: I) -> &I::Output {
        &self.as_slice()[index]
    }
}

impl<I: SliceIndex<[Field]>> IndexMut<I> for Args {
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        &mut self.as_mut_slice()[index]
    }
}

impl Clone for Args {
    fn clone(&self) -> Self {
        let mut copy = Args::with_capacity(self.len());
        copy.extend_from_slice(self);
        copy
    }
}

impl fmt::Debug for Args {
    // `Field` has no `Debug` (its payloads are runtime cells), so this shows
    // the shape of the vector.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Args")
            .field("len", &self.len())
            .field("spilled", &self.spilled())
            .finish()
    }
}

impl<const N: usize> From<[Field; N]> for Args {
    fn from(fields: [Field; N]) -> Self {
        if N <= INLINE {
            let mut args = Args::new();
            for field in fields {
                args.push(field);
            }
            args
        } else {
            Args(Repr::Heap(Vec::from(fields)))
        }
    }
}

impl From<Vec<Field>> for Args {
    /// Keeps the vector (and its allocation) as it is.
    fn from(vec: Vec<Field>) -> Self {
        Args(Repr::Heap(vec))
    }
}

impl From<Args> for Vec<Field> {
    fn from(args: Args) -> Self {
        args.into_vec()
    }
}

impl FromIterator<Field> for Args {
    fn from_iter<I: IntoIterator<Item = Field>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut args = Args::with_capacity(iter.size_hint().0);
        args.extend(iter);
        args
    }
}

impl Extend<Field> for Args {
    fn extend<I: IntoIterator<Item = Field>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        self.reserve(iter.size_hint().0);
        for field in iter {
            self.push(field);
        }
    }
}

/// By-value iterator over the arguments, in order.
pub struct IntoIter(IterRepr);

enum IterRepr {
    Inline(Inline),
    Heap(std::vec::IntoIter<Field>),
}

impl Iterator for IntoIter {
    type Item = Field;

    fn next(&mut self) -> Option<Field> {
        match &mut self.0 {
            IterRepr::Inline(inline) => inline.pop_front(),
            IterRepr::Heap(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let left = match &self.0 {
            IterRepr::Inline(inline) => inline.len(),
            IterRepr::Heap(iter) => iter.len(),
        };
        (left, Some(left))
    }
}

impl ExactSizeIterator for IntoIter {}

impl IntoIterator for Args {
    type Item = Field;
    type IntoIter = IntoIter;

    fn into_iter(self) -> IntoIter {
        IntoIter(match self.0 {
            Repr::Inline(inline) => IterRepr::Inline(inline),
            Repr::Heap(vec) => IterRepr::Heap(vec.into_iter()),
        })
    }
}

impl<'a> IntoIterator for &'a Args {
    type Item = &'a Field;
    type IntoIter = std::slice::Iter<'a, Field>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

#[cfg(test)]
mod tests {
    use super::super::Int;
    use super::*;
    use std::cell::Cell;
    use std::rc::Rc;

    /// A field whose destruction is observable: it owns a clone of `witness`,
    /// so `Rc::strong_count(&witness)` falls by one when the field is dropped.
    fn probe(witness: &Rc<Cell<u8>>) -> Field {
        let held = Rc::clone(witness);
        Field::Int(Int::defer(move || {
            held.set(held.get() + 1);
            0
        }))
    }

    fn ints(values: &[i64]) -> Args {
        values.iter().map(|&v| Field::Int64(v)).collect()
    }

    fn contents(args: &Args) -> Vec<i64> {
        args.iter().map(Field::int64).collect()
    }

    #[test]
    fn four_fields_and_a_length_are_the_size() {
        // 4 x 16 bytes of buffer plus a byte of length that doubles as the variant tag;
        // pinned so a change is deliberate.
        assert_eq!(std::mem::size_of::<Field>(), 16);
        assert!(
            std::mem::size_of::<Args>() <= 72,
            "{}",
            std::mem::size_of::<Args>()
        );
    }

    #[test]
    fn up_to_four_arguments_stay_inline() {
        let mut args = Args::new();
        assert!(args.is_empty());
        for n in 0..4 {
            args.push(Field::Int64(n));
            assert!(!args.spilled());
            assert_eq!(args.len(), n as usize + 1);
        }
        assert_eq!(contents(&args), [0, 1, 2, 3]);
        assert_eq!(args[2].int64(), 2);
        assert!(!Args::from([Field::Int64(1), Field::Int64(2)]).spilled());
        assert!(!Args::from([] as [Field; 0]).spilled());
    }

    #[test]
    fn the_fifth_argument_spills_and_keeps_order() {
        let mut args = ints(&[1, 2, 3, 4]);
        assert!(!args.spilled());
        args.push(Field::Int64(5));
        assert!(args.spilled());
        args.push(Field::Int64(6));
        assert_eq!(contents(&args), [1, 2, 3, 4, 5, 6]);
        assert_eq!(args.len(), 6);
        assert_eq!(args[5].int64(), 6);
        assert!(
            Args::from(std::array::from_fn::<Field, 5, _>(|n| Field::Int64(
                n as i64
            )))
            .spilled()
        );
        assert!(!ints(&[1, 2, 3, 4]).spilled());
        assert!(ints(&[1, 2, 3, 4, 5]).spilled());
    }

    #[test]
    fn take_front_keeps_the_rest_in_order() {
        let mut args = ints(&[1, 2, 3]);
        let front = args.take_front(2);
        assert_eq!(contents(&front), [1, 2]);
        assert_eq!(contents(&args), [3]);
        let all = args.take_front(1);
        assert_eq!(contents(&all), [3]);
        assert!(args.is_empty());
        assert!(args.take_front(0).is_empty());

        // A spilled vector gives up an inline prefix and keeps its `Vec`.
        let mut args = ints(&[1, 2, 3, 4, 5, 6]);
        let front = args.take_front(3);
        assert!(!front.spilled());
        assert_eq!(contents(&front), [1, 2, 3]);
        assert_eq!(contents(&args), [4, 5, 6]);
        // ... or a spilled one.
        let mut args = ints(&[1, 2, 3, 4, 5, 6, 7]);
        let front = args.take_front(5);
        assert!(front.spilled());
        assert_eq!(contents(&front), [1, 2, 3, 4, 5]);
        assert_eq!(contents(&args), [6, 7]);
    }

    #[test]
    #[should_panic(expected = "taking more arguments")]
    fn take_front_of_more_than_there_are_panics() {
        ints(&[1]).take_front(2);
    }

    #[test]
    fn extend_takes_an_iterator_or_another_args() {
        let mut args = ints(&[1]);
        args.extend(ints(&[2, 3]));
        assert!(!args.spilled());
        args.extend([Field::Int64(4), Field::Int64(5)]);
        assert!(args.spilled());
        args.extend_from_slice(&[Field::Int64(6)]);
        assert_eq!(contents(&args), [1, 2, 3, 4, 5, 6]);
        let mut spilled = ints(&[1, 2, 3, 4, 5]);
        spilled.extend(ints(&[6]));
        assert_eq!(contents(&spilled), [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn iteration_is_by_value_and_by_reference() {
        for values in [
            &[][..],
            &[7][..],
            &[1, 2, 3, 4][..],
            &[1, 2, 3, 4, 5, 6][..],
        ] {
            let args = ints(values);
            assert_eq!((&args).into_iter().count(), values.len());
            let mut iter = args.into_iter();
            assert_eq!(iter.len(), values.len());
            let mut seen = Vec::new();
            while let Some(field) = iter.next() {
                seen.push(field.int64());
                assert_eq!(iter.len(), values.len() - seen.len());
            }
            assert_eq!(seen, values);
        }
    }

    #[test]
    fn clone_is_independent_and_debug_shows_the_shape() {
        let args = ints(&[1, 2, 3]);
        let mut copy = args.clone();
        copy.push(Field::Int64(4));
        assert_eq!(contents(&args), [1, 2, 3]);
        assert_eq!(contents(&copy), [1, 2, 3, 4]);
        let big = ints(&[1, 2, 3, 4, 5]);
        assert_eq!(contents(&big.clone()), [1, 2, 3, 4, 5]);
        assert_eq!(format!("{args:?}"), "Args { len: 3, spilled: false }");
        assert_eq!(format!("{big:?}"), "Args { len: 5, spilled: true }");
    }

    #[test]
    fn conversions_to_and_from_vec() {
        let args = Args::from(vec![Field::Int64(1), Field::Int64(2)]);
        assert_eq!(contents(&args), [1, 2]);
        let vec: Vec<Field> = ints(&[3, 4]).into();
        assert_eq!(vec.len(), 2);
        let boxed = ints(&[5, 6, 7, 8, 9]).into_boxed_slice();
        assert_eq!(boxed.len(), 5);
        assert_eq!(ints(&[1, 2]).into_boxed_slice()[1].int64(), 2);
    }

    #[test]
    fn index_mut_and_slices_work() {
        let mut args = ints(&[1, 2, 3]);
        args[1] = Field::Int64(20);
        assert_eq!(contents(&args), [1, 20, 3]);
        assert_eq!(args[1..].len(), 2);
        args.as_mut_slice()[0] = Field::Int64(10);
        assert_eq!(args.first().map(Field::int64), Some(10));
    }

    #[test]
    fn dropping_drops_exactly_the_initialised_fields() {
        for n in 0..=7 {
            let witness = Rc::new(Cell::new(0));
            let mut args = Args::new();
            for _ in 0..n {
                args.push(probe(&witness));
            }
            assert_eq!(Rc::strong_count(&witness), 1 + n);
            drop(args);
            assert_eq!(Rc::strong_count(&witness), 1, "{n} arguments");
        }
    }

    #[test]
    fn moving_fields_around_never_drops_twice_or_leaks() {
        for n in 0..=7 {
            for taken in 0..=n {
                let witness = Rc::new(Cell::new(0));
                let mut args: Args = (0..n).map(|_| probe(&witness)).collect();
                let front = args.take_front(taken);
                assert_eq!(front.len(), taken);
                assert_eq!(args.len(), n - taken);
                assert_eq!(Rc::strong_count(&witness), 1 + n);
                drop(front);
                assert_eq!(Rc::strong_count(&witness), 1 + n - taken);
                let mut merged = Args::new();
                merged.extend(args);
                assert_eq!(Rc::strong_count(&witness), 1 + n - taken);
                drop(merged);
                assert_eq!(Rc::strong_count(&witness), 1);
            }
        }
    }

    #[test]
    fn a_half_consumed_iterator_drops_the_rest() {
        for n in [3, 6] {
            let witness = Rc::new(Cell::new(0));
            let args: Args = (0..n).map(|_| probe(&witness)).collect();
            let mut iter = args.into_iter();
            drop(iter.next());
            assert_eq!(Rc::strong_count(&witness), n);
            drop(iter);
            assert_eq!(Rc::strong_count(&witness), 1);
        }
    }

    #[test]
    fn cloning_and_boxing_account_for_every_field() {
        let witness = Rc::new(Cell::new(0));
        let args: Args = (0..3).map(|_| probe(&witness)).collect();
        let copy = args.clone();
        assert_eq!(Rc::strong_count(&witness), 1 + 3);
        let boxed = copy.into_boxed_slice();
        assert_eq!(Rc::strong_count(&witness), 1 + 3);
        drop(boxed);
        drop(args);
        assert_eq!(Rc::strong_count(&witness), 1);
    }
}
