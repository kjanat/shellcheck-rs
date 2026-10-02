//! Runtime support for Haskell compiled to Rust.
//!
//! The design rule for this crate is that as little of it as possible should
//! ever appear in generated code. Anything GHC's demand analysis proves strict
//! is emitted as a plain Rust value; what is left over -- bindings that may or
//! may not be demanded, and genuinely cyclic values -- lands here.

use std::cell::RefCell;
use std::mem::ManuallyDrop;
use std::rc::Rc;

/// The program's address literals, written by the emitter as one static table
/// and installed before any generated code runs. Global rather than
/// thread-local: the program runs on a thread of its own (`on_program_stack`).
static INSTALLED: std::sync::OnceLock<&'static [&'static [u8]]> = std::sync::OnceLock::new();

/// Install the program's address literal table. Installing the same table
/// again is a no-op; installing a different one is a bug and panics.
pub fn install_literals(table: &'static [&'static [u8]]) {
    let installed = *INSTALLED.get_or_init(|| table);
    assert!(
        std::ptr::eq(installed, table),
        "h2r-rt: a second, different address literal table was installed"
    );
}

/// An `Addr#`: a literal's index in the installed table and a byte offset into
/// that literal, eight bytes in all so that a `Field` stays at sixteen.
#[derive(Debug, Clone, Copy)]
pub struct Addr {
    literal: u32,
    offset: u32,
}

impl Addr {
    pub fn literal(index: u32) -> Self {
        Addr {
            literal: index,
            offset: 0,
        }
    }

    fn position(self, delta: i64) -> u32 {
        i64::from(self.offset)
            .checked_add(delta)
            .and_then(|at| u32::try_from(at).ok())
            .expect("h2r-rt: an address offset left the address space")
    }

    pub fn index_char(self, index: i64) -> i64 {
        self.index_word8(index)
    }

    pub fn index_word8(self, index: i64) -> i64 {
        let table = INSTALLED
            .get()
            .expect("h2r-rt: the address literal table was never installed");
        let bytes = table
            .get(self.literal as usize)
            .expect("h2r-rt: an address names a literal outside the table");
        i64::from(bytes[self.position(index) as usize])
    }

    pub fn plus(self, delta: i64) -> Self {
        Addr {
            literal: self.literal,
            offset: self.position(delta),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Bytes(Rc<RefCell<Vec<u8>>>);

impl Bytes {
    pub fn new(size: i64) -> Self {
        let size = usize::try_from(size).expect("h2r-rt: a byte array of negative size");
        Bytes(Rc::new(RefCell::new(vec![0; size])))
    }

    pub fn from_words(words: &[u64]) -> Self {
        Bytes(Rc::new(RefCell::new(
            words.iter().flat_map(|word| word.to_le_bytes()).collect(),
        )))
    }

    pub fn size(&self) -> i64 {
        self.0.borrow().len() as i64
    }

    fn span(offset: i64, count: usize) -> std::ops::Range<usize> {
        let start = usize::try_from(offset).expect("h2r-rt: a negative byte array offset");
        start..start + count
    }

    pub fn index_word(&self, index: i64) -> i64 {
        let bytes = self.0.borrow();
        let word = &bytes[Self::span(index * 8, 8)];
        i64::from_ne_bytes(word.try_into().expect("h2r-rt: a word is eight bytes"))
    }

    pub fn write_word(&self, index: i64, word: i64) {
        self.0.borrow_mut()[Self::span(index * 8, 8)].copy_from_slice(&word.to_ne_bytes());
    }

    pub fn index_word8(&self, index: i64) -> i64 {
        i64::from(self.0.borrow()[Self::span(index, 1)][0])
    }

    pub fn write_word8(&self, index: i64, byte: i64) {
        self.0.borrow_mut()[Self::span(index, 1)][0] = byte as u8;
    }

    pub fn shrink(&self, size: i64) {
        let size = usize::try_from(size).expect("h2r-rt: a byte array of negative size");
        let mut bytes = self.0.borrow_mut();
        assert!(
            size <= bytes.len(),
            "h2r-rt: a byte array shrunk past its size"
        );
        bytes.truncate(size);
    }

    pub fn set(&self, offset: i64, count: i64, byte: i64) {
        let count = usize::try_from(count).expect("h2r-rt: a negative byte count");
        self.0.borrow_mut()[Self::span(offset, count)].fill(byte as u8);
    }

    pub fn copy(source: &Bytes, from: i64, target: &Bytes, to: i64, count: i64) {
        let count = usize::try_from(count).expect("h2r-rt: a negative byte count");
        let (from, to) = (Self::span(from, count), Self::span(to, count));
        if Rc::ptr_eq(&source.0, &target.0) {
            source.0.borrow_mut().copy_within(from, to.start);
        } else {
            target.0.borrow_mut()[to].copy_from_slice(&source.0.borrow()[from]);
        }
    }
}

mod cell;

#[cfg(feature = "stats")]
pub mod stats;

/// Install the emitter's table of thunk-creating sites (WP17a); the generated
/// entry functions call it next to `install_literals` when emitted with stats.
#[cfg(feature = "stats")]
#[allow(unused_imports)]
pub use self::stats::{SiteInfo, install_sites};

// Public API of the crate; unused when the runtime is inlined as a private module.
#[allow(unused_imports)]
pub use self::cell::{Code, Deferred, Lazy, Shared, Thunk, shared};

pub trait Suspend: Sized + 'static {
    fn suspend(f: impl FnOnce() -> Self + 'static) -> Self;
}

impl Suspend for Int {
    fn suspend(f: impl FnOnce() -> Self + 'static) -> Self {
        Self::defer_to(f)
    }
}

impl Suspend for Data {
    fn suspend(f: impl FnOnce() -> Self + 'static) -> Self {
        Self::defer_to(f)
    }
}

impl Suspend for Closure {
    fn suspend(f: impl FnOnce() -> Self + 'static) -> Self {
        Self::defer_to(f)
    }
}

impl Suspend for Field {
    fn suspend(f: impl FnOnce() -> Self + 'static) -> Self {
        Self::defer_to(f)
    }
}

macro_rules! suspensions {
    ($($delay:ident $delay_at:ident $step:ident $n:literal($($argument:ident: $ty:ident),*);)*) => {$(
        pub fn $delay<T: Suspend, $($ty: 'static),*>(
            entry: fn($($ty),*) -> T,
            ($($argument,)*): ($($ty,)*),
        ) -> T {
            #[cfg(feature = "stats")]
            stats::bump(stats::DELAY + $n);
            T::suspend(move || entry($($argument),*))
        }

        /// As the function above, made at emitter site `site` (WP17a). Without
        /// the `stats` feature the site is ignored and this is that function.
        #[cfg_attr(not(feature = "stats"), inline(always))]
        pub fn $delay_at<T: Suspend, $($ty: 'static),*>(
            site: u32,
            entry: fn($($ty),*) -> T,
            arguments: ($($ty,)*),
        ) -> T {
            #[cfg(feature = "stats")]
            {
                stats::set_site(site);
                let thunk = $delay(entry, arguments);
                stats::set_site(stats::NO_SITE);
                thunk
            }
            #[cfg(not(feature = "stats"))]
            {
                let _ = site;
                $delay(entry, arguments)
            }
        }

        pub fn $step<R: 'static, $($ty: 'static),*>(
            entry: fn($($ty),*) -> Step<R>,
            ($($argument,)*): ($($ty,)*),
        ) -> Step<R> {
            #[cfg(feature = "stats")]
            stats::bump(stats::STEP + $n);
            Step::Next(Box::new(move || entry($($argument),*)))
        }
    )*};
}

suspensions! {
    delay0 delay0_at step0 0();
    delay1 delay1_at step1 1(a: A);
    delay2 delay2_at step2 2(a: A, b: B);
    delay3 delay3_at step3 3(a: A, b: B, c: C);
    delay4 delay4_at step4 4(a: A, b: B, c: C, d: D);
    delay5 delay5_at step5 5(a: A, b: B, c: C, d: D, e: E);
    delay6 delay6_at step6 6(a: A, b: B, c: C, d: D, e: E, f: F);
    delay7 delay7_at step7 7(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
    delay8 delay8_at step8 8(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
    delay9 delay9_at step9 9(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
    delay10 delay10_at step10 10(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
    delay11 delay11_at step11 11(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
    delay12 delay12_at step12 12(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
    delay13 delay13_at step13 13(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
    delay14 delay14_at step14 14(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
    delay15 delay15_at step15 15(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
    delay16 delay16_at step16 16(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);
}

pub fn apply_later<T: Suspend>(callee: Closure, arguments: Vec<Field>, read: fn(&Field) -> T) -> T {
    #[cfg(feature = "stats")]
    stats::bump(stats::APPLY_LATER);
    T::suspend(move || read(&callee.apply(arguments)))
}

/// [`apply_later`] made at emitter site `site` (WP17a); without the `stats`
/// feature the site is ignored.
#[cfg_attr(not(feature = "stats"), inline(always))]
pub fn apply_later_at<T: Suspend>(
    site: u32,
    callee: Closure,
    arguments: Vec<Field>,
    read: fn(&Field) -> T,
) -> T {
    #[cfg(feature = "stats")]
    {
        stats::set_site(site);
        let thunk = apply_later(callee, arguments, read);
        stats::set_site(stats::NO_SITE);
        thunk
    }
    #[cfg(not(feature = "stats"))]
    {
        let _ = site;
        apply_later(callee, arguments, read)
    }
}

pub fn apply_step(callee: Closure, arguments: Vec<Field>, read: fn(&Field) -> i64) -> Step<i64> {
    #[cfg(feature = "stats")]
    stats::bump(stats::APPLY_STEP);
    Step::Next(Box::new(move || match callee.apply_tail(arguments) {
        Tail::Enter(step) => step,
        Tail::Value(value) => Step::Done(read(&value)),
    }))
}

/// A shared, call-by-need boxed machine Int. Its I# field is unlifted.
#[derive(Clone)]
pub struct Int(Shared<i64>);

impl Int {
    pub fn defer(f: impl FnOnce() -> i64 + 'static) -> Self {
        Self(shared(f))
    }
    pub fn defer_to(f: impl FnOnce() -> Self + 'static) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::DEFER_TO);
        Self(Shared::step(move || Thunk::Indirect(f().0)))
    }
    pub fn pending() -> Self {
        Self(Shared::pending())
    }
    pub fn fill(&self, value: Self) {
        self.0.fill(move || Thunk::Indirect(value.0));
    }
    pub fn ready(value: i64) -> Self {
        Self(Shared::ready(value))
    }
    pub fn force(&self) -> i64 {
        *self.0.force()
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    pub fn shares_with(&self, other: &Self) -> bool {
        Shared::ptr_eq(&self.0, &other.0)
    }
}

/// A general algebraic value. The outer node and every lifted field have
/// independent memoisation cells; inspecting a tag never forces lazy fields.
#[derive(Clone)]
pub struct Data(Shared<Node>);

/// A data constructor as the generated code knows it: its name, for
/// diagnostics and `show`, and one `u32` the emitter numbers per name across
/// the whole program, which is all that pattern matches and the runtime's own
/// checks compare. The runtime is compiled into every generated crate, so a
/// constructor reached through two crates is two statics; the tag, never the
/// address, is what identifies it.
pub struct Constructor {
    pub name: &'static str,
    pub tag: u32,
}

impl PartialEq for Constructor {
    fn eq(&self, other: &Self) -> bool {
        self.tag == other.tag
    }
}

impl Eq for Constructor {}

impl std::fmt::Debug for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name)
    }
}

impl std::fmt::Display for Constructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name)
    }
}

#[derive(Clone)]
pub struct Node {
    pub constructor: &'static Constructor,
    pub fields: Fields,
}

/// The fields of a constructor, inline up to three. The arrays and the vector are
/// `ManuallyDrop` because `Fields` drops them itself (see its `Drop`).
#[derive(Clone)]
pub enum Fields {
    Zero,
    One(ManuallyDrop<[Field; 1]>),
    Two(ManuallyDrop<[Field; 2]>),
    Three(ManuallyDrop<[Field; 3]>),
    Many(ManuallyDrop<Vec<Field>>),
}

/// Drop one field without the call into its drop glue for the three common
/// payloads: the two that own nothing (a character list is mostly these) and
/// a constructor cell (its count is decremented here, and the free is the
/// vtable call `Shared`'s `Drop` makes).
///
/// # Safety
/// `field` is valid, and is not used again.
#[inline(always)]
unsafe fn drop_field(field: &mut Field) {
    match field {
        Field::Int64(_) | Field::Char(_) => {}
        // SAFETY: by the contract.
        Field::Data(data) => unsafe { std::ptr::drop_in_place(data) },
        // SAFETY: by the contract.
        _ => unsafe { std::ptr::drop_in_place(field) },
    }
}

/// The cases that are not a tail-less node or a head and a tail, kept out of
/// line so those two stay small (and a match with two arms is a compare, not
/// a jump table).
///
/// # Safety
/// As [`drop_field`]: the fields are dropped, so they must not be used again.
#[inline(never)]
unsafe fn drop_other(fields: &mut Fields) {
    // SAFETY: by the contract.
    unsafe {
        match fields {
            Fields::Zero | Fields::Two(_) => {}
            Fields::One(fields) => {
                let [a] = &mut **fields;
                drop_field(a);
            }
            Fields::Three(fields) => {
                let [a, b, c] = &mut **fields;
                drop_field(a);
                drop_field(b);
                drop_field(c);
            }
            Fields::Many(fields) => ManuallyDrop::drop(fields),
        }
    }
}

/// Both fields of a node, when the first may own something.
///
/// # Safety
/// As [`drop_field`].
#[inline(never)]
unsafe fn drop_two(a: &mut Field, b: &mut Field) {
    // SAFETY: by the contract.
    unsafe {
        drop_field(a);
        drop_field(b);
    }
}

impl Drop for Fields {
    /// What the derived glue did, without its loops: each field is dropped
    /// once, in order, and a field whose drop panics leaks the later ones
    /// (the glue would drop them while unwinding). Lists drop recursively
    /// through here exactly as before.
    #[inline]
    fn drop(&mut self) {
        // SAFETY: `self` is being dropped, so no field is used again, and the
        // arrays and the vector are `ManuallyDrop`, so nothing else drops them.
        unsafe {
            match self {
                Fields::Zero => {}
                Fields::Two(fields) => {
                    let [a, b] = &mut **fields;
                    // A head that owns nothing (a character) leaves only the
                    // tail, dropped as the last thing this function does: no
                    // stack frame, and the recursion down a list is a chain of
                    // jumps from one free to the next.
                    if matches!(a, Field::Int64(_) | Field::Char(_)) {
                        drop_field(b);
                    } else {
                        drop_two(a, b);
                    }
                }
                _ => drop_other(self),
            }
        }
    }
}

impl std::ops::Deref for Fields {
    type Target = [Field];
    fn deref(&self) -> &[Field] {
        match self {
            Fields::Zero => &[],
            Fields::One(fields) => &**fields,
            Fields::Two(fields) => &**fields,
            Fields::Three(fields) => &**fields,
            Fields::Many(fields) => fields,
        }
    }
}

impl From<[Field; 0]> for Fields {
    fn from(_: [Field; 0]) -> Self {
        Fields::Zero
    }
}

impl From<[Field; 1]> for Fields {
    #[inline(always)]
    fn from([a]: [Field; 1]) -> Self {
        Fields::One(ManuallyDrop::new([a]))
    }
}

impl From<[Field; 2]> for Fields {
    #[inline(always)]
    fn from([a, b]: [Field; 2]) -> Self {
        Fields::Two(ManuallyDrop::new([a, b]))
    }
}

impl From<[Field; 3]> for Fields {
    #[inline(always)]
    fn from([a, b, c]: [Field; 3]) -> Self {
        Fields::Three(ManuallyDrop::new([a, b, c]))
    }
}

impl From<Vec<Field>> for Fields {
    fn from(fields: Vec<Field>) -> Self {
        let fields = match <[Field; 1]>::try_from(fields) {
            Ok(one) => return Fields::One(ManuallyDrop::new(one)),
            Err(fields) => fields,
        };
        let fields = match <[Field; 2]>::try_from(fields) {
            Ok(two) => return Fields::Two(ManuallyDrop::new(two)),
            Err(fields) => fields,
        };
        let fields = match <[Field; 3]>::try_from(fields) {
            Ok(three) => return Fields::Three(ManuallyDrop::new(three)),
            Err(fields) => fields,
        };
        if fields.is_empty() {
            Fields::Zero
        } else {
            Fields::Many(ManuallyDrop::new(fields))
        }
    }
}

#[derive(Clone)]
pub enum Field {
    Int64(i64),
    /// An unboxed `Char#`: a Unicode code point, kept apart from `Int64` so a
    /// mixed-up field is a panic rather than a silently wrong character.
    Char(i64),
    Int(Int),
    Data(Data),
    Closure(Closure),
    MutVar(MutVar),
    Bytes(Bytes),
    Array(Array),
    Deferred(Shared<Field>),
    Tuple(Rc<Vec<Field>>),
    Addr(Addr),
}

/// The data of a field that is still a thunk: a thunk of its own. Out of line
/// so that the common `Field::data` (an evaluated field) does not carry the
/// allocation's registers and stack frame.
#[inline(never)]
fn deferred_data(cell: &Shared<Field>) -> Data {
    #[cfg(feature = "stats")]
    stats::bump(stats::DEFERRED_DATA);
    let cell = cell.clone();
    Data::defer_to(move || cell.force().data())
}

fn deferred(value: Field) -> Thunk<Field> {
    match value {
        Field::Deferred(next) => Thunk::Indirect(next),
        value => Thunk::Value(value),
    }
}

impl Field {
    pub fn defer_to(f: impl FnOnce() -> Field + 'static) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::DEFER_TO + 3);
        Self::Deferred(Shared::step(move || deferred(f())))
    }
    pub fn pending() -> Self {
        Self::Deferred(Shared::pending())
    }
    pub fn fill(&self, value: Field) {
        match self {
            Self::Deferred(cell) => cell.fill(move || deferred(value)),
            _ => panic!("h2r-rt: a filled binding must be pending"),
        }
    }
    pub fn force(&self) {
        match self {
            Self::Int64(_)
            | Self::Char(_)
            | Self::MutVar(_)
            | Self::Bytes(_)
            | Self::Array(_)
            | Self::Tuple(_)
            | Self::Addr(_) => {}
            Self::Int(v) => {
                v.force();
            }
            Self::Data(v) => {
                v.force();
            }
            Self::Closure(v) => {
                v.force();
            }
            Self::Deferred(cell) => cell.force().force(),
        }
    }
    pub fn dynamic(&self) -> Field {
        self.clone()
    }
    #[inline]
    pub fn int64(&self) -> i64 {
        match self {
            Self::Int64(v) => *v,
            _ => panic!("invalid Int# field"),
        }
    }
    pub fn char_code(&self) -> i64 {
        match self {
            Self::Char(v) => *v,
            _ => panic!("invalid Char# field"),
        }
    }
    pub fn int(&self) -> Int {
        match self {
            Self::Int(v) => v.clone(),
            Self::Deferred(cell) => match cell.get() {
                Some(value) => value.int(),
                None => {
                    let cell = cell.clone();
                    Int::defer_to(move || cell.force().int())
                }
            },
            _ => panic!("invalid Int field"),
        }
    }
    pub fn data(&self) -> Data {
        match self {
            Self::Data(v) => v.clone(),
            Self::Deferred(cell) => match cell.get() {
                Some(value) => value.data(),
                None => deferred_data(cell),
            },
            _ => panic!("invalid data field"),
        }
    }
    #[inline]
    pub fn closure(&self) -> Closure {
        match self {
            Self::Closure(v) => v.clone(),
            _ => self.closure_other(),
        }
    }
    /// A `closure` that is not a closure cell: a field that is still a thunk,
    /// or a miscompile. Out of line, so the common case stays small.
    #[inline(never)]
    fn closure_other(&self) -> Closure {
        match self {
            Self::Deferred(cell) => match cell.get() {
                Some(value) => value.closure(),
                None => {
                    let cell = cell.clone();
                    Closure::defer_to(move || cell.force().closure())
                }
            },
            _ => panic!("invalid function carrier"),
        }
    }
    pub fn mut_var(&self) -> MutVar {
        match self {
            Self::MutVar(v) => v.clone(),
            _ => panic!("invalid MutVar# field"),
        }
    }
    pub fn bytes(&self) -> Bytes {
        match self {
            Self::Bytes(v) => v.clone(),
            _ => panic!("invalid byte array field"),
        }
    }
    pub fn addr(&self) -> Addr {
        match self {
            Self::Addr(v) => *v,
            _ => panic!("invalid Addr# field"),
        }
    }
    pub fn tuple(&self) -> Rc<Vec<Field>> {
        match self {
            Self::Tuple(v) => v.clone(),
            _ => panic!("invalid unboxed tuple"),
        }
    }
    pub fn array(&self) -> Array {
        match self {
            Self::Array(v) => v.clone(),
            _ => panic!("invalid array field"),
        }
    }
}

#[derive(Clone)]
pub struct Array(Rc<RefCell<Vec<Field>>>);

impl Array {
    pub fn new(size: i64, fill: Field) -> Self {
        let size = usize::try_from(size).expect("h2r-rt: an array of negative size");
        Array(Rc::new(RefCell::new(vec![fill; size])))
    }

    fn slot(index: i64) -> usize {
        usize::try_from(index).expect("h2r-rt: a negative array index")
    }

    pub fn read(&self, index: i64) -> Field {
        self.0.borrow()[Self::slot(index)].clone()
    }

    pub fn write(&self, index: i64, value: Field) {
        self.0.borrow_mut()[Self::slot(index)] = value;
    }

    pub fn size(&self) -> i64 {
        self.0.borrow().len() as i64
    }
}

#[derive(Clone)]
pub struct MutVar(Rc<RefCell<Field>>);

impl MutVar {
    pub fn new(value: Field) -> Self {
        MutVar(Rc::new(RefCell::new(value)))
    }

    pub fn read(&self) -> Field {
        self.0.borrow().clone()
    }

    pub fn write(&self, value: Field) {
        *self.0.borrow_mut() = value;
    }
}

pub fn raise_arithmetic(message: &str) -> ! {
    report_error(message.as_bytes())
}

pub fn raise_exception() -> ! {
    panic!("h2r-rt: an uncaught Haskell exception")
}

pub fn absent_error(message: Addr) -> ! {
    let text: Vec<u8> = (0..)
        .map(|index| message.index_word8(index) as u8)
        .take_while(|byte| *byte != 0)
        .collect();
    eprintln!(
        "internal error: Oops!  Entered absent arg {}",
        String::from_utf8_lossy(&text)
    );
    std::process::abort()
}

/// A shared lazy function value. Partial application retains arguments without
/// forcing them; saturation invokes code exactly once per call, not per closure.
///
/// A closure made by [`Closure::bind`] is one allocation: the cell holds the
/// [`ClosureCode`] value (arity and shape) and, as its code tail, the captures
/// and the function pointers. A partial application is a second, small cell
/// that points at the cell with the code and holds the arguments supplied so
/// far. A deferred closure is a thunk cell whose value points at the closure it
/// turned out to be.
#[derive(Clone)]
pub struct Closure(Shared<ClosureCode>);

/// What a closure cell's value says about calling it. Opaque: [`Closure::force`]
/// hands it out so a caller can tell the cell has been evaluated.
#[derive(Clone)]
pub struct ClosureCode(ManuallyDrop<Kind>);

impl Drop for ClosureCode {
    /// Most closures are `Inline` and own nothing, so the test is in line and
    /// only a partial application or a forward calls out.
    #[inline(always)]
    fn drop(&mut self) {
        if !matches!(*self.0, Kind::Inline { .. }) {
            drop_kind(&mut self.0);
        }
    }
}

/// Drop what a partial application or a forward owns, field by field with
/// [`drop_field`] (a supplied argument is mostly an integer or a cell).
#[inline(never)]
fn drop_kind(kind: &mut ManuallyDrop<Kind>) {
    match &mut **kind {
        Kind::Inline { .. } => {}
        Kind::Partial {
            parent, supplied, ..
        } => {
            let len = supplied.len();
            let fields = supplied.as_mut_ptr();
            // SAFETY: called once, from `ClosureCode::drop`, which is the last
            // use, so nothing reads the fields again. The length is zeroed
            // first, so the vector's own drop only frees the buffer; each
            // field is in bounds and dropped once.
            unsafe {
                supplied.set_len(0);
                for index in 0..len {
                    drop_field(&mut *fields.add(index));
                }
                std::ptr::drop_in_place(supplied);
                std::ptr::drop_in_place(parent);
            }
        }
        // SAFETY: as above; `target` is dropped once.
        Kind::Forward(target) => unsafe { std::ptr::drop_in_place(target) },
    }
}

/// `repr(u8)` gives the enum a plain one-byte discriminant at offset 0, so a
/// match is one compare; the default layout hides it in the capacity of
/// `supplied`, which costs about ten instructions to decode on every call and
/// every drop. The fields are in the order that keeps the whole at 40 bytes
/// (tag, `entry` and `arity` share the first eight).
#[derive(Clone)]
#[repr(u8)]
enum Kind {
    /// The function body is this cell's own code tail ([`Shared::call`]).
    /// `entry` is whether the tail also has an entry that continues as a tail
    /// call.
    Inline { entry: bool, arity: u32 },
    /// `parent` is an `Inline` cell (never another partial application or a
    /// forward: those are flattened when this one is made); `supplied` are the
    /// arguments already given, fewer than the arity. `arity` and `entry` are
    /// the parent's.
    Partial {
        entry: bool,
        arity: u32,
        parent: Closure,
        supplied: Vec<Field>,
    },
    /// The value of a thunk cell that evaluated to the closure `target`, a
    /// cell whose own value is `Inline` or `Partial`, never a `Forward`.
    /// [`Closure::resolve`] follows the link.
    Forward(Closure),
}

impl ClosureCode {
    #[inline(always)]
    fn inline(arity: usize, entry: bool) -> Self {
        assert!(arity > 0);
        Self(ManuallyDrop::new(Kind::Inline {
            entry,
            arity: u32::try_from(arity).expect("h2r-rt: a function of absurd arity"),
        }))
    }

    fn forward(target: Closure) -> Self {
        Self(ManuallyDrop::new(Kind::Forward(target)))
    }
}

/// The code tail of `Closure::bind`: a known function and its captures.
struct Bound<C> {
    code: fn(&C, Vec<Field>) -> Field,
    captures: C,
}

/// The code tail of `Closure::bind_entering`.
struct BoundEntering<C> {
    code: fn(&C, Vec<Field>) -> Field,
    enter: fn(&C, Vec<Field>) -> Step<i64>,
    captures: C,
}

/// The code tail of `Closure::ready`: any Rust closure.
struct Boxed<F>(F);

/// The code tail of `Closure::entering`.
struct BoxedEntering<F, G> {
    code: F,
    enter: G,
}

/// Closure cells are created evaluated, so nothing ever enters or fills them.
/// The value of such a cell (`Kind::Inline`) refers to the cell's own tail, so
/// a cell that evaluates to it gets a `Kind::Forward` to it instead of a copy.
macro_rules! never_entered {
    () => {
        fn shares() -> bool {
            true
        }
        fn share(&self, cell: &Shared<ClosureCode>) -> ClosureCode {
            ClosureCode::forward(Closure(cell.clone()))
        }
        fn enter(&self) -> Option<Thunk<ClosureCode>> {
            unreachable!("h2r-rt: a closure cell is created evaluated")
        }
        fn fill(&self, _: Deferred<ClosureCode>) -> bool {
            false
        }
    };
}

impl<C: 'static> Code<ClosureCode> for Bound<C> {
    never_entered!();
    fn call(&self, arguments: Vec<Field>) -> Field {
        (self.code)(&self.captures, arguments)
    }
}

impl<C: 'static> Code<ClosureCode> for BoundEntering<C> {
    never_entered!();
    fn call(&self, arguments: Vec<Field>) -> Field {
        (self.code)(&self.captures, arguments)
    }
    fn call_enter(&self, arguments: Vec<Field>) -> Step<i64> {
        (self.enter)(&self.captures, arguments)
    }
}

impl<F: Fn(Vec<Field>) -> Field + 'static> Code<ClosureCode> for Boxed<F> {
    never_entered!();
    fn call(&self, arguments: Vec<Field>) -> Field {
        (self.0)(arguments)
    }
}

impl<F, G> Code<ClosureCode> for BoxedEntering<F, G>
where
    F: Fn(Vec<Field>) -> Field + 'static,
    G: Fn(Vec<Field>) -> Step<i64> + 'static,
{
    never_entered!();
    fn call(&self, arguments: Vec<Field>) -> Field {
        (self.code)(arguments)
    }
    fn call_enter(&self, arguments: Vec<Field>) -> Step<i64> {
        (self.enter)(arguments)
    }
}

pub enum Tail {
    Value(Field),
    Enter(Step<i64>),
}

pub enum Step<R> {
    Done(R),
    Next(Box<dyn FnOnce() -> Step<R>>),
}

impl<R> Step<R> {
    pub fn run(self) -> R {
        let mut step = self;
        loop {
            match step {
                Step::Done(value) => return value,
                Step::Next(next) => step = next(),
            }
        }
    }
}

impl Closure {
    pub fn ready(arity: usize, code: impl Fn(Vec<Field>) -> Field + 'static) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::BOXED);
        Self(Shared::ready_with(
            ClosureCode::inline(arity, false),
            Boxed(code),
        ))
    }
    pub fn entering(
        arity: usize,
        code: impl Fn(Vec<Field>) -> Field + 'static,
        enter: impl Fn(Vec<Field>) -> Step<i64> + 'static,
    ) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::BOXED);
        Self(Shared::ready_with(
            ClosureCode::inline(arity, true),
            BoxedEntering { code, enter },
        ))
    }
    /// A known function and its captures: one allocation, the cell.
    pub fn bind<C: 'static>(arity: usize, code: fn(&C, Vec<Field>) -> Field, captures: C) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::BIND);
        Self(Shared::ready_with(
            ClosureCode::inline(arity, false),
            Bound { code, captures },
        ))
    }
    pub fn bind_entering<C: 'static>(
        arity: usize,
        code: fn(&C, Vec<Field>) -> Field,
        enter: fn(&C, Vec<Field>) -> Step<i64>,
        captures: C,
    ) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::BIND_ENTERING);
        Self(Shared::ready_with(
            ClosureCode::inline(arity, true),
            BoundEntering {
                code,
                enter,
                captures,
            },
        ))
    }
    pub fn defer_to(f: impl FnOnce() -> Self + 'static) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::DEFER_TO + 2);
        Self(Shared::step(move || Thunk::Indirect(f().0)))
    }
    pub fn pending() -> Self {
        Self(Shared::pending())
    }
    pub fn fill(&self, value: Self) {
        self.0.fill(move || Thunk::Indirect(value.0));
    }
    /// Force this closure; if it is a thunk that turned out to be another
    /// closure, step to that one, which is a cell with the code or a partial
    /// application of it. `Shared` chases chains of thunks, and what it leaves
    /// in the thunk is a `Kind::Forward` to the last cell of the chain, so
    /// there is at most one link to follow.
    fn resolve(&self) -> (&Closure, &ClosureCode) {
        let code = self.0.force();
        match &*code.0 {
            Kind::Forward(target) => (target, target.0.force()),
            _ => (self, code),
        }
    }
    /// The cell with the code to call, the arguments already supplied to it,
    /// the arity of the closure applied and whether it has an entry.
    fn split(&self) -> (&Closure, &[Field], usize, bool) {
        Self::decode(self, self.0.force())
    }
    /// [`Closure::split`] for a closure whose cell has been forced to `code`.
    #[inline(always)]
    fn decode<'a>(
        this: &'a Closure,
        code: &'a ClosureCode,
    ) -> (&'a Closure, &'a [Field], usize, bool) {
        match &*code.0 {
            Kind::Inline { entry, arity } => (this, &[], *arity as usize, *entry),
            Kind::Partial {
                entry,
                arity,
                parent,
                supplied,
            } => (parent, supplied, *arity as usize, *entry),
            Kind::Forward(target) => match &*target.0.force().0 {
                Kind::Inline { entry, arity } => (target, &[], *arity as usize, *entry),
                Kind::Partial {
                    entry,
                    arity,
                    parent,
                    supplied,
                } => (parent, supplied, *arity as usize, *entry),
                Kind::Forward(_) => unreachable!("a forward is never a forward's target"),
            },
        }
    }
    pub fn apply_tail(&self, arguments: Vec<Field>) -> Tail {
        let (parent, supplied, arity, entry) = self.split();
        if entry && supplied.len() + arguments.len() == arity {
            if supplied.is_empty() {
                return Tail::Enter(parent.0.call_enter(arguments));
            }
            return Tail::Enter(
                parent
                    .0
                    .call_enter(Self::joined(supplied, arguments, arity)),
            );
        }
        Tail::Value(self.apply(arguments))
    }
    pub fn force(&self) -> &ClosureCode {
        self.resolve().1
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    #[inline]
    pub fn apply(&self, arguments: Vec<Field>) -> Field {
        #[cfg(feature = "stats")]
        stats::bump(stats::APPLY);
        // The common call: a closure with its own code, given exactly its
        // arity. Nothing else (a thunk that turned out to be a closure, a
        // partial application, too few or too many arguments) is decided here.
        // A thunk is forced by this test and again, now a load, by the general
        // case; the code runs once either way.
        let code = self.0.force();
        match &*code.0 {
            Kind::Inline { arity, .. } if arguments.len() == *arity as usize => {
                self.0.call(arguments)
            }
            _ => self.apply_general(code, arguments),
        }
    }
    /// Everything but the common call.
    #[inline(never)]
    fn apply_general(&self, code: &ClosureCode, arguments: Vec<Field>) -> Field {
        #[cfg(feature = "stats")]
        stats::bump(stats::APPLY_GENERAL);
        let (parent, supplied, arity, entry) = Self::decode(self, code);
        let missing = arity - supplied.len();
        if arguments.len() == missing {
            // Saturating exactly, from a thunk or a partial application.
            return Self::call_with(parent, supplied, arity, arguments);
        }
        if arguments.len() < missing {
            if arguments.is_empty() {
                return Field::Closure(self.clone());
            }
            return Field::Closure(Self::partial(parent, supplied, arity, entry, arguments));
        }
        self.apply_over(arguments)
    }
    /// `supplied`, cloned, followed by `arguments`, moved, in a vector with room
    /// for `capacity` fields (at least as many as there are). Callers pass the
    /// arity, which is a `u32`, so the allocation needs no overflow check.
    #[inline(always)]
    fn joined(supplied: &[Field], mut arguments: Vec<Field>, capacity: usize) -> Vec<Field> {
        let count = supplied.len();
        let moved = arguments.len();
        assert!(count + moved <= capacity);
        let mut all: Vec<Field> = Vec::with_capacity(capacity);
        let base = all.as_mut_ptr();
        // SAFETY: `all` has room for `count + moved` fields and is empty, so
        // each write is in bounds and into uninitialised memory; `arguments`
        // gives up its fields (its length is zeroed, so they are dropped once,
        // by `all`) and its own buffer is a different allocation. The length
        // is set last: a panic in a clone (there is none: `Field::clone` only
        // counts) would leak, not double-drop.
        unsafe {
            for (index, field) in supplied.iter().enumerate() {
                base.add(index).write(field.clone());
            }
            if moved == 1 {
                // The usual last argument of a partial application: a copy
                // of one field, not a call to `memcpy`.
                base.add(count).write(arguments.as_ptr().read());
            } else {
                std::ptr::copy_nonoverlapping(arguments.as_ptr(), base.add(count), moved);
            }
            arguments.set_len(0);
            all.set_len(count + moved);
        }
        all
    }
    /// Call `parent`'s code with `supplied` followed by exactly the arguments
    /// that are missing.
    #[inline(always)]
    fn call_with(
        parent: &Closure,
        supplied: &[Field],
        arity: usize,
        arguments: Vec<Field>,
    ) -> Field {
        if supplied.is_empty() {
            return parent.0.call(arguments);
        }
        parent.0.call(Self::joined(supplied, arguments, arity))
    }
    /// A partial application of `parent`: `supplied` and then `arguments`,
    /// together fewer than the arity.
    #[inline(always)]
    fn partial(
        parent: &Closure,
        supplied: &[Field],
        arity: usize,
        entry: bool,
        arguments: Vec<Field>,
    ) -> Closure {
        #[cfg(feature = "stats")]
        stats::bump(stats::PARTIAL);
        // The first arguments of a closure nobody applied yet become its
        // `supplied` as they are, vector and all.
        let supplied = if supplied.is_empty() {
            arguments
        } else {
            let total = supplied.len() + arguments.len();
            Self::joined(supplied, arguments, total)
        };
        Self(Shared::ready_with(
            ClosureCode(ManuallyDrop::new(Kind::Partial {
                entry,
                arity: arity as u32,
                parent: parent.clone(),
                supplied,
            })),
            cell::Evaluated,
        ))
    }
    /// More arguments than the closure takes: call it with the first ones and
    /// apply the result to the rest, until none are left.
    #[inline(never)]
    fn apply_over(&self, mut arguments: Vec<Field>) -> Field {
        #[cfg(feature = "stats")]
        stats::bump(stats::APPLY_OVER);
        let mut held;
        let mut current = self;
        loop {
            let (parent, supplied, arity, entry) = current.split();
            let missing = arity - supplied.len();
            if arguments.len() < missing {
                if arguments.is_empty() {
                    return Field::Closure(current.clone());
                }
                return Field::Closure(Self::partial(parent, supplied, arity, entry, arguments));
            }
            let result = if arguments.len() == missing {
                let last = std::mem::take(&mut arguments);
                Self::call_with(parent, supplied, arity, last)
            } else {
                let mut all = Vec::with_capacity(arity);
                all.extend_from_slice(supplied);
                all.extend(arguments.drain(..missing));
                parent.0.call(all)
            };
            if arguments.is_empty() {
                return result;
            }
            held = result.closure();
            current = &held;
        }
    }
}

/// The constructors the unit tests build values from. The emitter numbers the
/// real ones; these tags only have to differ.
#[cfg(test)]
mod fixtures {
    use super::Constructor;

    macro_rules! fixtures {
        ($($id:ident $name:literal $tag:literal),* $(,)?) => {
            $(pub const $id: &Constructor = &Constructor { name: $name, tag: $tag };)*
            /// The fixture called `name`.
            pub fn c(name: &str) -> &'static Constructor {
                match name {
                    $($name => $id,)*
                    other => panic!("no fixture constructor {other}"),
                }
            }
        };
    }

    fixtures! {
        CONS ":" 1, NIL "[]" 2, CHAR "C#" 3, TRUE "True" 4, FALSE "False" 5,
        LT "LT" 6, EQ "EQ" 7, GT "GT" 8,
        EMPTY_STACK "EmptyCallStack" 9, PUSH_STACK "PushCallStack" 10,
        FREEZE_STACK "FreezeCallStack" 11, SRC_LOC "SrcLoc" 12,
        PAIR "Pair" 13, LIST_NIL "Nil" 14, LIST_CONS "Cons" 15,
    }
}

#[cfg(test)]
mod constructor_tests {
    use super::*;

    #[test]
    fn constructors_are_the_same_when_their_tags_are_the_same() {
        // Two crates each carry their own static for one constructor.
        static IN_ONE: Constructor = Constructor {
            name: "Just",
            tag: 7,
        };
        static IN_ANOTHER: Constructor = Constructor {
            name: "Just",
            tag: 7,
        };
        static OTHER: Constructor = Constructor {
            name: "Nothing",
            tag: 8,
        };
        assert!(!std::ptr::eq(&IN_ONE, &IN_ANOTHER));
        assert_eq!(&IN_ONE, &IN_ANOTHER);
        assert_ne!(&IN_ONE, &OTHER);
        assert_eq!(format!("{IN_ONE} {IN_ONE:?}"), "Just Just");
        let node = Data::ready(&IN_ONE, []);
        assert_eq!(node.force().constructor, &IN_ANOTHER);
    }
}

#[cfg(test)]
mod closure_tests {
    use super::*;

    #[test]
    fn partial_application_is_lazy_shared_and_reusable() {
        let calls = Rc::new(std::cell::Cell::new(0));
        let counter = calls.clone();
        let function = Closure::ready(2, move |args| {
            counter.set(counter.get() + 1);
            args[0].clone()
        });
        let forced = Rc::new(std::cell::Cell::new(0));
        let counter = forced.clone();
        let x = Int::defer(move || {
            counter.set(counter.get() + 1);
            42
        });
        let partial = function.apply(vec![Field::Int(x)]).closure();
        assert_eq!(calls.get(), 0);
        assert_eq!(forced.get(), 0);
        for _ in 0..2 {
            let poison = Int::defer(|| panic!("unused argument forced"));
            assert_eq!(partial.apply(vec![Field::Int(poison)]).int().force(), 42);
        }
        assert_eq!(calls.get(), 2);
        assert_eq!(forced.get(), 1);
    }

    #[test]
    fn overapplication_enters_returned_closure() {
        let f = Closure::ready(1, |args| {
            let x = args[0].int64();
            Field::Closure(Closure::ready(1, move |args| {
                Field::Int64(x + args[0].int64())
            }))
        });
        assert_eq!(
            f.apply(vec![Field::Int64(20), Field::Int64(22)]).int64(),
            42
        );
    }

    #[test]
    fn deferred_function_is_shared_without_entering_its_body() {
        let n = Rc::new(std::cell::Cell::new(0));
        let count = n.clone();
        let f = Closure::defer_to(move || {
            count.set(count.get() + 1);
            Closure::ready(1, |args| args[0].clone())
        });
        assert!(!f.is_evaluated());
        assert_eq!(f.clone().apply(vec![Field::Int64(1)]).int64(), 1);
        assert_eq!(f.apply(vec![Field::Int64(2)]).int64(), 2);
        assert_eq!(n.get(), 1);
    }

    fn add((captured,): &(i64,), arguments: Vec<Field>) -> Field {
        Field::Int64(captured + arguments[0].int64() + arguments[1].int64())
    }

    #[test]
    fn a_bound_closure_applies_partially_and_repeatedly_through_its_own_cell() {
        let function = Closure::bind(2, add, (40,));
        let first = function.apply(vec![Field::Int64(1)]).closure();
        // A partial application of a partial application points at the cell
        // with the code, not at the partial application.
        let again = first.apply(Vec::new()).closure();
        assert_eq!(again.apply(vec![Field::Int64(1)]).int64(), 42);
        assert_eq!(first.apply(vec![Field::Int64(5)]).int64(), 46);
        let wide = Closure::bind(
            3,
            |(): &(), a| Field::Int64(a[0].int64() * 100 + a[1].int64() * 10 + a[2].int64()),
            (),
        );
        let one = wide.apply(vec![Field::Int64(1)]).closure();
        let two = one.apply(vec![Field::Int64(2)]).closure();
        assert_eq!(two.apply(vec![Field::Int64(3)]).int64(), 123);
        assert_eq!(
            one.apply(vec![Field::Int64(4), Field::Int64(5)]).int64(),
            145
        );
    }

    #[test]
    fn a_bound_closures_captures_are_dropped_with_its_last_owner() {
        let drops = Rc::new(std::cell::Cell::new(0));
        struct Probe(Rc<std::cell::Cell<u32>>);
        impl Drop for Probe {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let function = Closure::bind(2, |_: &Probe, _| Field::Int64(0), Probe(drops.clone()));
        let partial = function.apply(vec![Field::Int64(1)]).closure();
        drop(function);
        assert_eq!(
            drops.get(),
            0,
            "the partial application keeps the code alive"
        );
        assert_eq!(partial.apply(vec![Field::Int64(2)]).int64(), 0);
        drop(partial);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    fn a_pending_closure_is_filled_and_applied_through_the_fill() {
        let cell = Closure::pending();
        let alias = cell.clone();
        cell.fill(Closure::bind(2, add, (40,)));
        assert_eq!(
            alias.apply(vec![Field::Int64(1), Field::Int64(1)]).int64(),
            42
        );
    }

    #[test]
    fn a_million_indirections_of_closures_force_in_constant_stack() {
        fn countdown(n: u32) -> Closure {
            Closure::defer_to(move || {
                if n == 0 {
                    Closure::bind(1, |(): &(), a| a[0].clone(), ())
                } else {
                    countdown(n - 1)
                }
            })
        }
        let chain = countdown(1_000_000);
        assert_eq!(chain.apply(vec![Field::Int64(9)]).int64(), 9);
        assert_eq!(chain.apply(vec![Field::Int64(8)]).int64(), 8);
    }

    #[test]
    fn a_deferred_partial_application_is_shared_not_copied() {
        let function = Closure::bind(2, add, (40,));
        let partial = function.apply(vec![Field::Int64(1)]).closure();
        let deferred = Closure::defer_to({
            let partial = partial.clone();
            move || partial
        });
        assert_eq!(deferred.apply(vec![Field::Int64(1)]).int64(), 42);
        assert_eq!(deferred.apply(vec![Field::Int64(2)]).int64(), 43);
    }

    #[test]
    fn a_partial_application_holds_each_supplied_argument_once() {
        // `Field::Tuple` is a reference-counted field: its count says how many
        // holders there are, so a field cloned or dropped twice shows.
        let held = Rc::new(vec![Field::Int64(1)]);
        let function = Closure::bind(
            4,
            |(): &(), a| {
                assert_eq!(a.len(), 4);
                Field::Int64(a[1].int64() * 100 + a[2].int64() * 10 + a[3].int64())
            },
            (),
        );
        let one = function.apply(vec![Field::Tuple(held.clone())]).closure();
        assert_eq!(Rc::strong_count(&held), 2);
        // Supplied arguments are cloned into the next partial application.
        let two = one.apply(vec![Field::Int64(2)]).closure();
        assert_eq!(Rc::strong_count(&held), 3);
        let three = two.apply(vec![Field::Int64(3)]).closure();
        assert_eq!(Rc::strong_count(&held), 4);
        drop(one);
        assert_eq!(Rc::strong_count(&held), 3);
        // Saturating clones them into the call's vector, which the callee drops.
        assert_eq!(three.apply(vec![Field::Int64(4)]).int64(), 234);
        assert_eq!(Rc::strong_count(&held), 3);
        assert_eq!(
            two.apply(vec![Field::Int64(5), Field::Int64(6)]).int64(),
            256
        );
        assert_eq!(Rc::strong_count(&held), 3);
        drop(three);
        drop(two);
        assert_eq!(Rc::strong_count(&held), 1);
    }

    #[test]
    fn too_many_arguments_for_a_partial_application_apply_the_result_to_the_rest() {
        let function = Closure::bind(
            2,
            |(): &(), a| {
                let first = a[0].int64() * 10 + a[1].int64();
                Field::Closure(Closure::ready(2, move |b| {
                    Field::Int64(first * 100 + b[0].int64() * 10 + b[1].int64())
                }))
            },
            (),
        );
        let partial = function.apply(vec![Field::Int64(1)]).closure();
        // Over-applied by one: the call is made with `[1, 2]` and the closure
        // it returns, one argument short, is the result.
        let short = partial
            .apply(vec![Field::Int64(2), Field::Int64(3)])
            .closure();
        assert_eq!(short.apply(vec![Field::Int64(4)]).int64(), 1_234);
        // Over-applied by two: both calls are made.
        assert_eq!(
            partial
                .apply(vec![Field::Int64(2), Field::Int64(3), Field::Int64(4)])
                .int64(),
            1_234
        );
        // And from the closure itself, with nothing supplied yet.
        let all = vec![
            Field::Int64(5),
            Field::Int64(6),
            Field::Int64(7),
            Field::Int64(8),
        ];
        assert_eq!(function.apply(all).int64(), 5_678);
    }

    #[test]
    #[should_panic(expected = "<<loop>>")]
    fn a_closure_that_is_itself_is_a_loop() {
        let cell = Closure::pending();
        cell.fill(cell.clone());
        cell.force();
    }

    #[test]
    #[should_panic(expected = "<<loop>>")]
    fn two_closures_that_are_each_other_are_a_loop() {
        let (a, b) = (Closure::pending(), Closure::pending());
        a.fill(b.clone());
        b.fill(a.clone());
        a.apply(vec![Field::Int64(1)]);
    }

    #[test]
    fn a_deferred_dynamic_value_is_shared_and_read_lazily_at_its_carrier() {
        let n = Rc::new(std::cell::Cell::new(0));
        let count = n.clone();
        let value = Field::defer_to(move || {
            count.set(count.get() + 1);
            Field::Int(Int::ready(7))
        });
        let read = value.int();
        assert_eq!(n.get(), 0);
        assert_eq!(read.force(), 7);
        assert_eq!(value.int().force(), 7);
        assert_eq!(n.get(), 1);
    }

    #[test]
    fn a_pending_dynamic_value_ties_a_knot() {
        let knot = Field::pending();
        let tail = knot.clone();
        knot.fill(Field::Data(Data::defer(move || Node {
            constructor: fixtures::c(":"),
            fields: [Field::Int64(1), tail].into(),
        })));
        let knotted = knot.data();
        let first = knotted.force();
        let rest = first.fields[1].data();
        let second = rest.force();
        assert_eq!(second.fields[0].int64(), 1);
        assert!(first.fields[1].data().shares_with(&knot.data()));
    }
}

impl Data {
    pub fn defer(f: impl FnOnce() -> Node + 'static) -> Self {
        Self(shared(f))
    }
    pub fn defer_to(f: impl FnOnce() -> Self + 'static) -> Self {
        #[cfg(feature = "stats")]
        stats::bump(stats::DEFER_TO + 1);
        Self(Shared::step(move || Thunk::Indirect(f().0)))
    }
    pub fn pending() -> Self {
        Self(Shared::pending())
    }
    pub fn fill(&self, value: Self) {
        self.0.fill(move || Thunk::Indirect(value.0));
    }
    pub fn ready(constructor: &'static Constructor, fields: impl Into<Fields>) -> Self {
        #[cfg(feature = "stats")]
        {
            let fields: Fields = fields.into();
            stats::bump(stats::READY + fields.len().min(4));
            Self(Shared::ready(Node {
                constructor,
                fields,
            }))
        }
        #[cfg(not(feature = "stats"))]
        Self(Shared::ready(Node {
            constructor,
            fields: fields.into(),
        }))
    }
    pub fn force(&self) -> &Node {
        self.0.force()
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    pub fn shares_with(&self, other: &Self) -> bool {
        Shared::ptr_eq(&self.0, &other.0)
    }
}

/// How a Haskell string literal's bytes become characters.
///
/// GHC picks the unpacker when it emits the literal: `unpackCString#` for a
/// string whose characters are all ASCII 1..127, and `unpackCStringUtf8#`
/// otherwise, whose bytes are modified UTF-8 — an embedded NUL is the
/// overlong `C0 80`, which no validating UTF-8 decoder accepts. Both walks
/// stop at the first NUL byte, exactly as `GHC.CString`'s do.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Encoding {
    Latin1,
    Utf8,
}

/// The code point at `at`, and where the next one starts. The compiler already
/// refused a literal these steps could not walk, so a malformed one here is a
/// compiler defect rather than an input error.
fn code_point(bytes: &'static [u8], at: usize, encoding: Encoding) -> (i64, usize) {
    let first = bytes[at];
    if encoding == Encoding::Latin1 {
        return (i64::from(first), at + 1);
    }
    let (width, lead) = match first {
        0x00..=0x7f => (1, u32::from(first)),
        0xc0..=0xdf => (2, u32::from(first) - 0xc0),
        0xe0..=0xef => (3, u32::from(first) - 0xe0),
        _ => (4, u32::from(first) - 0xf0),
    };
    let codepoint = bytes[at + 1..at + width]
        .iter()
        .fold(lead, |acc, byte| (acc << 6) + (u32::from(*byte) - 0x80));
    (i64::from(codepoint), at + width)
}

/// One cell of a literal's `[Char]`, built only when it is demanded. The tail
/// is a thunk over the rest of the bytes, so `head` of a long literal decodes
/// one character and `null` decodes none.
fn unpack_at(
    bytes: &'static [u8],
    at: usize,
    encoding: Encoding,
    names: StringNames,
    tail: Data,
) -> Node {
    if at >= bytes.len() || bytes[at] == 0 {
        return tail.force().clone();
    }
    let (codepoint, next) = code_point(bytes, at, encoding);
    Node {
        constructor: names.cons,
        fields: [
            Field::Data(Data::ready(names.character, [Field::Char(codepoint)])),
            Field::Data(Data::defer(move || {
                unpack_at(bytes, next, encoding, names, tail)
            })),
        ]
        .into(),
    }
}

/// The constructor names the generated code matches these cells against. They
/// come from the compiler's own layout evidence, not from this crate.
#[derive(Clone, Copy)]
pub struct StringNames {
    pub cons: &'static Constructor,
    pub nil: &'static Constructor,
    pub character: &'static Constructor,
}

/// Render a finite Haskell String without forcing anything beyond its spine
/// and characters. This also handles messages assembled at runtime.
pub fn error_message(mut message: Data, names: StringNames) -> Vec<u8> {
    let mut text = Vec::new();
    loop {
        let cell = message.force();
        if cell.constructor == names.nil {
            assert!(cell.fields.is_empty());
            return text;
        }
        assert_eq!(cell.constructor, names.cons);
        assert_eq!(cell.fields.len(), 2);
        let character = cell.fields[0].data();
        let character = character.force();
        assert_eq!(character.constructor, names.character);
        assert_eq!(character.fields.len(), 1);
        // GHC drops surrogates but its UTF-8 encoder otherwise performs
        // unchecked word arithmetic, even for out-of-range chr# values.
        let code = character.fields[0].char_code() as u64;
        match code {
            0..=0x7f => text.push(code as u8),
            0x80..=0x7ff => text.extend([(0xc0 + (code >> 6)) as u8, (0x80 + (code & 0x3f)) as u8]),
            0xd800..=0xdfff => {}
            0x800..=0xffff => text.extend([
                (0xe0 + (code >> 12)) as u8,
                (0x80 + ((code >> 6) & 0x3f)) as u8,
                (0x80 + (code & 0x3f)) as u8,
            ]),
            _ => text.extend([
                (0xf0u64.wrapping_add(code >> 18)) as u8,
                (0x80 + ((code >> 12) & 0x3f)) as u8,
                (0x80 + ((code >> 6) & 0x3f)) as u8,
                (0x80 + (code & 0x3f)) as u8,
            ]),
        }
        message = cell.fields[1].data();
    }
}

/// The generated CLI's uncaught `errorWithoutStackTrace` boundary. Exception
/// catching is not implemented by this adapter.
pub fn raise_error(message: Data, names: StringNames) -> ! {
    report_error(&error_message(message, names))
}

/// The names of base's `CallStack` and `SrcLoc` constructors.
#[derive(Clone, Copy)]
pub struct CallStackNames {
    pub empty: &'static Constructor,
    pub push: &'static Constructor,
    pub freeze: &'static Constructor,
    pub location: &'static Constructor,
}

/// The next `PushCallStack` frame, through any `FreezeCallStack`.
fn next_frame(mut stack: Data, names: CallStackNames) -> Option<Data> {
    loop {
        let node = stack.force();
        if node.constructor == names.push {
            return Some(stack);
        }
        if node.constructor == names.empty {
            return None;
        }
        assert_eq!(node.constructor, names.freeze);
        stack = node.fields[0].data();
    }
}

/// The uncaught `error` boundary: base 4.18's `ErrorCallWithLocation`, shown
/// as its message, then `prettyCallStack` when the stack has a frame. The
/// stack is forced to its first frame before the message, as `showsPrec`'s
/// match on an empty location forces it.
pub fn raise_call_stack_error(
    message: Data,
    stack: Data,
    strings: StringNames,
    names: CallStackNames,
) -> ! {
    report_error(&call_stack_error_message(message, stack, strings, names))
}

fn call_stack_error_message(
    message: Data,
    stack: Data,
    strings: StringNames,
    names: CallStackNames,
) -> Vec<u8> {
    let mut frame = next_frame(stack, names);
    let mut text = error_message(message, strings);
    if frame.is_some() {
        text.extend_from_slice(b"\nCallStack (from HasCallStack):");
    }
    while let Some(pushed) = frame {
        let node = pushed.force();
        text.extend_from_slice(b"\n  ");
        text.extend(error_message(node.fields[0].data(), strings));
        text.extend_from_slice(b", called at ");
        let located = node.fields[1].data();
        let location = located.force();
        assert_eq!(location.constructor, names.location);
        text.extend(error_message(location.fields[2].data(), strings));
        text.push(b':');
        text.extend(location.fields[3].int().force().to_string().bytes());
        text.push(b':');
        text.extend(location.fields[4].int().force().to_string().bytes());
        text.extend_from_slice(b" in ");
        text.extend(error_message(location.fields[0].data(), strings));
        text.push(b':');
        text.extend(error_message(location.fields[1].data(), strings));
        frame = next_frame(node.fields[2].data(), names);
    }
    text
}

fn report_error(message: &[u8]) -> ! {
    use std::io::Write;
    // Match the oracle: a NUL truncates output, not evaluation of the
    // message's remaining tail.
    let message = message
        .split(|byte| *byte == 0)
        .next()
        .expect("one segment");
    let executable = std::env::args_os().next().unwrap_or_default();
    let name = std::path::Path::new(&executable)
        .file_name()
        .unwrap_or_default()
        .to_string_lossy();
    let mut diagnostic = format!("{name}: ").into_bytes();
    diagnostic.extend_from_slice(message);
    diagnostic.push(b'\n');
    match std::io::stderr().lock().write_all(&diagnostic) {
        Ok(()) | Err(_) => std::process::exit(1),
    }
}

/// A string literal as a lazy `[Char]`, appended to `tail`.
pub fn unpack_string(
    bytes: &'static [u8],
    encoding: Encoding,
    names: StringNames,
    tail: Data,
) -> Data {
    Data::defer(move || unpack_at(bytes, 0, encoding, names, tail))
}

/// The names of a list's two cells, from the compiler's layout evidence.
#[derive(Clone, Copy)]
pub struct ListNames {
    pub cons: &'static Constructor,
    pub nil: &'static Constructor,
}

/// `GHC.Base.(++)`: the left spine copied onto the right one, lazily.
///
/// Forcing the result to WHNF forces the left list to WHNF and nothing else,
/// so the right list is never touched until the left runs out, and a cell of
/// the left list is copied only when the corresponding result cell is
/// demanded. The right list is reached, not copied: its cells are shared.
pub fn append_list(left: Data, right: Data, names: ListNames) -> Data {
    Data(Shared::step(move || {
        let node = left.force();
        if node.constructor == names.nil {
            return Thunk::Indirect(right.0);
        }
        let tail = node.fields[1].data();
        Thunk::Value(Node {
            constructor: names.cons,
            fields: [
                node.fields[0].clone(),
                Field::Data(append_list(tail, right, names)),
            ]
            .into(),
        })
    }))
}

/// The carrier of a list element that is computed on demand.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lifted {
    Int,
    Data,
    Closure,
    Dynamic,
}

impl Lifted {
    fn defer(self, compute: impl FnOnce() -> Field + 'static) -> Field {
        match self {
            Self::Int => Field::Int(Int::defer_to(move || compute().int())),
            Self::Data => Field::Data(Data::defer_to(move || compute().data())),
            Self::Closure => Field::Closure(Closure::defer_to(move || compute().closure())),
            Self::Dynamic => Field::defer_to(compute),
        }
    }
}

fn nil(names: ListNames) -> Node {
    Node {
        constructor: names.nil,
        fields: Fields::Zero,
    }
}

/// `GHC.Base.map`: `map f (x:xs) = f x : map f xs`.
pub fn map_list(
    function: Closure,
    list: Data,
    element: Lifted,
    input: ListNames,
    output: ListNames,
) -> Data {
    Data::defer(move || {
        let cell = list.force();
        if cell.constructor == input.nil {
            return nil(output);
        }
        let head = cell.fields[0].clone();
        let applied = function.clone();
        Node {
            constructor: output.cons,
            fields: [
                element.defer(move || applied.apply(vec![head])),
                Field::Data(map_list(
                    function,
                    cell.fields[1].data(),
                    element,
                    input,
                    output,
                )),
            ]
            .into(),
        }
    })
}

/// `GHC.List.filter`: the cells whose element satisfies the predicate.
pub fn filter_list(predicate: Closure, list: Data, names: ListNames, truth: Truth) -> Data {
    Data::defer(move || {
        let mut list = list;
        loop {
            let cell = list.force();
            if cell.constructor == names.nil {
                return nil(names);
            }
            let head = cell.fields[0].clone();
            let tail = cell.fields[1].data();
            if truth.test(&predicate.apply(vec![head.clone()])) {
                return Node {
                    constructor: names.cons,
                    fields: [
                        head,
                        Field::Data(filter_list(predicate, tail, names, truth)),
                    ]
                    .into(),
                };
            }
            list = tail;
        }
    })
}

/// `GHC.List.takeWhile`: the longest prefix whose elements satisfy the predicate.
pub fn take_while(predicate: Closure, list: Data, names: ListNames, truth: Truth) -> Data {
    Data::defer(move || {
        let cell = list.force();
        if cell.constructor == names.nil {
            return nil(names);
        }
        let head = cell.fields[0].clone();
        if !truth.test(&predicate.apply(vec![head.clone()])) {
            return nil(names);
        }
        Node {
            constructor: names.cons,
            fields: [
                head,
                Field::Data(take_while(predicate, cell.fields[1].data(), names, truth)),
            ]
            .into(),
        }
    })
}

/// `GHC.List.dropWhile`: the first cell whose element fails the predicate, itself.
pub fn drop_while(predicate: Closure, list: Data, names: ListNames, truth: Truth) -> Data {
    Data::defer_to(move || {
        let mut list = list;
        loop {
            let cell = list.force();
            if cell.constructor == names.nil
                || !truth.test(&predicate.apply(vec![cell.fields[0].clone()]))
            {
                return list;
            }
            list = cell.fields[1].data();
        }
    })
}

/// `GHC.List.reverse1`, `reverse`'s `rev`: the list's elements pushed onto the accumulator.
pub fn reverse_onto(list: Data, accumulator: Data, names: ListNames) -> Data {
    Data::defer_to(move || {
        let mut list = list;
        let mut accumulator = accumulator;
        loop {
            let cell = list.force();
            if cell.constructor == names.nil {
                return accumulator;
            }
            accumulator = Data::ready(
                names.cons,
                [cell.fields[0].clone(), Field::Data(accumulator)],
            );
            list = cell.fields[1].data();
        }
    })
}

/// `GHC.List.reverse`: `rev l []`.
pub fn reverse_list(list: Data, names: ListNames) -> Data {
    reverse_onto(list, Data::ready(names.nil, Vec::new()), names)
}

/// `GHC.List.$wlenAcc`: the spine's length added to an `Int#` with wrapping addition.
pub fn length_from(list: Data, count: i64, names: ListNames) -> i64 {
    let mut list = list;
    let mut count = count;
    loop {
        let cell = list.force();
        if cell.constructor == names.nil {
            return count;
        }
        count = count.wrapping_add(1);
        list = cell.fields[1].data();
    }
}

/// `GHC.Base.++_$s++`, which base's rule `SC:++0` makes `(x : xs) ++ ys`.
pub fn cons_append(head: Field, tail: Data, right: Data, names: ListNames) -> Data {
    Data::ready(
        names.cons,
        [head, Field::Data(append_list(tail, right, names))],
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Equality {
    Char,
    String,
}

#[derive(Clone, Copy)]
pub struct Truth {
    pub false_: &'static Constructor,
    pub true_: &'static Constructor,
}

impl Truth {
    fn of(self, value: bool) -> Node {
        Node {
            constructor: if value { self.true_ } else { self.false_ },
            fields: Fields::Zero,
        }
    }
    fn test(self, value: &Field) -> bool {
        let data = value.data();
        let node = data.force();
        if node.constructor == self.true_ {
            true
        } else if node.constructor == self.false_ {
            false
        } else {
            panic!("a predicate returned {}, not a Bool", node.constructor)
        }
    }
}

fn character(value: &Data, names: StringNames) -> i64 {
    let node = value.force();
    assert_eq!(node.constructor, names.character);
    node.fields[0].char_code()
}

fn equal(left: &Data, right: &Data, equality: Equality, names: StringNames) -> bool {
    match equality {
        Equality::Char => {
            let left = character(left, names);
            left == character(right, names)
        }
        Equality::String => lists_equal(left.clone(), right.clone(), Equality::Char, names),
    }
}

fn lists_equal(mut left: Data, mut right: Data, element: Equality, names: StringNames) -> bool {
    loop {
        let l = left.force();
        let r = right.force();
        match (l.constructor == names.nil, r.constructor == names.nil) {
            (true, true) => return true,
            (false, false) => {
                if !equal(&l.fields[0].data(), &r.fields[0].data(), element, names) {
                    return false;
                }
                left = l.fields[1].data();
                right = r.fields[1].data();
            }
            _ => return false,
        }
    }
}

/// `GHC.Base.eqString` and `Eq [a]`'s `==`: both spines forced in step, left first.
pub fn equal_lists(
    left: Data,
    right: Data,
    element: Equality,
    names: StringNames,
    truth: Truth,
) -> Data {
    Data::defer(move || truth.of(lists_equal(left, right, element, names)))
}

/// `GHC.List.elem`: `x == y` with the needle on the left, stopping at the first match.
pub fn elem_list(
    needle: Data,
    mut list: Data,
    equality: Equality,
    names: StringNames,
    truth: Truth,
) -> Data {
    Data::defer(move || {
        loop {
            let cell = list.force();
            if cell.constructor == names.nil {
                return truth.of(false);
            }
            if equal(&needle, &cell.fields[0].data(), equality, names) {
                return truth.of(true);
            }
            list = cell.fields[1].data();
        }
    })
}

/// `Data.OldList.isPrefixOf`: the list is not forced once the prefix runs out.
pub fn is_prefix_of(
    mut prefix: Data,
    mut list: Data,
    equality: Equality,
    names: StringNames,
    truth: Truth,
) -> Data {
    Data::defer(move || {
        loop {
            let p = prefix.force();
            if p.constructor == names.nil {
                return truth.of(true);
            }
            let l = list.force();
            if l.constructor == names.nil {
                return truth.of(false);
            }
            if !equal(&p.fields[0].data(), &l.fields[0].data(), equality, names) {
                return truth.of(false);
            }
            prefix = p.fields[1].data();
            list = l.fields[1].data();
        }
    })
}

#[derive(Clone, Copy)]
pub struct Orderings {
    pub lt: &'static Constructor,
    pub eq: &'static Constructor,
    pub gt: &'static Constructor,
}

/// `Ord [a]`'s `compare` over `Ord Char`'s default `compare`, which orders `Char#` as an unsigned word.
pub fn compare_lists(
    mut left: Data,
    mut right: Data,
    names: StringNames,
    order: Orderings,
) -> Data {
    use std::cmp::Ordering;
    Data::defer(move || {
        let ordering = loop {
            let l = left.force();
            let r = right.force();
            match (l.constructor == names.nil, r.constructor == names.nil) {
                (true, true) => break Ordering::Equal,
                (true, false) => break Ordering::Less,
                (false, true) => break Ordering::Greater,
                (false, false) => {
                    let a = character(&l.fields[0].data(), names) as u64;
                    let b = character(&r.fields[0].data(), names) as u64;
                    match a.cmp(&b) {
                        Ordering::Equal => {
                            left = l.fields[1].data();
                            right = r.fields[1].data();
                        }
                        other => break other,
                    }
                }
            }
        };
        Node {
            constructor: match ordering {
                Ordering::Less => order.lt,
                Ordering::Equal => order.eq,
                Ordering::Greater => order.gt,
            },
            fields: Fields::Zero,
        }
    })
}

const ASCII_TAB: [&str; 32] = [
    "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS", "HT", "LF", "VT", "FF", "CR",
    "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM", "SUB", "ESC",
    "FS", "GS", "RS", "US",
];

/// `GHC.Show.showLitChar`, with the following character for `protectEsc`.
fn show_lit_char(out: &mut String, code: i64, next: Option<i64>) {
    let is_digit = |c: Option<i64>| c.is_some_and(|c| (0x30..=0x39).contains(&c));
    match code as u64 {
        0x7f => out.push_str("\\DEL"),
        0x5c => out.push_str("\\\\"),
        0x20..=0x7e => out.push(char::from(code as u8)),
        0x07 => out.push_str("\\a"),
        0x08 => out.push_str("\\b"),
        0x0c => out.push_str("\\f"),
        0x0a => out.push_str("\\n"),
        0x0d => out.push_str("\\r"),
        0x09 => out.push_str("\\t"),
        0x0b => out.push_str("\\v"),
        0x0e => {
            out.push_str("\\SO");
            if next == Some(0x48) {
                out.push_str("\\&");
            }
        }
        0x00..=0x1f => {
            out.push('\\');
            out.push_str(ASCII_TAB[code as usize]);
        }
        wide => {
            out.push('\\');
            out.push_str(&wide.to_string());
            if is_digit(next) {
                out.push_str("\\&");
            }
        }
    }
}

fn characters(value: &Data, names: StringNames) -> Vec<i64> {
    let mut codes = Vec::new();
    let mut cell = value.clone();
    loop {
        let node = cell.force();
        if node.constructor == names.nil {
            return codes;
        }
        codes.push(character(&node.fields[0].data(), names));
        cell = node.fields[1].data();
    }
}

pub fn put_lines(list: Data, names: StringNames, out: &mut impl std::io::Write) -> usize {
    let mut count = 0;
    let mut cell = list;
    loop {
        let node = cell.force();
        if node.constructor == names.nil {
            return count;
        }
        let mut line: String = characters(&node.fields[0].data(), names)
            .into_iter()
            .map(|code| {
                u32::try_from(code)
                    .ok()
                    .and_then(char::from_u32)
                    .expect("a printed Char is a Unicode scalar value")
            })
            .collect();
        line.push('\n');
        out.write_all(line.as_bytes()).expect("writing to stdout");
        count += 1;
        cell = node.fields[1].data();
    }
}

/// `show` at `String`: `showLitString` between double quotes.
pub fn show_string(value: &Data, names: StringNames) -> String {
    let codes = characters(value, names);
    let mut out = String::from("\"");
    for (index, &code) in codes.iter().enumerate() {
        if code == 0x22 {
            out.push_str("\\\"");
        } else {
            show_lit_char(&mut out, code, codes.get(index + 1).copied());
        }
    }
    out.push('"');
    out
}

/// `show` at `Char`.
pub fn show_char(value: &Data, names: StringNames) -> String {
    let code = character(value, names);
    if code == 0x27 {
        return "'\\''".into();
    }
    let mut out = String::from("'");
    show_lit_char(&mut out, code, Some(0x27));
    out.push('\'');
    out
}

/// `showsPrec` at `Int`, which parenthesises a negative number above precedence 6.
pub fn show_int(value: i64, precedence: u8) -> String {
    if value < 0 && precedence > 6 {
        format!("({value})")
    } else {
        value.to_string()
    }
}

/// A command-line argument as a fully evaluated `[Char]`.
pub fn string_argument(text: &str, names: StringNames) -> Data {
    text.chars()
        .rev()
        .fold(Data::ready(names.nil, []), |tail, c| {
            Data::ready(
                names.cons,
                [
                    Field::Data(Data::ready(
                        names.character,
                        [Field::Char(i64::from(u32::from(c)))],
                    )),
                    Field::Data(tail),
                ],
            )
        })
}

pub fn string_value(value: &Data, names: StringNames) -> String {
    characters(value, names)
        .into_iter()
        .map(|code| {
            u32::try_from(code)
                .ok()
                .and_then(char::from_u32)
                .expect("a String crossing to Rust holds Unicode scalar values")
        })
        .collect()
}

pub fn list_argument(elements: Vec<Field>, names: ListNames) -> Data {
    elements
        .into_iter()
        .rev()
        .fold(Data::ready(names.nil, []), |tail, head| {
            Data::ready(names.cons, [head, Field::Data(tail)])
        })
}

pub fn list_fields(list: &Data, names: ListNames) -> Vec<Field> {
    let mut elements = Vec::new();
    let mut cell = list.clone();
    loop {
        let node = cell.force();
        if node.constructor == names.nil {
            return elements;
        }
        assert_eq!(node.constructor, names.cons);
        elements.push(node.fields[0].clone());
        cell = node.fields[1].data();
    }
}

pub fn on_program_stack<R: Send + 'static>(run: impl FnOnce() -> R + Send + 'static) -> R {
    let memory = std::fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|text| {
            text.lines()
                .find_map(|line| line.strip_prefix("MemTotal:"))
                .and_then(|kib| kib.trim().trim_end_matches("kB").trim().parse::<u64>().ok())
        })
        .map_or(1 << 30, |kib| kib / 5 * 4 * 1024);
    let run = std::sync::Arc::new(std::sync::Mutex::new(Some(run)));
    let mut size = memory;
    loop {
        let task = run.clone();
        let started = std::thread::Builder::new()
            .stack_size(usize::try_from(size).unwrap_or(usize::MAX))
            .spawn(move || {
                let run = task
                    .lock()
                    .expect("program lock")
                    .take()
                    .expect("program runs once");
                #[cfg(feature = "stats")]
                {
                    let value = run();
                    stats::flush();
                    value
                }
                #[cfg(not(feature = "stats"))]
                run()
            });
        match started {
            Ok(thread) => {
                let value = match thread.join() {
                    Ok(value) => value,
                    Err(panic) => std::panic::resume_unwind(panic),
                };
                #[cfg(feature = "stats")]
                stats::print_report();
                return value;
            }
            Err(_) if size > 64 << 20 => size /= 2,
            Err(error) => panic!("cannot start the program's thread: {error}"),
        }
    }
}

#[cfg(test)]
mod append_tests {
    use super::*;

    const NAMES: ListNames = ListNames {
        cons: fixtures::CONS,
        nil: fixtures::NIL,
    };

    fn ints(values: &[i64]) -> Data {
        values
            .iter()
            .rev()
            .fold(Data::ready(NAMES.nil, []), |tail, value| {
                Data::ready(NAMES.cons, [Field::Int64(*value), Field::Data(tail)])
            })
    }

    fn collect(list: &Data) -> Vec<i64> {
        let mut out = Vec::new();
        let mut current = list.clone();
        loop {
            let node = current.force();
            if node.constructor == NAMES.nil {
                return out;
            }
            out.push(node.fields[0].int64());
            current = node.fields[1].data();
        }
    }

    #[test]
    fn error_messages_preserve_empty_unicode_nul_and_newlines() {
        const NAMES: StringNames = StringNames {
            cons: fixtures::CONS,
            nil: fixtures::NIL,
            character: fixtures::CHAR,
        };
        for (bytes, expected) in [
            (&b"\0"[..], ""),
            ("fout: λ 🐚\0".as_bytes(), "fout: λ 🐚"),
            (&b"a\xc0\x80b\n\0"[..], "a\0b\n"),
        ] {
            assert_eq!(
                error_message(unpack_literal(bytes, Encoding::Utf8, NAMES), NAMES),
                expected.as_bytes()
            );
        }
    }

    #[test]
    fn error_messages_force_computed_spines_and_characters_once() {
        const NAMES: StringNames = StringNames {
            cons: fixtures::CONS,
            nil: fixtures::NIL,
            character: fixtures::CHAR,
        };
        use std::cell::Cell;
        let forced = Rc::new(Cell::new(0));
        let count = forced.clone();
        let character = Data::defer(move || {
            count.set(count.get() + 1);
            Node {
                constructor: NAMES.character,
                fields: [Field::Char(0x3bb)].into(),
            }
        });
        let message = Data::ready(
            NAMES.cons,
            [
                Field::Data(character),
                Field::Data(Data::ready(NAMES.nil, [])),
            ],
        );
        assert_eq!(forced.get(), 0);
        assert_eq!(error_message(message.clone(), NAMES), "λ".as_bytes());
        assert_eq!(error_message(message, NAMES), "λ".as_bytes());
        assert_eq!(forced.get(), 1);
    }

    fn untouchable() -> Data {
        Data::defer(|| panic!("a lazily passed value was forced"))
    }

    const STACK: CallStackNames = CallStackNames {
        empty: fixtures::EMPTY_STACK,
        push: fixtures::PUSH_STACK,
        freeze: fixtures::FREEZE_STACK,
        location: fixtures::SRC_LOC,
    };

    fn located(file: &str, line: i64, column: i64) -> Data {
        let nil = || Data::ready(fixtures::c("[]"), []);
        Data::ready(
            STACK.location,
            vec![
                Field::Data(string("pkg-1", nil())),
                Field::Data(string("M.N", nil())),
                Field::Data(string(file, nil())),
                Field::Int(Int::ready(line)),
                Field::Int(Int::ready(column)),
                Field::Int(Int::defer(|| panic!("the end line was forced"))),
                Field::Int(Int::defer(|| panic!("the end column was forced"))),
            ],
        )
    }

    fn pushed(function: &str, location: Data, rest: Data) -> Data {
        Data::ready(
            STACK.push,
            [
                Field::Data(string(function, Data::ready(fixtures::c("[]"), []))),
                Field::Data(location),
                Field::Data(rest),
            ],
        )
    }

    #[test]
    fn error_messages_render_the_call_stack_as_base_shows_it() {
        let nil = || Data::ready(fixtures::c("[]"), []);
        let empty = || Data::ready(STACK.empty, []);
        let stack = Data::ready(
            STACK.freeze,
            [Field::Data(pushed(
                "error",
                located("src/M.hs", 12, 5),
                pushed("helper", located("src/N.hs", -3, 0), empty()),
            ))],
        );
        assert_eq!(
            call_stack_error_message(string("boom", nil()), stack, STRING, STACK),
            b"boom\nCallStack (from HasCallStack):\n  error, called at src/M.hs:12:5 in pkg-1:M.N\n  helper, called at src/N.hs:-3:0 in pkg-1:M.N"
        );
        assert_eq!(
            call_stack_error_message(string("plain", nil()), empty(), STRING, STACK),
            b"plain"
        );
        let frozen_empty = Data::ready(STACK.freeze, [Field::Data(empty())]);
        assert_eq!(
            call_stack_error_message(string("", nil()), frozen_empty, STRING, STACK),
            b""
        );
    }

    #[test]
    fn the_stack_is_forced_before_the_message() {
        let stack = Data::defer(|| panic!("stack forced first"));
        let message = Data::defer(|| panic!("message forced first"));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            call_stack_error_message(message, stack, STRING, STACK)
        }));
        let payload = outcome.expect_err("both panic");
        assert_eq!(panic_text(&*payload), "stack forced first");
    }

    fn panic_text(payload: &(dyn std::any::Any + Send)) -> String {
        payload
            .downcast_ref::<&str>()
            .map(|text| (*text).to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_default()
    }

    fn positive(calls: Rc<std::cell::Cell<u32>>) -> Closure {
        Closure::ready(1, move |a| {
            calls.set(calls.get() + 1);
            Field::Data(Data::ready(
                if a[0].int64() > 0 {
                    fixtures::TRUE
                } else {
                    fixtures::FALSE
                },
                [],
            ))
        })
    }

    fn cells(values: &[i64], tail: Data) -> Data {
        values.iter().rev().fold(tail, |tail, value| {
            Data::ready(NAMES.cons, [Field::Int64(*value), Field::Data(tail)])
        })
    }

    #[test]
    fn map_applies_once_per_demanded_element_and_builds_cells_on_demand() {
        let calls = Rc::new(std::cell::Cell::new(0));
        let count = calls.clone();
        let double = Closure::ready(1, move |a| {
            count.set(count.get() + 1);
            Field::Int(Int::ready(2 * a[0].int64()))
        });
        let mapped = map_list(
            double,
            cells(&[1, 2], untouchable()),
            Lifted::Int,
            NAMES,
            NAMES,
        );
        let first = mapped.force();
        assert_eq!(calls.get(), 0);
        let rest = first.fields[1].data();
        let second = rest.force();
        assert_eq!(second.fields[0].int().force(), 4);
        assert_eq!(second.fields[0].int().force(), 4);
        assert_eq!(calls.get(), 1);
        assert_eq!(first.fields[0].int().force(), 2);
        assert_eq!(calls.get(), 2);
        assert!(!second.fields[1].data().is_evaluated());
        let empty = map_list(
            Closure::ready(1, |_| panic!("map applied its function to nothing")),
            ints(&[]),
            Lifted::Int,
            NAMES,
            NAMES,
        );
        assert_eq!(empty.force().constructor, NAMES.nil);
    }

    #[test]
    fn filter_skips_failures_inside_one_cell_and_leaves_the_rest_unforced() {
        let calls = Rc::new(std::cell::Cell::new(0));
        let kept = filter_list(
            positive(calls.clone()),
            cells(&[0, -1, 3, 0, 5], untouchable()),
            NAMES,
            TRUTH,
        );
        let first = kept.force();
        assert_eq!(first.fields[0].int64(), 3);
        assert_eq!(calls.get(), 3);
        let rest = first.fields[1].data();
        let second = rest.force();
        assert_eq!(second.fields[0].int64(), 5);
        assert_eq!(calls.get(), 5);
        assert_eq!(
            collect(&filter_list(positive(calls), ints(&[-2, 0]), NAMES, TRUTH)),
            Vec::<i64>::new()
        );
    }

    #[test]
    fn take_while_stops_at_the_first_failure_without_reaching_the_tail() {
        let calls = Rc::new(std::cell::Cell::new(0));
        let taken = take_while(
            positive(calls.clone()),
            cells(&[1, 2, 0], untouchable()),
            NAMES,
            TRUTH,
        );
        assert_eq!(collect(&taken), vec![1, 2]);
        assert_eq!(calls.get(), 3);
        assert_eq!(
            collect(&take_while(positive(calls), ints(&[]), NAMES, TRUTH)),
            Vec::<i64>::new()
        );
    }

    #[test]
    fn drop_while_returns_the_first_failing_cell_itself() {
        let calls = Rc::new(std::cell::Cell::new(0));
        let rest = cells(&[0, 7], untouchable());
        let list = cells(&[1, 2], rest.clone());
        let dropped = drop_while(positive(calls.clone()), list, NAMES, TRUTH);
        let node = dropped.force();
        assert_eq!(calls.get(), 3);
        assert_eq!(node.fields[0].int64(), 0);
        assert!(
            node.fields[1]
                .data()
                .shares_with(&rest.force().fields[1].data())
        );
        assert_eq!(
            drop_while(positive(calls), ints(&[3]), NAMES, TRUTH)
                .force()
                .constructor,
            NAMES.nil
        );
    }

    #[test]
    fn reverse_forces_the_spine_but_neither_elements_nor_accumulator_until_the_end() {
        let element = Field::Int(Int::defer(|| panic!("reverse forced an element")));
        let list = Data::ready(
            NAMES.cons,
            [element, Field::Data(cells(&[2, 3], ints(&[])))],
        );
        let reversed = reverse_list(list, NAMES);
        let node = reversed.force();
        assert_eq!(node.fields[0].int64(), 3);
        let accumulated = reverse_onto(ints(&[1, 2]), ints(&[9]), NAMES);
        assert_eq!(collect(&accumulated), vec![2, 1, 9]);
        let lazy = reverse_onto(ints(&[]), untouchable(), NAMES);
        assert!(!lazy.is_evaluated());
        assert_eq!(collect(&reverse_list(ints(&[]), NAMES)), Vec::<i64>::new());
    }

    #[test]
    fn length_counts_the_spine_onto_its_start_and_wraps() {
        let element = Field::Int(Int::defer(|| panic!("length forced an element")));
        let list = Data::ready(NAMES.cons, [element, Field::Data(ints(&[5]))]);
        assert_eq!(length_from(list, 10, NAMES), 12);
        assert_eq!(length_from(ints(&[]), -4, NAMES), -4);
        assert_eq!(length_from(ints(&[1, 2]), i64::MAX, NAMES), i64::MIN + 1);
    }

    #[test]
    fn cons_append_builds_one_cell_and_leaves_everything_else_lazy() {
        let appended = cons_append(
            Field::Int(Int::defer(|| panic!("the head was forced"))),
            untouchable(),
            untouchable(),
            NAMES,
        );
        assert!(appended.is_evaluated());
        assert!(!appended.force().fields[1].data().is_evaluated());
        let whole = cons_append(Field::Int64(1), ints(&[2]), ints(&[3]), NAMES);
        assert_eq!(collect(&whole), vec![1, 2, 3]);
    }

    fn string(text: &str, tail: Data) -> Data {
        text.chars().rev().fold(tail, |tail, c| {
            Data::ready(
                fixtures::c(":"),
                [
                    Field::Data(Data::ready(fixtures::c("C#"), [Field::Char(c as i64)])),
                    Field::Data(tail),
                ],
            )
        })
    }

    fn holds(value: Data) -> bool {
        match value.force().constructor.name {
            "True" => true,
            "False" => false,
            other => panic!("not a Bool: {other}"),
        }
    }

    const STRING: StringNames = StringNames {
        cons: fixtures::CONS,
        nil: fixtures::NIL,
        character: fixtures::CHAR,
    };
    const TRUTH: Truth = Truth {
        false_: fixtures::FALSE,
        true_: fixtures::TRUE,
    };

    #[test]
    fn strings_and_characters_show_as_ghc_shows_them() {
        let nil = || Data::ready(fixtures::c("[]"), []);
        for (text, shown) in [
            ("", "\"\""),
            ("a\"b\\c", "\"a\\\"b\\\\c\""),
            ("\u{e9}1", "\"\\233\\&1\""),
            ("\u{e9}x", "\"\\233x\""),
            ("\u{e}H\u{e}I", "\"\\SO\\&H\\SOI\""),
            ("\n\t\u{7f}\u{0}\u{1b}", "\"\\n\\t\\DEL\\NUL\\ESC\""),
            ("🐚", "\"\\128026\""),
        ] {
            assert_eq!(show_string(&string(text, nil()), STRING), shown, "{text:?}");
        }
        let char_of = |text: &str| string(text, nil()).force().fields[0].data();
        assert_eq!(show_char(&char_of("'"), STRING), "'\\''");
        assert_eq!(show_char(&char_of("\""), STRING), "'\"'");
        assert_eq!(show_char(&char_of("\u{e9}"), STRING), "'\\233'");
        assert_eq!(show_int(-3, 11), "(-3)");
        assert_eq!(show_int(-3, 6), "-3");
        assert_eq!(
            show_string(&string_argument("λ x", STRING), STRING),
            "\"\\955 x\""
        );
    }

    #[test]
    fn values_cross_between_rust_and_haskell_unchanged() {
        let names = ListNames {
            cons: STRING.cons,
            nil: STRING.nil,
        };
        let text = "a\tλ🐚";
        assert_eq!(string_value(&string_argument(text, STRING), STRING), text);
        assert_eq!(string_value(&Data::ready(STRING.nil, []), STRING), "");
        let list = list_argument(vec![Field::Int64(3), Field::Int64(-1)], names);
        let read: Vec<i64> = list_fields(&list, names).iter().map(Field::int64).collect();
        assert_eq!(read, [3, -1]);
        assert!(list_fields(&list_argument(Vec::new(), names), names).is_empty());
        assert_eq!(on_program_stack(|| 6 * 7), 42);
    }

    #[test]
    fn put_lines_writes_each_string_and_counts_them() {
        let cons = |head: &str, tail: Data| {
            Data::ready(
                STRING.cons,
                [
                    Field::Data(string_argument(head, STRING)),
                    Field::Data(tail),
                ],
            )
        };
        let list = cons("a.sh:1:1: note: x", cons("λ", Data::ready(STRING.nil, [])));
        let mut out = Vec::new();
        assert_eq!(put_lines(list, STRING, &mut out), 2);
        assert_eq!(String::from_utf8(out).unwrap(), "a.sh:1:1: note: x\nλ\n");
        let mut empty = Vec::new();
        assert_eq!(
            put_lines(Data::ready(STRING.nil, []), STRING, &mut empty),
            0
        );
        assert!(empty.is_empty());
    }

    #[test]
    fn string_comparison_is_unsigned_and_stops_at_the_first_difference() {
        const ORDER: Orderings = Orderings {
            lt: fixtures::LT,
            eq: fixtures::EQ,
            gt: fixtures::GT,
        };
        let nil = || Data::ready(fixtures::c("[]"), []);
        let order = |left, right| {
            compare_lists(left, right, STRING, ORDER)
                .force()
                .constructor
                .name
        };
        let negative = Data::ready(
            fixtures::c(":"),
            [
                Field::Data(Data::ready(fixtures::c("C#"), [Field::Char(-1)])),
                Field::Data(nil()),
            ],
        );
        assert_eq!(order(negative, string("🐚", nil())), "GT");
        assert_eq!(
            order(string("ab", untouchable()), string("ac", untouchable())),
            "LT"
        );
        assert_eq!(order(string("", nil()), string("a", untouchable())), "LT");
        assert_eq!(order(string("λ", nil()), string("λ", nil())), "EQ");
    }

    #[test]
    fn list_predicates_stop_where_the_library_definitions_stop() {
        let nil = || Data::ready(fixtures::c("[]"), []);
        assert!(!holds(equal_lists(
            string("λa", untouchable()),
            string("λb", untouchable()),
            Equality::Char,
            STRING,
            TRUTH
        )));
        assert!(holds(equal_lists(
            string("", nil()),
            string("", nil()),
            Equality::Char,
            STRING,
            TRUTH
        )));
        assert!(holds(elem_list(
            string("🐚", nil()).force().fields[0].data(),
            string("a🐚", untouchable()),
            Equality::Char,
            STRING,
            TRUTH
        )));
        assert!(!holds(elem_list(
            untouchable(),
            nil(),
            Equality::Char,
            STRING,
            TRUTH
        )));
        assert!(holds(is_prefix_of(
            nil(),
            untouchable(),
            Equality::Char,
            STRING,
            TRUTH
        )));
        assert!(!holds(is_prefix_of(
            string("ab", untouchable()),
            string("ac", untouchable()),
            Equality::Char,
            STRING,
            TRUTH
        )));
        let words = Data::ready(
            fixtures::c(":"),
            [Field::Data(string("ab", nil())), Field::Data(untouchable())],
        );
        assert!(holds(elem_list(
            string("ab", nil()),
            words,
            Equality::String,
            STRING,
            TRUTH
        )));
    }

    #[test]
    fn error_diagnostics_match_unchecked_ghc_encoding_and_drop_surrogates() {
        let names = StringNames {
            cons: fixtures::CONS,
            nil: fixtures::NIL,
            character: fixtures::CHAR,
        };
        for (code, expected) in [
            (-1, &b"\xef\xbf\xbf\xbf"[..]),
            (0xd800, &b""[..]),
            (0x110000, &b"\xf4\x90\x80\x80"[..]),
        ] {
            let character = Data::ready(names.character, [Field::Char(code)]);
            let message = Data::ready(
                names.cons,
                [
                    Field::Data(character),
                    Field::Data(Data::ready(names.nil, [])),
                ],
            );
            assert_eq!(error_message(message, names), expected);
        }
    }

    #[test]
    fn appending_joins_both_spines_in_order() {
        assert_eq!(
            collect(&append_list(ints(&[1, 2]), ints(&[3]), NAMES)),
            vec![1, 2, 3]
        );
        assert_eq!(
            collect(&append_list(ints(&[]), ints(&[3, 4]), NAMES)),
            vec![3, 4]
        );
        assert_eq!(collect(&append_list(ints(&[]), ints(&[]), NAMES)), vec![]);
    }

    #[test]
    fn neither_argument_is_forced_before_the_result_is() {
        let left = Data::defer(|| panic!("append forced its left argument"));
        let right = Data::defer(|| panic!("append forced its right argument"));
        let joined = append_list(left, right, NAMES);
        assert!(!joined.is_evaluated());
    }

    #[test]
    fn the_right_list_is_reached_rather_than_copied() {
        let forced = std::rc::Rc::new(std::cell::Cell::new(0));
        let counter = forced.clone();
        let right = Data::defer(move || {
            counter.set(counter.get() + 1);
            ints(&[9]).force().clone()
        });
        let joined = append_list(ints(&[1]), right.clone(), NAMES);
        let first = joined.force();
        // One cell demanded: the right list has not been looked at yet.
        assert_eq!(forced.get(), 0);
        assert_eq!(first.fields[0].int64(), 1);
        // Reaching the end enters the right list once, and its cells are the
        // ones it already had rather than copies.
        let tail = first.fields[1].data();
        let rest = tail.force();
        assert_eq!(rest.fields[0].int64(), 9);
        assert_eq!(forced.get(), 1);
        assert!(right.is_evaluated());
    }

    #[test]
    fn a_lazy_element_survives_the_copy_unforced() {
        let element = Int::defer(|| panic!("append forced an element"));
        let left = Data::ready(
            NAMES.cons,
            [
                Field::Int(element.clone()),
                Field::Data(Data::ready(NAMES.nil, [])),
            ],
        );
        let joined = append_list(left, Data::ready(NAMES.nil, []), NAMES);
        let node = joined.force();
        assert!(node.fields[0].int().shares_with(&element));
        assert!(!element.is_evaluated());
    }
}

/// A string literal as a lazy `[Char]` ending in `[]`.
pub fn unpack_literal(bytes: &'static [u8], encoding: Encoding, names: StringNames) -> Data {
    unpack_string(bytes, encoding, names, Data::ready(names.nil, []))
}

#[cfg(test)]
mod string_tests {
    use super::*;

    const NAMES: StringNames = StringNames {
        cons: fixtures::CONS,
        nil: fixtures::NIL,
        character: fixtures::CHAR,
    };

    fn collect(list: &Data) -> Vec<i64> {
        let mut out = Vec::new();
        let mut current = list.clone();
        loop {
            let node = current.force();
            if node.constructor == NAMES.nil {
                return out;
            }
            out.push(node.fields[0].data().force().fields[0].char_code());
            current = node.fields[1].data();
        }
    }

    #[test]
    fn a_literal_decodes_to_its_own_code_points() {
        assert_eq!(
            collect(&unpack_literal(b"hi\0", Encoding::Latin1, NAMES)),
            vec![104, 105]
        );
        assert_eq!(
            collect(&unpack_literal("é€\0".as_bytes(), Encoding::Utf8, NAMES)),
            vec![0xe9, 0x20ac]
        );
        // GHC's overlong NUL, which a validating decoder would reject.
        assert_eq!(
            collect(&unpack_literal(b"a\xc0\x80b\0", Encoding::Utf8, NAMES)),
            vec![0x61, 0x00, 0x62]
        );
        assert!(collect(&unpack_literal(b"\0", Encoding::Latin1, NAMES)).is_empty());
    }

    #[test]
    fn only_the_demanded_prefix_is_decoded_and_the_tail_is_not_forced() {
        let poison = Data::defer(|| panic!("an undemanded string tail was forced"));
        let list = unpack_string(b"abc\0", Encoding::Latin1, NAMES, poison);
        let first = list.force();
        assert_eq!(
            first.fields[0].data().force().fields[0].char_code(),
            i64::from(b'a')
        );
        // The rest of the literal is still a thunk.
        assert!(!first.fields[1].data().is_evaluated());
    }

    #[test]
    fn an_appended_tail_continues_the_list_once_the_literal_runs_out() {
        let tail = unpack_literal(b"de\0", Encoding::Latin1, NAMES);
        let joined = unpack_string(b"abc\0", Encoding::Latin1, NAMES, tail);
        assert_eq!(collect(&joined), vec![97, 98, 99, 100, 101]);
        // An empty literal is its tail, with no cell of its own.
        let tail = unpack_literal(b"xy\0", Encoding::Latin1, NAMES);
        assert_eq!(
            collect(&unpack_string(b"\0", Encoding::Latin1, NAMES, tail)),
            vec![120, 121]
        );
    }

    #[test]
    fn forcing_one_cell_twice_decodes_it_once() {
        let list = unpack_literal(b"ab\0", Encoding::Latin1, NAMES);
        let node = list.force();
        let tail = node.fields[1].data();
        assert!(!tail.is_evaluated());
        tail.force();
        assert!(tail.is_evaluated());
        assert!(list.force().fields[1].data().shares_with(&tail));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn algebraic_tag_demand_preserves_lazy_fields_and_shared_identity() {
        let field = Int::defer(|| panic!("tag inspection forced a lazy field"));
        let retained = field.clone();
        let data = Data::defer(move || Node {
            constructor: fixtures::c("Pair"),
            fields: [Field::Int(field)].into(),
        });
        let copy = data.clone();
        assert!(data.shares_with(&copy));
        assert!(!copy.is_evaluated());
        let node = copy.force();
        assert_eq!(node.constructor.name, "Pair");
        assert!(data.is_evaluated());
        assert!(!retained.is_evaluated());
        assert!(node.fields[0].int().shares_with(&retained));
    }

    #[test]
    fn recursive_datatype_carriers_hold_finite_nested_values() {
        let tail = Data::ready(fixtures::c("Nil"), []);
        let list = Data::ready(
            fixtures::c("Cons"),
            [Field::Int64(42), Field::Data(tail.clone())],
        );
        let node = list.force();
        assert_eq!(node.fields[0].int64(), 42);
        assert!(node.fields[1].data().shares_with(&tail));
        assert_eq!(node.fields[1].data().force().constructor.name, "Nil");
    }

    #[test]
    fn evaluates_at_most_once() {
        thread_local! { static CALLS: Cell<u32> = const { Cell::new(0) }; }
        let l = Lazy::new(|| {
            CALLS.with(|c| c.set(c.get() + 1));
            41 + 1
        });
        assert!(!l.is_evaluated());
        assert_eq!(*l.force(), 42);
        assert_eq!(*l.force(), 42);
        assert!(l.is_evaluated());
        CALLS.with(|c| assert_eq!(c.get(), 1));
    }

    #[test]
    fn unforced_thunk_never_runs() {
        thread_local! { static CALLS: Cell<u32> = const { Cell::new(0) }; }
        let _l = Lazy::new(|| {
            CALLS.with(|c| c.set(c.get() + 1));
            0
        });
        CALLS.with(|c| assert_eq!(c.get(), 0));
    }

    #[test]
    fn ready_skips_the_closure() {
        let l = Lazy::ready(7);
        assert!(l.is_evaluated());
        assert_eq!(*l.force(), 7);
    }

    #[test]
    fn shared_thunks_share_the_result() {
        let a = shared(|| vec![1, 2, 3]);
        let b = a.clone();
        assert_eq!(a.force().len(), 3);
        assert!(b.is_evaluated());
    }

    fn countdown(n: u32, entered: Rc<Cell<u32>>) -> Data {
        if n == 0 {
            return Data::ready(fixtures::c("Nil"), []);
        }
        Data::defer_to(move || {
            entered.set(entered.get() + 1);
            countdown(n - 1, entered)
        })
    }

    #[test]
    fn a_million_indirections_force_in_constant_stack() {
        let entered = Rc::new(Cell::new(0));
        let chain = countdown(1_000_000, entered.clone());
        assert_eq!(chain.force().constructor.name, "Nil");
        assert_eq!(entered.get(), 1_000_000);
        assert_eq!(chain.force().constructor.name, "Nil");
        assert_eq!(entered.get(), 1_000_000);
    }

    #[test]
    fn a_shared_link_in_a_chain_is_memoised() {
        let entered = Rc::new(Cell::new(0));
        let middle = countdown(3, entered.clone());
        let held = middle.clone();
        let top = Data::defer_to(move || middle);
        assert_eq!(top.force().constructor.name, "Nil");
        assert!(held.is_evaluated());
        assert_eq!(held.force().constructor.name, "Nil");
        assert_eq!(entered.get(), 3);
    }

    #[test]
    #[should_panic(expected = "<<loop>>")]
    fn an_indirection_to_itself_is_a_loop() {
        let cell: Rc<RefCell<Option<Data>>> = Rc::new(RefCell::new(None));
        let reference = cell.clone();
        let this = Data::defer_to(move || reference.borrow().clone().expect("tied"));
        *cell.borrow_mut() = Some(this.clone());
        this.force();
    }

    #[test]
    fn a_saturated_tail_call_enters_and_a_partial_one_applies() {
        let function = Closure::entering(
            2,
            |a| Field::Int64(a[0].int64() + a[1].int64()),
            |a| {
                let (x, y) = (a[0].int64(), a[1].int64());
                Step::Next(Box::new(move || Step::Done(x * 100 + y)))
            },
        );
        match function.apply_tail(vec![Field::Int64(4), Field::Int64(2)]) {
            Tail::Enter(step) => assert_eq!(step.run(), 402),
            Tail::Value(_) => panic!("a saturated call with an entry was applied"),
        }
        let partial = function.apply(vec![Field::Int64(4)]).closure();
        match partial.apply_tail(vec![Field::Int64(2)]) {
            Tail::Enter(step) => assert_eq!(step.run(), 402),
            Tail::Value(_) => panic!("a partial application lost its entry"),
        }
        match function.apply_tail(vec![Field::Int64(4)]) {
            Tail::Value(value) => {
                assert_eq!(value.closure().apply(vec![Field::Int64(2)]).int64(), 6)
            }
            Tail::Enter(_) => panic!("an unsaturated call entered"),
        }
        match Closure::ready(1, |a| a[0].clone()).apply_tail(vec![Field::Int64(7)]) {
            Tail::Value(value) => assert_eq!(value.int64(), 7),
            Tail::Enter(_) => panic!("a closure without an entry entered"),
        }
    }

    #[test]
    fn boxed_int_clones_share_one_delayed_evaluation() {
        let calls = Rc::new(Cell::new(0));
        let counter = calls.clone();
        let value = Int::defer(move || {
            counter.set(counter.get() + 1);
            42
        });
        let alias = value.clone();
        assert!(value.shares_with(&alias));
        assert!(!alias.is_evaluated());
        assert_eq!(alias.force(), 42);
        assert_eq!(value.force(), 42);
        assert_eq!(calls.get(), 1);
        assert!(value.is_evaluated());
        assert!(Int::ready(7).is_evaluated());
    }
}

#[cfg(test)]
mod fields_drop_tests {
    use super::*;

    fn leaf() -> Data {
        Data::ready(fixtures::c("Nil"), [])
    }

    /// Fields of one owner each, `n` of them, all counting on `leaf`.
    fn owners(leaf: &Data, n: usize) -> Vec<Field> {
        (0..n).map(|_| Field::Data(leaf.clone())).collect()
    }

    #[test]
    fn dropping_a_node_drops_every_field_once_for_every_arity() {
        for n in 0..=6 {
            let leaf = leaf();
            let node = Data::ready(fixtures::c("Cons"), owners(&leaf, n));
            assert_eq!(node.force().fields.len(), n);
            assert_eq!(leaf.0.strong_count(), 1 + n, "{n} fields held");
            drop(node);
            assert_eq!(leaf.0.strong_count(), 1, "{n} fields dropped");
        }
    }

    #[test]
    fn a_head_that_owns_nothing_leaves_the_tail_to_be_dropped() {
        let leaf = leaf();
        for head in [Field::Int64(1), Field::Char(97)] {
            let node = Data::ready(fixtures::c(":"), [head, Field::Data(leaf.clone())]);
            assert_eq!(leaf.0.strong_count(), 2);
            drop(node);
            assert_eq!(leaf.0.strong_count(), 1);
        }
    }

    #[test]
    fn a_head_that_owns_something_is_dropped_with_the_tail_in_either_position() {
        let leaf = leaf();
        let int = Int::ready(5);
        let node = Data::ready(
            fixtures::c("Pair"),
            [Field::Int(int.clone()), Field::Data(leaf.clone())],
        );
        assert_eq!((leaf.0.strong_count(), int.0.strong_count()), (2, 2));
        drop(node);
        assert_eq!((leaf.0.strong_count(), int.0.strong_count()), (1, 1));
        let node = Data::ready(
            fixtures::c("Pair"),
            [Field::Data(leaf.clone()), Field::Int(int.clone())],
        );
        assert_eq!((leaf.0.strong_count(), int.0.strong_count()), (2, 2));
        drop(node);
        assert_eq!((leaf.0.strong_count(), int.0.strong_count()), (1, 1));
    }

    #[test]
    fn every_kind_of_field_is_released_in_one_two_three_and_many_field_nodes() {
        let leaf = leaf();
        let int = Int::ready(5);
        let deferred = Field::defer_to(|| Field::Int64(3));
        let closure = Closure::ready(1, |arguments| arguments[0].clone());
        let kinds = |k: usize| match k {
            0 => Field::Data(leaf.clone()),
            1 => Field::Int(int.clone()),
            2 => deferred.clone(),
            3 => Field::Closure(closure.clone()),
            4 => Field::Int64(7),
            _ => Field::Char(8),
        };
        for n in 1..=5 {
            for first in 0..6 {
                let fields: Vec<Field> = (0..n).map(|i| kinds((first + i) % 6)).collect();
                drop(Data::ready(fixtures::c("Cons"), fields));
            }
        }
        assert_eq!(leaf.0.strong_count(), 1);
        assert_eq!(int.0.strong_count(), 1);
        let Field::Deferred(cell) = &deferred else {
            unreachable!()
        };
        assert_eq!(cell.strong_count(), 1);
    }

    #[test]
    fn a_long_list_still_drops() {
        let mut list = leaf();
        for c in 0..5_000 {
            list = Data::ready(fixtures::c(":"), [Field::Char(c), Field::Data(list)]);
        }
        drop(list);
    }
}

#[cfg(all(test, feature = "stats"))]
mod stats_tests {
    use super::*;

    const INT: usize = 0;
    const DATA: usize = 1;

    fn double(n: i64) -> Int {
        Int::ready(n * 2)
    }

    fn through(n: i64) -> Int {
        delay1(double, (n,))
    }

    /// The counters of this thread (each test runs on a thread of its own)
    /// as they stood when the test began.
    struct Delta(Vec<u64>);

    impl Delta {
        fn start() -> Self {
            Self(stats::snapshot())
        }
        fn of(&self, index: usize) -> u64 {
            stats::get(index) - self.0[index]
        }
    }

    #[test]
    fn one_delay1_thunk_counts_as_made_and_forced() {
        let delta = Delta::start();
        let thunk = delay1(double, (21,));
        assert_eq!(delta.of(stats::DELAY + 1), 1);
        assert_eq!(delta.of(stats::DEFER_TO + INT), 1);
        assert_eq!(delta.of(stats::CREATED + INT), 1);
        assert_eq!(thunk.force(), 42);
        assert_eq!(delta.of(stats::FORCED_UNIQUE + INT), 1);
        assert_eq!(delta.of(stats::FORCED_SHARED + INT), 0);
        // The entry made a ready cell, which the force then took the value out of.
        assert_eq!(delta.of(stats::EVALUATED + INT), 1);
        assert_eq!(delta.of(stats::MOVED_UNIQUE + INT), 1);
        drop(thunk);
        assert_eq!(delta.of(stats::DROPPED_UNFORCED + INT), 0);
        let others: u64 = (0..17)
            .filter(|&n| n != 1)
            .map(|n| delta.of(stats::DELAY + n))
            .sum();
        assert_eq!(others, 0);
        assert_eq!(delta.of(stats::CREATED + DATA), 0);
    }

    #[test]
    fn a_thunk_dropped_unforced_is_counted() {
        let delta = Delta::start();
        drop(delay1(double, (1,)));
        assert_eq!(delta.of(stats::CREATED + INT), 1);
        assert_eq!(delta.of(stats::DROPPED_UNFORCED + INT), 1);
        assert_eq!(delta.of(stats::FORCED_UNIQUE + INT), 0);
        let forced = delay1(double, (1,));
        forced.force();
        drop(forced);
        assert_eq!(delta.of(stats::DROPPED_UNFORCED + INT), 1);
    }

    #[test]
    fn a_shared_thunk_is_counted_when_first_forced() {
        let delta = Delta::start();
        let thunk = delay1(double, (2,));
        let other = thunk.clone();
        assert_eq!(thunk.force(), 4);
        assert_eq!(other.force(), 4);
        assert_eq!(delta.of(stats::FORCED_SHARED + INT), 1);
        assert_eq!(delta.of(stats::FORCED_UNIQUE + INT), 0);
    }

    #[test]
    fn a_thunk_that_returns_a_thunk_is_chased_unique() {
        let delta = Delta::start();
        let outer = delay1(through, (5,));
        assert_eq!(outer.force(), 10);
        assert_eq!(delta.of(stats::DELAY + 1), 2);
        assert_eq!(delta.of(stats::CREATED + INT), 2);
        assert_eq!(delta.of(stats::FORCED_UNIQUE + INT), 1);
        assert_eq!(delta.of(stats::CHASED_UNIQUE + INT), 1);
        assert_eq!(delta.of(stats::CHASED_SHARED + INT), 0);
    }

    #[test]
    fn data_ready_is_counted_by_arity() {
        let delta = Delta::start();
        let all = (
            Data::ready(fixtures::c("Nil"), []),
            Data::ready(fixtures::c("Cons"), [Field::Int64(1)]),
            Data::ready(fixtures::c("Cons"), [Field::Int64(1), Field::Int64(2)]),
            Data::ready(fixtures::c("Cons"), vec![Field::Int64(1); 3]),
            Data::ready(fixtures::c("Cons"), vec![Field::Int64(1); 4]),
            Data::ready(fixtures::c("Cons"), vec![Field::Int64(1); 6]),
        );
        for (arity, count) in [(0, 1), (1, 1), (2, 1), (3, 1), (4, 2)] {
            assert_eq!(delta.of(stats::READY + arity), count, "arity {arity}");
        }
        assert_eq!(delta.of(stats::EVALUATED + DATA), 6);
        drop(all);
    }

    #[test]
    fn closures_are_counted() {
        fn code(_: &(), arguments: Vec<Field>) -> Field {
            arguments[0].clone()
        }
        let delta = Delta::start();
        let closure = Closure::bind(2, code, ());
        assert_eq!(delta.of(stats::BIND), 1);
        let partial = closure.apply(vec![Field::Int64(1)]);
        assert_eq!(delta.of(stats::PARTIAL), 1);
        assert_eq!(delta.of(stats::APPLY_GENERAL), 1);
        assert_eq!(partial.closure().apply(vec![Field::Int64(2)]).int64(), 1);
    }

    #[test]
    fn the_program_thread_flushes_its_counts_into_the_report() {
        // Runs on a thread of its own, which is gone when this returns: only
        // the flush at the end of `on_program_stack` carries its counts here.
        on_program_stack(|| {
            delay5(
                |a: i64, _: i64, _: i64, _: i64, _: i64| Int::ready(a),
                (1, 2, 3, 4, 5),
            )
            .force()
        });
        assert!(stats::report().contains("delay5"));
    }

    #[test]
    fn the_report_renders_a_table() {
        let delta = Delta::start();
        let thunk = delay1(through, (1,));
        thunk.force();
        drop(delay2(|a: i64, b: i64| Int::ready(a + b), (1, 2)));
        drop(Data::ready(
            fixtures::c("Cons"),
            [Field::Int64(1), Field::Int64(2)],
        ));
        assert!(delta.of(stats::CREATED + INT) >= 3);
        let report = stats::report();
        println!("{report}");
        for heading in [
            "thunks",
            "fate of those thunks",
            "delay1",
            "delay2",
            "Data::ready by arity",
            "calls",
        ] {
            assert!(report.contains(heading), "{heading}");
        }
    }

    fn site_counts(site: u32) -> [u64; 6] {
        [
            stats::SITE_CREATED,
            stats::SITE_FORCED_UNIQUE,
            stats::SITE_FORCED_SHARED,
            stats::SITE_CHASED_UNIQUE,
            stats::SITE_CHASED_SHARED,
            stats::SITE_UNFORCED,
        ]
        .map(|field| stats::site_get(site, field))
    }

    #[test]
    fn a_delay1_at_thunk_dropped_unforced_is_counted_against_its_site() {
        // [created, forced unique, forced shared, chased unique, chased shared, unforced]
        let thunk = delay1_at(3, double, (1,));
        assert_eq!(site_counts(3), [1, 0, 0, 0, 0, 0]);
        drop(thunk);
        assert_eq!(site_counts(3), [1, 0, 0, 0, 0, 1]);
        // Nothing leaked into the neighbours or into the unattributed row.
        assert_eq!(site_counts(2), [0; 6]);
        assert_eq!(site_counts(4), [0; 6]);
        assert_eq!(site_counts(stats::NO_SITE), [0; 6]);
        // The thread-local is spent by the thunk it was meant for.
        let unattributed = delay1(double, (1,));
        assert_eq!(site_counts(stats::NO_SITE)[0], 1);
        drop(unattributed);
        assert_eq!(site_counts(stats::NO_SITE)[5], 1);
    }

    #[test]
    fn forced_and_chased_thunks_are_counted_against_their_own_sites() {
        // `through` makes a second thunk (made by plain `delay1`, so
        // unattributed) that the first, site 10, returns and `chase` runs.
        let outer = delay1_at(10, through, (5,));
        let shared = delay1_at(11, double, (2,));
        let other = shared.clone();
        assert_eq!(outer.force(), 10);
        assert_eq!(shared.force(), 4);
        assert_eq!(other.force(), 4);
        assert_eq!(site_counts(10), [1, 1, 0, 0, 0, 0]);
        assert_eq!(site_counts(11), [1, 0, 1, 0, 0, 0]);
        let unattributed = site_counts(stats::NO_SITE);
        assert_eq!(unattributed[stats::SITE_CREATED], 1);
        assert_eq!(unattributed[stats::SITE_CHASED_UNIQUE], 1);
    }

    #[test]
    fn apply_later_at_is_attributed_too() {
        fn code(_: &(), arguments: Vec<Field>) -> Field {
            arguments[0].clone()
        }
        let callee = Closure::bind(1, code, ());
        let thunk: Int = apply_later_at(12, callee, vec![Field::Int(Int::ready(8))], Field::int);
        assert_eq!(site_counts(12)[stats::SITE_CREATED], 1);
        assert_eq!(thunk.force(), 8);
        assert_eq!(site_counts(12)[stats::SITE_FORCED_UNIQUE], 1);
    }

    static SITES: [stats::SiteInfo; 3] = [
        stats::SiteInfo {
            krate: "h2r_c0",
            function: "Main.loop",
            instance: 4,
            block: 2,
            kind: "DelayBlock instruction",
            origin: "DelayBlock / App (call of a global)",
            used_by: "field of a constructor",
            captured: 2,
        },
        stats::SiteInfo {
            krate: "h2r_c0",
            function: "Main.loop",
            instance: 4,
            block: 3,
            kind: "looping tail call",
            origin: "CallLocal",
            used_by: "",
            captured: 3,
        },
        stats::SiteInfo {
            krate: "h2r_c1",
            function: "Data.List.map",
            instance: 9,
            block: 0,
            kind: "f_ wrapper (lifted result)",
            origin: "function entry",
            used_by: "",
            captured: 1,
        },
    ];

    #[test]
    fn the_report_ranks_sites_with_their_table_rows() {
        install_sites(&SITES);
        for _ in 0..5 {
            drop(delay2_at(0, |a: i64, b: i64| Int::ready(a + b), (1, 2)));
        }
        for n in 0..2 {
            drop(delay1_at(1, double, (n,)));
        }
        for n in 0..7 {
            let thunk = delay1_at(2, double, (n,));
            assert_eq!(thunk.force(), n * 2);
        }
        let report = stats::report();
        println!("{report}");
        let unforced = report
            .split("top 40 sites by thunks freed unforced")
            .nth(1)
            .and_then(|rest| rest.split("top 40 sites by thunks created").next())
            .expect("the unforced table");
        let first = unforced.lines().nth(2).expect("a first row");
        assert!(first.contains("Main.loop#4 b2"), "{first}");
        assert!(unforced.contains("Main.loop#4 b3"));
        assert!(!unforced.contains("Data.List.map"), "never unforced");
        let created = report
            .split("top 40 sites by thunks created")
            .nth(1)
            .and_then(|rest| rest.split("by where written").next())
            .expect("the created table");
        assert!(
            created
                .lines()
                .nth(2)
                .expect("row")
                .contains("Data.List.map#9")
        );
        assert!(report.contains("DelayBlock instruction / DelayBlock / App (call of a global)"));
        assert!(report.contains("field of a constructor"));
    }
}
