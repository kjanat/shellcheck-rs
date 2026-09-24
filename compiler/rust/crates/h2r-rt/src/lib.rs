//! Runtime support for Haskell compiled to Rust.
//!
//! The design rule for this crate is that as little of it as possible should
//! ever appear in generated code. Anything GHC's demand analysis proves strict
//! is emitted as a plain Rust value; what is left over -- bindings that may or
//! may not be demanded, and genuinely cyclic values -- lands here.

use std::cell::{Cell, OnceCell, RefCell};
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone, Copy)]
pub struct Addr {
    bytes: &'static [u8],
    offset: usize,
}

impl Addr {
    pub fn literal(bytes: &'static [u8]) -> Self {
        Addr { bytes, offset: 0 }
    }

    pub fn index_char(self, index: i64) -> i64 {
        self.index_word8(index)
    }

    pub fn index_word8(self, index: i64) -> i64 {
        let at = self
            .offset
            .checked_add_signed(index as isize)
            .expect("h2r-rt: an address offset left the address space");
        i64::from(self.bytes[at])
    }

    pub fn plus(self, delta: i64) -> Self {
        Addr {
            bytes: self.bytes,
            offset: self
                .offset
                .checked_add_signed(delta as isize)
                .expect("h2r-rt: an address offset left the address space"),
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

/// A call-by-need binding: evaluated at most once, shared by every use.
pub struct Lazy<T, C: ?Sized = dyn Code<T>> {
    value: OnceCell<T>,
    code: C,
}

pub trait Code<T> {
    fn enter(&self) -> Option<Thunk<T>>;
    fn fill(&self, code: Box<dyn FnOnce() -> Thunk<T>>) -> bool;
}

struct Once<F>(Cell<Option<F>>);

impl<T, F: FnOnce() -> Thunk<T>> Code<T> for Once<F> {
    fn enter(&self) -> Option<Thunk<T>> {
        self.0.take().map(|f| f())
    }
    fn fill(&self, _: Box<dyn FnOnce() -> Thunk<T>>) -> bool {
        false
    }
}

struct Pending<T>(Cell<Option<Box<dyn FnOnce() -> Thunk<T>>>>);

impl<T> Code<T> for Pending<T> {
    fn enter(&self) -> Option<Thunk<T>> {
        self.0.take().map(|f| f())
    }
    fn fill(&self, code: Box<dyn FnOnce() -> Thunk<T>>) -> bool {
        self.0.replace(Some(code)).is_none()
    }
}

pub enum Thunk<T> {
    Value(T),
    Indirect(Rc<Lazy<T>>),
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
            code: Once(Cell::new(None::<fn() -> Thunk<T>>)),
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

    fn enter(&self) -> Thunk<T> {
        self.code
            .enter()
            .expect("h2r-rt: re-entrant force (<<loop>>)")
    }
}

impl<T: Clone, C: Code<T> + ?Sized> Lazy<T, C> {
    /// Force to WHNF, memoising the result.
    ///
    /// Panics on re-entrant forcing, which is this runtime's `<<loop>>`.
    pub fn force(&self) -> &T {
        if let Some(v) = self.value.get() {
            return v;
        }
        let value = match self.enter() {
            Thunk::Value(value) => value,
            Thunk::Indirect(next) => chase(next),
        };
        self.value.get_or_init(|| value)
    }
}

#[inline(never)]
fn chase<T: Clone>(first: Rc<Lazy<T>>) -> T {
    let mut pending = Vec::new();
    let mut current = first;
    let value = loop {
        if let Some(value) = current.value.get() {
            break value.clone();
        }
        match current.enter() {
            Thunk::Value(value) => {
                pending.push(current);
                break value;
            }
            Thunk::Indirect(next) => {
                if Rc::strong_count(&current) > 1 {
                    pending.push(current);
                }
                current = next;
            }
        }
    };
    for cell in pending {
        cell.value.get_or_init(|| value.clone());
    }
    value
}

impl<T: fmt::Debug, C: ?Sized> fmt::Debug for Lazy<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value.get() {
            Some(v) => write!(f, "Lazy({v:?})"),
            None => write!(f, "Lazy(<thunk>)"),
        }
    }
}

/// A thunk shared across several owners, for recursive or graph-shaped values.
pub type Shared<T> = Rc<Lazy<T>>;

pub fn shared<T: 'static>(f: impl FnOnce() -> T + 'static) -> Shared<T> {
    Rc::new(Lazy::new(f))
}

/// A shared, call-by-need boxed machine Int. Its I# field is unlifted.
#[derive(Clone)]
pub struct Int(Shared<i64>);

impl Int {
    pub fn defer(f: impl FnOnce() -> i64 + 'static) -> Self {
        Self(shared(f))
    }
    pub fn defer_to(f: impl FnOnce() -> Self + 'static) -> Self {
        Self(Rc::new(Lazy::step(move || Thunk::Indirect(f().0))))
    }
    pub fn pending() -> Self {
        Self(Rc::new(Lazy::pending()))
    }
    pub fn fill(&self, value: Self) {
        self.0.fill(move || Thunk::Indirect(value.0));
    }
    pub fn ready(value: i64) -> Self {
        Self(Rc::new(Lazy::ready(value)))
    }
    pub fn force(&self) -> i64 {
        *self.0.force()
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    pub fn shares_with(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

/// A general algebraic value. The outer node and every lifted field have
/// independent memoisation cells; inspecting a tag never forces lazy fields.
#[derive(Clone)]
pub struct Data(Shared<Node>);

#[derive(Clone)]
pub struct Node {
    pub constructor: &'static str,
    pub fields: Fields,
}

#[derive(Clone)]
pub enum Fields {
    Zero,
    One([Field; 1]),
    Two([Field; 2]),
    Three([Field; 3]),
    Many(Vec<Field>),
}

impl std::ops::Deref for Fields {
    type Target = [Field];
    fn deref(&self) -> &[Field] {
        match self {
            Fields::Zero => &[],
            Fields::One(fields) => fields,
            Fields::Two(fields) => fields,
            Fields::Three(fields) => fields,
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
    fn from(fields: [Field; 1]) -> Self {
        Fields::One(fields)
    }
}

impl From<[Field; 2]> for Fields {
    fn from(fields: [Field; 2]) -> Self {
        Fields::Two(fields)
    }
}

impl From<[Field; 3]> for Fields {
    fn from(fields: [Field; 3]) -> Self {
        Fields::Three(fields)
    }
}

impl From<Vec<Field>> for Fields {
    fn from(fields: Vec<Field>) -> Self {
        let fields = match <[Field; 1]>::try_from(fields) {
            Ok(one) => return Fields::One(one),
            Err(fields) => fields,
        };
        let fields = match <[Field; 2]>::try_from(fields) {
            Ok(two) => return Fields::Two(two),
            Err(fields) => fields,
        };
        let fields = match <[Field; 3]>::try_from(fields) {
            Ok(three) => return Fields::Three(three),
            Err(fields) => fields,
        };
        if fields.is_empty() {
            Fields::Zero
        } else {
            Fields::Many(fields)
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

fn deferred(value: Field) -> Thunk<Field> {
    match value {
        Field::Deferred(next) => Thunk::Indirect(next),
        value => Thunk::Value(value),
    }
}

impl Field {
    pub fn defer_to(f: impl FnOnce() -> Field + 'static) -> Self {
        Self::Deferred(Rc::new(Lazy::step(move || deferred(f()))))
    }
    pub fn pending() -> Self {
        Self::Deferred(Rc::new(Lazy::pending()))
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
            Self::Deferred(cell) => match cell.value.get() {
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
            Self::Deferred(cell) => match cell.value.get() {
                Some(value) => value.data(),
                None => {
                    let cell = cell.clone();
                    Data::defer_to(move || cell.force().data())
                }
            },
            _ => panic!("invalid data field"),
        }
    }
    pub fn closure(&self) -> Closure {
        match self {
            Self::Closure(v) => v.clone(),
            Self::Deferred(cell) => match cell.value.get() {
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
#[derive(Clone)]
pub struct Closure(Shared<ClosureCode>);

#[derive(Clone)]
pub struct ClosureCode {
    arity: usize,
    code: Rc<dyn Fn(Vec<Field>) -> Field>,
    enter: Option<Entry>,
    supplied: Vec<Field>,
}

type Entry = Rc<dyn Fn(Vec<Field>) -> Step<i64>>;

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
        assert!(arity > 0);
        Self(Rc::new(Lazy::ready(ClosureCode {
            arity,
            code: Rc::new(code),
            enter: None,
            supplied: Vec::new(),
        })))
    }
    pub fn entering(
        arity: usize,
        code: impl Fn(Vec<Field>) -> Field + 'static,
        enter: impl Fn(Vec<Field>) -> Step<i64> + 'static,
    ) -> Self {
        assert!(arity > 0);
        Self(Rc::new(Lazy::ready(ClosureCode {
            arity,
            code: Rc::new(code),
            enter: Some(Rc::new(enter)),
            supplied: Vec::new(),
        })))
    }
    pub fn defer(init: impl FnOnce() -> ClosureCode + 'static) -> Self {
        Self(shared(init))
    }
    pub fn defer_to(f: impl FnOnce() -> Self + 'static) -> Self {
        Self(Rc::new(Lazy::step(move || Thunk::Indirect(f().0))))
    }
    pub fn pending() -> Self {
        Self(Rc::new(Lazy::pending()))
    }
    pub fn fill(&self, value: Self) {
        self.0.fill(move || Thunk::Indirect(value.0));
    }
    pub fn apply_tail(&self, arguments: Vec<Field>) -> Tail {
        let function = self.force();
        if let Some(enter) = &function.enter
            && function.supplied.len() + arguments.len() == function.arity
        {
            let mut supplied = Vec::with_capacity(function.arity);
            supplied.extend(function.supplied.iter().cloned());
            supplied.extend(arguments);
            return Tail::Enter(enter(supplied));
        }
        Tail::Value(self.apply(arguments))
    }
    pub fn force(&self) -> &ClosureCode {
        self.0.force()
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    pub fn apply(&self, arguments: Vec<Field>) -> Field {
        let mut arguments = arguments.into_iter();
        let mut current = self.clone();
        loop {
            let function = current.force();
            let missing = function.arity - function.supplied.len();
            if arguments.len() < missing {
                if arguments.len() == 0 {
                    return Field::Closure(current);
                }
                let mut supplied = function.supplied.clone();
                supplied.extend(arguments);
                return Field::Closure(Self(Rc::new(Lazy::ready(ClosureCode {
                    arity: function.arity,
                    code: function.code.clone(),
                    enter: function.enter.clone(),
                    supplied,
                }))));
            }
            let mut supplied = Vec::with_capacity(function.arity);
            supplied.extend(function.supplied.iter().cloned());
            supplied.extend(arguments.by_ref().take(missing));
            let result = (function.code)(supplied);
            if arguments.len() == 0 {
                return result;
            }
            current = result.closure();
        }
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
        let f = Closure::defer(move || {
            count.set(count.get() + 1);
            Closure::ready(1, |args| args[0].clone()).force().clone()
        });
        assert!(!f.is_evaluated());
        assert_eq!(f.clone().apply(vec![Field::Int64(1)]).int64(), 1);
        assert_eq!(f.apply(vec![Field::Int64(2)]).int64(), 2);
        assert_eq!(n.get(), 1);
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
            constructor: ":",
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
        Self(Rc::new(Lazy::step(move || Thunk::Indirect(f().0))))
    }
    pub fn pending() -> Self {
        Self(Rc::new(Lazy::pending()))
    }
    pub fn fill(&self, value: Self) {
        self.0.fill(move || Thunk::Indirect(value.0));
    }
    pub fn ready(constructor: &'static str, fields: impl Into<Fields>) -> Self {
        Self(Rc::new(Lazy::ready(Node {
            constructor,
            fields: fields.into(),
        })))
    }
    pub fn force(&self) -> &Node {
        self.0.force()
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    pub fn shares_with(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
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
        ].into(),
    }
}

/// The constructor names the generated code matches these cells against. They
/// come from the compiler's own layout evidence, not from this crate.
#[derive(Clone, Copy)]
pub struct StringNames {
    pub cons: &'static str,
    pub nil: &'static str,
    pub character: &'static str,
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
    pub empty: &'static str,
    pub push: &'static str,
    pub freeze: &'static str,
    pub location: &'static str,
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
    pub cons: &'static str,
    pub nil: &'static str,
}

/// `GHC.Base.(++)`: the left spine copied onto the right one, lazily.
///
/// Forcing the result to WHNF forces the left list to WHNF and nothing else,
/// so the right list is never touched until the left runs out, and a cell of
/// the left list is copied only when the corresponding result cell is
/// demanded. The right list is reached, not copied: its cells are shared.
pub fn append_list(left: Data, right: Data, names: ListNames) -> Data {
    Data(Rc::new(Lazy::step(move || {
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
            ].into(),
        })
    })))
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
            ].into(),
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
                    ].into(),
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
            ].into(),
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
    pub false_: &'static str,
    pub true_: &'static str,
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
    pub lt: &'static str,
    pub eq: &'static str,
    pub gt: &'static str,
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

#[cfg(test)]
mod append_tests {
    use super::*;

    const NAMES: ListNames = ListNames {
        cons: ":",
        nil: "[]",
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
            cons: ":",
            nil: "[]",
            character: "C#",
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
            cons: ":",
            nil: "[]",
            character: "C#",
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
        empty: "EmptyCallStack",
        push: "PushCallStack",
        freeze: "FreezeCallStack",
        location: "SrcLoc",
    };

    fn located(file: &str, line: i64, column: i64) -> Data {
        let nil = || Data::ready("[]", []);
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
                Field::Data(string(function, Data::ready("[]", []))),
                Field::Data(location),
                Field::Data(rest),
            ],
        )
    }

    #[test]
    fn error_messages_render_the_call_stack_as_base_shows_it() {
        let nil = || Data::ready("[]", []);
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
                if a[0].int64() > 0 { "True" } else { "False" },
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
                ":",
                [
                    Field::Data(Data::ready("C#", [Field::Char(c as i64)])),
                    Field::Data(tail),
                ],
            )
        })
    }

    fn holds(value: Data) -> bool {
        match value.force().constructor {
            "True" => true,
            "False" => false,
            other => panic!("not a Bool: {other}"),
        }
    }

    const STRING: StringNames = StringNames {
        cons: ":",
        nil: "[]",
        character: "C#",
    };
    const TRUTH: Truth = Truth {
        false_: "False",
        true_: "True",
    };

    #[test]
    fn strings_and_characters_show_as_ghc_shows_them() {
        let nil = || Data::ready("[]", []);
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
        let list = cons(
            "a.sh:1:1: note: x",
            cons("λ", Data::ready(STRING.nil, [])),
        );
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
            lt: "LT",
            eq: "EQ",
            gt: "GT",
        };
        let nil = || Data::ready("[]", []);
        let order = |left, right| {
            compare_lists(left, right, STRING, ORDER)
                .force()
                .constructor
        };
        let negative = Data::ready(
            ":",
            [
                Field::Data(Data::ready("C#", [Field::Char(-1)])),
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
        let nil = || Data::ready("[]", []);
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
            ":",
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
            cons: ":",
            nil: "[]",
            character: "C#",
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
        cons: ":",
        nil: "[]",
        character: "C#",
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
            constructor: "Pair",
            fields: [Field::Int(field)].into(),
        });
        let copy = data.clone();
        assert!(data.shares_with(&copy));
        assert!(!copy.is_evaluated());
        let node = copy.force();
        assert_eq!(node.constructor, "Pair");
        assert!(data.is_evaluated());
        assert!(!retained.is_evaluated());
        assert!(node.fields[0].int().shares_with(&retained));
    }

    #[test]
    fn recursive_datatype_carriers_hold_finite_nested_values() {
        let tail = Data::ready("Nil", []);
        let list = Data::ready("Cons", [Field::Int64(42), Field::Data(tail.clone())]);
        let node = list.force();
        assert_eq!(node.fields[0].int64(), 42);
        assert!(node.fields[1].data().shares_with(&tail));
        assert_eq!(node.fields[1].data().force().constructor, "Nil");
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
        let b = Rc::clone(&a);
        assert_eq!(a.force().len(), 3);
        assert!(b.is_evaluated());
    }

    fn countdown(n: u32, entered: Rc<Cell<u32>>) -> Data {
        if n == 0 {
            return Data::ready("Nil", []);
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
        assert_eq!(chain.force().constructor, "Nil");
        assert_eq!(entered.get(), 1_000_000);
        assert_eq!(chain.force().constructor, "Nil");
        assert_eq!(entered.get(), 1_000_000);
    }

    #[test]
    fn a_shared_link_in_a_chain_is_memoised() {
        let entered = Rc::new(Cell::new(0));
        let middle = countdown(3, entered.clone());
        let held = middle.clone();
        let top = Data::defer_to(move || middle);
        assert_eq!(top.force().constructor, "Nil");
        assert!(held.is_evaluated());
        assert_eq!(held.force().constructor, "Nil");
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
