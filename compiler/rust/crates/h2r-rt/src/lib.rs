//! Runtime support for Haskell compiled to Rust.
//!
//! The design rule for this crate is that as little of it as possible should
//! ever appear in generated code. Anything GHC's demand analysis proves strict
//! is emitted as a plain Rust value; what is left over -- bindings that may or
//! may not be demanded, and genuinely cyclic values -- lands here.

use std::cell::{OnceCell, RefCell};
use std::fmt;
use std::rc::Rc;

/// A call-by-need binding: evaluated at most once, shared by every use.
pub struct Lazy<T> {
    value: OnceCell<T>,
    init: RefCell<Option<Box<dyn FnOnce() -> T>>>,
}

impl<T> Lazy<T> {
    /// Defer `f` until the value is first demanded.
    pub fn new(f: impl FnOnce() -> T + 'static) -> Self {
        Lazy {
            value: OnceCell::new(),
            init: RefCell::new(Some(Box::new(f))),
        }
    }

    /// An already-evaluated binding; the common case after strictness analysis.
    pub fn ready(value: T) -> Self {
        let cell = OnceCell::new();
        let _ = cell.set(value);
        Lazy {
            value: cell,
            init: RefCell::new(None),
        }
    }

    /// Force to WHNF, memoising the result.
    ///
    /// Panics on re-entrant forcing, which is this runtime's `<<loop>>`.
    pub fn force(&self) -> &T {
        if let Some(v) = self.value.get() {
            return v;
        }
        let f = self
            .init
            .borrow_mut()
            .take()
            .expect("h2r-rt: re-entrant force (<<loop>>)");
        let v = f();
        let _ = self.value.set(v);
        self.value.get().expect("h2r-rt: thunk set failed")
    }

    /// Whether the binding has already been forced.
    pub fn is_evaluated(&self) -> bool {
        self.value.get().is_some()
    }
}

impl<T: fmt::Debug> fmt::Debug for Lazy<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value.get() {
            Some(v) => write!(f, "Lazy({v:?})"),
            None => write!(f, "Lazy(<thunk>)"),
        }
    }
}

/// A thunk shared across several owners, for recursive or graph-shaped values.
pub type Shared<T> = Rc<Lazy<T>>;

pub fn shared<T>(f: impl FnOnce() -> T + 'static) -> Shared<T> {
    Rc::new(Lazy::new(f))
}

/// A shared, call-by-need boxed machine Int. Its I# field is unlifted.
#[derive(Clone)]
pub struct Int(Shared<i64>);

impl Int {
    pub fn defer(f: impl FnOnce() -> i64 + 'static) -> Self {
        Self(shared(f))
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
    pub fields: Vec<Field>,
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
}

impl Field {
    pub fn force(&self) {
        match self {
            Self::Int64(_) | Self::Char(_) => {}
            Self::Int(v) => {
                v.force();
            }
            Self::Data(v) => {
                v.force();
            }
            Self::Closure(v) => {
                v.force();
            }
        }
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
            _ => panic!("invalid Int field"),
        }
    }
    pub fn data(&self) -> Data {
        match self {
            Self::Data(v) => v.clone(),
            _ => panic!("invalid data field"),
        }
    }
    pub fn closure(&self) -> Closure {
        match self {
            Self::Closure(v) => v.clone(),
            _ => panic!("invalid function carrier"),
        }
    }
}

/// A shared lazy function value. Partial application retains arguments without
/// forcing them; saturation invokes code exactly once per call, not per closure.
#[derive(Clone)]
pub struct Closure(Shared<ClosureCode>);

#[derive(Clone)]
pub struct ClosureCode {
    arity: usize,
    code: Rc<dyn Fn(Vec<Field>) -> Field>,
    supplied: Vec<Field>,
}

impl Closure {
    pub fn ready(arity: usize, code: impl Fn(Vec<Field>) -> Field + 'static) -> Self {
        assert!(arity > 0);
        Self(Rc::new(Lazy::ready(ClosureCode {
            arity,
            code: Rc::new(code),
            supplied: Vec::new(),
        })))
    }
    pub fn defer(init: impl FnOnce() -> ClosureCode + 'static) -> Self {
        Self(shared(init))
    }
    pub fn force(&self) -> ClosureCode {
        self.0.force().clone()
    }
    pub fn is_evaluated(&self) -> bool {
        self.0.is_evaluated()
    }
    pub fn apply(&self, arguments: Vec<Field>) -> Field {
        let mut result = Field::Closure(self.clone());
        for argument in arguments {
            let mut function = result.closure().force();
            function.supplied.push(argument);
            result = if function.supplied.len() == function.arity {
                (function.code)(function.supplied)
            } else {
                Field::Closure(Self(Rc::new(Lazy::ready(function))))
            };
        }
        result
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
            Closure::ready(1, |args| args[0].clone()).force()
        });
        assert!(!f.is_evaluated());
        assert_eq!(f.clone().apply(vec![Field::Int64(1)]).int64(), 1);
        assert_eq!(f.apply(vec![Field::Int64(2)]).int64(), 2);
        assert_eq!(n.get(), 1);
    }
}

impl Data {
    pub fn defer(f: impl FnOnce() -> Node + 'static) -> Self {
        Self(shared(f))
    }
    pub fn ready(constructor: &'static str, fields: Vec<Field>) -> Self {
        Self(Rc::new(Lazy::ready(Node {
            constructor,
            fields,
        })))
    }
    pub fn force(&self) -> Node {
        self.0.force().clone()
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
        return tail.force();
    }
    let (codepoint, next) = code_point(bytes, at, encoding);
    Node {
        constructor: names.cons,
        fields: vec![
            Field::Data(Data::ready(names.character, vec![Field::Char(codepoint)])),
            Field::Data(Data::defer(move || {
                unpack_at(bytes, next, encoding, names, tail)
            })),
        ],
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
    Data::defer(move || {
        let node = left.force();
        if node.constructor == names.nil {
            return right.force();
        }
        let tail = node.fields[1].data();
        Node {
            constructor: names.cons,
            fields: vec![
                node.fields[0].clone(),
                Field::Data(append_list(tail, right, names)),
            ],
        }
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
            .fold(Data::ready(NAMES.nil, vec![]), |tail, value| {
                Data::ready(NAMES.cons, vec![Field::Int64(*value), Field::Data(tail)])
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
            ints(&[9]).force()
        });
        let joined = append_list(ints(&[1]), right.clone(), NAMES);
        let first = joined.force();
        // One cell demanded: the right list has not been looked at yet.
        assert_eq!(forced.get(), 0);
        assert_eq!(first.fields[0].int64(), 1);
        // Reaching the end enters the right list once, and its cells are the
        // ones it already had rather than copies.
        let rest = first.fields[1].data().force();
        assert_eq!(rest.fields[0].int64(), 9);
        assert_eq!(forced.get(), 1);
        assert!(right.is_evaluated());
    }

    #[test]
    fn a_lazy_element_survives_the_copy_unforced() {
        let element = Int::defer(|| panic!("append forced an element"));
        let left = Data::ready(
            NAMES.cons,
            vec![
                Field::Int(element.clone()),
                Field::Data(Data::ready(NAMES.nil, vec![])),
            ],
        );
        let joined = append_list(left, Data::ready(NAMES.nil, vec![]), NAMES);
        let node = joined.force();
        assert!(node.fields[0].int().shares_with(&element));
        assert!(!element.is_evaluated());
    }
}

/// A string literal as a lazy `[Char]` ending in `[]`.
pub fn unpack_literal(bytes: &'static [u8], encoding: Encoding, names: StringNames) -> Data {
    unpack_string(bytes, encoding, names, Data::ready(names.nil, vec![]))
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
            fields: vec![Field::Int(field)],
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
        let tail = Data::ready("Nil", vec![]);
        let list = Data::ready("Cons", vec![Field::Int64(42), Field::Data(tail.clone())]);
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
