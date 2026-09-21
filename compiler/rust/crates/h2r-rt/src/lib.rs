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
    Int(Int),
    Data(Data),
    Closure(Closure),
}

impl Field {
    pub fn force(&self) {
        match self {
            Self::Int64(_) => {}
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
