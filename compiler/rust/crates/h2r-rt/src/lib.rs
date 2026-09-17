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

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

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
}
