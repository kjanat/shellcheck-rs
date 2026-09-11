//! Ported check batches. Each batch module is a self-contained set of checks
//! authored/validated independently (e.g. by a subagent), registering into the
//! shared `Checker`. Keeping batches in separate files lets them be developed in
//! parallel without merge conflicts.

use crate::analyzer_lib::Checker;

pub mod batch_a;
pub mod batch_b;

/// Register every ported batch into the analytics checker.
pub fn register_all(c: &mut Checker) {
    batch_a::register(c);
    batch_b::register(c);
}
