//! Ported check batches. Each batch module is a self-contained set of checks
//! authored/validated independently (e.g. by a subagent), registering into the
//! shared `Checker`. Separate files let batches be developed in parallel.

use crate::analyzer_lib::Checker;

pub mod batch_a;
pub mod batch_b;
pub mod batch_c;
pub mod batch_d;
pub mod batch_e;

pub fn register_all(c: &mut Checker) {
    batch_a::register(c);
    batch_b::register(c);
    batch_c::register(c);
    batch_d::register(c);
    batch_e::register(c);
}
