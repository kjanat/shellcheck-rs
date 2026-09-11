//! Ported check batches. Separate files let batches be developed in parallel.
use crate::analyzer_lib::Checker;
pub mod batch_a; pub mod batch_b; pub mod batch_c; pub mod batch_d; pub mod batch_e;
pub mod batch_f; pub mod batch_g; pub mod batch_h; pub mod batch_i; pub mod batch_j; pub mod batch_k;
pub mod batch_l; pub mod batch_m; pub mod batch_n;
pub mod flow;
pub fn register_all(c: &mut Checker) {
    batch_a::register(c); batch_b::register(c); batch_c::register(c); batch_d::register(c);
    batch_e::register(c); batch_f::register(c); batch_g::register(c); batch_h::register(c);
    batch_i::register(c); batch_j::register(c); batch_k::register(c);
    batch_l::register(c); batch_m::register(c); batch_n::register(c);
    flow::register(c);
}
