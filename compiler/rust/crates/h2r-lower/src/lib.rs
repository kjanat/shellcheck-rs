//! Lowering. Where [`h2r_analysis`] *proves* things about the dumped Core,
//! this crate *constructs* the program the proofs licence.
//!
//! The source arena ([`h2r_core_ir`]) and every M1–M2.4 proof object are
//! immutable evidence: nothing here mutates Core, and nothing here
//! re-derives a fact an analysis already carries. M3a is the first step
//! and the smallest one — decide which of the dump's top-level bindings
//! the program can actually reach from `Main.main`, with a witness for
//! every live binding and a named reason for every dead one.

pub mod reachability;
