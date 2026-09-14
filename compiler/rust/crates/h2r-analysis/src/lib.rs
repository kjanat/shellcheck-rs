//! Analyses over the flattened Core arena.

pub mod boundary;
pub mod callee;
pub mod classops;
pub mod dictflow;
pub mod fields;
pub mod flow;
pub mod higher;
pub mod laziness;
pub mod link;
pub mod lists;
pub mod m23;
pub mod metrics;
pub mod parsec;
pub mod scalar;
pub mod scope;
pub mod shape;
pub mod text;
pub mod tuples;
pub mod verify;
pub mod verify_rep;
pub mod views;

#[cfg(test)]
mod tests;
