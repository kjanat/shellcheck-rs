//! Analyses over the flattened Core arena.

pub mod boundary;
pub mod callee;
pub mod fields;
pub mod flow;
pub mod laziness;
pub mod link;
pub mod lists;
pub mod metrics;
pub mod parsec;
pub mod scalar;
pub mod scope;
pub mod shape;
pub mod text;
pub mod tuples;
pub mod verify;

#[cfg(test)]
mod tests;
