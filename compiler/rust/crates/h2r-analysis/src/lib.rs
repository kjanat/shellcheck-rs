//! Analyses over the flattened Core arena.

pub mod callee;
pub mod laziness;
pub mod metrics;
pub mod parsec;
pub mod scope;
pub mod shape;
pub mod tuples;

#[cfg(test)]
mod tests;
