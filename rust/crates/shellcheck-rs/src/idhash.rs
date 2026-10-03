//! A fast, deterministic hasher for the integer keys of the control flow
//! graph (`Node` = `usize`, `ast::Id` = `i32`).
//!
//! The standard library's default `RandomState` is SipHash-1-3 with a random
//! seed: DoS-resistant, and several times more expensive than the lookup it
//! guards when the key is one small integer. The keys here are dense indices
//! produced by this crate, never attacker-chosen strings, so a
//! multiply-and-rotate hash (the `FxHash` construction) is enough.
//!
//! Nothing may depend on the iteration order of an [`IdMap`] or [`IdSet`]
//! (it is deterministic but arbitrary, as it was with `RandomState`);
//! anything observable goes through a sort or a `BTreeMap`.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

/// Multiplier of `FxHash` (rustc-hash 2): an odd constant with well mixed bits.
const K: u64 = 0xf135_7aea_2e62_a9c5;

/// Hasher for small integer keys (and tuples or enums of them).
#[derive(Default, Clone, Copy)]
pub struct IdHasher {
    hash: u64,
}

impl IdHasher {
    #[inline]
    const fn add(&mut self, x: u64) {
        self.hash = (self.hash.rotate_left(5) ^ x).wrapping_mul(K);
    }
}

impl Hasher for IdHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.add(u64::from(b));
        }
    }

    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }

    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(u64::from(i));
    }

    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(u64::from(i));
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }

    #[inline]
    fn write_i32(&mut self, i: i32) {
        // Sign-extend through i64 so equal values hash equally however they
        // were widened.
        self.add(i64::from(i).cast_unsigned());
    }

    #[inline]
    fn write_isize(&mut self, i: isize) {
        self.add((i as i64).cast_unsigned());
    }

    #[inline]
    fn finish(&self) -> u64 {
        // The multiply leaves the entropy in the high bits; hashbrown takes
        // the low bits for the bucket and the top seven for the tag.
        self.hash.rotate_left(26)
    }
}

/// `BuildHasher` for [`IdHasher`].
pub type IdBuild = BuildHasherDefault<IdHasher>;

/// A `HashMap` keyed by `Node` or `Id` (build it with `IdMap::default()`).
pub type IdMap<K, V> = HashMap<K, V, IdBuild>;

/// A `HashSet` of `Node`s or `Id`s (build it with `IdSet::default()`).
pub type IdSet<K> = HashSet<K, IdBuild>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::{BuildHasher, Hash};

    fn hash_of<T: Hash>(x: T) -> u64 {
        IdBuild::default().hash_one(x)
    }

    #[test]
    fn hashing_is_deterministic_and_spreads_dense_keys() {
        assert_eq!(hash_of(42usize), hash_of(42usize));
        assert_ne!(hash_of(1usize), hash_of(2usize));
        // Negative ids do not collide with small positive ones.
        assert_eq!(hash_of(-1i32), hash_of(-1i32));
        assert_ne!(hash_of(-1i32), hash_of(1i32));
        // The bucket index (low bits) must differ for sequential keys.
        let buckets: IdSet<u64> = (0usize..64).map(|n| hash_of(n) & 0xff).collect();
        assert!(
            buckets.len() > 40,
            "only {} distinct buckets",
            buckets.len()
        );
    }

    #[test]
    fn maps_and_sets_behave_like_std() {
        let mut m: IdMap<usize, &str> = IdMap::default();
        m.insert(3, "c");
        m.insert(1, "a");
        m.insert(3, "z");
        assert_eq!(m.get(&3), Some(&"z"));
        assert_eq!(m.get(&2), None);
        let s: IdSet<(usize, usize)> = [(1, 2), (1, 2), (2, 1)].into_iter().collect();
        assert_eq!(s.len(), 2);
    }
}
