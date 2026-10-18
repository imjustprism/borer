//! A fast, seedless hash map for the keys hot loops look up.
//!
//! The standard library's hasher is `SipHash` 1-3, which is strong against
//! hash-flooding and slow for short keys. The engine's hot maps are keyed on
//! registers, stack offsets and addresses, none of which an analyzed binary
//! can choose: the keys come from the engine's own model of the code, not
//! from attacker-controlled bytes. That makes the trade the other way round.
//!
//! This is the hash rustc uses for the same reason, a rotate, an xor and a
//! multiply per word. It carries no random seed, so a given insertion
//! sequence always produces the same table and the same iteration order,
//! which the engine's determinism contract requires: same binary,
//! same query, same answer, byte-identical.
//!
//! Maps whose iteration order reaches an output still use `BTreeMap`, where
//! the order is a property of the keys rather than of the insertion history.

use crate::num::from_usize;
use std::hash::{BuildHasherDefault, Hasher};

/// The odd multiplier rustc's hash uses; chosen for its bit spread.
const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

/// A hash map over [`FxHasher`].
pub type FxHashMap<K, V> = std::collections::HashMap<K, V, BuildHasherDefault<FxHasher>>;

/// A hash set over [`FxHasher`].
pub type FxHashSet<K> = std::collections::HashSet<K, BuildHasherDefault<FxHasher>>;

/// A seedless hash: one rotate, xor and multiply per word.
#[derive(Debug, Default, Clone, Copy)]
pub struct FxHasher {
    /// The accumulated hash.
    hash: u64,
}

impl FxHasher {
    /// Folds one word into the hash.
    ///
    /// # Arguments
    ///
    /// * `w` - The word.
    #[inline]
    fn add(&mut self, w: u64) {
        self.hash = (self.hash.rotate_left(5) ^ w).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            let mut w = [0u8; 8];
            w.copy_from_slice(c);
            self.add(u64::from_le_bytes(w));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut w = [0u8; 8];
            w.get_mut(..rest.len())
                .map(|d| d.copy_from_slice(rest))
                .unwrap_or_default();
            self.add(u64::from_le_bytes(w));
        }
    }

    #[inline]
    fn write_u8(&mut self, v: u8) {
        self.add(u64::from(v));
    }

    #[inline]
    fn write_u16(&mut self, v: u16) {
        self.add(u64::from(v));
    }

    #[inline]
    fn write_u32(&mut self, v: u32) {
        self.add(u64::from(v));
    }

    #[inline]
    fn write_u64(&mut self, v: u64) {
        self.add(v);
    }

    #[inline]
    fn write_usize(&mut self, v: usize) {
        self.add(from_usize(v));
    }

    #[inline]
    fn write_i64(&mut self, v: i64) {
        self.add(v.cast_unsigned());
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{FxHashMap, FxHasher};
    use std::hash::{Hash, Hasher};

    /// The hash carries no seed, so one value always hashes the same.
    ///
    /// This is what lets a hash map stand in for an ordered one without
    /// breaking the determinism contract.
    #[test]
    fn the_hash_is_seedless() {
        let once = {
            let mut h = FxHasher::default();
            0x1234_5678_9abc_deffu64.hash(&mut h);
            h.finish()
        };
        let twice = {
            let mut h = FxHasher::default();
            0x1234_5678_9abc_deffu64.hash(&mut h);
            h.finish()
        };
        assert_eq!(once, twice);
        assert_ne!(once, 0);
    }

    /// Distinct keys reach distinct slots, and the map round-trips.
    #[test]
    fn the_map_stores_and_reads_back() {
        let mut m: FxHashMap<u64, u32> = FxHashMap::default();
        for k in 0..1000u32 {
            m.insert(u64::from(k) * 7, k);
        }
        assert_eq!(m.len(), 1000);
        for k in 0..1000u32 {
            assert_eq!(m.get(&(u64::from(k) * 7)), Some(&k));
        }
        assert_eq!(m.get(&3), None);
    }

    /// One insertion sequence yields one iteration order, every time.
    #[test]
    fn iteration_order_is_reproducible() {
        let build = || -> Vec<u64> {
            let mut m: FxHashMap<u64, ()> = FxHashMap::default();
            for k in [9u64, 3, 27, 1, 81, 5, 243] {
                m.insert(k, ());
            }
            m.keys().copied().collect()
        };
        assert_eq!(build(), build());
    }
}
