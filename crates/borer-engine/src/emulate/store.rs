//! The bytes a run holds over the program image, eight to an entry.
//!
//! A map with an entry per byte cost tens of bytes of map for every byte a
//! run wrote, so one `rep stos` filling the memory cap took over a
//! gigabyte. Eight neighbouring bytes share an entry here, with a bit each
//! for whether the byte is held and whether the run wrote it outside the
//! stack: a filled cap takes tens of megabytes, and a byte written alone
//! costs no more than its own map entry did. Iteration is in address order,
//! as the per-byte map's was.

use std::collections::BTreeMap;
use std::ops::Range;

use crate::num::lo8;

/// Eight neighbouring bytes: the addresses that agree in all but the low
/// three bits.
#[derive(Debug, Clone, Copy, Default)]
struct Chunk {
    /// The bytes, by the low three bits of their address.
    bytes: [u8; 8],
    /// Bit `k` set: byte `k` is held.
    held: u8,
    /// Bit `k` set: the run wrote byte `k` outside the stack; always a
    /// subset of `held`.
    dirty: u8,
}

/// The bytes a run holds, by address, and which of them it wrote outside
/// the stack.
#[derive(Debug, Clone, Default)]
pub(super) struct Store {
    /// Chunks by address shifted right three bits.
    chunks: BTreeMap<u64, Chunk>,
    /// Bytes held: the set `held` bits of every chunk.
    len: usize,
}

/// The chunk key of an address and the position of its byte in the chunk.
///
/// # Arguments
///
/// * `a` - The address.
fn place(a: u64) -> (u64, u8) {
    (a >> 3, lo8(a) & 7)
}

/// The address of byte `k` of the chunk at `key`.
///
/// # Arguments
///
/// * `key` - The chunk's key.
/// * `k` - The byte's position, 0 to 7.
fn address(key: u64, k: u8) -> u64 {
    (key << 3) | u64::from(k)
}

impl Store {
    /// How many bytes are held.
    pub(super) fn len(&self) -> usize {
        self.len
    }

    /// The byte held at `a`, or `None` when none is.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    pub(super) fn get(&self, a: u64) -> Option<u8> {
        let (key, k) = place(a);
        let c = self.chunks.get(&key)?;
        (c.held & (1 << k) != 0).then_some(c.bytes[usize::from(k)])
    }

    /// Whether a byte is held at `a`.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    pub(super) fn contains(&self, a: u64) -> bool {
        self.get(a).is_some()
    }

    /// Holds `v` at `a`, marking it written outside the stack when `dirty`.
    ///
    /// A byte once marked stays marked when it is set again without the
    /// mark, as an address once in a set stays there.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    /// * `v` - The byte.
    /// * `dirty` - Whether the run wrote it outside the stack.
    pub(super) fn set(&mut self, a: u64, v: u8, dirty: bool) {
        let (key, k) = place(a);
        let bit = 1 << k;
        let c = self.chunks.entry(key).or_default();
        if c.held & bit == 0 {
            self.len += 1;
        }
        c.held |= bit;
        if dirty {
            c.dirty |= bit;
        }
        c.bytes[usize::from(k)] = v;
    }

    /// Whether the run wrote the byte at `a` outside the stack.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    pub(super) fn is_dirty(&self, a: u64) -> bool {
        let (key, k) = place(a);
        self.chunks
            .get(&key)
            .is_some_and(|c| c.dirty & (1 << k) != 0)
    }

    /// Whether any byte in `range` was written outside the stack.
    ///
    /// # Arguments
    ///
    /// * `range` - The addresses, start included, end excluded.
    pub(super) fn any_dirty(&self, range: Range<u64>) -> bool {
        if range.is_empty() {
            return false;
        }
        let (first, _) = place(range.start);
        let (last, _) = place(range.end - 1);
        self.chunks.range(first..=last).any(|(&key, c)| {
            (0..8).any(|k| c.dirty & (1 << k) != 0 && range.contains(&address(key, k)))
        })
    }

    /// How many bytes are held at addresses below `limit`.
    ///
    /// # Arguments
    ///
    /// * `limit` - The first address not counted.
    pub(super) fn held_below(&self, limit: u64) -> usize {
        self.chunks
            .range(..=place(limit).0)
            .map(|(&key, c)| {
                (0..8)
                    .filter(|&k| c.held & (1 << k) != 0 && address(key, k) < limit)
                    .count()
            })
            .sum()
    }

    /// The addresses written outside the stack, in order.
    pub(super) fn dirty(&self) -> impl Iterator<Item = u64> + '_ {
        self.chunks.iter().flat_map(|(&key, c)| {
            (0..8)
                .filter(move |&k| c.dirty & (1 << k) != 0)
                .map(move |k| address(key, k))
        })
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::Store;

    /// A filled block takes one entry per eight bytes, where a map of
    /// single bytes took one per byte, and reads back byte for byte.
    #[test]
    fn a_filled_block_takes_an_entry_per_eight_bytes() {
        let mut s = Store::default();
        for a in 0x1000..0x1400u64 {
            s.set(a, crate::num::lo8(a), true);
        }
        assert_eq!(s.len(), 0x400);
        assert_eq!(s.chunks.len(), 0x80);
        assert!((0x1000..0x1400u64).all(|a| s.get(a) == Some(crate::num::lo8(a))));
        assert_eq!(s.get(0xfff), None);
        assert_eq!(s.get(0x1400), None);
    }

    /// Setting a held byte again does not count it twice, and a byte once
    /// marked written stays marked when it is set again unmarked.
    #[test]
    fn a_byte_is_counted_and_marked_once() {
        let mut s = Store::default();
        s.set(0x2003, 1, true);
        s.set(0x2003, 2, false);
        assert_eq!(s.len(), 1);
        assert_eq!(s.get(0x2003), Some(2));
        assert!(s.is_dirty(0x2003));
        assert!(!s.is_dirty(0x2004));
        assert!(s.contains(0x2003));
        assert!(!s.contains(0x2002));
    }

    /// The written bytes come out in address order, a window finds one
    /// only inside it, and the count below a limit stops at the limit,
    /// whatever chunk the limit falls in.
    #[test]
    fn written_bytes_are_ordered_and_windowed() {
        let mut s = Store::default();
        for a in [0x3009u64, 0x3001, 0x5000, 0x3002, u64::MAX] {
            s.set(a, 0, true);
        }
        s.set(0x3004, 0, false);
        assert_eq!(
            s.dirty().collect::<Vec<_>>(),
            [0x3001, 0x3002, 0x3009, 0x5000, u64::MAX]
        );
        assert!(s.any_dirty(0x3009..0x300a));
        assert!(!s.any_dirty(0x3003..0x3009));
        assert!(!s.any_dirty(0x3004..0x3004));
        assert!(!s.any_dirty(u64::MAX - 3..u64::MAX));
        assert_eq!(s.held_below(0x3004), 2);
        assert_eq!(s.held_below(0x3005), 3);
        assert_eq!(s.held_below(0x5001), 5);
        assert_eq!(s.held_below(u64::MAX), 5);
    }
}
