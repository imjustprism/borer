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
use std::ops::{Range, RangeBounds};
use std::sync::Arc;

use crate::num::{from_usize, lo8};

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
    /// Bit `k` set: byte `k` was set up before the run ([`Store::poke`]);
    /// always a subset of `held`. Kept apart from `dirty` so a deliberate
    /// patch is not reported as code the program unpacked, while still
    /// being fetched as code: an experiment that nops a check out has to
    /// see the nops execute.
    patched: u8,
}

/// The bytes a run holds, by address, and which of them it wrote outside
/// the stack.
///
/// The chunks a machine was set up with can be frozen into a layer its
/// clones share ([`Store::freeze`]): a replay clones one set-up machine
/// for every trial of every block, and copying the planted loader each
/// time cost more than the trial. A chunk the run changes is copied up
/// into the store's own layer first, which then hides the shared one.
#[derive(Debug, Clone, Default)]
pub(super) struct Store {
    /// Chunks by address shifted right three bits, shared between clones;
    /// a key in [`Store::chunks`] hides the one here.
    base: Arc<BTreeMap<u64, Chunk>>,
    /// Chunks by address shifted right three bits, this store's own.
    chunks: BTreeMap<u64, Chunk>,
    /// Bytes held: the set `held` bits of every chunk either layer shows.
    len: usize,
    /// The address the bytes held below are counted at as they are held
    /// ([`Store::split_at`]), zero when they are not.
    split: u64,
    /// Bytes held below [`Store::split`].
    below: usize,
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
    /// Returns an empty store that counts the bytes it holds below `split`
    /// as it holds them, so [`Store::held_below`] answers for that address
    /// without a walk.
    ///
    /// A machine asks how much it holds below its stack at the end of every
    /// run, and a 32-bit one plants its thread block and loader there:
    /// walking them took longer than a short run.
    ///
    /// # Arguments
    ///
    /// * `split` - The address.
    pub(super) fn split_at(split: u64) -> Self {
        Self {
            split,
            ..Self::default()
        }
    }

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
        let c = self.chunk(key)?;
        (c.held & (1 << k) != 0).then_some(c.bytes[usize::from(k)])
    }

    /// The chunk at `key` as the store shows it: its own, else the shared
    /// one.
    ///
    /// # Arguments
    ///
    /// * `key` - The chunk's key.
    fn chunk(&self, key: u64) -> Option<&Chunk> {
        self.chunks.get(&key).or_else(|| self.base.get(&key))
    }

    /// The chunks at `keys` as the store shows them, in key order.
    ///
    /// # Arguments
    ///
    /// * `keys` - The chunk keys.
    fn shown(&self, keys: impl RangeBounds<u64> + Clone) -> impl Iterator<Item = (u64, &Chunk)> {
        let mut shared = self.base.range(keys.clone()).peekable();
        let mut own = self.chunks.range(keys).peekable();
        std::iter::from_fn(move || {
            let next = match (shared.peek(), own.peek()) {
                (Some(s), Some(o)) => match s.0.cmp(o.0) {
                    std::cmp::Ordering::Less => shared.next(),
                    std::cmp::Ordering::Greater => own.next(),
                    std::cmp::Ordering::Equal => {
                        shared.next();
                        own.next()
                    }
                },
                (Some(_), None) => shared.next(),
                (None, _) => own.next(),
            };
            next.map(|(&key, c)| (key, c))
        })
    }

    /// Moves every chunk into the layer clones share, so a clone copies
    /// none of them until it changes one.
    pub(super) fn freeze(&mut self) {
        let own = std::mem::take(&mut self.chunks);
        if self.base.is_empty() {
            self.base = Arc::new(own);
        } else {
            Arc::make_mut(&mut self.base).extend(own);
        }
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
        let base = &self.base;
        let c = self
            .chunks
            .entry(key)
            .or_insert_with(|| base.get(&key).copied().unwrap_or_default());
        if c.held & bit == 0 {
            self.len += 1;
            self.below += usize::from(a < self.split);
        }
        c.held |= bit;
        if dirty {
            c.dirty |= bit;
        }
        c.bytes[usize::from(k)] = v;
    }

    /// Holds a run of bytes from `at` on as [`Store::set`] does each one
    /// unmarked, looking each chunk up once rather than once per byte.
    ///
    /// The emulator's setup plants pages of zeros and every imported name
    /// before a run, and a map lookup per byte made building a machine
    /// cost milliseconds.
    ///
    /// # Arguments
    ///
    /// * `at` - The address of the first byte; later ones follow it,
    ///   wrapping at the top of the address space.
    /// * `bytes` - The bytes, in address order.
    pub(super) fn plant(&mut self, at: u64, bytes: impl IntoIterator<Item = u8>) {
        self.plant_marked(at, bytes, false);
    }

    /// Holds a byte set up before a run: as [`Store::set`] unmarked, and
    /// marked patched.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    /// * `v` - The byte.
    pub(super) fn poke(&mut self, a: u64, v: u8) {
        self.plant_marked(a, [v], true);
    }

    /// Holds a run of bytes set up before a run, as [`Store::poke`] does
    /// each one, looking each chunk up once.
    ///
    /// A store that holds none of its own yet (a clone of a frozen machine,
    /// as a replay sets up every trial) builds its layer from the run in
    /// one pass, reading the shared chunks the run covers in one walk:
    /// a lookup and an insert per chunk was most of a trial's setup.
    ///
    /// # Arguments
    ///
    /// * `at` - The address of the first byte; later ones follow it,
    ///   wrapping at the top of the address space.
    /// * `bytes` - The bytes, in address order.
    pub(super) fn poke_run(&mut self, at: u64, bytes: &[u8]) {
        let end = at.checked_add(from_usize(bytes.len()));
        let (Some(end), true, false) = (end, self.chunks.is_empty(), bytes.is_empty()) else {
            self.plant_marked(at, bytes.iter().copied(), true);
            return;
        };
        let (first, _) = place(at);
        let (last, _) = place(end - 1);
        let mut shared = self.base.range(first..=last).peekable();
        let mut fresh: Vec<(u64, Chunk)> = Vec::new();
        for (&v, i) in bytes.iter().zip(0u64..) {
            let (key, k) = place(at + i);
            if fresh.last().is_none_or(|(held, _)| *held != key) {
                while shared.next_if(|(s, _)| **s < key).is_some() {}
                let c = shared
                    .next_if(|(s, _)| **s == key)
                    .map_or_else(Chunk::default, |(_, c)| *c);
                fresh.push((key, c));
            }
            let Some((_, c)) = fresh.last_mut() else {
                continue;
            };
            let bit = 1 << k;
            if c.held & bit == 0 {
                self.len += 1;
                self.below += usize::from(at + i < self.split);
            }
            c.held |= bit;
            c.patched |= bit;
            c.bytes[usize::from(k)] = v;
        }
        self.chunks = fresh.into_iter().collect();
    }

    /// Holds a run of bytes unmarked as written, marked patched when
    /// `patched`.
    ///
    /// # Arguments
    ///
    /// * `at` - The address of the first byte; later ones follow it,
    ///   wrapping at the top of the address space.
    /// * `bytes` - The bytes, in address order.
    /// * `patched` - Whether they were set up before the run.
    fn plant_marked(&mut self, at: u64, bytes: impl IntoIterator<Item = u8>, patched: bool) {
        let Self {
            base,
            chunks,
            len,
            split,
            below,
        } = self;
        let mut a = at;
        let mut slot: Option<(u64, &mut Chunk)> = None;
        for v in bytes {
            let (key, k) = place(a);
            a = a.wrapping_add(1);
            if slot.as_ref().is_none_or(|(held, _)| *held != key) {
                slot = Some((
                    key,
                    chunks
                        .entry(key)
                        .or_insert_with(|| base.get(&key).copied().unwrap_or_default()),
                ));
            }
            let Some((_, c)) = slot.as_mut() else {
                continue;
            };
            let bit = 1 << k;
            if c.held & bit == 0 {
                *len += 1;
                *below += usize::from(address(key, k) < *split);
            }
            c.held |= bit;
            if patched {
                c.patched |= bit;
            }
            c.bytes[usize::from(k)] = v;
        }
    }

    /// Whether the run wrote the byte at `a` outside the stack.
    ///
    /// # Arguments
    ///
    /// * `a` - The address.
    pub(super) fn is_dirty(&self, a: u64) -> bool {
        let (key, k) = place(a);
        self.chunk(key).is_some_and(|c| c.dirty & (1 << k) != 0)
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
        self.shown(first..=last).any(|(key, c)| {
            (0..8).any(|k| c.dirty & (1 << k) != 0 && range.contains(&address(key, k)))
        })
    }

    /// Whether any byte in `range` was set up before the run.
    ///
    /// # Arguments
    ///
    /// * `range` - The addresses, start included, end excluded.
    pub(super) fn any_patched(&self, range: Range<u64>) -> bool {
        if range.is_empty() {
            return false;
        }
        let (first, _) = place(range.start);
        let (last, _) = place(range.end - 1);
        self.shown(first..=last).any(|(key, c)| {
            (0..8).any(|k| c.patched & (1 << k) != 0 && range.contains(&address(key, k)))
        })
    }

    /// How many bytes are held at addresses below `limit`: the count kept
    /// as they were held when `limit` is the store's split
    /// ([`Store::split_at`]), else a walk of the chunks below it.
    ///
    /// # Arguments
    ///
    /// * `limit` - The first address not counted.
    pub(super) fn held_below(&self, limit: u64) -> usize {
        if limit == self.split {
            return self.below;
        }
        self.shown(..=place(limit).0)
            .map(|(key, c)| {
                (0..8)
                    .filter(|&k| c.held & (1 << k) != 0 && address(key, k) < limit)
                    .count()
            })
            .sum()
    }

    /// The addresses written outside the stack, in order.
    pub(super) fn dirty(&self) -> impl Iterator<Item = u64> + '_ {
        self.shown(..).flat_map(|(key, c)| {
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

    /// A planted run holds what setting each byte unmarked holds: the
    /// same bytes, count and marks, across chunk edges, over bytes already
    /// held and marked, and wrapping at the top of the address space.
    #[test]
    fn a_planted_run_holds_what_setting_each_byte_holds() {
        let mut by_byte = Store::default();
        let mut planted = Store::default();
        for s in [&mut by_byte, &mut planted] {
            s.set(0x4005, 9, true);
            s.set(0x4011, 7, false);
        }
        let run: Vec<u8> = (0..30u8).collect();
        for (k, &v) in run.iter().enumerate() {
            by_byte.set(0x4003 + crate::num::from_usize(k), v, false);
        }
        planted.plant(0x4003, run.iter().copied());
        for (k, v) in [(u64::MAX - 1, 1u8), (u64::MAX, 2), (0, 3), (1, 4)] {
            by_byte.set(k, v, false);
        }
        planted.plant(u64::MAX - 1, [1, 2, 3, 4]);
        assert_eq!(planted.len(), by_byte.len());
        assert_eq!(planted.chunks.len(), by_byte.chunks.len());
        for (a, b) in planted.chunks.iter().zip(&by_byte.chunks) {
            assert_eq!(a.0, b.0);
            assert_eq!(
                (a.1.bytes, a.1.held, a.1.dirty),
                (b.1.bytes, b.1.held, b.1.dirty)
            );
        }
        assert!(planted.is_dirty(0x4005));
    }

    /// A frozen store and its clones read, count and mark exactly as the
    /// store would unfrozen, and a clone's writes reach neither the store
    /// nor its other clones.
    #[test]
    fn a_frozen_store_answers_as_it_would_unfrozen() {
        let mut plain = Store::default();
        plain.plant(0x6000, (0..40u8).map(|v| v + 1));
        plain.set(0x6100, 5, true);
        let mut frozen = plain.clone();
        frozen.freeze();
        let pristine = frozen.clone();
        let mut writes: Vec<(u64, u8, bool)> = vec![(0x6003, 9, true), (0x6027, 8, false)];
        writes.extend([(0x6200, 7, true), (0x6100, 6, false), (0x5fff, 4, false)]);
        let mut copy = frozen.clone();
        for &(a, v, d) in &writes {
            plain.set(a, v, d);
            copy.set(a, v, d);
        }
        copy.plant(0x6010, [0xaa, 0xbb]);
        plain.plant(0x6010, [0xaa, 0xbb]);
        assert_eq!(copy.len(), plain.len());
        for a in 0x5ff0..0x6210u64 {
            assert_eq!(copy.get(a), plain.get(a), "{a:#x}");
            assert_eq!(copy.is_dirty(a), plain.is_dirty(a), "{a:#x}");
        }
        assert_eq!(
            copy.dirty().collect::<Vec<_>>(),
            plain.dirty().collect::<Vec<_>>()
        );
        for limit in [0x6000u64, 0x6004, 0x6028, 0x6101, u64::MAX] {
            assert_eq!(copy.held_below(limit), plain.held_below(limit));
        }
        assert!(copy.any_dirty(0x6003..0x6004));
        assert!(!copy.any_dirty(0x6004..0x6100));
        assert_eq!(pristine.get(0x6003), Some(4));
        assert!(!pristine.is_dirty(0x6003));
        assert_eq!(frozen.get(0x6200), None);
    }

    /// A store split at an address counts the bytes it holds below it as a
    /// walk of its chunks counts them, through plants, sets, a freeze, and
    /// a clone's poked run and pokes over the frozen layer.
    #[test]
    fn a_split_store_counts_below_its_split_as_a_walk_does() {
        let split = 0x6004;
        let (mut counted, mut walked) = (Store::split_at(split), Store::default());
        for s in [&mut counted, &mut walked] {
            s.plant(0x5ff8, (0..24u8).map(|v| v + 1));
            s.set(0x6100, 5, true);
            s.set(0x5000, 1, false);
            s.freeze();
        }
        let (mut copy, mut walked_copy) = (counted.clone(), walked.clone());
        for s in [&mut copy, &mut walked_copy] {
            s.poke_run(0x5ff0, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
            s.poke(0x4fff, 9);
            s.set(0x6003, 4, true);
            s.plant(0x6000, [1, 2, 3, 4, 5, 6]);
        }
        assert_eq!(counted.held_below(split), 13);
        assert_eq!(walked.held_below(split), 13);
        assert_eq!(copy.held_below(split), 22);
        assert_eq!(walked_copy.held_below(split), 22);
        assert_eq!(copy.held_below(0x6100), walked_copy.held_below(0x6100));
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
