//! The address sets the walk keeps: a dense bitmap of addresses and an
//! index of the code already covered.

use std::collections::BTreeSet;

use crate::analysis::{BasicBlock, Function};
use crate::num::from_usize;
use crate::program::Program;

/// Most bytes of address range an [`AddrSet`] or a [`Covered`] covers with
/// bits; a wider range spills into an ordered set or sorted spans instead.
const ADDR_BITS_MAX: u64 = 1 << 28;

/// A set of addresses: a bit per byte of the executable address range plus
/// an ordered spill set for everything else.
///
/// The walks test membership for every decoded instruction, jump and call
/// target and queue entry, so the bits keep those tests to one load; the
/// spill keeps addresses outside the range (or every address, when the
/// range is wider than [`ADDR_BITS_MAX`]) exact.
#[derive(Clone)]
pub(super) struct AddrSet {
    /// Address of bit 0.
    pub(super) base: u64,
    /// One bit per byte from `base`.
    pub(super) bits: Vec<u64>,
    /// Addresses outside the bit range.
    pub(super) spill: BTreeSet<u64>,
}

impl AddrSet {
    /// Sizes the bits to the executable, file-backed sections.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    pub(super) fn new(program: &Program) -> Self {
        let (lo, hi) = program
            .sections
            .iter()
            .filter(|s| s.executable && s.file_size > 0)
            .fold((u64::MAX, 0), |(lo, hi), s| {
                (
                    lo.min(s.va.0),
                    hi.max(s.va.0.saturating_add(s.vsize.max(s.file_size))),
                )
            });
        let span = hi.saturating_sub(lo);
        let words = if span > ADDR_BITS_MAX {
            0
        } else {
            usize::try_from(span.div_ceil(64)).unwrap_or(0)
        };
        Self {
            base: lo,
            bits: vec![0; words],
            spill: BTreeSet::new(),
        }
    }

    /// Locates the bit for `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    ///
    /// # Returns
    ///
    /// The word index and mask, or `None` when the bits do not cover `va`.
    pub(super) fn bit(&self, va: u64) -> Option<(usize, u64)> {
        let off = va.checked_sub(self.base)?;
        let word = usize::try_from(off / 64).ok()?;
        (word < self.bits.len()).then_some((word, 1u64 << (off % 64)))
    }

    /// Tells whether `va` is in the set.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    pub(super) fn contains(&self, va: u64) -> bool {
        match self.bit(va) {
            Some((w, m)) => self.bits.get(w).is_some_and(|b| b & m != 0),
            None => self.spill.contains(&va),
        }
    }

    /// Adds `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    pub(super) fn insert(&mut self, va: u64) {
        match self.bit(va) {
            Some((w, m)) => {
                if let Some(b) = self.bits.get_mut(w) {
                    *b |= m;
                }
            }
            None => {
                self.spill.insert(va);
            }
        }
    }

    /// Finds the first address in the set after `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    ///
    /// # Returns
    ///
    /// The address, or `None` when nothing in the set lies past `va`.
    pub(super) fn next_after(&self, va: u64) -> Option<u64> {
        let spilled = self.spill.range(va.saturating_add(1)..).next().copied();
        let Some(first) = va.saturating_add(1).checked_sub(self.base) else {
            return self
                .bits
                .iter()
                .enumerate()
                .find(|(_, w)| **w != 0)
                .map(|(i, w)| self.base + from_usize(i) * 64 + u64::from(w.trailing_zeros()))
                .into_iter()
                .chain(spilled)
                .min();
        };
        let mut word = usize::try_from(first / 64).unwrap_or(usize::MAX);
        let mut mask = u64::MAX << (first % 64);
        let mut found = None;
        while let Some(w) = self.bits.get(word) {
            let hit = w & mask;
            if hit != 0 {
                found = Some(self.base + from_usize(word) * 64 + u64::from(hit.trailing_zeros()));
                break;
            }
            word += 1;
            mask = u64::MAX;
        }
        found.into_iter().chain(spilled).min()
    }

    /// Adds every address of `iter`.
    ///
    /// # Arguments
    ///
    /// * `iter` - Any addresses.
    pub(super) fn extend<I: IntoIterator<Item = u64>>(&mut self, iter: I) {
        for va in iter {
            self.insert(va);
        }
    }

    /// Removes `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - Any address.
    pub(super) fn remove(&mut self, va: u64) {
        match self.bit(va) {
            Some((w, m)) => {
                if let Some(b) = self.bits.get_mut(w) {
                    *b &= !m;
                }
            }
            None => {
                self.spill.remove(&va);
            }
        }
    }
}

/// A half-open address range.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Span {
    /// First address.
    pub(super) start: u64,
    /// One past the last.
    pub(super) end: u64,
}

impl Span {
    /// The range a block covers.
    ///
    /// # Arguments
    ///
    /// * `b` - The block.
    fn of_block(b: &BasicBlock) -> Span {
        Span {
            start: b.start,
            end: b.end,
        }
    }
}

/// Index of the blocks found so far, by address.
///
/// A function's whole span would over-answer: a thunk the linker dropped
/// in a gap between two of a function's blocks would read as claimed, and
/// a function whose walk followed a jump into a shared block far away
/// would claim everything between. Whether an address is worth walking is
/// the finer question of whether any block covers it at all.
///
/// The index is a bit per byte from the lowest span's start to the highest
/// span's end, so a lookup is one load and a build is one pass with no sort:
/// a large program has millions of blocks, and discovery rebuilds the index
/// every seed round. Spans reaching wider than [`ADDR_BITS_MAX`], or an
/// empty span, are kept sorted instead, where an empty span still splits
/// the gap around it as it always did.
pub(super) struct Covered {
    /// Address of bit 0.
    base: u64,
    /// One bit per byte from `base`, set where a span covers it; empty when
    /// `spans` answers instead.
    bits: Vec<u64>,
    /// The spans sorted by start, each end raised to the farthest end at or
    /// before it; empty when `bits` answers.
    spans: Vec<Span>,
}

impl Covered {
    /// Builds the index from the functions found so far.
    ///
    /// # Arguments
    ///
    /// * `functions` - Functions in any order.
    pub(super) fn new(functions: &[Function]) -> Covered {
        Covered::from_spans(
            functions
                .iter()
                .flat_map(|f| f.blocks.iter().map(Span::of_block)),
        )
    }

    /// Adds a function's blocks to the bits.
    ///
    /// # Arguments
    ///
    /// * `blocks` - The blocks.
    ///
    /// # Returns
    ///
    /// `false` when the index cannot take them, as it was built would not
    /// have: it holds sorted spans, or a block is empty or reaches past the
    /// bits. The index is then partly updated and must be built again.
    pub(super) fn add(&mut self, blocks: &[BasicBlock]) -> bool {
        if !self.spans.is_empty() {
            return false;
        }
        let len = from_usize(self.bits.len()).saturating_mul(64);
        for b in blocks {
            let (Some(lo), Some(hi)) =
                (b.start.checked_sub(self.base), b.end.checked_sub(self.base))
            else {
                return false;
            };
            if hi <= lo || hi > len {
                return false;
            }
            set_range(&mut self.bits, lo, hi);
        }
        true
    }

    /// Builds the index from spans in any order, as bits when every span is
    /// non-empty and all of them fit [`ADDR_BITS_MAX`] bytes, else as the
    /// sorted spans.
    ///
    /// # Arguments
    ///
    /// * `spans` - The covered ranges, walked twice when they fit the bits.
    fn from_spans<I: Iterator<Item = Span> + Clone>(spans: I) -> Covered {
        let (lo, hi, empty) = spans.clone().fold((u64::MAX, 0, false), |(lo, hi, e), s| {
            (lo.min(s.start), hi.max(s.end), e || s.end <= s.start)
        });
        let words = usize::try_from(hi.saturating_sub(lo).div_ceil(64)).ok();
        if let Some(words) = words.filter(|_| !empty && hi.saturating_sub(lo) <= ADDR_BITS_MAX) {
            let mut bits = vec![0u64; words];
            for s in spans {
                set_range(&mut bits, s.start - lo, s.end - lo);
            }
            return Covered {
                base: lo,
                bits,
                spans: Vec::new(),
            };
        }
        let mut spans: Vec<Span> = spans.collect();
        spans.sort_unstable();
        let mut max_end = 0;
        for s in &mut spans {
            max_end = max_end.max(s.end);
            s.end = max_end;
        }
        Covered {
            base: 0,
            bits: Vec::new(),
            spans,
        }
    }

    /// Builds the index from the functions' ranges rather than their blocks.
    ///
    /// A function's range spans the alignment inside it - the `nop` run
    /// before a loop head, a jump table the compiler left between two
    /// blocks - and a seed placed there would walk part of the function as
    /// a function of its own.
    ///
    /// # Arguments
    ///
    /// * `functions` - Functions in any order.
    pub(super) fn ranges(functions: &[Function]) -> Covered {
        /// Widest gap between two of a function's blocks that its span
        /// still bridges: the alignment and jump tables inside a function.
        ///
        /// Past that the blocks are chunks apart - a PGO cold chunk, an
        /// `__except` handler moved to the section's end, a followed jump
        /// into a distant shared tail - and bridging them hid every
        /// function between from the seeds below: in 32-bit `KernelBase`, a
        /// quarter of all functions.
        const GAP_MAX: u64 = 0x1000;
        let mut spans: Vec<Span> = Vec::new();
        for f in functions {
            let mut chunk: Option<Span> = None;
            for b in f.blocks.iter().map(Span::of_block) {
                chunk = match chunk {
                    Some(c) if b.start <= c.end.saturating_add(GAP_MAX) => Some(Span {
                        start: c.start,
                        end: c.end.max(b.end),
                    }),
                    Some(done) => {
                        spans.push(done);
                        Some(b)
                    }
                    None => Some(b),
                };
            }
            spans.extend(chunk);
        }
        Covered::from_spans(spans.into_iter())
    }

    /// Lists the maximal ranges of `lo..hi` no block covers.
    ///
    /// # Arguments
    ///
    /// * `lo` - First address of the span.
    /// * `hi` - One past the last.
    ///
    /// # Returns
    ///
    /// The gaps in address order, each non-empty.
    pub(super) fn uncovered(&self, lo: u64, hi: u64) -> Vec<Span> {
        let mut gaps = Vec::new();
        if self.spans.is_empty() {
            let mut at = self.next(lo, hi, false);
            while at < hi {
                let end = self.next(at, hi, true);
                gaps.push(Span { start: at, end });
                at = self.next(end, hi, false);
            }
            return gaps;
        }
        let mut at = lo;
        let first = self.spans.partition_point(|s| s.end <= lo);
        for s in &self.spans[first..] {
            if s.start >= hi {
                break;
            }
            if s.start > at {
                gaps.push(Span {
                    start: at,
                    end: s.start.min(hi),
                });
            }
            at = at.max(s.end);
            if at >= hi {
                break;
            }
        }
        if at < hi {
            gaps.push(Span { start: at, end: hi });
        }
        gaps
    }

    /// Finds the first address of `from..hi` whose bit is `set`, over the
    /// bits.
    ///
    /// # Arguments
    ///
    /// * `from` - Where the search starts.
    /// * `hi` - One past the last address searched.
    /// * `set` - `true` for the first covered address, `false` for the
    ///   first uncovered one.
    ///
    /// # Returns
    ///
    /// The address, or `hi` when none of the range has it.
    fn next(&self, from: u64, hi: u64, set: bool) -> u64 {
        let mut va = from;
        while va < hi {
            let Some(off) = va.checked_sub(self.base) else {
                if !set {
                    return va;
                }
                va = self.base;
                continue;
            };
            let Some(&word) = usize::try_from(off / 64)
                .ok()
                .and_then(|w| self.bits.get(w))
            else {
                return if set { hi } else { va };
            };
            let hit = (if set { word } else { !word }) & (u64::MAX << (off % 64));
            if hit != 0 {
                return (va - off % 64 + u64::from(hit.trailing_zeros())).min(hi);
            }
            va = (va - off % 64).saturating_add(64);
        }
        hi
    }

    /// Tells whether `p` lies inside some indexed block.
    ///
    /// # Arguments
    ///
    /// * `p` - A virtual address.
    ///
    /// # Returns
    ///
    /// Whether a block starting at or before `p` reaches past it.
    pub(super) fn contains(&self, p: u64) -> bool {
        if self.spans.is_empty() {
            return p.checked_sub(self.base).is_some_and(|off| {
                usize::try_from(off / 64)
                    .ok()
                    .and_then(|w| self.bits.get(w))
                    .is_some_and(|w| w & (1 << (off % 64)) != 0)
            });
        }
        self.spans
            .partition_point(|s| s.start <= p)
            .checked_sub(1)
            .is_some_and(|i| self.spans.get(i).is_some_and(|s| s.end > p))
    }
}

/// Sets the bits of `lo..hi`, offsets from bit 0.
///
/// # Arguments
///
/// * `bits` - The bitmap, long enough for `hi`.
/// * `lo` - First offset set.
/// * `hi` - One past the last.
fn set_range(bits: &mut [u64], lo: u64, hi: u64) {
    let (first, last) = (lo / 64, (hi - 1) / 64);
    for w in first..=last {
        let from = if w == first { lo % 64 } else { 0 };
        let to = if w == last { (hi - 1) % 64 } else { 63 };
        let mask = (u64::MAX << from) & (u64::MAX >> (63 - to));
        if let Some(b) = usize::try_from(w).ok().and_then(|w| bits.get_mut(w)) {
            *b |= mask;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Covered, Span};
    use crate::analysis::{BasicBlock, BlockTerm};

    /// Returns the spans of a small fixed pseudo-random set, some
    /// overlapping, some nested, some touching.
    fn sample() -> Vec<Span> {
        let mut x: u64 = 0x9e37_79b9;
        (0..200)
            .map(|_| {
                x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                let start = 0x1000 + (x >> 33) % 0x2000;
                let len = 1 + (x >> 20) % 150;
                Span {
                    start,
                    end: start + len,
                }
            })
            .collect()
    }

    /// Returns the gaps of `lo..hi` byte by byte, the model the index must
    /// match.
    fn model(spans: &[Span], lo: u64, hi: u64) -> Vec<Span> {
        let mut gaps: Vec<Span> = Vec::new();
        for p in lo..hi {
            if spans.iter().any(|s| s.start <= p && p < s.end) {
                continue;
            }
            match gaps.last_mut() {
                Some(g) if g.end == p => g.end = p + 1,
                _ => gaps.push(Span {
                    start: p,
                    end: p + 1,
                }),
            }
        }
        gaps
    }

    /// The bits and the sorted spans give the gaps and the lookups a byte
    /// by byte model gives.
    ///
    /// # Panics
    ///
    /// When either index disagrees with the model.
    #[test]
    fn bits_and_sorted_spans_answer_alike() {
        let spans = sample();
        let bits = Covered::from_spans(spans.iter().copied());
        assert!(!bits.bits.is_empty() && bits.spans.is_empty());
        let far = Span {
            start: 1 << 40,
            end: (1 << 40) + 1,
        };
        let sorted = Covered::from_spans(spans.iter().copied().chain([far]));
        assert!(sorted.bits.is_empty());
        for (lo, hi) in [
            (0x800, 0x3400),
            (0x1003, 0x1777),
            (0x2fff, 0x9000),
            (0, 0x10),
        ] {
            let want = model(&spans, lo, hi);
            assert_eq!(bits.uncovered(lo, hi), want, "{lo:#x}..{hi:#x}");
            assert_eq!(sorted.uncovered(lo, hi), want, "{lo:#x}..{hi:#x}");
        }
        for p in 0xf00..0x3300 {
            let want = spans.iter().any(|s| s.start <= p && p < s.end);
            assert_eq!(bits.contains(p), want, "{p:#x}");
            assert_eq!(sorted.contains(p), want, "{p:#x}");
        }
    }

    /// An empty span is kept by the sorted index, where it splits the gap
    /// around it.
    ///
    /// # Panics
    ///
    /// When the bits are built or the gap is not split.
    #[test]
    fn an_empty_span_keeps_the_sorted_index() {
        let spans = [
            Span {
                start: 0x10,
                end: 0x20,
            },
            Span {
                start: 0x30,
                end: 0x30,
            },
        ];
        let c = Covered::from_spans(spans.iter().copied());
        assert!(c.bits.is_empty());
        assert_eq!(c.uncovered(0x20, 0x40).len(), 2);
    }

    /// An index of no spans covers nothing.
    ///
    /// # Panics
    ///
    /// When an address reads as covered.
    #[test]
    fn no_spans_cover_nothing() {
        let c = Covered::from_spans(std::iter::empty());
        assert!(!c.contains(0x1000));
        assert_eq!(
            c.uncovered(0x1000, 0x1010),
            vec![Span {
                start: 0x1000,
                end: 0x1010
            }]
        );
    }

    /// Blocks added to the bits answer as the bits built over every block
    /// at once, and a block the bits cannot take is refused.
    ///
    /// # Panics
    ///
    /// When the added index disagrees with the built one, or takes a block
    /// past its bits.
    #[test]
    fn added_blocks_answer_as_a_fresh_index() {
        let spans = sample();
        let (first, rest) = spans.split_at(120);
        let block = |s: &Span| BasicBlock {
            start: s.start,
            end: s.end,
            term: BlockTerm::Fall,
            successors: Vec::new(),
        };
        let mut grown = Covered::from_spans(first.iter().copied());
        let top = first.iter().map(|s| s.end).max().unwrap_or(0);
        let rest: Vec<BasicBlock> = rest
            .iter()
            .filter(|s| s.start >= grown.base && s.end <= top)
            .map(block)
            .collect();
        assert!(!rest.is_empty());
        assert!(grown.add(&rest));
        let all: Vec<Span> = first
            .iter()
            .copied()
            .chain(rest.iter().map(|b| Span {
                start: b.start,
                end: b.end,
            }))
            .collect();
        let fresh = Covered::from_spans(all.iter().copied());
        assert_eq!(
            grown.uncovered(0x800, 0x3400),
            fresh.uncovered(0x800, 0x3400)
        );
        let far = Span {
            start: 1 << 40,
            end: (1 << 40) + 1,
        };
        assert!(!grown.add(&[block(&far)]));
    }
}
