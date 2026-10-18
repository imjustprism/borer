//! The address sets the walk keeps: a dense bitmap of addresses and the
//! sorted spans of code already covered.

use std::collections::BTreeSet;

use crate::analysis::{BasicBlock, Function};
use crate::num::from_usize;
use crate::program::Program;

/// Most bytes of executable address range an [`AddrSet`] covers with bits;
/// a wider range spills every address into the ordered set instead.
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
pub(super) struct Covered(Vec<Span>);

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
                .flat_map(|f| f.blocks.iter().map(Span::of_block))
                .collect(),
        )
    }

    /// Builds the index from spans in any order: sorted by start, each end
    /// raised to the farthest end at or before it, so a search over the
    /// starts answers whether anything covers an address.
    ///
    /// # Arguments
    ///
    /// * `spans` - The covered ranges.
    fn from_spans(mut spans: Vec<Span>) -> Covered {
        spans.sort_unstable();
        let mut max_end = 0;
        for s in &mut spans {
            max_end = max_end.max(s.end);
            s.end = max_end;
        }
        Covered(spans)
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
        Covered::from_spans(spans)
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
        let mut at = lo;
        let first = self.0.partition_point(|s| s.end <= lo);
        for s in &self.0[first..] {
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
        self.0
            .partition_point(|s| s.start <= p)
            .checked_sub(1)
            .is_some_and(|i| self.0.get(i).is_some_and(|s| s.end > p))
    }
}
