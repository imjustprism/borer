//! Address-ordered basic-block ownership index ([`super::Analysis::block_at`]).

use std::cmp::Reverse;
use std::collections::BTreeSet;

use super::{BasicBlock, Function};

/// One disjoint virtual-address stretch and the block that owns all of it.
#[derive(Debug, Clone, Copy)]
pub(super) struct BlockRow {
    /// First virtual address of the stretch.
    start: u64,
    /// One past its last virtual address.
    end: u64,
    /// Index of the owning function in [`super::Analysis::functions`].
    func: u32,
    /// Index of the owning block in that function's [`Function::blocks`].
    block: u32,
}

/// Ordering key of an active span: entry ascending, then lowest function and
/// block indexes last so a range ceiling picks them first.
type SpanKey = (u64, Reverse<u32>, Reverse<u32>);

/// Finds the function and basic block whose decoded instructions cover `va`.
///
/// # Arguments
///
/// * `functions` - The discovered functions.
/// * `index` - Disjoint rows built by [`index_blocks`].
/// * `va` - Any virtual address.
///
/// # Returns
///
/// The owning function and block, or `None` when no discovered block holds `va`.
pub(super) fn block_in<'f>(
    functions: &'f [Function],
    index: &[BlockRow],
    va: u64,
) -> Option<(&'f Function, &'f BasicBlock)> {
    let i = index.partition_point(|r| r.start <= va).checked_sub(1)?;
    let r = index.get(i).filter(|r| va < r.end)?;
    let f = functions.get(usize::try_from(r.func).ok()?)?;
    let b = f.blocks.get(usize::try_from(r.block).ok()?)?;
    Some((f, b))
}

/// Builds the disjoint, address-ordered block table from `functions`.
///
/// Non-overlapping blocks pass straight through after one sort; overlapping
/// runs are split at their boundaries, picking at each stretch the active
/// owner with the highest entry at or below it, else the lowest entry.
///
/// # Arguments
///
/// * `functions` - The discovered functions.
///
/// # Returns
///
/// Non-overlapping [`BlockRow`]s sorted by `start`.
pub(super) fn index_blocks(functions: &[Function]) -> Vec<BlockRow> {
    let mut spans = Vec::with_capacity(functions.iter().map(|f| f.blocks.len()).sum());
    for (fi, f) in functions.iter().enumerate() {
        let Ok(func) = u32::try_from(fi) else {
            break;
        };
        for (bi, b) in f.blocks.iter().enumerate() {
            let Ok(block) = u32::try_from(bi) else {
                break;
            };
            if b.start >= b.end {
                continue;
            }
            if b.start < f.entry && f.entry < b.end {
                spans.push(BlockRow {
                    start: b.start,
                    end: f.entry,
                    func,
                    block,
                });
                spans.push(BlockRow {
                    start: f.entry,
                    end: b.end,
                    func,
                    block,
                });
            } else {
                spans.push(BlockRow {
                    start: b.start,
                    end: b.end,
                    func,
                    block,
                });
            }
        }
    }
    spans.sort_unstable_by_key(|r| (r.start, r.end, r.func, r.block));
    if spans.windows(2).all(|w| w[0].end <= w[1].start) {
        spans.dedup_by(|next, prev| {
            let merge =
                prev.end == next.start && prev.func == next.func && prev.block == next.block;
            if merge {
                prev.end = next.end;
            }
            merge
        });
        spans.shrink_to_fit();
        return spans;
    }
    let mut out = Vec::with_capacity(spans.len());
    let mut i = 0;
    while let Some(&first) = spans.get(i) {
        let mut reach = first.end;
        let mut j = i + 1;
        while let Some(&next) = spans.get(j).filter(|r| r.start < reach) {
            reach = reach.max(next.end);
            j += 1;
        }
        if j == i + 1 {
            push_row(&mut out, first);
        } else {
            sweep_cluster(functions, &spans[i..j], &mut out);
        }
        i = j;
    }
    out.shrink_to_fit();
    out
}

/// Resolves one overlapping cluster of block spans into disjoint rows.
///
/// # Arguments
///
/// * `functions` - The discovered functions, for their entry addresses.
/// * `cluster` - Overlapping spans sorted by `start`.
/// * `out` - Receives the disjoint winning rows in address order.
fn sweep_cluster(functions: &[Function], cluster: &[BlockRow], out: &mut Vec<BlockRow>) {
    let key_of = |r: BlockRow| {
        let entry = usize::try_from(r.func)
            .ok()
            .and_then(|i| functions.get(i))
            .map_or(0, |f| f.entry);
        (entry, Reverse(r.func), Reverse(r.block))
    };
    let mut events = Vec::with_capacity(cluster.len().saturating_mul(2));
    for &r in cluster {
        let key = key_of(r);
        events.push((r.end, false, key));
        events.push((r.start, true, key));
    }
    events.sort_unstable();
    let mut live = BTreeSet::new();
    let mut at = None;
    for group in events.chunk_by(|a, b| a.0 == b.0) {
        let Some(&(next, ..)) = group.first() else {
            continue;
        };
        if let Some(lo) = at
            && let Some((_, Reverse(func), Reverse(block))) = winner_at(lo, &live)
        {
            push_row(
                out,
                BlockRow {
                    start: lo,
                    end: next,
                    func,
                    block,
                },
            );
        }
        for &(_, open, key) in group {
            if open {
                live.insert(key);
            } else {
                live.remove(&key);
            }
        }
        at = Some(next);
    }
}

/// Picks the winning active span at `va`: highest `entry <= va`, else lowest
/// `entry`, breaking ties by lowest function and block index.
///
/// # Arguments
///
/// * `va` - Start of the elementary stretch.
/// * `live` - Active spans covering the stretch.
///
/// # Returns
///
/// The winning key, or `None` when `live` is empty.
fn winner_at(va: u64, live: &BTreeSet<SpanKey>) -> Option<SpanKey> {
    let at_or_below = |cap: u64| {
        live.range(..=(cap, Reverse(0), Reverse(0)))
            .next_back()
            .copied()
    };
    at_or_below(va).or_else(|| live.first().and_then(|&(entry, ..)| at_or_below(entry)))
}

/// Appends `row` to `out`, merging when it continues the same block.
///
/// # Arguments
///
/// * `out` - Disjoint rows built so far.
/// * `row` - Next non-empty stretch in address order.
fn push_row(out: &mut Vec<BlockRow>, row: BlockRow) {
    match out.last_mut() {
        Some(last) if last.end == row.start && last.func == row.func && last.block == row.block => {
            last.end = row.end;
        }
        Some(_) | None => out.push(row),
    }
}
