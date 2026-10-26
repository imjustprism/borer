//! What the code after a call does with the float a callee may leave in
//! xmm0.

use super::*;

/// What the code after a call does with xmm0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FloatUse {
    /// Read before anything writes it: the caller takes a float result,
    /// at the precision the reading instruction names, when it names one
    /// ([`xmm0_read_bits`]).
    Read(Option<u8>),
    /// Handed on by the caller's `ret`, untouched: taken exactly when the
    /// caller's own float result is (the caller's entry).
    Tail(u64),
    /// Written, clobbered by a call, or lost where the scan stops.
    Dropped,
}

/// The precision a scalar float instruction reads xmm0 at, in bits.
///
/// A conversion names its source after `cvt` or `cvtt` (`cvtss2sd` reads a
/// single); any other scalar instruction names it as its suffix (`movss`,
/// `addsd`). A packed or bit instruction names none.
///
/// # Arguments
///
/// * `i` - The instruction that reads xmm0.
fn xmm0_read_bits(i: &Instruction) -> Option<u8> {
    let name = format!("{:?}", i.mnemonic()).to_ascii_lowercase();
    let name = name
        .strip_prefix('v')
        .filter(|n| n.starts_with("cvt"))
        .unwrap_or(&name);
    let lane = match name
        .strip_prefix("cvtt")
        .or_else(|| name.strip_prefix("cvt"))
    {
        Some(rest) => rest.get(..2)?,
        None => name.get(name.len().checked_sub(2)?..)?,
    };
    match lane {
        "ss" => Some(32),
        "sd" => Some(64),
        _ => None,
    }
}

/// What the scans after a call read.
///
/// The image, the functions, and per function whether its blocks are in
/// order ([`blocks_ordered`]), worked out once rather than at each of a
/// large caller's thousands of call sites.
#[derive(Clone, Copy)]
pub(super) struct Sites<'a> {
    /// The image.
    pub(super) program: &'a Program,
    /// The functions and their cross-references.
    pub(super) analysis: &'a Analysis,
    /// Decoder bitness.
    pub(super) bitness: u32,
    /// Per function, in order, whether its blocks are in order; empty to
    /// work it out at each call.
    pub(super) ordered: &'a [bool],
}

impl<'a> Sites<'a> {
    /// Returns the scans' inputs with no order worked out ahead, for a
    /// caller that asks about a few call sites.
    ///
    /// # Arguments
    ///
    /// * `program` - The image.
    /// * `analysis` - The functions and their cross-references.
    /// * `bitness` - Decoder bitness.
    pub(super) fn unordered(program: &'a Program, analysis: &'a Analysis, bitness: u32) -> Self {
        Sites {
            program,
            analysis,
            bitness,
            ordered: &[],
        }
    }

    /// Returns the function holding `va` and whether its blocks are in
    /// order.
    ///
    /// # Arguments
    ///
    /// * `va` - The call site.
    ///
    /// # Returns
    ///
    /// The caller and its order, or `None` when no function holds `va`.
    pub(super) fn caller(&self, va: u64) -> Option<(&'a Function, bool)> {
        let f = self.analysis.function_at(va)?;
        let ordered = self
            .analysis
            .entry_index
            .get(&f.entry)
            .and_then(|&i| self.ordered.get(i))
            .copied()
            .unwrap_or_else(|| blocks_ordered(&f.blocks));
        Some((f, ordered))
    }
}

/// The instructions the scans after one call site decoded, by address, so
/// its scans for rax, rdx and xmm0 decode each instruction once.
///
/// Keyed by address, so a branch-heavy scan's lookups stay constant time;
/// it is only read by key, never walked, so its order never reaches an
/// answer.
#[derive(Default)]
pub(super) struct Decoded(crate::fxmap::FxHashMap<u64, Option<Instruction>>);

impl Decoded {
    /// Returns the instruction at `va` ([`decode_at`]), decoded the first
    /// time it is asked for.
    ///
    /// # Arguments
    ///
    /// * `sites` - The image.
    /// * `va` - The instruction's address.
    pub(super) fn at(&mut self, sites: &Sites<'_>, va: u64) -> Option<Instruction> {
        *self
            .0
            .entry(va)
            .or_insert_with(|| decode_at(sites.program, sites.bitness, va))
    }
}

/// Classifies what the code after the call at `call_va` does with xmm0.
///
/// The scan follows the return address, jumps within the caller, both
/// ways of a conditional branch, and calls to functions that hand xmm0
/// back untouched ([`preserves`]), [`SCAN_MAX`] instructions down each
/// path. A read of xmm0 on any path takes the result: xmm0 is volatile
/// across a call, so code reads it after one only for the result
/// (`test ebx, ebx; je; xorps xmm0, xmm5` negates it on one path). With no
/// read, a `ret` on some path hands it on; a write, another call or the
/// end of the scan drops it.
///
/// # Arguments
///
/// * `sites` - The image and the callers' blocks.
/// * `factory` - Reused instruction-info factory.
/// * `code` - What the site's other scans decoded.
/// * `call_va` - Address of the call instruction.
/// * `preserving` - Per function, in order, whether it hands xmm0 back
///   untouched.
pub(super) fn float_use(
    sites: &Sites<'_>,
    factory: &mut InstructionInfoFactory,
    code: &mut Decoded,
    call_va: u64,
    preserving: &[bool],
) -> FloatUse {
    let analysis = sites.analysis;
    let Some((caller, ordered)) = sites.caller(call_va) else {
        return FloatUse::Dropped;
    };
    let Some(call) = code.at(sites, call_va) else {
        return FloatUse::Dropped;
    };
    let within = |va: u64| block_holding(&caller.blocks, va, ordered).is_some();
    let preserves = |target: u64| {
        analysis
            .entry_index
            .get(&target)
            .is_some_and(|&i| preserving.get(i).copied().unwrap_or(false))
    };
    let (mut read, mut tail) = (None, false);
    let mut seen = BTreeSet::new();
    let mut paths = vec![(call.next_ip(), 0)];
    while let Some((mut va, mut walked)) = paths.pop() {
        while walked < SCAN_MAX && within(va) && seen.insert(va) {
            walked += 1;
            let Some(instr) = code.at(sites, va) else {
                break;
            };
            if reads_vector(factory, &instr, Register::ZMM0) {
                let bits = xmm0_read_bits(&instr);
                if bits.is_some() {
                    return FloatUse::Read(bits);
                }
                read = Some(bits);
                break;
            }
            if writes_xmm0(factory, &instr) {
                break;
            }
            let target = instr.near_branch_target();
            va = match instr.flow_control() {
                FlowControl::Next => instr.next_ip(),
                FlowControl::UnconditionalBranch if within(target) => target,
                FlowControl::ConditionalBranch => {
                    paths.push((target, walked));
                    instr.next_ip()
                }
                FlowControl::Call if preserves(target) => instr.next_ip(),
                FlowControl::Return => {
                    tail = true;
                    break;
                }
                FlowControl::UnconditionalBranch
                | FlowControl::IndirectBranch
                | FlowControl::Call
                | FlowControl::IndirectCall
                | FlowControl::Interrupt
                | FlowControl::Exception
                | FlowControl::XbeginXabortXend => break,
            };
        }
    }
    match (read, tail) {
        (Some(bits), _) => FloatUse::Read(bits),
        (None, true) => FloatUse::Tail(caller.entry),
        (None, false) => FloatUse::Dropped,
    }
}

/// Tells whether blocks are in address order, none empty and none reaching
/// into the next, as discovery builds a function's: then a block is found
/// by bisection ([`block_holding`]).
///
/// # Arguments
///
/// * `blocks` - A function's blocks.
pub(super) fn blocks_ordered(blocks: &[BasicBlock]) -> bool {
    blocks.iter().all(|b| b.start < b.end) && blocks.windows(2).all(|w| w[0].end <= w[1].start)
}

/// Returns the first of a function's blocks, in list order, that holds
/// `va`.
///
/// A function with thousands of blocks, asked once per instruction of every
/// call site's path, made a scan quadratic in the blocks.
///
/// # Arguments
///
/// * `blocks` - A function's blocks.
/// * `va` - Any address.
/// * `ordered` - What [`blocks_ordered`] says of the blocks: bisected when
///   `true`, scanned when `false`.
///
/// # Returns
///
/// The block, or `None` when no block holds `va`.
pub(super) fn block_holding(blocks: &[BasicBlock], va: u64, ordered: bool) -> Option<&BasicBlock> {
    if !ordered {
        return blocks.iter().find(|b| b.start <= va && va < b.end);
    }
    let i = blocks.partition_point(|b| b.start <= va).checked_sub(1)?;
    blocks.get(i).filter(|b| va < b.end)
}

/// Returns the first of a function's blocks, in list order, that starts at
/// `va`.
///
/// # Arguments
///
/// * `blocks` - A function's blocks.
/// * `va` - Any address.
/// * `ordered` - As for [`block_holding`].
///
/// # Returns
///
/// The block, or `None` when none starts at `va`.
pub(super) fn block_starting(blocks: &[BasicBlock], va: u64, ordered: bool) -> Option<&BasicBlock> {
    if !ordered {
        return blocks.iter().find(|b| b.start == va);
    }
    let i = blocks.binary_search_by_key(&va, |b| b.start).ok()?;
    blocks.get(i)
}

#[cfg(test)]
mod tests {
    use super::{block_holding, block_starting, blocks_ordered};
    use crate::analysis::{BasicBlock, BlockTerm};

    /// Returns blocks over the given spans.
    fn blocks(spans: &[(u64, u64)]) -> Vec<BasicBlock> {
        spans
            .iter()
            .map(|&(start, end)| BasicBlock {
                start,
                end,
                term: BlockTerm::Fall,
                successors: smallvec::SmallVec::new(),
            })
            .collect()
    }

    /// Bisection finds the block a scan finds, and a list it cannot bisect
    /// is scanned.
    ///
    /// # Panics
    ///
    /// When a lookup disagrees with the scan.
    #[test]
    fn bisected_blocks_are_the_scanned_ones() {
        let ordered = blocks(&[(0x10, 0x18), (0x18, 0x20), (0x30, 0x34)]);
        let overlapping = blocks(&[(0x10, 0x20), (0x14, 0x18), (0x30, 0x34)]);
        assert!(blocks_ordered(&ordered));
        assert!(!blocks_ordered(&overlapping));
        for b in [&ordered, &overlapping] {
            let o = blocks_ordered(b);
            for va in 0x08..0x40 {
                let scanned = b.iter().position(|x| x.start <= va && va < x.end);
                let started = b.iter().position(|x| x.start == va);
                let at = |x: &BasicBlock| b.iter().position(|y| std::ptr::eq(x, y));
                assert_eq!(block_holding(b, va, o).and_then(at), scanned, "{va:#x}");
                assert_eq!(block_starting(b, va, o).and_then(at), started, "{va:#x}");
            }
        }
    }
}
