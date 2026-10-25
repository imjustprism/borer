//! The search for a state that tells a claim's two sides apart.

use std::collections::BTreeMap;

use super::super::super::expr::Key;
use super::super::super::verify::{FRAME_SPAN, low};
use super::super::Witness;
use super::super::term::{self, Point};
use super::Claimed;
use crate::fxmap::FxHashMap;
use crate::num::from_usize;

/// States tried per claim whose two sides differ, looking for one that
/// tells them apart.
const SEARCH_POINTS: u64 = 192;

/// What the search adds to a value it starts from: nothing, or the sign
/// bit of a byte, a word, a doubleword or a quadword, so a value that
/// agrees with a constant only in its low bits is tried too.
const SIGNS: [u64; 6] = [0, 0, 1 << 7, 1 << 15, 1 << 31, 1 << 63];

/// The stack a replayed function owns, where no variable starts.
///
/// It runs from [`FRAME_SPAN`] below a block's stack pointer, through the
/// frame the function allocates after its entry, up past the return
/// address, the shadow space its convention gives it and the stack slots
/// the text names above them (its stack arguments).
///
/// The frame's addresses are constants of the terms (the replay's stack
/// pointer is fixed), so the search would start variables at them, but
/// no state the replay draws does: a caller cannot pass the address of a
/// frame allocated after the call, nor of the return address and the
/// arguments it hands over, and the sampled states draw variables at
/// random or from the block's own constants. A pointer into the frame
/// that the lift keeps as a bare variable, its tie to the stack pointer
/// lost, stays outside what the replay checks, in the samples and the
/// proof alike.
#[derive(Debug, Clone, Copy)]
pub(super) struct Owned {
    /// The lowest address.
    lo: u64,
    /// Bytes from `lo` to the first the function does not own.
    len: u64,
    /// The mask of the register width.
    mask: u64,
}

impl Owned {
    /// Returns the stack owned at a block whose stack pointer is `rsp` at
    /// its start, in a function entered with `sp0`.
    ///
    /// # Arguments
    ///
    /// * `rsp` - The stack pointer at the block's start.
    /// * `sp0` - The stack pointer at the function's entry.
    /// * `w` - The function's witness: its convention and named slots.
    /// * `mask` - The mask of the register width.
    pub(super) fn of(rsp: u64, sp0: u64, w: &Witness, mask: u64) -> Self {
        let named = w
            .slot_bits
            .iter()
            .map(|(&o, &bits)| o.saturating_add(i64::from(bits / 8)))
            .max()
            .unwrap_or(0);
        let above = named
            .max(w.conv.word.saturating_add(w.conv.shadow))
            .cast_unsigned();
        let lo = rsp.wrapping_sub(FRAME_SPAN) & mask;
        Self {
            lo,
            len: sp0.wrapping_add(above).wrapping_sub(lo) & mask,
            mask,
        }
    }

    /// Tells whether an address lies in the stack the function owns.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn holds(self, at: u64) -> bool {
        (at.wrapping_sub(self.lo) & self.mask) < self.len
    }
}

/// Looks for a state in which two terms differ in their low bits.
///
/// The variables start next to the constants the terms are built with,
/// at zero, one and the signed and unsigned limits, or at random; a state
/// in which one starts inside the function's own frame ([`Owned`]) is not
/// tried.
///
/// # Arguments
///
/// * `c` - The claim.
/// * `width` - The register width.
/// * `owned` - The function's own frame.
///
/// # Returns
///
/// The variables' values in such a state, if one is found.
pub(super) fn search(c: &Claimed, width: u8, owned: Owned) -> Option<FxHashMap<Key, u64>> {
    let mut inputs = BTreeMap::new();
    c.text.inputs(&mut inputs);
    c.machine.inputs(&mut inputs);
    let mut consts = Vec::new();
    c.text.constants(&mut consts);
    c.machine.constants(&mut consts);
    let mut near: Vec<u64> = vec![0, 1, u64::MAX, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff];
    for k in consts {
        near.extend([k, k.wrapping_add(1), k.wrapping_sub(1), k.wrapping_neg()]);
    }
    near.sort_unstable();
    near.dedup();
    let len = from_usize(near.len()).max(1);
    for p in 0..SEARCH_POINTS {
        let ins: FxHashMap<Key, u64> = inputs
            .iter()
            .zip(0u64..)
            .map(|((k, bits), j)| {
                let h = splitmix(p.wrapping_mul(0x9e37) ^ j.rotate_left(17));
                let v = if p > 0 && h & 3 == 0 {
                    h
                } else {
                    near[usize::try_from((h >> 2) % len).unwrap_or(0)]
                };
                let lift = SIGNS[usize::try_from((h >> 3) % from_usize(SIGNS.len())).unwrap_or(0)];
                (*k, v.wrapping_add(lift) & low(*bits))
            })
            .collect();
        if ins.values().any(|v| owned.holds(*v)) {
            continue;
        }
        let at = Point {
            ins: &ins,
            seed: splitmix(p),
            width,
        };
        if let (Some(x), Some(y)) = (term::value(&c.text, &at), term::value(&c.machine, &at))
            && (x ^ y) & low(c.bits) != 0
        {
            return Some(ins);
        }
    }
    None
}

/// Mixes bits for the search's draws.
///
/// # Arguments
///
/// * `x` - The input.
fn splitmix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}
