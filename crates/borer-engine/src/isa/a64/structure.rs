//! The register list and memory layout of an Advanced SIMD structure load
//! or store, read from the word: the decoder leaves the list unmodeled.

use super::Reg;
use crate::num::lo8;

/// Bits 29 to 25 of every structure load and store.
const STRUCTURE_GROUP: u32 = 0b0_0110;

/// How a structure access lays its elements over its registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Layout {
    /// `ld1` and `st1` of whole registers: register `k` is the `k`th
    /// block of memory.
    Blocks,
    /// `ld2` to `ld4` and `st2` to `st4`: element `e` of register `k` lies
    /// `e * count + k` elements in.
    Interleaved,
    /// One lane of each register, by index: register `k`'s lies `k`
    /// elements in, and a load keeps every other lane.
    Lane(u8),
    /// `ld1r` to `ld4r`: register `k`'s element, `k` elements in, loaded
    /// into every lane.
    Replicate,
}

/// The registers and memory an `ld1`..`ld4` or `st1`..`st4` word moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Structure {
    /// The first register's number, 0 to 31.
    pub first: u8,
    /// How many consecutive registers, one to four, wrapping from `v31`
    /// to `v0`.
    pub count: u8,
    /// The element width in bits, 8 to 64.
    pub elem: u16,
    /// Each register is moved whole; otherwise its low 64 bits, a load
    /// clearing the rest. A lane form is whole.
    pub whole: bool,
    /// How the elements lie.
    pub layout: Layout,
}

/// One element a structure access moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Slot {
    /// The register, counted from [`Structure::first`].
    pub reg: u8,
    /// The lane of that register.
    pub lane: u32,
    /// Where the element lies, in bytes from the address.
    pub at: u64,
}

impl Structure {
    /// Returns the `k`th register of the list.
    ///
    /// # Arguments
    ///
    /// * `k` - The offset from the first, 0 to 3.
    #[must_use]
    pub fn reg(&self, k: u8) -> Reg {
        Reg::V(self.first.wrapping_add(k) % 32)
    }

    /// Returns how many lanes of [`Structure::elem`] one register holds.
    #[must_use]
    pub fn lanes(&self) -> u32 {
        (if self.whole { 128 } else { 64 }) / u32::from(self.elem)
    }

    /// Returns how many bytes the access moves, the step a post-indexed
    /// form's immediate takes.
    #[must_use]
    pub fn bytes(&self) -> u64 {
        let elems = match self.layout {
            Layout::Blocks | Layout::Interleaved => self.lanes(),
            Layout::Lane(_) | Layout::Replicate => 1,
        };
        u64::from(self.count) * u64::from(elems) * u64::from(self.elem / 8)
    }

    /// Returns every element the access moves, register by register.
    ///
    /// # Returns
    ///
    /// The slots: every lane of each register, but one lane each for
    /// [`Layout::Lane`]. A replicated element is listed once per lane, all
    /// at the same place.
    #[must_use]
    pub fn slots(&self) -> Vec<Slot> {
        let lanes = self.lanes();
        let bytes = u64::from(self.elem / 8);
        let count = u32::from(self.count);
        let mut out = Vec::with_capacity(usize::from(self.count) * 16);
        for k in 0..self.count {
            let kk = u32::from(k);
            let mut put = |lane: u32, elems: u32| {
                out.push(Slot {
                    reg: k,
                    lane,
                    at: u64::from(elems) * bytes,
                });
            };
            match self.layout {
                Layout::Blocks => (0..lanes).for_each(|e| put(e, kk * lanes + e)),
                Layout::Interleaved => (0..lanes).for_each(|e| put(e, e * count + kk)),
                Layout::Lane(index) => put(u32::from(index), kk),
                Layout::Replicate => (0..lanes).for_each(|e| put(e, kk)),
            }
        }
        out
    }
}

/// Reads the register list and layout of a structure load or store.
///
/// # Arguments
///
/// * `word` - The encoded word.
///
/// # Returns
///
/// The structure; `None` for a word outside the structure loads and
/// stores, or one of their reserved encodings.
#[must_use]
pub fn structure(word: u32) -> Option<Structure> {
    if word >> 31 != 0 || (word >> 25) & 0x1f != STRUCTURE_GROUP {
        return None;
    }
    let whole = (word >> 30) & 1 == 1;
    let size = (word >> 10) & 3;
    let first = lo8(u64::from(word & 0x1f));
    if (word >> 24) & 1 == 0 {
        let (count, layout) = match (word >> 12) & 0xf {
            0b0000 => (4, Layout::Interleaved),
            0b0010 => (4, Layout::Blocks),
            0b0100 => (3, Layout::Interleaved),
            0b0110 => (3, Layout::Blocks),
            0b0111 => (1, Layout::Blocks),
            0b1000 => (2, Layout::Interleaved),
            0b1010 => (2, Layout::Blocks),
            _ => return None,
        };
        if layout == Layout::Interleaved && size == 3 && !whole {
            return None;
        }
        return Some(Structure {
            first,
            count,
            elem: 8u16 << size,
            whole,
            layout,
        });
    }
    let opcode = (word >> 13) & 7;
    let s = (word >> 12) & 1;
    let load = (word >> 22) & 1 == 1;
    let count = lo8(u64::from((((opcode & 1) << 1) | ((word >> 21) & 1)) + 1));
    let index = (u32::from(whole) << 3) | (s << 2) | size;
    let lane = |shift: u32| Layout::Lane(lo8(u64::from(index >> shift)));
    let (elem, layout) = match opcode >> 1 {
        0 => (8, lane(0)),
        1 if size & 1 == 0 => (16, lane(1)),
        2 if size == 0 => (32, lane(2)),
        2 if size == 1 && s == 0 => (64, lane(3)),
        3 if s == 0 && load => (8u16 << size, Layout::Replicate),
        _ => return None,
    };
    Some(Structure {
        first,
        count,
        elem,
        whole: whole || layout != Layout::Replicate,
        layout,
    })
}
