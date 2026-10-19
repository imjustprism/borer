//! Advanced SIMD lane operations for the arm64 machine.
//!
//! The bitwise selects, the narrowing shifts, the table lookups and the
//! byte-wise bit reversal and population count, every field read from the
//! word as the decoder leaves the arrangement operands unmodeled.

use super::{Machine, unmodeled};
use crate::emulate::{Stop, lo64, mask, sign_extend};
use crate::isa::a64::{Insn, Reg, Simd};
use crate::num::lo8;

/// Bytes in a `v` register.
const V_BYTES: usize = 16;

/// How a narrowing shift fits a lane to half its width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Saturate {
    /// Its low bits are kept.
    Cut,
    /// It is clamped to the signed range.
    Signed,
    /// It is clamped to the unsigned range.
    Unsigned,
}

/// The lanes of a narrowing shift: each lane of `src` twice `lane` wide,
/// shifted right, rounded where asked, and fitted to `lane` bits, packed
/// into the low 64 bits.
///
/// # Arguments
///
/// * `src` - The wide source register.
/// * `lane` - The narrow lane's width, 8 to 32.
/// * `shift` - The shift, 1 to `lane`.
/// * `sat` - How a lane is fitted to its width.
/// * `rounded` - Half the last place shifted out is added first.
pub(crate) fn narrow_lanes(src: u128, lane: u32, shift: u32, sat: Saturate, rounded: bool) -> u64 {
    let round = if rounded { 1i128 << (shift - 1) } else { 0 };
    let (lo, hi) = (-(1i128 << (lane - 1)), (1i128 << (lane - 1)) - 1);
    let mut half = 0u64;
    for k in 0..64 / lane {
        let x = mask(lo64(src >> (2 * k * lane)), 2 * lane);
        let signed = i128::from(sign_extend(x, 2 * lane));
        let v = match sat {
            Saturate::Signed => cut(((signed + round) >> shift).clamp(lo, hi), lane),
            Saturate::Unsigned => cut(
                ((i128::from(x) + round) >> shift).min((1i128 << lane) - 1),
                lane,
            ),
            Saturate::Cut => cut((i128::from(x) + round) >> shift, lane),
        };
        half |= v << (k * lane);
    }
    half
}

/// Returns the bytes of a table lookup.
///
/// Each of the index's first `span` bytes is looked up in the table, an
/// index past it reading zero or, given the old value (`tbx`), keeping
/// that byte; the bytes past `span` are zero.
///
/// # Arguments
///
/// * `table` - The table's bytes, sixteen per register.
/// * `index` - The index register.
/// * `old` - The destination's value for `tbx`, `None` for `tbl`.
/// * `span` - How many bytes are looked up, 8 or 16.
pub(crate) fn lookup(table: &[u8], index: u128, old: Option<u128>, span: usize) -> u128 {
    let keep = old.unwrap_or(0).to_le_bytes();
    let mut out = [0u8; V_BYTES];
    for ((o, at), k) in out.iter_mut().zip(index.to_le_bytes()).zip(keep).take(span) {
        *o = table.get(usize::from(at)).copied().unwrap_or(k);
    }
    u128::from_le_bytes(out)
}

/// The `v` register a vector word's field names.
///
/// # Arguments
///
/// * `w` - The encoded word.
/// * `at` - Where the register's number starts.
fn vreg(w: u32, at: u32) -> Reg {
    Reg::V(lo8(u64::from((w >> at) & 0x1f)))
}

/// The low `bits` of a wide intermediate, as the lane a narrowing keeps.
///
/// # Arguments
///
/// * `q` - The value.
/// * `bits` - The lane's width, 8 to 32.
fn cut(q: i128, bits: u32) -> u64 {
    u64::try_from(q & ((1i128 << bits) - 1)).unwrap_or(0)
}

impl Machine<'_> {
    /// Runs an Advanced SIMD lane operation the machine models.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - Which operation.
    ///
    /// # Errors
    ///
    /// An unmodeled stop for every other operation, and for a form or
    /// arrangement the operation is not modeled in.
    pub(super) fn simd(&mut self, i: &Insn, op: Simd) -> Result<(), Stop> {
        match op {
            Simd::Bsl => self.select_bits(i, |d, n, m| (d & n) | (!d & m)),
            Simd::Bit => self.select_bits(i, |d, n, m| (n & m) | (d & !m)),
            Simd::Bif => self.select_bits(i, |d, n, m| (n & !m) | (d & m)),
            Simd::Shrn => self.narrow(i, Saturate::Cut, false),
            Simd::Rshrn => self.narrow(i, Saturate::Cut, true),
            Simd::Sqshrn => self.narrow(i, Saturate::Signed, false),
            Simd::Sqrshrn => self.narrow(i, Saturate::Signed, true),
            Simd::Uqshrn => self.narrow(i, Saturate::Unsigned, false),
            Simd::Uqrshrn => self.narrow(i, Saturate::Unsigned, true),
            Simd::Tbl => self.table(i, false),
            Simd::Tbx => self.table(i, true),
            Simd::Cnt => self.bytewise(i, |b| lo8(u64::from(b.count_ones()))),
            Simd::Addv
            | Simd::Cmeq
            | Simd::Cmgt
            | Simd::Cmge
            | Simd::Cmhi
            | Simd::Cmhs
            | Simd::Cmle
            | Simd::Cmlt
            | Simd::Ushll
            | Simd::Sshll
            | Simd::Ext
            | Simd::Ins
            | Simd::Umov
            | Simd::Smin
            | Simd::Smax
            | Simd::Umin
            | Simd::Umax
            | Simd::Sminv
            | Simd::Smaxv
            | Simd::Uminv
            | Simd::Umaxv
            | Simd::Smlal
            | Simd::Umlal
            | Simd::Smull
            | Simd::Umull
            | Simd::Saddw
            | Simd::Uaddw
            | Simd::Addp
            | Simd::Mla => Err(unmodeled(i)),
        }
    }

    /// `bsl`, `bit` and `bif`: each bit taken from one source or the
    /// other by a mask, the destination itself the mask (`bsl`) or the
    /// bits kept where the second source's mask says (`bit`, `bif`); a
    /// 64-bit arrangement clears the upper half.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The select over the destination, the first source and the
    ///   second.
    ///
    /// # Errors
    ///
    /// Never; the decoder has already accepted the arrangement.
    fn select_bits(&mut self, i: &Insn, f: impl Fn(u128, u128, u128) -> u128) -> Result<(), Stop> {
        let w = i.word;
        let v = f(
            self.reg(vreg(w, 0)),
            self.reg(vreg(w, 5)),
            self.reg(vreg(w, 16)),
        );
        let span = if (w >> 30) & 1 == 1 { 128 } else { 64 };
        self.set_reg(vreg(w, 0), span, v);
        Ok(())
    }

    /// The narrowing shifts (`shrn`, `rshrn`, `sqshrn`, `sqrshrn`,
    /// `uqshrn`, `uqrshrn`): each lane of the source shifted right by the
    /// immediate, rounded where the mnemonic says, then cut or saturated
    /// to half its width. The plain form writes the lower half and clears
    /// the upper; the `2` form writes the upper half and keeps the lower.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `sat` - How a lane is fitted to half its width.
    /// * `rounded` - Half the last place shifted out is added first.
    ///
    /// # Errors
    ///
    /// For the scalar forms and an `immh` naming no lane width.
    fn narrow(&mut self, i: &Insn, sat: Saturate, rounded: bool) -> Result<(), Stop> {
        let w = i.word;
        if (w >> 28) & 1 == 1 {
            return Err(unmodeled(i));
        }
        let lane: u32 = match (w >> 19) & 0xf {
            1 => 8,
            2 | 3 => 16,
            4..=7 => 32,
            _ => return Err(unmodeled(i)),
        };
        let shift = 2 * lane - ((w >> 16) & 0x7f);
        let half = narrow_lanes(self.reg(vreg(w, 5)), lane, shift, sat, rounded);
        let d = vreg(w, 0);
        let v = if (w >> 30) & 1 == 1 {
            (self.reg(d) & u128::from(u64::MAX)) | (u128::from(half) << 64)
        } else {
            u128::from(half)
        };
        self.set_reg(d, 128, v);
        Ok(())
    }

    /// `tbl` and `tbx`: each byte of the index register looked up in a
    /// table of one to four consecutive registers, wrapping from `v31` to
    /// `v0`; an index past the table reads zero (`tbl`) or keeps the
    /// destination's byte (`tbx`). A 64-bit arrangement clears the upper
    /// half.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `extend` - The instruction is `tbx`.
    ///
    /// # Errors
    ///
    /// Never; the decoder has already accepted the arrangement.
    fn table(&mut self, i: &Insn, extend: bool) -> Result<(), Stop> {
        let w = i.word;
        let first = (w >> 5) & 0x1f;
        let table: Vec<u8> = (0..=(w >> 13) & 3)
            .flat_map(|k| {
                self.reg(Reg::V(lo8(u64::from((first + k) % 32))))
                    .to_le_bytes()
            })
            .collect();
        let span = if (w >> 30) & 1 == 1 {
            V_BYTES
        } else {
            V_BYTES / 2
        };
        let out = lookup(
            &table,
            self.reg(vreg(w, 16)),
            extend.then(|| self.reg(vreg(w, 0))),
            span,
        );
        self.set_reg(vreg(w, 0), 128, out);
        Ok(())
    }

    /// `rbit` (vector): the bits of each byte reversed; a 64-bit
    /// arrangement clears the upper half.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Errors
    ///
    /// Never; the decoder has already accepted the arrangement.
    pub(super) fn vector_rbit(&mut self, i: &Insn) -> Result<(), Stop> {
        self.bytewise(i, u8::reverse_bits)
    }

    /// A byte-wise operation over the source (`rbit`, `cnt`); a 64-bit
    /// arrangement clears the upper half.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on one byte.
    ///
    /// # Errors
    ///
    /// Never; the decoder has already accepted the arrangement.
    fn bytewise(&mut self, i: &Insn, f: impl Fn(u8) -> u8) -> Result<(), Stop> {
        let w = i.word;
        let bytes = self.reg(vreg(w, 5)).to_le_bytes().map(f);
        let span = if (w >> 30) & 1 == 1 { 128 } else { 64 };
        self.set_reg(vreg(w, 0), span, u128::from_le_bytes(bytes));
        Ok(())
    }
}
