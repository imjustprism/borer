//! Data processing for the arm64 machine: moves, adds and subtracts with
//! their flags, logic, bitfields, multiplies, conditional selects and
//! compares, and the scalar vector moves.
//!
//! Each handler reads its operands at the width of its destination, as
//! the architecture's `datasize`, so a `w` operation computes in 32 bits
//! and its write zero-extends ([`Machine::set_reg`]). The flags follow the
//! pseudocode exactly: an add's carry is its carry out, a subtract's is
//! not-borrow, and the logical forms clear carry and overflow.

use super::{Machine, lo32_count, mask_wide, unmodeled};
use crate::emulate::{Stop, lo64, mask, rotate_right, sign_extend};
use crate::isa::a64::{Insn, Opnd, Reg, Shift};
use crate::num::lo8;

/// The fixed bits of `fmov` (scalar, immediate), as `(mask, value)`: the
/// one `fmov` whose source is an immediate and whose destination is a
/// scalar register.
// SPEC: Arm ARM (DDI 0487) C7.2 FMOV (scalar, immediate): 0001 1110 ty 1 imm8 100 00000 Rd.
pub(crate) const FMOV_IMM: (u32, u32) = (0xff20_1fe0, 0x1e20_1000);

/// Each byte's low bit, for replicating a byte across a doubleword.
const BYTES: u64 = 0x0101_0101_0101_0101;

/// Each halfword's low bit, for replicating a halfword across a doubleword.
const HALVES: u64 = 0x0001_0001_0001_0001;

/// How an add or subtract forms its second operand and its carry in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Form {
    /// `x + y`.
    Add,
    /// `x - y`, computed as `x + !y + 1`, so the carry out is not-borrow.
    Sub,
    /// `x + y + C`.
    Adc,
    /// `x - y - !C`, computed as `x + !y + C`.
    Sbc,
}

/// How a move-wide instruction combines its shifted immediate with the
/// register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Wide {
    /// `movz`: the immediate alone.
    Zero,
    /// `movn`: its inverse.
    Not,
    /// `movk`: the immediate over the register's other bits.
    Keep,
}

/// The four condition flags one result sets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Flags {
    /// Negative: the result's top bit.
    n: bool,
    /// Zero: the result is zero.
    z: bool,
    /// Carry: unsigned carry out.
    c: bool,
    /// Overflow: signed overflow.
    v: bool,
}

impl Machine<'_> {
    /// Sets the flags.
    ///
    /// # Arguments
    ///
    /// * `f` - The new flags.
    fn apply(&mut self, f: Flags) {
        (self.n, self.z, self.c, self.v) = (f.n, f.z, f.c, f.v);
    }

    /// Reads a source operand as an integer at the operation's width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The operand's position.
    /// * `width` - The operation's width in bits, 32 or 64.
    ///
    /// # Returns
    ///
    /// A register at its own width, a shifted or extended register after
    /// its shift or extension, or an immediate, each masked to `width`.
    ///
    /// # Errors
    ///
    /// When the operand is no general register or immediate.
    fn source(&self, i: &Insn, k: usize, width: u32) -> Result<u64, Stop> {
        match i.operands.get(k).copied().unwrap_or(Opnd::None) {
            Opnd::Reg {
                reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
                bits,
            } => Ok(mask(lo64(mask_wide(self.reg(reg), bits)), width)),
            Opnd::Shifted {
                reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
                bits,
                shift,
                amount,
            } => Ok(shifted(
                lo64(self.reg(reg)),
                u32::from(bits),
                shift,
                amount,
                width,
            )),
            Opnd::Imm(v) => Ok(mask(v, width)),
            Opnd::Reg { .. }
            | Opnd::Shifted { .. }
            | Opnd::None
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => Err(unmodeled(i)),
        }
    }

    /// `movz`, `movn` and `movk`.
    ///
    /// The immediate and its shift are read from the word: the decoder
    /// folds the shift into the immediate, which loses it when the
    /// immediate is zero, and `movk` needs it to know which bits to keep.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `form` - How the immediate combines with the register.
    ///
    /// # Errors
    ///
    /// When a 32-bit form shifts by 32 or 48, which is unallocated.
    pub(super) fn move_wide(&mut self, i: &Insn, form: Wide) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        // SPEC: Arm ARM (DDI 0487) C6.2 MOVZ/MOVN/MOVK: imm16 is bits 5..20 and hw bits 21..22, shifting by hw * 16.
        let pos = ((i.word >> 21) & 3) * 16;
        if pos >= u32::from(bits) {
            return Err(unmodeled(i));
        }
        let imm = u64::from((i.word >> 5) & 0xffff) << pos;
        let v = match form {
            Wide::Zero => imm,
            Wide::Not => !imm,
            Wide::Keep => (lo64(self.reg(rd)) & !(0xffff << pos)) | imm,
        };
        self.set_reg(rd, bits, u128::from(v));
        Ok(())
    }

    /// An instruction of one source: `f(source, width)` into the
    /// destination.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn unary(&mut self, i: &Insn, f: impl Fn(u64, u32) -> u64) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let v = f(self.source(i, 1, width)?, width);
        self.set_reg(rd, bits, u128::from(mask(v, width)));
        Ok(())
    }

    /// An instruction of two sources: `f(x, y, width)` into the
    /// destination.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn binary(
        &mut self,
        i: &Insn,
        f: impl Fn(u64, u64, u32) -> u64,
    ) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let v = f(self.source(i, 1, width)?, self.source(i, 2, width)?, width);
        self.set_reg(rd, bits, u128::from(mask(v, width)));
        Ok(())
    }

    /// `add`, `sub`, `adc` and `sbc`, and their flag-setting forms, over
    /// an immediate, a shifted register or an extended register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `form` - How the second operand and the carry in are formed.
    /// * `flags` - Whether the instruction sets the flags (its `S` bit).
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn arith(&mut self, i: &Insn, form: Form, flags: bool) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let (x, y) = (self.source(i, 1, width)?, self.source(i, 2, width)?);
        let (v, f) = self.add_form(x, y, form, width);
        if flags {
            self.apply(f);
        }
        self.set_reg(rd, bits, u128::from(v));
        Ok(())
    }

    /// The result and flags of an add or subtract.
    ///
    /// # Arguments
    ///
    /// * `x` - The first operand.
    /// * `y` - The second, before [`Form`] inverts it.
    /// * `form` - The form.
    /// * `width` - The width in bits.
    fn add_form(&self, x: u64, y: u64, form: Form, width: u32) -> (u64, Flags) {
        match form {
            Form::Add => add_with_carry(x, y, false, width),
            Form::Sub => add_with_carry(x, !y, true, width),
            Form::Adc => add_with_carry(x, y, self.c, width),
            Form::Sbc => add_with_carry(x, !y, self.c, width),
        }
    }

    /// `and`, `orr`, `eor`, `orn`, `eon`, `bic` and the flag-setting
    /// `ands` and `bics`, over a bitmask immediate or a shifted register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on the two operands.
    /// * `flags` - Whether it sets the flags: N and Z from the result, C
    ///   and V cleared.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn logical(
        &mut self,
        i: &Insn,
        f: impl Fn(u64, u64) -> u64,
        flags: bool,
    ) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let v = mask(
            f(self.source(i, 1, width)?, self.source(i, 2, width)?),
            width,
        );
        if flags {
            self.apply(Flags {
                n: (v >> (width - 1)) & 1 == 1,
                z: v == 0,
                c: false,
                v: false,
            });
        }
        self.set_reg(rd, bits, u128::from(v));
        Ok(())
    }

    /// `ubfm`, `sbfm` and `bfm` and their aliases (`lsl`, `lsr`, `asr`,
    /// `ubfx`, `sbfiz`, `bfi`, `sxtw`, ...).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, source, `immr`, `imms`.
    /// * `f` - The field operation: `(old destination, source, immr, imms,
    ///   width)`.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or a field position is out of the
    /// width.
    pub(super) fn bitfield(
        &mut self,
        i: &Insn,
        f: fn(u64, u64, u32, u32, u32) -> u64,
    ) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let src = self.source(i, 1, width)?;
        let (r, s) = (lo32_count(self.int(i, 2)?), lo32_count(self.int(i, 3)?));
        if r >= width || s >= width {
            return Err(unmodeled(i));
        }
        let old = mask(lo64(self.reg(rd)), width);
        self.set_reg(rd, bits, u128::from(mask(f(old, src, r, s, width), width)));
        Ok(())
    }

    /// `extr`, and `ror` by an immediate: the `width` bits of `Rn:Rm`
    /// starting at bit `lsb`.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, `Rn`, `Rm`, `lsb`.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or `lsb` is out of the width.
    pub(super) fn extract(&mut self, i: &Insn) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let (hi, lo) = (self.source(i, 1, width)?, self.source(i, 2, width)?);
        let lsb = lo32_count(self.int(i, 3)?);
        if lsb >= width {
            return Err(unmodeled(i));
        }
        let v = if lsb == 0 {
            lo
        } else {
            (lo >> lsb) | (hi << (width - lsb))
        };
        self.set_reg(rd, bits, u128::from(mask(v, width)));
        Ok(())
    }

    /// `madd`, `msub` and the long forms `smaddl`, `smsubl`, `umaddl` and
    /// `umsubl` (and their aliases `mul`, `smull`, `umull`, ...):
    /// `f(n, m, a)` into the destination.
    ///
    /// Each source is read at its own width, so a long form's `w`
    /// multiplicands arrive zero-extended for `f` to extend as it means.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, `Rn`, `Rm`, `Ra`.
    /// * `f` - The operation.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn multiply(
        &mut self,
        i: &Insn,
        f: impl Fn(u64, u64, u64) -> u64,
    ) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let v = f(self.int(i, 1)?, self.int(i, 2)?, self.int(i, 3)?);
        self.set_reg(rd, bits, u128::from(v));
        Ok(())
    }

    /// `csel`, `csinc`, `csinv` and `csneg` (and `cset`, `cinc`, `cneg`,
    /// ...): `Rn` when the condition holds, else `f(Rm)`.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, `Rn`, `Rm`, condition.
    /// * `f` - What the second source becomes when the condition fails.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn select(&mut self, i: &Insn, f: impl Fn(u64) -> u64) -> Result<(), Stop> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let Opnd::Cond(cond) = i.operands[3] else {
            return Err(unmodeled(i));
        };
        let v = if self.holds(cond) {
            self.source(i, 1, width)?
        } else {
            f(self.source(i, 2, width)?)
        };
        self.set_reg(rd, bits, u128::from(mask(v, width)));
        Ok(())
    }

    /// `ccmp` and `ccmn`: the flags of a compare when the condition holds,
    /// else the immediate flags.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rn`, `Rm` or a five-bit immediate, the
    ///   `nzcv` immediate, the condition.
    /// * `form` - [`Form::Sub`] for `ccmp`, [`Form::Add`] for `ccmn`.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn compare_if(&mut self, i: &Insn, form: Form) -> Result<(), Stop> {
        let Opnd::Reg { bits, .. } = i.operands[0] else {
            return Err(unmodeled(i));
        };
        let width = u32::from(bits);
        let Opnd::Cond(cond) = i.operands[3] else {
            return Err(unmodeled(i));
        };
        if self.holds(cond) {
            let (x, y) = (self.source(i, 0, width)?, self.source(i, 1, width)?);
            let (_, f) = self.add_form(x, y, form, width);
            self.apply(f);
        } else {
            self.set_nzcv(self.int(i, 2)? << 28);
        }
        Ok(())
    }

    /// `fmov` between registers, general and floating-point alike, and
    /// of a scalar immediate.
    ///
    /// A move between registers copies the source's bits at its width and
    /// zero-extends them into the destination. The immediate is read from
    /// the word: the decoder expands it to a double whatever the width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Errors
    ///
    /// For the vector forms, the lane forms (`fmov v0.d[1], x1`), and any
    /// other operand.
    pub(super) fn fmov(&mut self, i: &Insn) -> Result<(), Stop> {
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return Err(unmodeled(i));
        };
        match i.operands[1] {
            Opnd::Reg { reg, bits: from } => {
                self.set_reg(dst, bits, mask_wide(self.reg(reg), from));
                Ok(())
            }
            Opnd::Other if matches!(dst, Reg::V(_)) && i.word & FMOV_IMM.0 == FMOV_IMM.1 => {
                let v = vfp_expand((i.word >> 13) & 0xff, bits).ok_or_else(|| unmodeled(i))?;
                self.set_reg(dst, bits, u128::from(v));
                Ok(())
            }
            Opnd::Other
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => Err(unmodeled(i)),
        }
    }

    /// `movi` and `mvni`: an expanded immediate into a whole `v` register,
    /// replicated into the upper half for a 128-bit arrangement and zero
    /// there for a 64-bit one.
    ///
    /// Every field is read from the word: the decoder does not keep the
    /// arrangement of the destination.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `invert` - Whether the immediate is inverted (`mvni`).
    ///
    /// # Errors
    ///
    /// For an encoding that expands to a floating-point immediate.
    pub(super) fn movi(&mut self, i: &Insn, invert: bool) -> Result<(), Stop> {
        // SPEC: Arm ARM (DDI 0487) C7.2 MOVI/MVNI: Rd bits 0..4, d:e:f:g:h bits 5..9, cmode bits 12..15, a:b:c bits 16..18, op bit 29, Q bit 30.
        let w = i.word;
        let imm8 = u64::from((((w >> 16) & 7) << 5) | ((w >> 5) & 0x1f));
        let imm = expand_imm((w >> 29) & 1, (w >> 12) & 0xf, imm8).ok_or_else(|| unmodeled(i))?;
        let imm = u128::from(if invert { !imm } else { imm });
        let v = if (w >> 30) & 1 == 1 {
            (imm << 64) | imm
        } else {
            imm
        };
        self.set_reg(Reg::V(lo8(u64::from(w & 0x1f))), 128, v);
        Ok(())
    }

    /// `and`, `orr`, `eor` and `bic` (vector, register and immediate forms):
    /// the operation over the whole registers, the upper half zero for a
    /// 64-bit arrangement.
    ///
    /// Every field is read from the word: the arrangement operands stay
    /// unmodeled, and the immediate form (`orr`/`bic` only) combines with
    /// the destination it reads as the register at bits 0 to 4.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on the two values.
    ///
    /// # Errors
    ///
    /// For the immediate forms' `cmode`, which [`expand_imm`] refuses.
    // SPEC: Arm ARM (DDI 0487) C7.2 AND/ORR/EOR/BIC (vector): Rd bits 0..4,
    // Rn bits 5..9, Rm bits 16..20, Q bit 30; the immediate forms share
    // movi's imm8 and cmode fields, op bit 29 and cmode's low bit naming
    // the operation in place of the move.
    pub(super) fn vector_logical(
        &mut self,
        i: &Insn,
        f: impl Fn(u128, u128) -> u128,
    ) -> Result<(), Stop> {
        let w = i.word;
        let vreg = |at: u32| Reg::V(lo8(u64::from((w >> at) & 0x1f)));
        let (x, y) = match i.operands[1] {
            Opnd::Other => (self.reg(vreg(5)), self.reg(vreg(16))),
            Opnd::Imm(_) => {
                let imm8 = u64::from((((w >> 16) & 7) << 5) | ((w >> 5) & 0x1f));
                let imm =
                    expand_imm((w >> 29) & 1, (w >> 12) & 0xf, imm8).ok_or_else(|| unmodeled(i))?;
                let imm = u128::from(imm);
                let span = if (w >> 30) & 1 == 1 {
                    (imm << 64) | imm
                } else {
                    imm
                };
                (self.reg(vreg(0)), span)
            }
            Opnd::Reg { .. }
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => return Err(unmodeled(i)),
        };
        let v = f(x, y);
        let v = if (w >> 30) & 1 == 1 {
            v
        } else {
            v & u128::from(u64::MAX)
        };
        self.set_reg(vreg(0), 128, v);
        Ok(())
    }

    /// `dup`: one lane's value replicated through a whole `v` register, the
    /// upper half zero for a 64-bit arrangement.
    ///
    /// Every field is read from the word: the general form takes the low
    /// lane bits of a general register, the element form the lane `imm5`
    /// names of a `v` register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Errors
    ///
    /// When `imm5` names no lane width.
    // SPEC: Arm ARM (DDI 0487) C7.2 DUP: imm5 bits 16..20, its lowest set
    /// bit naming the element size and the bits above it the index; Q bit 30.
    pub(super) fn dup(&mut self, i: &Insn) -> Result<(), Stop> {
        let w = i.word;
        let imm5 = (w >> 16) & 0x1f;
        let Some(shift) = (0..4).find(|&s| imm5 >> s & 1 == 1) else {
            return Err(unmodeled(i));
        };
        let lane = 8u16 << shift;
        let index = imm5 >> (shift + 1);
        let lane_value = match i.operands[1] {
            Opnd::Reg { reg, .. } => mask(lo64(self.reg(reg)), u32::from(lane)),
            _ => {
                let at = index * u32::from(lane);
                mask(
                    lo64(self.reg(Reg::V(lo8(u64::from((w >> 5) & 0x1f)))) >> at),
                    u32::from(lane),
                )
            }
        };
        let span = if (w >> 30) & 1 == 1 { 128 } else { 64 };
        let v = (0..u32::from(span / lane)).fold(0u128, |acc, k| {
            acc | u128::from(lane_value) << (k * u32::from(lane))
        });
        self.set_reg(Reg::V(lo8(u64::from(w & 0x1f))), 128, v);
        Ok(())
    }
}

/// The destination of a data-processing instruction: operand 0 as a
/// general register or the stack pointer, with its width.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Errors
///
/// When operand 0 is anything else, a `v` register among them.
fn dest(i: &Insn) -> Result<(Reg, u16), Stop> {
    match i.operands[0] {
        Opnd::Reg {
            reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
            bits: bits @ (32 | 64),
        } => Ok((reg, bits)),
        Opnd::Reg { .. }
        | Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => Err(unmodeled(i)),
    }
}

/// Shifts or extends a register operand, then masks it to the operation's
/// width.
///
/// # Arguments
///
/// * `raw` - The register's value.
/// * `from` - The width it is read at, 32 or 64.
/// * `shift` - The shift or extension.
/// * `amount` - The shift, or the left shift after an extension.
/// * `width` - The operation's width.
pub(super) fn shifted(raw: u64, from: u32, shift: Shift, amount: u8, width: u32) -> u64 {
    let raw = mask(raw, from);
    let by = u32::from(amount);
    let left = |v: u64| v.checked_shl(by).unwrap_or(0);
    let v = match shift {
        Shift::Lsl | Shift::Uxtx | Shift::Sxtx => left(raw),
        Shift::Lsr => raw.checked_shr(by).unwrap_or(0),
        Shift::Asr => (sign_extend(raw, from) >> by.min(63)).cast_unsigned(),
        Shift::Ror => rotate_right(raw, by, from),
        Shift::Uxtb => left(raw & 0xff),
        Shift::Uxth => left(raw & 0xffff),
        Shift::Uxtw => left(raw & 0xffff_ffff),
        Shift::Sxtb => left(sign_extend(raw, 8).cast_unsigned()),
        Shift::Sxth => left(sign_extend(raw, 16).cast_unsigned()),
        Shift::Sxtw => left(sign_extend(raw, 32).cast_unsigned()),
    };
    mask(v, width)
}

/// Adds two values and a carry at a width, with the flags the sum sets.
///
/// # Arguments
///
/// * `x` - The first operand.
/// * `y` - The second.
/// * `carry` - The carry in.
/// * `width` - The width in bits, 32 or 64.
///
/// # Returns
///
/// The sum masked to `width`, and its flags: C is the unsigned carry out
/// of the top bit, V the signed overflow.
// SPEC: Arm ARM (DDI 0487) J1, AddWithCarry.
fn add_with_carry(x: u64, y: u64, carry: bool, width: u32) -> (u64, Flags) {
    let (x, y) = (mask(x, width), mask(y, width));
    let wide = u128::from(x) + u128::from(y) + u128::from(carry);
    let v = mask(lo64(wide), width);
    let signed =
        i128::from(sign_extend(x, width)) + i128::from(sign_extend(y, width)) + i128::from(carry);
    (
        v,
        Flags {
            n: (v >> (width - 1)) & 1 == 1,
            z: v == 0,
            c: wide >> width != 0,
            v: signed != i128::from(sign_extend(v, width)),
        },
    )
}

/// `ubfm`: the field `src<s:r>` at bit 0 when `s >= r`, else `src<s:0>`
/// at bit `width - r`; the rest zero.
///
/// # Arguments
///
/// * `_old` - The destination before, which `ubfm` does not read.
/// * `src` - The source.
/// * `r` - `immr`, below `width`.
/// * `s` - `imms`, below `width`.
/// * `width` - The width in bits.
pub(super) fn ubfm(_old: u64, src: u64, r: u32, s: u32, width: u32) -> u64 {
    if s >= r {
        mask(src >> r, s - r + 1)
    } else {
        mask(mask(src, s + 1) << (width - r), width)
    }
}

/// `sbfm`: as [`ubfm`], with the field's top bit copied into every bit
/// above it.
///
/// # Arguments
///
/// * `_old` - The destination before, which `sbfm` does not read.
/// * `src` - The source.
/// * `r` - `immr`, below `width`.
/// * `s` - `imms`, below `width`.
/// * `width` - The width in bits.
pub(super) fn sbfm(_old: u64, src: u64, r: u32, s: u32, width: u32) -> u64 {
    if s >= r {
        mask(sign_extend(src >> r, s - r + 1).cast_unsigned(), width)
    } else {
        mask(
            sign_extend(src, s + 1).cast_unsigned() << (width - r),
            width,
        )
    }
}

/// `bfm`: as [`ubfm`], but into the destination, whose other bits stay.
///
/// # Arguments
///
/// * `old` - The destination before.
/// * `src` - The source.
/// * `r` - `immr`, below `width`.
/// * `s` - `imms`, below `width`.
/// * `width` - The width in bits.
pub(super) fn bfm(old: u64, src: u64, r: u32, s: u32, width: u32) -> u64 {
    let (field, pos) = if s >= r {
        (mask(u64::MAX, s - r + 1), 0)
    } else {
        (mask(u64::MAX, s + 1), width - r)
    };
    let placed = ubfm(old, src, r, s, width);
    mask((old & !(field << pos)) | placed, width)
}

/// Expands an `fmov` immediate into a floating-point value's bits.
///
/// # Arguments
///
/// * `imm8` - The eight-bit immediate.
/// * `bits` - The value's width: 16, 32 or 64.
///
/// # Returns
///
/// The bits, or `None` for any other width.
// SPEC: Arm ARM (DDI 0487) J1, VFPExpandImm.
pub(crate) fn vfp_expand(imm8: u32, bits: u16) -> Option<u64> {
    let exp_bits: u32 = match bits {
        16 => 5,
        32 => 8,
        64 => 11,
        _ => return None,
    };
    let n = u32::from(bits);
    let frac_bits = n - exp_bits - 1;
    let imm = u64::from(imm8);
    let b6 = (imm >> 6) & 1;
    let exp = ((b6 ^ 1) << (exp_bits - 1))
        | (if b6 == 1 {
            mask(u64::MAX, exp_bits - 3) << 2
        } else {
            0
        })
        | ((imm >> 4) & 3);
    Some((((imm >> 7) & 1) << (n - 1)) | (exp << frac_bits) | ((imm & 0xf) << (frac_bits - 4)))
}

/// Expands a vector-immediate's eight bits into the 64-bit pattern
/// `movi` and `mvni` write.
///
/// # Arguments
///
/// * `op` - The `op` bit.
/// * `cmode` - The four-bit `cmode`.
/// * `imm8` - The eight-bit immediate.
///
/// # Returns
///
/// The pattern, or `None` for the `cmode` that encodes a floating-point
/// immediate.
// SPEC: Arm ARM (DDI 0487) J1, AdvSIMDExpandImm.
pub(crate) fn expand_imm(op: u32, cmode: u32, imm8: u64) -> Option<u64> {
    let words = |v: u64| v | (v << 32);
    Some(match cmode >> 1 {
        0b000 => words(imm8),
        0b001 => words(imm8 << 8),
        0b010 => words(imm8 << 16),
        0b011 => words(imm8 << 24),
        0b100 => imm8 * HALVES,
        0b101 => (imm8 << 8) * HALVES,
        0b110 if cmode & 1 == 0 => words((imm8 << 8) | 0xff),
        0b110 => words((imm8 << 16) | 0xffff),
        _ if cmode & 1 == 1 => return None,
        _ if op == 0 => imm8 * BYTES,
        _ => (0..8).fold(0, |acc, k| {
            acc | if (imm8 >> k) & 1 == 1 {
                0xff << (8 * k)
            } else {
                0
            }
        }),
    })
}
