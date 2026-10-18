//! Scalar floating-point arithmetic for the arm64 machine: the data
//! processing, the compares and conditional select, and the conversions to
//! and from integers and between widths.
//!
//! The x86 machine's float model carries every value as an `f64`, a single
//! computing in a single so its rounding happens at the operation
//! (`emulate::sse`); these handlers keep its conventions, so both machines
//! answer byte for byte: the host's IEEE-754 arithmetic rounds to
//! nearest-even and quiets a signaling NaN as the operation itself does.
//! A vector form computes each lane at the lane's own width the same way,
//! independently, the bits above the arrangement's span cleared.
//!
//! The flags a compare sets follow the architecture's table exactly, and a
//! float converted to an integer saturates with a NaN going to zero, as the
//! architecture says, where x86 answers its integer indefinite.

use crate::emulate::{Stop, lo64, mask, sign_extend};
use crate::isa::a64::{Cond, Insn, Opnd, Reg};

use super::{Machine, mask_wide, unmodeled, vector};

/// The sign bit of a value `bits` wide, for `fabs` and `fneg`.
fn sign_bit(bits: u16) -> u64 {
    1u64 << (u32::from(bits) - 1)
}

/// A `v` register operand at a scalar float's width.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `k` - The operand's position.
///
/// # Returns
///
/// The register and its width, 32 or 64 bits.
///
/// # Errors
///
/// When the operand is no `v` register at one of those widths.
fn reg_opnd(i: &Insn, k: usize) -> Result<(Reg, u16), Stop> {
    match i.operands.get(k) {
        Some(Opnd::Reg {
            reg: reg @ Reg::V(_),
            bits: bits @ (32 | 64),
        }) => Ok((*reg, *bits)),
        _ => Err(unmodeled(i)),
    }
}

/// A scalar float's value at its width, as the double the model computes on.
///
/// # Arguments
///
/// * `m` - The machine holding the register.
/// * `reg` - The `v` register.
/// * `bits` - The width, 32 or 64.
fn value(m: &Machine<'_>, reg: Reg, bits: u16) -> f64 {
    let raw = lo64(m.reg(reg)) & mask(u64::MAX, u32::from(bits));
    if bits == 32 {
        f64::from(f32::from_bits(crate::num::lo32(raw)))
    } else {
        f64::from_bits(raw)
    }
}

/// A float's value from its bits at a width, as the double the model
/// computes on.
///
/// # Arguments
///
/// * `raw` - The value's low bits.
/// * `bits` - The width, 32 or 64.
fn of_bits(raw: u64, bits: u16) -> f64 {
    if bits == 32 {
        f64::from(f32::from_bits(crate::num::lo32(raw)))
    } else {
        f64::from_bits(raw)
    }
}

/// The `v` register a vector word's field names.
///
/// # Arguments
///
/// * `w` - The encoded word.
/// * `at` - Where the register's number starts.
fn vreg(w: u32, at: u32) -> Reg {
    Reg::V(crate::num::lo8(u64::from((w >> at) & 0x1f)))
}

/// The lane width and span a vector floating-point word names: a single
/// or a double lane, over the low half or the whole register.
///
/// # Arguments
///
/// * `i` - The instruction.
fn fp_shape(i: &Insn) -> (u16, u16) {
    let lane = if (i.word >> 22) & 1 == 1 { 64 } else { 32 };
    let span = if (i.word >> 30) & 1 == 1 { 128 } else { 64 };
    (lane, span)
}

/// A result written back at a single's or a double's width.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width, 32 or 64.
fn single(v: f64, bits: u16) -> u64 {
    if bits == 32 {
        #[expect(
            clippy::cast_possible_truncation,
            reason = "a single's operation computes in a single, rounding there as the machine does"
        )]
        let r = v as f32;
        u64::from(r.to_bits())
    } else {
        v.to_bits()
    }
}

/// The condition operand of `fccmp` and `fcsel`.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Errors
///
/// When the fourth operand is no condition.
fn cond(i: &Insn) -> Result<Cond, Stop> {
    match i.operands[3] {
        Opnd::Cond(c) => Ok(c),
        Opnd::Reg { .. }
        | Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Other => Err(unmodeled(i)),
    }
}

impl Machine<'_> {
    /// `fadd`, `fsub`, `fmul`, `fdiv`, `fmax` and `fmin`: the operation at
    /// the destination's width, which clears every bit above it — scalar,
    /// or lane-wise over the two registers for a vector form.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on doubles.
    ///
    /// # Errors
    ///
    /// When an operand is no `v` register at 32 or 64 bits.
    pub(super) fn float_binary(
        &mut self,
        i: &Insn,
        f: impl Fn(f64, f64) -> f64,
    ) -> Result<(), Stop> {
        if vector(i) {
            return self.float_array(i, f);
        }
        let (rd, bits) = reg_opnd(i, 0)?;
        let (rn, from_n) = reg_opnd(i, 1)?;
        let (rm, from_m) = reg_opnd(i, 2)?;
        if from_n != bits || from_m != bits {
            return Err(unmodeled(i));
        }
        let (x, y) = (value(self, rn, bits), value(self, rm, bits));
        self.set_reg(rd, bits, u128::from(single(f(x, y), bits)));
        Ok(())
    }

    /// `fmadd`, `fmsub`, `fnmadd` and `fnmsub` (scalar): the product of the
    /// first two sources fused with the third, rounded once at the
    /// destination's width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on the two factors and the addend, as doubles.
    ///
    /// # Errors
    ///
    /// When a source is not a scalar register of the destination's width.
    pub(super) fn float_fused(
        &mut self,
        i: &Insn,
        f: impl Fn(f64, f64, f64) -> f64,
    ) -> Result<(), Stop> {
        let (rd, bits) = reg_opnd(i, 0)?;
        let (rn, from_n) = reg_opnd(i, 1)?;
        let (rm, from_m) = reg_opnd(i, 2)?;
        let (ra, from_a) = reg_opnd(i, 3)?;
        if vector(i) || from_n != bits || from_m != bits || from_a != bits {
            return Err(unmodeled(i));
        }
        let (x, y, z) = (
            value(self, rn, bits),
            value(self, rm, bits),
            value(self, ra, bits),
        );
        self.set_reg(rd, bits, u128::from(single(f(x, y, z), bits)));
        Ok(())
    }

    /// The vector form of a two-source float operation: the operation
    /// lane-wise at the lane's width, each lane a single computing in a
    /// single, the bits above the arrangement's span cleared.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on doubles.
    ///
    /// # Errors
    ///
    /// Never; the decoder has already accepted the arrangement.
    pub(super) fn float_array(
        &mut self,
        i: &Insn,
        f: impl Fn(f64, f64) -> f64,
    ) -> Result<(), Stop> {
        let (rn, rm) = (vreg(i.word, 5), vreg(i.word, 16));
        let (lane, span) = fp_shape(i);
        let (x, y) = (self.reg(rn), self.reg(rm));
        let mut v = 0u128;
        for k in 0..u32::from(span / lane) {
            let at = k * u32::from(lane);
            let (a, b) = (of_bits(lo64(x >> at), lane), of_bits(lo64(y >> at), lane));
            v |= u128::from(single(f(a, b), lane)) << at;
        }
        self.set_reg(vreg(i.word, 0), 128, v);
        Ok(())
    }

    /// `fsqrt`: the square root in the width's own arithmetic, scalar or
    /// lane-wise.
    ///
    /// # Errors
    ///
    /// When the source is no `v` register at 32 or 64 bits.
    pub(super) fn float_sqrt(&mut self, i: &Insn) -> Result<(), Stop> {
        if vector(i) {
            let rn = vreg(i.word, 5);
            let (lane, span) = fp_shape(i);
            let x = self.reg(rn);
            let mut v = 0u128;
            for k in 0..u32::from(span / lane) {
                let at = k * u32::from(lane);
                let a = of_bits(lo64(x >> at), lane);
                v |= u128::from(single(a.sqrt(), lane)) << at;
            }
            self.set_reg(vreg(i.word, 0), 128, v);
            return Ok(());
        }
        let (rd, bits) = reg_opnd(i, 0)?;
        let (rn, from) = reg_opnd(i, 1)?;
        if from != bits {
            return Err(unmodeled(i));
        }
        let x = value(self, rn, bits);
        self.set_reg(rd, bits, u128::from(single(x.sqrt(), bits)));
        Ok(())
    }

    /// `fabs` and `fneg` (register): the value's sign bit cleared or
    /// flipped, every other bit as it was — scalar, or every lane's sign
    /// bit for a vector form.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `flip` - Whether the sign bit flips (`fneg`) or clears (`fabs`).
    ///
    /// # Errors
    ///
    /// When the source is no `v` register at 32 or 64 bits.
    pub(super) fn float_sign(&mut self, i: &Insn, flip: bool) -> Result<(), Stop> {
        if vector(i) {
            let (lane, span) = fp_shape(i);
            let signs = (0..u32::from(span / lane)).fold(0u128, |acc, k| {
                acc | u128::from(sign_bit(lane)) << (k * u32::from(lane))
            });
            let raw = self.reg(vreg(i.word, 5)) & mask_wide(u128::MAX, span);
            let v = if flip { raw ^ signs } else { raw & !signs };
            self.set_reg(vreg(i.word, 0), 128, v);
            return Ok(());
        }
        let (rd, bits) = reg_opnd(i, 0)?;
        let (rn, from) = reg_opnd(i, 1)?;
        let raw = lo64(self.reg(rn)) & mask(u64::MAX, u32::from(from));
        let v = if flip {
            raw ^ sign_bit(from)
        } else {
            raw & !sign_bit(from)
        };
        self.set_reg(rd, bits, u128::from(v));
        Ok(())
    }

    /// `fcmp` and `fcmpe`: the flags of the order of two values, the second
    /// of which the `#0.0` form holds as zero. Both leave the same flags;
    /// only a signaling NaN's exception differs, which no flag the engine
    /// reads carries.
    ///
    /// # Errors
    ///
    /// When an operand is no `v` register at 32 or 64 bits, or the
    /// immediate form's second operand is anything the decoder left
    /// unmodeled.
    pub(super) fn float_compare(&mut self, i: &Insn) -> Result<(), Stop> {
        let (rn, bits) = reg_opnd(i, 0)?;
        let x = value(self, rn, bits);
        let y = match i.operands[1] {
            Opnd::Reg { reg, bits: from } => value(self, reg, from),
            Opnd::Other => 0.0,
            Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => return Err(unmodeled(i)),
        };
        self.set_nzcv(compare_flags(x.partial_cmp(&y)) << 28);
        Ok(())
    }

    /// `fccmp` and `fccmpe`: the flags of a floating-point compare when the
    /// condition holds, else the immediate flags.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn float_compare_if(&mut self, i: &Insn) -> Result<(), Stop> {
        let (rn, bits) = reg_opnd(i, 0)?;
        let (rm, from) = reg_opnd(i, 1)?;
        let c = cond(i)?;
        if self.holds(c) {
            if from != bits {
                return Err(unmodeled(i));
            }
            let (x, y) = (value(self, rn, bits), value(self, rm, bits));
            self.set_nzcv(compare_flags(x.partial_cmp(&y)) << 28);
        } else {
            self.set_nzcv(self.int(i, 2)? << 28);
        }
        Ok(())
    }

    /// `fcsel`: the first source when the condition holds, else the second,
    /// at the destination's width.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled.
    pub(super) fn float_select(&mut self, i: &Insn) -> Result<(), Stop> {
        let (rd, bits) = reg_opnd(i, 0)?;
        let (rn, from_n) = reg_opnd(i, 1)?;
        let (rm, from_m) = reg_opnd(i, 2)?;
        let c = cond(i)?;
        let v = if self.holds(c) {
            value_bits(self, rn, from_n)
        } else {
            value_bits(self, rm, from_m)
        };
        self.set_reg(rd, bits, u128::from(v));
        Ok(())
    }

    /// `scvtf` and `ucvtf`: an integer, signed or unsigned, into the
    /// destination's width, the fixed-point form divided by `2^fbits` and
    /// the register form as it is.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `signed` - Whether the integer is signed.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or the fixed-point shift is out of
    /// the source's width.
    pub(super) fn int_to_float(&mut self, i: &Insn, signed: bool) -> Result<(), Stop> {
        let (Opnd::Reg { reg: rd, bits: to }, Opnd::Reg { bits: from, .. }) =
            (i.operands[0], i.operands[1])
        else {
            return Err(unmodeled(i));
        };
        let raw = self.int(i, 1)?;
        #[expect(
            clippy::cast_precision_loss,
            reason = "the conversion rounds the integer to the float, as the machine does"
        )]
        let base = if signed {
            sign_extend(raw, u32::from(from)) as f64
        } else {
            raw as f64
        };
        let v = match i.operands.get(2) {
            Some(Opnd::Imm(v)) if *v != 0 && *v <= u64::from(from) => base / pow2(*v),
            Some(Opnd::None) | None => base,
            _ => return Err(unmodeled(i)),
        };
        self.set_reg(rd, to, u128::from(single(v, to)));
        Ok(())
    }

    /// `fcvtzs` and `fcvtzu`: a float rounded toward zero into an integer,
    /// the fixed-point form scaled by `2^fbits` first. A NaN converts to
    /// zero and a value out of range saturates to the width's bound, where
    /// x86 answers its integer indefinite.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `signed` - Whether the integer is signed.
    ///
    /// # Errors
    ///
    /// When an operand is not modeled or the fixed-point shift is out of
    /// range.
    pub(super) fn float_to_int(&mut self, i: &Insn, signed: bool) -> Result<(), Stop> {
        let (
            Opnd::Reg { reg: rd, bits: to },
            Opnd::Reg {
                reg: src,
                bits: from,
            },
        ) = (i.operands[0], i.operands[1])
        else {
            return Err(unmodeled(i));
        };
        if !matches!(to, 32 | 64) || !matches!(from, 32 | 64) {
            return Err(unmodeled(i));
        }
        let x = match i.operands.get(2) {
            Some(Opnd::Imm(v)) if *v != 0 && *v <= 64 => value(self, src, from) * pow2(*v),
            Some(Opnd::None) | None => value(self, src, from),
            _ => return Err(unmodeled(i)),
        };
        self.set_reg(rd, to, u128::from(fixed(x, signed, to)));
        Ok(())
    }

    /// `fcvt`: a value between the half, single and double widths.
    ///
    /// # Errors
    ///
    /// For any widths but those three.
    pub(super) fn float_convert(&mut self, i: &Insn) -> Result<(), Stop> {
        let (
            Opnd::Reg { reg: rd, bits: to },
            Opnd::Reg {
                reg: src,
                bits: from,
            },
        ) = (i.operands[0], i.operands[1])
        else {
            return Err(unmodeled(i));
        };
        let bits_of = |m: &Machine<'_>, r: Reg| lo64(m.reg(r));
        let v = match (from, to) {
            (32, 64) => f64::from(f32::from_bits(crate::num::lo32(bits_of(self, src)))).to_bits(),
            (64, 32) => single(f64::from_bits(bits_of(self, src)), 32),
            (16, 32) => single(half(bits_of(self, src)), 32),
            (16, 64) => half(bits_of(self, src)).to_bits(),
            (32, 16) => u64::from(to_half(f64::from(f32::from_bits(crate::num::lo32(
                bits_of(self, src),
            ))))),
            (64, 16) => u64::from(to_half(f64::from_bits(bits_of(self, src)))),
            _ => return Err(unmodeled(i)),
        };
        self.set_reg(rd, to, u128::from(v));
        Ok(())
    }
}

/// A register's low bits at a width, for instructions that move bits.
///
/// # Arguments
///
/// * `m` - The machine holding the register.
/// * `reg` - The `v` register.
/// * `bits` - The width.
fn value_bits(m: &Machine<'_>, reg: Reg, bits: u16) -> u64 {
    lo64(m.reg(reg)) & mask(u64::MAX, u32::from(bits))
}

/// The flags word (N in bit 3 down to V in bit 0) of a float's order.
///
/// # Arguments
///
/// * `order` - The comparison's outcome, `None` for an unordered pair.
fn compare_flags(order: Option<std::cmp::Ordering>) -> u64 {
    match order {
        None => 0b0111,
        Some(std::cmp::Ordering::Less) => 0b1000,
        Some(std::cmp::Ordering::Equal) => 0b0110,
        Some(std::cmp::Ordering::Greater) => 0b0010,
    }
}

/// A float rounded toward zero into an integer of `bits` bits: a NaN to
/// zero, a value out of range saturated to the width's bound.
///
/// # Arguments
///
/// * `x` - The value.
/// * `signed` - Whether the integer is signed.
/// * `bits` - The integer's width, 32 or 64.
fn fixed(x: f64, signed: bool, bits: u16) -> u64 {
    let t = x.trunc();
    if t.is_nan() {
        return 0;
    }
    let top = 2f64.powi(i32::from(bits) - 1);
    if signed {
        if t < -top {
            return 1u64 << (bits - 1);
        }
        if t >= top {
            return (1u64 << (bits - 1)) - 1;
        }
    } else {
        if t < 0.0 {
            return 0;
        }
        if t >= top * 2.0 {
            return mask(u64::MAX, u32::from(bits));
        }
        // A value in `[2^63, 2^64)` fits in the unsigned result and does not
        // fit in `i64`. Casting through `i64` would saturate a step early.
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "the bounds keep the truncated value within the unsigned width"
        )]
        let v = t as u64;
        return mask(v, u32::from(bits));
    }
    #[expect(
        clippy::cast_possible_truncation,
        reason = "the bounds above keep the truncated value within the signed width"
    )]
    let v = t as i64;
    mask(v.cast_unsigned(), u32::from(bits))
}

/// Two to a power, for the fixed-point shift the conversions scale by.
///
/// # Arguments
///
/// * `n` - The power, at most 64, as every caller has validated.
fn pow2(n: u64) -> f64 {
    2f64.powi(u32::try_from(n).unwrap_or(64).cast_signed())
}

/// A half's value as a double, exactly.
///
/// # Arguments
///
/// * `h` - The half's low 16 bits.
fn half(h: u64) -> f64 {
    let (sign, exp, frac) = (
        (h >> 15) & 1,
        u32::try_from((h >> 10) & 0x1f).unwrap_or(0x1f),
        crate::num::lo32(h & 0x3ff),
    );
    let magnitude = if exp == 0 {
        f64::from(frac) * pow2(24).recip()
    } else if exp == 0x1f {
        f64::NAN
    } else {
        f64::from_bits((u64::from(exp + 1023 - 15) << 52) | (u64::from(frac) << 42))
    };
    if sign == 1 { -magnitude } else { magnitude }
}

/// A double rounded to a half's bits, to nearest with ties to even, an
/// overflow saturating to infinity as the rounding takes it and a NaN
/// quieting.
///
/// # Arguments
///
/// * `x` - The value.
fn to_half(x: f64) -> u16 {
    let sign = u16::from(x.is_sign_negative()) << 15;
    if x.is_nan() {
        return sign | 0x7e00;
    }
    if x.is_infinite() {
        return sign | 0x7c00;
    }
    let a = x.abs();
    if a < pow2(25).recip() {
        return sign;
    }
    let e = u32::try_from((a.to_bits() >> 52) & 0x7ff)
        .unwrap_or(0x7ff)
        .cast_signed()
        - 1023;
    if e < -14 {
        let units = a * pow2(24);
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "the subnormal range is under 1024 nonnegative units, so the rounding keeps every bit"
        )]
        return sign | u16::try_from(units.round_ties_even() as u64).unwrap_or(0x3ff);
    }
    let scaled = a / pow2((e - 10).cast_unsigned().into());
    #[expect(
        clippy::cast_possible_truncation,
        reason = "the scaled magnitude is under 2048, so the rounding keeps every bit"
    )]
    let m = scaled.round_ties_even() as i32;
    let (e, m) = if m == 0x800 { (e + 1, 0x400) } else { (e, m) };
    if e > 15 {
        return sign | 0x7c00;
    }
    sign | ((u16::try_from(e + 15).unwrap_or(31)) << 10) | u16::try_from(m - 0x400).unwrap_or(0)
}
