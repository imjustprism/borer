//! The float instructions on the RISC-V machine.
//!
//! A single sits in a float register boxed in ones; a register not boxed
//! reads as the canonical NaN, and every NaN an operation makes is the
//! canonical one, as the F and D extensions define. A single's addition,
//! subtraction, multiplication, division and square root are computed in
//! a double and rounded once to the single, which gives the single's
//! correctly rounded result; its fused multiply-add is computed in the
//! single. The machine keeps no `fcsr`: the dynamic rounding mode is to
//! nearest, ties to even, and no flag is raised. An operation that rounds
//! in another mode stops the run as unmodeled, except a conversion to an
//! integer, which rounds in any mode the encoding names, and a conversion
//! whose result is exact.

use super::Machine;
use super::exec::{n, unmodeled};
use crate::emulate::Stop;
use crate::isa::rv::{FArith, FCmp, FOp, Fmt, Fused, Insn, IntFmt, Reg};
use crate::num::{lo32, sext32};

/// The canonical NaN of a single.
const CANONICAL_NAN_32: u32 = 0x7fc0_0000;
/// The canonical NaN of a double.
const CANONICAL_NAN_64: u64 = 0x7ff8_0000_0000_0000;
/// The rounding mode field's value for to nearest, ties to even.
const RNE: u8 = 0;
/// The rounding mode field's value for toward zero.
const RTZ: u8 = 1;
/// The rounding mode field's value for down.
const RDN: u8 = 2;
/// The rounding mode field's value for up.
const RUP: u8 = 3;
/// The rounding mode field's value for to nearest, ties away from zero.
const RMM: u8 = 4;
/// The rounding mode field's value for the dynamic mode, `frm`.
const DYN: u8 = 7;

/// Tells whether a rounding mode rounds to nearest, ties to even: named so,
/// or the dynamic mode, which the machine keeps there.
///
/// # Arguments
///
/// * `rm` - The rounding mode field.
fn to_nearest(rm: u8) -> bool {
    matches!(rm, RNE | DYN)
}

/// Rounds a value to an integral one in a rounding mode.
///
/// # Arguments
///
/// * `x` - The value.
/// * `rm` - The rounding mode field.
///
/// # Returns
///
/// The integral value, or `None` for a reserved mode.
fn round(x: f64, rm: u8) -> Option<f64> {
    match rm {
        RNE | DYN => Some(x.round_ties_even()),
        RTZ => Some(x.trunc()),
        RDN => Some(x.floor()),
        RUP => Some(x.ceil()),
        RMM => Some(x.round()),
        _ => None,
    }
}

/// Returns an integral value as the integer a conversion writes.
///
/// A NaN is the largest value, and a value past either bound, an infinity
/// among them, saturates to that bound. A 32-bit result is sign-extended,
/// as the register takes it.
///
/// # Arguments
///
/// * `x` - The rounded value.
/// * `int` - The integer format.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "the bounds keep the integral value within the integer's width"
)]
fn to_int(x: f64, int: IntFmt) -> u64 {
    let (signed, bits): (bool, i32) = match int {
        IntFmt::W => (true, 32),
        IntFmt::Wu => (false, 32),
        IntFmt::L => (true, 64),
        IntFmt::Lu => (false, 64),
    };
    let all = u64::MAX >> (64 - bits);
    let top = 2f64.powi(bits - 1);
    let v = match (signed, x) {
        (true, x) if x.is_nan() || x >= top => all >> 1,
        (true, x) if x < -top => 1u64 << (bits - 1),
        (true, x) => (x as i64).cast_unsigned() & all,
        (false, x) if x.is_nan() || x >= top * 2.0 => all,
        (false, x) if x <= -1.0 => 0,
        (false, x) => x as u64,
    };
    if bits == 32 { sext32(v) } else { v }
}

/// Returns a float's class as `fclass` reports it: one bit of ten.
///
/// # Arguments
///
/// * `kind` - The value's category at its own format.
/// * `neg` - Whether its sign is negative.
/// * `quiet` - Whether a NaN is quiet; ignored for any other value.
fn class(kind: std::num::FpCategory, neg: bool, quiet: bool) -> u64 {
    let bit = match kind {
        std::num::FpCategory::Nan => {
            return if quiet { 1 << 9 } else { 1 << 8 };
        }
        std::num::FpCategory::Infinite => 0,
        std::num::FpCategory::Normal => 1,
        std::num::FpCategory::Subnormal => 2,
        std::num::FpCategory::Zero => 3,
    };
    if neg { 1 << bit } else { 1 << (7 - bit) }
}

/// Returns the smaller or larger of two values as `fmin` and `fmax` do:
/// a NaN loses to a number, two NaNs make the canonical one, and `-0`
/// is below `+0`.
///
/// # Arguments
///
/// * `a` - The first value.
/// * `b` - The second value.
/// * `max` - Whether the larger is wanted.
fn min_max(a: f64, b: f64, max: bool) -> f64 {
    let first = match (a.is_nan(), b.is_nan()) {
        (true, true) => return f64::NAN,
        (true, false) => false,
        (false, true) => true,
        (false, false) if a == b => a.is_sign_negative() != max,
        (false, false) => (a < b) != max,
    };
    if first { a } else { b }
}

impl Machine<'_> {
    /// Reads a single from a float register: its low word when the high
    /// word boxes it in ones, else the canonical NaN.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn single(&self, r: Reg) -> u32 {
        let v = self.f.get(n(r)).copied().unwrap_or(0);
        if v >> 32 == 0xffff_ffff {
            lo32(v)
        } else {
            CANONICAL_NAN_32
        }
    }

    /// Reads a float register at a format, as a double.
    ///
    /// # Arguments
    ///
    /// * `fmt` - The format.
    /// * `r` - The register.
    fn value(&self, fmt: Fmt, r: Reg) -> f64 {
        match fmt {
            Fmt::S => f64::from(f32::from_bits(self.single(r))),
            Fmt::D => f64::from_bits(self.f.get(n(r)).copied().unwrap_or(0)),
        }
    }

    /// Writes a float register, a single boxed in ones.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `fmt` - The format written.
    /// * `v` - The bits.
    fn set_f(&mut self, r: Reg, fmt: Fmt, v: u64) {
        let v = match fmt {
            Fmt::S => 0xffff_ffff_0000_0000 | (v & 0xffff_ffff),
            Fmt::D => v,
        };
        if let Some(f) = self.f.get_mut(n(r)) {
            *f = v;
        }
    }

    /// Writes the result of an operation to a float register: a double
    /// rounded once to the format, a NaN made the canonical one.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `fmt` - The format.
    /// * `x` - The result, exact or rounded to the format already.
    fn put(&mut self, r: Reg, fmt: Fmt, x: f64) {
        let bits = match fmt {
            Fmt::S if x.is_nan() => u64::from(CANONICAL_NAN_32),
            #[expect(
                clippy::cast_possible_truncation,
                reason = "the single's result rounds the double once, as the machine does"
            )]
            Fmt::S => u64::from((x as f32).to_bits()),
            Fmt::D if x.is_nan() => CANONICAL_NAN_64,
            Fmt::D => x.to_bits(),
        };
        self.set_f(r, fmt, bits);
    }

    /// Runs a float instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - Its operation.
    ///
    /// # Errors
    ///
    /// A fault, a full memory, or a rounding mode the machine does not
    /// model.
    pub(super) fn float(&mut self, i: &Insn, f: FOp) -> Result<(), Stop> {
        match f {
            FOp::Load { fmt, rd, rs1, off } => {
                let at = self.xlen.addr(self.get(rs1).wrapping_add_signed(off));
                let v = self.load(at, if fmt == Fmt::S { 4 } else { 8 })?;
                self.set_f(rd, fmt, v);
            }
            FOp::Store { fmt, rs2, rs1, off } => {
                let at = self.xlen.addr(self.get(rs1).wrapping_add_signed(off));
                let raw = self.f.get(n(rs2)).copied().unwrap_or(0);
                self.store(at, if fmt == Fmt::S { 4 } else { 8 }, raw)?;
            }
            FOp::MvToInt { fmt, rd, rs1 } => {
                let raw = self.f.get(n(rs1)).copied().unwrap_or(0);
                let v = if fmt == Fmt::S { sext32(raw) } else { raw };
                self.set_x(n(rd), v);
            }
            FOp::MvFromInt { fmt, rd, rs1 } => self.set_f(rd, fmt, self.get(rs1)),
            FOp::Arith {
                op,
                fmt,
                rd,
                rs1,
                rs2,
                rm,
            } => self.arith(i, op, fmt, (rd, rs1, rs2), rm)?,
            FOp::Sqrt { fmt, rd, rs1, rm } if to_nearest(rm) => {
                self.put(rd, fmt, self.value(fmt, rs1).sqrt());
            }
            FOp::Fused {
                op,
                fmt,
                rd,
                rs1,
                rs2,
                rs3,
                rm,
            } if to_nearest(rm) => self.fused(op, fmt, rd, [rs1, rs2, rs3]),
            FOp::Cmp {
                op,
                fmt,
                rd,
                rs1,
                rs2,
            } => {
                let (a, b) = (self.value(fmt, rs1), self.value(fmt, rs2));
                let holds = match op {
                    FCmp::Eq => a == b,
                    FCmp::Lt => a < b,
                    FCmp::Le => a <= b,
                };
                self.set_x(n(rd), u64::from(holds));
            }
            FOp::Class { fmt, rd, rs1 } => self.classify(fmt, rd, rs1),
            FOp::ToInt {
                fmt,
                int,
                rd,
                rs1,
                rm,
            } => {
                let x = round(self.value(fmt, rs1), rm).ok_or_else(|| unmodeled(i))?;
                self.set_x(n(rd), to_int(x, int));
            }
            FOp::FromInt {
                fmt,
                int,
                rd,
                rs1,
                rm,
            } => self.int_to_float(i, fmt, int, (rd, rs1), rm)?,
            FOp::Convert {
                from,
                to,
                rd,
                rs1,
                rm,
            } => {
                let x = self.value(from, rs1);
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "the check below keeps an inexact narrowing to the modes modeled"
                )]
                let exact = to == Fmt::D || x.is_nan() || f64::from(x as f32) == x;
                if !exact && !to_nearest(rm) {
                    return Err(unmodeled(i));
                }
                self.put(rd, to, x);
            }
            FOp::Sqrt { .. } | FOp::Fused { .. } => return Err(unmodeled(i)),
        }
        Ok(())
    }

    /// Runs `fclass`: the source's class at its format, as one bit of ten.
    ///
    /// # Arguments
    ///
    /// * `fmt` - The format.
    /// * `rd` - The destination.
    /// * `rs1` - The source.
    fn classify(&mut self, fmt: Fmt, rd: Reg, rs1: Reg) {
        let (kind, neg, quiet) = match fmt {
            Fmt::S => {
                let v = f32::from_bits(self.single(rs1));
                (
                    v.classify(),
                    v.is_sign_negative(),
                    v.to_bits() & 0x0040_0000 != 0,
                )
            }
            Fmt::D => {
                let v = f64::from_bits(self.f.get(n(rs1)).copied().unwrap_or(0));
                (
                    v.classify(),
                    v.is_sign_negative(),
                    v.to_bits() & (1 << 51) != 0,
                )
            }
        };
        self.set_x(n(rd), class(kind, neg, quiet));
    }

    /// Runs an arithmetic, minimum, maximum or sign-injection instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - The operation.
    /// * `fmt` - The format.
    /// * `(rd, rs1, rs2)` - The destination and the two sources.
    /// * `rm` - The rounding mode field, which a minimum, a maximum or a
    ///   sign injection uses to tell its operations apart.
    ///
    /// # Errors
    ///
    /// A rounding mode the machine does not model.
    fn arith(
        &mut self,
        i: &Insn,
        op: FArith,
        fmt: Fmt,
        (rd, rs1, rs2): (Reg, Reg, Reg),
        rm: u8,
    ) -> Result<(), Stop> {
        let (a, b) = (self.value(fmt, rs1), self.value(fmt, rs2));
        let x = match op {
            FArith::Add | FArith::Sub | FArith::Mul | FArith::Div if !to_nearest(rm) => {
                return Err(unmodeled(i));
            }
            FArith::Add => a + b,
            FArith::Sub => a - b,
            FArith::Mul => a * b,
            FArith::Div => a / b,
            FArith::Min => min_max(a, b, false),
            FArith::Max => min_max(a, b, true),
            FArith::Sgnj | FArith::Sgnjn | FArith::Sgnjx => {
                let bits = |r: Reg| match fmt {
                    Fmt::S => u64::from(self.single(r)),
                    Fmt::D => self.f.get(n(r)).copied().unwrap_or(0),
                };
                let sign = if fmt == Fmt::S {
                    1u64 << 31
                } else {
                    1u64 << 63
                };
                let (a, b) = (bits(rs1), bits(rs2));
                let s = match op {
                    FArith::Sgnjn => !b & sign,
                    FArith::Sgnjx => (a ^ b) & sign,
                    FArith::Sgnj
                    | FArith::Add
                    | FArith::Sub
                    | FArith::Mul
                    | FArith::Div
                    | FArith::Min
                    | FArith::Max => b & sign,
                };
                self.set_f(rd, fmt, (a & !sign) | s);
                return Ok(());
            }
        };
        self.put(rd, fmt, x);
        Ok(())
    }

    /// Runs a fused multiply-add, rounded once at the format.
    ///
    /// # Arguments
    ///
    /// * `op` - Which signs the product and the addend take.
    /// * `fmt` - The format.
    /// * `rd` - The destination.
    /// * `[rs1, rs2, rs3]` - The factors and the addend.
    fn fused(&mut self, op: Fused, fmt: Fmt, rd: Reg, [rs1, rs2, rs3]: [Reg; 3]) {
        let (a, b, c) = (
            self.value(fmt, rs1),
            self.value(fmt, rs2),
            self.value(fmt, rs3),
        );
        let (a, c) = match op {
            Fused::Madd => (a, c),
            Fused::Msub => (a, -c),
            Fused::Nmsub => (-a, c),
            Fused::Nmadd => (-a, -c),
        };
        #[expect(
            clippy::cast_possible_truncation,
            reason = "a single's operands are singles, so the narrowing is exact"
        )]
        let x = match fmt {
            Fmt::S => f64::from((a as f32).mul_add(b as f32, c as f32)),
            Fmt::D => a.mul_add(b, c),
        };
        self.put(rd, fmt, x);
    }

    /// Runs a conversion of an integer to a float.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `fmt` - The float format.
    /// * `int` - The integer format.
    /// * `(rd, rs1)` - The destination and the source.
    /// * `rm` - The rounding mode field.
    ///
    /// # Errors
    ///
    /// An inexact conversion in a rounding mode the machine does not
    /// model.
    #[expect(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        reason = "the conversion rounds the integer to nearest, as the mode it is checked against does"
    )]
    fn int_to_float(
        &mut self,
        i: &Insn,
        fmt: Fmt,
        int: IntFmt,
        (rd, rs1): (Reg, Reg),
        rm: u8,
    ) -> Result<(), Stop> {
        let raw = self.get(rs1);
        let v: i128 = match int {
            IntFmt::W => i128::from(sext32(raw).cast_signed()),
            IntFmt::Wu => i128::from(lo32(raw)),
            IntFmt::L => i128::from(raw.cast_signed()),
            IntFmt::Lu => i128::from(raw),
        };
        let x = match fmt {
            Fmt::S => f64::from(v as f32),
            Fmt::D => v as f64,
        };
        if !to_nearest(rm) && x as i128 != v {
            return Err(unmodeled(i));
        }
        self.put(rd, fmt, x);
        Ok(())
    }
}
