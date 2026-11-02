//! The F and D instructions for the RISC-V lifter.
//!
//! A float register holds a float expression typed at its format, as the
//! arm64 lifter's scalar `v` registers do ([`super::super::lift_a64`]): a
//! load is the float it reads, arithmetic is the shared float operators
//! ([`Op::FAdd`] and the rest) stamped with the instruction's width, a
//! square root is [`UnOp::Sqrt`], a sign injection of a register with
//! itself is a move, a negation or an absolute value (of a register that
//! holds no float yet, its sign bit flipped or cleared), a compare is the 0
//! or 1 its ordered predicate holds, and a conversion is a cast, toward
//! zero into an integer through [`RoundToInt`] with RISC-V's NaN rule. A
//! register that holds no float yet (a parameter, or bits an `fmv` moved
//! in) is read as it is, and a parameter read so is declared at that
//! width. The forms C has a library call for and no operator, a fused
//! multiply-add and a minimum or maximum, are that call (`fma`, `fmin`,
//! `fmax` and their single forms), which a check of the lifter counts and
//! does not compare. An operation rounding in a mode other than to
//! nearest, a conversion to an integer that does not round toward zero,
//! a sign injection of two different registers, a class, and a read of a
//! register at a width other than the one it holds are not modeled.
//! A NaN an operation makes keeps the payload the evaluator gives it, not
//! the canonical NaN the machine writes: the C means the same on RISC-V,
//! and only the bits an `fmv` or a store then shows differ.

use super::super::expr::{
    Cc, Cond, Expr, Flags, Key, Op, Ty, UnOp, bitcast, fold, mask, mask_bits, sign_extend,
};
use super::super::fcmp::FPred;
use super::super::helper::Helper;
use super::super::lift_a64::mem::{bear_width, float_width};
use super::super::round_to_int::RoundToInt;
use super::{Lift, offset};
use crate::isa::rv::{FArith, FCmp, FOp, Fmt, Fused, IntFmt, Reg, Xlen};
use crate::isa::x86::ConditionCode;

/// The rounding mode field's value for to nearest, ties to even.
const RNE: u8 = 0;
/// The rounding mode field's value for toward zero.
const RTZ: u8 = 1;
/// The rounding mode field's value for the dynamic mode, to nearest.
const DYN: u8 = 7;

/// Returns the type of a float format.
///
/// # Arguments
///
/// * `fmt` - The format.
fn ty(fmt: Fmt) -> Ty {
    match fmt {
        Fmt::S => Ty::F32,
        Fmt::D => Ty::F64,
    }
}

/// Returns a C library call over float arguments, named for the format: a
/// single's name ends in `f`.
///
/// # Arguments
///
/// * `name` - The double's name.
/// * `fmt` - The format.
/// * `args` - The arguments.
fn libm(name: &str, fmt: Fmt, args: Vec<Expr>) -> Expr {
    let name = match fmt {
        Fmt::S => format!("{name}f"),
        Fmt::D => name.to_owned(),
    };
    Expr::Call(name, args)
}

impl Lift<'_, '_> {
    /// Reads a float register at a format.
    ///
    /// A float of that width is itself, an untyped float operation is
    /// stamped with the width, and a constant is the float its bits are.
    /// Anything else not a float (a parameter, bits moved in) is read as
    /// it is; a parameter still in its register is declared at the width.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `fmt` - The format read.
    ///
    /// # Returns
    ///
    /// The value, or `None` when the register holds a float of the other
    /// width.
    fn fread(&mut self, r: Reg, fmt: Fmt) -> Option<Expr> {
        let t = ty(fmt);
        match self.get(r) {
            Expr::Const(c) => Some(Expr::FConst(c & mask_bits(t.bits()), t)),
            v if v.is_float() => match float_width(&v) {
                Some(w) if w == t.bits() => Some(v),
                Some(_) => None,
                None => Some(bear_width(v, t)),
            },
            v => {
                if let Expr::Var(key @ Key::Param(_)) = v {
                    self.ex.ctx.reg_ty.entry(key).or_insert(t);
                }
                self.ex.ctx.reg_ty.entry(Key::Rv(r)).or_insert(t);
                Some(v)
            }
        }
    }

    /// Lifts a float instruction.
    ///
    /// # Arguments
    ///
    /// * `f` - The operation.
    ///
    /// # Returns
    ///
    /// `None` for a form this does not model.
    pub(super) fn float(&mut self, f: FOp) -> Option<()> {
        let w = self.w();
        match f {
            FOp::Load { fmt, rd, rs1, off } => {
                let at = offset(self.get(rs1), off, w);
                let v = self.ex.read_at(at, ty(fmt));
                let v = if v.is_float() { v } else { bitcast(v, ty(fmt)) };
                self.write(rd, v);
            }
            FOp::Store { fmt, rs2, rs1, off } => {
                let v = self.fread(rs2, fmt)?;
                let at = offset(self.get(rs1), off, w);
                self.ex.store_at(at, ty(fmt), v);
            }
            FOp::MvToInt { fmt, rd, rs1 } => {
                let v = self.fread(rs1, fmt)?;
                let v = match fmt {
                    Fmt::S => sign_extend(bitcast(v, Ty::U32), 32),
                    Fmt::D => bitcast(v, Ty::U64),
                };
                self.write(rd, v);
            }
            FOp::MvFromInt { fmt, rd, rs1 } => {
                let t = ty(fmt);
                let v = mask(self.get(rs1), mask_bits(t.bits()));
                self.write(rd, bitcast(v, t));
            }
            FOp::Arith {
                op,
                fmt,
                rd,
                rs1,
                rs2,
                rm,
            } => self.arith(op, fmt, (rd, rs1, rs2), rm)?,
            FOp::Sqrt {
                fmt,
                rd,
                rs1,
                rm: RNE | DYN,
            } => {
                let x = self.fread(rs1, fmt)?;
                self.write(rd, bear_width(Expr::Un(UnOp::Sqrt, Box::new(x)), ty(fmt)));
            }
            FOp::Fused {
                op,
                fmt,
                rd,
                rs1,
                rs2,
                rs3,
                rm: RNE | DYN,
            } => self.fused(op, fmt, rd, [rs1, rs2, rs3])?,
            FOp::Cmp {
                op,
                fmt,
                rd,
                rs1,
                rs2,
            } => self.compare(op, fmt, rd, (rs1, rs2))?,
            FOp::ToInt {
                fmt,
                int,
                rd,
                rs1,
                rm: RTZ,
            } => self.round_to_int(fmt, int, rd, rs1)?,
            FOp::FromInt {
                fmt,
                int,
                rd,
                rs1,
                rm,
            } => self.cast_int(fmt, int, (rd, rs1), rm)?,
            FOp::Convert {
                from,
                to,
                rd,
                rs1,
                rm,
            } if to == Fmt::D || matches!(rm, RNE | DYN) => {
                let x = self.fread(rs1, from)?;
                self.write(rd, Expr::Cast(Box::new(x), ty(to)));
            }
            FOp::Sqrt { .. }
            | FOp::Fused { .. }
            | FOp::Class { .. }
            | FOp::ToInt { .. }
            | FOp::Convert { .. } => return None,
        }
        Some(())
    }

    /// Lifts a fused multiply-add as the C call that names it, `fma` or
    /// `fmaf`, rounded once as the machine does.
    ///
    /// # Arguments
    ///
    /// * `op` - Which signs the product and the addend take.
    /// * `fmt` - The format.
    /// * `rd` - The destination.
    /// * `[rs1, rs2, rs3]` - The factors and the addend.
    ///
    /// # Returns
    ///
    /// `None` for a source this does not read.
    fn fused(&mut self, op: Fused, fmt: Fmt, rd: Reg, [rs1, rs2, rs3]: [Reg; 3]) -> Option<()> {
        let neg = |x: Expr| Expr::Un(UnOp::Neg, Box::new(x));
        let (a, b, c) = (
            self.fread(rs1, fmt)?,
            self.fread(rs2, fmt)?,
            self.fread(rs3, fmt)?,
        );
        let (a, c) = match op {
            Fused::Madd => (a, c),
            Fused::Msub => (a, neg(c)),
            Fused::Nmsub => (neg(a), c),
            Fused::Nmadd => (neg(a), neg(c)),
        };
        self.write(rd, libm("fma", fmt, vec![a, b, c]));
        Some(())
    }

    /// Lifts a compare: the 0 or 1 its ordered predicate holds, false for
    /// a NaN on either side.
    ///
    /// # Arguments
    ///
    /// * `op` - The predicate.
    /// * `fmt` - The format.
    /// * `rd` - The integer destination.
    /// * `(rs1, rs2)` - The two sources.
    ///
    /// # Returns
    ///
    /// `None` for a source this does not read.
    fn compare(&mut self, op: FCmp, fmt: Fmt, rd: Reg, (rs1, rs2): (Reg, Reg)) -> Option<()> {
        let (a, b) = (self.fread(rs1, fmt)?, self.fread(rs2, fmt)?);
        let p = match op {
            FCmp::Eq => FPred::Oeq,
            FCmp::Lt => FPred::Olt,
            FCmp::Le => FPred::Ole,
        };
        let truth = Expr::Cond(Box::new(Cond {
            cc: Cc(ConditionCode::ne),
            flags: Flags::FCmp(p, a, b, ty(fmt).bits()),
        }));
        self.write(rd, truth);
        Some(())
    }

    /// Lifts the arithmetic, the minimum and maximum, and a sign injection
    /// of a register with itself.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    /// * `fmt` - The format.
    /// * `(rd, rs1, rs2)` - The destination and the two sources.
    /// * `rm` - The rounding mode field.
    ///
    /// # Returns
    ///
    /// `None` for a form this does not model.
    fn arith(
        &mut self,
        op: FArith,
        fmt: Fmt,
        (rd, rs1, rs2): (Reg, Reg, Reg),
        rm: u8,
    ) -> Option<()> {
        let t = ty(fmt);
        let near = matches!(rm, RNE | DYN);
        let a = self.fread(rs1, fmt)?;
        let mut binary = |fop: Op, a: Expr| {
            let b = self.fread(rs2, fmt)?;
            Some(bear_width(fold(fop, a, b, 64), t))
        };
        let v = match op {
            FArith::Add if near => binary(Op::FAdd, a)?,
            FArith::Sub if near => binary(Op::FSub, a)?,
            FArith::Mul if near => binary(Op::FMul, a)?,
            FArith::Div if near => binary(Op::FDiv, a)?,
            FArith::Min | FArith::Max => {
                let b = self.fread(rs2, fmt)?;
                let name = if op == FArith::Min { "fmin" } else { "fmax" };
                libm(name, fmt, vec![a, b])
            }
            FArith::Sgnj if rs1 == rs2 => a,
            FArith::Sgnjn | FArith::Sgnjx if rs1 == rs2 && !a.is_float() => {
                let sign = 1u64 << (t.bits() - 1);
                let bits = if op == FArith::Sgnjn {
                    fold(Op::Xor, a, Expr::Const(sign), 64)
                } else {
                    fold(Op::And, a, Expr::Const(sign - 1), 64)
                };
                bitcast(bits, t)
            }
            FArith::Sgnjn if rs1 == rs2 => Expr::Un(UnOp::Neg, Box::new(a)),
            FArith::Sgnjx if rs1 == rs2 => Expr::Un(UnOp::Fabs, Box::new(a)),
            FArith::Add
            | FArith::Sub
            | FArith::Mul
            | FArith::Div
            | FArith::Sgnj
            | FArith::Sgnjn
            | FArith::Sgnjx => return None,
        };
        self.write(rd, v);
        Some(())
    }

    /// Lifts a conversion toward zero into an integer, a 32-bit result
    /// sign-extended as the register takes it.
    ///
    /// # Arguments
    ///
    /// * `fmt` - The float format.
    /// * `int` - The integer format.
    /// * `rd` - The destination.
    /// * `rs1` - The source.
    ///
    /// # Returns
    ///
    /// `None` for a source this does not read.
    fn round_to_int(&mut self, fmt: Fmt, int: IntFmt, rd: Reg, rs1: Reg) -> Option<()> {
        let x = self.fread(rs1, fmt)?;
        let (signed, bits) = match int {
            IntFmt::W => (true, 32),
            IntFmt::Wu => (false, 32),
            IntFmt::L => (true, 64),
            IntFmt::Lu => (false, 64),
        };
        let round = RoundToInt::new(signed, bits)?.nan_max();
        let fb = u64::from(ty(fmt).bits());
        let v = Expr::Helper(Helper::RoundToInt(round), vec![x, Expr::Const(fb)]);
        let v = if bits == 32 && self.xlen == Xlen::X64 {
            sign_extend(v, 32)
        } else {
            v
        };
        self.write(rd, v);
        Some(())
    }

    /// Lifts a conversion of an integer to a float: a cast of the integer,
    /// signed or not as the format says.
    ///
    /// # Arguments
    ///
    /// * `fmt` - The float format.
    /// * `int` - The integer format.
    /// * `(rd, rs1)` - The destination and the source.
    /// * `rm` - The rounding mode field.
    ///
    /// # Returns
    ///
    /// `None` when the conversion may round in a mode other than to
    /// nearest: only a word into a double is always exact.
    fn cast_int(&mut self, fmt: Fmt, int: IntFmt, (rd, rs1): (Reg, Reg), rm: u8) -> Option<()> {
        let exact = fmt == Fmt::D && matches!(int, IntFmt::W | IntFmt::Wu);
        if !exact && !matches!(rm, RNE | DYN) {
            return None;
        }
        let v = self.get(rs1);
        let n = match int {
            IntFmt::W => Expr::Sext(Box::new(v), 32),
            IntFmt::Wu => mask(v, mask_bits(32)),
            IntFmt::L => Expr::Sext(Box::new(v), 64),
            IntFmt::Lu => v,
        };
        self.write(rd, Expr::Cast(Box::new(n), ty(fmt)));
        Some(())
    }
}
