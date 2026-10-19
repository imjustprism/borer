//! The VFP instructions for the ARM32 lifter: the loads and stores, the
//! moves between core and VFP registers, the arithmetic, the compares and
//! the conversions.
//!
//! A single computes as [`Ty::F32`] and a double as [`Ty::F64`], over the
//! shared float operations, as the arm64 lifter's scalars do; an integer
//! constant read as a float is the float its bits are. `vcmp` sets
//! `FPSCR`'s flags to a float compare, which `vmrs APSR_nzcv, fpscr`
//! moves into the flags the conditions read.

use super::super::expr::{Expr, Flags, Key, Op, RoundToInt, Ty, UnOp, fold, unary};
use super::super::helper::Helper;
use super::super::lift_a64::mem::{as_integer_bits, bear_width, float_width, put_at};
use super::{Lift, offset};
use crate::isa::a32::{Cvt, FpOp, FpUn, Insn, Op as AOp, PC, Reg, run};

/// The float type of a VFP register.
///
/// # Arguments
///
/// * `r` - The register.
fn ty(r: Reg) -> Ty {
    match r {
        Reg::D(_) => Ty::F64,
        Reg::R(_) | Reg::S(_) => Ty::F32,
    }
}

/// The width in bits of a VFP register.
///
/// # Arguments
///
/// * `r` - The register.
fn bits(r: Reg) -> u16 {
    match r {
        Reg::D(_) => 64,
        Reg::R(_) | Reg::S(_) => 32,
    }
}

/// A register's value as the float of type `t` its bits are: a float
/// expression or a bare register as it is, any other integer bits
/// reinterpreted, not converted.
///
/// # Arguments
///
/// * `x` - The value.
/// * `t` - The float type, [`Ty::F32`] or [`Ty::F64`].
fn as_float(x: Expr, t: Ty) -> Expr {
    if x.is_float() || float_width(&x).is_some() || matches!(x, Expr::Var(_)) {
        x
    } else {
        Expr::Bitcast(Box::new(x), t)
    }
}

/// A single's value as the 32-bit integer its bits are, for a conversion
/// that reads them as one: a single loaded from memory is the word there.
///
/// # Arguments
///
/// * `x` - The value.
fn integer(x: Expr) -> Expr {
    if let Expr::Deref(at, Ty::F32) = x {
        return Expr::Deref(at, Ty::U32);
    }
    if x.is_float() || float_width(&x).is_some() {
        as_integer_bits(x, 32)
    } else {
        x
    }
}

impl Lift<'_, '_> {
    /// Reads a VFP register as a float operand: an integer constant is the
    /// float its bits are.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `r` - The register.
    fn float(&self, i: &Insn, r: Reg) -> Expr {
        match self.get(i, r) {
            Expr::Const(c) => Expr::FConst(c, ty(r)),
            other => other,
        }
    }

    /// Records the first type a register is seen at.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn note(&mut self, r: Reg) {
        self.ex.ctx.reg_ty.entry(Key::A32(r)).or_insert(ty(r));
    }

    /// Lifts a VFP instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Returns
    ///
    /// `None` for a form not modeled.
    pub(super) fn vfp(&mut self, i: &Insn) -> Option<()> {
        match i.op {
            AOp::VLoad { vd, addr } => {
                let (at, _) = self.address(i, addr);
                self.note(vd);
                let v = match self.literal(addr, &at, bits(vd) / 8) {
                    Some(c) => Expr::FConst(c, ty(vd)),
                    None => self.ex.read_at(at, ty(vd)),
                };
                self.write(vd, v);
            }
            AOp::VStore { vd, addr } => {
                let (at, _) = self.address(i, addr);
                let held = self.get(i, vd);
                let (t, v) = put_at(held, ty(vd), None);
                self.ex.store_at(at, t, v);
            }
            AOp::VLdm {
                rn,
                first,
                count,
                wback,
                db,
            } => {
                let size = i64::from(bits(first) / 8);
                let span = size * i64::from(count);
                let base = self.get(i, rn);
                let start = if db {
                    offset(base.clone(), -span)
                } else {
                    base.clone()
                };
                let mut writes: Vec<(Reg, Expr)> = run(first, count)
                    .zip(0i64..)
                    .map(|(r, k)| (r, self.ex.read_at(offset(start.clone(), k * size), ty(r))))
                    .collect();
                if wback {
                    writes.push((rn, offset(base, if db { -span } else { span })));
                }
                self.write_all(writes);
            }
            AOp::VStm {
                rn,
                first,
                count,
                wback,
                db,
            } => {
                let size = i64::from(bits(first) / 8);
                let span = size * i64::from(count);
                let base = self.get(i, rn);
                let start = if db {
                    offset(base.clone(), -span)
                } else {
                    base.clone()
                };
                let values: Vec<(Reg, Expr)> =
                    run(first, count).map(|r| (r, self.get(i, r))).collect();
                for ((r, v), k) in values.into_iter().zip(0i64..) {
                    let (t, v) = put_at(v, ty(r), None);
                    self.ex.store_at(offset(start.clone(), k * size), t, v);
                }
                if wback {
                    self.write(rn, offset(base, if db { -span } else { span }));
                }
            }
            AOp::FpBin { op, vd, vn, vm } => {
                let t = ty(vd);
                self.note(vn);
                self.note(vm);
                let (n, m) = (self.float(i, vn), self.float(i, vm));
                let product = || bear_width(fold(Op::FMul, n.clone(), m.clone(), 64), t);
                let d = || self.float(i, vd);
                let neg = |e: Expr| unary(UnOp::Neg, e, 64);
                let v = match op {
                    FpOp::Add => fold(Op::FAdd, n.clone(), m.clone(), 64),
                    FpOp::Sub => fold(Op::FSub, n.clone(), m.clone(), 64),
                    FpOp::Mul => fold(Op::FMul, n.clone(), m.clone(), 64),
                    FpOp::Div => fold(Op::FDiv, n.clone(), m.clone(), 64),
                    FpOp::Nmul => neg(product()),
                    FpOp::Mla | FpOp::Fma => fold(Op::FAdd, d(), product(), 64),
                    FpOp::Mls | FpOp::Fms => fold(Op::FSub, d(), product(), 64),
                    FpOp::Nmla | FpOp::Fnma => fold(Op::FSub, neg(d()), product(), 64),
                    FpOp::Nmls | FpOp::Fnms => fold(Op::FSub, product(), d(), 64),
                };
                self.note(vd);
                self.write(vd, bear_width(v, t));
            }
            AOp::FpUn { op, vd, vm } => {
                let t = ty(vd);
                let x = self.float(i, vm);
                let v = match op {
                    FpUn::Mov => x,
                    FpUn::Neg | FpUn::Abs if !x.is_float() => {
                        let op = if op == FpUn::Neg {
                            UnOp::Neg
                        } else {
                            UnOp::Fabs
                        };
                        Expr::Un(op, Box::new(Expr::Bitcast(Box::new(x), t)))
                    }
                    FpUn::Neg => bear_width(unary(UnOp::Neg, x, 64), t),
                    FpUn::Abs => bear_width(Expr::Un(UnOp::Fabs, Box::new(x)), t),
                    FpUn::Sqrt => {
                        self.note(vm);
                        bear_width(Expr::Un(UnOp::Sqrt, Box::new(x)), t)
                    }
                };
                self.write(vd, v);
            }
            AOp::FpImm { vd, imm8 } => {
                let v = crate::emulate::a64::vfp_expand(u32::from(imm8), bits(vd))?;
                self.note(vd);
                self.write(vd, Expr::FConst(v, ty(vd)));
            }
            AOp::FpCmp { vd, vm } => {
                let a = as_float(self.float(i, vd), ty(vd));
                let b = vm.map_or(Expr::FConst(0, ty(vd)), |m| {
                    as_float(self.float(i, m), ty(vd))
                });
                let width = u8::try_from(bits(vd)).ok()?;
                self.fp_flags = Flags::Float(a, b, width);
            }
            AOp::Vmrs { rt: PC } => {
                self.ex.flags = self.fp_flags.clone();
            }
            AOp::Vcvt { cvt, vd, vm } => {
                let x = self.float(i, vm);
                let v = match cvt {
                    Cvt::SingleToDouble | Cvt::DoubleToSingle => {
                        Expr::Cast(Box::new(as_float(x, ty(vm))), ty(vd))
                    }
                    Cvt::SignedToFloat => {
                        let raw = integer(self.get(i, vm));
                        Expr::Cast(Box::new(Expr::Sext(Box::new(raw), 32)), ty(vd))
                    }
                    Cvt::UnsignedToFloat => {
                        let raw = integer(self.get(i, vm));
                        Expr::Cast(Box::new(super::super::expr::mask(raw, 0xffff_ffff)), ty(vd))
                    }
                    Cvt::FloatToSigned | Cvt::FloatToUnsigned => {
                        let round = RoundToInt::new(cvt == Cvt::FloatToSigned, 32)?;
                        Expr::Helper(
                            Helper::RoundToInt(round),
                            vec![x, Expr::Const(u64::from(bits(vm)))],
                        )
                    }
                    Cvt::FloatToSignedR | Cvt::FloatToUnsignedR => return None,
                };
                self.note(vd);
                self.write(vd, v);
            }
            AOp::VmovCore { to_core, rt, sn } => {
                if to_core {
                    let v = self.get(i, sn);
                    let v = if v.is_float() || float_width(&v).is_some() {
                        as_integer_bits(v, 32)
                    } else {
                        v
                    };
                    self.put(rt, v)?;
                } else {
                    let v = self.get(i, rt);
                    self.write(sn, v);
                }
            }
            AOp::VmovPair {
                to_core,
                rt,
                rt2,
                dm,
            } => {
                if to_core {
                    let v = self.get(i, dm);
                    let lo = as_integer_bits(v.clone(), 32);
                    let hi = Expr::Call("__hi32".to_owned(), vec![v]);
                    self.write_all(vec![(rt, lo), (rt2, hi)]);
                } else {
                    let v =
                        Expr::Call("__pair".to_owned(), vec![self.get(i, rt), self.get(i, rt2)]);
                    self.write(dm, v);
                }
            }
            AOp::Vmrs { .. }
            | AOp::Vmsr { .. }
            | AOp::Dp { .. }
            | AOp::Movw { .. }
            | AOp::Movt { .. }
            | AOp::Adr { .. }
            | AOp::Mul { .. }
            | AOp::MulLong { .. }
            | AOp::Smmul { .. }
            | AOp::Smulxy { .. }
            | AOp::Div { .. }
            | AOp::Clz { .. }
            | AOp::Rbit { .. }
            | AOp::Rev { .. }
            | AOp::Rev16 { .. }
            | AOp::Revsh { .. }
            | AOp::Bfx { .. }
            | AOp::Sat { .. }
            | AOp::Bfi { .. }
            | AOp::Extend { .. }
            | AOp::Load { .. }
            | AOp::Store { .. }
            | AOp::LoadEx { .. }
            | AOp::StoreEx { .. }
            | AOp::LoadDual { .. }
            | AOp::StoreDual { .. }
            | AOp::Ldm { .. }
            | AOp::Stm { .. }
            | AOp::B { .. }
            | AOp::Bl { .. }
            | AOp::Blx { .. }
            | AOp::BlxReg { .. }
            | AOp::Bx { .. }
            | AOp::Cbz { .. }
            | AOp::Tb { .. }
            | AOp::It { .. }
            | AOp::Svc { .. }
            | AOp::Trap
            | AOp::Nop
            | AOp::Mrs { .. }
            | AOp::Msr { .. }
            | AOp::Neon { .. }
            | AOp::Unknown
            | AOp::Invalid => return None,
        }
        Some(())
    }
}
