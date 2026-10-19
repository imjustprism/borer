//! The VFP instructions of the ARM32 machine: the loads and stores, the
//! moves, the arithmetic, the compares and the conversions.
//!
//! Every value computes as a double, a single rounding to a single at the
//! operation as the arm64 machine's model does, so the two machines and
//! the decompiler's checks answer alike. A float converted to an integer
//! saturates, a NaN going to zero, as the architecture says.

use super::Machine;
use super::exec::unmodeled;
use crate::emulate::Stop;
use crate::isa::a32::{Cvt, FpOp, FpUn, Insn, Op, PC, Reg, run};
use crate::num::lo32;

/// The sign bit of a single.
const SIGN_32: u64 = 0x8000_0000;
/// The sign bit of a double.
const SIGN_64: u64 = 0x8000_0000_0000_0000;

/// A float's value from its bits, as the double the model computes on.
///
/// # Arguments
///
/// * `raw` - The bits.
/// * `double` - Whether they are a double's, else a single's.
fn of_bits(raw: u64, double: bool) -> f64 {
    if double {
        f64::from_bits(raw)
    } else {
        f64::from(f32::from_bits(lo32(raw)))
    }
}

/// A double's value as the bits of the precision written, a single
/// rounding there.
///
/// # Arguments
///
/// * `v` - The value.
/// * `double` - Whether the destination is a double.
fn to_bits(v: f64, double: bool) -> u64 {
    if double {
        v.to_bits()
    } else {
        #[expect(
            clippy::cast_possible_truncation,
            reason = "a single's operation rounds to a single, as the machine does"
        )]
        let r = v as f32;
        u64::from(r.to_bits())
    }
}

/// A float converted to a 32-bit integer: rounded toward zero or to
/// nearest-even, saturated, a NaN to zero.
///
/// # Arguments
///
/// * `x` - The value.
/// * `signed` - Whether the integer is signed.
/// * `nearest` - Round to nearest-even, else toward zero.
fn to_int(x: f64, signed: bool, nearest: bool) -> u32 {
    let t = if nearest {
        x.round_ties_even()
    } else {
        x.trunc()
    };
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "a float-to-integer `as` saturates and takes a NaN to zero, as the instruction does"
    )]
    if signed {
        (t as i32).cast_unsigned()
    } else {
        t as u32
    }
}

impl Machine<'_> {
    /// Reads a single: a half of a double.
    ///
    /// # Arguments
    ///
    /// * `n` - Its number, 0 to 31.
    pub(super) fn single(&self, n: u8) -> u32 {
        let d = self.d.get(usize::from(n / 2)).copied().unwrap_or(0);
        lo32(if n % 2 == 1 { d >> 32 } else { d })
    }

    /// Writes a single, the other half of its double kept.
    ///
    /// # Arguments
    ///
    /// * `n` - Its number, 0 to 31.
    /// * `v` - The bits.
    pub(super) fn set_single(&mut self, n: u8, v: u32) {
        if let Some(d) = self.d.get_mut(usize::from(n / 2)) {
            *d = if n % 2 == 1 {
                (*d & 0xffff_ffff) | (u64::from(v) << 32)
            } else {
                (*d & !0xffff_ffff) | u64::from(v)
            };
        }
    }

    /// Reads a double.
    ///
    /// # Arguments
    ///
    /// * `n` - Its number, 0 to 31.
    pub(super) fn double(&self, n: u8) -> u64 {
        self.d.get(usize::from(n)).copied().unwrap_or(0)
    }

    /// Writes a double.
    ///
    /// # Arguments
    ///
    /// * `n` - Its number, 0 to 31.
    /// * `v` - The bits.
    pub(super) fn set_double(&mut self, n: u8, v: u64) {
        if let Some(d) = self.d.get_mut(usize::from(n)) {
            *d = v;
        }
    }

    /// Reads a VFP register's bits.
    ///
    /// # Arguments
    ///
    /// * `r` - The register: `s` or `d`.
    fn vget(&self, r: Reg) -> u64 {
        match r {
            Reg::S(n) => u64::from(self.single(n)),
            Reg::D(n) => self.double(n),
            Reg::R(n) => u64::from(self.r.get(usize::from(n)).copied().unwrap_or(0)),
        }
    }

    /// Writes a VFP register's bits.
    ///
    /// # Arguments
    ///
    /// * `r` - The register: `s` or `d`.
    /// * `v` - The bits; a single keeps the low 32.
    fn vset(&mut self, r: Reg, v: u64) {
        match r {
            Reg::S(n) => self.set_single(n, lo32(v)),
            Reg::D(n) => self.set_double(n, v),
            Reg::R(n) => {
                if let Some(slot) = self.r.get_mut(usize::from(n)) {
                    *slot = lo32(v);
                }
            }
        }
    }

    /// A VFP register's value as the double the model computes on.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn value(&self, r: Reg) -> f64 {
        of_bits(self.vget(r), matches!(r, Reg::D(_)))
    }

    /// Executes a VFP instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    ///
    /// # Errors
    ///
    /// When a memory access faults.
    pub(super) fn vfp(&mut self, i: &Insn) -> Result<(), Stop> {
        match i.op {
            Op::VLoad { vd, addr } => {
                let (at, _) = self.address(i, addr);
                let bytes = if matches!(vd, Reg::D(_)) { 8 } else { 4 };
                let v = self.load(u64::from(at), bytes)?;
                self.vset(vd, v);
            }
            Op::VStore { vd, addr } => {
                let (at, _) = self.address(i, addr);
                let bytes = if matches!(vd, Reg::D(_)) { 8 } else { 4 };
                let v = self.vget(vd);
                self.store(u64::from(at), bytes, v)?;
            }
            Op::VLdm {
                rn,
                first,
                count,
                wback,
                db,
            }
            | Op::VStm {
                rn,
                first,
                count,
                wback,
                db,
            } => {
                let load = matches!(i.op, Op::VLdm { .. });
                let size = if matches!(first, Reg::D(_)) { 8 } else { 4 };
                let span = u32::from(count) * size;
                let base = self.get(rn, i);
                let start = if db { base.wrapping_sub(span) } else { base };
                for (k, r) in (0u32..).zip(run(first, count)) {
                    let at = u64::from(start.wrapping_add(k * size));
                    if load {
                        let v = self.load(at, usize::try_from(size).unwrap_or(4))?;
                        self.vset(r, v);
                    } else {
                        let v = self.vget(r);
                        self.store(at, usize::try_from(size).unwrap_or(4), v)?;
                    }
                }
                if wback {
                    self.set(
                        rn,
                        if db {
                            base.wrapping_sub(span)
                        } else {
                            base.wrapping_add(span)
                        },
                    );
                }
            }
            Op::FpBin { op, vd, vn, vm } => {
                let double = matches!(vd, Reg::D(_));
                let (d, n, m) = (self.value(vd), self.value(vn), self.value(vm));
                let round = |v: f64| of_bits(to_bits(v, double), double);
                let v = match op {
                    FpOp::Add => n + m,
                    FpOp::Sub => n - m,
                    FpOp::Mul => n * m,
                    FpOp::Div => n / m,
                    FpOp::Nmul => -round(n * m),
                    FpOp::Mla => d + round(n * m),
                    FpOp::Mls => d - round(n * m),
                    FpOp::Nmla => -d - round(n * m),
                    FpOp::Nmls => -d + round(n * m),
                    FpOp::Fma => n.mul_add(m, d),
                    FpOp::Fms => (-n).mul_add(m, d),
                    FpOp::Fnma => (-n).mul_add(m, -d),
                    FpOp::Fnms => n.mul_add(m, -d),
                };
                self.vset(vd, to_bits(v, double));
            }
            Op::FpUn { op, vd, vm } => {
                let double = matches!(vd, Reg::D(_));
                let sign = if double { SIGN_64 } else { SIGN_32 };
                let bits = self.vget(vm);
                let v = match op {
                    FpUn::Mov => bits,
                    FpUn::Abs => bits & !sign,
                    FpUn::Neg => bits ^ sign,
                    FpUn::Sqrt => to_bits(of_bits(bits, double).sqrt(), double),
                };
                self.vset(vd, v);
            }
            Op::FpImm { vd, imm8 } => {
                let bits = if matches!(vd, Reg::D(_)) { 64 } else { 32 };
                let v = crate::emulate::a64::vfp_expand(u32::from(imm8), bits)
                    .ok_or_else(|| unmodeled(i))?;
                self.vset(vd, v);
            }
            Op::FpCmp { vd, vm } => {
                let x = self.value(vd);
                let y = vm.map_or(0.0, |m| self.value(m));
                let flags: u32 = match x.partial_cmp(&y) {
                    None => 0b0011,
                    Some(std::cmp::Ordering::Less) => 0b1000,
                    Some(std::cmp::Ordering::Equal) => 0b0110,
                    Some(std::cmp::Ordering::Greater) => 0b0010,
                };
                self.fpscr = (self.fpscr & 0x0fff_ffff) | (flags << 28);
            }
            Op::Vcvt { cvt, vd, vm } => {
                let v = match cvt {
                    Cvt::SingleToDouble => to_bits(self.value(vm), true),
                    Cvt::DoubleToSingle => to_bits(self.value(vm), false),
                    Cvt::SignedToFloat => to_bits(
                        f64::from(lo32(self.vget(vm)).cast_signed()),
                        matches!(vd, Reg::D(_)),
                    ),
                    Cvt::UnsignedToFloat => {
                        to_bits(f64::from(lo32(self.vget(vm))), matches!(vd, Reg::D(_)))
                    }
                    Cvt::FloatToSigned => u64::from(to_int(self.value(vm), true, false)),
                    Cvt::FloatToUnsigned => u64::from(to_int(self.value(vm), false, false)),
                    Cvt::FloatToSignedR => u64::from(to_int(self.value(vm), true, true)),
                    Cvt::FloatToUnsignedR => u64::from(to_int(self.value(vm), false, true)),
                };
                self.vset(vd, v);
            }
            Op::VmovCore { to_core, rt, sn } => {
                if to_core {
                    let v = lo32(self.vget(sn));
                    self.set(rt, v);
                } else {
                    let v = self.get(rt, i);
                    self.vset(sn, u64::from(v));
                }
            }
            Op::VmovPair {
                to_core,
                rt,
                rt2,
                dm,
            } => {
                if to_core {
                    let v = self.vget(dm);
                    self.set(rt, lo32(v));
                    self.set(rt2, lo32(v >> 32));
                } else {
                    let v = (u64::from(self.get(rt2, i)) << 32) | u64::from(self.get(rt, i));
                    self.vset(dm, v);
                }
            }
            Op::Vmrs { rt } => {
                if rt == PC {
                    let f = self.fpscr;
                    self.set_nzcv(f);
                } else {
                    let f = self.fpscr;
                    self.set(rt, f);
                }
            }
            Op::Vmsr { rt } => self.fpscr = self.get(rt, i),
            Op::Dp { .. }
            | Op::Movw { .. }
            | Op::Movt { .. }
            | Op::Adr { .. }
            | Op::Mul { .. }
            | Op::MulLong { .. }
            | Op::Div { .. }
            | Op::Clz { .. }
            | Op::Rbit { .. }
            | Op::Rev { .. }
            | Op::Rev16 { .. }
            | Op::Revsh { .. }
            | Op::Smmul { .. }
            | Op::Smulxy { .. }
            | Op::Bfx { .. }
            | Op::Sat { .. }
            | Op::Bfi { .. }
            | Op::Extend { .. }
            | Op::Load { .. }
            | Op::Store { .. }
            | Op::LoadEx { .. }
            | Op::StoreEx { .. }
            | Op::LoadDual { .. }
            | Op::StoreDual { .. }
            | Op::Ldm { .. }
            | Op::Stm { .. }
            | Op::B { .. }
            | Op::Bl { .. }
            | Op::Blx { .. }
            | Op::BlxReg { .. }
            | Op::Bx { .. }
            | Op::Cbz { .. }
            | Op::Tb { .. }
            | Op::It { .. }
            | Op::Svc { .. }
            | Op::Trap
            | Op::Nop
            | Op::Mrs { .. }
            | Op::Msr { .. }
            | Op::Neon { .. }
            | Op::Unknown
            | Op::Invalid => return Err(unmodeled(i)),
        }
        Ok(())
    }
}
