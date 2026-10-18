//! Advanced SIMD lane operations, named as calls over the registers.
//!
//! A lane operation over a `v` register has no one value the expression
//! tree holds, so the lifter names it as the instruction with its
//! arrangement, `__cmeq_16b(v0, v1)`, as [`Lift::vector_arith`] names
//! `add`, and the text spells it as C's vector extension
//! ([`super::super::vector`]). A widening operation's arrangement is its
//! destination's and its name ends in `2` where it reads the upper half
//! of its narrow sources (`__smlal2_4s`). A lane read into a general
//! register is the shift and mask it is while the lane lies in the low
//! 64 bits. Every field is read from the word, as the emulator reads it.

use super::super::expr::{Expr, Op, fold};
use super::float::{packed_name, vreg};
use super::{Lift, low, low64};
use crate::isa::a64::{Insn, Opnd, Simd};

/// The bits 28 to 24 of an Advanced SIMD vector word's integer forms; a
/// scalar form sets bit 28, a shift-by-immediate form bit 24.
const VECTOR_INTEGER: u32 = 0b0_1110;

/// The name an operation's call takes, its mnemonic.
///
/// # Arguments
///
/// * `op` - The operation.
fn mnemonic(op: Simd) -> &'static str {
    match op {
        Simd::Addv => "addv",
        Simd::Cmeq => "cmeq",
        Simd::Cmgt => "cmgt",
        Simd::Cmge => "cmge",
        Simd::Cmhi => "cmhi",
        Simd::Cmhs => "cmhs",
        Simd::Cmle => "cmle",
        Simd::Cmlt => "cmlt",
        Simd::Ushll => "ushll",
        Simd::Sshll => "sshll",
        Simd::Ext => "ext",
        Simd::Ins => "ins",
        Simd::Umov => "umov",
        Simd::Smin => "smin",
        Simd::Smax => "smax",
        Simd::Umin => "umin",
        Simd::Umax => "umax",
        Simd::Sminv => "sminv",
        Simd::Smaxv => "smaxv",
        Simd::Uminv => "uminv",
        Simd::Umaxv => "umaxv",
        Simd::Smlal => "smlal",
        Simd::Umlal => "umlal",
        Simd::Smull => "smull",
        Simd::Umull => "umull",
        Simd::Saddw => "saddw",
        Simd::Uaddw => "uaddw",
        Simd::Addp => "addp",
        Simd::Mla => "mla",
    }
}

/// The lane width and index an `imm5` field names: its lowest set bit the
/// width (8 to 64 bits), the bits above it the index.
///
/// # Arguments
///
/// * `imm5` - The field.
///
/// # Returns
///
/// `(lane bits, index)`, or `None` for an `imm5` naming no width.
fn element(imm5: u32) -> Option<(u16, u32)> {
    let shift = (0..4).find(|&s| imm5 >> s & 1 == 1)?;
    Some((8u16 << shift, imm5 >> (shift + 1)))
}

impl Lift<'_, '_> {
    /// Lifts an Advanced SIMD lane operation.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - Which operation.
    ///
    /// # Returns
    ///
    /// `None` for a form or an arrangement the operation is not modeled
    /// in; nothing was written then.
    pub(super) fn simd(&mut self, i: &Insn, op: Simd) -> Option<()> {
        let w = i.word;
        let whole = (w >> 30) & 1 == 1;
        let lane = 8u16 << ((w >> 22) & 3);
        let vector = (w >> 24) & 0x1f == VECTOR_INTEGER;
        let v = |s: &Self, at: u32| s.reg_at(vreg(w, at), 128);
        let name = mnemonic(op);
        let call = |name: &str, lane: u16, whole: bool, args: Vec<Expr>| {
            Expr::Call(packed_name(name, lane, whole), args)
        };
        let value = match op {
            Simd::Addv | Simd::Sminv | Simd::Smaxv | Simd::Uminv | Simd::Umaxv => {
                if !vector || lane == 64 || (lane == 32 && !whole) {
                    return None;
                }
                call(name, lane, whole, vec![v(self, 5)])
            }
            Simd::Cmeq
            | Simd::Cmgt
            | Simd::Cmge
            | Simd::Cmhi
            | Simd::Cmhs
            | Simd::Cmle
            | Simd::Cmlt => {
                if !vector || (lane == 64 && !whole) {
                    return None;
                }
                let against = if (w >> 10) & 1 == 1 {
                    v(self, 16)
                } else {
                    Expr::Const(0)
                };
                call(name, lane, whole, vec![v(self, 5), against])
            }
            Simd::Smin | Simd::Smax | Simd::Umin | Simd::Umax | Simd::Addp => {
                if lane == 64 && !whole {
                    return None;
                }
                if !vector {
                    let pairwise = op == Simd::Addp && lane == 64 && whole;
                    return pairwise.then(|| {
                        let sum = call(name, 64, true, vec![v(self, 5)]);
                        self.write(vreg(w, 0), 128, sum);
                    });
                }
                call(name, lane, whole, vec![v(self, 5), v(self, 16)])
            }
            Simd::Mla => {
                if !vector || lane == 64 {
                    return None;
                }
                call(name, lane, whole, vec![v(self, 0), v(self, 5), v(self, 16)])
            }
            Simd::Smlal | Simd::Umlal | Simd::Smull | Simd::Umull | Simd::Saddw | Simd::Uaddw => {
                if !vector || lane == 64 {
                    return None;
                }
                let half = if whole {
                    format!("{name}2")
                } else {
                    name.to_owned()
                };
                let mut args = vec![v(self, 5), v(self, 16)];
                if matches!(op, Simd::Smlal | Simd::Umlal) {
                    args.insert(0, v(self, 0));
                }
                call(&half, lane * 2, true, args)
            }
            Simd::Ushll | Simd::Sshll => {
                let immh = (w >> 19) & 0xf;
                let from: u16 = match immh {
                    1 => 8,
                    2 | 3 => 16,
                    4..=7 => 32,
                    _ => return None,
                };
                let shift = ((w >> 16) & 0x7f) - u32::from(from);
                let half = if whole {
                    format!("{name}2")
                } else {
                    name.to_owned()
                };
                call(
                    &half,
                    from * 2,
                    true,
                    vec![v(self, 5), Expr::Const(u64::from(shift))],
                )
            }
            Simd::Ext => {
                let at = (w >> 11) & 0xf;
                if !whole && at >= 8 {
                    return None;
                }
                call(
                    name,
                    8,
                    whole,
                    vec![v(self, 5), v(self, 16), Expr::Const(u64::from(at))],
                )
            }
            Simd::Ins => {
                let (bits, index) = element((w >> 16) & 0x1f)?;
                let put = if (w >> 29) & 1 == 1 {
                    let from = ((w >> 11) & 0xf) >> (bits / 8).trailing_zeros();
                    lane_of(v(self, 5), from, bits)
                } else {
                    let Opnd::Reg { reg, bits: width } = i.operands[1] else {
                        return None;
                    };
                    low(self.reg_at(reg, width), bits)
                };
                call(
                    name,
                    bits,
                    true,
                    vec![v(self, 0), put, Expr::Const(u64::from(index))],
                )
            }
            Simd::Umov => {
                let (bits, index) = element((w >> 16) & 0x1f)?;
                let Opnd::Reg { reg, bits: width } = i.operands[0] else {
                    return None;
                };
                self.write(reg, width, lane_of(v(self, 5), index, bits));
                return Some(());
            }
        };
        self.write(vreg(w, 0), 128, value);
        Some(())
    }

    /// `scvtf` and `ucvtf` (vector, integer): each lane converted to the
    /// float of its width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `signed` - Whether the integers are signed.
    pub(super) fn int_to_float_array(&mut self, i: &Insn, signed: bool) -> Option<()> {
        let w = i.word;
        if (w >> 24) & 0x1f != VECTOR_INTEGER {
            return None;
        }
        let lane = if (w >> 22) & 1 == 1 { 64 } else { 32 };
        let whole = (w >> 30) & 1 == 1;
        if lane == 64 && !whole {
            return None;
        }
        let name = if signed { "scvtf" } else { "ucvtf" };
        let x = self.reg_at(vreg(w, 5), 128);
        let v = Expr::Call(packed_name(name, lane, whole), vec![x]);
        self.write(vreg(w, 0), 128, v);
        Some(())
    }
}

/// One lane of a `v` register's value: a shift and mask of its low 64
/// bits, or the call naming the lane above them.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `index` - The lane.
/// * `bits` - The lane's width.
pub(super) fn lane_of(v: Expr, index: u32, bits: u16) -> Expr {
    let at = index * u32::from(bits);
    match at {
        0 => low(low64(v), bits),
        1..64 => low(
            fold(Op::Shr, low64(v), Expr::Const(u64::from(at)), 64),
            bits,
        ),
        _ => Expr::Call(
            packed_name("umov", bits, true),
            vec![v, Expr::Const(u64::from(index))],
        ),
    }
}
