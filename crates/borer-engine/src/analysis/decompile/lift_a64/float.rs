//! Scalar floating-point and vector instructions for the arm64 lifter.
//!
//! The x86 lifter types a float by where it came from: a memory load, a
//! conversion or a constant is a float expression, a register alone holds
//! its bits until a float instruction reads them, when an integer constant
//! becomes the float its bits are ([`Lift::float_source`]). The arm64
//! lifter keeps the same conventions, so a `v` register a `ldr s0, [x1]`
//! loaded carries [`Ty::F32`] from the access itself and the arithmetic
//! over it verifies against the machine ([`super::super::verify_a64`])
//! over the shared float operations [`Op::FAdd`] and friends.
//!
//! `fneg` of a bare register flips that lane's sign bit. A negation of
//! the integer would be a different value, so the bit is what is written.
//! A packed
//! float operation over lanes has no one value the tree could hold, as
//! the x86 lifter's own packed operations do not either, so it names the
//! instruction as an intrinsic over the registers ([`Lift::float_array`]);
//! the sign operations, which are bit operations at heart, mask the sign
//! bits instead.

use super::super::expr::{Expr, Flags, Key, Op, RoundToInt, Ty, UnOp, fold, ternary, unary};
use super::flags::{self, next_reader};
use super::step::imm;
use super::{Lift, low, vector, width8};
use crate::emulate::a64::expand_imm;
use crate::isa::a64::{Insn, Opnd, Reg};
use crate::num::lo8;

/// The bits of `v` as the float `src` names, not an integer converted to one.
///
/// `fcvt` then converts that float. A cast of the integer is `scvtf`,
/// which is a different number. Xoring with a zero of `src` keeps every
/// bit, a sign and a NaN included, and the cast of that xor is the
/// encoding. An integer zero would fold away. Adding zero would quiet a
/// NaN and turn a negative zero positive.
///
/// # Arguments
///
/// * `v` - The register's bits.
/// * `src` - The width the instruction reads, [`Ty::F32`] or [`Ty::F64`].
fn lane_bits(v: Expr, src: Ty) -> Expr {
    let bits = Expr::Bin(Op::Xor, Box::new(v), Box::new(Expr::FConst(0, src)));
    Expr::Cast(Box::new(bits), src)
}

/// The float type of a scalar width.
///
/// # Arguments
///
/// * `bits` - The width, 32 or 64 bits; the half forms have no type the C
///   vocabulary names.
fn ty(bits: u16) -> Option<Ty> {
    match bits {
        32 => Some(Ty::F32),
        64 => Some(Ty::F64),
        _ => None,
    }
}

/// The `v` register a vector encoding's field names.
///
/// # Arguments
///
/// * `w` - The encoded word.
/// * `at` - Where the register's number starts.
pub(super) fn vreg(w: u32, at: u32) -> Reg {
    Reg::V(lo8(u64::from((w >> at) & 0x1f)))
}

/// The arrangement suffix of a lane width over a span, as the assembly
/// writes it: `4s` for 32-bit lanes over the whole register.
///
/// # Arguments
///
/// * `lane` - The lane width in bits, 8 to 64.
/// * `whole` - Whether the arrangement covers all 128 bits.
fn arrangement(lane: u16, whole: bool) -> String {
    let letter = match lane {
        8 => "b",
        16 => "h",
        32 => "s",
        _ => "d",
    };
    let count = u64::from(if whole { 128 } else { 64 } / lane);
    format!("{count}{letter}")
}

/// The intrinsic name of a packed operation: its mnemonic with its
/// arrangement.
///
/// # Arguments
///
/// * `name` - The mnemonic.
/// * `lane` - The lane width in bits, 8 to 64.
/// * `whole` - Whether the arrangement covers all 128 bits.
pub(super) fn packed_name(name: &str, lane: u16, whole: bool) -> String {
    format!("__{}_{}", name, arrangement(lane, whole))
}

/// The lane width a vector floating-point word names: a single or a
/// double.
///
/// # Arguments
///
/// * `w` - The encoded word.
fn fp_lane(w: u32) -> u16 {
    if (w >> 22) & 1 == 1 { 64 } else { 32 }
}

/// Two to a power as a float constant of a width.
///
/// # Arguments
///
/// * `n` - The power, at most 63, so the value is exact at either width.
/// * `t` - The constant's type.
fn small_pow2(n: u64, t: Ty) -> Expr {
    let v = 2f64.powi(i32::try_from(n).unwrap_or(0));
    match t {
        Ty::F32 => {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "the value is exact at a single for the powers a shift names"
            )]
            let v = v as f32;
            Expr::FConst(u64::from(v.to_bits()), t)
        }
        _ => Expr::FConst(v.to_bits(), t),
    }
}

impl Lift<'_, '_> {
    /// Reads a scalar float operand: the register's value, with an integer
    /// constant retyped as the float its bits are, exactly as the x86
    /// lifter's `float_bits` does.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The operand's position.
    /// * `bits` - The width, 32 or 64.
    ///
    /// # Returns
    ///
    /// The value, or `None` for any other operand.
    fn float_source(&self, i: &Insn, k: usize, bits: u16) -> Option<Expr> {
        let Opnd::Reg {
            reg: reg @ Reg::V(_),
            ..
        } = *i.operands.get(k)?
        else {
            return None;
        };
        let t = ty(bits)?;
        Some(match self.reg_at(reg, bits) {
            Expr::Const(c) => Expr::FConst(c, t),
            other => other,
        })
    }

    /// Reads a scalar float operand at the width the instruction uses.
    ///
    /// A narrower float is that encoding, zero-extended, not the number.
    /// A wider float contributes the low bits of its encoding, not a
    /// rounded narrower number. A value already at this width, or not a
    /// float, is the register's value. A bare parameter has no float node;
    /// the width recorded for it is that float. `fcvt` converts the value
    /// this read produced.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The operand's position.
    /// * `bits` - The width, 32 or 64.
    fn float_read(&self, i: &Insn, k: usize, bits: u16) -> Option<Expr> {
        let v = self.float_source(i, k, bits)?;
        let known = self.declared_width(&v);
        Some(super::mem::as_encoding_at(v, bits, known))
    }

    /// Types the destination register's declaration, the first type seen
    /// winning, as the x86 lifter's `note_reg_ty` does.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `t` - The type its value has.
    fn note(&mut self, r: Reg, t: Ty) {
        self.ex.ctx.reg_ty.entry(Key::A64(r)).or_insert(t);
    }

    /// Records `t` as the first type of `r`.
    ///
    /// An `fmov` immediate is that float. A later use of the register
    /// reads this width, not the integer the bits happen to be.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `t` - The immediate's width.
    pub(super) fn note_lane(&mut self, r: Reg, t: Ty) {
        self.note(r, t);
    }

    /// Records the width a scalar float instruction reads a `v` register
    /// at, the first width winning, so a parameter that arrives in it is
    /// declared at that width.
    ///
    /// The same width is recorded on the parameter the register still
    /// holds. A later cast of that parameter converts the float, which a
    /// cast of an untyped parameter would not: the parameter's bits would
    /// be read as an integer.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `k` - The operand's position.
    /// * `t` - The width the instruction reads.
    fn note_float(&mut self, i: &Insn, k: usize, t: Ty) {
        if let Some(Opnd::Reg {
            reg: reg @ Reg::V(_),
            ..
        }) = i.operands.get(k).copied()
        {
            self.note(reg, t);
            self.note_own_param(reg, t);
        }
    }

    /// Records `t` on the parameter that arrives in `reg`, when the
    /// register still holds that parameter.
    ///
    /// A value moved in from another register is some other parameter.
    /// Stamping `t` on it would make a later cast of that integer convert
    /// as a float of the same width, which is a different number.
    ///
    /// # Arguments
    ///
    /// * `reg` - The `v` register.
    /// * `t` - The width the instruction uses.
    fn note_own_param(&mut self, reg: Reg, t: Ty) {
        let Expr::Var(key @ Key::Param(i)) = self.reg_at(reg, 64) else {
            return;
        };
        if super::shape::arg_reg(usize::from(i), self.ex.ctx.arg_floats) == Some(reg) {
            self.ex.ctx.reg_ty.entry(key).or_insert(t);
        }
    }

    /// A store of a `v` register that still holds its incoming parameter
    /// declares that parameter at the width the store writes.
    ///
    /// The register is only its name by then. Without the width, the store
    /// is an integer store of a float, and the number converts.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register stored.
    /// * `t` - The width the store writes.
    pub(super) fn note_stored_param(&mut self, reg: Reg, t: Ty) {
        if !matches!(t, Ty::F32 | Ty::F64) {
            return;
        }
        let Expr::Var(Key::Param(_)) = self.reg_at(reg, 64) else {
            return;
        };
        self.note(reg, t);
        self.note_own_param(reg, t);
    }

    /// The declared float width of a bare variable, when the expression
    /// itself does not say.
    ///
    /// The value written out carries its own width. The register's first
    /// note is the fallback, and only for a name.
    ///
    /// # Arguments
    ///
    /// * `v` - The value a float instruction reads.
    fn declared_width(&self, v: &Expr) -> Option<u8> {
        let Expr::Var(k) = v else {
            return None;
        };
        self.ex
            .early_value(*k)
            .and_then(super::mem::float_width)
            .or_else(|| {
                self.ex
                    .ctx
                    .reg_ty
                    .get(k)
                    .copied()
                    .and_then(super::mem::float_ty_bits)
            })
    }

    /// Whether `v` is already the float a conversion reads at `from`.
    ///
    /// A value that carries that width, including one an earlier read
    /// encoded for it, converts as the number. A bare name declared at
    /// that width does too: the cast is the conversion, and wrapping the
    /// name would read bits this instruction did not keep. Anything else
    /// is still an integer pattern.
    ///
    /// # Arguments
    ///
    /// * `v` - The value [`Lift::float_read`] returned.
    /// * `from` - The width the conversion reads, 32 or 64.
    fn at_source_width(&self, v: &Expr, from: u16) -> bool {
        let Ok(from) = u8::try_from(from) else {
            return false;
        };
        super::mem::float_width(v) == Some(from)
            || matches!(v, Expr::Var(_)) && self.declared_width(v) == Some(from)
    }

    /// `fadd`, `fsub`, `fmul` and `fdiv` (scalar): the operation over the
    /// two sources at the destination's width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - The float operator.
    pub(super) fn float_binary(&mut self, i: &Insn, op: Op) -> Option<()> {
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        let t = ty(bits)?;
        self.note_float(i, 1, t);
        self.note_float(i, 2, t);
        let (a, b) = (self.float_read(i, 1, bits)?, self.float_read(i, 2, bits)?);
        let v = super::mem::bear_width(fold(op, a, b, 64), t);
        self.note(dst, t);
        self.write(dst, bits, v);
        Some(())
    }

    /// `fmadd`, `fmsub`, `fnmadd` and `fnmsub` (scalar): the product of the
    /// first two sources plus the third, either side negated as the
    /// mnemonic says, at the destination's width.
    ///
    /// The machine rounds the fused result once. The tree has no fused
    /// operator, so the text spells the product and the sum, as the x86
    /// lifter spells `vfmadd`; the two differ only in the last bit of a
    /// result whose product the sum cancels.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `neg_addend` - The third source is negated (`fnmadd`, `fnmsub`).
    /// * `neg_product` - The product is negated (`fmsub`, `fnmadd`).
    pub(super) fn float_fused(
        &mut self,
        i: &Insn,
        neg_addend: bool,
        neg_product: bool,
    ) -> Option<()> {
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        let t = ty(bits)?;
        for k in 1..4 {
            self.note_float(i, k, t);
        }
        let n = self.float_read(i, 1, bits)?;
        let m = self.float_read(i, 2, bits)?;
        let a = self.float_read(i, 3, bits)?;
        let prod = fold(Op::FMul, n, m, 64);
        let v = match (neg_addend, neg_product) {
            (false, false) => fold(Op::FAdd, a, prod, 64),
            (false, true) => fold(Op::FSub, a, prod, 64),
            (true, false) => fold(Op::FSub, prod, a, 64),
            (true, true) => fold(Op::FSub, Expr::Un(UnOp::Neg, Box::new(a)), prod, 64),
        };
        let v = super::mem::bear_width(v, t);
        self.note(dst, t);
        self.write(dst, bits, v);
        Some(())
    }

    /// `fadd`, `fsub`, `fmul`, `fdiv`, `fmax` and `fmin` (vector): the
    /// instruction named as an intrinsic over the two registers, its
    /// arrangement in the name.
    ///
    /// A lane's arithmetic over a value the tree holds as one integer has
    /// no expression the C vocabulary names, so the packed operation stays
    /// whole, as the x86 lifter's own vector operations do.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `name` - The mnemonic.
    pub(super) fn float_array(&mut self, i: &Insn, name: &str) -> Option<()> {
        let w = i.word;
        let (a, b) = (self.reg_at(vreg(w, 5), 128), self.reg_at(vreg(w, 16), 128));
        let v = Expr::Call(
            packed_name(name, fp_lane(w), (w >> 30) & 1 == 1),
            vec![low(a, 64), low(b, 64)],
        );
        self.write(vreg(w, 0), 128, v);
        Some(())
    }

    /// `fsqrt` (vector): the instruction named as an intrinsic over the
    /// register, as [`Lift::float_array`] names its three-register kin.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn float_sqrt_array(&mut self, i: &Insn) -> Option<()> {
        let w = i.word;
        let x = low(self.reg_at(vreg(w, 5), 128), 64);
        let v = Expr::Call(
            packed_name("fsqrt", fp_lane(w), (w >> 30) & 1 == 1),
            vec![x],
        );
        self.write(vreg(w, 0), 128, v);
        Some(())
    }

    /// `fsqrt`, `fabs` and `fneg` (scalar): the one operation over the
    /// source at the destination's width.
    ///
    /// A source that is already a float is that operation. A source that
    /// is only a register's name is not a float expression, and a negation
    /// of the integer would be a different value: the sign bit is cleared
    /// or flipped instead, which is what the lane instruction does.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - The unary operator, [`UnOp::Sqrt`], [`UnOp::Fabs`] or
    ///   [`UnOp::Neg`].
    pub(super) fn float_unary(&mut self, i: &Insn, op: UnOp) -> Option<()> {
        if vector(i) {
            return match op {
                UnOp::Sqrt => self.float_sqrt_array(i),
                UnOp::Fabs | UnOp::Neg => {
                    let w = i.word;
                    let lane = fp_lane(w);
                    let sign = 1u64 << (lane - 1);
                    let signs = (1..u64::from(64 / lane))
                        .fold(sign, |acc, k| acc | sign << (k * u64::from(lane)));
                    let x = low(self.reg_at(vreg(w, 5), 128), 64);
                    let v = if matches!(op, UnOp::Neg) {
                        fold(Op::Xor, x, Expr::Const(signs), 64)
                    } else {
                        fold(Op::And, x, Expr::Const(!signs), 64)
                    };
                    self.write(vreg(w, 0), 128, v);
                    Some(())
                }
                _ => None,
            };
        }
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        let t = ty(bits)?;
        self.note_float(i, 1, t);
        let x = self.float_read(i, 1, bits)?;
        let v = match op {
            UnOp::Neg | UnOp::Fabs if !x.is_float() => {
                let sign = super::mem::lane_sign_bit(bits)?;
                if matches!(op, UnOp::Neg) {
                    fold(Op::Xor, x, Expr::Const(sign), 64)
                } else {
                    fold(Op::And, x, Expr::Const(!sign), 64)
                }
            }
            UnOp::Neg => unary(UnOp::Neg, x, 64),
            UnOp::Sqrt | UnOp::Fabs => Expr::Un(op, Box::new(x)),
            UnOp::Not
            | UnOp::Bswap
            | UnOp::Lzcnt
            | UnOp::Tzcnt
            | UnOp::Popcnt
            | UnOp::Bsf
            | UnOp::Bsr => return None,
        };
        let v = super::mem::bear_width(v, t);
        self.note(dst, t);
        self.write(dst, bits, v);
        Some(())
    }

    /// `fcmp` and `fcmpe`: a floating-point compare of the two values,
    /// which the conditions over float operands read, the second of which
    /// the `#0.0` form holds as zero. Each register is read at this
    /// width, so a narrower float contributes its encoding.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn float_compare(&mut self, i: &Insn) -> Option<()> {
        let Opnd::Reg { bits, .. } = i.operands[0] else {
            return None;
        };
        ty(bits)?;
        let a = self.float_read(i, 0, bits)?;
        let b = match i.operands[1] {
            Opnd::Reg { .. } => self.float_read(i, 1, bits)?,
            Opnd::Other => Expr::FConst(0, ty(bits)?),
            Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => return None,
        };
        self.ex.flags = Flags::Float(a, b, width8(bits));
        Some(())
    }

    /// `fccmp` and `fccmpe`: the flags of a float compare when the
    /// condition holds, else the immediate flags, read as [`Self::float_compare`].
    ///
    /// An `mrs` of `NZCV` before the next flag write leaves the whole word:
    /// the compare's N, Z, C and V when the condition holds, else the
    /// immediate in bits 31 to 28. Otherwise the flags are the truth of the
    /// next reader's condition, or unknown when the block has none.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `later` - The block's instructions after it, for the next reader.
    pub(super) fn float_compare_if(&mut self, i: &Insn, later: &[Insn]) -> Option<()> {
        let Opnd::Reg { bits, .. } = i.operands[0] else {
            return None;
        };
        ty(bits)?;
        let Opnd::Cond(c) = i.operands[3] else {
            return None;
        };
        let (a, b, nzcv) = (
            self.float_read(i, 0, bits)?,
            self.float_read(i, 1, bits)?,
            imm(i, 2)?,
        );
        let compared = Flags::Float(a, b, width8(bits));
        self.ex.flags = if flags::mrs_nzcv_before_write(later) {
            let held = flags::condition(&self.ex.flags, c);
            flags::conditional_nzcv(held, &compared, nzcv)
        } else {
            match next_reader(later) {
                Some(asked) => {
                    let then = flags::value(&compared, asked);
                    let otherwise = Expr::Const(u64::from(flags::holds(asked, nzcv)));
                    let held = ternary(flags::condition(&self.ex.flags, c), then, otherwise);
                    flags::answer(asked, held)
                }
                None => Flags::Unknown,
            }
        };
        Some(())
    }

    /// `fcsel`: the first source when the condition holds, else the second,
    /// at the destination's width. Each source is read at that width, so a
    /// narrower float contributes its encoding, and a bare register is
    /// declared at that width. A pair of bare registers is unchanged, and
    /// the write still cuts the high bits. A select that mixes a float with
    /// a value that is not one is cut here: one float arm would keep the
    /// other's high bits, and a 32-bit `fcsel` clears them.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn float_select(&mut self, i: &Insn) -> Option<()> {
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        let t = ty(bits)?;
        let Opnd::Cond(c) = i.operands[3] else {
            return None;
        };
        self.note_float(i, 1, t);
        self.note_float(i, 2, t);
        let (a, b) = (self.float_read(i, 1, bits)?, self.float_read(i, 2, bits)?);
        let mixed = bits < 64 && (!a.is_float() || !b.is_float());
        let v = ternary(flags::condition(&self.ex.flags, c), a, b);
        let v = if mixed { low(v, bits) } else { v };
        self.note(dst, t);
        self.write(dst, bits, v);
        Some(())
    }

    /// `scvtf` and `ucvtf`: an integer, signed or unsigned, divided by
    /// `2^fbits` into the destination's width.
    ///
    /// A signed source stays a sign extension, so a negative constant is
    /// not an unsigned bit pattern. The fixed-point form divides in a
    /// double and narrows afterwards: dividing a single would round the
    /// integer before the scale.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `signed` - Whether the integer is signed.
    pub(super) fn int_to_float(&mut self, i: &Insn, signed: bool) -> Option<()> {
        let (Opnd::Reg { reg: dst, bits: to }, Opnd::Reg { bits: from, .. }) =
            (i.operands[0], i.operands[1])
        else {
            return None;
        };
        let t = ty(to)?;
        let raw = self.source(i, 1, from)?;
        let n = if signed {
            Expr::Sext(Box::new(raw), width8(from))
        } else {
            low(raw, from)
        };
        let v = match i.operands.get(2) {
            Some(Opnd::Imm(fbits)) if *fbits != 0 && *fbits <= u64::from(from) => {
                let wide = Expr::Cast(Box::new(n), Ty::F64);
                let scale = small_pow2(*fbits, Ty::F64);
                let q = fold(Op::FDiv, wide, scale, 64);
                if t == Ty::F32 {
                    Expr::Cast(Box::new(q), Ty::F32)
                } else {
                    q
                }
            }
            Some(Opnd::None) | None => Expr::Cast(Box::new(n), t),
            _ => return None,
        };
        self.note(dst, t);
        self.write(dst, to, v);
        Some(())
    }

    /// `fcvtzs` and `fcvtzu`: a float to an integer toward zero, which
    /// saturates where the architecture says and C leaves undefined, as the
    /// intrinsic that names it; the fixed-point form scales by `2^fbits`
    /// first. The float is read at the instruction's width, so a narrower
    /// value is that encoding. `fcvt` is the conversion, and does not.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `signed` - Whether the integer is signed. The printed name
    ///   carries that and the integer width.
    pub(super) fn float_to_int(&mut self, i: &Insn, signed: bool) -> Option<()> {
        let Opnd::Reg { reg: dst, bits: to } = i.operands[0] else {
            return None;
        };
        let Opnd::Reg { bits: from, .. } = i.operands[1] else {
            return None;
        };
        ty(from)?;
        let x = self.float_read(i, 1, from)?;
        let x = match i.operands.get(2) {
            Some(Opnd::Imm(fbits)) if *fbits != 0 && *fbits <= 64 => {
                let t = ty(from)?;
                let scale = small_pow2(*fbits, t);
                fold(Op::FMul, x, scale, 64)
            }
            Some(Opnd::None) | None => x,
            _ => return None,
        };
        let round = u8::try_from(to)
            .ok()
            .and_then(|bits| RoundToInt::new(signed, bits))?;
        let args = vec![x, Expr::Const(u64::from(from))];
        self.write(dst, to, Expr::Call(round.name()?.to_owned(), args));
        Some(())
    }

    /// `fcvt`: a value between the single and double widths; the half forms
    /// have no type the C vocabulary names.
    ///
    /// The source is read at the width the instruction names. A value
    /// already at that width converts to the destination. A value at the
    /// other width contributes its encoding, and that encoding converts:
    /// converting the number the register's expression happens to hold
    /// would be a different float. A bare name declared narrower than this
    /// read, a sign bit flipped or cleared on a name, or an integer moved
    /// into the lane is not that float yet. The bits are named as this
    /// width and then converted. A cast of the integer would be `scvtf`.
    /// The source width is recorded first, so an in-place conversion
    /// declares the parameter as what was read, not as the result.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn float_convert(&mut self, i: &Insn) -> Option<()> {
        let (Opnd::Reg { reg: dst, bits: to }, Opnd::Reg { bits: from, .. }) =
            (i.operands[0], i.operands[1])
        else {
            return None;
        };
        let t = ty(to)?;
        let src = ty(from)?;
        self.note_float(i, 1, src);
        let x = self.float_read(i, 1, from)?;
        let v = if self.at_source_width(&x, from) {
            Expr::Cast(Box::new(x), t)
        } else {
            Expr::Cast(Box::new(lane_bits(x, src)), t)
        };
        self.note(dst, t);
        self.write(dst, to, v);
        Some(())
    }

    /// `and`, `orr`, `eor` and `bic` (vector, register and immediate
    /// forms): the operation over the whole registers.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation on the two values.
    pub(super) fn vector_logical(
        &mut self,
        i: &Insn,
        f: impl Fn(Expr, Expr) -> Expr,
    ) -> Option<()> {
        let w = i.word;
        let (a, b) = match i.operands[1] {
            Opnd::Other => (self.reg_at(vreg(w, 5), 128), self.reg_at(vreg(w, 16), 128)),
            Opnd::Imm(_) => {
                let imm8 = u64::from((((w >> 16) & 7) << 5) | ((w >> 5) & 0x1f));
                let imm = expand_imm((w >> 29) & 1, (w >> 12) & 0xf, imm8)?;
                if (w >> 30) & 1 == 1 && imm != 0 {
                    return None;
                }
                (self.reg_at(vreg(w, 0), 128), Expr::Const(imm))
            }
            Opnd::Reg { .. }
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => return None,
        };
        let v = f(a, b);
        self.write(vreg(w, 0), 128, v);
        Some(())
    }

    /// `dup`: one lane's value replicated through the low `span` bits of
    /// the register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn dup(&mut self, i: &Insn) -> Option<()> {
        let w = i.word;
        let imm5 = (w >> 16) & 0x1f;
        let shift = (0..4).find(|&s| imm5 >> s & 1 == 1)?;
        let lane = 8u16 << shift;
        let index = imm5 >> (shift + 1);
        let span = if (w >> 30) & 1 == 1 { 128 } else { 64 };
        let one = match i.operands[1] {
            Opnd::Reg { reg, bits } => low(self.reg_at(reg, bits), lane),
            _ => {
                let at = index * u32::from(lane);
                if at >= 64 {
                    return None;
                }
                let all = self.reg_at(vreg(w, 5), 128);
                low(
                    if at == 0 {
                        all
                    } else {
                        fold(Op::Shr, all, Expr::Const(u64::from(at)), 64)
                    },
                    lane,
                )
            }
        };
        let copies = u32::from(span / lane);
        let v = (1..copies).fold(one.clone(), |acc, k| {
            fold(
                Op::Or,
                acc,
                fold(
                    Op::Shl,
                    one.clone(),
                    Expr::Const(u64::from(k) * u64::from(lane)),
                    64,
                ),
                64,
            )
        });
        self.write(vreg(w, 0), 128, v);
        Some(())
    }
}
