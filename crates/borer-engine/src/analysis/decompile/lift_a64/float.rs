//! Scalar floating-point and vector bitwise instructions for the arm64
//! lifter.
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
//! An instruction whose value the tree does not hold as a float, where
//! modeling it would read as an integer operation (`fneg` of a bare
//! register), stays an `/* asm */` comment rather than guess.

use super::super::expr::{Expr, Flags, Key, Op, Ty, UnOp, fold, sign_extend, ternary, unary};
use super::flags::{self, next_reader};
use super::step::imm;
use super::{Lift, low, width8};
use crate::emulate::a64::expand_imm;
use crate::isa::a64::{Insn, Opnd, Reg};
use crate::num::lo8;

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
fn vreg(w: u32, at: u32) -> Reg {
    Reg::V(lo8(u64::from((w >> at) & 0x1f)))
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
            Expr::Const(bits) => Expr::FConst(bits, t),
            other => other,
        })
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
        let (a, b) = (
            self.float_source(i, 1, bits)?,
            self.float_source(i, 2, bits)?,
        );
        let v = fold(op, a, b, 64);
        self.note(dst, t);
        self.write(dst, bits, v);
        Some(())
    }

    /// `fsqrt`, `fabs` and `fneg` (scalar): the one operation over the
    /// source at the destination's width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - The unary operator, [`UnOp::Sqrt`], [`UnOp::Fabs`] or
    ///   [`UnOp::Neg`].
    pub(super) fn float_unary(&mut self, i: &Insn, op: UnOp) -> Option<()> {
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        let t = ty(bits)?;
        let x = self.float_source(i, 1, bits)?;
        // INVARIANT: the tree reads `neg` and `fabs` of a value it does not
        // hold as a float as integer operations, so those stay asm; `sqrt`
        // keeps the x86 lifter's shape whatever the operand holds.
        if !matches!(op, UnOp::Sqrt) && !x.is_float() {
            return None;
        }
        let v = match op {
            UnOp::Neg => unary(UnOp::Neg, x, 64),
            _ => Expr::Un(op, Box::new(x)),
        };
        self.note(dst, t);
        self.write(dst, bits, v);
        Some(())
    }

    /// `fcmp` and `fcmpe`: a floating-point compare of the two values,
    /// which the conditions over float operands read, the second of which
    /// the `#0.0` form holds as zero.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn float_compare(&mut self, i: &Insn) -> Option<()> {
        let Opnd::Reg { bits, .. } = i.operands[0] else {
            return None;
        };
        ty(bits)?;
        let a = self.float_source(i, 0, bits)?;
        let b = match i.operands[1] {
            Opnd::Reg { .. } => self.float_source(i, 1, bits)?,
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
            self.float_source(i, 0, bits)?,
            self.float_source(i, 1, bits)?,
            imm(i, 2)?,
        );
        let compared = Flags::Float(a, b, width8(bits));
        self.ex.flags = match next_reader(later) {
            Some(asked) => {
                let then = flags::value(&compared, asked);
                let otherwise = Expr::Const(u64::from(flags::holds(asked, nzcv)));
                let held = ternary(flags::condition(&self.ex.flags, c), then, otherwise);
                flags::answer(asked, held)
            }
            None => Flags::Unknown,
        };
        Some(())
    }

    /// `fcsel`: the first source when the condition holds, else the second,
    /// at the destination's width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    pub(super) fn float_select(&mut self, i: &Insn) -> Option<()> {
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        ty(bits)?;
        let Opnd::Cond(c) = i.operands[3] else {
            return None;
        };
        let (a, b) = (
            self.float_source(i, 1, bits)?,
            self.float_source(i, 2, bits)?,
        );
        let v = ternary(flags::condition(&self.ex.flags, c), a, b);
        self.note(dst, ty(bits)?);
        self.write(dst, bits, v);
        Some(())
    }

    /// `scvtf` and `ucvtf`: an integer, signed or unsigned, divided by
    /// `2^fbits` into the destination's width.
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
            sign_extend(raw, width8(from))
        } else {
            low(raw, from)
        };
        let v = Expr::Cast(Box::new(n), t);
        let v = match i.operands.get(2) {
            // SPEC: Arm ARM (DDI 0487) C7.2 SCVTF/UCVTF (scalar,
            // fixed-point): the integer scales by 2^-fbits.
            Some(Opnd::Imm(fbits)) if *fbits != 0 && *fbits <= u64::from(from) => {
                let scale = small_pow2(*fbits, t);
                fold(Op::FDiv, v, scale, 64)
            }
            Some(Opnd::None) | None => v,
            _ => return None,
        };
        self.note(dst, t);
        self.write(dst, to, v);
        Some(())
    }

    /// `fcvtzs` and `fcvtzu`: a float to an integer toward zero, which
    /// saturates where the architecture says and C leaves undefined, as the
    /// intrinsic that names it; the fixed-point form scales by `2^fbits`
    /// first.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `name` - The intrinsic, `__fcvtzs` or `__fcvtzu`.
    pub(super) fn float_to_int(&mut self, i: &Insn, name: &str) -> Option<()> {
        let Opnd::Reg { reg: dst, bits: to } = i.operands[0] else {
            return None;
        };
        let Opnd::Reg { bits: from, .. } = i.operands[1] else {
            return None;
        };
        ty(from)?;
        let x = self.float_source(i, 1, from)?;
        let x = match i.operands.get(2) {
            Some(Opnd::Imm(fbits)) if *fbits != 0 && *fbits <= 64 => {
                let t = ty(from)?;
                let scale = small_pow2(*fbits, t);
                fold(Op::FMul, x, scale, 64)
            }
            Some(Opnd::None) | None => x,
            _ => return None,
        };
        let v = Expr::Call(name.to_owned(), vec![x]);
        self.write(dst, to, v);
        Some(())
    }

    /// `fcvt`: a value between the single and double widths; the half forms
    /// have no type the C vocabulary names.
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
        ty(from)?;
        let x = self.float_source(i, 1, from)?;
        let v = Expr::Cast(Box::new(x), t);
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
                // SPEC: Arm ARM (DDI 0487) C7.2 ORR/BIC (vector, immediate):
                // imm8 bits 5..9, the same cmode shape movi takes, with op
                // bit 29 naming the operation in place of the move. The
                // pattern fills both halves of a 128-bit arrangement, which
                // only a zero can be as one value, as `movi` reads it.
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
        // SPEC: Arm ARM (DDI 0487) C7.2 DUP: imm5 bits 16..20, its lowest
        // set bit naming the element size and the bits above it the index.
        let imm5 = (w >> 16) & 0x1f;
        let shift = (0..4).find(|&s| imm5 >> s & 1 == 1)?;
        let lane = 8u16 << shift;
        let index = imm5 >> (shift + 1);
        let span = if (w >> 30) & 1 == 1 { 128 } else { 64 };
        let one = match i.operands[1] {
            Opnd::Reg { reg, bits } => low(self.reg_at(reg, bits), lane),
            _ => {
                let at = index * u32::from(lane);
                // INVARIANT: the tree holds a `v` register's low 64 bits, so
                // a lane at or above them — a `d` lane's second element, an
                // `s` lane's third — is one shift past what it can name.
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
