//! Data processing for the arm64 lifter: moves, arithmetic and logic with
//! their flags, bitfields, shifts, multiplies and divides, conditional
//! selects and compares, and the scalar vector moves.
//!
//! Each handler computes every value before it writes anything, and
//! answers `None` for an operand it does not model, which leaves the
//! instruction unmodeled. A value is built from the registers' values as
//! the instruction reads them, folded at the operation's width, and left
//! uncut by a `w` write, which holds the register narrow instead: an add,
//! a subtract, a multiply or a logical operation needs no bit of a `w`
//! operand above its 32, so only an operation that does (a right shift, a
//! divide, a rotate, an extension) cuts or sign-extends its operand first,
//! and a compare's flags carry their width.

use super::super::expr::{Expr, Flags, Op, Ty, UnOp, fold, mask, sign_extend, ternary, unary};
use super::flags::{self, holds, next_reader};
use super::float::{packed_name, vreg};
use super::{Lift, low, low64, vector, width8};
use crate::emulate::a64::{FMOV_IMM, expand_imm, vfp_expand};
use crate::isa::a64::{self, Insn, Mnemonic, Opnd, Reg};
use crate::num::lo8;

/// How an add or subtract forms its second operand and its carry in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// `x + y`.
    Add,
    /// `x - y`.
    Sub,
    /// `x + y + C`.
    Adc,
    /// `x - y - !C`.
    Sbc,
}

/// How a move-wide instruction combines its shifted immediate with the
/// register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Wide {
    /// `movz`: the immediate alone.
    Zero,
    /// `movn`: its inverse.
    Not,
    /// `movk`: the immediate over the register's other bits.
    Keep,
}

/// A bitfield move: `ubfm`, `sbfm` or `bfm`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Field {
    /// The field, zero-extended.
    Unsigned,
    /// The field, sign-extended.
    Signed,
    /// The field into the destination, whose other bits stay.
    Insert,
}

/// A shift by a register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ShiftBy {
    /// `lslv`.
    Left,
    /// `lsrv`.
    Right,
    /// `asrv`.
    Arith,
    /// `rorv`.
    Rotate,
}

/// The mask of the low `n` bits, all of them from 64 up.
///
/// # Arguments
///
/// * `n` - How many.
fn ones(n: u32) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// The destination of a data-processing instruction: operand 0 as a
/// general register, the stack pointer or the zero register, with its
/// width.
///
/// # Arguments
///
/// * `i` - The instruction.
fn dest(i: &Insn) -> Option<(Reg, u16)> {
    match i.operands[0] {
        Opnd::Reg {
            reg: reg @ (Reg::X(_) | Reg::Sp | Reg::Zr),
            bits: bits @ (32 | 64),
        } => Some((reg, bits)),
        Opnd::Reg { .. }
        | Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    }
}

/// An immediate operand's value.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `k` - The operand's position.
pub(super) fn imm(i: &Insn, k: usize) -> Option<u64> {
    match i.operands.get(k).copied()? {
        Opnd::Imm(v) => Some(v),
        Opnd::None
        | Opnd::Reg { .. }
        | Opnd::Shifted { .. }
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    }
}

/// `ubfm`: the field `src<s:r>` at bit 0 when `s >= r`, else `src<s:0>` at
/// bit `width - r`; the rest zero up to the width the write cuts at.
///
/// # Arguments
///
/// * `src` - The source.
/// * `r` - `immr`, below `width`.
/// * `s` - `imms`, below `width`.
/// * `width` - The width in bits.
fn ubfm(src: Expr, r: u32, s: u32, width: u32) -> Expr {
    if s >= r {
        mask(
            fold(Op::Shr, src, Expr::Const(u64::from(r)), 64),
            ones(s - r + 1),
        )
    } else if s + 1 == r {
        fold(Op::Shl, src, Expr::Const(u64::from(width - r)), 64)
    } else {
        fold(
            Op::Shl,
            mask(src, ones(s + 1)),
            Expr::Const(u64::from(width - r)),
            64,
        )
    }
}

/// `sbfm`: as [`ubfm`], with the field's top bit copied into every bit
/// above it.
///
/// # Arguments
///
/// * `src` - The source.
/// * `r` - `immr`, below `width`.
/// * `s` - `imms`, below `width`.
/// * `width` - The width in bits.
fn sbfm(src: Expr, r: u32, s: u32, width: u32) -> Expr {
    let at = |n: u32| Expr::Const(u64::from(n));
    let bits = |n: u32| u8::try_from(n).unwrap_or(u8::MAX);
    if s + 1 == width && width == 64 {
        fold(Op::Sar, src, at(r), 64)
    } else if s + 1 == width {
        fold(Op::Sar, sign_extend(src, bits(width)), at(r), 64)
    } else if s >= r {
        sign_extend(fold(Op::Shr, src, at(r), 64), bits(s - r + 1))
    } else {
        fold(Op::Shl, sign_extend(src, bits(s + 1)), at(width - r), 64)
    }
}

/// `bfm`: as [`ubfm`], into the destination, whose other bits stay.
///
/// # Arguments
///
/// * `old` - The destination before.
/// * `src` - The source.
/// * `r` - `immr`, below `width`.
/// * `s` - `imms`, below `width`.
/// * `width` - The width in bits.
fn bfm(old: Expr, src: Expr, r: u32, s: u32, width: u32) -> Expr {
    let (field, pos) = if s >= r {
        (ones(s - r + 1), 0)
    } else {
        (ones(s + 1), width - r)
    };
    let kept = fold(Op::And, old, Expr::Const(!(field << pos)), 64);
    fold(Op::Or, kept, ubfm(src, r, s, width), 64)
}

impl Lift<'_, '_> {
    /// Lifts an instruction that does not move control.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `later` - The block's instructions after it, for a conditional
    ///   compare's reader.
    pub(super) fn step(&mut self, i: &Insn, later: &[Insn]) {
        let done = match i.op {
            a64::Op::Adr | a64::Op::Adrp => self.address_of(i),
            a64::Op::Nop | a64::Op::Bti | a64::Op::Pac => Some(()),
            a64::Op::Other => self.compute(i, later),
            a64::Op::Syscall
            | a64::Op::Sve
            | a64::Op::Sme
            | a64::Op::B
            | a64::Op::BCond(_)
            | a64::Op::Cbz
            | a64::Op::Cbnz
            | a64::Op::Tbz
            | a64::Op::Tbnz
            | a64::Op::Bl
            | a64::Op::Br
            | a64::Op::Blr
            | a64::Op::Ret
            | a64::Op::Eret
            | a64::Op::Trap
            | a64::Op::Invalid => None,
        };
        if done.is_none() {
            self.unmodeled(i);
        }
    }

    /// `adr` and `adrp`: the absolute address the decoder resolved.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, then address.
    fn address_of(&mut self, i: &Insn) -> Option<()> {
        let (Opnd::Reg { reg, bits }, Opnd::PcRel(at)) = (i.operands[0], i.operands[1]) else {
            return None;
        };
        self.write(reg, bits, Expr::Const(at));
        Some(())
    }

    /// Lifts an instruction by what it computes: the one table from base
    /// instruction to the handler that models it.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `later` - The block's instructions after it.
    ///
    /// # Returns
    ///
    /// `None` when the instruction or an operand is not modeled; nothing
    /// was written then.
    fn compute(&mut self, i: &Insn, later: &[Insn]) -> Option<()> {
        match i.mnemonic {
            Mnemonic::Movz => self.move_wide(i, Wide::Zero),
            Mnemonic::Movn => self.move_wide(i, Wide::Not),
            Mnemonic::Movk => self.move_wide(i, Wide::Keep),
            Mnemonic::Add if vector(i) => self.vector_arith(i, "add"),
            Mnemonic::Sub if vector(i) => self.vector_arith(i, "sub"),
            Mnemonic::Add => self.arith(i, Form::Add, false),
            Mnemonic::Adds => self.arith(i, Form::Add, true),
            Mnemonic::Sub => self.arith(i, Form::Sub, false),
            Mnemonic::Subs => self.arith(i, Form::Sub, true),
            Mnemonic::Adc => self.arith(i, Form::Adc, false),
            Mnemonic::Adcs => self.arith(i, Form::Adc, true),
            Mnemonic::Sbc => self.arith(i, Form::Sbc, false),
            Mnemonic::Sbcs => self.arith(i, Form::Sbc, true),
            Mnemonic::And if vector(i) => self.vector_logical(i, |a, b| fold(Op::And, a, b, 64)),
            Mnemonic::Bic if vector(i) => {
                self.vector_logical(i, |a, b| fold(Op::And, a, unary(UnOp::Not, b, 64), 64))
            }
            Mnemonic::Orr if vector(i) => self.vector_logical(i, |a, b| fold(Op::Or, a, b, 64)),
            Mnemonic::Eor if vector(i) => self.vector_logical(i, |a, b| fold(Op::Xor, a, b, 64)),
            Mnemonic::Mul => self.vector_arith(i, "mul"),
            Mnemonic::Neg => self.vector_unary(i, "neg"),
            Mnemonic::Abs => self.vector_unary(i, "abs"),
            Mnemonic::And => self.logical(i, Op::And, false, false),
            Mnemonic::Ands => self.logical(i, Op::And, false, true),
            Mnemonic::Orr => self.logical(i, Op::Or, false, false),
            Mnemonic::Orn => self.logical(i, Op::Or, true, false),
            Mnemonic::Eor => self.logical(i, Op::Xor, false, false),
            Mnemonic::Eon => self.logical(i, Op::Xor, true, false),
            Mnemonic::Bic => self.logical(i, Op::And, true, false),
            Mnemonic::Bics => self.logical(i, Op::And, true, true),
            Mnemonic::Ubfm => self.bitfield(i, Field::Unsigned),
            Mnemonic::Sbfm => self.bitfield(i, Field::Signed),
            Mnemonic::Bfm => self.bitfield(i, Field::Insert),
            Mnemonic::Extr => self.extract(i),
            Mnemonic::Lslv => self.shift_by(i, ShiftBy::Left),
            Mnemonic::Lsrv => self.shift_by(i, ShiftBy::Right),
            Mnemonic::Asrv => self.shift_by(i, ShiftBy::Arith),
            Mnemonic::Rorv => self.shift_by(i, ShiftBy::Rotate),
            Mnemonic::Madd => self.multiply(i, Op::Add, None),
            Mnemonic::Msub => self.multiply(i, Op::Sub, None),
            Mnemonic::Smaddl => self.multiply(i, Op::Add, Some(true)),
            Mnemonic::Smsubl => self.multiply(i, Op::Sub, Some(true)),
            Mnemonic::Umaddl => self.multiply(i, Op::Add, Some(false)),
            Mnemonic::Umsubl => self.multiply(i, Op::Sub, Some(false)),
            Mnemonic::Smulh => self.binary(i, |x, y, _| fold(Op::SMulHi(64), x, y, 64)),
            Mnemonic::Umulh => self.binary(i, |x, y, _| fold(Op::MulHi(64), x, y, 64)),
            Mnemonic::Udiv => self.binary(i, |x, y, w| fold(Op::Div, low(x, w), low(y, w), 64)),
            Mnemonic::Sdiv => self.binary(i, |x, y, w| {
                let signed = |e: Expr| {
                    if w >= 64 {
                        e
                    } else {
                        sign_extend(e, width8(w))
                    }
                };
                fold(Op::SDiv, signed(x), signed(y), 64)
            }),
            Mnemonic::Clz => self.unary_op(i, |x, w| Expr::Un(UnOp::Lzcnt, Box::new(cast(x, w)))),
            Mnemonic::Rev => self.unary_op(i, |x, w| Expr::Un(UnOp::Bswap, Box::new(cast(x, w)))),
            Mnemonic::Cls => self.unary_op(i, |x, w| call("__cls", x, w)),
            Mnemonic::Rbit => self.unary_op(i, |x, w| call("__rbit", x, w)),
            Mnemonic::Rev16 => self.unary_op(i, |x, w| call("__rev16", x, w)),
            Mnemonic::Rev32 => self.unary_op(i, |x, w| call("__rev32", x, w)),
            Mnemonic::Csel => self.select(i, |m| m),
            Mnemonic::Csinc => self.select(i, |m| fold(Op::Add, m, Expr::Const(1), 64)),
            Mnemonic::Csinv => self.select(i, |m| unary(UnOp::Not, m, 64)),
            Mnemonic::Csneg => self.select(i, |m| unary(UnOp::Neg, m, 64)),
            Mnemonic::Ccmp => self.compare_if(i, later, false),
            Mnemonic::Ccmn => self.compare_if(i, later, true),
            Mnemonic::Fmov => self.fmov(i),
            Mnemonic::Fadd if vector(i) => self.float_array(i, "fadd"),
            Mnemonic::Fsub if vector(i) => self.float_array(i, "fsub"),
            Mnemonic::Fmul if vector(i) => self.float_array(i, "fmul"),
            Mnemonic::Fdiv if vector(i) => self.float_array(i, "fdiv"),
            Mnemonic::Fmax if vector(i) => self.float_array(i, "fmax"),
            Mnemonic::Fmin if vector(i) => self.float_array(i, "fmin"),
            Mnemonic::Fadd => self.float_binary(i, Op::FAdd),
            Mnemonic::Fsub => self.float_binary(i, Op::FSub),
            Mnemonic::Fmul => self.float_binary(i, Op::FMul),
            Mnemonic::Fdiv => self.float_binary(i, Op::FDiv),
            Mnemonic::Fmax => self.float_binary(i, Op::FMax),
            Mnemonic::Fmin => self.float_binary(i, Op::FMin),
            Mnemonic::Fsqrt => self.float_unary(i, UnOp::Sqrt),
            Mnemonic::Fabs => self.float_unary(i, UnOp::Fabs),
            Mnemonic::Fneg => self.float_unary(i, UnOp::Neg),
            Mnemonic::Fcmp | Mnemonic::Fcmpe => self.float_compare(i),
            Mnemonic::Fccmp => self.float_compare_if(i, later),
            Mnemonic::Fcsel => self.float_select(i),
            Mnemonic::Scvtf => self.int_to_float(i, true),
            Mnemonic::Ucvtf => self.int_to_float(i, false),
            Mnemonic::Fcvtzs => self.float_to_int(i, "__fcvtzs"),
            Mnemonic::Fcvtzu => self.float_to_int(i, "__fcvtzu"),
            Mnemonic::Fcvt => self.float_convert(i),
            Mnemonic::Dup => self.dup(i),
            Mnemonic::Movi => self.movi(i, false),
            Mnemonic::Mvni => self.movi(i, true),
            Mnemonic::Ldr(width) => self.load(i, width),
            Mnemonic::Str(width) => self.store(i, width),
            Mnemonic::Ldp(width) => self.load_pair(i, width),
            Mnemonic::Stp => self.store_pair(i),
            Mnemonic::Ld1 => self.load_group(i),
            Mnemonic::St1 => self.store_group(i),
            Mnemonic::Prfm | Mnemonic::Barrier => Some(()),
            Mnemonic::Stxr(_)
            | Mnemonic::Stxp
            | Mnemonic::Atomic(..)
            | Mnemonic::Cas(_)
            | Mnemonic::Svc
            | Mnemonic::Mrs
            | Mnemonic::Msr
            | Mnemonic::Other => None,
        }
    }

    /// `movz`, `movn` and `movk`.
    ///
    /// The immediate and its shift are read from the word, as the machine
    /// reads them: the decoder folds the shift into the immediate, which
    /// loses it when the immediate is zero.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `form` - How the immediate combines with the register.
    fn move_wide(&mut self, i: &Insn, form: Wide) -> Option<()> {
        let (rd, bits) = dest(i)?;
        // SPEC: Arm ARM (DDI 0487) C6.2 MOVZ/MOVN/MOVK: imm16 is bits 5..20 and hw bits 21..22, shifting by hw * 16.
        let pos = ((i.word >> 21) & 3) * 16;
        if pos >= u32::from(bits) {
            return None;
        }
        let field = u64::from((i.word >> 5) & 0xffff) << pos;
        let v = match form {
            Wide::Zero => Expr::Const(field),
            Wide::Not => Expr::Const(!field),
            Wide::Keep => fold(
                Op::Or,
                fold(
                    Op::And,
                    self.reg_at(rd, bits),
                    Expr::Const(!(0xffff << pos)),
                    64,
                ),
                Expr::Const(field),
                64,
            ),
        };
        self.write(rd, bits, v);
        Some(())
    }

    /// `add`, `sub`, `adc` and `sbc`, and their flag-setting forms (`cmp`
    /// and `cmn` among them), over an immediate, a shifted register or an
    /// extended register.
    ///
    /// A `subs` leaves a [`Flags::Cmp`] and an `adds` a [`Flags::Add`] of
    /// its operands at its width; the forms with carry read the carry
    /// through whatever set the flags, and leave flags the lifter does not
    /// model.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `form` - How the second operand and the carry in are formed.
    /// * `sets` - Whether the instruction sets the flags.
    fn arith(&mut self, i: &Insn, form: Form, sets: bool) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let (x, y) = (self.source(i, 1, bits)?, self.source(i, 2, bits)?);
        let carry = || {
            (!matches!(self.ex.flags, Flags::Unknown))
                .then(|| flags::value(&self.ex.flags, a64::Cond::Hs))
        };
        let w = width8(bits);
        let v = match form {
            Form::Add => fold(Op::Add, x.clone(), y.clone(), w),
            Form::Sub => fold(Op::Sub, x.clone(), y.clone(), w),
            Form::Adc => fold(Op::Add, fold(Op::Add, x.clone(), y.clone(), w), carry()?, w),
            Form::Sbc => fold(
                Op::Add,
                fold(
                    Op::Sub,
                    fold(Op::Sub, x.clone(), y.clone(), w),
                    Expr::Const(1),
                    w,
                ),
                carry()?,
                w,
            ),
        };
        if sets {
            self.ex.flags = match form {
                Form::Add => Flags::Add(x, y, width8(bits)),
                Form::Sub => Flags::Cmp(x, y, width8(bits)),
                Form::Adc | Form::Sbc => Flags::Unknown,
            };
        }
        self.write(rd, bits, v);
        Some(())
    }

    /// `and`, `orr`, `eor`, `orn`, `eon`, `bic` and the flag-setting `ands`
    /// and `bics` (and `mov`, `mvn` and `tst`), over a bitmask immediate or a
    /// shifted register.
    ///
    /// A flag-setting form leaves a [`Flags::Test`] of its operands, carry
    /// and overflow clear.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - The operation on the two operands.
    /// * `invert` - Whether the second operand is inverted first.
    /// * `sets` - Whether it sets the flags.
    fn logical(&mut self, i: &Insn, op: Op, invert: bool, sets: bool) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let x = self.source(i, 1, bits)?;
        let y = self.source(i, 2, bits)?;
        let y = if invert { unary(UnOp::Not, y, 64) } else { y };
        let v = fold(op, x.clone(), y.clone(), width8(bits));
        if sets {
            self.ex.flags = Flags::Test(x, y, width8(bits));
        }
        self.write(rd, bits, v);
        Some(())
    }

    /// `ubfm`, `sbfm` and `bfm` and their aliases (`lsl`, `lsr`, `asr`,
    /// `ubfx`, `sbfiz`, `bfi`, `uxtb`, `sxtw`, ...).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, source, `immr`, `imms`.
    /// * `kind` - Which of the three.
    fn bitfield(&mut self, i: &Insn, kind: Field) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let src = self.source(i, 1, bits)?;
        let r = u32::try_from(imm(i, 2)?).ok()?;
        let s = u32::try_from(imm(i, 3)?).ok()?;
        if r >= width || s >= width {
            return None;
        }
        let v = match kind {
            Field::Unsigned => ubfm(src, r, s, width),
            Field::Signed => sbfm(src, r, s, width),
            Field::Insert => bfm(self.reg_at(rd, bits), src, r, s, width),
        };
        self.write(rd, bits, v);
        Some(())
    }

    /// `extr`, and `ror` by an immediate: the `width` bits of `Rn:Rm`
    /// starting at bit `lsb`.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, `Rn`, `Rm`, `lsb`.
    fn extract(&mut self, i: &Insn) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let width = u32::from(bits);
        let (hi, lo) = (self.source(i, 1, bits)?, self.source(i, 2, bits)?);
        let lsb = u32::try_from(imm(i, 3)?).ok()?;
        if lsb >= width {
            return None;
        }
        let at = |n: u32| Expr::Const(u64::from(n));
        let v = if lsb == 0 {
            lo
        } else if hi == lo {
            fold(Op::Ror(width8(bits)), low(lo, bits), at(lsb), 64)
        } else {
            fold(
                Op::Or,
                fold(Op::Shr, low(lo, bits), at(lsb), 64),
                fold(Op::Shl, hi, at(width - lsb), 64),
                64,
            )
        };
        self.write(rd, bits, v);
        Some(())
    }

    /// `lslv`, `lsrv`, `asrv` and `rorv`: a shift by a register, taken
    /// modulo the width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `kind` - Which shift.
    fn shift_by(&mut self, i: &Insn, kind: ShiftBy) -> Option<()> {
        self.binary(i, |x, y, w| {
            let by = fold(Op::And, y, Expr::Const(u64::from(w) - 1), 64);
            match kind {
                ShiftBy::Left => fold(Op::Shl, x, by, 64),
                ShiftBy::Right => fold(Op::Shr, low(x, w), by, 64),
                ShiftBy::Arith if w >= 64 => fold(Op::Sar, x, by, 64),
                ShiftBy::Arith => fold(Op::Sar, sign_extend(x, width8(w)), by, 64),
                ShiftBy::Rotate => fold(Op::Ror(width8(w)), low(x, w), by, 64),
            }
        })
    }

    /// An instruction of two sources: `f(x, y, width)` into the
    /// destination.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation.
    fn binary(&mut self, i: &Insn, f: impl Fn(Expr, Expr, u16) -> Expr) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let v = f(self.source(i, 1, bits)?, self.source(i, 2, bits)?, bits);
        self.write(rd, bits, v);
        Some(())
    }

    /// An instruction of one source: `f(x, width)` into the destination.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `f` - The operation.
    fn unary_op(&mut self, i: &Insn, f: impl Fn(Expr, u16) -> Expr) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let v = f(self.source(i, 1, bits)?, bits);
        self.write(rd, bits, v);
        Some(())
    }

    /// `madd` and `msub`, and the long forms `smaddl`, `smsubl`, `umaddl`
    /// and `umsubl` (and `mul`, `mneg`, `smull`, `umull`, ...): `Ra` plus or
    /// minus the product.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, `Rn`, `Rm`, `Ra`.
    /// * `op` - [`Op::Add`] or [`Op::Sub`].
    /// * `long` - For a long form, whether its `w` multiplicands are
    ///   signed; `None` for the plain forms.
    fn multiply(&mut self, i: &Insn, op: Op, long: Option<bool>) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let widen = |e: Expr| match long {
            Some(true) => sign_extend(e, 32),
            Some(false) => low(e, 32),
            None => e,
        };
        let n = widen(self.source(i, 1, 64)?);
        let m = widen(self.source(i, 2, 64)?);
        let a = self.source(i, 3, bits)?;
        let product = if long.is_some() { 64 } else { width8(bits) };
        let v = fold(op, a, fold(Op::Mul, n, m, product), width8(bits));
        self.write(rd, bits, v);
        Some(())
    }

    /// `csel`, `csinc`, `csinv` and `csneg` (and `cset`, `cinc`, `cneg`,
    /// ...): `Rn` when the condition holds, else `f(Rm)`.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: destination, `Rn`, `Rm`, condition.
    /// * `f` - What the second source becomes when the condition fails.
    fn select(&mut self, i: &Insn, f: impl Fn(Expr) -> Expr) -> Option<()> {
        let (rd, bits) = dest(i)?;
        let Opnd::Cond(c) = i.operands[3] else {
            return None;
        };
        let (a, b) = (self.source(i, 1, bits)?, f(self.source(i, 2, bits)?));
        let v = ternary(flags::condition(&self.ex.flags, c), a, b);
        self.write(rd, bits, v);
        Some(())
    }

    /// `ccmp` and `ccmn`: the flags of a compare when the condition holds,
    /// else the immediate flags.
    ///
    /// The flags are left as the truth of the condition the next reader
    /// in the block asks: the condition held and the compare satisfies the
    /// reader, or it failed and the immediate flags do. With no reader in
    /// the block, nothing can say which condition the flags answer, and
    /// they are left unknown.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rn`, `Rm` or a five-bit immediate, the
    ///   `nzcv` immediate, the condition.
    /// * `later` - The block's instructions after it.
    /// * `add` - Whether it compares by adding (`ccmn`).
    fn compare_if(&mut self, i: &Insn, later: &[Insn], add: bool) -> Option<()> {
        let Opnd::Reg { bits, .. } = i.operands[0] else {
            return None;
        };
        let Opnd::Cond(c) = i.operands[3] else {
            return None;
        };
        let (x, y, nzcv) = (
            self.source(i, 0, bits)?,
            self.source(i, 1, bits)?,
            imm(i, 2)?,
        );
        let compared = if add {
            Flags::Add(x, y, width8(bits))
        } else {
            Flags::Cmp(x, y, width8(bits))
        };
        self.ex.flags = match next_reader(later) {
            Some(asked) => {
                let then = flags::value(&compared, asked);
                let otherwise = Expr::Const(u64::from(holds(asked, nzcv)));
                let held = ternary(flags::condition(&self.ex.flags, c), then, otherwise);
                flags::answer(asked, held)
            }
            None => Flags::Unknown,
        };
        Some(())
    }

    /// `fmov` between registers, general and floating-point alike, of a
    /// scalar immediate, and of a vector immediate replicated through the
    /// lanes: the source's bits at its width, zero-extended into the
    /// destination. A float value moves as the float it is, its bits
    /// already fitting the width.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    fn fmov(&mut self, i: &Insn) -> Option<()> {
        if vector(i) {
            return self.fmov_imm_array(i);
        }
        let Opnd::Reg { reg: dst, bits } = i.operands[0] else {
            return None;
        };
        let v = match i.operands[1] {
            Opnd::Reg { reg, bits: from } => {
                let v = self.reg_at(reg, from);
                if v.is_float() {
                    v
                } else if from == 64 {
                    low64(v)
                } else {
                    low(v, from)
                }
            }
            Opnd::Other if matches!(dst, Reg::V(_)) && i.word & FMOV_IMM.0 == FMOV_IMM.1 => {
                Expr::Const(vfp_expand((i.word >> 13) & 0xff, bits)?)
            }
            Opnd::Other
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_) => return None,
        };
        self.write(dst, bits, v);
        Some(())
    }

    /// `movi` and `mvni`: an expanded immediate into a whole `v` register,
    /// replicated into the upper half for a 128-bit arrangement, which only
    /// a zero can be as one value.
    ///
    /// Every field is read from the word, as the machine reads it.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `invert` - Whether the immediate is inverted (`mvni`).
    fn movi(&mut self, i: &Insn, invert: bool) -> Option<()> {
        // SPEC: Arm ARM (DDI 0487) C7.2 MOVI/MVNI: Rd bits 0..4, d:e:f:g:h bits 5..9, cmode bits 12..15, a:b:c bits 16..18, op bit 29, Q bit 30.
        let w = i.word;
        let imm8 = u64::from((((w >> 16) & 7) << 5) | ((w >> 5) & 0x1f));
        let v = expand_imm((w >> 29) & 1, (w >> 12) & 0xf, imm8)?;
        let v = if invert { !v } else { v };
        if (w >> 30) & 1 == 1 && v != 0 {
            return None;
        }
        self.write(Reg::V(lo8(u64::from(w & 0x1f))), 128, Expr::Const(v));
        Some(())
    }

    /// `fmov` (vector, immediate): the expanded imm8 in every lane, one
    /// constant over the tree's low 64 bits.
    ///
    /// Every field is read from the word, as the machine reads it.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    // SPEC: Arm ARM (DDI 0487) C7.2 FMOV (vector, immediate): the
    // modified-immediate group with cmode 1111, its op and o2 bits naming
    // the lane width, as the machine's handler reads it.
    fn fmov_imm_array(&mut self, i: &Insn) -> Option<()> {
        let w = i.word;
        if (w >> 24) & 0x1f != 0b01111 || (w >> 12) & 0xf != 0b1111 {
            return None;
        }
        let lane = match ((w >> 29) & 1 == 1, (w >> 11) & 1 == 1) {
            (false, false) => 32,
            (false, true) => 16,
            (true, false) => 64,
            (true, true) => return None,
        };
        let imm8 = (((w >> 16) & 7) << 5) | ((w >> 5) & 0x1f);
        let one = vfp_expand(imm8, lane)?;
        let v = (1..u64::from(64 / lane)).fold(one, |acc, k| acc | one << (k * u64::from(lane)));
        self.write(Reg::V(lo8(u64::from(w & 0x1f))), 128, Expr::Const(v));
        Some(())
    }

    /// `add`, `sub` and `mul` (vector): the instruction named as an
    /// intrinsic over the two registers, as [`Lift::float_array`] names
    /// the packed float operations.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `name` - The mnemonic.
    // SPEC: Arm ARM (DDI 0487) C7.2 ADD/SUB/MUL (vector): size bits 22..23
    // name the lane width, as every three-register vector word encodes it.
    fn vector_arith(&mut self, i: &Insn, name: &str) -> Option<()> {
        let w = i.word;
        let (a, b) = (self.reg_at(vreg(w, 5), 128), self.reg_at(vreg(w, 16), 128));
        let lane = 8u16 << ((w >> 22) & 3);
        let v = Expr::Call(
            packed_name(name, lane, (w >> 30) & 1 == 1),
            vec![low(a, 64), low(b, 64)],
        );
        self.write(vreg(w, 0), 128, v);
        Some(())
    }

    /// `neg` and `abs` (vector): the instruction named as an intrinsic
    /// over the register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `name` - The mnemonic.
    // SPEC: Arm ARM (DDI 0487) C7.2 NEG/ABS (vector): the two-register
    // shape, its size and Q fields as every vector word encodes them.
    fn vector_unary(&mut self, i: &Insn, name: &str) -> Option<()> {
        let w = i.word;
        let x = low(self.reg_at(vreg(w, 5), 128), 64);
        let lane = 8u16 << ((w >> 22) & 3);
        let v = Expr::Call(packed_name(name, lane, (w >> 30) & 1 == 1), vec![x]);
        self.write(vreg(w, 0), 128, v);
        Some(())
    }
}

/// A value cut to an operation's width for an operation that depends on
/// its width, as the text reads it: `lzcnt((uint32_t)x)`.
///
/// # Arguments
///
/// * `e` - The value.
/// * `width` - The width, 32 or 64.
fn cast(e: Expr, width: u16) -> Expr {
    if width >= 64 {
        e
    } else {
        Expr::Cast(Box::new(e), Ty::U32)
    }
}

/// A bit operation the C vocabulary has no operator for, as the intrinsic
/// that names it, over the value cut to its width.
///
/// # Arguments
///
/// * `name` - The intrinsic.
/// * `e` - The value.
/// * `width` - The width, 32 or 64.
fn call(name: &str, e: Expr, width: u16) -> Expr {
    Expr::Call(name.to_owned(), vec![cast(e, width)])
}
