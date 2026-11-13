//! Shift value and flag semantics shared across single- and double-precision
//! x86 shifts.

use super::*;

/// Returns the flags a shift leaves.
///
/// SPEC: Intel SDM Vol. 2, SAL/SAR/SHL/SHR and SHLD/SHRD: the count is
/// masked to five bits, six for a 64-bit operand, and a masked count of 0
/// affects no flag, so a constant count masking to 0 (`shl eax, 32`, `shld
/// eax, ebx, 32`) leaves the flags from before. A count below the width
/// sets CF to the last bit shifted out of the destination and ZF, SF and
/// PF from the result. At a count of 1, OF is the change of sign for SHL,
/// SHLD and SHRD, the original top bit for SHR and 0 for SAR; past 1 it is
/// undefined. [`Flags::Shift`] leaves OF undecided, and a one-bit shift
/// other than SAR whose OF may be read lifts to no flags (a one-bit SHL is
/// lifted as `x + x` before it gets here). At the width on a 16-bit SHLD or
/// SHRD, CF is still the last bit shifted out of the destination; at the
/// width or past it on SHL, SHR or SAR, ZF, SF and PF follow the lifted
/// result and CF and OF stay undecided. A count that is no constant may
/// mask to 0, so what it leaves is unknown.
///
/// # Arguments
///
/// * `mn` - `shl`, `sal`, `shr`, `sar`, `shld` or `shrd`.
/// * `l` - The shifted operand, as the shift reads it: the destination of
///   a `shld` or `shrd`.
/// * `count` - The count, as the shift reads it.
/// * `v` - The shifted value.
/// * `bits` - Operand width.
/// * `before` - The flags before the shift.
/// * `needed` - The flags read after the shift ([`RflagsBits`]), all of
///   them where they leave the block.
pub(super) fn shift_flags(
    mn: Mnemonic,
    l: Expr,
    count: &Expr,
    v: &Expr,
    bits: u8,
    before: &Flags,
    needed: u32,
) -> Flags {
    let count_mask = if bits == 64 { 0x3f } else { 0x1f };
    let Expr::Const(n) = count else {
        return Flags::Unknown;
    };
    match n & count_mask {
        0 => before.clone(),
        1 if needed & RflagsBits::OF != 0 && mn != Mnemonic::Sar => Flags::Unknown,
        n if n < u64::from(bits)
            || (n == u64::from(bits) && matches!(mn, Mnemonic::Shld | Mnemonic::Shrd)) =>
        {
            let pos = if matches!(mn, Mnemonic::Shr | Mnemonic::Sar | Mnemonic::Shrd) {
                n - 1
            } else {
                u64::from(bits) - n
            };
            let out = fold(Op::Shr, l, Expr::Const(pos), bits);
            Flags::Shift(v.clone(), bits, fold(Op::And, out, Expr::Const(1), bits))
        }
        _ => Flags::Result(v.clone(), bits),
    }
}

/// Builds the shifted value of a three-operand `shld` or `shrd`.
///
/// SPEC: Intel SDM Vol. 2, SHLD/SHRD: a 16-bit shift at a masked count of 16
/// moves the source into the destination, and a variable 16-bit shift funnels
/// through an unsigned 32-bit word so counts 0 through 16 all evaluate at C
/// width without undefined shifts.
///
/// # Arguments
///
/// * `mn` - `Shld` or `Shrd`.
/// * `dst` - Destination operand.
/// * `src` - Source operand.
/// * `cnt` - Masked shift count.
/// * `bits` - Operand width in bits (16, 32 or 64).
pub(super) fn double_shift_value(
    mn: Mnemonic,
    dst: &Expr,
    src: Expr,
    cnt: &Expr,
    bits: u8,
) -> Expr {
    let left = mn == Mnemonic::Shld;
    let (near, far) = if left {
        (Op::Shl, Op::Shr)
    } else {
        (Op::Shr, Op::Shl)
    };
    match (bits, cnt) {
        (_, Expr::Const(0)) => dst.clone(),
        (16, Expr::Const(16)) => mask(src, 0xffff),
        (_, &Expr::Const(n)) => fold(
            Op::Or,
            fold(near, dst.clone(), Expr::Const(n), bits),
            fold(
                far,
                src,
                Expr::Const(u64::from(bits).saturating_sub(n)),
                bits,
            ),
            bits,
        ),
        (16, _) => {
            let (hi, lo) = if left {
                (mask(dst.clone(), 0xffff), mask(src, 0xffff))
            } else {
                (mask(src, 0xffff), mask(dst.clone(), 0xffff))
            };
            let wide = fold(Op::Or, fold(Op::Shl, hi, Expr::Const(16), 32), lo, 32);
            let raw = if left {
                let sh = Expr::Cast(Box::new(fold(Op::Shl, wide, cnt.clone(), 32)), Ty::U32);
                fold(Op::Shr, sh, Expr::Const(16), 32)
            } else {
                fold(
                    Op::Shr,
                    Expr::Cast(Box::new(wide), Ty::U32),
                    cnt.clone(),
                    32,
                )
            };
            mask(raw, 0xffff)
        }
        _ => {
            let rest = fold(Op::Sub, Expr::Const(u64::from(bits) - 1), cnt.clone(), bits);
            fold(
                Op::Or,
                fold(near, dst.clone(), cnt.clone(), bits),
                fold(far, fold(far, src, Expr::Const(1), bits), rest, bits),
                bits,
            )
        }
    }
}

/// Returns the flags an instruction writes on every run: those a reader
/// after it never has from before it.
///
/// SPEC: Intel SDM Vol. 2, SAL/SAR/SHL/SHR, RCL/RCR/ROL/ROR and SHLD/SHRD:
/// a count that masks to 0 affects no flag. iced counts a shift or rotate
/// by `cl` as writing every flag it may ([`Instruction::rflags_modified`]),
/// and `cl` may hold 0, so such an instruction writes none for sure and
/// the flags before it stay live across it; an immediate count iced
/// already reads by its masked value.
///
/// # Arguments
///
/// * `instr` - The instruction.
pub(in crate::analysis::decompile) fn flags_always_written(instr: &Instruction) -> u32 {
    let count = instr.op_count().saturating_sub(1);
    let by_cl = matches!(
        instr.mnemonic(),
        Mnemonic::Shl
            | Mnemonic::Sal
            | Mnemonic::Shr
            | Mnemonic::Sar
            | Mnemonic::Rol
            | Mnemonic::Ror
            | Mnemonic::Rcl
            | Mnemonic::Rcr
            | Mnemonic::Shld
            | Mnemonic::Shrd
    ) && instr.op_kind(count) == OpKind::Register
        && instr.op_register(count) == Register::CL;
    if by_cl { 0 } else { instr.rflags_modified() }
}
