//! The MIR evaluator: a body's values computed under a starting state,
//! with the emulator's semantics.
//!
//! Each op computes at the width it holds, so a 32-bit difference wraps
//! at 32 bits whatever its operands' history. A float op computes in its
//! type's own arithmetic, rounding a single's result to a single as the
//! machine's scalar operation does. A select reads only the arm it
//! chooses. A value the state does not give (a register it does not
//! hold, a load that faults, a zero divisor, an [`Inst::Undef`]) is
//! unknown, and so is everything computed from it.

use super::super::expr::{Op, Ty, UnOp as EUn, sext as sext64};
use super::super::floats::{
    convert_float, float_arith, float_of, float_to_int, float_un, integer_to_float,
};
use super::super::helper::Helper;
use super::super::verify::low;
use super::{BinOp, Body, FOp, FUnOp, IPred, Inst, Lane, MTy, OvfOp, UnOp, Val, WideOp};
use crate::num::lo32;

/// What a body's inputs read: the block's starting state.
pub(in super::super) trait Inputs {
    /// Reads a register's starting value, as the lifter keys it.
    ///
    /// # Arguments
    ///
    /// * `k` - The register.
    ///
    /// # Returns
    ///
    /// The value, or `None` when the state does not hold it.
    fn reg(&self, k: super::super::expr::Key) -> Option<u64>;

    /// Returns the starting stack pointer.
    fn sp(&self) -> u64;

    /// Returns the address of the thread's TLS block.
    fn tls(&self) -> u64;

    /// Reads memory as it was where the block started, and records the
    /// range read.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - The bytes, 1 to 8; any other count records the range and
    ///   reads nothing.
    ///
    /// # Returns
    ///
    /// The bytes, little-endian, or `None` for a count past 8.
    fn load(&mut self, at: u64, n: u64) -> Option<u64>;
}

/// Evaluates one value of a body.
///
/// # Arguments
///
/// * `body` - The body.
/// * `v` - The value.
/// * `inputs` - The starting state.
///
/// # Returns
///
/// The value's bits, zero above its type's width, or `None` when it is
/// unknown.
pub(in super::super) fn eval(body: &Body, v: Val, inputs: &mut impl Inputs) -> Option<u64> {
    let mut memo = vec![None; body.nodes.len()];
    value(body, v, inputs, &mut memo)
}

/// [`eval`] with the values already computed.
///
/// # Arguments
///
/// * `body` - The body.
/// * `v` - The value.
/// * `inputs` - The starting state.
/// * `memo` - Each value computed so far, by index.
fn value(
    body: &Body,
    v: Val,
    inputs: &mut impl Inputs,
    memo: &mut Vec<Option<Option<u64>>>,
) -> Option<u64> {
    let i = usize::try_from(v.0).ok()?;
    if let Some(known) = memo.get(i).copied().flatten() {
        return known;
    }
    let node = body.nodes.get(i)?;
    let word = body.word;
    let out = match &node.inst {
        Inst::Const { bits, .. } | Inst::FConst { bits, .. } => Some(*bits),
        Inst::Reg(k) => inputs.reg(*k),
        Inst::Frame(off) => Some(inputs.sp().wrapping_add_signed(*off) & low(word)),
        Inst::Tls => Some(inputs.tls() & low(word)),
        Inst::Load { addr, ty } => {
            let at = value(body, *addr, inputs, memo)? & low(word);
            inputs.load(at, u64::from(ty.bits(word) / 8))
        }
        Inst::Bin { op, w, l, r } => {
            let a = value(body, *l, inputs, memo)?;
            let b = value(body, *r, inputs, memo)?;
            bin(*op, a, b, *w)
        }
        Inst::Ovf { op, w, l, r } => {
            let a = value(body, *l, inputs, memo)?;
            let b = value(body, *r, inputs, memo)?;
            Some(u64::from(overflows(*op, a, b, *w)))
        }
        Inst::Wide { op, w, l, r } => {
            let a = value(body, *l, inputs, memo)?;
            let b = value(body, *r, inputs, memo)?;
            Some(high(*op, a, b, *w))
        }
        Inst::Un { op, w, x } => {
            let a = value(body, *x, inputs, memo)?;
            Some(match op {
                UnOp::Neg => a.wrapping_neg() & low(*w),
                UnOp::Not => !a & low(*w),
                UnOp::Parity => u64::from((a & 0xff).count_ones().is_multiple_of(2)),
            })
        }
        Inst::Ext {
            signed,
            from,
            to,
            x,
        } => {
            let a = value(body, *x, inputs, memo)? & low(*from);
            Some(if *signed { sext64(a, *from) } else { a } & low(*to))
        }
        Inst::Trunc { to, x } => Some(value(body, *x, inputs, memo)? & low(*to)),
        Inst::Bitcast { to, x } => Some(value(body, *x, inputs, memo)? & low(to.bits(word))),
        Inst::Convert { to, signed, x } => {
            let a = value(body, *x, inputs, memo)?;
            convert(body.ty(*x), *to, *signed, a, word)
        }
        Inst::FBin { op, ty, l, r } => {
            let fb = ty.float()?;
            let a = float_of(value(body, *l, inputs, memo)?, fb);
            let b = float_of(value(body, *r, inputs, memo)?, fb);
            float_arith(float_op(*op), a, b, fb)
        }
        Inst::FUn { op, ty, x } => {
            let fb = ty.float()?;
            let a = value(body, *x, inputs, memo)?;
            match op {
                FUnOp::Neg => Some(a ^ (1u64 << (fb - 1))),
                FUnOp::Abs => float_un(EUn::Fabs, a, fb),
                FUnOp::Sqrt => float_un(EUn::Sqrt, a, fb),
            }
        }
        Inst::ICmp { pred, w, l, r } => {
            let a = value(body, *l, inputs, memo)?;
            let b = value(body, *r, inputs, memo)?;
            Some(u64::from(compare(*pred, a, b, *w)))
        }
        Inst::FCmp { pred, ty, l, r } => {
            let fb = ty.float()?;
            let a = float_of(value(body, *l, inputs, memo)?, fb);
            let b = float_of(value(body, *r, inputs, memo)?, fb);
            Some(u64::from(pred.holds(a, b)))
        }
        Inst::Select { c, t, f } => {
            let chosen = if value(body, *c, inputs, memo)? & 1 != 0 {
                t
            } else {
                f
            };
            value(body, *chosen, inputs, memo)
        }
        Inst::Splat { lane, x } => {
            let step = u32::from(*lane);
            let one = value(body, *x, inputs, memo)? & low(*lane);
            (step > 0).then(|| (0..64 / step).fold(0, |v, k| v | one << (k * step)))
        }
        Inst::Helper {
            h,
            bits,
            word,
            args,
        } => {
            let mut vals = Vec::with_capacity(args.len());
            for a in args {
                vals.push(value(body, *a, inputs, memo)?);
            }
            if let Helper::RoundToInt(round) = h {
                round.apply(*vals.first()?, *bits)
            } else {
                h.eval(&vals, *bits, *word)
            }
        }
        Inst::Undef(_) => None,
    };
    if let Some(slot) = memo.get_mut(i) {
        *slot = Some(out);
    }
    out
}

/// Computes an integer binary operation at width `w`.
///
/// # Arguments
///
/// * `op` - The operation.
/// * `a` - The left operand.
/// * `b` - The right operand.
/// * `w` - The width, 1 to 64.
///
/// # Returns
///
/// The result, or `None` for a zero divisor or a width out of range.
fn bin(op: BinOp, a: u64, b: u64, w: u8) -> Option<u64> {
    if !(1..=64).contains(&w) {
        return None;
    }
    let m = low(w);
    let (a, b) = (a & m, b & m);
    let signed = |v: u64| sext64(v, w).cast_signed();
    let count = lo32(b) & 63;
    let v = match op {
        BinOp::Add => a.wrapping_add(b),
        BinOp::Sub => a.wrapping_sub(b),
        BinOp::Mul => a.wrapping_mul(b),
        BinOp::UDiv => a.checked_div(b)?,
        BinOp::URem => a.checked_rem(b)?,
        BinOp::SDiv | BinOp::SRem => {
            let (sa, sb) = (signed(a), signed(b));
            if sb == 0 {
                return None;
            }
            if op == BinOp::SDiv {
                sa.wrapping_div(sb).cast_unsigned()
            } else {
                sa.wrapping_rem(sb).cast_unsigned()
            }
        }
        BinOp::And => a & b,
        BinOp::Or => a | b,
        BinOp::Xor => a ^ b,
        BinOp::Shl => a.wrapping_shl(count),
        BinOp::LShr => a.wrapping_shr(count),
        BinOp::AShr => signed(a).wrapping_shr(count).cast_unsigned(),
        BinOp::Rotl | BinOp::Rotr => {
            let n = lo32(b) % u32::from(w);
            let n = if op == BinOp::Rotl {
                n
            } else {
                (u32::from(w) - n) % u32::from(w)
            };
            if n == 0 {
                a
            } else {
                (a << n) | (a >> (u32::from(w) - n))
            }
        }
    };
    Some(v & m)
}

/// Tells whether an operation at width `w` overflows.
///
/// # Arguments
///
/// * `op` - The operation.
/// * `a` - The left operand.
/// * `b` - The right operand.
/// * `w` - The width, 1 to 64.
fn overflows(op: OvfOp, a: u64, b: u64, w: u8) -> bool {
    let m = low(w);
    let (a, b) = (a & m, b & m);
    let (sa, sb) = (
        i128::from(sext64(a, w).cast_signed()),
        i128::from(sext64(b, w).cast_signed()),
    );
    let half = 1i128 << (w.clamp(1, 64) - 1);
    let fits = |v: i128| v >= -half && v < half;
    match op {
        OvfOp::UAddO => u128::from(a) + u128::from(b) > u128::from(m),
        OvfOp::SAddO => !fits(sa + sb),
        OvfOp::USubO => a < b,
        OvfOp::SMulO => !fits(sa * sb),
    }
}

/// The high `w` bits of the `2w`-bit product of two `w`-bit operands.
///
/// # Arguments
///
/// * `op` - Whether the product is signed.
/// * `a` - The left operand.
/// * `b` - The right operand.
/// * `w` - The width, 1 to 64.
fn high(op: WideOp, a: u64, b: u64, w: u8) -> u64 {
    let m = low(w);
    let (a, b) = (a & m, b & m);
    let shift = u32::from(w.clamp(1, 64));
    let bits = match op {
        WideOp::UMulHi => (u128::from(a) * u128::from(b)) >> shift,
        WideOp::SMulHi => {
            let p = i128::from(sext64(a, w).cast_signed()) * i128::from(sext64(b, w).cast_signed());
            (p >> shift).cast_unsigned()
        }
    };
    u64::try_from(bits & u128::from(m)).unwrap_or(0)
}

/// Decides an integer compare of two `w`-bit values.
///
/// # Arguments
///
/// * `pred` - The predicate.
/// * `a` - The left operand.
/// * `b` - The right operand.
/// * `w` - The width.
fn compare(pred: IPred, a: u64, b: u64, w: u8) -> bool {
    let m = low(w);
    let (a, b) = (a & m, b & m);
    let (sa, sb) = (sext64(a, w).cast_signed(), sext64(b, w).cast_signed());
    match pred {
        IPred::Eq => a == b,
        IPred::Ne => a != b,
        IPred::Ult => a < b,
        IPred::Ule => a <= b,
        IPred::Ugt => a > b,
        IPred::Uge => a >= b,
        IPred::Slt => sa < sb,
        IPred::Sle => sa <= sb,
        IPred::Sgt => sa > sb,
        IPred::Sge => sa >= sb,
    }
}

/// The expression operator a float op computes as.
///
/// # Arguments
///
/// * `op` - The float op.
fn float_op(op: FOp) -> Op {
    match op {
        FOp::Add => Op::FAdd,
        FOp::Sub => Op::FSub,
        FOp::Mul => Op::FMul,
        FOp::Div => Op::FDiv,
        FOp::MinX86 => Op::FMin,
        FOp::MaxX86 => Op::FMax,
    }
}

/// Converts a value from one type to another.
///
/// # Arguments
///
/// * `from` - The operand's type.
/// * `to` - The result's type.
/// * `signed` - Whether the integer side is signed.
/// * `v` - The operand's bits.
/// * `word` - The machine word's width.
///
/// # Returns
///
/// The result's bits, or `None` for a pair of types no conversion joins.
fn convert(from: MTy, to: MTy, signed: bool, v: u64, word: u8) -> Option<u64> {
    let float_ty = |t: MTy| match t {
        MTy::F32 => Some(Ty::F32),
        MTy::F64 => Some(Ty::F64),
        MTy::I(_) | MTy::V(..) | MTy::Ptr => None,
    };
    match (from.float(), float_ty(to)) {
        (Some(fb), Some(t)) => Some(convert_float(v, Some(fb), t)),
        (None, Some(t)) => {
            let w = from.bits(word);
            let v = if signed { sext64(v, w) } else { v & low(w) };
            Some(integer_to_float(v, signed, t))
        }
        (Some(fb), None) => match to {
            MTy::I(bits) if bits <= 64 => Some(float_to_int(v, fb, bits)),
            MTy::I(_) | MTy::F32 | MTy::F64 | MTy::V(_, Lane::I(_)) | MTy::Ptr => None,
        },
        (None, None) => None,
    }
}
