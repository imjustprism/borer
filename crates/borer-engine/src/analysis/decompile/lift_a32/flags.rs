//! The flags an ARM32 block sets and reads, in the vocabulary the arm64
//! lifter reads them in ([`super::super::lift_a64::flags::condition`]).
//!
//! A `cmp` (and `subs`) leaves a [`Flags::Cmp`], a `cmn` (and `adds`) a
//! [`Flags::Add`], with A32's carry the arm64 one. A logical or shifting
//! instruction sets N and Z from its result, C from the shifter (or leaves
//! it) and leaves V: when the next reader in the block asks only of N and
//! Z, that is [`Flags::Result`] of the value, and otherwise the whole word
//! in [`Flags::Carry`], C and V taken from the flags before it when the
//! instruction leaves them. An add or subtract with carry leaves the word
//! too, its carry and overflow computed.

use super::super::expr::{Cc, Cond as XCond, Expr, Flags, Op, fold, ternary};
use crate::isa::a32::{Cond, DpKind, Flow, Insn, Op as AOp, Operand, PC, Reg, Shift};
use crate::isa::x86::ConditionCode;

/// What a conditional branch tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Test {
    /// A `b<cond>`: a condition on the flags.
    Flags(Cond),
    /// `cbz` or `cbnz`: a register against zero.
    Zero {
        /// The register.
        reg: Reg,
        /// Taken when the register is zero (`cbz`).
        zero: bool,
    },
}

/// Reads what a conditional branch tests.
///
/// # Arguments
///
/// * `i` - The branch.
pub(super) fn test(i: &Insn) -> Option<Test> {
    if let AOp::Cbz { rn, nonzero, .. } = i.op {
        return Some(Test::Zero {
            reg: rn,
            zero: !nonzero,
        });
    }
    matches!(i.op, AOp::B { .. }).then_some(Test::Flags(i.cond))
}

/// The condition a register equals (or differs from) zero.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `zero` - Taken when it is zero.
pub(super) fn zero_test(v: Expr, zero: bool) -> XCond {
    XCond {
        cc: Cc(if zero {
            ConditionCode::e
        } else {
            ConditionCode::ne
        }),
        flags: Flags::Cmp(v, Expr::Const(0), 32),
    }
}

/// The condition an instruction reads the flags for: its own when it runs
/// under one or is a conditional branch, `hs` for the carry an add or
/// subtract with carry or a rotate through the carry reads.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(in crate::analysis::decompile) fn reads(i: &Insn) -> Option<Cond> {
    if !matches!(i.cond, Cond::Al | Cond::Nv) {
        return Some(i.cond);
    }
    let carry = if let AOp::Dp { kind, src, .. } = i.op {
        matches!(kind, DpKind::Adc | DpKind::Sbc | DpKind::Rsc)
            || matches!(
                src,
                Operand::Reg {
                    shift: Shift::Rrx,
                    ..
                }
            )
    } else {
        false
    };
    carry.then_some(Cond::Hs)
}

/// Tells whether an instruction sets the flags, a call among them, after
/// which they hold nothing the caller set.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(in crate::analysis::decompile) fn sets_flags(i: &Insn) -> bool {
    i.flow() == Flow::Call || i.sets || matches!(i.op, AOp::Msr { .. } | AOp::Vmrs { rt: PC })
}

/// The conditions every reader of the flags asks before anything sets
/// them again, and whether something does before the block ends.
///
/// # Arguments
///
/// * `later` - The block's instructions after the one setting them.
pub(super) fn readers(later: &[Insn]) -> (Vec<Cond>, bool) {
    let mut asked = Vec::new();
    for i in later {
        if let Some(c) = reads(i) {
            asked.push(c);
        }
        if sets_flags(i) && !i.predicated() {
            return (asked, true);
        }
    }
    (asked, false)
}

/// The condition the next reader of the flags asks, before anything sets
/// them again.
///
/// # Arguments
///
/// * `later` - The block's instructions after the one setting them.
pub(super) fn next_reader(later: &[Insn]) -> Option<Cond> {
    for i in later {
        if let Some(c) = reads(i) {
            return Some(c);
        }
        if sets_flags(i) {
            return None;
        }
    }
    None
}

/// Which flags each instruction of a block leaves for a later reader:
/// every bit where one reads them before they are set again, in the block
/// or, when `flags_out`, after it.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
/// * `flags_out` - Some successor reads the flags the block leaves.
pub(super) fn live_after(instrs: &[Insn], flags_out: bool) -> Vec<u32> {
    let mut live = if flags_out { u32::MAX } else { 0 };
    let mut after = vec![0; instrs.len()];
    for (slot, i) in after.iter_mut().zip(instrs).rev() {
        *slot = live;
        if sets_flags(i) && !i.predicated() {
            live = 0;
        }
        if reads(i).is_some()
            || (i.sets && !matches!(i.op, AOp::Dp { kind, .. } if kind.arithmetic()))
        {
            live = u32::MAX;
        }
    }
    after
}

/// Tells whether a block reads the flags before it sets them.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
pub(in crate::analysis::decompile) fn reads_inherited_flags(instrs: &[Insn]) -> bool {
    for i in instrs {
        if reads(i).is_some() {
            return true;
        }
        if sets_flags(i) {
            return false;
        }
    }
    false
}

/// A flag as 1 or 0: the truth of a condition on the flags.
///
/// # Arguments
///
/// * `flags` - What set them.
/// * `c` - The condition.
fn bit(flags: &Flags, c: Cond) -> Expr {
    super::super::lift_a64::flags::value(flags, c)
}

/// N, Z, C and V as bits 31 to 28 of one word.
///
/// # Arguments
///
/// * `n` - N, 1 or 0.
/// * `z` - Z, 1 or 0.
/// * `c` - C, 1 or 0.
/// * `v` - V, 1 or 0.
fn pack(n: Expr, z: Expr, c: Expr, v: Expr) -> Flags {
    let place = |b: Expr, at: u64| fold(Op::Shl, b, Expr::Const(at), 32);
    Flags::Carry(fold(
        Op::Or,
        fold(Op::Or, place(n, 31), place(z, 30), 32),
        fold(Op::Or, place(c, 29), place(v, 28), 32),
        32,
    ))
}

/// N and Z of a 32-bit result, as 1 or 0.
///
/// # Arguments
///
/// * `r` - The result.
fn nz(r: &Expr) -> (Expr, Expr) {
    let n = fold(
        Op::And,
        fold(Op::Shr, r.clone(), Expr::Const(31), 32),
        Expr::Const(1),
        32,
    );
    let z = ternary(zero_test(r.clone(), true), Expr::Const(1), Expr::Const(0));
    (n, z)
}

/// The flags a logical or shifting instruction leaves.
///
/// # Arguments
///
/// * `r` - The result.
/// * `carry` - The shifter's carry, 1 or 0; `None` leaves the carry.
/// * `old` - The flags before it.
/// * `asked` - The condition the next reader in the block asks.
pub(super) fn logical(r: Expr, carry: Option<Expr>, old: &Flags, asked: Option<Cond>) -> Flags {
    if matches!(asked, Some(Cond::Eq | Cond::Ne | Cond::Mi | Cond::Pl)) {
        return Flags::Result(r, 32);
    }
    let c = match carry {
        Some(c) => c,
        None if matches!(old, Flags::Unknown) => return Flags::Unknown,
        None => bit(old, Cond::Hs),
    };
    if matches!(old, Flags::Unknown)
        && !matches!(asked, Some(Cond::Hs | Cond::Lo | Cond::Hi | Cond::Ls))
    {
        return Flags::Unknown;
    }
    let v = if matches!(old, Flags::Unknown) {
        Expr::Const(0)
    } else {
        bit(old, Cond::Vs)
    };
    let (n, z) = nz(&r);
    pack(n, z, c, v)
}

/// Returns the 64-bit compare a `sbcs` after a compare of low words leaves.
///
/// A `sbcs` that subtracts the high words of a pair whose low words a
/// `subs` or `cmp` just compared leaves, for a reader that asks `lt`,
/// `ge`, `lo` or `hs`, the compare of the two pairs.
///
/// # Arguments
///
/// * `old` - The flags before it, the low words' compare.
/// * `hi_a` - The first pair's high word.
/// * `hi_b` - The second pair's.
/// * `asked` - The conditions the readers ask before the flags are set
///   again, all of which must ask the one compare.
///
/// # Returns
///
/// The answer to those conditions, or `None` when the low words were not
/// compared or a reader asks of the equality, which a `sbcs` does not
/// leave for the pair.
pub(super) fn wide_compare(old: &Flags, hi_a: &Expr, hi_b: &Expr, asked: &[Cond]) -> Option<Flags> {
    let Flags::Cmp(lo_a, lo_b, 32) = old else {
        return None;
    };
    let (below, cc) = match *asked.first()? {
        Cond::Lt | Cond::Ge => (ConditionCode::l, Cond::Lt),
        Cond::Lo | Cond::Hs => (ConditionCode::b, Cond::Lo),
        Cond::Eq
        | Cond::Ne
        | Cond::Mi
        | Cond::Pl
        | Cond::Vs
        | Cond::Vc
        | Cond::Hi
        | Cond::Ls
        | Cond::Gt
        | Cond::Le
        | Cond::Al
        | Cond::Nv => return None,
    };
    let same = |c: &Cond| match cc {
        Cond::Lt => matches!(c, Cond::Lt | Cond::Ge),
        _ => matches!(c, Cond::Lo | Cond::Hs),
    };
    if !asked.iter().all(same) {
        return None;
    }
    let test = |cc, a: &Expr, b: &Expr| {
        Expr::Cond(Box::new(XCond {
            cc: Cc(cc),
            flags: Flags::Cmp(a.clone(), b.clone(), 32),
        }))
    };
    let high = test(below, hi_a, hi_b);
    let tie = fold(
        Op::And,
        test(ConditionCode::e, hi_a, hi_b),
        test(ConditionCode::b, lo_a, lo_b),
        32,
    );
    Some(super::super::lift_a64::flags::answer(
        cc,
        fold(Op::Or, high, tie, 32),
    ))
}

/// The flags an add or subtract with carry leaves: `x + y + c`, with
/// `y` already inverted for a subtraction.
///
/// # Arguments
///
/// * `x` - The first operand.
/// * `y` - The second, as added.
/// * `cin` - The carry in, 1 or 0.
/// * `r` - The 32-bit result.
pub(super) fn with_carry(x: &Expr, y: &Expr, cin: &Expr, r: &Expr) -> Flags {
    let sum = fold(Op::Add, x.clone(), y.clone(), 32);
    let all_ones = XCond {
        cc: Cc(ConditionCode::e),
        flags: Flags::Cmp(sum, Expr::Const(0xffff_ffff), 32),
    };
    let carry = fold(
        Op::Or,
        fold(Op::UAddO(32), x.clone(), y.clone(), 32),
        fold(
            Op::And,
            ternary(all_ones, Expr::Const(1), Expr::Const(0)),
            cin.clone(),
            32,
        ),
        32,
    );
    let signs = fold(
        Op::And,
        fold(
            Op::Xor,
            fold(Op::Xor, x.clone(), y.clone(), 32),
            Expr::Const(0xffff_ffff),
            32,
        ),
        fold(Op::Xor, x.clone(), r.clone(), 32),
        32,
    );
    let v = fold(
        Op::And,
        fold(Op::Shr, signs, Expr::Const(31), 32),
        Expr::Const(1),
        32,
    );
    let (n, z) = nz(r);
    pack(n, z, carry, v)
}
