//! An A32 or T32 shift by a register, printed as the one operation it is.
//!
//! The lifter writes `lsl`, `lsr` and `asr` by a register as the Arm ARM
//! computes them: the amount is the register's low byte, a logical shift by
//! 32 or more leaves 0 and an arithmetic one the sign in every bit, so the
//! value is a select on `amount < 32` (`lift_a32::step`). The lift check
//! runs that select against the emulator. C's `?:` would print it as a
//! branch on every shift, and C's bare `<<` is undefined from 32 on, so the
//! text prints the select as the helper call it equals ([`Helper::Lsl32`],
//! [`Helper::Lsr32`], [`Helper::Asr32`]), which [`super::super::helper::declare`]
//! defines exactly as the Arm ARM computes it.

use super::super::expr::{Cond, Expr, Flags, Op, fold, known_bits, mask_bits, sext};
use super::super::helper::Helper;
use crate::isa::Isa;
use crate::isa::x86::ConditionCode;
use crate::program::Program;

/// Returns the helper call a register shift's select prints as.
///
/// The select is `by < 32 ? x << by : 0`, `by < 32 ? x >> by : 0`, or
/// `by < 32 ? s >> by : s >> 31` with `s` the sign extension of a word.
/// Meaning is kept because each call is printed only on evidence that it
/// has the select's value for every input: the image is A32, where every
/// value is a 32-bit word (the lift check holds the lifter to that); the
/// test is the unsigned `by < 32` of a 32-bit compare; `by` has no known
/// bit above its low byte, so the helper's own cut to the low byte keeps
/// it; and the true arm shifts by that same `by` while the false arm is
/// the shift's own fill. A mask of `by` to its low byte is left out of the
/// call, which cuts to the low byte itself. Any other select, or one in an
/// image of another instruction set, gets `None` and prints as `?:`.
///
/// # Arguments
///
/// * `c` - The select's condition.
/// * `a` - Value when true.
/// * `b` - Value when false.
/// * `program` - The image, whose instruction set the rule requires.
///
/// # Returns
///
/// The call, or `None` when the select is not a register shift's.
pub(super) fn call(c: &Cond, a: &Expr, b: &Expr, program: &Program) -> Option<Expr> {
    let Flags::Cmp(by, Expr::Const(32), 32) = &c.flags else {
        return None;
    };
    if c.cc.0 != ConditionCode::b
        || program.arch.isa() != Some(Isa::A32)
        || known_bits(by) & !0xff != 0
    {
        return None;
    }
    let (h, x) = match (a, b) {
        (Expr::Bin(Op::Shl, x, n), Expr::Const(0)) if **n == *by => (Helper::Lsl32, (**x).clone()),
        (Expr::Bin(Op::Shr, x, n), Expr::Const(0)) if **n == *by => (Helper::Lsr32, (**x).clone()),
        (Expr::Bin(Op::Sar, s, n), fill)
            if **n == *by && *fill == fold(Op::Sar, (**s).clone(), Expr::Const(31), 32) =>
        {
            (Helper::Asr32, signed_word(s)?)
        }
        _ => return None,
    };
    let amount = match by {
        Expr::Bin(Op::And, r, m) if **m == Expr::Const(0xff) => (**r).clone(),
        other => other.clone(),
    };
    Some(Expr::Helper(h, vec![x, amount]))
}

/// The word whose sign extension an arithmetic shift reads.
///
/// # Arguments
///
/// * `s` - The shifted value.
///
/// # Returns
///
/// The word, or `None` when `s` is not the sign extension of a 32-bit
/// word, where the helper's signed read of the low word would not be its
/// value.
fn signed_word(s: &Expr) -> Option<Expr> {
    if let Expr::Sext(x, 32) = s {
        return Some((**x).clone());
    }
    let Expr::Const(c) = s else {
        return None;
    };
    (sext(c & mask_bits(32), 32) == *c).then(|| Expr::Const(c & mask_bits(32)))
}

#[cfg(test)]
mod tests {
    use super::call;
    use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, Op, fold};
    use crate::analysis::decompile::helper::Helper;
    use crate::emulate::Stop;
    use crate::emulate::a32::Machine;
    use crate::isa::a32::{Mode, Modes};
    use crate::isa::x86::{ConditionCode, Register};
    use crate::program::{Arch, Program, Section};

    /// Where the A32 routines run.
    const AT: u64 = 0x1_0000;

    /// An A32 image of one instruction and its return.
    ///
    /// # Arguments
    ///
    /// * `word` - The instruction.
    fn a32(word: u32) -> Program {
        // ASM: bx lr
        let bytes: Vec<u8> = [word, 0xe12f_ff1e]
            .iter()
            .flat_map(|w| w.to_le_bytes())
            .collect();
        let text = Section::mapped(".text", AT, 0, 8, false, true);
        let mut p = Program::raw(bytes, Arch::Arm, 0, Some(AT), vec![text]);
        p.modes = Modes::from_marks(vec![(AT, Mode::Arm)]);
        p
    }

    /// The register-shift select of `a` and `b` on `by < 32`.
    ///
    /// # Arguments
    ///
    /// * `by` - The amount.
    /// * `cc` - The test's condition code, `b` for the lifter's.
    fn small(by: &Expr, cc: ConditionCode) -> Cond {
        Cond {
            cc: Cc(cc),
            flags: Flags::Cmp(by.clone(), Expr::Const(32), 32),
        }
    }

    /// Each helper is the machine's shift by a register at every edge amount.
    ///
    /// The amounts lie on either side of 32 and of the low byte, the words
    /// are negative and positive: the amount is the low byte, a logical
    /// shift from 32 on is 0 and an arithmetic one the sign.
    ///
    /// # Panics
    ///
    /// When a helper's value is not the machine's.
    #[test]
    fn each_shift_helper_is_the_machine_shift_at_every_edge_amount() {
        let shifts = [
            // ASM: lsl r0, r1, r2
            (0xe1a0_0211, Helper::Lsl32),
            // ASM: lsr r0, r1, r2
            (0xe1a0_0231, Helper::Lsr32),
            // ASM: asr r0, r1, r2
            (0xe1a0_0251, Helper::Asr32),
        ];
        let amounts = [0, 1, 31, 32, 33, 255, 256, 257, 0x121, 0xffff_ffff];
        for (word, h) in shifts {
            let p = a32(word);
            for x in [0x8000_0001, 0x7fff_fffe, 0xffff_ffff, 1] {
                for n in amounts {
                    let mut m = Machine::new(&p, 64).expect("an ARM32 machine");
                    assert!(m.set_register("r1", x) && m.set_register("r2", n));
                    assert_eq!(m.run(AT).stop, Stop::Returned);
                    let want = m.register("r0");
                    assert_eq!(h.eval(&[x, n], 64, 32), want, "{h}({x:#x}, {n:#x})");
                }
            }
        }
    }

    /// Only a register shift's select prints as its helper.
    ///
    /// The lifter's three selects print as their helpers on the amount
    /// register; a select whose false arm is not the shift's fill, whose
    /// test is another, whose amount may pass the low byte, or in an image
    /// of another instruction set, prints as it is.
    ///
    /// # Panics
    ///
    /// When a select is read wrong.
    #[test]
    fn only_a_register_shift_select_prints_as_its_helper() {
        let p = a32(0xe1a0_0211);
        let x = Expr::Var(Key::Reg(Register::ECX));
        let rs = Expr::Var(Key::Reg(Register::EDX));
        let by = Expr::Bin(Op::And, Box::new(rs.clone()), Box::new(Expr::Const(0xff)));
        let s = Expr::Sext(Box::new(x.clone()), 32);
        let shl = fold(Op::Shl, x.clone(), by.clone(), 32);
        let shr = fold(Op::Shr, x.clone(), by.clone(), 32);
        let sar = fold(Op::Sar, s.clone(), by.clone(), 32);
        let sign = fold(Op::Sar, s, Expr::Const(31), 32);
        let below = ConditionCode::b;
        for (then, fill, h) in [
            (&shl, &Expr::Const(0), Helper::Lsl32),
            (&shr, &Expr::Const(0), Helper::Lsr32),
            (&sar, &sign, Helper::Asr32),
        ] {
            assert_eq!(
                call(&small(&by, below), then, fill, &p),
                Some(Expr::Helper(h, vec![x.clone(), rs.clone()])),
                "{h}"
            );
        }
        let x86 = Program::raw_x64(&[0xc3]);
        for (cond, then, fill) in [
            (small(&by, below), &shl, &Expr::Const(1)),
            (small(&by, below), &shr, &sign),
            (small(&by, below), &sar, &Expr::Const(0)),
            (small(&by, ConditionCode::be), &shl, &Expr::Const(0)),
            (
                small(&rs, below),
                &fold(Op::Shl, x, rs, 32),
                &Expr::Const(0),
            ),
        ] {
            assert_eq!(call(&cond, then, fill, &p), None, "{then:?} {fill:?}");
        }
        assert_eq!(call(&small(&by, below), &shl, &Expr::Const(0), &x86), None);
    }
}
