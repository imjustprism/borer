//! The flags an arm64 block sets and reads, in the x86 lifter's vocabulary.
//!
//! The lifter keeps what set the flags ([`Flags`]) and asks a condition of
//! it, so what an arm64 condition means depends on that instruction, as on
//! the machine. A `subs` (and `cmp`) leaves a compare whose carry is set
//! when nothing borrows, the opposite of the x86 carry a [`Flags::Cmp`]
//! models: `hs` reads as x86's `ae` and `lo` as `b`, which is the same
//! unsigned order. An `adds` (and `cmn`) leaves an addition whose carry is
//! the x86 carry: `hs` reads as `b` and `lo` as `ae`. An `ands` (and `tst`)
//! leaves a test with carry and overflow clear. A `ccmp` leaves the truth
//! of the condition the next reader asks ([`Flags::Truth`]), tagged with
//! the x86 code standing for that condition ([`tag`]), unless an `mrs` of
//! `NZCV` reads those flags before anything sets them again: then it leaves
//! [`Flags::Carry`] holding the whole word, the compare when the condition
//! holds and the immediate otherwise. A register `msr` of `NZCV` leaves
//! [`Flags::Carry`] holding that word in bits 28 to 31, and a condition
//! reads those bits; any other `msr` sets no flags.

use super::super::expr::{Cc, Cond, Expr, Flags, Op, fold, ternary};
use super::super::fcmp::FPred;
use crate::emulate::a64::{SYSREG_NZCV, SYSREG_TPIDR_EL0};
use crate::isa::a64::{self, Flow, Insn, Mnemonic, Opnd, Reg};
use crate::isa::x86::ConditionCode;
use crate::num::lo8;

/// Bit 31 of an `NZCV` word: the N flag.
const N_BIT: u64 = 31;
/// Bit 30 of an `NZCV` word: the Z flag.
const Z_BIT: u64 = 30;
/// Bit 29 of an `NZCV` word: the C flag.
const C_BIT: u64 = 29;
/// Bit 28 of an `NZCV` word: the V flag, and the shift that places a
/// conditional compare's immediate there.
const V_BIT: u64 = 28;

/// What a conditional branch tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Test {
    /// `b.cond`: a condition on the flags.
    Flags(a64::Cond),
    /// `cbz` or `cbnz`: a register against zero.
    Zero {
        /// The register.
        reg: Reg,
        /// The width it is read at, 32 or 64.
        bits: u16,
        /// Taken when the register is zero (`cbz`), else when it is not.
        zero: bool,
    },
    /// `tbz` or `tbnz`: one bit of a register.
    Bit {
        /// The register.
        reg: Reg,
        /// The width it is read at, 32 or 64.
        bits: u16,
        /// The bit's number, below 64.
        bit: u8,
        /// Taken when the bit is set (`tbnz`), else when it is clear.
        set: bool,
    },
}

/// Reads what a conditional branch tests.
///
/// # Arguments
///
/// * `i` - The branch.
///
/// # Returns
///
/// The test, or `None` for an instruction that is no conditional branch or
/// whose operands the decoder left unmodeled.
pub(super) fn test(i: &Insn) -> Option<Test> {
    match i.op {
        a64::Op::BCond(c) => Some(Test::Flags(c)),
        a64::Op::Cbz | a64::Op::Cbnz => {
            let Opnd::Reg { reg, bits } = i.operands[0] else {
                return None;
            };
            Some(Test::Zero {
                reg,
                bits,
                zero: i.op == a64::Op::Cbz,
            })
        }
        a64::Op::Tbz | a64::Op::Tbnz => {
            let (Opnd::Reg { reg, bits }, Opnd::Imm(bit)) = (i.operands[0], i.operands[1]) else {
                return None;
            };
            Some(Test::Bit {
                reg,
                bits,
                bit: u8::try_from(bit).ok().filter(|b| *b < 64)?,
                set: i.op == a64::Op::Tbnz,
            })
        }
        a64::Op::B
        | a64::Op::Bl
        | a64::Op::Br
        | a64::Op::Blr
        | a64::Op::Ret
        | a64::Op::Eret
        | a64::Op::Trap
        | a64::Op::Syscall
        | a64::Op::Adr
        | a64::Op::Adrp
        | a64::Op::Nop
        | a64::Op::Bti
        | a64::Op::Pac
        | a64::Op::Sve
        | a64::Op::Sme
        | a64::Op::Invalid
        | a64::Op::Other => None,
    }
}

/// Returns the x86 condition code that stands for an arm64 condition.
///
/// A [`Flags::Truth`] is tagged with it: one code per condition, the
/// inverse condition's code the inverse code, so a truth tagged for one
/// condition answers it and its inverse.
///
/// # Arguments
///
/// * `c` - The arm64 condition.
///
/// # Returns
///
/// The code, or `None` for `al` and `nv`, which hold whatever the flags.
fn tag(c: a64::Cond) -> Option<Cc> {
    use ConditionCode as C;
    Some(Cc(match c {
        a64::Cond::Eq => C::e,
        a64::Cond::Ne => C::ne,
        a64::Cond::Hs => C::ae,
        a64::Cond::Lo => C::b,
        a64::Cond::Mi => C::s,
        a64::Cond::Pl => C::ns,
        a64::Cond::Vs => C::o,
        a64::Cond::Vc => C::no,
        a64::Cond::Hi => C::a,
        a64::Cond::Ls => C::be,
        a64::Cond::Ge => C::ge,
        a64::Cond::Lt => C::l,
        a64::Cond::Gt => C::g,
        a64::Cond::Le => C::le,
        a64::Cond::Al | a64::Cond::Nv => return None,
    }))
}

/// A condition that holds exactly when `e` is not zero.
///
/// # Arguments
///
/// * `e` - The truth value.
/// * `cc` - The code it stands for.
fn truth(e: Expr, cc: Cc) -> Cond {
    Cond {
        cc,
        flags: Flags::Truth(e, cc),
    }
}

/// The condition over a float compare's flags.
///
/// An unordered `fcmp` sets N, Z, C and V to `0011`, so each arm64
/// condition asks one predicate ([`FPred`]): `eq` is the ordered equality
/// and `ne` its negation, `mi` and `lo` the ordered less-than, `pl` and
/// `hs` its negation, `ge` and `gt` ordered, `lt` and `le` unordered, `hi`
/// the unordered greater-than, `ls` the ordered less-or-equal, `vs` the
/// unordered test and `vc` its negation.
///
/// # Arguments
///
/// * `a` - The compare's first value.
/// * `b` - Its second.
/// * `bits` - Their width.
/// * `c` - The arm64 condition.
///
/// # Returns
///
/// The condition: [`Flags::FCmp`] asked by `ne`.
fn float_condition(a: &Expr, b: &Expr, bits: u8, c: a64::Cond) -> Cond {
    let p = match c {
        a64::Cond::Eq => FPred::Oeq,
        a64::Cond::Ne => FPred::Une,
        a64::Cond::Hs | a64::Cond::Pl => FPred::Uge,
        a64::Cond::Lo | a64::Cond::Mi => FPred::Olt,
        a64::Cond::Vs => FPred::Uno,
        a64::Cond::Vc => FPred::Ord,
        a64::Cond::Hi => FPred::Ugt,
        a64::Cond::Ls => FPred::Ole,
        a64::Cond::Ge => FPred::Oge,
        a64::Cond::Lt => FPred::Ult,
        a64::Cond::Gt => FPred::Ogt,
        a64::Cond::Le => FPred::Ule,
        a64::Cond::Al | a64::Cond::Nv => FPred::True,
    };
    Cond {
        cc: Cc(ConditionCode::ne),
        flags: Flags::FCmp(p, a.clone(), b.clone(), bits),
    }
}

/// The condition an arm64 condition code asks of the flags.
///
/// # Arguments
///
/// * `flags` - What set the flags.
/// * `c` - The arm64 condition.
///
/// # Returns
///
/// The condition: one that always holds for `al` and `nv`, and one over
/// [`Flags::Unknown`] when nothing the lifter knows set the flags.
pub(in crate::analysis::decompile) fn condition(flags: &Flags, c: a64::Cond) -> Cond {
    let Some(cc) = tag(c) else {
        return truth(Expr::Const(1), Cc(ConditionCode::ne));
    };
    let plain = |cc: Cc| Cond {
        cc,
        flags: flags.clone(),
    };
    let unknown = Cond {
        cc,
        flags: Flags::Unknown,
    };
    match flags {
        Flags::Float(a, b, bits) => float_condition(a, b, *bits, c),
        Flags::Cmp(a, b, bits) => match c {
            a64::Cond::Vs | a64::Cond::Vc => Cond {
                cc,
                flags: Flags::Truth(sub_overflow(a, b, *bits), Cc(ConditionCode::o)),
            },
            a64::Cond::Eq
            | a64::Cond::Ne
            | a64::Cond::Hs
            | a64::Cond::Lo
            | a64::Cond::Mi
            | a64::Cond::Pl
            | a64::Cond::Hi
            | a64::Cond::Ls
            | a64::Cond::Ge
            | a64::Cond::Lt
            | a64::Cond::Gt
            | a64::Cond::Le
            | a64::Cond::Al
            | a64::Cond::Nv => plain(cc),
        },
        Flags::Add(a, b, bits) => match c {
            a64::Cond::Hs => plain(Cc(ConditionCode::b)),
            a64::Cond::Lo => plain(Cc(ConditionCode::ae)),
            a64::Cond::Hi | a64::Cond::Ls => {
                let carry = fold(Op::UAddO(*bits), a.clone(), b.clone(), 64);
                let nonzero = Expr::Cond(Box::new(Cond {
                    cc: Cc(ConditionCode::ne),
                    flags: flags.clone(),
                }));
                Cond {
                    cc,
                    flags: Flags::Truth(fold(Op::And, carry, nonzero, 64), Cc(ConditionCode::a)),
                }
            }
            a64::Cond::Eq
            | a64::Cond::Ne
            | a64::Cond::Mi
            | a64::Cond::Pl
            | a64::Cond::Vs
            | a64::Cond::Vc
            | a64::Cond::Ge
            | a64::Cond::Lt
            | a64::Cond::Gt
            | a64::Cond::Le
            | a64::Cond::Al
            | a64::Cond::Nv => plain(cc),
        },
        Flags::Test(..) | Flags::Result(..) => match c {
            a64::Cond::Hs | a64::Cond::Hi | a64::Cond::Vs => truth(Expr::Const(0), cc),
            a64::Cond::Lo | a64::Cond::Ls | a64::Cond::Vc => truth(Expr::Const(1), cc),
            a64::Cond::Eq
            | a64::Cond::Ne
            | a64::Cond::Mi
            | a64::Cond::Pl
            | a64::Cond::Ge
            | a64::Cond::Lt
            | a64::Cond::Gt
            | a64::Cond::Le
            | a64::Cond::Al
            | a64::Cond::Nv => plain(cc),
        },
        Flags::Truth(_, held) if *held == cc || held.invert() == cc => plain(cc),
        Flags::Carry(word) => nzcv_condition(word, c, cc),
        Flags::Truth(..) | Flags::Shift(..) | Flags::FCmp(..) | Flags::Unknown => unknown,
    }
}

/// The flags that answer the condition `c` with the truth of `e`: what a
/// conditional compare leaves for its reader.
///
/// # Arguments
///
/// * `c` - The condition the reader asks.
/// * `e` - Whether it holds, as 1 or 0.
///
/// # Returns
///
/// A [`Flags::Truth`] tagged for `c`, or [`Flags::Unknown`] for `al` and
/// `nv`, which ask nothing of the flags.
pub(in crate::analysis::decompile) fn answer(c: a64::Cond, e: Expr) -> Flags {
    tag(c).map_or(Flags::Unknown, |cc| Flags::Truth(e, cc))
}

/// The value 1 or 0 of the condition `c` on the flags.
///
/// # Arguments
///
/// * `flags` - What set the flags.
/// * `c` - The condition.
pub(in crate::analysis::decompile) fn value(flags: &Flags, c: a64::Cond) -> Expr {
    ternary(condition(flags, c), Expr::Const(1), Expr::Const(0))
}

/// The signed overflow of `a - b` at a width, as 1 or 0: the operands'
/// signs differ and the difference's differs from the first's.
///
/// # Arguments
///
/// * `a` - The minuend.
/// * `b` - The subtrahend.
/// * `bits` - The width, 32 or 64; only the low `bits` of each operand
///   count.
fn sub_overflow(a: &Expr, b: &Expr, bits: u8) -> Expr {
    let difference = fold(Op::Sub, a.clone(), b.clone(), 64);
    let signs = fold(
        Op::And,
        fold(Op::Xor, a.clone(), b.clone(), 64),
        fold(Op::Xor, a.clone(), difference, 64),
        64,
    );
    let top = fold(
        Op::Shr,
        signs,
        Expr::Const(u64::from(bits.saturating_sub(1))),
        64,
    );
    fold(Op::And, top, Expr::Const(1), 64)
}

/// Tells whether a condition holds on four immediate flags, as a `ccmp`
/// whose condition fails sets them.
///
/// # Arguments
///
/// * `c` - The condition.
/// * `nzcv` - The flags, N in bit 3 down to V in bit 0.
pub(in crate::analysis::decompile) fn holds(c: a64::Cond, nzcv: u64) -> bool {
    let (n, z, carry, v) = (nzcv & 8 != 0, nzcv & 4 != 0, nzcv & 2 != 0, nzcv & 1 != 0);
    match c {
        a64::Cond::Eq => z,
        a64::Cond::Ne => !z,
        a64::Cond::Hs => carry,
        a64::Cond::Lo => !carry,
        a64::Cond::Mi => n,
        a64::Cond::Pl => !n,
        a64::Cond::Vs => v,
        a64::Cond::Vc => !v,
        a64::Cond::Hi => carry && !z,
        a64::Cond::Ls => !carry || z,
        a64::Cond::Ge => n == v,
        a64::Cond::Lt => n != v,
        a64::Cond::Gt => !z && n == v,
        a64::Cond::Le => z || n != v,
        a64::Cond::Al | a64::Cond::Nv => true,
    }
}

/// The condition an instruction reads the flags for.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// The condition of a `b.cond`, a conditional select or compare, and `hs`
/// for the carry an add or subtract with carry reads; `None` for an
/// instruction that reads no flags, or reads them for `al` or `nv`.
pub(super) fn reads(i: &Insn) -> Option<a64::Cond> {
    let selects = matches!(
        i.mnemonic,
        Mnemonic::Csel
            | Mnemonic::Csinc
            | Mnemonic::Csinv
            | Mnemonic::Csneg
            | Mnemonic::Ccmp
            | Mnemonic::Ccmn
            | Mnemonic::Fccmp
            | Mnemonic::Fcsel
    );
    let carries = matches!(
        i.mnemonic,
        Mnemonic::Adc | Mnemonic::Adcs | Mnemonic::Sbc | Mnemonic::Sbcs
    );
    let c = if let a64::Op::BCond(c) = i.op {
        c
    } else if let (true, Opnd::Cond(c)) = (selects, i.operands[3]) {
        c
    } else if carries {
        a64::Cond::Hs
    } else {
        return None;
    };
    (!matches!(c, a64::Cond::Al | a64::Cond::Nv)).then_some(c)
}

/// Tells whether an instruction sets the flags.
///
/// The flag-setting arithmetic and logic, the compares, integer and
/// floating-point alike, the conditional compares, a register `msr` of
/// `NZCV`, and a call, after which the flags hold nothing the caller set.
/// An `msr` of any other register, `TPIDR_EL0` included, sets no flags.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(super) fn writes(i: &Insn) -> bool {
    if i.flow == Flow::Call {
        return true;
    }
    if i.mnemonic == Mnemonic::Msr {
        let (_, field, register_form) = system_access(i);
        return register_form && field == SYSREG_NZCV;
    }
    matches!(
        i.mnemonic,
        Mnemonic::Subs
            | Mnemonic::Adds
            | Mnemonic::Ands
            | Mnemonic::Bics
            | Mnemonic::Adcs
            | Mnemonic::Sbcs
            | Mnemonic::Ccmp
            | Mnemonic::Ccmn
            | Mnemonic::Fcmp
            | Mnemonic::Fcmpe
            | Mnemonic::Fccmp
    )
}

/// The condition the next reader of the flags asks, before anything sets
/// them again.
///
/// # Arguments
///
/// * `later` - The block's instructions after the one setting them.
///
/// # Returns
///
/// The condition, or `None` when nothing in the block reads them first.
pub(super) fn next_reader(later: &[Insn]) -> Option<a64::Cond> {
    for i in later {
        if let Some(c) = reads(i) {
            return Some(c);
        }
        if writes(i) {
            return None;
        }
    }
    None
}

/// Which flags each instruction of a block leaves for a later reader:
/// every bit where one reads them before they are set again, in the block
/// or, when `flags_out`, after it; none where they are dead.
///
/// An `mrs` of `NZCV` reads the flags the block already holds. [`reads`]
/// does not report it, so the block does not keep a predecessor's flags:
/// a block starts with them clear.
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
        if writes(i) {
            live = 0;
        }
        let reads_nzcv = i.mnemonic == Mnemonic::Mrs && {
            let (_, field, _) = system_access(i);
            field == SYSREG_NZCV
        };
        if reads(i).is_some() || reads_nzcv {
            live = u32::MAX;
        }
    }
    after
}

/// The general register, system-register field and register form of an
/// `mrs` or `msr`, read from the word as the machine reads them.
///
/// The decoder keeps only four bits of an `msr`'s register, so the field
/// is not an operand.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// The general register (`x31` as the zero register), bits 5 to 20, and
/// whether bit 20 selects the register form.
pub(super) fn system_access(i: &Insn) -> (Reg, u32, bool) {
    let rt = match i.word & 0x1f {
        0x1f => Reg::Zr,
        n => Reg::X(lo8(u64::from(n))),
    };
    let field = (i.word >> 5) & 0xffff;
    let register_form = (i.word >> 20) & 1 == 1;
    (rt, field, register_form)
}

/// Tells whether an `mrs` of `NZCV` reads the flags before anything sets
/// them again.
///
/// [`reads`] does not report that `mrs`: a block that leads with one does
/// not keep a predecessor's flags, and replay still checks the block. This
/// only says the flags just set are read back as a whole word.
///
/// # Arguments
///
/// * `later` - The block's instructions after the one setting the flags.
pub(super) fn mrs_nzcv_before_write(later: &[Insn]) -> bool {
    for i in later {
        if i.mnemonic == Mnemonic::Mrs {
            let (_, field, _) = system_access(i);
            if field == SYSREG_NZCV {
                return true;
            }
        }
        if writes(i) {
            return false;
        }
    }
    false
}

/// The flags a conditional compare leaves when an `mrs` of `NZCV` reads
/// them back.
///
/// The word is the compare's N, Z, C and V when `held` is true, and the
/// immediate `nzcv` in bits 31 to 28 otherwise. A later condition reads
/// those bits. The word is not the truth of one condition, and it is not
/// [`Flags::Unknown`], which [`nzcv_word`] would read as zero.
///
/// # Arguments
///
/// * `held` - Whether the compare's own condition holds.
/// * `compared` - The compare performed when `held` is true.
/// * `nzcv` - The immediate flags, N in bit 3 down to V in bit 0.
pub(super) fn conditional_nzcv(held: Cond, compared: &Flags, nzcv: u64) -> Flags {
    let then = nzcv_word(compared);
    let shift = u32::try_from(V_BIT).unwrap_or(0);
    let otherwise = Expr::Const(nzcv << shift);
    Flags::Carry(ternary(held, then, otherwise))
}

/// Tells whether an `mrs` or `msr` is one the lifter models.
///
/// Modeled moves are `TPIDR_EL0` and `NZCV`. An `msr` is modeled only in
/// its register form; an immediate write of a processor-state field is not.
/// `svc` and every other system register are not.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(in crate::analysis::decompile) fn modeled_system(i: &Insn) -> bool {
    let (_, field, register_form) = system_access(i);
    let known = field == SYSREG_TPIDR_EL0 || field == SYSREG_NZCV;
    (i.mnemonic == Mnemonic::Mrs && known)
        || (i.mnemonic == Mnemonic::Msr && known && register_form)
}

/// The `NZCV` word the flags hold, in bits 28 to 31.
///
/// A float compare's C flag is the inverse of N. Flags nothing in the
/// block set read as zero, which is how a block starts. An `msr` of `NZCV`
/// leaves the word in [`Flags::Carry`], already masked to those bits.
///
/// # Arguments
///
/// * `flags` - What set the flags.
pub(in crate::analysis::decompile) fn nzcv_word(flags: &Flags) -> Expr {
    match flags {
        Flags::Carry(word) => word.clone(),
        Flags::Unknown => Expr::Const(0),
        Flags::Float(..) => {
            let n = value(flags, a64::Cond::Mi);
            pack_nzcv(
                n.clone(),
                value(flags, a64::Cond::Eq),
                invert_bit(n),
                value(flags, a64::Cond::Vs),
            )
        }
        Flags::Cmp(..)
        | Flags::Add(..)
        | Flags::Test(..)
        | Flags::Result(..)
        | Flags::Truth(..)
        | Flags::FCmp(..)
        | Flags::Shift(..) => pack_nzcv(
            value(flags, a64::Cond::Mi),
            value(flags, a64::Cond::Eq),
            value(flags, a64::Cond::Hs),
            value(flags, a64::Cond::Vs),
        ),
    }
}

/// N, Z, C and V as bits 31 to 28 of one word.
///
/// # Arguments
///
/// * `n` - The N flag, 1 or 0.
/// * `z` - The Z flag, 1 or 0.
/// * `c` - The C flag, 1 or 0.
/// * `v` - The V flag, 1 or 0.
fn pack_nzcv(n: Expr, z: Expr, c: Expr, v: Expr) -> Expr {
    let place = |bit: Expr, at: u64| fold(Op::Shl, bit, Expr::Const(at), 64);
    fold(
        Op::Or,
        fold(Op::Or, place(n, N_BIT), place(z, Z_BIT), 64),
        fold(Op::Or, place(c, C_BIT), place(v, V_BIT), 64),
        64,
    )
}

/// One bit of an `NZCV` word, as 1 or 0.
///
/// # Arguments
///
/// * `word` - The word.
/// * `at` - The bit's index.
fn flag_bit(word: &Expr, at: u64) -> Expr {
    fold(
        Op::And,
        fold(Op::Shr, word.clone(), Expr::Const(at), 64),
        Expr::Const(1),
        64,
    )
}

/// The inverse of a flag bit: `1` when `bit` is `0`.
///
/// # Arguments
///
/// * `bit` - The flag, 1 or 0.
fn invert_bit(bit: Expr) -> Expr {
    fold(Op::Xor, bit, Expr::Const(1), 64)
}

/// A condition on an `NZCV` word an `msr` stored.
///
/// # Arguments
///
/// * `word` - The word, N in bit 31 down to V in bit 28.
/// * `c` - The arm64 condition.
/// * `cc` - The x86 code that stands for `c`.
fn nzcv_condition(word: &Expr, c: a64::Cond, cc: Cc) -> Cond {
    let n = flag_bit(word, N_BIT);
    let z = flag_bit(word, Z_BIT);
    let carry = flag_bit(word, C_BIT);
    let v = flag_bit(word, V_BIT);
    let pred = match c {
        a64::Cond::Eq => z,
        a64::Cond::Ne => invert_bit(z),
        a64::Cond::Hs => carry,
        a64::Cond::Lo => invert_bit(carry),
        a64::Cond::Mi => n,
        a64::Cond::Pl => invert_bit(n),
        a64::Cond::Vs => v,
        a64::Cond::Vc => invert_bit(v),
        a64::Cond::Hi => fold(Op::And, carry, invert_bit(z), 64),
        a64::Cond::Ls => fold(Op::Or, invert_bit(carry), z, 64),
        a64::Cond::Ge => invert_bit(fold(Op::Xor, n, v, 64)),
        a64::Cond::Lt => fold(Op::Xor, n, v, 64),
        a64::Cond::Gt => fold(
            Op::And,
            invert_bit(z),
            invert_bit(fold(Op::Xor, n, v, 64)),
            64,
        ),
        a64::Cond::Le => fold(Op::Or, z, fold(Op::Xor, n, v, 64), 64),
        a64::Cond::Al | a64::Cond::Nv => Expr::Const(1),
    };
    truth(pred, cc)
}
