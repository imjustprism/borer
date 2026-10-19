//! The claims of one block proved over every state, not three.
//!
//! The sampled replay draws three states, runs the block on the emulator
//! and its statements on the text, and compares. This runs the same block
//! once over symbolic values ([`Term`]): the text's statements through the
//! replay's own evaluation with terms in place of bits, and the machine
//! through the lifter's symbolic semantics of the block's instructions
//! (the lifting [`verify`](super::super::verify) checks against the
//! emulator), from the same relation at the block's start. Every claim the
//! sampled replay compares (a register or slot a successor reads, memory
//! off the frame, the stack pointer, the branch, a call's target and
//! arguments, a return) becomes an equality of two terms. When every one
//! holds in normal form the block is proved: no state the replay could
//! draw tells the text from the machine.
//!
//! What the proof does not model it does not guess. A block is left to
//! the samples when an address it stores to or reads after a write is
//! not a constant (the frame is: the replay's stack pointer is fixed), a
//! vector register a successor reads changes, a value the lift does not
//! state takes part, or a statement reaches past integers and float
//! compares (a helper, a float conversion, a `switch`). A claim whose two
//! sides differ as terms proves nothing either way; the states it returns
//! ([`Proof::Differ`]) are tried on the emulator, and only a disagreement
//! the emulator confirms refutes the block.

use std::collections::{BTreeMap, BTreeSet};

use crate::isa::x86::{
    ConditionCode, Instruction, InstructionInfoFactory, OpAccess, OpKind, Register,
};

use super::super::expr::{Cond, Expr, Flags, Key, Op, TLS_BASE, Ty, UnOp, either_width, tls_slot};
use super::super::helper::Helper;
use super::super::lift::{
    ArgAt, BlockFacts, Callee, EffectKind, Env, Pass, exec_block, try_level_store,
};
use super::super::verify::{
    EVAL_DEPTH, Effect as Wrote, FRAME_SPAN, Probe, REGION_MAX, aligns_stack, low, statement_only,
    written_registers,
};
use super::super::{Ctx, new_ctx};
use super::term::{
    self, EQ, GT, LT, Logic, Point, Pred, Term, UN, float_rel, ite, narrow, not, truth, zero,
};
use super::{
    Bench, Code, End, Function, Replay, Transfer, covering, floating, frame_base, op_width,
    overwritten_first, value_lane,
};
use crate::analysis::BasicBlock;
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::num::from_usize;

/// States tried per claim whose two sides differ, looking for one that
/// tells them apart.
const SEARCH_POINTS: u64 = 192;
/// Most bytes written over memory a read through an address the state
/// picks is modeled over.
const OVERRIDES_MAX: usize = 128;
/// Claims a block's search looks at before it stops.
const SEARCHED_CLAIMS: usize = 4;
/// What the search adds to a value it starts from: nothing, or the sign
/// bit of a byte, a word, a doubleword or a quadword, so a value that
/// agrees with a constant only in its low bits is tried too.
const SIGNS: [u64; 6] = [0, 0, 1 << 7, 1 << 15, 1 << 31, 1 << 63];

/// What a block's proof found.
#[derive(Debug)]
pub(super) enum Proof {
    /// Every claim holds in every state the replay compares it in.
    Proved,
    /// Some claim's two sides differ as terms: states that may tell them
    /// apart, each as the values the block's variables start with.
    Differ(Vec<FxHashMap<Key, u64>>),
    /// Why the block is outside what the proof models.
    Unknown(&'static str),
}

/// Why the proof leaves a block to the samples.
type Why = &'static str;

/// The temporary that stands for the left operand of the flags an earlier
/// instruction left, while the next is lifted on its own.
const FLAG_LEFT: u32 = u32::MAX;
/// The temporary that stands for the right operand of those flags.
const FLAG_RIGHT: u32 = u32::MAX - 1;
/// The temporary below which a register's bits the lift does not state
/// are named, one fresh variable each, counting down.
const FRESH_FIRST: u32 = u32::MAX - 1;
/// Why a whole block's lifting cannot be read: it reads bytes it also
/// writes, before or after the write.
const STALE: &str = "a read of memory the block writes";
/// Why a block is left to the samples: a compare's flags were set by a
/// float compare and an integer one, and the lift does not say which a
/// reader reads.
const MIXED: &str = "flags from both a float and an integer compare";
/// Why a whole block's lifting cannot be read: it reads through an
/// address the state picks, before or after a write.
const BESIDE: &str = "a read through a computed address beside a write";

/// Flags an instruction left, their operands named by [`FLAG_LEFT`] and
/// [`FLAG_RIGHT`], with the names' values.
type Held = (Flags, FxHashMap<u32, Term>);

/// The machine's state between the steps the lifter takes through a
/// block.
#[derive(Debug, Clone)]
struct Run {
    /// Each register's value, whole: the bits the lift does not state are
    /// a fresh variable.
    regs: FxHashMap<Key, Term>,
    /// The low bits of each general register the lift states, where fewer
    /// than all.
    known: FxHashMap<Key, u8>,
    /// The stack pointer.
    sp: u64,
    /// Memory beyond what it held before the block.
    mem: BTreeMap<u64, Byte>,
    /// The bytes written so far.
    written: BTreeSet<u64>,
    /// The flags left so far, as operands named by [`FLAG_LEFT`] and
    /// [`FLAG_RIGHT`] with their values.
    flags: Option<Held>,
    /// Some vector register was written.
    vectors: bool,
    /// Whether the block's conditional branch is taken.
    taken: Option<Pred>,
    /// The last fresh variable named.
    fresh: u32,
    /// The frame bytes the text holds no value for.
    lost: BTreeSet<u64>,
}

/// The flags an instruction left, with their operands named by
/// temporaries the next instruction's lifting reads.
///
/// A compare of floats becomes a float compare, so the reading does not
/// depend on the operands' types, which the names hide.
///
/// # Arguments
///
/// * `f` - The flags.
/// * `lifted` - The instruction's state, which gives the operands' values.
///
/// # Returns
///
/// The named flags and the names' values, `None` for unknown flags.
///
/// # Errors
///
/// An operand outside what the proof models.
fn hold_flags(f: &Flags, lifted: &Lifted<'_>) -> Result<Option<Held>, Why> {
    let (l, r) = (
        Expr::Var(Key::Tmp(FLAG_LEFT)),
        Expr::Var(Key::Tmp(FLAG_RIGHT)),
    );
    let ev = |e: &Expr| lifted.eval(e, EVAL_DEPTH);
    let temps = Some(lifted.temps);
    let (shape, a, b) = match f {
        Flags::Unknown => return Ok(None),
        Flags::Cmp(x, y, w) => {
            let fb = match (
                float_bits(x, temps).or_else(|| float_bits(y, temps)),
                lifted.floats,
            ) {
                (Some(fb), _) => Some(fb),
                (None, Some(true)) if matches!(w, 32 | 64) => Some(*w),
                (None, None) if matches!(w, 32 | 64) => return Err(MIXED),
                (None, Some(_) | None) => None,
            };
            match fb {
                Some(fb) => (Flags::Float(l, r, fb), ev(x)?, Some(ev(y)?)),
                None => (Flags::Cmp(l, r, *w), ev(x)?, Some(ev(y)?)),
            }
        }
        Flags::Float(x, y, w) => (Flags::Float(l, r, *w), ev(x)?, Some(ev(y)?)),
        Flags::Test(x, y, w) => (Flags::Test(l, r, *w), ev(x)?, Some(ev(y)?)),
        Flags::Add(x, y, w) => (Flags::Add(l, r, *w), ev(x)?, Some(ev(y)?)),
        Flags::Result(x, w) => (Flags::Result(l, *w), ev(x)?, None),
        Flags::Carry(x) => (Flags::Carry(l), ev(x)?, None),
        Flags::Shift(x, w, y) => (Flags::Shift(l, *w, r), ev(x)?, Some(ev(y)?)),
        Flags::Truth(x, cc) => (Flags::Truth(l, *cc), ev(x)?, None),
    };
    let mut held = FxHashMap::default();
    held.insert(FLAG_LEFT, a);
    if let Some(b) = b {
        held.insert(FLAG_RIGHT, b);
    }
    Ok(Some((shape, held)))
}

/// One byte of memory as a side holds it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Byte {
    /// Byte `i` of a value, little-endian.
    Of(Term, u8),
    /// The byte memory held at this address where the block started.
    Was(u64),
    /// A byte no state of the replay reads.
    Lost,
}

/// The value of one byte.
///
/// # Arguments
///
/// * `b` - The byte.
fn byte_value(b: &Byte) -> Term {
    match b {
        Byte::Of(t, 0) => narrow(t, 8),
        Byte::Of(_, i) if *i >= 8 => Term::Const(0),
        Byte::Of(t, i) => narrow(
            &term::bin(Op::Shr, 64, t, &Term::Const(8 * u64::from(*i))),
            8,
        ),
        Byte::Was(x) => Term::Mem(Box::new(Term::Const(*x)), 1, Vec::new()),
        Byte::Lost => Term::Undef,
    }
}

/// The bytes a read through an address the state picks may land on that
/// differ from memory as the block found it, each with its value.
///
/// # Arguments
///
/// * `bytes` - Each byte written, by address.
/// * `lost` - Bytes no state of the replay reads a value of.
///
/// # Errors
///
/// More bytes than a read is worth modeling.
fn overrides(bytes: &BTreeMap<u64, Byte>, lost: &BTreeSet<u64>) -> Result<Vec<(u64, Term)>, Why> {
    let keys: BTreeSet<u64> = bytes.keys().chain(lost).copied().collect();
    if keys.len() > OVERRIDES_MAX {
        return Err("a read through a computed address over many writes");
    }
    Ok(keys
        .into_iter()
        .filter_map(|x| {
            if lost.contains(&x) {
                return Some((x, Term::Undef));
            }
            match bytes.get(&x) {
                Some(Byte::Was(y)) if *y == x => None,
                Some(b) => Some((x, byte_value(b))),
                None => None,
            }
        })
        .collect())
}

/// The value of consecutive bytes, little-endian, at most eight.
///
/// Bytes of one value in order read back as the value's own bits, and
/// bytes memory held in order as one read of it, so a store read back
/// whole is the stored value.
///
/// # Arguments
///
/// * `bytes` - The bytes, lowest address first.
/// * `mask` - The register width's mask, where addresses wrap.
fn assemble(bytes: &[Byte], mask: u64) -> Term {
    let n = bytes.len().min(8);
    let bytes = &bytes[..n];
    if bytes.contains(&Byte::Lost) {
        return Term::Undef;
    }
    let bits = u8::try_from(8 * n).unwrap_or(64);
    let count = u8::try_from(n).unwrap_or(8);
    match bytes.first() {
        None => return Term::Const(0),
        Some(Byte::Of(t, k))
            if bytes
                .iter()
                .zip(*k..)
                .all(|(b, i)| matches!(b, Byte::Of(u, j) if u == t && *j == i))
                && usize::from(*k) + n <= 8 =>
        {
            let shifted = if *k == 0 {
                t.clone()
            } else {
                term::bin(Op::Shr, 64, t, &Term::Const(8 * u64::from(*k)))
            };
            return narrow(&shifted, bits);
        }
        Some(Byte::Was(a))
            if bytes
                .iter()
                .zip(0u64..)
                .all(|(b, i)| matches!(b, Byte::Was(x) if *x == a.wrapping_add(i) & mask)) =>
        {
            return Term::Mem(Box::new(Term::Const(*a)), count, Vec::new());
        }
        Some(_) => {}
    }
    bytes
        .iter()
        .zip(0u32..)
        .fold(Term::Const(0), |acc, (b, i)| {
            let shifted = term::mul(64, &byte_value(b), &Term::Const(1u64 << (8 * i)));
            term::add(64, &acc, &shifted)
        })
}

/// The outcomes of a float compare a condition code holds for, as
/// [`super::super::expr::float_cc`] reads them.
///
/// # Arguments
///
/// * `cc` - The condition code.
///
/// # Returns
///
/// The outcome set, `None` for a code a float compare does not decide.
fn float_set(cc: ConditionCode) -> Option<u8> {
    use ConditionCode as C;
    Some(match cc {
        C::a => GT,
        C::ae => EQ | GT,
        C::b => LT | UN,
        C::be => LT | EQ | UN,
        C::e => EQ | UN,
        C::ne => LT | GT,
        C::p => UN,
        C::np => LT | EQ | GT,
        C::None | C::s | C::ns | C::o | C::no | C::l | C::ge | C::le | C::g => return None,
    })
}

/// A float compare's truth under a condition code.
///
/// # Arguments
///
/// * `cc` - The condition code.
/// * `fb` - The values' width.
/// * `a` - The left value.
/// * `b` - The right value.
fn float_pred(cc: ConditionCode, fb: u8, a: &Term, b: &Term) -> Pred {
    match float_set(cc) {
        Some(set) => float_rel(set, fb, a, b),
        None => Pred::Undef,
    }
}

/// What the flags hold, with terms for the values a condition compares.
#[derive(Debug)]
enum Flagged {
    /// `cmp l, r` at a width.
    Cmp(Term, Term, u8),
    /// `test l, r` at a width.
    Test(Term, Term, u8),
    /// An arithmetic result at a width.
    Result(Term, u8),
    /// `add l, r` at a width.
    Add(Term, Term, u8),
    /// A carry out.
    Carry(Term),
    /// A shift's result at a width and its last bit out.
    Shift(Term, u8, Term),
    /// A truth for a condition code.
    Truth(Term, super::super::expr::Cc),
}

/// The truth of a condition code on two values at a width, as
/// [`Cond::eval`] decides it with bits.
///
/// # Arguments
///
/// * `cc` - The condition code.
/// * `l` - The left value.
/// * `r` - The right value.
/// * `bits` - The compared width.
///
/// # Errors
///
/// A width the proof does not model.
fn compare(cc: ConditionCode, l: &Term, r: &Term, bits: u8) -> Result<Pred, Why> {
    use ConditionCode as C;
    if bits == 0 || bits > 64 {
        return Err("a compare of no width");
    }
    let (nl, nr) = (narrow(l, bits), narrow(r, bits));
    let differ = || term::sub(bits, l, r);
    Ok(match cc {
        C::e => zero(differ()),
        C::ne => not(zero(differ())),
        C::b => term::ult(nl, nr),
        C::ae => not(term::ult(nl, nr)),
        C::be => not(term::ult(nr, nl)),
        C::a => term::ult(nr, nl),
        C::l => term::slt(bits, l, r),
        C::ge => not(term::slt(bits, l, r)),
        C::le => not(term::slt(bits, r, l)),
        C::g => term::slt(bits, r, l),
        C::s => term::bit(bits - 1, &differ()),
        C::ns => not(term::bit(bits - 1, &differ())),
        C::None | C::o | C::no | C::p | C::np => Pred::Undef,
    })
}

/// The truth of a condition code on flags, as [`Cond::eval`] decides it
/// once the flags' operands are constants.
///
/// # Arguments
///
/// * `cc` - The condition code.
/// * `f` - The flags.
///
/// # Errors
///
/// A combination the proof does not model.
fn flags_pred(cc: super::super::expr::Cc, f: Flagged) -> Result<Pred, Why> {
    use ConditionCode as C;
    Ok(match f {
        Flagged::Cmp(l, r, bits) => compare(cc.0, &l, &r, bits)?,
        Flagged::Test(l, r, bits) => {
            let both = term::logic(Logic::And, 64, vec![l, r]);
            compare(cc.0, &both, &Term::Const(0), bits)?
        }
        Flagged::Result(e, bits) => compare(cc.0, &e, &Term::Const(0), bits)?,
        Flagged::Shift(e, bits, c) => match cc.0 {
            C::b => not(zero(c)),
            C::ae => zero(c),
            C::be | C::a => return Err("a shift's carry with its result"),
            C::o | C::no => Pred::Undef,
            C::None | C::e | C::ne | C::s | C::ns | C::p | C::np | C::l | C::ge | C::le | C::g => {
                compare(cc.0, &e, &Term::Const(0), bits)?
            }
        },
        Flagged::Carry(c) => match cc.0 {
            C::b | C::o => not(zero(c)),
            C::ae | C::no => zero(c),
            C::None
            | C::e
            | C::ne
            | C::be
            | C::a
            | C::s
            | C::ns
            | C::p
            | C::np
            | C::l
            | C::ge
            | C::le
            | C::g => Pred::Undef,
        },
        Flagged::Add(l, r, bits) => {
            if bits == 0 || bits > 64 {
                return Err("an addition of no width");
            }
            let sum = term::add(bits, &l, &r);
            match cc.0 {
                C::e => zero(sum),
                C::ne => not(zero(sum)),
                C::s => term::bit(bits - 1, &sum),
                C::ns => not(term::bit(bits - 1, &sum)),
                C::b => term::ult(sum, narrow(&l, bits)),
                C::ae => not(term::ult(sum, narrow(&l, bits))),
                C::l | C::ge | C::le | C::g | C::o | C::no => {
                    return Err("a signed test of an addition");
                }
                C::None | C::be | C::a | C::p | C::np => Pred::Undef,
            }
        }
        Flagged::Truth(e, tcc) => {
            if cc == tcc {
                not(zero(e))
            } else if cc == tcc.invert() {
                zero(e)
            } else {
                Pred::Undef
            }
        }
    })
}

/// The width of a floating-point expression, as the replay's text reads
/// it structurally ([`super::Text::float_bits`]), looking through the
/// lifter's temporaries where given.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `temps` - The temporaries the lifter made, or `None` on the text's
///   side, which reads a temporary as its own variable.
fn float_bits(e: &Expr, temps: Option<&BTreeMap<u32, Expr>>) -> Option<u8> {
    match e {
        Expr::Deref(_, Ty::F32) | Expr::Cast(_, Ty::F32) | Expr::FConst(_, Ty::F32) => Some(32),
        Expr::Deref(_, Ty::F64) | Expr::Cast(_, Ty::F64) | Expr::FConst(_, Ty::F64) => Some(64),
        Expr::Var(Key::Tmp(id)) => float_bits(temps?.get(id)?, temps),
        Expr::Bin(op, l, r) if op.is_float() => {
            Some(float_bits(l, temps)?.max(float_bits(r, temps)?))
        }
        Expr::Ternary(_, a, b) => either_width(float_bits(a, temps), float_bits(b, temps)),
        Expr::Un(_, inner) => float_bits(inner, temps),
        Expr::Helper(Helper::Rint, args) => args.first().and_then(|a| float_bits(a, temps)),
        Expr::Deref(..)
        | Expr::Cast(..)
        | Expr::FConst(..)
        | Expr::Var(_)
        | Expr::Bin(..)
        | Expr::Helper(..)
        | Expr::Const(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Cond(_)
        | Expr::Sext(..)
        | Expr::Call(..) => None,
    }
}

/// The text's state over terms: [`super::Text`] with terms for bits.
#[derive(Debug)]
struct Sym<'t> {
    /// The register width, 32 or 64.
    width: u8,
    /// The stack pointer at the function's entry: where slot 0 is.
    sp0: u64,
    /// The stack pointer where the block starts.
    start: u64,
    /// The stack pointer where the block's run stops, which the text's
    /// `rsp` names.
    rsp: u64,
    /// Each variable's value where the block starts, where not its own
    /// input.
    entry: FxHashMap<Key, Term>,
    /// Variables the statements assigned.
    vars: FxHashMap<Key, Term>,
    /// Variables a call left unknown.
    unknown: BTreeSet<Key>,
    /// Memory the text wrote.
    mem: BTreeMap<u64, Byte>,
    /// Bytes both sides start from that the block's equality fixes.
    base: &'t BTreeMap<u64, Byte>,
    /// Bytes the text holds no value for.
    lost: BTreeSet<u64>,
    /// Memory reads as unknown, after a call or a store through an
    /// address the replay cannot evaluate.
    lost_all: bool,
    /// Each frame byte last written through a slot's name, with the slot.
    names: BTreeMap<u64, i64>,
    /// The width each declared slot is declared with.
    slot_bits: &'t BTreeMap<i64, u8>,
    /// The declaration type of each vector register named a float.
    reg_ty: &'t BTreeMap<Key, Ty>,
    /// The float width a call left in a result register.
    result_ty: FxHashMap<Key, Ty>,
    /// The instruction of the statement being replayed.
    at: u64,
    /// The block's flag setters and readers, as the replay keeps them.
    setters: (Vec<(u64, bool)>, Vec<u64>),
}

impl Sym<'_> {
    /// Returns the register width's mask.
    fn mask(&self) -> u64 {
        low(self.width)
    }

    /// Tells whether `n` bytes at `at` run past the top of the address
    /// space.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes.
    fn crosses_top(&self, at: u64, n: u64) -> bool {
        n.saturating_sub(1) > self.mask() - (at & self.mask())
    }

    /// Returns a byte as the text holds it.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn byte(&self, at: u64) -> Byte {
        if self.lost_all || self.lost.contains(&at) {
            return Byte::Lost;
        }
        self.mem
            .get(&at)
            .or_else(|| self.base.get(&at))
            .cloned()
            .unwrap_or(Byte::Was(at))
    }

    /// Reads `n` bytes as the text holds them, little-endian.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes, at most 8.
    ///
    /// # Errors
    ///
    /// A read through an address the state picks after the text wrote
    /// memory, which may or may not land on what it wrote.
    fn read(&self, at: &Term, n: u64) -> Result<Term, Why> {
        match at {
            Term::Undef => Ok(Term::Undef),
            Term::Const(a) => {
                if self.crosses_top(*a, n) {
                    return Ok(Term::Undef);
                }
                let bytes: Vec<Byte> = (0..n.min(8))
                    .map(|i| self.byte(a.wrapping_add(i) & self.mask()))
                    .collect();
                Ok(assemble(&bytes, self.mask()))
            }
            a => {
                if self.lost_all {
                    return Ok(Term::Undef);
                }
                let mut written = self.base.clone();
                written.extend(self.mem.iter().map(|(x, b)| (*x, b.clone())));
                Ok(Term::Mem(
                    Box::new(narrow(a, self.width)),
                    u8::try_from(n.min(8)).unwrap_or(8),
                    overrides(&written, &self.lost)?,
                ))
            }
        }
    }

    /// Writes `n` bytes of a value.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes.
    /// * `value` - The value.
    ///
    /// A value some states lack is written as it is: where it has no value,
    /// the replay loses the bytes and every later read of them has none
    /// either, so the claims that read them compare nothing there.
    fn write(&mut self, at: u64, n: u64, value: &Term) {
        if self.crosses_top(at, n) {
            self.lost_all = true;
            return;
        }
        let undef = *value == Term::Undef;
        for i in 0..n {
            let a = at.wrapping_add(i) & self.mask();
            if undef {
                self.lost.insert(a);
            } else {
                self.mem.insert(
                    a,
                    Byte::Of(value.clone(), u8::try_from(i).unwrap_or(u8::MAX)),
                );
                self.lost.remove(&a);
            }
            self.names.remove(&a);
        }
    }

    /// Tells whether the text last wrote any of `n` bytes at slot `o`
    /// through another slot's name.
    ///
    /// # Arguments
    ///
    /// * `o` - The slot.
    /// * `n` - Bytes.
    fn foreign(&self, o: i64, n: u64) -> bool {
        let at = self.sp0.wrapping_add_signed(o);
        (0..n).any(|i| {
            self.names
                .get(&(at.wrapping_add(i) & self.mask()))
                .is_some_and(|p| *p != o)
        })
    }

    /// Returns a variable's value.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    ///
    /// # Errors
    ///
    /// What [`Sym::read`] refuses.
    fn var(&self, k: Key) -> Result<Term, Why> {
        if self.unknown.contains(&k) {
            return Ok(Term::Undef);
        }
        match k {
            Key::Slot(o) => {
                let bits = self.slot_bits.get(&o).copied().unwrap_or(self.width);
                if bits > 64 {
                    return Ok(Term::Undef);
                }
                let n = u64::from(bits / 8).max(1);
                if self.foreign(o, n) {
                    return Ok(Term::Undef);
                }
                self.read(&Term::Const(self.sp0.wrapping_add_signed(o)), n)
            }
            Key::Global(a, bits) => {
                if a >= TLS_BASE {
                    return Ok(Term::Undef);
                }
                self.read(&Term::Const(a), u64::from(bits / 8).max(1))
            }
            Key::Reg(Register::RSP | Register::ESP) => Ok(Term::Const(self.rsp)),
            Key::A64(_) => Err("an arm64 register"),
            Key::Reg(r) if !r.is_gpr() && !r.is_xmm() => Ok(Term::Undef),
            Key::Reg(_) | Key::Tmp(_) | Key::Param(_) => Ok(self
                .vars
                .get(&k)
                .or_else(|| self.entry.get(&k))
                .cloned()
                .unwrap_or(Term::In(k, self.width))),
        }
    }

    /// The width a float unary operation over `e` runs at
    /// ([`super::Text::un_width`]).
    ///
    /// # Arguments
    ///
    /// * `e` - The operand.
    fn un_width(&self, e: &Expr) -> Option<u8> {
        let Expr::Var(k) = e else {
            return float_bits(e, None);
        };
        float_bits(e, None).or(match self.result_ty.get(k).or_else(|| self.reg_ty.get(k)) {
            Some(Ty::F32) => Some(32),
            Some(Ty::F64) => Some(64),
            Some(Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128) | None => None,
        })
    }

    /// Evaluates an expression over the text's state
    /// ([`super::Text::eval_at`]).
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `depth` - How much deeper to look.
    ///
    /// # Errors
    ///
    /// An expression outside what the proof models.
    fn eval(&self, e: &Expr, depth: u8) -> Result<Term, Why> {
        let Some(d) = depth.checked_sub(1) else {
            return Ok(Term::Undef);
        };
        let w = self.width;
        Ok(match e {
            Expr::Const(v) | Expr::FConst(v, _) => Term::Const(*v),
            Expr::Var(k) => self.var(*k)?,
            Expr::Str(_) | Expr::Call(..) => Term::Undef,
            Expr::Helper(..) => return Err("a helper"),
            Expr::Sp(o) => Term::Const(self.sp0.wrapping_add_signed(*o) & low(w)),
            Expr::Bin(op, l, r) if op.is_float() => {
                let (Some(fl), Some(fr)) = (float_bits(l, None), float_bits(r, None)) else {
                    return Ok(Term::Undef);
                };
                let fb = fl.max(fr);
                term::float_bin(*op, fb, fb, &self.eval(l, d)?, &self.eval(r, d)?)
            }
            Expr::Bin(op, l, r) => term::bin(*op, w, &self.eval(l, d)?, &self.eval(r, d)?),
            Expr::Un(UnOp::Neg, x) if self.un_width(x).is_some() => {
                let fb = self.un_width(x).unwrap_or(64);
                term::logic(
                    Logic::Xor,
                    64,
                    vec![self.eval(x, d)?, Term::Const(1u64 << (u32::from(fb) - 1))],
                )
            }
            Expr::Un(op @ (UnOp::Sqrt | UnOp::Fabs), x) if self.un_width(x).is_some() => {
                term::float_unary(*op, self.un_width(x).unwrap_or(64), &self.eval(x, d)?)
            }
            Expr::Un(UnOp::Sqrt | UnOp::Fabs, _) => Term::Undef,
            Expr::Un(op, x) => term::un(*op, op_width(*op, x, w), &self.eval(x, d)?),
            Expr::Deref(a, ty) => {
                if *ty == Ty::U128 {
                    return Ok(Term::Undef);
                }
                let n = u64::from(ty.bits() / 8).max(1);
                if let Expr::Sp(o) = **a
                    && self.foreign(o, n)
                {
                    return Ok(Term::Undef);
                }
                self.read(&narrow(&self.eval(a, d)?, w), n)?
            }
            Expr::Cond(c) => truth(self.cond(c, d)?),
            Expr::Ternary(c, a, b) => ite(self.cond(c, d)?, self.eval(a, d)?, self.eval(b, d)?),
            Expr::Sext(x, bits) => term::sign_extend(&self.eval(x, d)?, *bits),
            Expr::Cast(x, ty) => match ty {
                Ty::U128 => Term::Undef,
                Ty::F32 | Ty::F64 => return Err("a float conversion"),
                Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 => {
                    let v = self.eval(x, d)?;
                    if matches!(**x, Expr::Var(Key::Param(_))) && self.un_width(x).is_some() {
                        return Err("a parameter declared a float");
                    }
                    match float_bits(x, None) {
                        Some(fb) => term::to_int(fb, ty.bits(), &v),
                        None if floating(x) => Term::Undef,
                        None => narrow(&v, ty.bits()),
                    }
                }
            },
        })
    }

    /// Tells whether the flags a condition at the current statement reads
    /// came from a float compare ([`super::Text::cond_at`]).
    fn float_flags(&self) -> bool {
        let (setters, readers) = &self.setters;
        readers
            .iter()
            .rev()
            .find(|&&r| r <= self.at)
            .and_then(|&r| setters.iter().rev().find(|&&(s, _)| s < r))
            .is_some_and(|&(_, f)| f)
    }

    /// Decides a condition over the text's state
    /// ([`super::Text::cond_at`]).
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    /// * `d` - How much deeper to look.
    ///
    /// # Errors
    ///
    /// A condition outside what the proof models.
    fn cond(&self, c: &Cond, d: u8) -> Result<Pred, Why> {
        if let Flags::Cmp(a, b, w) = &c.flags {
            let fb = float_bits(a, None)
                .or_else(|| float_bits(b, None))
                .or_else(|| {
                    matches!(w, 32 | 64)
                        .then_some(*w)
                        .filter(|_| self.float_flags())
                });
            if let Some(fb) = fb {
                return Ok(float_pred(c.cc.0, fb, &self.eval(a, d)?, &self.eval(b, d)?));
            }
        }
        if let Flags::Float(a, b, fb) = &c.flags {
            return Ok(float_pred(
                c.cc.0,
                *fb,
                &self.eval(a, d)?,
                &self.eval(b, d)?,
            ));
        }
        let k = |e: &Expr| {
            if floating(e) {
                Ok(Term::Undef)
            } else {
                self.eval(e, d)
            }
        };
        let flags = match &c.flags {
            Flags::Cmp(a, b, w) => Flagged::Cmp(k(a)?, k(b)?, *w),
            Flags::Float(..) | Flags::Unknown => return Ok(Pred::Undef),
            Flags::Test(a, b, w) => Flagged::Test(k(a)?, k(b)?, *w),
            Flags::Result(a, w) => Flagged::Result(k(a)?, *w),
            Flags::Add(a, b, w) => Flagged::Add(k(a)?, k(b)?, *w),
            Flags::Carry(a) => Flagged::Carry(k(a)?),
            Flags::Shift(a, w, b) => Flagged::Shift(k(a)?, *w, k(b)?),
            Flags::Truth(a, cc) => Flagged::Truth(k(a)?, *cc),
        };
        flags_pred(c.cc, flags)
    }

    /// Replays `name = value;` ([`super::Text::assign`]).
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    /// * `v` - The value.
    /// * `bits` - The variable's width.
    ///
    /// # Errors
    ///
    /// A value outside what the proof models.
    fn assign(&mut self, k: Key, v: &Expr, bits: u8) -> Result<(), Why> {
        let n = u64::from(bits / 8).max(1);
        let mut value = self.wide(v, n)?;
        if bits <= 64 {
            value = narrow(&value, bits);
        }
        match k {
            Key::Slot(o) => {
                let at = self.sp0.wrapping_add_signed(o);
                self.write(at, n, &value);
                for i in 0..n {
                    self.names.insert(at.wrapping_add(i) & self.mask(), o);
                }
            }
            Key::Global(a, gb) => {
                if a < TLS_BASE {
                    self.write(a, u64::from(gb / 8).max(1), &value);
                }
            }
            Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => {
                self.result_ty.remove(&k);
                if bits > 64 {
                    return Err("a vector variable");
                }
                if value == Term::Undef {
                    self.unknown.insert(k);
                } else {
                    self.vars.insert(k, value);
                    self.unknown.remove(&k);
                }
            }
        }
        Ok(())
    }

    /// A value written to `n` bytes ([`super::wide_value`]).
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    /// * `n` - Bytes.
    ///
    /// # Errors
    ///
    /// A whole vector lane, outside what the proof models.
    fn wide(&self, v: &Expr, n: u64) -> Result<Term, Why> {
        if n <= 8 {
            return self.eval(v, EVAL_DEPTH);
        }
        if *v == Expr::Const(0) {
            Ok(Term::Const(0))
        } else {
            Err("a vector value")
        }
    }

    /// Replays `*(T *)addr = value;` ([`super::Text::store`]).
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `ty` - The type stored.
    /// * `v` - The value.
    ///
    /// # Errors
    ///
    /// An address the state picks, or a value outside what the proof
    /// models.
    fn store(&mut self, addr: &Expr, ty: Ty, v: &Expr) -> Result<(), Why> {
        let a = self.eval(addr, EVAL_DEPTH)?;
        let at = match a {
            Term::Const(at) => at,
            Term::Undef => {
                self.lost_all = true;
                return Ok(());
            }
            Term::In(..)
            | Term::Mem(..)
            | Term::Poly(..)
            | Term::Logic(..)
            | Term::Bin(..)
            | Term::Un(..)
            | Term::Sext(..)
            | Term::Truth(_)
            | Term::Ite(..)
            | Term::Float(..)
            | Term::FloatUn(..)
            | Term::ToInt(..) => return Err("a store through an address the state picks"),
        };
        let below = |k: i64| {
            at.wrapping_sub(self.sp0.wrapping_add_signed(k))
                .cast_signed()
                .wrapping_shl(64 - u32::from(self.width))
                < 0
        };
        if frame_base(addr).is_some_and(below) || at >= TLS_BASE {
            self.lost_all = true;
            return Ok(());
        }
        let n = u64::from(ty.bits() / 8).max(1);
        let value = self.wide(v, n)?;
        self.write(at, n, &value);
        Ok(())
    }
}

/// The machine's side: the lifter's symbolic semantics of a block's
/// instructions, read over the state the relation at its start builds.
#[derive(Debug)]
struct Lifted<'a> {
    /// The register width, 32 or 64.
    width: u8,
    /// The stack pointer where the block starts.
    rsp: u64,
    /// The registers' values where the block starts.
    regs: &'a FxHashMap<Key, Term>,
    /// The bytes memory holds where the block starts beyond what it held
    /// before: the equality's and the values pending for the text.
    overlay: &'a BTreeMap<u64, Byte>,
    /// The bytes the block writes: a read of one reads what the lifter
    /// only knows as it was.
    written: &'a BTreeSet<u64>,
    /// The temporaries the lifter made.
    temps: &'a BTreeMap<u32, Expr>,
    /// The values of the temporaries that stand for the flags' operands
    /// an earlier instruction left ([`FLAG_LEFT`], [`FLAG_RIGHT`]).
    held: &'a FxHashMap<u32, Term>,
    /// Whether the flags the instructions read came from a float compare:
    /// `None` where both a float and an integer compare set them, so which
    /// one a reader reads is not known.
    floats: Option<bool>,
    /// The frame bytes the text holds no value for, which a read through
    /// an address the state picks reads none of either.
    lost: &'a BTreeSet<u64>,
}

impl Lifted<'_> {
    /// Reads `n` bytes as the block found them.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes.
    ///
    /// # Errors
    ///
    /// A read of bytes the block writes, or through an address the state
    /// picks where the block's memory is not all as it was.
    fn read(&self, at: &Term, n: u64) -> Result<Term, Why> {
        if !(1..=8).contains(&n) {
            return Ok(Term::Undef);
        }
        let mask = low(self.width);
        match at {
            Term::Undef => Ok(Term::Undef),
            Term::Const(a) => {
                let bytes: Vec<Byte> = (0..n)
                    .map(|i| {
                        let x = a.wrapping_add(i) & mask;
                        if self.written.contains(&x) {
                            return Err(STALE);
                        }
                        Ok(self.overlay.get(&x).cloned().unwrap_or(Byte::Was(x)))
                    })
                    .collect::<Result<_, Why>>()?;
                Ok(assemble(&bytes, mask))
            }
            a => {
                if !self.written.is_empty() {
                    return Err(BESIDE);
                }
                Ok(Term::Mem(
                    Box::new(narrow(a, self.width)),
                    u8::try_from(n).unwrap_or(8),
                    overrides(self.overlay, self.lost)?,
                ))
            }
        }
    }

    /// Evaluates a lifted expression over the block's starting state, as
    /// [`super::super::verify::eval`] does with bits.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `depth` - How much deeper to look.
    ///
    /// # Errors
    ///
    /// An expression outside what the proof models.
    fn eval(&self, e: &Expr, depth: u8) -> Result<Term, Why> {
        let Some(d) = depth.checked_sub(1) else {
            return Ok(Term::Undef);
        };
        let w = self.width;
        let temps = Some(self.temps);
        Ok(match e {
            Expr::Const(v) | Expr::FConst(v, _) => Term::Const(*v),
            Expr::Var(k @ Key::Reg(r)) => match self.regs.get(k) {
                Some(v) => v.clone(),
                None if matches!(r, Register::ES | Register::CS | Register::SS | Register::DS) => {
                    Term::Const(0)
                }
                None => Term::Undef,
            },
            Expr::Var(Key::Tmp(id)) => match (self.held.get(id), self.temps.get(id)) {
                (Some(v), _) => v.clone(),
                (None, Some(v)) => self.eval(v, d)?,
                (None, None) => Term::Undef,
            },
            Expr::Var(Key::Slot(off)) => {
                self.read(&Term::Const(self.rsp.wrapping_add_signed(*off) & low(w)), 8)?
            }
            Expr::Var(Key::Global(at, bits)) => {
                if tls_slot(*at).is_some() {
                    return Err("a thread-local slot");
                }
                self.read(&Term::Const(*at), u64::from(*bits / 8))?
            }
            Expr::Var(Key::Param(_) | Key::A64(_)) | Expr::Str(_) => Term::Undef,
            Expr::Sp(off) => Term::Const(self.rsp.wrapping_add_signed(*off) & low(w)),
            Expr::Bin(op, l, r) if op.is_float() => {
                let (Some(fl), Some(fr)) = (float_bits(l, temps), float_bits(r, temps)) else {
                    return Ok(Term::Undef);
                };
                term::float_bin(*op, fl, fr, &self.eval(l, d)?, &self.eval(r, d)?)
            }
            Expr::Bin(op, l, r) => term::bin(*op, w, &self.eval(l, d)?, &self.eval(r, d)?),
            Expr::Un(UnOp::Neg, inner) if float_bits(inner, temps).is_some() => {
                let fb = float_bits(inner, temps).unwrap_or(64);
                term::logic(
                    Logic::Xor,
                    64,
                    vec![
                        self.eval(inner, d)?,
                        Term::Const(1u64 << (u32::from(fb) - 1)),
                    ],
                )
            }
            Expr::Un(op @ (UnOp::Sqrt | UnOp::Fabs), inner)
                if float_bits(inner, temps).is_some() =>
            {
                term::float_unary(
                    *op,
                    float_bits(inner, temps).unwrap_or(64),
                    &self.eval(inner, d)?,
                )
            }
            Expr::Un(UnOp::Sqrt | UnOp::Fabs, _) => Term::Undef,
            Expr::Un(op, inner) => term::un(*op, op_width(*op, inner, w), &self.eval(inner, d)?),
            Expr::Deref(addr, ty) => {
                let at = narrow(&self.eval(addr, d)?, w);
                self.read(&at, u64::from(ty.bits() / 8))?
            }
            Expr::Cond(c) => truth(self.cond(c, d)?),
            Expr::Ternary(c, a, b) => ite(self.cond(c, d)?, self.eval(a, d)?, self.eval(b, d)?),
            Expr::Sext(inner, bits) => term::sign_extend(&self.eval(inner, d)?, *bits),
            Expr::Cast(inner, ty) if ty.bits() <= 64 && !matches!(ty, Ty::F32 | Ty::F64) => {
                let v = self.eval(inner, d)?;
                match float_bits(inner, temps) {
                    Some(fb) => term::to_int(fb, ty.bits(), &v),
                    None => narrow(&v, ty.bits()),
                }
            }
            Expr::Cast(..) => return Err("a float conversion"),
            Expr::Helper(..) | Expr::Call(..) => return Err("a helper"),
        })
    }

    /// Decides a lifted condition over the block's starting state, as
    /// [`super::super::verify::eval_cond`] does with bits.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    /// * `d` - How much deeper to look.
    ///
    /// # Errors
    ///
    /// A condition outside what the proof models.
    fn cond(&self, c: &Cond, d: u8) -> Result<Pred, Why> {
        let temps = Some(self.temps);
        if let Flags::Float(a, b, fb) = &c.flags {
            return Ok(float_pred(
                c.cc.0,
                *fb,
                &self.eval(a, d)?,
                &self.eval(b, d)?,
            ));
        }
        if let Flags::Cmp(a, b, _) = &c.flags
            && let Some(fb) = float_bits(a, temps).or_else(|| float_bits(b, temps))
        {
            return Ok(float_pred(c.cc.0, fb, &self.eval(a, d)?, &self.eval(b, d)?));
        }
        if let Flags::Cmp(a, b, w) = &c.flags
            && matches!(w, 32 | 64)
        {
            match self.floats {
                Some(true) => {
                    return Ok(float_pred(c.cc.0, *w, &self.eval(a, d)?, &self.eval(b, d)?));
                }
                None => return Err(MIXED),
                Some(false) => {}
            }
        }
        let k = |e: &Expr| self.eval(e, d);
        let flags = match &c.flags {
            Flags::Cmp(a, b, w) => Flagged::Cmp(k(a)?, k(b)?, *w),
            Flags::Float(..) | Flags::Unknown => return Ok(Pred::Undef),
            Flags::Test(a, b, w) => Flagged::Test(k(a)?, k(b)?, *w),
            Flags::Result(a, w) => Flagged::Result(k(a)?, *w),
            Flags::Add(a, b, w) => Flagged::Add(k(a)?, k(b)?, *w),
            Flags::Carry(a) => Flagged::Carry(k(a)?),
            Flags::Shift(a, w, b) => Flagged::Shift(k(a)?, *w, k(b)?),
            Flags::Truth(a, cc) => Flagged::Truth(k(a)?, *cc),
        };
        flags_pred(c.cc, flags)
    }
}

/// The machine where a block's run stops, from the lifter's semantics.
#[derive(Debug)]
struct Machine {
    /// Each general register's value, with the low bits of it the lift
    /// states; the bits above are the machine's own.
    regs: FxHashMap<Key, (Term, u8)>,
    /// The stack pointer.
    sp: u64,
    /// Memory beyond what it held before the block: the starting overlay
    /// and the block's writes.
    mem: BTreeMap<u64, Byte>,
    /// The bytes the block wrote.
    written: BTreeSet<u64>,
    /// Whether the block's conditional branch is taken.
    taken: Option<Pred>,
    /// Vector registers the block's instructions write.
    vectors: bool,
    /// The frame bytes the text holds no value for.
    lost: BTreeSet<u64>,
}

impl Machine {
    /// Returns a byte as the machine holds it.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn byte(&self, at: u64) -> Byte {
        self.mem.get(&at).cloned().unwrap_or(Byte::Was(at))
    }

    /// Reads `n` bytes, at most eight, little-endian
    /// ([`super::machine_word`]).
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes.
    /// * `width` - The register width.
    ///
    /// # Errors
    ///
    /// A read through an address the state picks after a write.
    fn word(&self, at: &Term, n: u64, width: u8) -> Result<Term, Why> {
        let mask = low(width);
        match at {
            Term::Const(a) => {
                let bytes: Vec<Byte> = (0..n.min(8))
                    .map(|i| self.byte(a.wrapping_add(i) & mask))
                    .collect();
                Ok(assemble(&bytes, mask))
            }
            Term::Undef => Ok(Term::Undef),
            a => Ok(Term::Mem(
                Box::new(narrow(a, width)),
                u8::try_from(n.min(8)).unwrap_or(8),
                overrides(&self.mem, &self.lost)?,
            )),
        }
    }

    /// Returns a register's value in its own lane
    /// ([`super::reg_value`]).
    ///
    /// # Arguments
    ///
    /// * `r` - Any general register, or the stack pointer.
    /// * `width` - The register width.
    ///
    /// # Errors
    ///
    /// A lane wider than the lift states.
    fn reg(&self, r: Register, width: u8) -> Result<Term, Why> {
        let full = if width == 32 {
            r.full_register32()
        } else {
            r.full_register()
        };
        if matches!(full, Register::RSP | Register::ESP) {
            return Ok(Term::Const(self.sp));
        }
        let (v, known) = self
            .regs
            .get(&Key::Reg(full))
            .ok_or("a register no lane holds")?;
        let high = matches!(r, Register::AH | Register::CH | Register::DH | Register::BH);
        let bits = u8::try_from(r.size() * 8).map_err(|_| "a register's size")?;
        if bits + if high { 8 } else { 0 } > *known {
            return Err("a register lane the lift does not state");
        }
        let v = if high {
            term::bin(Op::Shr, 64, v, &Term::Const(8))
        } else {
            v.clone()
        };
        Ok(narrow(&v, bits))
    }

    /// The value of an instruction's first operand ([`super::operand`]).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `width` - The register width.
    ///
    /// # Returns
    ///
    /// The value, `None` where the replay compares nothing.
    ///
    /// # Errors
    ///
    /// What [`Machine::reg`] and [`Machine::word`] refuse.
    fn operand(&self, i: &Instruction, width: u8) -> Result<Option<Term>, Why> {
        Ok(Some(match i.op0_kind() {
            OpKind::Register => self.reg(i.op0_register(), width)?,
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
                Term::Const(i.near_branch_target())
            }
            OpKind::Memory => {
                if matches!(i.memory_segment(), Register::FS | Register::GS) {
                    return Ok(None);
                }
                let base = i.memory_base();
                let mut at = Term::Const(i.memory_displacement64());
                if !matches!(base, Register::RIP | Register::EIP) {
                    if base != Register::None {
                        at = term::add(64, &at, &self.reg(base, width)?);
                    }
                    if i.memory_index() != Register::None {
                        let index = self.reg(i.memory_index(), width)?;
                        let scaled =
                            term::mul(64, &index, &Term::Const(u64::from(i.memory_index_scale())));
                        at = term::add(64, &at, &scaled);
                    }
                }
                self.word(&at, from_usize(i.memory_size().size()), width)?
            }
            OpKind::FarBranch16
            | OpKind::FarBranch32
            | OpKind::Immediate8
            | OpKind::Immediate8_2nd
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate64
            | OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate32to64
            | OpKind::MemorySegSI
            | OpKind::MemorySegESI
            | OpKind::MemorySegRSI
            | OpKind::MemorySegDI
            | OpKind::MemorySegEDI
            | OpKind::MemorySegRDI
            | OpKind::MemoryESDI
            | OpKind::MemoryESEDI
            | OpKind::MemoryESRDI => return Ok(None),
        }))
    }
}

/// One claim as two terms: what the text says and what the machine holds,
/// compared in the low bits.
#[derive(Debug)]
struct Claimed {
    /// The text's side.
    text: Term,
    /// The machine's side.
    machine: Term,
    /// The width compared.
    bits: u8,
}

/// Looks for a state in which two terms differ in their low bits.
///
/// The variables start next to the constants the terms are built with,
/// at zero, one and the signed and unsigned limits, or at random.
///
/// # Arguments
///
/// * `c` - The claim.
/// * `width` - The register width.
///
/// # Returns
///
/// The variables' values in such a state, if one is found.
fn search(c: &Claimed, width: u8) -> Option<FxHashMap<Key, u64>> {
    let mut inputs = BTreeMap::new();
    c.text.inputs(&mut inputs);
    c.machine.inputs(&mut inputs);
    let mut consts = Vec::new();
    c.text.constants(&mut consts);
    c.machine.constants(&mut consts);
    let mut near: Vec<u64> = vec![0, 1, u64::MAX, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff];
    for k in consts {
        near.extend([k, k.wrapping_add(1), k.wrapping_sub(1), k.wrapping_neg()]);
    }
    near.sort_unstable();
    near.dedup();
    let len = from_usize(near.len()).max(1);
    for p in 0..SEARCH_POINTS {
        let ins: FxHashMap<Key, u64> = inputs
            .iter()
            .zip(0u64..)
            .map(|((k, bits), j)| {
                let h = splitmix(p.wrapping_mul(0x9e37) ^ j.rotate_left(17));
                let v = if p > 0 && h & 3 == 0 {
                    h
                } else {
                    near[usize::try_from((h >> 2) % len).unwrap_or(0)]
                };
                let lift = SIGNS[usize::try_from((h >> 3) % from_usize(SIGNS.len())).unwrap_or(0)];
                (*k, v.wrapping_add(lift) & low(*bits))
            })
            .collect();
        let at = Point {
            ins: &ins,
            seed: splitmix(p),
            width,
        };
        if let (Some(x), Some(y)) = (term::value(&c.text, &at), term::value(&c.machine, &at))
            && (x ^ y) & low(c.bits) != 0
        {
            return Some(ins);
        }
    }
    None
}

/// Mixes bits for the search's draws.
///
/// # Arguments
///
/// * `x` - The input.
fn splitmix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

/// Decides a block from its claims.
///
/// # Arguments
///
/// * `claims` - Every claim the block makes.
/// * `width` - The register width.
fn decide(claims: &[Claimed], width: u8) -> Proof {
    let mut lacking = false;
    let mut differ: Vec<Claimed> = Vec::new();
    for c in claims {
        let (t, m) = (narrow(&c.text, c.bits), narrow(&c.machine, c.bits));
        if t == m || t == Term::Undef {
            continue;
        }
        if m.lacks() {
            lacking = true;
            continue;
        }
        differ.push(Claimed {
            text: t,
            machine: m,
            bits: c.bits,
        });
    }
    if !differ.is_empty() {
        let found: Vec<FxHashMap<Key, u64>> = differ
            .iter()
            .take(SEARCHED_CLAIMS)
            .filter_map(|c| search(c, width))
            .collect();
        return if found.is_empty() {
            Proof::Unknown("a claim whose two sides the normal form does not equate")
        } else {
            Proof::Differ(found)
        };
    }
    if lacking {
        return Proof::Unknown("a value the lift does not state");
    }
    Proof::Proved
}

impl<'p, L: Replay> Function<'_, 'p, L> {
    /// Proves a block's claims over every state.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `block` - The block.
    /// * `written` - The bytes a sampled run of the block wrote, which the
    ///   lifter's writes must name exactly.
    ///
    /// # Returns
    ///
    /// Proved, the states that may refute a claim, or why the block is
    /// left to the samples.
    pub(super) fn prove(&self, b: usize, block: &BasicBlock, written: &FxHashSet<u64>) -> Proof {
        match self.prove_or(b, block, written) {
            Ok(p) => p,
            Err(why) => Proof::Unknown(why),
        }
    }

    /// [`Function::prove`] with what it leaves to the samples as an error.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `block` - The block.
    /// * `observed` - The bytes a sampled run wrote.
    ///
    /// # Errors
    ///
    /// Why the block is left to the samples.
    #[expect(
        clippy::too_many_lines,
        reason = "one block's claims, built in the order the replay compares them"
    )]
    fn prove_or(
        &self,
        b: usize,
        block: &BasicBlock,
        observed: &FxHashSet<u64>,
    ) -> Result<Proof, Why> {
        let Code::X86(all) = &self.w.code else {
            return Err("an arm64 block");
        };
        let code = all.get(b).ok_or("no instructions")?;
        let w = self.w;
        let width = self.width;
        let mask = low(width);
        let inn = w.ins.get(b).ok_or("no witness")?;
        let effects = self.effects.get(b).ok_or("no effects")?;
        if code.iter().any(|i| {
            matches!(
                i.mnemonic(),
                crate::isa::x86::Mnemonic::Bsf | crate::isa::x86::Mnemonic::Bsr
            )
        }) {
            return Err("a bit scan");
        }
        if <super::super::arch::X86 as Replay>::whole_lanes(code) {
            return Err("whole vector lanes");
        }
        if code.iter().any(|i| statement_only(i) || aligns_stack(i)) {
            return Err("an instruction the lifter writes as a statement");
        }
        if w.seh_frame && code.iter().any(|i| try_level_store(i, u32::from(width))) {
            return Err("a try level the text leaves out");
        }
        let end = End::of::<super::super::arch::X86>(code)?;
        let sp = inn.sp.ok_or("the stack pointer unknown")?;
        let rsp = self
            .template
            .register(<L::Rig<'p> as Bench>::SP)
            .ok_or("no stack pointer")?;
        let sp0 = rsp.wrapping_sub(sp.cast_unsigned()) & mask;

        let mut base: BTreeMap<u64, Byte> = BTreeMap::new();
        let assumed = w.assumes.get(b).copied().flatten();
        if let Some((k @ (Key::Slot(_) | Key::Global(..)), c)) = assumed {
            let (at, n) = match k {
                Key::Slot(o) => (
                    sp0.wrapping_add_signed(o),
                    u64::from(inn.slot_bits.get(&o).copied().unwrap_or(width) / 8),
                ),
                Key::Global(a, bits) => (a, u64::from(bits / 8).max(1)),
                Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => (0, 0),
            };
            for i in 0..n.min(8) {
                base.insert(
                    at.wrapping_add(i) & mask,
                    Byte::Of(Term::Const(c), u8::try_from(i).unwrap_or(0)),
                );
            }
        }
        let mut entry: FxHashMap<Key, Term> = FxHashMap::default();
        let narrowed = |entry: &mut FxHashMap<Key, Term>, k: Key, nb: u8| {
            let bits = if let Some(Term::In(_, b)) = entry.get(&k) {
                *b
            } else {
                width
            };
            entry.insert(k, Term::In(k, bits.min(nb).min(width)));
        };
        for &(_, k) in &self.regs {
            if !inn.vals.contains_key(&k)
                && let Some(nb) = inn.narrow.get(&k)
            {
                narrowed(&mut entry, k, *nb);
            }
        }
        for (k, e) in &inn.vals {
            if let (
                Expr::Var(src @ (Key::Reg(_) | Key::A64(_) | Key::Tmp(_) | Key::Param(_))),
                Some(nb),
            ) = (e, inn.narrow.get(k))
            {
                if matches!(src, Key::Reg(Register::RSP | Register::ESP)) {
                    return Err("a pending copy of the stack pointer");
                }
                narrowed(&mut entry, *src, *nb);
            }
        }
        if let Some((k @ (Key::Reg(_) | Key::A64(_) | Key::Tmp(_) | Key::Param(_)), c)) = assumed {
            entry.insert(k, Term::Const(c & mask));
        }
        let mut text = Sym {
            width,
            sp0,
            start: rsp,
            rsp,
            entry,
            vars: FxHashMap::default(),
            unknown: BTreeSet::new(),
            mem: BTreeMap::new(),
            base: &base,
            lost: BTreeSet::new(),
            lost_all: false,
            names: BTreeMap::new(),
            slot_bits: &w.slot_bits,
            reg_ty: &w.reg_ty,
            result_ty: self.entry_result_ty(b),
            at: block.start,
            setters: <super::super::arch::X86 as Replay>::flag_setters(code),
        };

        let mut regs: FxHashMap<Key, Term> = FxHashMap::default();
        for &(_, k) in &self.regs {
            let v = match inn.vals.get(&k) {
                Some(e) => narrow(
                    &text.eval(e, EVAL_DEPTH)?,
                    inn.narrow.get(&k).copied().unwrap_or(64),
                ),
                None => text.var(k)?,
            };
            regs.insert(k, narrow(&v, width));
        }
        for &k in &self.vectors {
            let v = match inn.vals.get(&k) {
                None => text.var(k)?,
                Some(Expr::Call(..) | Expr::Deref(_, Ty::U128)) => {
                    return Err("a whole vector lane pending");
                }
                Some(e) => text.eval(e, EVAL_DEPTH)?,
            };
            regs.insert(k, v);
        }
        let mut overlay = base.clone();
        let mut pending: BTreeSet<u64> = BTreeSet::new();
        for (k, e) in &inn.vals {
            let (at, n) = match k {
                Key::Slot(o) => match inn.slot_bits.get(o) {
                    Some(bits) => (sp0.wrapping_add_signed(*o), u64::from(*bits / 8).max(1)),
                    None => continue,
                },
                Key::Global(a, bits) if *a < TLS_BASE => (*a, u64::from(*bits / 8).max(1)),
                Key::Global(..) | Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => {
                    continue;
                }
            };
            let value = text.wide(e, n)?;
            for i in 0..n {
                let a = at.wrapping_add(i) & mask;
                pending.insert(a);
                if value == Term::Undef {
                    text.lost.insert(a);
                } else {
                    overlay.insert(a, Byte::Of(value.clone(), u8::try_from(i).unwrap_or(0)));
                }
            }
        }

        let defs = w.defs.get(b);
        for &x in observed {
            let off = x.wrapping_sub(sp0).cast_signed();
            let frame = (x.wrapping_sub(rsp).wrapping_add(FRAME_SPAN) & mask) < 2 * FRAME_SPAN;
            if frame
                && !pending.contains(&x)
                && defs.is_none_or(|d| covering(d, off).next().is_none())
            {
                text.lost.insert(x);
            }
        }
        let machine = self.machine(code, end, rsp, &regs, &overlay, &text.lost)?;
        let modeled: FxHashSet<u64> = machine.written.iter().copied().collect();
        if modeled != *observed {
            return Err("writes the lift does not name");
        }
        text.rsp = machine.sp;

        let mut claims: Vec<Claimed> = Vec::new();
        let mut called = false;
        let mut settled = false;
        let mut texted_vectors = false;
        for e in effects {
            text.at = e.at;
            match &e.kind {
                EffectKind::Assign(k, v, bits) => {
                    if matches!(k, Key::Reg(r) if r.is_xmm()) {
                        texted_vectors = true;
                    }
                    text.assign(*k, v, *bits)?;
                }
                EffectKind::Store(s) => text.store(&s.0, s.1, &s.2)?,
                EffectKind::Call(c) => {
                    if matches!(c.callee, Callee::Builtin(..)) {
                        return Err("a library routine for a string instruction");
                    }
                    let Some(instr) = end.last() else { continue };
                    if let Callee::Through(target) = &c.callee
                        && let Some(m) = machine.operand(&instr, width)?
                    {
                        let m = match (&m, w.dispatches.is_empty()) {
                            (_, true) => m,
                            (Term::Const(to), false) => match w.dispatches.get(to) {
                                Some(r) => machine.reg(*r, width)?,
                                None => m,
                            },
                            (_, false) => return Err("a call that may go through a thunk"),
                        };
                        claims.push(Claimed {
                            text: text.eval(target, EVAL_DEPTH)?,
                            machine: m,
                            bits: width,
                        });
                    }
                    for (at, arg) in &c.args {
                        let (m, stored) = match at {
                            ArgAt::Stack(off, bits) => (
                                machine.word(
                                    &Term::Const(machine.sp.wrapping_add_signed(*off)),
                                    u64::from(width / 8),
                                    width,
                                )?,
                                *bits,
                            ),
                            ArgAt::Reg(r) if r.is_gpr() => (machine.reg(*r, width)?, 64),
                            ArgAt::Reg(_) | ArgAt::Operand | ArgAt::A64(_) => continue,
                        };
                        claims.push(Claimed {
                            text: text.eval(arg, EVAL_DEPTH)?,
                            machine: m,
                            bits: value_lane(arg, width).min(stored.max(8)),
                        });
                    }
                    self.memory_claims(&text, &machine, None, &pending, &mut claims);
                    settled = true;
                    called = true;
                    text.lost_all = true;
                    for k in &self.volatile {
                        text.unknown.insert(*k);
                    }
                    text.unknown.extend(c.result);
                    text.unknown.extend(c.result2);
                }
                EffectKind::Return(v) => {
                    if v.is_some() && w.ret_xmm {
                        return Err("a float return");
                    }
                    if let Some(v) = v
                        && !w.ret_float
                    {
                        let bits = if matches!(w.ret_bits, 8 | 16 | 32) {
                            w.ret_bits
                        } else {
                            width
                        }
                        .min(value_lane(v, width));
                        let first = self.regs.first().map(|(_, k)| *k).ok_or("no registers")?;
                        claims.push(Claimed {
                            text: text.eval(v, EVAL_DEPTH)?,
                            machine: full(&machine, first, bits)?,
                            bits,
                        });
                    }
                    self.memory_claims(&text, &machine, None, &pending, &mut claims);
                    settled = true;
                }
                EffectKind::Branch(c) => {
                    let p = text.cond(c, EVAL_DEPTH)?;
                    if let Some(m) = &machine.taken {
                        claims.push(Claimed {
                            text: truth(p),
                            machine: truth(m.clone()),
                            bits: 1,
                        });
                    }
                }
                EffectKind::Switch(_) => return Err("a switch"),
                EffectKind::Jump(_) => return Err("a computed goto"),
                EffectKind::Unmodeled => return Err("a statement no effect models"),
            }
        }
        text.setters = (Vec::new(), Vec::new());
        called |= end
            .last()
            .is_some_and(|i| <super::super::arch::X86 as Replay>::transfer(&i) == Transfer::Call);
        if !called && !settled {
            self.memory_claims(&text, &machine, Some(b), &pending, &mut claims);
        }
        for &s in self.succs.get(b).map_or(&[][..], Vec::as_slice) {
            if w.processed.get(s).copied().unwrap_or(false) {
                let vectors = machine.vectors || texted_vectors;
                self.successor_claims(
                    &text,
                    &machine,
                    b,
                    s,
                    called,
                    vectors,
                    &pending,
                    &mut claims,
                )?;
            }
        }
        Ok(decide(&claims, width))
    }

    /// Runs a block through the lifter and reads where its run stops.
    ///
    /// The block is lifted whole first, the way the verifier lifts it. The
    /// lifter reads memory where each load sits, so a read of bytes the
    /// block also writes may have come before the write or after it; such
    /// a block is lifted again one instruction at a time, each from the
    /// state the ones before it left, where every read is of memory as it
    /// is then.
    ///
    /// # Arguments
    ///
    /// * `code` - The block's instructions.
    /// * `end` - How it ends.
    /// * `rsp` - The stack pointer where it starts.
    /// * `regs` - The registers' values where it starts.
    /// * `overlay` - The bytes memory holds where it starts beyond what it
    ///   held before.
    /// * `lost` - The frame bytes the text holds no value for.
    ///
    /// # Errors
    ///
    /// A block or a value outside what the proof models.
    fn machine(
        &self,
        code: &[Instruction],
        end: End<Instruction>,
        rsp: u64,
        regs: &FxHashMap<Key, Term>,
        overlay: &BTreeMap<u64, Byte>,
        lost: &BTreeSet<u64>,
    ) -> Result<Machine, Why> {
        let branches = match end {
            End::Branch(jcc) => matches!(
                <super::super::arch::X86 as Replay>::transfer(&jcc),
                Transfer::Branch { target, next } if target != next
            ),
            End::Before(_) | End::Fall(_) => false,
        };
        let lifted_code: &[Instruction] = match end {
            End::Branch(_) if branches => code,
            End::Branch(_) | End::Before(_) => {
                code.get(..code.len().saturating_sub(1)).unwrap_or(&[])
            }
            End::Fall(_) => code,
        };
        let start = Run {
            regs: regs.clone(),
            known: FxHashMap::default(),
            sp: rsp,
            mem: overlay.clone(),
            written: BTreeSet::new(),
            flags: None,
            vectors: false,
            taken: None,
            fresh: FRESH_FIRST,
            lost: lost.clone(),
        };
        let mut run = start.clone();
        match self.step(lifted_code, &mut run, true, branches) {
            Ok(()) => {}
            Err(why) if why == STALE || why == BESIDE => {
                run = start;
                let last = lifted_code.len().saturating_sub(1);
                for (n, i) in lifted_code.iter().enumerate() {
                    self.step(
                        std::slice::from_ref(i),
                        &mut run,
                        false,
                        branches && n == last,
                    )?;
                }
            }
            Err(why) => return Err(why),
        }
        if branches && run.taken.is_none() {
            return Err("a branch the lift has no condition for");
        }
        let regs = self
            .regs
            .iter()
            .map(|&(_, k)| {
                let v = run.regs.get(&k).cloned().unwrap_or(Term::Undef);
                (k, (v, run.known.get(&k).copied().unwrap_or(64)))
            })
            .collect();
        Ok(Machine {
            regs,
            sp: run.sp,
            mem: run.mem,
            written: run.written,
            taken: run.taken,
            vectors: run.vectors,
            lost: run.lost,
        })
    }

    /// Lifts some instructions from the state a run holds and moves the run
    /// past them.
    ///
    /// # Arguments
    ///
    /// * `code` - The instructions: the whole block, or one of them.
    /// * `run` - The machine's state before them, after them on return.
    /// * `whole` - They are more than one instruction: a read of bytes
    ///   they also write cannot be placed before or after the write.
    /// * `branches` - The block's conditional branch is among them.
    ///
    /// # Errors
    ///
    /// An instruction or a value outside what the proof models.
    #[expect(
        clippy::too_many_lines,
        reason = "the lift's registers, memory, flags and branch, read the way the verifier reads them"
    )]
    fn step(
        &self,
        code: &[Instruction],
        run: &mut Run,
        whole: bool,
        branches: bool,
    ) -> Result<(), Why> {
        let width = self.width;
        let mask = low(width);
        let mut entry = Env::entry();
        if let Some((shape, _)) = &run.flags {
            entry.flags = shape.clone();
        }
        let (env, probe, branch) = self.lift(code, entry, !whole)?;
        let written_regs: Vec<Register> = written_registers(code, width);
        let mut partial: BTreeSet<Register> = BTreeSet::new();
        let mut vectors: BTreeSet<Register> = BTreeSet::new();
        let mut info = InstructionInfoFactory::new();
        for i in code {
            for u in info.info(i).used_registers() {
                if matches!(
                    u.access(),
                    OpAccess::Read | OpAccess::CondRead | OpAccess::None | OpAccess::NoMemAccess
                ) {
                    continue;
                }
                let r = u.register();
                if r.is_xmm() || r.is_ymm() || r.is_zmm() {
                    vectors.insert(r.full_register());
                }
                if r.is_gpr() && r.size() < 4 {
                    partial.insert(if width == 32 {
                        r.full_register32()
                    } else {
                        r.full_register()
                    });
                }
            }
        }
        let held = run
            .flags
            .as_ref()
            .map(|(_, h)| h.clone())
            .unwrap_or_default();
        let none = BTreeSet::new();
        let first = Lifted {
            width,
            rsp: run.sp,
            regs: &run.regs,
            overlay: &run.mem,
            written: &none,
            temps: &probe.temps,
            held: &held,
            floats: {
                let setters = <super::super::arch::X86 as Replay>::flag_setters(code).0;
                match (setters.iter().any(|s| s.1), setters.iter().all(|s| s.1)) {
                    (true, true) => Some(true),
                    (false, _) => Some(false),
                    (true, false) => None,
                }
            },
            lost: &run.lost,
        };
        let mut spans: Vec<(u64, u64)> = Vec::new();
        for wrote in &probe.effects {
            match wrote {
                Wrote::Store { addr, ty, .. } => {
                    if matches!(ty, Ty::F32 | Ty::F64 | Ty::U128) {
                        return Err("a float or vector store");
                    }
                    let Term::Const(a) = narrow(&first.eval(addr, EVAL_DEPTH)?, width) else {
                        return Err("a store through an address the state picks");
                    };
                    if tls_slot(a).is_some() {
                        return Err("a thread-local store");
                    }
                    let n = u64::from(ty.bits() / 8).max(1);
                    if n.saturating_sub(1) > mask - (a & mask) || n > from_usize(REGION_MAX) {
                        return Err("a store past the top of memory");
                    }
                    spans.push((a, n));
                }
                Wrote::Rep { .. } => return Err("a repeated string instruction"),
                Wrote::Asm => return Err("an instruction left as asm"),
            }
        }
        let slots: Vec<(u64, u64, i64)> = env
            .slot_bits
            .iter()
            .map(|(&o, &bits)| {
                (
                    run.sp.wrapping_add_signed(o) & mask,
                    u64::from(bits / 8).max(1),
                    o,
                )
            })
            .collect();
        let covers = |(a, n): (u64, u64), x: u64| x.wrapping_sub(a) & mask < n;
        let mut written: BTreeSet<u64> = BTreeSet::new();
        for &(a, n) in &spans {
            for i in 0..n {
                let x = a.wrapping_add(i) & mask;
                if slots.iter().any(|&(s, sn, _)| covers((s, sn), x)) {
                    return Err("a store under a slot the lift holds");
                }
                written.insert(x);
            }
        }
        for &(a, n, _) in &slots {
            if n > 8 {
                return Err("a vector slot");
            }
            written.extend((0..n).map(|i| a.wrapping_add(i) & mask));
        }
        let lifted = Lifted {
            written: if whole { &written } else { &none },
            ..first
        };
        let mut bytes: Vec<(u64, Byte)> = Vec::new();
        for (wrote, &(a, n)) in probe.effects.iter().zip(&spans) {
            let Wrote::Store { addr, value, .. } = wrote else {
                continue;
            };
            lifted.eval(addr, EVAL_DEPTH)?;
            let v = lifted.eval(value, EVAL_DEPTH)?;
            for i in 0..n {
                bytes.push((
                    a.wrapping_add(i) & mask,
                    Byte::Of(v.clone(), u8::try_from(i).unwrap_or(0)),
                ));
            }
        }
        for &(a, n, o) in &slots {
            let bits = u8::try_from(n * 8).unwrap_or(64);
            let v = match env.vals.get(&Key::Slot(o)) {
                Some(e) => {
                    if float_bits(e, Some(&probe.temps)).is_some_and(|fb| fb != bits) {
                        return Err("a float a slot converts");
                    }
                    narrow(&lifted.eval(e, EVAL_DEPTH)?, bits)
                }
                None => Term::Undef,
            };
            for i in 0..n {
                let byte = match &v {
                    Term::Undef => Byte::Lost,
                    v => Byte::Of(v.clone(), u8::try_from(i).unwrap_or(0)),
                };
                bytes.push((a.wrapping_add(i) & mask, byte));
            }
        }
        let mut regs: Vec<(Key, Term, u8)> = Vec::new();
        for &(_, k) in &self.regs {
            let Key::Reg(reg) = k else { continue };
            let lane = env.narrow.get(&k).copied().unwrap_or(64);
            let was = written_regs.contains(&reg);
            let before = run.regs.get(&k).cloned().unwrap_or(Term::Undef);
            let (v, bits) = match env.vals.get(&k) {
                None if was && lane != 32 => (Term::Undef, 0),
                None if was => (before, 32),
                None => continue,
                Some(e) => {
                    let v = lifted.eval(e, EVAL_DEPTH)?;
                    if lane < 32 && !partial.contains(&reg) && v.fits() <= lane {
                        (v, 64)
                    } else {
                        (v, lane.clamp(8, 64))
                    }
                }
            };
            let (v, known) = if width == 64 && bits == 32 {
                (narrow(&v, 32), 64)
            } else {
                (v, bits)
            };
            regs.push((k, v, known));
        }
        let mut xmms: Vec<(Key, Option<Term>)> = Vec::new();
        for &k in &self.vectors {
            let Key::Reg(reg) = k else { continue };
            match env.vals.get(&k) {
                Some(e) => xmms.push((k, Some(lifted.eval(e, EVAL_DEPTH)?))),
                None if vectors.contains(&reg.full_register()) => xmms.push((k, None)),
                None => {}
            }
        }
        let sp = match (env.sp, env.vals.get(&Key::Reg(Register::RSP))) {
            (Some(o), _) => run.sp.wrapping_add_signed(o) & mask,
            (None, Some(e)) => {
                let Term::Const(v) = narrow(&lifted.eval(e, EVAL_DEPTH)?, width) else {
                    return Err("the stack pointer unknown where the block ends");
                };
                v
            }
            (None, None) => return Err("the stack pointer unknown where the block ends"),
        };
        let flags = if code.iter().any(|i| i.rflags_modified() != 0) {
            hold_flags(&env.flags, &lifted)?
        } else {
            run.flags.clone()
        };
        let taken = match (branches, branch) {
            (true, Some(c)) => Some(lifted.cond(&c, EVAL_DEPTH)?),
            (true, None) => return Err("a branch the lift has no condition for"),
            (false, _) => None,
        };
        for (a, byte) in bytes {
            run.mem.insert(a, byte);
        }
        run.written.extend(written);
        for (k, v, known) in regs {
            let full = if known >= width {
                v
            } else {
                run.fresh = run.fresh.wrapping_sub(1);
                let upper = Term::In(Key::Tmp(run.fresh), width - known);
                if known == 0 || v == Term::Undef {
                    upper
                } else {
                    let shifted = term::mul(64, &upper, &Term::Const(1u64 << known));
                    term::add(64, &narrow(&v, known), &shifted)
                }
            };
            run.regs.insert(k, full);
            run.known.insert(k, known);
        }
        for (k, v) in xmms {
            let v = v.unwrap_or_else(|| {
                run.fresh = run.fresh.wrapping_sub(1);
                Term::In(Key::Tmp(run.fresh), 64)
            });
            run.regs.insert(k, v);
        }
        run.vectors |= !vectors.is_empty();
        run.sp = sp;
        run.flags = flags;
        if taken.is_some() {
            run.taken = taken;
        }
        Ok(())
    }

    /// Lifts instructions symbolically from a neutral state, as the
    /// verifier does.
    ///
    /// # Arguments
    ///
    /// * `code` - The instructions, the conditional branch last if any.
    /// * `env` - The state they start from: every variable its own value,
    ///   the flags those an earlier instruction left.
    /// * `flags_out` - Keep the flags they leave, for the next.
    ///
    /// # Returns
    ///
    /// The environment where they end, the memory writes and temporaries
    /// recorded, and the branch's condition.
    ///
    /// # Errors
    ///
    /// An instruction the lifter leaves as asm.
    fn lift(
        &self,
        code: &[Instruction],
        mut env: Env,
        flags_out: bool,
    ) -> Result<(Env, Probe, Option<Cond>), Why> {
        let mut slot = self.lifting.borrow_mut();
        if slot.is_none() {
            let f = self.analysis.function(self.entry).ok_or("no function")?;
            let starts = f.blocks.iter().map(|b| b.start).collect();
            let mut ctx = new_ctx(
                self.program,
                self.analysis,
                self.overlay,
                f,
                u32::from(self.width),
                starts,
                &[],
            );
            ctx.symbolic_only = true;
            ctx.flag_readers = vec![false; f.blocks.len()];
            ctx.rebase_flags = vec![None; f.blocks.len()];
            *slot = Some(ctx);
        }
        let ctx: &mut Ctx<'_> = slot.as_mut().ok_or("no lifter")?;
        ctx.probe = Some(Probe::default());
        let out = exec_block(
            ctx,
            code,
            None,
            &mut env,
            Pass::Dataflow,
            None,
            BlockFacts {
                flags_out,
                ..BlockFacts::default()
            },
        );
        let probe = ctx.probe.take().unwrap_or_default();
        if out.unmodeled > 0 {
            return Err("an instruction the lifter leaves as asm");
        }
        Ok((env, probe, out.branch.map(|br| br.cond)))
    }

    /// Adds the claims of a memory compare off the frame
    /// ([`Function::memory`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The text's state.
    /// * `machine` - The machine's.
    /// * `b` - The block's index, whose successors' pending globals are
    ///   left out; `None` at a call or a return.
    /// * `pending` - The bytes pending at the block's start.
    /// * `claims` - Where the claims go.
    fn memory_claims(
        &self,
        text: &Sym<'_>,
        machine: &Machine,
        b: Option<usize>,
        pending: &BTreeSet<u64>,
        claims: &mut Vec<Claimed>,
    ) {
        let mask = low(self.width);
        if text.lost_all || machine.written.iter().any(|x| *x > mask) {
            return;
        }
        let frame = |x: u64| {
            [text.start, machine.sp, text.sp0]
                .iter()
                .any(|sp| (x.wrapping_sub(*sp).wrapping_add(FRAME_SPAN) & mask) < 2 * FRAME_SPAN)
        };
        let mut kept: BTreeSet<u64> = BTreeSet::new();
        for &s in b
            .and_then(|b| self.succs.get(b))
            .map_or(&[][..], Vec::as_slice)
        {
            for k in self
                .w
                .ins
                .get(s)
                .map_or(&BTreeMap::new(), |e| &e.vals)
                .keys()
            {
                if let Key::Global(a, bits) = *k {
                    kept.extend((0..u64::from(bits / 8).max(1)).map(|i| a.wrapping_add(i) & mask));
                }
            }
        }
        let addrs: BTreeSet<u64> = machine
            .written
            .iter()
            .chain(text.mem.keys())
            .chain(pending.iter())
            .copied()
            .filter(|x| !frame(*x) && !kept.contains(x) && !text.lost.contains(x))
            .collect();
        for x in addrs {
            claims.push(Claimed {
                text: byte_value(&text.byte(x)),
                machine: byte_value(&machine.byte(x)),
                bits: 8,
            });
        }
    }

    /// Adds the claims of the relation at a successor
    /// ([`Function::successor`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The text's state at the block's end.
    /// * `machine` - The machine's.
    /// * `b` - The block's index.
    /// * `s` - The successor's index.
    /// * `called` - The block made a call.
    /// * `vectors` - Some vector register changed on either side.
    /// * `pending` - The bytes pending at the block's start.
    /// * `claims` - Where the claims go.
    ///
    /// # Errors
    ///
    /// A claim outside what the proof models.
    #[expect(
        clippy::too_many_arguments,
        reason = "one edge's facts, threaded through"
    )]
    fn successor_claims(
        &self,
        text: &Sym<'_>,
        machine: &Machine,
        b: usize,
        s: usize,
        called: bool,
        vectors: bool,
        pending: &BTreeSet<u64>,
        claims: &mut Vec<Claimed>,
    ) -> Result<(), Why> {
        let w = self.w;
        let width = self.width;
        let mask = low(width);
        let Some(sin) = w.ins.get(s) else {
            return Ok(());
        };
        let held = |k: Key| match sin.vals.get(&k) {
            Some(e) => text.eval(e, EVAL_DEPTH),
            None => text.var(k),
        };
        for &(_, k) in &self.regs {
            let Some(&need) = w.live.regs.get(s).and_then(|m| m.get(&k)) else {
                continue;
            };
            if called && self.volatile.contains(&k) {
                continue;
            }
            let t = held(k)?;
            let narrow_to = sin.narrow.get(&k).copied();
            let mut bits = need.min(width);
            if let Some(nb) = narrow_to {
                bits = bits.min(nb).max(8);
            }
            if let Some(nb) = narrow_to
                && nb < 32
                && !sin.vals.contains_key(&k)
            {
                claims.push(Claimed {
                    text: t.clone(),
                    machine: narrow(&t, nb),
                    bits: 64,
                });
            }
            claims.push(Claimed {
                text: t,
                machine: full(machine, k, bits)?,
                bits,
            });
        }
        for &k in &self.vectors {
            if w.live.regs.get(s).and_then(|m| m.get(&k)).is_none()
                || (called && self.volatile.contains(&k))
            {
                continue;
            }
            if vectors
                || sin.vals.contains_key(&k)
                || w.ins[b].vals.contains_key(&k)
                || text.vars.contains_key(&k)
            {
                return Err("a vector register a successor reads");
            }
        }
        if called || text.lost_all {
            return Ok(());
        }
        let mut covered: Vec<(u64, u64)> = Vec::new();
        for (k, e) in &sin.vals {
            let Key::Slot(o) = k else { continue };
            let Some(&bits) = sin.slot_bits.get(o) else {
                continue;
            };
            let a = text.sp0.wrapping_add_signed(*o) & mask;
            let n = u64::from(bits / 8).max(1);
            covered.push((a, n));
            if !w.live.is_live(s, *k) {
                continue;
            }
            if bits > 64 {
                return Err("a vector slot a successor reads");
            }
            claims.push(Claimed {
                text: text.eval(e, EVAL_DEPTH)?,
                machine: machine.word(&Term::Const(a), n, width)?,
                bits,
            });
        }
        let defs = w.defs.get(b);
        let defined = |off: i64| {
            defs.is_some_and(|d| covering(d, off).any(|d| w.live.is_live(s, Key::Slot(d))))
        };
        let next = self.effects.get(s).map_or(&[][..], Vec::as_slice);
        let inn = &w.ins[b];
        let sp0 = text.sp0;
        let pending_live = |x: u64| {
            inn.slot_bits.iter().any(|(&p, &bits)| {
                let lo = sp0.wrapping_add_signed(p) & mask;
                x.wrapping_sub(lo) & mask < u64::from(bits / 8).max(1)
                    && inn.vals.contains_key(&Key::Slot(p))
                    && w.live.is_live(s, Key::Slot(p))
            })
        };
        let floor = sin.sp.unwrap_or(i64::MIN);
        for (&o, &n) in self.named {
            if !w.live.is_live(s, Key::Slot(o)) {
                continue;
            }
            let a = sp0.wrapping_add_signed(o) & mask;
            let bytes: Vec<u64> = (0i64..)
                .zip(0..n)
                .map(|(i, _)| (o + i, a.wrapping_add_signed(i) & mask))
                .filter(|&(off, x)| {
                    let texted = text.mem.contains_key(&x)
                        || (pending.contains(&x)
                            && !overwritten_first(next, off)
                            && pending_live(x));
                    off >= floor
                        && (texted || (machine.written.contains(&x) && defined(off)))
                        && !covered
                            .iter()
                            .any(|&(c, len)| x.wrapping_sub(c) & mask < len)
                })
                .map(|(_, x)| x)
                .collect();
            if bytes.iter().any(|x| text.byte(*x) == Byte::Lost) {
                continue;
            }
            for &x in bytes.iter().take(8) {
                claims.push(Claimed {
                    text: byte_value(&text.byte(x)),
                    machine: byte_value(&machine.byte(x)),
                    bits: 8,
                });
            }
        }
        if let Some(ssp) = sin.sp {
            claims.push(Claimed {
                text: Term::Const(sp0.wrapping_add_signed(ssp) & mask),
                machine: Term::Const(machine.sp),
                bits: width,
            });
        }
        Ok(())
    }
}

/// A general register's whole value as the machine holds it, for a claim
/// in its low bits.
///
/// # Arguments
///
/// * `machine` - The machine.
/// * `k` - The register.
/// * `bits` - The bits the claim compares.
///
/// # Errors
///
/// A claim on bits the lift does not state.
fn full(machine: &Machine, k: Key, bits: u8) -> Result<Term, Why> {
    let (v, known) = machine.regs.get(&k).ok_or("a register no lane holds")?;
    if bits > *known {
        return Err("a register lane the lift does not state");
    }
    Ok(v.clone())
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Flagged, compare, flags_pred, float_pred};
    use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, float_cc};
    use crate::analysis::decompile::replay::term::{Point, Term, holds};
    use crate::analysis::decompile::verify::float_of;
    use crate::fxmap::FxHashMap;
    use crate::isa::x86::{ConditionCode, Register};

    /// Every condition code.
    const CODES: [ConditionCode; 17] = [
        ConditionCode::None,
        ConditionCode::o,
        ConditionCode::no,
        ConditionCode::b,
        ConditionCode::ae,
        ConditionCode::e,
        ConditionCode::ne,
        ConditionCode::be,
        ConditionCode::a,
        ConditionCode::s,
        ConditionCode::ns,
        ConditionCode::p,
        ConditionCode::np,
        ConditionCode::l,
        ConditionCode::ge,
        ConditionCode::le,
        ConditionCode::g,
    ];

    /// The variables the conditions compare.
    const KEYS: [Key; 2] = [Key::Reg(Register::RAX), Key::Reg(Register::RCX)];

    /// Values worth comparing: around zero, the sign bits and the limits.
    const EDGES: [u64; 12] = [
        0,
        1,
        2,
        0x7f,
        0x80,
        0xff,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        u64::MAX,
    ];

    /// A condition over symbolic flags holds exactly where the lifter's own
    /// condition logic says it does once the flags' operands are known,
    /// for every code, width and kind of flags the proof reads.
    #[test]
    fn a_condition_holds_where_the_lifter_s_logic_says() {
        let (x, y) = (Term::In(KEYS[0], 64), Term::In(KEYS[1], 64));
        for &cc in &CODES {
            for w in [8, 16, 32, 64] {
                for &a in &EDGES {
                    for &b in &EDGES {
                        let ins: FxHashMap<Key, u64> = KEYS.iter().copied().zip([a, b]).collect();
                        let at = Point {
                            ins: &ins,
                            seed: 1,
                            width: 64,
                        };
                        let (ca, cb) = (Expr::Const(a), Expr::Const(b));
                        let kinds = [
                            (
                                Flags::Cmp(ca.clone(), cb.clone(), w),
                                Flagged::Cmp(x.clone(), y.clone(), w),
                            ),
                            (
                                Flags::Test(ca.clone(), cb.clone(), w),
                                Flagged::Test(x.clone(), y.clone(), w),
                            ),
                            (Flags::Result(ca.clone(), w), Flagged::Result(x.clone(), w)),
                            (
                                Flags::Add(ca.clone(), cb.clone(), w),
                                Flagged::Add(x.clone(), y.clone(), w),
                            ),
                            (Flags::Carry(ca.clone()), Flagged::Carry(x.clone())),
                        ];
                        for (flags, flagged) in kinds {
                            let want = Cond { cc: Cc(cc), flags }.eval();
                            let Ok(p) = flags_pred(Cc(cc), flagged) else {
                                continue;
                            };
                            assert_eq!(holds(&p, &at), want, "{cc:?} w{w} {a:#x} {b:#x}: {p:?}");
                        }
                    }
                }
                let p = compare(cc, &x, &x, w);
                assert!(p.is_ok(), "{cc:?}");
            }
        }
    }

    /// A float compare's outcome set holds exactly where the machine's own
    /// float condition does, NaNs, zeros and infinities included.
    #[test]
    fn a_float_condition_holds_where_the_machine_s_does() {
        let floats = [
            0.0f64,
            -0.0,
            1.0,
            -1.0,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            f64::MIN_POSITIVE,
        ];
        let (x, y) = (Term::In(KEYS[0], 64), Term::In(KEYS[1], 64));
        for &cc in &CODES {
            for &a in &floats {
                for &b in &floats {
                    let (ba, bb) = (a.to_bits(), b.to_bits());
                    let ins: FxHashMap<Key, u64> = KEYS.iter().copied().zip([ba, bb]).collect();
                    let at = Point {
                        ins: &ins,
                        seed: 1,
                        width: 64,
                    };
                    let want = float_cc(cc, float_of(ba, 64), float_of(bb, 64));
                    let p = float_pred(cc, 64, &x, &y);
                    let got = holds(&p, &at);
                    match want {
                        Some(want) => assert_eq!(got, Some(want), "{cc:?} {a} {b}"),
                        None => assert_eq!(got, None, "{cc:?} {a} {b}"),
                    }
                }
            }
        }
    }
}
