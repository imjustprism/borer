//! Conditions whose outcome does not depend on what they read.
//!
//! An obfuscator inflates a function's control flow with branches that only
//! look like decisions: `(x * x + x) % 2 == 0` is true whatever `x` holds,
//! and `7 * y * y - 1 == z * z` is never true. Each one doubles a region's
//! block count and defeats structuring, so a reader sees ten times the flow
//! the program actually has.
//!
//! A condition is first evaluated over a fixed spread of inputs; one that
//! changes its answer is ordinary logic. One that never changes it is
//! proven constant only when its outcome depends on few enough low bits of
//! its variables ([`demand`]) that every value of those bits is tried, or
//! when the low bits of an equality's two sides never agree, which no
//! value can then make equal. Otherwise the samples are all there is: a
//! key check that fails one input in 4919 agrees on every sample, so such
//! a verdict says how many inputs it rests on and claims no dead branch.
//! The sample set is fixed, so the verdict is deterministic for a given
//! condition.

use std::collections::{BTreeMap, BTreeSet};

use super::expr::{Cc, Cond, Expr, Flags, Key, Op, fold};
use crate::isa::x86::ConditionCode;

/// Values a free variable is given, in this order, across the samples.
///
/// Chosen for the boundaries an arithmetic identity turns on: zero and one,
/// each width's largest value, each width's sign boundary, and two odd
/// values that are not near any of them.
const VALUES: [u64; 16] = [
    0,
    1,
    2,
    0x7f,
    0x80,
    0xff,
    0x7fff,
    0x8000,
    0xffff,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    0xffff_ffff_ffff_ffff,
    0x0123_4567_89ab_cdef,
];

/// Assignments tried before a condition is called constant.
const SAMPLES: usize = 64;

/// Most assignments tried, however many boundary values the pool gathered.
const SAMPLES_MAX: usize = 256;

/// Free variables a condition may hold and still be worth testing.
///
/// An opaque predicate is built from one or two values; a condition reading
/// more than this is ordinary program logic, and testing it costs more than
/// it can return.
const VARS_MAX: usize = 3;

/// Largest condition tested, in expression nodes.
const SIZE_MAX: usize = 24;

/// Most input bits a proof enumerates: every value of up to this many
/// bits, across all the condition's variables, is tried.
const PROOF_BITS: u32 = 12;

/// What a verdict that a condition never varies rests on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Evidence {
    /// Every value of the bits the outcome depends on was tried, or the
    /// low bits of an equality's sides never agree: the outcome is fixed.
    Proven,
    /// This many sampled assignments agreed; others may not.
    Sampled(usize),
}

/// What trying every value of the bits a condition depends on found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exhaustive {
    /// Every value gave this outcome.
    Always(bool),
    /// Two values gave different outcomes.
    Varies,
    /// The condition depends on too many bits, or on an operation whose low
    /// bits a higher operand bit reaches, to be enumerated.
    Unknown,
}

/// Returns the outcome a condition always produced, if it never varied,
/// with what that rests on.
///
/// # Arguments
///
/// * `cond` - The branch condition.
///
/// # Returns
///
/// `Some((outcome, evidence))` when every sampled assignment agreed and no
/// enumeration found one that disagrees, `None` when the condition varied,
/// when it reads memory or anything else the evaluator cannot give a value,
/// or when it is too large or reads too many variables to be an opaque
/// predicate.
pub(super) fn constant_outcome(cond: &Cond) -> Option<(bool, Evidence)> {
    if cond.size() > SIZE_MAX {
        return None;
    }
    if !computes(cond) {
        return None;
    }
    let mut vars = BTreeSet::new();
    match &cond.flags {
        Flags::Cmp(l, r, _)
        | Flags::Float(l, r, _)
        | Flags::Test(l, r, _)
        | Flags::Add(l, r, _) => {
            if reads_memory(l) || reads_memory(r) {
                return None;
            }
            collect(l, &mut vars);
            collect(r, &mut vars);
        }
        Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => {
            if reads_memory(e) {
                return None;
            }
            collect(e, &mut vars);
        }
        Flags::Shift(e, _, c) => {
            if reads_memory(e) || reads_memory(c) {
                return None;
            }
            collect(e, &mut vars);
            collect(c, &mut vars);
        }
        Flags::Unknown => return None,
    }
    if vars.is_empty() || vars.len() > VARS_MAX {
        return None;
    }
    let vars: Vec<Key> = vars.into_iter().collect();
    let pool = pool_for(cond);
    let samples = pool.len().clamp(SAMPLES, SAMPLES_MAX);
    let mut agreed: Option<bool> = None;
    for s in 0..samples {
        let mut c = cond.clone();
        // Every fourth sample gives all variables one value. Spreading them
        // apart on every sample means two variables never hold the same
        // thing, and `x != y` then looks like it can never be false.
        let together = s % 4 == 0;
        for (i, k) in vars.iter().enumerate() {
            // One variable walks the pool a step at a time, which reaches every
            // value it holds; a stride can miss some whenever it shares a factor
            // with the size. The others take an offset that changes with the
            // sample, and their order reverses on alternate samples, because the
            // pool is sorted: offsets that only ever grow rank the variables the
            // same way every time, and `a - c >= b - c` then never sees `a`
            // above `b`.
            let rank = if s % 2 == 0 {
                i
            } else {
                vars.len().saturating_sub(1) - i
            };
            let step = if together {
                0
            } else {
                rank.wrapping_mul(1 + s % 7)
            };
            let v = pool[s.wrapping_add(step) % pool.len()];
            c = c.subst(&Expr::Var(*k), &Expr::Const(v));
        }
        let outcome = folded(&c).eval()?;
        match agreed {
            None => agreed = Some(outcome),
            Some(a) if a == outcome => {}
            Some(_) => return None,
        }
    }
    let sampled = agreed?;
    match proven(cond, &vars) {
        Exhaustive::Always(outcome) if outcome == sampled => Some((outcome, Evidence::Proven)),
        Exhaustive::Always(_) | Exhaustive::Varies => None,
        Exhaustive::Unknown => Some((sampled, Evidence::Sampled(samples))),
    }
}

/// Decides a condition's outcome for every input, where that takes few
/// enough evaluations.
///
/// The outcome is a function of the low bits [`demand`] finds, so trying
/// every value of those bits, the rest zero, tries every input. An
/// equality whose sides depend on too many bits is still never true when
/// the sides' low `k` bits never agree, for some `k` small enough to
/// enumerate: `7 * y * y - 1 == z * z` differs in its low three bits for
/// every `y` and `z`.
///
/// # Arguments
///
/// * `cond` - The branch condition.
/// * `vars` - Every variable it reads.
fn proven(cond: &Cond, vars: &[Key]) -> Exhaustive {
    let found = exhaust(cond, vars);
    if found != Exhaustive::Unknown {
        return found;
    }
    let (Flags::Cmp(l, r, w), ConditionCode::e | ConditionCode::ne) = (&cond.flags, cond.cc.0)
    else {
        return Exhaustive::Unknown;
    };
    let low = |e: &Expr, m: u64| Expr::Bin(Op::And, Box::new(e.clone()), Box::new(Expr::Const(m)));
    for k in 1..(*w).min(63) {
        let m = (1u64 << k) - 1;
        let equal = Cond {
            cc: Cc(ConditionCode::e),
            flags: Flags::Cmp(low(l, m), low(r, m), *w),
        };
        match exhaust(&equal, vars) {
            Exhaustive::Always(false) => return Exhaustive::Always(cond.cc.0 == ConditionCode::ne),
            Exhaustive::Unknown => break,
            Exhaustive::Always(true) | Exhaustive::Varies => {}
        }
    }
    Exhaustive::Unknown
}

/// Evaluates a condition on every value of the low bits its outcome
/// depends on.
///
/// # Arguments
///
/// * `cond` - The branch condition.
/// * `vars` - Every variable it reads; one whose bits do not matter is zero.
fn exhaust(cond: &Cond, vars: &[Key]) -> Exhaustive {
    let mut need = BTreeMap::new();
    if depends(cond, &mut need).is_none() {
        return Exhaustive::Unknown;
    }
    let total: u32 = need.values().map(|b: &u8| u32::from(*b)).sum();
    if total > PROOF_BITS {
        return Exhaustive::Unknown;
    }
    let mut agreed = None;
    for i in 0..1u64 << total {
        let mut c = cond.clone();
        let mut at = 0u32;
        for k in vars {
            let bits = need.get(k).copied().map_or(0, u32::from);
            let v = (i >> at) & ((1u64 << bits) - 1);
            at += bits;
            c = c.subst(&Expr::Var(*k), &Expr::Const(v));
        }
        let Some(outcome) = folded(&c).eval() else {
            return Exhaustive::Unknown;
        };
        match agreed {
            None => agreed = Some(outcome),
            Some(a) if a == outcome => {}
            Some(_) => return Exhaustive::Varies,
        }
    }
    agreed.map_or(Exhaustive::Unknown, Exhaustive::Always)
}

/// Gathers how many low bits of each variable a condition's outcome
/// depends on.
///
/// The flags a compare, a test or an operation's result leaves are a
/// function of the low `w` bits of what it computed, at its width `w`.
///
/// # Arguments
///
/// * `cond` - The branch condition.
/// * `need` - Receives each variable's count of low bits, the most asked.
///
/// # Returns
///
/// `None` when the flags read something [`demand`] cannot bound.
fn depends(cond: &Cond, need: &mut BTreeMap<Key, u8>) -> Option<()> {
    match &cond.flags {
        Flags::Cmp(l, r, w) | Flags::Float(l, r, w) | Flags::Add(l, r, w) => {
            demand(l, *w, need)?;
            demand(r, *w, need)
        }
        Flags::Test(l, r, w) => {
            let both = Expr::Bin(Op::And, Box::new(l.clone()), Box::new(r.clone()));
            demand(&both, *w, need)
        }
        Flags::Result(e, w) => demand(e, *w, need),
        Flags::Carry(_) | Flags::Truth(..) | Flags::Shift(..) | Flags::Unknown => None,
    }
}

/// Gathers how many low bits of each variable the low `k` bits of an
/// expression depend on.
///
/// The low bits of a sum, a difference, a product and a bitwise operation
/// are a function of the low bits of their operands alone; a constant mask
/// clears the bits above its highest, and a left shift by a constant moves
/// the operand's bits up past the low ones. Anything else (a right shift,
/// a division, a rotate) lets a high bit reach the low ones.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `k` - How many of its low bits are read.
/// * `need` - Receives each variable's count of low bits, the most asked.
///
/// # Returns
///
/// `None` when a higher bit of an operand can reach the low `k` bits.
fn demand(e: &Expr, k: u8, need: &mut BTreeMap<Key, u8>) -> Option<()> {
    if k == 0 {
        return Some(());
    }
    let top = |m: u64| u8::try_from(64 - m.leading_zeros()).unwrap_or(64);
    match e {
        Expr::Const(_) => Some(()),
        Expr::Var(key) => {
            let bits = need.entry(*key).or_default();
            *bits = (*bits).max(k);
            Some(())
        }
        Expr::Bin(Op::And, l, r) => match (&**l, &**r) {
            (x, Expr::Const(m)) | (Expr::Const(m), x) => demand(x, k.min(top(*m)), need),
            _ => {
                demand(l, k, need)?;
                demand(r, k, need)
            }
        },
        Expr::Bin(Op::Add | Op::Sub | Op::Mul | Op::Or | Op::Xor, l, r) => {
            demand(l, k, need)?;
            demand(r, k, need)
        }
        Expr::Bin(Op::Shl, l, r) => match **r {
            Expr::Const(c) if c < 64 => demand(l, k.saturating_sub(u8::try_from(c).ok()?), need),
            _ => None,
        },
        Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Sext(..)
        | Expr::Cast(..)
        | Expr::Deref(..)
        | Expr::Cond(_)
        | Expr::Ternary(..)
        | Expr::Call(..)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::FConst(..) => None,
    }
}

/// Tells whether a condition computes anything before comparing.
///
/// An opaque predicate is an identity dressed as a decision, so it always
/// does arithmetic: `(x * x + x) % 2 == 0`. A bare `x == y` or `x < 5`
/// compares what it was given and cannot be one. Ordinary code is almost
/// entirely bare comparisons, and sampling each of them costs far more than
/// the answer is worth.
///
/// # Arguments
///
/// * `cond` - The branch condition.
///
/// # Returns
///
/// `true` when some operand is an operation rather than a plain value.
fn computes(cond: &Cond) -> bool {
    let operand = |e: &Expr| matches!(e, Expr::Bin(..) | Expr::Un(..));
    match &cond.flags {
        Flags::Cmp(l, r, _)
        | Flags::Float(l, r, _)
        | Flags::Test(l, r, _)
        | Flags::Add(l, r, _) => operand(l) || operand(r),
        Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => operand(e),
        Flags::Shift(e, _, c) => operand(e) || operand(c),
        Flags::Unknown => false,
    }
}

/// Folds a condition's operands, so an assignment reaches a verdict.
///
/// Substitution replaces a variable with a constant but leaves the
/// arithmetic around it standing, and the evaluator only decides a
/// comparison of two constants. Folding bottom-up closes that gap.
///
/// # Arguments
///
/// * `c` - The condition with its variables already substituted.
///
/// # Returns
///
/// The same condition with constant-valued operands reduced.
fn folded(c: &Cond) -> Cond {
    let flags = match &c.flags {
        Flags::Cmp(l, r, b) => Flags::Cmp(reduce(l, *b), reduce(r, *b), *b),
        Flags::Test(l, r, b) => Flags::Test(reduce(l, *b), reduce(r, *b), *b),
        Flags::Add(l, r, b) => Flags::Add(reduce(l, *b), reduce(r, *b), *b),
        Flags::Result(e, b) => Flags::Result(reduce(e, *b), *b),
        other => other.clone(),
    };
    Cond { cc: c.cc, flags }
}

/// Reduces an expression to a constant where its operands allow.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `bits` - Width the operation is performed at.
///
/// # Returns
///
/// The reduced expression, unchanged where nothing folds.
fn reduce(e: &Expr, bits: u8) -> Expr {
    match e {
        Expr::Bin(op, l, r) => {
            let w = match op {
                Op::Rol(w) | Op::Ror(w) | Op::MulHi(w) | Op::SMulHi(w) => *w,
                _ => bits,
            };
            fold(*op, reduce(l, w), reduce(r, w), w)
        }
        other => other.clone(),
    }
}

/// Builds the values sampled into this condition's variables.
///
/// The fixed spread alone calls `x == 5` constant, because it never tries
/// five: an ordinary comparison against a constant the spread misses looks
/// exactly like a predicate that cannot be satisfied. Every constant the
/// condition itself names, and its neighbours, join the pool so a
/// comparison is always tried against the value it compares to.
///
/// # Arguments
///
/// * `cond` - The condition being tested.
///
/// # Returns
///
/// The fixed spread followed by the condition's own constants, deduplicated
/// and in a fixed order.
fn pool_for(cond: &Cond) -> Vec<u64> {
    let mut consts = BTreeSet::new();
    match &cond.flags {
        Flags::Cmp(l, r, _)
        | Flags::Float(l, r, _)
        | Flags::Test(l, r, _)
        | Flags::Add(l, r, _) => {
            constants(l, &mut consts);
            constants(r, &mut consts);
        }
        Flags::Result(e, _) | Flags::Carry(e) | Flags::Truth(e, _) => constants(e, &mut consts),
        Flags::Shift(e, _, c) => {
            constants(e, &mut consts);
            constants(c, &mut consts);
        }
        Flags::Unknown => {}
    }
    let mut pool: Vec<u64> = VALUES.to_vec();
    let consts: Vec<u64> = consts.into_iter().collect();
    for &c in &consts {
        // The value itself, its neighbours, and the input that cancels it: a
        // width guard is written `size + K <= N`, true only for the handful of
        // inputs that carry the sum around zero, and a pool that never lands
        // there reports an ordinary overflow check as a branch that never runs.
        pool.extend([c, c.wrapping_sub(1), c.wrapping_add(1), c.wrapping_neg()]);
        // The inputs a one-operation guard turns on: `x >> 1 == C` holds for the
        // two values that shift down to C, and a pool without them reports a
        // width check written with a shift as a branch that never runs.
        pool.extend([c << 1, (c << 1) | 1, c >> 1]);
        for &d in &consts {
            pool.extend([d.wrapping_sub(c), d.wrapping_sub(c).wrapping_add(1)]);
        }
    }
    pool.sort_unstable();
    pool.dedup();
    pool
}

/// Collects the constants an expression names.
///
/// # Arguments
///
/// * `e` - The expression to walk.
/// * `out` - Receives each constant found.
fn constants(e: &Expr, out: &mut BTreeSet<u64>) {
    match e {
        Expr::Const(c) => {
            out.insert(*c);
        }
        Expr::Bin(_, l, r) => {
            constants(l, out);
            constants(r, out);
        }
        Expr::Un(_, x) | Expr::Sext(x, _) | Expr::Cast(x, _) | Expr::Deref(x, _) => {
            constants(x, out);
        }
        Expr::Ternary(_, a, b) => {
            constants(a, out);
            constants(b, out);
        }
        Expr::Call(_, args) => {
            for a in args {
                constants(a, out);
            }
        }
        Expr::Var(_) | Expr::Str(_) | Expr::Sp(_) | Expr::Cond(_) | Expr::FConst(..) => {}
    }
}

/// Collects the distinct variables an expression reads.
///
/// A memory read is not collected: its value cannot be sampled, so a
/// condition holding one is rejected when the evaluator declines it.
///
/// # Arguments
///
/// * `e` - The expression to walk.
/// * `out` - Receives each variable found.
fn collect(e: &Expr, out: &mut BTreeSet<Key>) {
    match e {
        Expr::Var(k) => {
            out.insert(*k);
        }
        Expr::Bin(_, l, r) => {
            collect(l, out);
            collect(r, out);
        }
        Expr::Un(_, x) | Expr::Sext(x, _) | Expr::Cast(x, _) | Expr::Deref(x, _) => {
            collect(x, out);
        }
        Expr::Ternary(_, a, b) => {
            collect(a, out);
            collect(b, out);
        }
        Expr::Call(_, args) => {
            for a in args {
                collect(a, out);
            }
        }
        Expr::Const(_) | Expr::Str(_) | Expr::Sp(_) | Expr::Cond(_) | Expr::FConst(..) => {}
    }
}

/// Tells whether an expression reads memory anywhere inside it.
///
/// A memory read has no value to sample. Giving its address a sampled value
/// and letting the read fold against the image answers a question nobody
/// asked: every sample reads somewhere unmapped, every read agrees, and an
/// ordinary null check on a loaded pointer is reported as never varying.
///
/// # Arguments
///
/// * `e` - The expression to walk.
fn reads_memory(e: &Expr) -> bool {
    match e {
        Expr::Deref(..) => true,
        Expr::Bin(_, l, r) | Expr::Ternary(_, l, r) => reads_memory(l) || reads_memory(r),
        Expr::Un(_, x) | Expr::Sext(x, _) | Expr::Cast(x, _) => reads_memory(x),
        Expr::Call(_, args) => args.iter().any(reads_memory),
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Cond(_)
        | Expr::FConst(..) => false,
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Evidence, constant_outcome};
    use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, Op, opaque_note};
    use crate::isa::x86::{ConditionCode, Register};

    /// Builds `x` as a register variable.
    fn x() -> Expr {
        Expr::Var(Key::Reg(Register::RAX))
    }

    /// Builds `y` as a second register variable.
    fn y() -> Expr {
        Expr::Var(Key::Reg(Register::RCX))
    }

    /// Builds `l <op> r`.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `l` - Left operand.
    /// * `r` - Right operand.
    fn bin(op: Op, l: Expr, r: Expr) -> Expr {
        Expr::Bin(op, Box::new(l), Box::new(r))
    }

    /// Builds the condition `l <cc> r` over 64-bit operands.
    ///
    /// # Arguments
    ///
    /// * `cc` - The condition code.
    /// * `l` - Left operand.
    /// * `r` - Right operand.
    fn cmp(cc: ConditionCode, l: Expr, r: Expr) -> Cond {
        Cond {
            cc: Cc(cc),
            flags: Flags::Cmp(l, r, 64),
        }
    }

    /// A predicate true for every input is reported as never varying.
    ///
    /// `(x | 1) & 1` is one whatever `x` holds, which is the shape an
    /// obfuscator emits to make a branch that is not a decision; it reads
    /// one bit of `x`, so both of its values prove it.
    #[test]
    fn an_always_true_predicate_is_found() {
        let e = bin(Op::And, bin(Op::Or, x(), Expr::Const(1)), Expr::Const(1));
        assert_eq!(
            constant_outcome(&cmp(ConditionCode::e, e, Expr::Const(1))),
            Some((true, Evidence::Proven))
        );
    }

    /// The note names the branch that never runs, and which way it goes.
    ///
    /// Saying a predicate is opaque tells a reader to distrust it; saying
    /// which way it always goes tells them which half of the function to
    /// stop reading, which is the part worth having.
    #[test]
    fn the_note_names_the_dead_branch() {
        let e = bin(Op::And, bin(Op::Or, x(), Expr::Const(1)), Expr::Const(1));
        let cond = cmp(ConditionCode::e, e, Expr::Const(1));
        assert_eq!(constant_outcome(&cond), Some((true, Evidence::Proven)));
        let note = opaque_note(true, false, Evidence::Proven);
        assert!(note.contains("always true"), "{note}");
        assert!(note.contains("the else never runs"), "{note}");
        // Rendered negated, the same condition kills the body instead.
        let flipped = opaque_note(true, true, Evidence::Proven);
        assert!(flipped.contains("always false"), "{flipped}");
        assert!(flipped.contains("the body never runs"), "{flipped}");
    }

    /// A key check that fails one input in 4919 agrees on every sample,
    /// and its 32 bits are too many to try: the note says what it rests
    /// on and names no dead branch.
    ///
    /// `(uint32_t)(x * 0x3c441287 + 0x76733932) >= 0xd52b3` is a remainder
    /// by `0x1337` tested against `0x42`, as a compiler writes it.
    #[test]
    fn a_rare_failure_past_enumeration_is_only_sampled() {
        let e = bin(
            Op::Add,
            bin(Op::Mul, x(), Expr::Const(0x3c44_1287)),
            Expr::Const(0x7673_3932),
        );
        let cond = Cond {
            cc: Cc(ConditionCode::ae),
            flags: Flags::Cmp(e, Expr::Const(0xd52b3), 32),
        };
        let Some((true, evidence @ Evidence::Sampled(_))) = constant_outcome(&cond) else {
            panic!("{:?}", constant_outcome(&cond));
        };
        let note = opaque_note(true, false, evidence);
        assert!(
            note.contains("sampled") && !note.contains("never runs"),
            "{note}"
        );
    }

    /// A condition whose one exception lies within the bits it reads is
    /// found to vary, however the samples fell.
    ///
    /// `(x * 5) & 0xfff != 0x5a5` is false only where the low twelve bits
    /// of `x` are `0x121`.
    #[test]
    fn an_exception_within_enumeration_varies() {
        let e = bin(
            Op::And,
            bin(Op::Mul, x(), Expr::Const(5)),
            Expr::Const(0xfff),
        );
        assert_eq!(
            constant_outcome(&cmp(ConditionCode::ne, e, Expr::Const(0x5a5))),
            None
        );
    }

    /// An equality whose sides never agree in their low bits is proven
    /// false: `7 * y * y - 1` is 2 or 3 modulo 4, a square 0 or 1.
    #[test]
    fn low_bits_that_never_agree_prove_an_inequality() {
        let left = bin(
            Op::Sub,
            bin(Op::Mul, bin(Op::Mul, Expr::Const(7), x()), x()),
            Expr::Const(1),
        );
        let cond = cmp(ConditionCode::e, left, bin(Op::Mul, y(), y()));
        assert_eq!(constant_outcome(&cond), Some((false, Evidence::Proven)));
    }

    /// An ordinary comparison against a constant is not reported.
    ///
    /// The fixed spread of sampled values does not contain five, so a pool
    /// that ignored the condition's own constants would call this constant.
    #[test]
    fn a_comparison_against_a_constant_varies() {
        assert_eq!(
            constant_outcome(&cmp(ConditionCode::e, x(), Expr::Const(5))),
            None
        );
    }

    /// A comparison of two variables is not reported.
    ///
    /// Sampling that spread the variables apart on every assignment never
    /// gave them one value, and `x != y` then looked like it could not be
    /// false.
    #[test]
    fn a_comparison_of_two_variables_varies() {
        assert_eq!(constant_outcome(&cmp(ConditionCode::ne, x(), y())), None);
        assert_eq!(constant_outcome(&cmp(ConditionCode::e, x(), y())), None);
    }

    /// A condition reading memory is declined rather than sampled.
    #[test]
    fn a_condition_reading_memory_is_declined() {
        let load = Expr::Deref(Box::new(x()), crate::analysis::decompile::expr::Ty::U64);
        assert_eq!(
            constant_outcome(&cmp(ConditionCode::ne, load, Expr::Const(0))),
            None
        );
    }
}
