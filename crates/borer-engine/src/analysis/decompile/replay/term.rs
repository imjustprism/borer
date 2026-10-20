//! Values over every state: the replay's arithmetic with terms in place of
//! bits, kept in a normal form so that two spellings of one value are one
//! term.
//!
//! A [`Term`] denotes a 64-bit value, or none in a state where the replay's
//! own evaluation finds none (a division by zero, a variable a call left
//! unknown). Every operator means exactly what the replay's evaluators do
//! with bits: an integer operator is [`fold`] at its width, a unary one
//! [`unary`], a sign extension [`sext`], a float one [`float_arith`].
//!
//! The normal form makes structural equality a proof. Sums and products
//! are polynomials modulo `2^w` ([`Term::Poly`]): `x + 1 - x` is `1`, and
//! `(x + y) * 2` is `2x + 2y`. A mask of the low `n` bits reduces a
//! polynomial to `2^n` and is dropped from a value that already fits. The
//! bitwise operators are flattened, sorted and merged with their constants
//! ([`Term::Logic`]). Every other operator is kept as it is over normalized
//! operands, so it is equal only to itself on equal operands, which is true
//! of any function. A comparison is a [`Pred`] over the difference of its
//! sides, its sign chosen once, and a float comparison is the set of
//! outcomes (less, equal, greater, unordered) it holds for: the same pair
//! of values always has the same outcome, so two compares over one pair
//! agree in every state exactly when their sets do.
//!
//! Equal normal forms prove two values equal wherever both are defined.
//! Different ones prove nothing; [`value`] then evaluates both at concrete
//! points to look for a state that tells them apart.

use std::collections::BTreeMap;
use std::rc::Rc;

use super::super::expr::{Expr, Key, Op, UnOp, fold, unary};
use super::super::floats::{float_arith, float_of, float_to_int, float_un};
use super::super::verify::{low, sext};
use crate::fxmap::FxHashMap;

/// Most monomials a product of two sums keeps before the product stays an
/// opaque multiply.
const PRODUCT_MAX: usize = 32;
/// Most atoms one monomial multiplies before the product stays opaque.
const DEGREE_MAX: usize = 4;

/// The outcome of a float compare where the left value is less.
pub(super) const LT: u8 = 1;
/// The outcome where the values are equal (a zero equals the other zero).
pub(super) const EQ: u8 = 2;
/// The outcome where the left value is greater.
pub(super) const GT: u8 = 4;
/// The outcome where either value is a NaN.
pub(super) const UN: u8 = 8;
/// Every outcome.
const ALL: u8 = LT | EQ | GT | UN;

/// A bitwise operator of a [`Term::Logic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Logic {
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise exclusive or.
    Xor,
}

/// One monomial of a [`Term::Poly`]: its atoms, sorted, repeated for a
/// power, with its coefficient.
pub(super) type Monomial = (Vec<Term>, u64);

/// A value over every state, in normal form.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Term {
    /// A constant.
    Const(u64),
    /// A variable's value where the block starts: the variable, and the
    /// bits its value fits in.
    In(Key, u8),
    /// Bytes of memory read through an address, little-endian: the
    /// address, at the register width; how many bytes, one to eight; and
    /// the bytes written over memory as the block found it before the
    /// read, by address, each its byte's value (none where the replay
    /// reads no value). No value where the bytes run past the top of the
    /// address space.
    Mem(Rc<Term>, u8, Rc<[(u64, Term)]>),
    /// A value no state has.
    Undef,
    /// A sum of monomials modulo `2^w`: the width, and the monomials
    /// sorted, each coefficient nonzero modulo `2^w`.
    Poly(u8, Vec<Monomial>),
    /// A bitwise operator over its operands, sorted, the result masked to
    /// the width.
    Logic(Logic, u8, Vec<Term>),
    /// Another integer operator at a width, as [`fold`] computes it.
    Bin(Op, u8, Rc<Term>, Rc<Term>),
    /// An integer unary operator at a width, as [`unary`] computes it.
    Un(UnOp, u8, Rc<Term>),
    /// The low bits of a value sign-extended to 64 bits ([`sext`]).
    Sext(Rc<Term>, u8),
    /// 1 where a predicate holds, else 0.
    Truth(Rc<Pred>),
    /// One of two values, as a predicate holds.
    Ite(Rc<Pred>, Rc<Term>, Rc<Term>),
    /// A float operator over two values of these widths, computed at the
    /// wider ([`float_arith`]).
    Float(Op, u8, u8, Rc<Term>, Rc<Term>),
    /// A float unary operator at a width ([`float_un`]).
    FloatUn(UnOp, u8, Rc<Term>),
    /// A float of a width converted to an integer of a width
    /// ([`float_to_int`]).
    ToInt(u8, u8, Rc<Term>),
}

/// A truth over every state, in normal form.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum Pred {
    /// Holds in every state, or in none.
    Is(bool),
    /// The value is zero.
    Zero(Term),
    /// The left value is below the right, unsigned.
    Ult(Term, Term),
    /// The left value is below the right, signed at a width.
    Slt(u8, Term, Term),
    /// A bit of the value is set: its index, and the value.
    Bit(u8, Term),
    /// A float compare of two values of a width has one of a set of
    /// outcomes ([`LT`], [`EQ`], [`GT`], [`UN`]).
    Float(u8, u8, Term, Term),
    /// The predicate does not hold.
    Not(Rc<Pred>),
    /// No state decides it.
    Undef,
}

impl Term {
    /// Returns the most bits the value can have: it is below `2^n`.
    pub(super) fn fits(&self) -> u8 {
        match self {
            Term::Const(c) => u8::try_from(64 - c.leading_zeros()).unwrap_or(64),
            Term::In(_, b) | Term::FloatUn(_, b, _) => *b,
            Term::Poly(w, p) => bound(p)
                .map_or(*w, |b| u8::try_from(64 - b.leading_zeros()).unwrap_or(64))
                .min(*w),
            Term::Mem(_, n, _) => n.saturating_mul(8).min(64),
            Term::Undef => 0,
            Term::Logic(Logic::And, w, xs) => xs.iter().map(Term::fits).min().unwrap_or(*w).min(*w),
            Term::Logic(Logic::Or | Logic::Xor, w, xs) => {
                xs.iter().map(Term::fits).max().unwrap_or(0).min(*w)
            }
            Term::Bin(op, w, a, b) => match op {
                Op::UAddO(_) | Op::USubO(_) | Op::SMulO(_) => 1,
                Op::MulHi(n) | Op::SMulHi(n) | Op::Rol(n) | Op::Ror(n) => (*n).min(*w),
                Op::Div => a.fits().min(*w),
                Op::Rem => a.fits().min(b.fits()).min(*w),
                Op::Shr => {
                    if let Term::Const(k) = **b {
                        a.fits()
                            .min(*w)
                            .saturating_sub(u8::try_from(k & 63).unwrap_or(63))
                    } else {
                        *w
                    }
                }
                Op::Add
                | Op::Sub
                | Op::Mul
                | Op::SDiv
                | Op::SRem
                | Op::And
                | Op::Or
                | Op::Xor
                | Op::Shl
                | Op::Sar
                | Op::FAdd
                | Op::FSub
                | Op::FMul
                | Op::FDiv
                | Op::FMin
                | Op::FMax => *w,
            },
            Term::Un(op, w, _) => match op {
                UnOp::Tzcnt | UnOp::Lzcnt | UnOp::Popcnt | UnOp::Bsf | UnOp::Bsr => 7.min(*w),
                UnOp::Neg | UnOp::Not | UnOp::Bswap | UnOp::Sqrt | UnOp::Fabs => *w,
            },
            Term::Sext(..) => 64,
            Term::Truth(_) => 1,
            Term::Ite(_, a, b) => a.fits().max(b.fits()),
            Term::Float(_, fa, fb, ..) => (*fa).max(*fb),
            Term::ToInt(_, bits, _) => match bits {
                0..=16 => *bits,
                17..=32 => 32,
                33..=u8::MAX => 64,
            },
        }
    }

    /// Tells whether some state may leave the value undefined because it
    /// reads an unknown: no state's evaluation of a value the lift does not
    /// state has an answer.
    pub(super) fn lacks(&self) -> bool {
        match self {
            Term::Const(_) | Term::In(..) => false,
            Term::Undef => true,
            Term::Mem(a, _, d) => a.lacks() || d.iter().any(|(_, v)| v.lacks()),
            Term::Un(_, _, a)
            | Term::Sext(a, _)
            | Term::FloatUn(_, _, a)
            | Term::ToInt(_, _, a) => a.lacks(),
            Term::Poly(_, p) => p.iter().any(|(m, _)| m.iter().any(Term::lacks)),
            Term::Logic(_, _, xs) => xs.iter().any(Term::lacks),
            Term::Bin(_, _, a, b) | Term::Float(_, _, _, a, b) => a.lacks() || b.lacks(),
            Term::Truth(p) => p.lacks(),
            Term::Ite(p, a, b) => p.lacks() || a.lacks() || b.lacks(),
        }
    }

    /// Takes the value's nodes out of a budget, stopping once it runs out.
    ///
    /// # Arguments
    ///
    /// * `budget` - Nodes left, lowered by each node visited.
    ///
    /// # Returns
    ///
    /// Whether the whole value fits in what the budget had.
    pub(super) fn spend(&self, budget: &mut usize) -> bool {
        let Some(left) = budget.checked_sub(1) else {
            return false;
        };
        *budget = left;
        match self {
            Term::Const(_) | Term::In(..) | Term::Undef => true,
            Term::Mem(a, _, d) => a.spend(budget) && d.iter().all(|(_, v)| v.spend(budget)),
            Term::Un(_, _, a)
            | Term::Sext(a, _)
            | Term::FloatUn(_, _, a)
            | Term::ToInt(_, _, a) => a.spend(budget),
            Term::Poly(_, p) => p.iter().flat_map(|(m, _)| m).all(|a| a.spend(budget)),
            Term::Logic(_, _, xs) => xs.iter().all(|x| x.spend(budget)),
            Term::Bin(_, _, a, b) | Term::Float(_, _, _, a, b) => {
                a.spend(budget) && b.spend(budget)
            }
            Term::Truth(p) => p.spend(budget),
            Term::Ite(p, a, b) => p.spend(budget) && a.spend(budget) && b.spend(budget),
        }
    }

    /// Collects the constants the value is built with, the values a search
    /// for a state that tells two values apart starts next to.
    ///
    /// # Arguments
    ///
    /// * `out` - Where they go.
    pub(super) fn constants(&self, out: &mut Vec<u64>) {
        match self {
            Term::Const(c) => out.push(*c),
            Term::In(..) | Term::Undef => {}
            Term::Mem(a, _, d) => {
                a.constants(out);
                d.iter().for_each(|(_, v)| v.constants(out));
            }
            Term::Un(_, _, a)
            | Term::Sext(a, _)
            | Term::FloatUn(_, _, a)
            | Term::ToInt(_, _, a) => a.constants(out),
            Term::Poly(_, p) => {
                for (m, c) in p {
                    out.push(*c);
                    for a in m {
                        a.constants(out);
                    }
                }
            }
            Term::Logic(_, _, xs) => xs.iter().for_each(|x| x.constants(out)),
            Term::Bin(_, _, a, b) | Term::Float(_, _, _, a, b) => {
                a.constants(out);
                b.constants(out);
            }
            Term::Truth(p) => p.constants(out),
            Term::Ite(p, a, b) => {
                p.constants(out);
                a.constants(out);
                b.constants(out);
            }
        }
    }

    /// Collects the variables the value reads where the block starts.
    ///
    /// # Arguments
    ///
    /// * `out` - Each variable with the bits its value fits in.
    pub(super) fn inputs(&self, out: &mut BTreeMap<Key, u8>) {
        match self {
            Term::In(k, b) => {
                out.insert(*k, *b);
            }
            Term::Const(_) | Term::Undef => {}
            Term::Mem(a, _, d) => {
                a.inputs(out);
                d.iter().for_each(|(_, v)| v.inputs(out));
            }
            Term::Un(_, _, a)
            | Term::Sext(a, _)
            | Term::FloatUn(_, _, a)
            | Term::ToInt(_, _, a) => a.inputs(out),
            Term::Poly(_, p) => p.iter().flat_map(|(m, _)| m).for_each(|a| a.inputs(out)),
            Term::Logic(_, _, xs) => xs.iter().for_each(|x| x.inputs(out)),
            Term::Bin(_, _, a, b) | Term::Float(_, _, _, a, b) => {
                a.inputs(out);
                b.inputs(out);
            }
            Term::Truth(p) => p.inputs(out),
            Term::Ite(p, a, b) => {
                p.inputs(out);
                a.inputs(out);
                b.inputs(out);
            }
        }
    }
}

impl Pred {
    /// Tells whether the truth reads an unknown ([`Term::lacks`]).
    fn lacks(&self) -> bool {
        match self {
            Pred::Is(_) => false,
            Pred::Undef => true,
            Pred::Zero(t) | Pred::Bit(_, t) => t.lacks(),
            Pred::Ult(a, b) | Pred::Slt(_, a, b) | Pred::Float(_, _, a, b) => {
                a.lacks() || b.lacks()
            }
            Pred::Not(p) => p.lacks(),
        }
    }

    /// Takes the predicate's nodes out of a budget ([`Term::spend`]).
    ///
    /// # Arguments
    ///
    /// * `budget` - Nodes left, lowered by each node visited.
    ///
    /// # Returns
    ///
    /// Whether the whole predicate fits in what the budget had.
    fn spend(&self, budget: &mut usize) -> bool {
        let Some(left) = budget.checked_sub(1) else {
            return false;
        };
        *budget = left;
        match self {
            Pred::Is(_) | Pred::Undef => true,
            Pred::Zero(t) | Pred::Bit(_, t) => t.spend(budget),
            Pred::Ult(a, b) | Pred::Slt(_, a, b) | Pred::Float(_, _, a, b) => {
                a.spend(budget) && b.spend(budget)
            }
            Pred::Not(p) => p.spend(budget),
        }
    }

    /// Collects the constants the predicate is built with
    /// ([`Term::constants`]).
    ///
    /// # Arguments
    ///
    /// * `out` - Where they go.
    fn constants(&self, out: &mut Vec<u64>) {
        match self {
            Pred::Is(_) | Pred::Undef => {}
            Pred::Zero(t) | Pred::Bit(_, t) => t.constants(out),
            Pred::Ult(a, b) | Pred::Slt(_, a, b) | Pred::Float(_, _, a, b) => {
                a.constants(out);
                b.constants(out);
            }
            Pred::Not(p) => p.constants(out),
        }
    }

    /// Collects the variables the predicate reads ([`Term::inputs`]).
    ///
    /// # Arguments
    ///
    /// * `out` - Each variable with the bits its value fits in.
    fn inputs(&self, out: &mut BTreeMap<Key, u8>) {
        match self {
            Pred::Is(_) | Pred::Undef => {}
            Pred::Zero(t) | Pred::Bit(_, t) => t.inputs(out),
            Pred::Ult(a, b) | Pred::Slt(_, a, b) | Pred::Float(_, _, a, b) => {
                a.inputs(out);
                b.inputs(out);
            }
            Pred::Not(p) => p.inputs(out),
        }
    }
}

/// The width `n` when `m` is the mask of the low `n` bits, `n` from 1 to 64.
///
/// # Arguments
///
/// * `m` - The mask.
fn low_run(m: u64) -> Option<u8> {
    (m != 0 && m & m.wrapping_add(1) == 0).then(|| u8::try_from(m.count_ones()).unwrap_or(64))
}

/// A value's low `n` bits: `t & ((1 << n) - 1)`.
///
/// # Arguments
///
/// * `t` - The value.
/// * `n` - Bits kept; 64 or more keeps them all.
pub(super) fn narrow(t: &Term, n: u8) -> Term {
    if n >= 64 {
        return t.clone();
    }
    let r = reduce(t, n);
    if r.fits() <= n {
        return r;
    }
    poly(n, vec![(vec![r], 1)])
}

/// Returns a value equal to `t` in its low `w` bits, in the form two such
/// values share.
///
/// A mask, a sign extension or a wider operation the low bits do not
/// depend on is dropped, and the bits a shift brings down are read only
/// as far as they reach.
///
/// # Arguments
///
/// * `t` - The value.
/// * `w` - The bits that matter.
pub(super) fn reduce(t: &Term, w: u8) -> Term {
    if w >= 64 {
        return t.clone();
    }
    match t {
        Term::Const(c) => Term::Const(c & low(w)),
        Term::Poly(pw, p) if *pw >= w => unwrap(poly(w, p.clone()), w),
        Term::Logic(op, lw, xs) if *lw > w => unwrap(logic(*op, w, xs.clone()), w),
        Term::Ite(p, a, b) => ite((**p).clone(), reduce(a, w), reduce(b, w)),
        Term::Sext(a, b) if *b >= w => reduce(a, w),
        Term::Bin(Op::Shr, bw, a, s) => match **s {
            Term::Const(k) => {
                let need = u8::try_from((k & 63) + u64::from(w)).unwrap_or(64).min(*bw);
                opaque(Op::Shr, *bw, reduce(a, need), Term::Const(k))
            }
            Term::In(..)
            | Term::Mem(..)
            | Term::Undef
            | Term::Poly(..)
            | Term::Logic(..)
            | Term::Bin(..)
            | Term::Un(..)
            | Term::Sext(..)
            | Term::Truth(_)
            | Term::Ite(..)
            | Term::Float(..)
            | Term::FloatUn(..)
            | Term::ToInt(..) => t.clone(),
        },
        Term::Poly(..)
        | Term::Logic(..)
        | Term::Sext(..)
        | Term::In(..)
        | Term::Mem(..)
        | Term::Undef
        | Term::Bin(..)
        | Term::Un(..)
        | Term::Truth(_)
        | Term::Float(..)
        | Term::FloatUn(..)
        | Term::ToInt(..) => t.clone(),
    }
}

/// A one-atom sum read as its atom, reduced again to the low `w` bits.
///
/// # Arguments
///
/// * `r` - A value already reduced to `w` bits at its top.
/// * `w` - The bits that matter.
fn unwrap(r: Term, w: u8) -> Term {
    if let Term::Poly(_, q) = &r
        && let [(atoms, 1)] = q.as_slice()
        && let [x] = atoms.as_slice()
    {
        return reduce(x, w);
    }
    r
}

/// A value as monomials modulo `2^w`.
///
/// # Arguments
///
/// * `t` - The value.
/// * `w` - The width.
fn monomials(t: &Term, w: u8) -> Vec<Monomial> {
    let m = low(w);
    match reduce(t, w) {
        Term::Const(c) if c & m == 0 => Vec::new(),
        Term::Const(c) => vec![(Vec::new(), c & m)],
        Term::Poly(pw, p) if pw >= w => p.iter().map(|(a, c)| (a.clone(), c & m)).collect(),
        r => vec![(vec![r], 1)],
    }
}

/// A sum of monomials modulo `2^w` in normal form.
///
/// # Arguments
///
/// * `w` - The width, 1 to 64.
/// * `terms` - The monomials, in any order, alike ones not yet merged.
pub(super) fn poly(w: u8, terms: Vec<Monomial>) -> Term {
    let m = low(w);
    if terms.iter().any(|(a, _)| a.contains(&Term::Undef)) {
        return Term::Undef;
    }
    let mut terms = expand(w, terms);
    terms.sort_by(|a, b| a.0.cmp(&b.0));
    let mut merged: Vec<Monomial> = Vec::with_capacity(terms.len());
    for (a, c) in terms {
        if let Some(last) = merged.last_mut()
            && last.0 == a
        {
            last.1 = last.1.wrapping_add(c) & m;
        } else {
            merged.push((a, c & m));
        }
    }
    merged.retain(|(_, c)| *c != 0);
    if merged.is_empty() {
        return Term::Const(0);
    }
    if let [(a, c)] = merged.as_slice() {
        if a.is_empty() {
            return Term::Const(*c);
        }
        if *c == 1 && a.len() == 1 && a[0].fits() <= w {
            return a[0].clone();
        }
    }
    let exact = bound(&merged).is_some_and(|b| b <= m);
    Term::Poly(if exact { 64 } else { w }, merged)
}

/// Monomials with every atom that is itself a sum at least as wide
/// multiplied out, so a sum read back at a narrower width is one sum.
///
/// # Arguments
///
/// * `w` - The width.
/// * `terms` - The monomials.
fn expand(w: u8, terms: Vec<Monomial>) -> Vec<Monomial> {
    let nested = |a: &Term| matches!(a, Term::Poly(pw, _) if *pw >= w);
    let mut out = Vec::with_capacity(terms.len());
    for (atoms, c) in terms {
        let reduced: Vec<Term> = atoms.iter().map(|a| reduce(a, w)).collect();
        if reduced == atoms && !atoms.iter().any(nested) {
            out.push((atoms, c));
            continue;
        }
        let product = reduced
            .iter()
            .fold(Term::Const(c), |acc, a| mul(w, &acc, a));
        out.extend(monomials(&product, w));
    }
    out
}

/// The most a sum of monomials can be, summed without wrapping.
///
/// # Arguments
///
/// * `p` - The monomials, each atom below `2^fits`.
///
/// # Returns
///
/// The bound, `None` when it passes 64 bits.
fn bound(p: &[Monomial]) -> Option<u64> {
    let top = u128::from(u64::MAX);
    let mut sum: u128 = 0;
    for (atoms, c) in p {
        let mut prod = u128::from(*c);
        for a in atoms {
            let f = a.fits();
            if f >= 64 {
                return None;
            }
            prod = prod.checked_mul((1u128 << f) - 1).filter(|v| *v <= top)?;
        }
        sum = sum.checked_add(prod).filter(|v| *v <= top)?;
    }
    u64::try_from(sum).ok()
}

/// `a + b` modulo `2^w`.
///
/// # Arguments
///
/// * `w` - The width.
/// * `a` - One addend.
/// * `b` - The other.
pub(super) fn add(w: u8, a: &Term, b: &Term) -> Term {
    let mut terms = monomials(a, w);
    terms.extend(monomials(b, w));
    poly(w, terms)
}

/// `-a` modulo `2^w`.
///
/// # Arguments
///
/// * `w` - The width.
/// * `a` - The value.
pub(super) fn neg(w: u8, a: &Term) -> Term {
    poly(
        w,
        monomials(a, w)
            .into_iter()
            .map(|(m, c)| (m, c.wrapping_neg()))
            .collect(),
    )
}

/// `a - b` modulo `2^w`.
///
/// # Arguments
///
/// * `w` - The width.
/// * `a` - The minuend.
/// * `b` - The subtrahend.
pub(super) fn sub(w: u8, a: &Term, b: &Term) -> Term {
    add(w, a, &neg(w, b))
}

/// `a * b` modulo `2^w`, distributed while the product stays small.
///
/// # Arguments
///
/// * `w` - The width.
/// * `a` - One factor.
/// * `b` - The other.
pub(super) fn mul(w: u8, a: &Term, b: &Term) -> Term {
    let (pa, pb) = (monomials(a, w), monomials(b, w));
    let degree = |p: &[Monomial]| p.iter().map(|(m, _)| m.len()).max().unwrap_or(0);
    if pa.len() * pb.len() > PRODUCT_MAX || degree(&pa) + degree(&pb) > DEGREE_MAX {
        let (x, y) = if a <= b { (a, b) } else { (b, a) };
        return opaque(Op::Mul, w, narrow(x, w), narrow(y, w));
    }
    let mut terms = Vec::with_capacity(pa.len() * pb.len());
    for (ma, ca) in &pa {
        for (mb, cb) in &pb {
            let mut m: Vec<Term> = ma.iter().chain(mb).cloned().collect();
            m.sort();
            terms.push((m, ca.wrapping_mul(*cb)));
        }
    }
    poly(w, terms)
}

/// A bitwise operator over values at a width, in normal form.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `w` - The width the result is masked to.
/// * `xs` - The operands.
pub(super) fn logic(op: Logic, w: u8, xs: Vec<Term>) -> Term {
    let m = low(w);
    let mut k: u64 = match op {
        Logic::And => m,
        Logic::Or | Logic::Xor => 0,
    };
    let mut ops: Vec<Term> = Vec::new();
    let mut stack = xs;
    while let Some(x) = stack.pop() {
        match narrow(&x, w) {
            Term::Const(c) => {
                k = match op {
                    Logic::And => k & c,
                    Logic::Or => k | c,
                    Logic::Xor => k ^ c,
                };
            }
            Term::Undef => return Term::Undef,
            Term::Logic(o, lw, inner) if o == op && (lw >= w || op == Logic::And) => {
                if op == Logic::And {
                    k &= low(lw);
                }
                stack.extend(inner);
            }
            other => ops.push(other),
        }
    }
    k &= m;
    match op {
        Logic::And if k == 0 => return Term::Const(0),
        Logic::Or if k == m => return Term::Const(m),
        Logic::And | Logic::Or | Logic::Xor => {}
    }
    ops.sort();
    match op {
        Logic::And | Logic::Or => ops.dedup(),
        Logic::Xor => {
            let mut kept: Vec<Term> = Vec::with_capacity(ops.len());
            for x in ops {
                if kept.last() == Some(&x) {
                    kept.pop();
                } else {
                    kept.push(x);
                }
            }
            ops = kept;
        }
    }
    let narrowest = ops.iter().map(Term::fits).min().unwrap_or(w);
    if op == Logic::And {
        k &= low(narrowest);
        if k == 0 {
            return Term::Const(0);
        }
    }
    let identity = match op {
        Logic::And => k & low(narrowest) == low(narrowest),
        Logic::Or | Logic::Xor => k == 0,
    };
    if op == Logic::And
        && !identity
        && let ([x], Some(n)) = (ops.as_slice(), low_run(k))
    {
        return narrow(x, n);
    }
    if op == Logic::Xor
        && k == 1
        && let [Term::Truth(p)] = ops.as_slice()
    {
        return truth(not((**p).clone()));
    }
    if !identity {
        ops.insert(0, Term::Const(k));
    }
    let exact = match op {
        Logic::And => ops.iter().map(Term::fits).min().unwrap_or(64) <= w,
        Logic::Or | Logic::Xor => ops.iter().map(Term::fits).max().unwrap_or(0) <= w,
    };
    if ops.is_empty() {
        Term::Const(k)
    } else if ops.len() == 1 {
        ops.remove(0)
    } else {
        Term::Logic(op, if exact { 64 } else { w }, ops)
    }
}

/// An operator kept as it is over its operands, or its value when both
/// are constants.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `w` - The width [`fold`] computes it at.
/// * `a` - The left operand.
/// * `b` - The right operand.
fn opaque(op: Op, w: u8, a: Term, b: Term) -> Term {
    if a == Term::Undef || b == Term::Undef {
        return Term::Undef;
    }
    if let (Term::Const(x), Term::Const(y)) = (&a, &b) {
        let folded = fold(op, Expr::Const(*x), Expr::Const(*y), w);
        return if let Expr::Const(v) = folded {
            Term::Const(v)
        } else {
            Term::Undef
        };
    }
    Term::Bin(op, w, Rc::new(a), Rc::new(b))
}

/// An integer operator at a width, as [`fold`] computes it with bits.
///
/// # Arguments
///
/// * `op` - The operator, not a float one.
/// * `w` - The width.
/// * `a` - The left operand.
/// * `b` - The right operand.
pub(super) fn bin(op: Op, w: u8, a: &Term, b: &Term) -> Term {
    match op {
        Op::Add => add(w, a, b),
        Op::Sub => sub(w, a, b),
        Op::Mul => mul(w, a, b),
        Op::And => logic(Logic::And, w, vec![a.clone(), b.clone()]),
        Op::Or => logic(Logic::Or, w, vec![a.clone(), b.clone()]),
        Op::Xor => logic(Logic::Xor, w, vec![a.clone(), b.clone()]),
        Op::Shl => {
            let Term::Const(k) = b else {
                return opaque(op, w, narrow(a, w), b.clone());
            };
            let k = k & 63;
            if k < u64::from(w) {
                mul(w, a, &Term::Const(1u64 << k))
            } else if *a == Term::Undef {
                Term::Undef
            } else {
                Term::Const(0)
            }
        }
        Op::Shr | Op::Sar if matches!(b, Term::Const(k) if k & 63 == 0) => narrow(a, w),
        Op::Shr | Op::Sar | Op::Div | Op::Rem | Op::SDiv | Op::SRem => {
            let b = if matches!(op, Op::Shr | Op::Sar) {
                b.clone()
            } else {
                narrow(b, w)
            };
            opaque(op, w, narrow(a, w), b)
        }
        Op::Rol(_)
        | Op::Ror(_)
        | Op::MulHi(_)
        | Op::SMulHi(_)
        | Op::SMulO(_)
        | Op::UAddO(_)
        | Op::USubO(_)
        | Op::FAdd
        | Op::FSub
        | Op::FMul
        | Op::FDiv
        | Op::FMin
        | Op::FMax => opaque(op, w, a.clone(), b.clone()),
    }
}

/// An integer unary operator at a width, as [`unary`] computes it.
///
/// # Arguments
///
/// * `op` - The operator, not a float one.
/// * `w` - The width.
/// * `a` - The operand.
pub(super) fn un(op: UnOp, w: u8, a: &Term) -> Term {
    match op {
        UnOp::Neg => neg(w, a),
        UnOp::Not => sub(w, &Term::Const(low(w)), a),
        UnOp::Bswap
        | UnOp::Tzcnt
        | UnOp::Lzcnt
        | UnOp::Popcnt
        | UnOp::Bsf
        | UnOp::Bsr
        | UnOp::Sqrt
        | UnOp::Fabs => match narrow(a, w) {
            Term::Undef => Term::Undef,
            Term::Const(c) => {
                const_of(&unary(op, Expr::Const(c), w)).map_or(Term::Undef, Term::Const)
            }
            x => Term::Un(op, w, Rc::new(x)),
        },
    }
}

/// The low `bits` of a value sign-extended to 64 bits ([`sext`]).
///
/// # Arguments
///
/// * `a` - The value.
/// * `bits` - The width of the signed field, 1 to 64.
pub(super) fn sign_extend(a: &Term, bits: u8) -> Term {
    if bits == 0 || bits > 64 || matches!(a, Term::Undef) {
        return Term::Undef;
    }
    let a = narrow(a, bits);
    if bits == 64 || a.fits() < bits {
        return a;
    }
    match a {
        Term::Const(c) => sext(c, bits).map_or(Term::Undef, Term::Const),
        other => Term::Sext(Rc::new(other), bits),
    }
}

/// A float operator over two values, computed at the wider of their
/// widths ([`float_arith`]).
///
/// # Arguments
///
/// * `op` - The float operator.
/// * `fa` - The left value's width, 32 or 64.
/// * `fb` - The right value's width, 32 or 64.
/// * `a` - The left value's bits.
/// * `b` - The right value's bits.
pub(super) fn float_bin(op: Op, fa: u8, fb: u8, a: &Term, b: &Term) -> Term {
    match (narrow(a, fa), narrow(b, fb)) {
        (Term::Undef, _) | (_, Term::Undef) => Term::Undef,
        (Term::Const(x), Term::Const(y)) => {
            float_arith(op, float_of(x, fa), float_of(y, fb), fa.max(fb))
                .map_or(Term::Undef, Term::Const)
        }
        (x, y) => Term::Float(op, fa, fb, Rc::new(x), Rc::new(y)),
    }
}

/// A float unary operator at a width ([`float_un`]).
///
/// # Arguments
///
/// * `op` - The operator, a square root or a magnitude.
/// * `fb` - The value's width, 32 or 64.
/// * `a` - The value's bits.
pub(super) fn float_unary(op: UnOp, fb: u8, a: &Term) -> Term {
    match a {
        Term::Undef => Term::Undef,
        Term::Const(x) => float_un(op, *x, fb).map_or(Term::Undef, Term::Const),
        x => Term::FloatUn(op, fb, Rc::new(x.clone())),
    }
}

/// A float converted to an integer ([`float_to_int`]).
///
/// # Arguments
///
/// * `fb` - The float's width, 32 or 64.
/// * `bits` - The integer's width.
/// * `a` - The float's bits.
pub(super) fn to_int(fb: u8, bits: u8, a: &Term) -> Term {
    match narrow(a, fb) {
        Term::Undef => Term::Undef,
        Term::Const(x) => Term::Const(float_to_int(x, fb, bits)),
        x => Term::ToInt(fb, bits, Rc::new(x)),
    }
}

/// A choice of value by a predicate.
///
/// # Arguments
///
/// * `p` - The predicate.
/// * `a` - The value where it holds.
/// * `b` - The value where it does not.
pub(super) fn ite(p: Pred, a: Term, b: Term) -> Term {
    match p {
        Pred::Is(true) => a,
        Pred::Is(false) => b,
        Pred::Undef => Term::Undef,
        _ if a == b => a,
        Pred::Not(q) => ite(Rc::unwrap_or_clone(q), b, a),
        p => Term::Ite(Rc::new(p), Rc::new(a), Rc::new(b)),
    }
}

/// 1 where a predicate holds, else 0.
///
/// # Arguments
///
/// * `p` - The predicate.
pub(super) fn truth(p: Pred) -> Term {
    match p {
        Pred::Is(b) => Term::Const(u64::from(b)),
        Pred::Undef => Term::Undef,
        p => Term::Truth(Rc::new(p)),
    }
}

/// The predicate that does not hold where `p` does.
///
/// # Arguments
///
/// * `p` - The predicate.
pub(super) fn not(p: Pred) -> Pred {
    match p {
        Pred::Is(b) => Pred::Is(!b),
        Pred::Not(q) => Rc::unwrap_or_clone(q),
        Pred::Undef => Pred::Undef,
        p => Pred::Not(Rc::new(p)),
    }
}

/// The predicate that a value is zero.
///
/// The difference of two sides is the value; its sign is chosen once, so
/// `a == b` and `b == a` are one predicate, and an exclusive or of two
/// values is zero exactly when their difference is.
///
/// # Arguments
///
/// * `t` - The value.
pub(super) fn zero(t: Term) -> Pred {
    match t {
        Term::Const(c) => Pred::Is(c == 0),
        Term::Undef => Pred::Undef,
        Term::Truth(p) => not(Rc::unwrap_or_clone(p)),
        Term::Logic(Logic::Xor, w, xs) if xs.len() == 2 => zero(sub(w, &xs[0], &xs[1])),
        Term::Poly(w, p) => {
            if let Some((a, b)) = sides(w, &p) {
                let k = a.fits().max(b.fits());
                if k < w {
                    return zero(sub(k, &a, &b));
                }
            }
            let flipped = neg(w, &Term::Poly(w, p.clone()));
            let kept = Term::Poly(w, p);
            Pred::Zero(if flipped < kept { flipped } else { kept })
        }
        t => Pred::Zero(t),
    }
}

/// The two sides of a sum that is one value less another, each a
/// variable's value or a constant.
///
/// Such a sum is zero exactly when the sides are equal, which a width
/// they both fit in decides as well as the sum's own.
///
/// # Arguments
///
/// * `w` - The sum's width.
/// * `p` - Its monomials.
///
/// # Returns
///
/// The sides, `None` for any other sum.
fn sides(w: u8, p: &[Monomial]) -> Option<(Term, Term)> {
    let m = low(w);
    let [(pa, ca), (pb, cb)] = p else {
        return None;
    };
    let one = |atoms: &[Term]| match atoms {
        [x] => Some(x.clone()),
        [] | [_, _, ..] => None,
    };
    match (pa.as_slice(), *ca, *cb) {
        ([], c, cb) if cb == m => Some((Term::Const(c), one(pb)?)),
        ([], c, 1) => Some((one(pb)?, Term::Const(c.wrapping_neg() & m))),
        (_, 1, cb) if cb == m => Some((one(pa)?, one(pb)?)),
        (_, ca, 1) if ca == m => Some((one(pb)?, one(pa)?)),
        (_, _, _) => None,
    }
}

/// The predicate `a < b`, unsigned, over values already at the compared
/// width.
///
/// # Arguments
///
/// * `a` - The left value.
/// * `b` - The right value.
pub(super) fn ult(a: Term, b: Term) -> Pred {
    if a == Term::Undef || b == Term::Undef {
        return Pred::Undef;
    }
    if let (Term::Const(x), Term::Const(y)) = (&a, &b) {
        return Pred::Is(x < y);
    }
    if b == Term::Const(0) || a == b {
        return Pred::Is(false);
    }
    if a == Term::Const(0) {
        return not(zero(b));
    }
    Pred::Ult(a, b)
}

/// The predicate `a < b`, signed at a width.
///
/// # Arguments
///
/// * `w` - The width, 1 to 64.
/// * `a` - The left value.
/// * `b` - The right value.
pub(super) fn slt(w: u8, a: &Term, b: &Term) -> Pred {
    if w == 0 {
        return Pred::Undef;
    }
    let (a, b) = (narrow(a, w), narrow(b, w));
    if a == Term::Undef || b == Term::Undef {
        return Pred::Undef;
    }
    if let (Term::Const(x), Term::Const(y)) = (&a, &b) {
        return match (sext(*x, w), sext(*y, w)) {
            (Some(x), Some(y)) => Pred::Is(x.cast_signed() < y.cast_signed()),
            (None, _) | (_, None) => Pred::Undef,
        };
    }
    if b == Term::Const(0) {
        return bit(w - 1, &a);
    }
    if a == b {
        return Pred::Is(false);
    }
    Pred::Slt(w, a, b)
}

/// The predicate that bit `i` of a value is set.
///
/// # Arguments
///
/// * `i` - The bit, 0 to 63.
/// * `t` - The value.
pub(super) fn bit(i: u8, t: &Term) -> Pred {
    let t = narrow(t, i.saturating_add(1));
    match t {
        Term::Undef => Pred::Undef,
        Term::Const(c) => Pred::Is(c >> i & 1 == 1),
        _ if t.fits() <= i => Pred::Is(false),
        t => Pred::Bit(i, t),
    }
}

/// The predicate that a float compare of two values has one of a set of
/// outcomes.
///
/// # Arguments
///
/// * `set` - The outcomes ([`LT`], [`EQ`], [`GT`], [`UN`]).
/// * `fb` - The values' width, 32 or 64.
/// * `a` - The left value's bits.
/// * `b` - The right value's bits.
pub(super) fn float_rel(set: u8, fb: u8, a: &Term, b: &Term) -> Pred {
    let (a, b) = (narrow(a, fb), narrow(b, fb));
    if matches!(a, Term::Undef) || matches!(b, Term::Undef) {
        return Pred::Undef;
    }
    if set & ALL == ALL {
        return Pred::Is(true);
    }
    if set & ALL == 0 {
        return Pred::Is(false);
    }
    if let (Term::Const(x), Term::Const(y)) = (&a, &b) {
        return Pred::Is(set & outcome(*x, *y, fb) != 0);
    }
    if b < a {
        let swapped = (set & (EQ | UN)) | (set & LT) << 2 | (set & GT) >> 2;
        return Pred::Float(swapped, fb, b, a);
    }
    Pred::Float(set, fb, a, b)
}

/// The outcome of a float compare of two values' bits.
///
/// # Arguments
///
/// * `a` - The left value's bits.
/// * `b` - The right value's bits.
/// * `fb` - Their width, 32 or 64.
fn outcome(a: u64, b: u64, fb: u8) -> u8 {
    let (x, y) = (float_of(a, fb), float_of(b, fb));
    if x.is_nan() || y.is_nan() {
        UN
    } else if x < y {
        LT
    } else if x > y {
        GT
    } else {
        EQ
    }
}

/// The value of an expression the replay's arithmetic folded to a
/// constant.
///
/// # Arguments
///
/// * `e` - The folded expression.
///
/// # Returns
///
/// The constant, `None` where the arithmetic has no value (a division by
/// zero, a bit scan of zero).
fn const_of(e: &Expr) -> Option<u64> {
    if let Expr::Const(v) = e {
        Some(*v)
    } else {
        None
    }
}

/// A concrete state a term is evaluated in: the variables' values, and
/// the bytes of memory drawn from a seed.
#[derive(Debug)]
pub(super) struct Point<'a> {
    /// The values of the variables where the block starts; one absent
    /// reads as drawn from the seed.
    pub(super) ins: &'a FxHashMap<Key, u64>,
    /// The seed of what is not given.
    pub(super) seed: u64,
    /// The register width, 32 or 64, an address wraps at.
    pub(super) width: u8,
}

impl Point<'_> {
    /// Returns a variable's value where the block starts.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    /// * `bits` - The bits it fits in.
    fn input(&self, k: Key, bits: u8) -> u64 {
        let drawn = || {
            let mut h = std::hash::DefaultHasher::new();
            std::hash::Hash::hash(&k, &mut h);
            mix(self.seed ^ std::hash::Hasher::finish(&h))
        };
        self.ins.get(&k).copied().unwrap_or_else(drawn) & low(bits)
    }

    /// Returns a byte of memory where the block starts.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn byte(&self, at: u64) -> u64 {
        mix(self.seed.rotate_left(29) ^ (at & low(self.width))) & 0xff
    }
}

/// Mixes bits, so neighbouring inputs give unrelated outputs.
///
/// # Arguments
///
/// * `x` - The input.
fn mix(mut x: u64) -> u64 {
    x ^= x >> 31;
    x = x.wrapping_mul(0x9e37_79b9_7f4a_7c15);
    x ^= x >> 29;
    x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^ (x >> 32)
}

/// Evaluates a term in a concrete state.
///
/// # Arguments
///
/// * `t` - The term.
/// * `at` - The state.
///
/// # Returns
///
/// The value, `None` where the replay's evaluation has none.
pub(super) fn value(t: &Term, at: &Point<'_>) -> Option<u64> {
    let c = Expr::Const;
    Some(match t {
        Term::Const(v) => *v,
        Term::In(k, b) => at.input(*k, *b),
        Term::Mem(a, n, d) => {
            let a = value(a, at)?;
            let mask = low(at.width);
            if u64::from(n.saturating_sub(1)) > mask - (a & mask) {
                return None;
            }
            let mut v = 0u64;
            for i in (0..u64::from(*n)).rev() {
                let x = a.wrapping_add(i) & mask;
                let byte = match d.binary_search_by_key(&x, |(k, _)| *k) {
                    Ok(j) => value(&d[j].1, at)? & 0xff,
                    Err(_) => at.byte(x),
                };
                v = v << 8 | byte;
            }
            v
        }
        Term::Undef => return None,
        Term::Poly(w, p) => {
            let mut sum = 0u64;
            for (m, k) in p {
                let mut prod = *k;
                for a in m {
                    prod = prod.wrapping_mul(value(a, at)?);
                }
                sum = sum.wrapping_add(prod);
            }
            sum & low(*w)
        }
        Term::Logic(op, w, xs) => {
            let mut acc = match op {
                Logic::And => u64::MAX,
                Logic::Or | Logic::Xor => 0,
            };
            for x in xs {
                let v = value(x, at)?;
                acc = match op {
                    Logic::And => acc & v,
                    Logic::Or => acc | v,
                    Logic::Xor => acc ^ v,
                };
            }
            acc & low(*w)
        }
        Term::Bin(op, w, a, b) => const_of(&fold(*op, c(value(a, at)?), c(value(b, at)?), *w))?,
        Term::Un(op, w, a) => const_of(&unary(*op, c(value(a, at)?), *w))?,
        Term::Sext(a, b) => sext(value(a, at)?, *b)?,
        Term::Truth(p) => u64::from(holds(p, at)?),
        Term::Ite(p, a, b) => {
            if holds(p, at)? {
                value(a, at)?
            } else {
                value(b, at)?
            }
        }
        Term::Float(op, fa, fb, a, b) => float_arith(
            *op,
            float_of(value(a, at)?, *fa),
            float_of(value(b, at)?, *fb),
            (*fa).max(*fb),
        )?,
        Term::FloatUn(op, fb, a) => float_un(*op, value(a, at)?, *fb)?,
        Term::ToInt(fb, bits, a) => float_to_int(value(a, at)?, *fb, *bits),
    })
}

/// Decides a predicate in a concrete state.
///
/// # Arguments
///
/// * `p` - The predicate.
/// * `at` - The state.
///
/// # Returns
///
/// Whether it holds, `None` where the replay's evaluation has no answer.
pub(super) fn holds(p: &Pred, at: &Point<'_>) -> Option<bool> {
    Some(match p {
        Pred::Is(b) => *b,
        Pred::Zero(t) => value(t, at)? == 0,
        Pred::Ult(a, b) => value(a, at)? < value(b, at)?,
        Pred::Slt(w, a, b) => {
            sext(value(a, at)?, *w)?.cast_signed() < sext(value(b, at)?, *w)?.cast_signed()
        }
        Pred::Bit(i, t) => value(t, at)? >> i & 1 == 1,
        Pred::Float(set, fb, a, b) => set & outcome(value(a, at)?, value(b, at)?, *fb) != 0,
        Pred::Not(q) => !holds(q, at)?,
        Pred::Undef => return None,
    })
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{
        EQ, GT, LT, Point, Pred, Term, UN, add, bin, const_of, float_rel, mul, narrow, sign_extend,
        sub, un, value, zero,
    };
    use crate::analysis::decompile::expr::{Expr, Key, Op, UnOp, fold, unary};
    use crate::analysis::decompile::verify::{low, sext};
    use crate::fxmap::FxHashMap;
    use crate::isa::x86::Register;

    /// A small expression over two variables, built once as a term and
    /// evaluated once with bits.
    #[derive(Debug)]
    enum Node {
        /// A variable, by index.
        X(usize),
        /// A constant.
        C(u64),
        /// An integer operator.
        Bin(Op, Box<Node>, Box<Node>),
        /// An integer unary operator.
        Un(UnOp, Box<Node>),
        /// The low bits.
        Low(Box<Node>, u8),
        /// The low bits sign-extended.
        Sext(Box<Node>, u8),
    }

    /// The variables the expressions read.
    const KEYS: [Key; 2] = [Key::Reg(Register::RAX), Key::Reg(Register::RCX)];

    /// A deterministic source of draws.
    struct Draw(u64);

    impl Draw {
        /// Returns the next draw.
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut x = self.0;
            x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            x ^ (x >> 31)
        }

        /// Returns a draw below `n`.
        ///
        /// # Arguments
        ///
        /// * `n` - The bound, above zero.
        fn below(&mut self, n: u64) -> usize {
            usize::try_from(self.next() % n).expect("small")
        }
    }

    /// Builds a random expression.
    ///
    /// # Arguments
    ///
    /// * `d` - The draws.
    /// * `depth` - How much deeper it may go.
    fn node(d: &mut Draw, depth: u8) -> Node {
        const OPS: [Op; 13] = [
            Op::Add,
            Op::Sub,
            Op::Mul,
            Op::And,
            Op::Or,
            Op::Xor,
            Op::Shl,
            Op::Shr,
            Op::Sar,
            Op::Div,
            Op::Rem,
            Op::SDiv,
            Op::SRem,
        ];
        const WIDTHS: [u8; 4] = [8, 16, 32, 1];
        if depth == 0 || d.below(4) == 0 {
            return if d.below(2) == 0 {
                Node::X(d.below(2))
            } else {
                Node::C([0, 1, 2, 3, 0xff, 0x8000_0000, u64::MAX, d.next()][d.below(8)])
            };
        }
        let sub = |d: &mut Draw| Box::new(node(d, depth - 1));
        let pick = d.below(5);
        if pick < 2 {
            let op = OPS[d.below(13)];
            let l = sub(d);
            let r = if matches!(op, Op::Shl | Op::Shr | Op::Sar) {
                Box::new(Node::C(d.next() % 70))
            } else {
                sub(d)
            };
            Node::Bin(op, l, r)
        } else if pick == 2 {
            Node::Un([UnOp::Neg, UnOp::Not, UnOp::Popcnt][d.below(3)], sub(d))
        } else if pick == 3 {
            Node::Low(sub(d), WIDTHS[d.below(4)])
        } else {
            Node::Sext(sub(d), WIDTHS[d.below(4)])
        }
    }

    /// Evaluates an expression with bits, as the replay does.
    ///
    /// # Arguments
    ///
    /// * `n` - The expression.
    /// * `xs` - The variables' values.
    /// * `w` - The register width.
    fn bits(n: &Node, xs: [u64; 2], w: u8) -> Option<u64> {
        Some(match n {
            Node::X(i) => xs[*i] & low(w),
            Node::C(c) => *c,
            Node::Bin(op, l, r) => const_of(&fold(
                *op,
                Expr::Const(bits(l, xs, w)?),
                Expr::Const(bits(r, xs, w)?),
                w,
            ))?,
            Node::Un(op, x) => const_of(&unary(*op, Expr::Const(bits(x, xs, w)?), w))?,
            Node::Low(x, b) => bits(x, xs, w)? & low(*b),
            Node::Sext(x, b) => sext(bits(x, xs, w)?, *b)?,
        })
    }

    /// Builds an expression as a term.
    ///
    /// # Arguments
    ///
    /// * `n` - The expression.
    /// * `w` - The register width.
    fn term(n: &Node, w: u8) -> Term {
        match n {
            Node::X(i) => Term::In(KEYS[*i], w),
            Node::C(c) => Term::Const(*c),
            Node::Bin(op, l, r) => bin(*op, w, &term(l, w), &term(r, w)),
            Node::Un(op, x) => un(*op, w, &term(x, w)),
            Node::Low(x, b) => narrow(&term(x, w), *b),
            Node::Sext(x, b) => sign_extend(&term(x, w), *b),
        }
    }

    /// A normal form has the value the replay's own arithmetic gives the
    /// expression it came from, wherever that arithmetic has one.
    ///
    /// The normalization is sound for every state, not only for the ones a
    /// test happens to try.
    #[test]
    fn normal_forms_evaluate_as_the_replays_arithmetic() {
        let mut d = Draw(7);
        for w in [64, 32] {
            for _ in 0..4000 {
                let n = node(&mut d, 4);
                let t = term(&n, w);
                for _ in 0..8 {
                    let xs = [d.next() >> d.below(64), d.next() >> d.below(64)];
                    let ins: FxHashMap<Key, u64> = KEYS.iter().copied().zip(xs).collect();
                    let at = Point {
                        ins: &ins,
                        seed: 1,
                        width: w,
                    };
                    if let Some(v) = bits(&n, xs, w) {
                        assert_eq!(value(&t, &at), Some(v), "{n:?} at {xs:x?}: {t:?}");
                    }
                }
            }
        }
    }

    /// Two spellings of one value are one term: a sum in any order, a
    /// product distributed, a mask of a value that fits, a compare either
    /// way round.
    #[test]
    fn two_spellings_of_one_value_are_one_term() {
        let x = Term::In(KEYS[0], 64);
        let y = Term::In(KEYS[1], 64);
        let one = Term::Const(1);
        assert_eq!(sub(64, &add(64, &x, &one), &x), one);
        assert_eq!(
            mul(64, &add(64, &x, &y), &Term::Const(2)),
            add(64, &add(64, &x, &x), &add(64, &y, &y))
        );
        let byte = Term::In(KEYS[0], 8);
        assert_eq!(bin(Op::And, 64, &byte, &Term::Const(0xff)), byte);
        assert_eq!(
            narrow(&add(64, &x, &one), 32),
            narrow(&add(32, &x, &one), 32)
        );
        assert_eq!(zero(sub(64, &x, &y)), zero(sub(64, &y, &x)));
        assert_eq!(
            zero(bin(Op::Xor, 32, &x, &y)),
            zero(narrow(&sub(64, &x, &y), 32))
        );
        assert_eq!(
            narrow(&sign_extend(&narrow(&x, 32), 32), 32),
            narrow(&x, 32)
        );
        assert_ne!(
            narrow(&add(64, &x, &one), 64),
            narrow(&add(32, &x, &one), 64)
        );
    }

    /// A float compare is the set of outcomes it holds for, so the same
    /// compare written with its operands swapped is one predicate, and a
    /// compare that differs only on a NaN is another.
    #[test]
    fn a_float_compare_is_its_set_of_outcomes() {
        let a = Term::In(KEYS[0], 64);
        let b = Term::In(KEYS[1], 64);
        let less = float_rel(LT, 64, &a, &b);
        assert_eq!(less, float_rel(GT, 64, &b, &a));
        assert_ne!(float_rel(LT | UN, 64, &a, &b), less);
        assert_eq!(float_rel(LT | EQ | GT | UN, 64, &a, &b), Pred::Is(true));
        let nan = Term::Const(f64::NAN.to_bits());
        assert_eq!(float_rel(UN, 64, &nan, &b), float_rel(UN, 64, &b, &nan));
        assert_eq!(
            float_rel(EQ, 64, &Term::Const(0), &Term::Const((-0.0f64).to_bits())),
            Pred::Is(true)
        );
    }
}
