//! The folder's algebra checked by enumeration, Alive-style without a
//! solver.
//!
//! Every rewrite [`fold`] and the constructors beside it apply is
//! compared with the expression it replaces, under an evaluator of this
//! module's own, on every 8-bit operand and on harvested and sampled
//! 32- and 64-bit ones.

use std::collections::BTreeMap;

use crate::isa::x86::{ConditionCode as C, Register};

use super::{
    Cc, Cond, Expr, Flags, Helper, Key, Op, Ty, UnOp, fold, lo64, mask, merge_bits, sign_extend,
    ternary, unary, without_addend,
};
use crate::num::{lo16, lo32};

mod builders;

use builders::builders;

/// The first variable.
const X: Expr = Expr::Var(Key::Reg(Register::RAX));

/// The second variable.
const Y: Expr = Expr::Var(Key::Reg(Register::RCX));

/// The entry stack pointer the evaluator gives `Sp` offsets.
const SP: u64 = 0x7ff0_1230;

/// The mask of the low `w` bits.
///
/// # Arguments
///
/// * `w` - The width.
fn lane(w: u8) -> u64 {
    u64::MAX >> (64 - u32::from(w.clamp(1, 64)))
}

/// The low `w` bits of `v` read as a signed number.
///
/// # Arguments
///
/// * `v` - The bits.
/// * `w` - The width.
fn signed(v: u64, w: u8) -> i128 {
    let v = i128::from(v & lane(w));
    if v >> (w - 1) & 1 == 1 {
        v - (1i128 << w)
    } else {
        v
    }
}

/// What `op` gives at width `w`, by the definitions the lifter states
/// for [`Op`], or `None` where it is undefined (a zero divisor, floats).
///
/// # Arguments
///
/// * `op` - The operator.
/// * `a` - Left operand.
/// * `b` - Right operand.
/// * `w` - The width of the operation.
fn bin(op: Op, a: u64, b: u64, w: u8) -> Option<u64> {
    let (ua, ub) = (u128::from(a & lane(w)), u128::from(b & lane(w)));
    let (sa, sb) = (signed(a, w), signed(b, w));
    let n = b % 64;
    let own = |hw: u8| (u128::from(a & lane(hw)), u128::from(b & lane(hw)));
    let rotl = |hw: u8, k: u64| {
        let (v, k) = (own(hw).0, k % u64::from(hw));
        ((v << k) | (v >> (u64::from(hw) - k))) & u128::from(lane(hw))
    };
    let v = match op {
        Op::Add => ua + ub,
        Op::Sub => ua.wrapping_sub(ub),
        Op::Mul => ua.wrapping_mul(ub),
        Op::Div => ua.checked_div(ub)?,
        Op::Rem => ua.checked_rem(ub)?,
        Op::SDiv => sa.checked_div(sb)?.cast_unsigned(),
        Op::SRem => sa.checked_rem(sb)?.cast_unsigned(),
        Op::And => ua & ub,
        Op::Or => ua | ub,
        Op::Xor => ua ^ ub,
        Op::Shl => ua << n,
        Op::Shr => ua >> n,
        Op::Sar => (sa >> n).cast_unsigned(),
        Op::Rol(hw) => rotl(hw, b),
        Op::Ror(hw) => rotl(hw, u64::from(hw) - b % u64::from(hw)),
        Op::MulHi(hw) => (own(hw).0 * own(hw).1) >> hw,
        Op::SMulHi(hw) => {
            ((signed(a, hw) * signed(b, hw)) >> hw).cast_unsigned() & u128::from(lane(hw))
        }
        Op::SMulO(hw) => {
            let p = signed(a, hw) * signed(b, hw);
            u128::from(p < -(1i128 << (hw - 1)) || p >= 1i128 << (hw - 1))
        }
        Op::UAddO(hw) => u128::from(own(hw).0 + own(hw).1 > u128::from(lane(hw))),
        Op::USubO(hw) => u128::from(own(hw).0 < own(hw).1),
        Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FMin | Op::FMax => return None,
    };
    Some(lo64(v) & lane(w))
}

/// What `op` gives at width `w`, or `None` where it is undefined (a bit
/// scan of zero, a byte swap of a byte, floats).
///
/// # Arguments
///
/// * `op` - The operator.
/// * `a` - The operand.
/// * `w` - The width of the operation.
fn un(op: UnOp, a: u64, w: u8) -> Option<u64> {
    let v = a & lane(w);
    let lz = v.leading_zeros() - (64 - u32::from(w));
    let v = match op {
        UnOp::Neg => v.wrapping_neg(),
        UnOp::Not => !v,
        UnOp::Bswap => match w {
            16 => u64::from(lo16(v).swap_bytes()),
            32 => u64::from(lo32(v).swap_bytes()),
            64 => v.swap_bytes(),
            _ => return None,
        },
        UnOp::Tzcnt => u64::from(v.trailing_zeros().min(u32::from(w))),
        UnOp::Bsf => u64::from((v != 0).then(|| v.trailing_zeros())?),
        UnOp::Lzcnt => u64::from(lz),
        UnOp::Bsr => u64::from((v != 0).then(|| u32::from(w) - 1 - lz)?),
        UnOp::Popcnt => u64::from(v.count_ones()),
        UnOp::Sqrt | UnOp::Fabs => return None,
    };
    Some(v & lane(w))
}

/// The truth of a condition, from the flags the processor would set,
/// or `None` where a flag it reads is not defined.
///
/// # Arguments
///
/// * `c` - The condition.
/// * `x` - The first variable's value.
/// * `y` - The second's.
fn truth(c: &Cond, x: u64, y: u64) -> Option<bool> {
    let v = |e: &Expr, w: u8| ev(e, w, x, y);
    let res = |r: u64, w: u8| {
        let r = r & lane(w);
        (
            r == 0,
            r >> (w - 1) & 1 == 1,
            (r & 0xff).count_ones().is_multiple_of(2),
        )
    };
    let (cf, (zf, sf, pf), of) = match &c.flags {
        Flags::Cmp(l, r, w) => {
            let (a, b) = (v(l, *w)?, v(r, *w)?);
            let d = a.wrapping_sub(b);
            let of = signed(a, *w) - signed(b, *w) != signed(d, *w);
            (Some(a & lane(*w) < b & lane(*w)), res(d, *w), Some(of))
        }
        Flags::Float(l, r, w) => {
            let f = |e: &Expr| -> Option<f64> {
                let bits = v(e, *w)?;
                Some(if *w == 32 {
                    f64::from(f32::from_bits(u32::try_from(bits).ok()?))
                } else {
                    f64::from_bits(bits)
                })
            };
            let (a, b) = (f(l)?, f(r)?);
            match a.partial_cmp(&b) {
                None => (Some(true), (true, false, true), None),
                Some(std::cmp::Ordering::Less) => (Some(true), (false, false, false), None),
                Some(std::cmp::Ordering::Equal) => (Some(false), (true, false, false), None),
                Some(std::cmp::Ordering::Greater) => (Some(false), (false, false, false), None),
            }
        }
        Flags::Test(l, r, w) => (Some(false), res(v(l, *w)? & v(r, *w)?, *w), Some(false)),
        Flags::Add(l, r, w) => {
            let (a, b) = (v(l, *w)?, v(r, *w)?);
            let s = a.wrapping_add(b);
            let wide = u128::from(a & lane(*w)) + u128::from(b & lane(*w));
            let of = signed(a, *w) + signed(b, *w) != signed(s, *w);
            (Some(wide > u128::from(lane(*w))), res(s, *w), Some(of))
        }
        Flags::Result(e, w) => (None, res(v(e, *w)?, *w), None),
        Flags::Carry(e) => {
            let set = v(e, 64)? != 0;
            return match c.cc.0 {
                C::b | C::o => Some(set),
                C::ae | C::no => Some(!set),
                _ => None,
            };
        }
        Flags::Truth(e, cc) => {
            let set = v(e, 64)? != 0;
            return if c.cc == *cc {
                Some(set)
            } else {
                (c.cc == cc.invert()).then_some(!set)
            };
        }
        Flags::FCmp(p, l, r, w) => {
            let f = |e: &Expr| -> Option<f64> {
                let bits = v(e, *w)?;
                Some(if *w == 32 {
                    f64::from(f32::from_bits(u32::try_from(bits).ok()?))
                } else {
                    f64::from_bits(bits)
                })
            };
            let held = p.holds(f(l)?, f(r)?);
            return match c.cc.0 {
                C::ne => Some(held),
                C::e => Some(!held),
                _ => None,
            };
        }
        Flags::Shift(..) | Flags::Unknown => return None,
    };
    let lt = || Some(sf != of?);
    Some(match c.cc.0 {
        C::o => of?,
        C::no => !of?,
        C::b => cf?,
        C::ae => !cf?,
        C::e => zf,
        C::ne => !zf,
        C::be => cf? || zf,
        C::a => !cf? && !zf,
        C::s => sf,
        C::ns => !sf,
        C::p => pf,
        C::np => !pf,
        C::l => lt()?,
        C::ge => !lt()?,
        C::le => zf || lt()?,
        C::g => !zf && !lt()?,
        C::None => return None,
    })
}

/// The value of `e` with every operation at width `w`, or `None` where
/// it is undefined or not modeled here.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `w` - The width its operations run at.
/// * `x` - The first variable's value.
/// * `y` - The second's.
fn ev(e: &Expr, w: u8, x: u64, y: u64) -> Option<u64> {
    let v = |e: &Expr| ev(e, w, x, y);
    Some(match e {
        Expr::Const(c) => *c,
        Expr::Var(Key::Reg(Register::RAX)) => x,
        Expr::Var(Key::Reg(Register::RCX)) => y,
        Expr::Var(Key::Reg(Register::EAX)) => x & 0xffff_ffff,
        Expr::Sp(k) => SP.wrapping_add_signed(*k),
        Expr::Bin(op, l, r) => bin(*op, v(l)?, v(r)?, w)?,
        Expr::Un(op, a) => un(*op, v(a)?, w)?,
        Expr::Sext(a, bits) => lo64(signed(v(a)?, *bits).cast_unsigned()),
        Expr::Deref(a, ty) => v(a)?.wrapping_mul(0x9e37_79b9_7f4a_7c15) & lane(ty.bits()),
        Expr::Cond(c) => u64::from(truth(c, x, y)?),
        Expr::Ternary(c, a, b) => v(if truth(c, x, y)? { a } else { b })?,
        Expr::Helper(h, args) => {
            let vals = args.iter().map(v).collect::<Option<Vec<u64>>>()?;
            h.eval(&vals, w, w)?
        }
        _ => return None,
    })
}

/// Builds `l op r` without folding.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - Left operand.
/// * `r` - Right operand.
fn b(op: Op, l: &Expr, r: &Expr) -> Expr {
    Expr::Bin(op, Box::new(l.clone()), Box::new(r.clone()))
}

/// Builds a constant.
///
/// # Arguments
///
/// * `c` - Its value.
fn k(c: u64) -> Expr {
    Expr::Const(c)
}

/// Builds a complement.
///
/// # Arguments
///
/// * `e` - The expression complemented.
fn u(e: Expr) -> Expr {
    Expr::Un(UnOp::Not, Box::new(e))
}

/// Every rewrite seen and the first counterexample found to each.
#[derive(Default)]
struct Tally {
    /// How often each rewrite was handed its shape, and how often it
    /// changed it.
    fired: BTreeMap<&'static str, (usize, usize)>,
    /// The first counterexample to each rewrite that has one.
    fails: BTreeMap<&'static str, String>,
}

impl Tally {
    /// Compares `after` with `before` on every pair of values, noting
    /// the first pair they differ on in the low `w` bits.
    ///
    /// # Arguments
    ///
    /// * `name` - The rewrite.
    /// * `before` - The expression as handed in.
    /// * `after` - What the rewrite made of it.
    /// * `w` - The width both are evaluated at.
    /// * `xs` - The first variable's values.
    /// * `ys` - The second's.
    fn same(
        &mut self,
        name: &'static str,
        before: &Expr,
        after: &Expr,
        w: u8,
        xs: &[u64],
        ys: &[u64],
    ) {
        let seen = self.fired.entry(name).or_default();
        seen.0 += 1;
        seen.1 += usize::from(after != before);
        if self.fails.contains_key(name) {
            return;
        }
        for &x in xs {
            for &y in ys {
                let Some(want) = ev(before, w, x, y) else {
                    continue;
                };
                let got = ev(after, w, x, y);
                if got.is_none_or(|g| (g ^ want) & lane(w) != 0) {
                    self.fails.insert(
                        name,
                        format!(
                            "{before:?} became {after:?} at width {w}: x={x:#x} y={y:#x} gives {got:x?}, not {want:#x}"
                        ),
                    );
                    return;
                }
            }
        }
    }

    /// Folds `l op r` at width `w` and compares it with the unfolded node.
    ///
    /// # Arguments
    ///
    /// * `name` - The rewrite.
    /// * `op` - The operator.
    /// * `l` - Left operand.
    /// * `r` - Right operand.
    /// * `w` - The width of the operation.
    /// * `xs` - The first variable's values.
    /// * `ys` - The second's.
    fn fold(
        &mut self,
        name: &'static str,
        (op, l, r): (Op, Expr, Expr),
        w: u8,
        xs: &[u64],
        ys: &[u64],
    ) {
        let before = b(op, &l, &r);
        self.same(name, &before, &fold(op, l, r, w), w, xs, ys);
    }

    /// Requires no counterexample, and every rewrite to have changed at
    /// least one expression it was handed: a shape that never fires
    /// checks nothing.
    fn verdict(&self) {
        let idle: Vec<&str> = self
            .fired
            .iter()
            .filter(|(_, (_, changed))| *changed == 0)
            .map(|(name, _)| *name)
            .collect();
        assert!(
            self.fails.is_empty() && idle.is_empty(),
            "counterexamples: {:#?}\nshapes never rewritten: {idle:?}",
            self.fails
        );
    }
}

/// Harvested 64-bit values: zero, one, each width's signed and unsigned
/// edges, every power of two and its neighbours, their negations, and a
/// seeded spread of others.
fn harvest() -> Vec<u64> {
    let mut v = vec![0, 1, 2, 3, 5, 7, 10, 0x55, 0xaa, 0xdead_beef];
    for w in [8u8, 16, 32, 64] {
        let top = 1u64 << (w - 1);
        v.extend([top - 1, top, top + 1, lane(w), lane(w) - 1]);
    }
    for s in 0..64 {
        v.extend([1u64 << s, (1u64 << s) - 1, (1u64 << s) + 1]);
    }
    let mut seed = 0x0123_4567_89ab_cdefu64;
    for _ in 0..24 {
        seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        v.push(z ^ (z >> 31));
    }
    let negated: Vec<u64> = v.iter().map(|x| x.wrapping_neg()).collect();
    v.extend(negated);
    v.sort_unstable();
    v.dedup();
    v
}

/// The values the checks at one width run over.
struct Domain {
    /// The width.
    w: u8,
    /// The first variable's values.
    xs: Vec<u64>,
    /// The second variable's values where the first is swept too.
    ys: Vec<u64>,
    /// The first constant's values.
    cs: Vec<u64>,
    /// A second constant's, and the second variable's beside a constant.
    ds: Vec<u64>,
}

/// Every operator with an integer meaning, at width `w`.
///
/// # Arguments
///
/// * `w` - The width the width-carrying operators take.
fn ops(w: u8) -> [Op; 20] {
    [
        Op::Add,
        Op::Sub,
        Op::Mul,
        Op::Div,
        Op::Rem,
        Op::SDiv,
        Op::SRem,
        Op::And,
        Op::Or,
        Op::Xor,
        Op::Shl,
        Op::Shr,
        Op::Sar,
        Op::Rol(w),
        Op::Ror(w),
        Op::MulHi(w),
        Op::SMulHi(w),
        Op::SMulO(w),
        Op::UAddO(w),
        Op::USubO(w),
    ]
}

/// Every condition code.
const CCS: [C; 16] = [
    C::o,
    C::no,
    C::b,
    C::ae,
    C::e,
    C::ne,
    C::be,
    C::a,
    C::s,
    C::ns,
    C::p,
    C::np,
    C::l,
    C::ge,
    C::le,
    C::g,
];

/// Builds a condition.
///
/// # Arguments
///
/// * `cc` - The condition code.
/// * `flags` - What set the flags.
fn cond(cc: C, flags: Flags) -> Cond {
    Cond { cc: Cc(cc), flags }
}

/// Constant folding, the local identities, like terms, constant
/// re-association, remainders and the stack-address arithmetic of
/// [`fold`].
///
/// # Arguments
///
/// * `t` - The tally.
/// * `d` - The values.
fn local(t: &mut Tally, d: &Domain) {
    let (w, xs, ys, one) = (d.w, d.xs.as_slice(), d.ys.as_slice(), &[0u64][..]);
    for (name, op, l, r) in [
        ("x ^ x", Op::Xor, X, X),
        ("x - x", Op::Sub, X, X),
        ("x + 0", Op::Add, X, k(0)),
        ("x - 0", Op::Sub, X, k(0)),
        ("x | 0", Op::Or, X, k(0)),
        ("x ^ 0", Op::Xor, X, k(0)),
        ("x << 0", Op::Shl, X, k(0)),
        ("x >> 0", Op::Shr, X, k(0)),
        ("x sar 0", Op::Sar, X, k(0)),
        ("x * 1", Op::Mul, X, k(1)),
        ("x / 1", Op::Div, X, k(1)),
        ("x sdiv 1", Op::SDiv, X, k(1)),
        ("uaddo(x, 0)", Op::UAddO(w), X, k(0)),
        ("usubo(x, 0)", Op::USubO(w), X, k(0)),
        ("x & 0", Op::And, X, k(0)),
        ("0 & x", Op::And, k(0), X),
        ("x * 0", Op::Mul, X, k(0)),
        ("0 * x", Op::Mul, k(0), X),
        ("0 + x", Op::Add, k(0), X),
        ("0 | x", Op::Or, k(0), X),
        ("0 ^ x", Op::Xor, k(0), X),
        ("0 - x", Op::Sub, k(0), X),
        ("x + x", Op::Add, X, X),
    ] {
        t.fold(name, (op, l, r), w, xs, one);
    }
    for &c in &d.cs {
        for op in ops(w) {
            for &e in xs {
                t.fold("constant folding", (op, k(c), k(e)), w, one, one);
            }
        }
        let s = c % 64;
        for (name, op, l, r) in [
            ("x & c", Op::And, X, k(c)),
            ("x | c", Op::Or, X, k(c)),
            ("c | x", Op::Or, k(c), X),
            ("x - c", Op::Sub, X, k(c)),
            ("sp + c", Op::Add, Expr::Sp(-0x28), k(c)),
            ("c + sp", Op::Add, k(c), Expr::Sp(0x10)),
            ("sp - c", Op::Sub, Expr::Sp(-8), k(c)),
            ("x + x * c", Op::Add, X, b(Op::Mul, &X, &k(c))),
            ("x * c + x", Op::Add, b(Op::Mul, &X, &k(c)), X),
            ("x * c - x", Op::Sub, b(Op::Mul, &X, &k(c)), X),
            ("x - x * c", Op::Sub, X, b(Op::Mul, &X, &k(c))),
            ("(x << s) + x", Op::Add, b(Op::Shl, &X, &k(s)), X),
            ("x - (x << s)", Op::Sub, X, b(Op::Shl, &X, &k(s))),
            (
                "x - x / c * c",
                Op::Sub,
                X,
                b(Op::Mul, &b(Op::Div, &X, &k(c)), &k(c)),
            ),
            (
                "x - c * x / c",
                Op::Sub,
                X,
                b(Op::Mul, &k(c), &b(Op::Div, &X, &k(c))),
            ),
            (
                "x - x sdiv c * c",
                Op::Sub,
                X,
                b(Op::Mul, &b(Op::SDiv, &X, &k(c)), &k(c)),
            ),
            (
                "x + x / c * -c",
                Op::Add,
                X,
                b(Op::Mul, &b(Op::Div, &X, &k(c)), &k(c.wrapping_neg())),
            ),
            (
                "x sdiv c * -c + x",
                Op::Add,
                b(Op::Mul, &k(c.wrapping_neg()), &b(Op::SDiv, &X, &k(c))),
                X,
            ),
        ] {
            t.fold(name, (op, l, r), w, xs, one);
        }
        for &e in &d.ds {
            for (name, op, l, r) in [
                ("(x + c) + e", Op::Add, b(Op::Add, &X, &k(c)), k(e)),
                (
                    "x * c + x * e",
                    Op::Add,
                    b(Op::Mul, &X, &k(c)),
                    b(Op::Mul, &X, &k(e)),
                ),
                (
                    "x * c - x * e",
                    Op::Sub,
                    b(Op::Mul, &X, &k(c)),
                    b(Op::Mul, &X, &k(e)),
                ),
                ("(x * c) * e", Op::Mul, b(Op::Mul, &X, &k(c)), k(e)),
                ("(x << s) * e", Op::Mul, b(Op::Shl, &X, &k(s)), k(e)),
            ] {
                t.fold(name, (op, l, r), w, xs, one);
            }
        }
        t.fold(
            "(x + c) - y",
            (Op::Sub, b(Op::Add, &X, &k(c)), Y),
            w,
            xs,
            &d.ds,
        );
    }
    for cc in CCS {
        for &c in &d.ds {
            let test = Expr::Cond(Box::new(cond(cc, Flags::Cmp(Y, k(c), w))));
            let neg = Expr::Un(UnOp::Neg, Box::new(test.clone()));
            t.fold("-(c) & x", (Op::And, neg, X), w, xs, &d.ds);
            t.fold(
                "x & (0 - c)",
                (Op::And, X, b(Op::Sub, &k(0), &test)),
                w,
                xs,
                &d.ds,
            );
        }
    }
    let word = |e: &Expr| Expr::Sext(Box::new(e.clone()), 32);
    for (name, div) in [("x - x / y * y", Op::Div), ("x - x sdiv y * y", Op::SDiv)] {
        let rem = b(Op::Sub, &X, &b(Op::Mul, &b(div, &X, &Y), &Y));
        if let Expr::Bin(op, l, r) = rem {
            t.fold(name, (op, *l, *r), w, xs, ys);
        }
    }
    if w <= 32 {
        let quot = b(Op::SDiv, &word(&X), &word(&Y));
        t.fold(
            "x - sext(x) sdiv sext(y) * y",
            (Op::Sub, X, b(Op::Mul, &quot, &Y)),
            w,
            xs,
            ys,
        );
        for &c in &d.cs {
            let quot = b(Op::SDiv, &word(&X), &k(c));
            t.fold(
                "x + sext(x) sdiv c * -c",
                (
                    Op::Add,
                    X,
                    b(Op::Mul, &quot, &k(c.wrapping_neg() & lane(w))),
                ),
                w,
                xs,
                one,
            );
        }
    }
    for (name, op, l, r) in [
        (
            "(x ^ y) + (x & y) * 2",
            Op::Add,
            b(Op::Xor, &X, &Y),
            b(Op::Mul, &b(Op::And, &X, &Y), &k(2)),
        ),
        (
            "(y & x) << 1 + (x ^ y)",
            Op::Add,
            b(Op::Shl, &b(Op::And, &Y, &X), &k(1)),
            b(Op::Xor, &X, &Y),
        ),
        (
            "(x ^ y) + 2 * (y & x)",
            Op::Add,
            b(Op::Xor, &X, &Y),
            b(Op::Mul, &k(2), &b(Op::And, &Y, &X)),
        ),
        (
            "(x & y) + (x | y)",
            Op::Add,
            b(Op::And, &X, &Y),
            b(Op::Or, &X, &Y),
        ),
        (
            "(y | x) + (x & y)",
            Op::Add,
            b(Op::Or, &Y, &X),
            b(Op::And, &X, &Y),
        ),
        (
            "(x ^ y) + (y & x)",
            Op::Add,
            b(Op::Xor, &X, &Y),
            b(Op::And, &Y, &X),
        ),
        (
            "(x & y) + (x ^ y)",
            Op::Add,
            b(Op::And, &X, &Y),
            b(Op::Xor, &X, &Y),
        ),
        (
            "(x | y) - (y & x)",
            Op::Sub,
            b(Op::Or, &X, &Y),
            b(Op::And, &Y, &X),
        ),
        (
            "(x | y) - (x ^ y)",
            Op::Sub,
            b(Op::Or, &X, &Y),
            b(Op::Xor, &X, &Y),
        ),
        (
            "2 * (x & y) + (x ^ y) - (x & y)",
            Op::Sub,
            b(
                Op::Add,
                &b(Op::Mul, &k(2), &b(Op::And, &X, &Y)),
                &b(Op::Xor, &X, &Y),
            ),
            b(Op::And, &X, &Y),
        ),
        (
            "(x & ~y) + (x & y) + 5",
            Op::Add,
            b(Op::Add, &b(Op::And, &X, &u(Y.clone())), &b(Op::And, &X, &Y)),
            k(5),
        ),
        (
            "(x | y) - (x & y) - (x ^ y)",
            Op::Sub,
            b(Op::Sub, &b(Op::Or, &X, &Y), &b(Op::And, &X, &Y)),
            b(Op::Xor, &X, &Y),
        ),
        (
            "~(x ^ y) & (x | y)",
            Op::And,
            u(b(Op::Xor, &X, &Y)),
            b(Op::Or, &X, &Y),
        ),
    ] {
        t.fold(name, (op, l, r), w, xs, ys);
    }
    for (name, op, l, r) in [
        (
            "(x ^ y) + ((x & y) << 1) - (x & y)",
            Op::Sub,
            b(
                Op::Add,
                &b(Op::Xor, &X, &Y),
                &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
            ),
            b(Op::And, &X, &Y),
        ),
        (
            "(x & ~y) - (~x & y)",
            Op::Sub,
            b(Op::And, &X, &u(Y.clone())),
            b(Op::And, &u(X.clone()), &Y),
        ),
        (
            "(x | y) + (x & y) - (x + y)",
            Op::Sub,
            b(Op::Add, &b(Op::Or, &X, &Y), &b(Op::And, &X, &Y)),
            b(Op::Add, &X, &Y),
        ),
        ("~x + y + 1", Op::Add, b(Op::Add, &u(X.clone()), &Y), k(1)),
    ] {
        t.fold(name, (op, l, r), w, xs, ys);
    }
    let top = k(u64::from(w) - 1);
    let scan = Expr::Un(UnOp::Bsr, Box::new(X));
    t.fold(
        "bsr(x) ^ (w - 1)",
        (Op::Xor, scan.clone(), top.clone()),
        w,
        xs,
        one,
    );
    t.fold(
        "(w - 1) ^ bsr(x)",
        (Op::Xor, top.clone(), scan.clone()),
        w,
        xs,
        one,
    );
    t.fold("(w - 1) - bsr(x)", (Op::Sub, top, scan), w, xs, one);
}

/// The general MBA collapse under attack: shapes that smuggle a
/// non-linear step past the linear gate, sign-extension layers, stack
/// slots as variables, and constants above the width.
///
/// Every row is a shape the collapse either rewrites or must refuse;
/// [`fold`] comparing it with the unfolded node on the domain's values
/// is the ground truth either way. Rows that must come back unchanged
/// are pinned structurally in [`mba_refusals_stay_unfolded`].
///
/// # Arguments
///
/// * `t` - The tally.
/// * `d` - The values.
fn mba_stress(t: &mut Tally, d: &Domain) {
    let (w, xs, ys, one) = (d.w, d.xs.as_slice(), d.ys.as_slice(), &[0u64][..]);
    let sext = |e: Expr| Expr::Sext(Box::new(e), w);
    for (name, op, l, r, sweep) in [
        (
            "(x & ~y) + (~x & y) + ((x & y) << 1)",
            Op::Add,
            b(
                Op::Add,
                &b(Op::And, &X, &u(Y.clone())),
                &b(Op::And, &u(X.clone()), &Y),
            ),
            b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
            ys,
        ),
        (
            "(x ^ y) + (x & y) + (x & y)",
            Op::Add,
            b(Op::Add, &b(Op::Xor, &X, &Y), &b(Op::And, &X, &Y)),
            b(Op::And, &X, &Y),
            ys,
        ),
        (
            "sext(x ^ y) + sext((x & y) << 1)",
            Op::Add,
            sext(b(Op::Xor, &X, &Y)),
            sext(b(Op::Shl, &b(Op::And, &X, &Y), &k(1))),
            ys,
        ),
        (
            "sext(~(x + c))",
            Op::Add,
            sext(u(b(Op::Add, &X, &k(0x5a)))),
            k(0),
            one,
        ),
        (
            "~(~(x + c)) + c",
            Op::Add,
            u(u(b(Op::Add, &X, &k(7)))),
            k(7),
            one,
        ),
        (
            "(x ^ above) ^ above",
            Op::Xor,
            b(Op::Xor, &X, &k(lane(w).wrapping_add(3))),
            k(lane(w).wrapping_add(3)),
            one,
        ),
        ("~(x + c) + 1", Op::Add, u(b(Op::Add, &X, &k(9))), k(1), one),
        (
            "(sp ^ y) + ((sp & y) << 1)",
            Op::Add,
            b(Op::Xor, &Expr::Sp(-0x28), &Y),
            b(Op::Shl, &b(Op::And, &Expr::Sp(-0x28), &Y), &k(1)),
            ys,
        ),
        (
            "(x | y) - (x & y) - 1",
            Op::Sub,
            b(Op::Sub, &b(Op::Or, &X, &Y), &b(Op::And, &X, &Y)),
            k(1),
            ys,
        ),
    ] {
        t.fold(name, (op, l, r), w, xs, sweep);
    }
    for &c in &d.cs {
        t.fold(
            "(x ^ c) ^ c",
            (Op::Xor, b(Op::Xor, &X, &k(c)), k(c)),
            w,
            xs,
            one,
        );
    }
    let pad = b(Op::Xor, &b(Op::And, &X, &Y), &b(Op::And, &X, &Y));
    let mut capped = b(
        Op::Add,
        &b(Op::Xor, &X, &Y),
        &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
    );
    for _ in 0..2 {
        capped = b(Op::Add, &capped, &pad.clone());
    }
    t.fold("x + y at the node cap", (Op::Add, capped, k(0)), w, xs, ys);
}

/// The MBA collapse's rows hold at width 16, between the exhaustive
/// byte sweep and the sampled words, where the negative-looking
/// constants `0xff` and `0xfe` sit inside the lane.
///
/// # Panics
///
/// When a rewrite changed a row's value.
#[test]
fn mba_rows_hold_at_16_bits() {
    let wide = harvest();
    let pick: Vec<u64> = wide.iter().copied().step_by(7).collect();
    let d = Domain {
        w: 16,
        xs: wide,
        ys: pick.clone(),
        cs: pick.clone(),
        ds: pick,
    };
    let mut t = Tally::default();
    mba_stress(&mut t, &d);
    assert!(t.fails.is_empty(), "counterexamples: {:#?}", t.fails);
}

/// The divisions a compiler strength-reduces, as [`fold`] reverses them.
///
/// # Arguments
///
/// * `t` - The tally.
/// * `w` - The width.
/// * `magics` - The multipliers and shifts to try.
/// * `xs` - The dividends.
fn divisions(t: &mut Tally, w: u8, magics: &[(u64, u64)], xs: &[u64]) {
    let one = [0u64];
    for &(m, s) in magics {
        let hi = b(Op::MulHi(w), &k(m), &X);
        t.fold("mulhi(m, x) >> s", (Op::Shr, hi.clone(), k(s)), w, xs, &one);
        let quot = fold(Op::MulHi(w), k(m), X, w);
        t.fold("x / d >> s", (Op::Shr, quot, k(s)), w, xs, &one);
        t.fold(
            "mulhi(x, m) >> s",
            (Op::Shr, b(Op::MulHi(w), &X, &k(m)), k(s)),
            w,
            xs,
            &one,
        );
        if s >= 1 {
            let half = b(Op::Shr, &b(Op::Sub, &X, &hi), &k(1));
            t.fold(
                "((x - hi) >> 1 + hi) >> s",
                (Op::Shr, b(Op::Add, &half, &hi), k(s - 1)),
                w,
                xs,
                &one,
            );
            t.fold(
                "(hi + (x - hi) >> 1) >> s",
                (Op::Shr, b(Op::Add, &hi, &half), k(s - 1)),
                w,
                xs,
                &one,
            );
            let x5 = b(Op::Add, &X, &k(5));
            let hi5 = b(Op::MulHi(w), &k(m), &x5);
            let half5 = b(Op::Shr, &b(Op::Add, &b(Op::Sub, &X, &hi5), &k(5)), &k(1));
            t.fold(
                "((x - hi) + 5 >> 1 + hi) >> s",
                (Op::Shr, b(Op::Add, &half5, &hi5), k(s - 1)),
                w,
                xs,
                &one,
            );
        }
        let shi = b(Op::SMulHi(w), &k(m), &X);
        let sar = |e: &Expr| {
            if s == 0 {
                e.clone()
            } else {
                b(Op::Sar, e, &k(s))
            }
        };
        let quotients = [
            ("smulhi(m, x) sar s", sar(&shi)),
            ("(smulhi(m, x) + x) sar s", sar(&b(Op::Add, &shi, &X))),
            (
                "sext(smulhi(m, x)) sar s",
                sar(&Expr::Sext(Box::new(shi.clone()), w)),
            ),
        ];
        let sign = |e: &Expr| b(Op::Shr, e, &k(u64::from(w) - 1));
        for (name, q) in quotients {
            t.fold(name, (Op::Shr, q.clone(), k(u64::from(w) - 1)), w, xs, &one);
            t.fold(
                "q + (q >> w - 1)",
                (Op::Add, q.clone(), sign(&q)),
                w,
                xs,
                &one,
            );
            t.fold(
                "(q >> w - 1) + q",
                (Op::Add, sign(&q), q.clone()),
                w,
                xs,
                &one,
            );
            t.fold(
                "q + (x >> w - 1)",
                (Op::Add, q.clone(), sign(&X)),
                w,
                xs,
                &one,
            );
            let masked = b(Op::And, &q, &k(lane(w)));
            t.fold(
                "q + ((q & lane) >> w - 1)",
                (Op::Add, q.clone(), sign(&masked)),
                w,
                xs,
                &one,
            );
        }
    }
}

/// The quotients read off the whole 64-bit product of a word.
///
/// As [`fold`] reverses them: clang's `imul` of a sign-extended word,
/// its high word shifted and its sign added, and arm64's `smull` and
/// `umull`, the dividend added back to a negative magic's high word.
///
/// # Arguments
///
/// * `t` - The tally.
/// * `magics` - The 32-bit multipliers and shifts to try.
/// * `xs` - The dividends.
fn wide_quotients(t: &mut Tally, magics: &[(u64, u64)], xs: &[u64]) {
    let one = [0u64];
    let word = 0xffff_ffff;
    for &(m, s) in magics {
        let c = lo64(signed(m, 32).cast_unsigned());
        let p = b(Op::Mul, &Expr::Sext(Box::new(X), 32), &k(c));
        t.fold(
            "sext(x) * c >> k",
            (Op::Shr, p.clone(), k(32 + s)),
            64,
            xs,
            &one,
        );
        t.fold(
            "sext(x) * c sar k",
            (Op::Sar, p.clone(), k(32 + s)),
            64,
            xs,
            &one,
        );
        let u = b(Op::Mul, &b(Op::And, &X, &k(word)), &k(m));
        t.fold("(x & word) * c >> k", (Op::Shr, u, k(32 + s)), 64, xs, &one);
        let q = fold(Op::Sar, p.clone(), k(32 + s), 64);
        let sign = fold(Op::Shr, p.clone(), k(63), 64);
        t.fold("q + (p >> 63)", (Op::Add, q, sign), 64, xs, &one);
        let hi = fold(Op::Shr, p, k(32), 64);
        let sum = fold(Op::Add, b(Op::And, &X, &k(word)), hi, 64);
        let q = fold(Op::Sar, sign_extend(sum.clone(), 32), k(s), 64);
        let fix = fold(Op::Shr, mask(sum, word), k(31), 64);
        t.fold("q + ((x + hi) >> 31)", (Op::Add, q, fix), 32, xs, &one);
    }
}

/// The signed divisions by powers of two a compiler writes as shifts,
/// as [`fold`] reverses them.
///
/// # Arguments
///
/// * `t` - The tally.
/// * `w` - The width.
/// * `xs` - The dividends.
fn power_quotients(t: &mut Tally, w: u8, xs: &[u64]) {
    let one = [0u64];
    let signs = [
        b(Op::Sar, &X, &k(63)),
        b(Op::Sar, &Expr::Sext(Box::new(X), 32), &k(31)),
    ];
    for kk in 1..u64::from(w) {
        for sign in &signs {
            let fix = b(Op::And, sign, &k((1u64 << kk) - 1));
            for inner in [b(Op::Add, &X, &fix), b(Op::Add, &fix, &X)] {
                t.fold(
                    "(x + (sign & 2^k - 1)) sar k",
                    (Op::Sar, inner.clone(), k(kk)),
                    w,
                    xs,
                    &one,
                );
                let lane_of = Expr::Sext(Box::new(inner), 32);
                t.fold(
                    "sext(x + (sign & 2^k - 1)) sar k",
                    (Op::Sar, lane_of, k(kk)),
                    w,
                    xs,
                    &one,
                );
            }
        }
    }
    for sign in &signs {
        t.fold(
            "(x - sign) sar 1",
            (Op::Sar, b(Op::Sub, &X, sign), k(1)),
            w,
            xs,
            &one,
        );
    }
    for top in [31, 63] {
        let bit = b(Op::Shr, &X, &k(top));
        t.fold(
            "(x + (x >> top)) sar 1",
            (Op::Sar, b(Op::Add, &X, &bit), k(1)),
            w,
            xs,
            &one,
        );
        t.fold(
            "((x >> top) + x) sar 1",
            (Op::Sar, b(Op::Add, &bit, &X), k(1)),
            w,
            xs,
            &one,
        );
    }
}

/// Every rewrite the folder applies holds on every 8-bit operand.
///
/// Each shape is folded with every constant and every value of its
/// first variable, and a second variable runs over every value or a
/// spread of edges, as the shape's size allows.
#[test]
fn every_rewrite_of_the_folder_holds_on_every_byte() {
    let all: Vec<u64> = (0..=255).collect();
    let edges = vec![0, 1, 2, 3, 0x7e, 0x7f, 0x80, 0x81, 0xfe, 0xff];
    let d = Domain {
        w: 8,
        xs: all.clone(),
        ys: all.clone(),
        cs: all.clone(),
        ds: edges,
    };
    let mut t = Tally::default();
    local(&mut t, &d);
    mba_stress(&mut t, &d);
    builders(&mut t, &d);
    let magics: Vec<(u64, u64)> = (0..=255)
        .flat_map(|m| (0..8).map(move |s| (m, s)))
        .collect();
    divisions(&mut t, 8, &magics, &all);
    t.verdict();
}

/// Every rewrite the folder applies holds at 32 and 64 bits.
///
/// The operands are harvested (zero, one, minus one, each width's
/// signed and unsigned limits, powers of two and their neighbours) or
/// seeded; the division idioms run over the multipliers a compiler
/// would pick for a spread of divisors at every shift, and over the
/// dividends just below each multiple of the divisor near the top of
/// the range, where an inexact multiplier first goes wrong.
#[test]
fn every_rewrite_of_the_folder_holds_on_sampled_words() {
    let wide = harvest();
    let pick: Vec<u64> = wide.iter().copied().step_by(13).collect();
    let divisors = [
        3u64,
        5,
        6,
        7,
        9,
        10,
        11,
        12,
        13,
        25,
        60,
        100,
        641,
        1000,
        86_400,
        1_000_000_007,
        0x7fff_ffff,
    ];
    let mut t = Tally::default();
    for w in [32u8, 64] {
        let d = Domain {
            w,
            xs: wide.clone(),
            ys: pick.clone(),
            cs: pick.clone(),
            ds: pick.iter().copied().step_by(3).collect(),
        };
        local(&mut t, &d);
        mba_stress(&mut t, &d);
        builders(&mut t, &d);
        power_quotients(&mut t, w, &wide);
        let mut xs = wide.clone();
        let mut magics = Vec::new();
        for dv in divisors.into_iter().filter(|dv| *dv < 1 << (w - 1)) {
            for top in [lane(w), lane(w) >> 1] {
                let q = top / dv;
                xs.extend([q * dv - 1, q * dv, (q - 1) * dv + dv - 1]);
                xs.extend([(q * dv - 1).wrapping_neg(), (q * dv).wrapping_neg()]);
            }
            for s in 0..u64::from(w) {
                let pow = 1u128 << (u64::from(w) + s);
                if let Ok(m) = u64::try_from(pow.div_ceil(u128::from(dv)))
                    && m <= lane(w)
                {
                    magics.push((m, s));
                }
            }
        }
        if w == 32 {
            wide_quotients(&mut t, &magics, &xs);
        }
        for &(m, _) in &magics {
            t.fold("mulhi(m, x)", (Op::MulHi(w), k(m), X), w, &xs, &[0]);
        }
        divisions(&mut t, w, &magics, &xs);
    }
    t.verdict();
}

/// What the collapse must refuse, pinned on the tree it returns.
///
/// A right shift anywhere in a linear form, a shift whose count is
/// the second variable, a multiplication of a selector by a constant
/// wider than one bit, a tree past [`MBA_NODES_MAX`] nodes, and a
/// negation or a sum inside an and, or or xor (its carries move bits
/// between positions, off the lattice the collapse measures) all
/// come back unfolded. A stack slot leaf is a variable, so the
/// collapse that fires names it, not a constant.
///
/// # Panics
///
/// When a refused shape is rewritten, or the stack-slot form collapses
/// to something but `sp + y`.
#[test]
fn mba_refusals_stay_unfolded() {
    let unchanged = |op, l: &Expr, r: &Expr, w| {
        assert_eq!(
            fold(op, l.clone(), r.clone(), w),
            b(op, l, r),
            "rewrote a refused shape at width {w}"
        );
    };
    let smuggled_l = b(
        Op::Add,
        &b(Op::Add, &b(Op::Shr, &X, &k(1)), &Y),
        &b(Op::And, &X, &Y),
    );
    let smuggled_r = b(Op::Add, &Y, &b(Op::And, &X, &Y));
    unchanged(Op::Sub, &smuggled_l, &smuggled_r, 64);
    unchanged(
        Op::Add,
        &b(Op::Xor, &X, &Y),
        &b(Op::Shl, &b(Op::And, &X, &Y), &Y),
        32,
    );
    unchanged(Op::Mul, &b(Op::And, &X, &Y), &k(2), 8);
    unchanged(Op::Mul, &b(Op::And, &X, &Y), &k(3), 8);
    unchanged(
        Op::Mul,
        &k(2),
        &b(
            Op::Add,
            &b(Op::Xor, &X, &Y),
            &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
        ),
        32,
    );
    let borrows = b(
        Op::And,
        &u(Y.clone()),
        &b(
            Op::And,
            &Expr::Un(UnOp::Neg, Box::new(X.clone())),
            &b(Op::Shl, &k(11_444_343_663_368_143_628), &k(7)),
        ),
    );
    unchanged(Op::Or, &Y, &u(borrows), 32);
    unchanged(Op::And, &u(b(Op::Add, &X, &k(3))), &Y, 32);
    let pad = b(Op::Xor, &b(Op::And, &X, &Y), &b(Op::And, &X, &Y));
    let mut capped = b(
        Op::Add,
        &b(Op::Xor, &X, &Y),
        &b(Op::Shl, &b(Op::And, &X, &Y), &k(1)),
    );
    for _ in 0..3 {
        capped = b(Op::Add, &capped, &pad.clone());
    }
    assert_eq!(
        fold(Op::Add, capped.clone(), k(0), 32),
        capped,
        "a tree past MBA_NODES_MAX must come back unfolded"
    );
    let sp = b(
        Op::Add,
        &b(Op::Xor, &Expr::Sp(-0x28), &Y),
        &b(Op::Shl, &b(Op::And, &Expr::Sp(-0x28), &Y), &k(1)),
    );
    assert_eq!(
        fold(Op::Add, sp, k(0), 64),
        b(Op::Add, &Expr::Sp(-0x28), &Y),
        "a stack slot leaf must collapse as a variable"
    );
}

/// Builds the next seeded value of a splitmix64 stream.
///
/// # Arguments
///
/// * `s` - The stream state, advanced in place.
fn next(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Builds one seeded random tree over the folder's algebra.
///
/// # Arguments
///
/// * `s` - The stream state, advanced in place.
/// * `depth` - Remaining recursion; at zero only leaves are built.
/// * `sext` - Whether [`Expr::Sext`] layers may appear.
fn tree(s: &mut u64, depth: u8, sext: bool) -> Expr {
    let pick = |s: &mut u64, n: u64| next(s) % n;
    let leaf = |s: &mut u64| match pick(s, 4) {
        0 => X.clone(),
        1 => Y.clone(),
        _ => k(next(s)),
    };
    let sub = |s: &mut u64, d: u8| tree(s, d, sext);
    if depth == 0 {
        return leaf(s);
    }
    if sext && pick(s, 6) == 0 {
        let from = [8u8, 16, 24, 31, 32, 64][usize::try_from(pick(s, 6)).unwrap()];
        return Expr::Sext(Box::new(sub(s, depth - 1)), from);
    }
    match pick(s, 13) {
        0 => b(Op::And, &sub(s, depth - 1), &sub(s, depth - 1)),
        1 => b(Op::Or, &sub(s, depth - 1), &sub(s, depth - 1)),
        2 => b(Op::Xor, &sub(s, depth - 1), &sub(s, depth - 1)),
        3 => b(Op::Add, &sub(s, depth - 1), &sub(s, depth - 1)),
        4 => b(Op::Sub, &sub(s, depth - 1), &sub(s, depth - 1)),
        5 => b(Op::Mul, &sub(s, depth - 1), &k(next(s))),
        6 => b(Op::Shl, &sub(s, depth - 1), &k(pick(s, 40))),
        7 => b(Op::Shr, &sub(s, depth - 1), &k(pick(s, 40))),
        8 => u(sub(s, depth - 1)),
        9 => Expr::Un(UnOp::Neg, Box::new(sub(s, depth - 1))),
        _ => leaf(s),
    }
}

/// Folds seeded random trees and holds every rewrite they survive
/// against the unfolded tree on seeded inputs.
///
/// # Arguments
///
/// * `s` - The stream state, advanced in place.
/// * `sext` - Whether the trees may sign-extend.
/// * `name` - The check's name, for the failure message.
///
/// # Panics
///
/// When a rewrite changes a tree's value, or no tree was rewritten at
/// all (the sweep would then check nothing).
fn sweep_holds(s: &mut u64, sext: bool, name: &str) {
    const W: u8 = 32;
    let mut changed = 0usize;
    for _ in 0..300 {
        let op = match next(s) % 5 {
            0 => Op::Add,
            1 => Op::Sub,
            2 => Op::And,
            3 => Op::Or,
            _ => Op::Xor,
        };
        let l = tree(s, 4, sext);
        let r = tree(s, 4, sext);
        let before = b(op, &l, &r);
        let after = fold(op, l, r, W);
        changed += usize::from(after != before);
        for _ in 0..64 {
            let (x, y) = (next(s), next(s));
            let Some(want) = ev(&before, W, x, y) else {
                continue;
            };
            let got = ev(&after, W, x, y);
            assert_eq!(
                got.map(|v| v & lane(W)),
                Some(want & lane(W)),
                "{name}: {before:?} became {after:?} at x={x:#x} y={y:#x}"
            );
        }
    }
    assert!(changed > 0, "{name}: no tree was rewritten");
}

/// The folder's rewrites hold on seeded random trees.
///
/// # Panics
///
/// When a rewrite changes a tree's value.
#[test]
fn rewrites_hold_on_seeded_trees() {
    for seed in [0x0123_4567_89ab_cdefu64, 0x243f_6a88_85a3_08d3] {
        let mut s = seed;
        sweep_holds(&mut s, false, "plain");
    }
}

/// The collapse holds with sign-extension layers in the tree.
///
/// A [`Expr::Sext`] from fewer bits than the width is not linear on
/// the lattice the collapse measures, so this is the shape a misread
/// would slip through on.
///
/// # Panics
///
/// When a rewrite changes a tree's value.
#[test]
fn rewrites_hold_on_seeded_trees_with_sign_extensions() {
    for seed in [0xfeed_face_dead_beefu64, 0x1319_8a2e_0370_7344] {
        let mut s = seed;
        sweep_holds(&mut s, true, "sext");
    }
}
