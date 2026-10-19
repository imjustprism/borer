//! The rewrite rules: each adds forms equal to an e-node's class.
//!
//! A rule reads one e-node and the classes under it, and returns a class
//! that computes the same bits, which saturation then joins to the
//! e-node's class. Each one is checked against the MIR evaluator on edge
//! and random inputs (exhaustively at 8 bits) in the tests. The division
//! rules also prove each instance before they add it: a multiply-high and
//! shift is turned into a quotient only when the error bound of its
//! constant holds for every input of its width.

use super::super::super::expr::sext;
use super::super::super::helper::Helper;
use super::super::super::verify::low;
use super::super::eval::{Inputs, eval};
use super::super::{BinOp, Body, IPred, Inst, MTy, Prov, UnOp, Val, WideOp};
use super::{EGraph, remap};

/// How deep the division rules look under a quotient for its multiply.
const DEPTH: u8 = 6;

/// One rewrite rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in super::super::super) enum Rule {
    /// An integer op of constants becomes its value.
    Fold,
    /// A constant moves to the right of a commutative op or a compare.
    Commute,
    /// `x << k` and `x * 2^k` are one value, and a sum of multiples of
    /// `x` (what `lea` chains compute) is one multiply.
    Scale,
    /// A multiply-high and shift by a magic constant is an unsigned
    /// quotient.
    UDivMagic,
    /// A signed multiply-high, shift and sign fix is a signed quotient.
    SDivMagic,
    /// `x - (x / d) * d` is a remainder.
    Rem,
    /// `(x << k) | (x >> (w - k))` is a rotate.
    Rotate,
    /// A select or a sign-mask idiom that negates a negative value is
    /// `llabs`, or the select at another width.
    Abs,
    /// A select of the lesser or greater of two values is `min` or `max`.
    MinMax,
    /// Chains of extensions and truncations fold, a zero extension of a
    /// truncation is a mask, and a shift pair is a sign extension.
    Extend,
    /// Masks and shifts that read a bit field fold to one shift and mask.
    Field,
    /// A negated compare is the inverse compare, and a 0/1 select is the
    /// condition.
    Bool,
    /// Mixed boolean-arithmetic identities: `(x ^ y) + 2 * (x & y)` is
    /// `x + y`, and their kin.
    Mba,
}

impl Rule {
    /// Every rule, in the order saturation applies them.
    pub(in super::super::super) const ALL: [Self; 13] = [
        Self::Fold,
        Self::Commute,
        Self::Extend,
        Self::Field,
        Self::Scale,
        Self::Bool,
        Self::Rotate,
        Self::Abs,
        Self::MinMax,
        Self::Mba,
        Self::UDivMagic,
        Self::SDivMagic,
        Self::Rem,
    ];

    /// Applies the rule to one e-node.
    ///
    /// # Arguments
    ///
    /// * `g` - The graph, which the rule adds forms to.
    /// * `id` - The e-node's class.
    /// * `node` - The e-node.
    ///
    /// # Returns
    ///
    /// A class equal to `id`, or `None` when the rule does not match or
    /// the budget is spent.
    pub(in super::super::super) fn apply(
        self,
        g: &mut EGraph,
        id: Val,
        node: &Inst,
    ) -> Option<Val> {
        let MTy::I(w) = g.ty(id) else {
            return None;
        };
        let p = g.prov(id);
        match self {
            Self::Fold => fold(g, w, p, node),
            Self::Commute => commute(g, p, node),
            Self::Scale => scale(g, p, node),
            Self::UDivMagic => udiv_magic(g, w, p, node),
            Self::SDivMagic => sdiv_magic(g, p, node),
            Self::Rem => rem(g, p, node),
            Self::Rotate => rotate(g, p, node),
            Self::Abs => abs(g, w, p, node),
            Self::MinMax => min_max(g, w, p, node),
            Self::Extend => extend(g, p, node),
            Self::Field => field(g, p, node),
            Self::Bool => boolean(g, w, p, node),
            Self::Mba => mba(g, p, node),
        }
    }
}

/// A state with nothing in it, for evaluating constants.
struct Nothing;

impl Inputs for Nothing {
    fn reg(&self, _: super::super::super::expr::Key) -> Option<u64> {
        None
    }

    fn sp(&self) -> u64 {
        0
    }

    fn tls(&self) -> u64 {
        0
    }

    fn load(&mut self, _: u64, _: u64) -> Option<u64> {
        None
    }
}

/// A value recognized as `floor(x * m / 2^n)`.
#[derive(Debug, Clone, Copy)]
struct Floor {
    /// The dividend.
    x: Val,
    /// The dividend's width.
    k: u8,
    /// The multiplier, positive.
    m: u128,
    /// The power of two divided by.
    n: u32,
}

/// Returns a class's width, or `None` for a class that is not an
/// integer.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
fn width(g: &EGraph, v: Val) -> Option<u8> {
    match g.ty(v) {
        MTy::I(w) => Some(w),
        MTy::F32 | MTy::F64 | MTy::V(..) | MTy::Ptr => None,
    }
}

/// Returns the operands of each form of a class that is one binary op.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `want` - The op.
fn bins(g: &EGraph, v: Val, want: BinOp) -> Vec<(u8, Val, Val)> {
    g.nodes(v)
        .iter()
        .filter_map(|n| {
            if let Inst::Bin { op, w, l, r } = n
                && *op == want
            {
                Some((*w, *l, *r))
            } else {
                None
            }
        })
        .collect()
}

/// Returns the operands of each form of a class that is one binary op
/// with a constant: on the right, or on either side for a commutative op.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `want` - The op.
///
/// # Returns
///
/// The width, the other operand and the constant of each.
fn with_const(g: &EGraph, v: Val, want: BinOp) -> Vec<(u8, Val, u64)> {
    let commutes = matches!(
        want,
        BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
    );
    bins(g, v, want)
        .into_iter()
        .filter_map(|(w, l, r)| match (g.konst(l), g.konst(r)) {
            (_, Some(c)) => Some((w, l, c)),
            (Some(c), None) if commutes => Some((w, r, c)),
            (Some(_) | None, None) => None,
        })
        .collect()
}

/// Returns the operand of each form of a class that is one unary op.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `want` - The op.
fn uns(g: &EGraph, v: Val, want: UnOp) -> Vec<Val> {
    g.nodes(v)
        .iter()
        .filter_map(|n| {
            if let Inst::Un { op, x, .. } = n
                && *op == want
            {
                Some(*x)
            } else {
                None
            }
        })
        .collect()
}

/// Returns each extension a class's forms make.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
///
/// # Returns
///
/// Whether it is signed, the widths from and to, and the operand.
fn exts(g: &EGraph, v: Val) -> Vec<(bool, u8, u8, Val)> {
    g.nodes(v)
        .iter()
        .filter_map(|n| {
            if let Inst::Ext {
                signed,
                from,
                to,
                x,
            } = n
            {
                Some((*signed, *from, *to, *x))
            } else {
                None
            }
        })
        .collect()
}

/// Returns each truncation a class's forms make: the width kept and the
/// operand.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
fn truncs(g: &EGraph, v: Val) -> Vec<(u8, Val)> {
    g.nodes(v)
        .iter()
        .filter_map(|n| {
            if let Inst::Trunc { to, x } = n {
                Some((*to, *x))
            } else {
                None
            }
        })
        .collect()
}

/// Returns each integer compare a class's forms make.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
fn icmps(g: &EGraph, v: Val) -> Vec<(IPred, u8, Val, Val)> {
    g.nodes(v)
        .iter()
        .filter_map(|n| {
            if let Inst::ICmp { pred, w, l, r } = n {
                Some((*pred, *w, *l, *r))
            } else {
                None
            }
        })
        .collect()
}

/// Returns each wide product by a constant a class's forms make.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `want` - The signedness.
///
/// # Returns
///
/// The width, the other operand and the constant of each.
fn wides(g: &EGraph, v: Val, want: WideOp) -> Vec<(u8, Val, u64)> {
    g.nodes(v)
        .iter()
        .filter_map(|n| {
            let Inst::Wide { op, w, l, r } = n else {
                return None;
            };
            if *op != want {
                return None;
            }
            match (g.konst(*l), g.konst(*r)) {
                (_, Some(c)) => Some((*w, *l, c)),
                (Some(c), None) => Some((*w, *r, c)),
                (None, None) => None,
            }
        })
        .collect()
}

/// Returns the class of `2 * r` for each `r` a class doubles: `r * 2`,
/// `r << 1` or `r + r`.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
fn halves(g: &EGraph, v: Val) -> Vec<Val> {
    let mut out: Vec<Val> = with_const(g, v, BinOp::Mul)
        .into_iter()
        .filter(|&(_, _, c)| c == 2)
        .map(|(_, r, _)| r)
        .collect();
    out.extend(
        with_const(g, v, BinOp::Shl)
            .into_iter()
            .filter(|&(_, _, c)| c == 1)
            .map(|(_, r, _)| r),
    );
    out.extend(
        bins(g, v, BinOp::Add)
            .into_iter()
            .filter(|&(_, l, r)| g.same(l, r))
            .map(|(_, l, _)| l),
    );
    out
}

/// Returns the operand pairs of each form of a class that is one binary
/// op, both ways round.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `want` - The op, which commutes.
fn pairs(g: &EGraph, v: Val, want: BinOp) -> Vec<(Val, Val)> {
    bins(g, v, want)
        .into_iter()
        .flat_map(|(_, l, r)| [(l, r), (r, l)])
        .collect()
}

/// Tells whether a class's forms include one pair of operands.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `want` - The op, which commutes.
/// * `x` - One operand.
/// * `y` - The other.
fn holds(g: &EGraph, v: Val, want: BinOp, x: Val, y: Val) -> bool {
    pairs(g, v, want)
        .into_iter()
        .any(|(a, b)| g.same(a, x) && g.same(b, y))
}

/// Adds an integer constant.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `w` - The width.
/// * `bits` - The value, cut to the width.
/// * `p` - The provenance.
fn konst(g: &mut EGraph, w: u8, bits: u64, p: Prov) -> Option<Val> {
    g.add(
        &Inst::Const {
            w,
            bits: bits & low(w),
        },
        MTy::I(w),
        p,
    )
}

/// Adds a binary op.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `op` - The op.
/// * `w` - The width.
/// * `l` - The left operand.
/// * `r` - The right operand.
/// * `p` - The provenance.
fn bin(g: &mut EGraph, op: BinOp, w: u8, l: Val, r: Val, p: Prov) -> Option<Val> {
    g.add(&Inst::Bin { op, w, l, r }, MTy::I(w), p)
}

/// Adds a binary op whose right operand is a constant.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `op` - The op.
/// * `w` - The width.
/// * `l` - The left operand.
/// * `c` - The constant.
/// * `p` - The provenance.
fn bin_k(g: &mut EGraph, op: BinOp, w: u8, l: Val, c: u64, p: Prov) -> Option<Val> {
    let r = konst(g, w, c, p)?;
    bin(g, op, w, l, r, p)
}

/// Adds a unary op.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `op` - The op.
/// * `w` - The width.
/// * `x` - The operand.
/// * `p` - The provenance.
fn un(g: &mut EGraph, op: UnOp, w: u8, x: Val, p: Prov) -> Option<Val> {
    g.add(&Inst::Un { op, w, x }, MTy::I(w), p)
}

/// Adds an extension.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `signed` - Sign- rather than zero-extend.
/// * `from` - The operand's width.
/// * `to` - The result's width.
/// * `x` - The operand.
/// * `p` - The provenance.
fn ext(g: &mut EGraph, signed: bool, from: u8, to: u8, x: Val, p: Prov) -> Option<Val> {
    g.add(
        &Inst::Ext {
            signed,
            from,
            to,
            x,
        },
        MTy::I(to),
        p,
    )
}

/// Adds a truncation.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `to` - The width kept.
/// * `x` - The operand.
/// * `p` - The provenance.
fn trunc(g: &mut EGraph, to: u8, x: Val, p: Prov) -> Option<Val> {
    g.add(&Inst::Trunc { to, x }, MTy::I(to), p)
}

/// Adds a helper of two or one word-wide operands with a result of `w`
/// bits.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `h` - The helper.
/// * `w` - The result's width, the machine word.
/// * `args` - The operands.
/// * `p` - The provenance.
fn helper(g: &mut EGraph, h: Helper, w: u8, args: Vec<Val>, p: Prov) -> Option<Val> {
    let word = g.word();
    g.add(
        &Inst::Helper {
            h,
            bits: word,
            word,
            args,
        },
        MTy::I(w),
        p,
    )
}

/// Returns the compare that holds exactly when another does not.
///
/// # Arguments
///
/// * `pred` - The compare.
fn inverse(pred: IPred) -> IPred {
    match pred {
        IPred::Eq => IPred::Ne,
        IPred::Ne => IPred::Eq,
        IPred::Ult => IPred::Uge,
        IPred::Ule => IPred::Ugt,
        IPred::Ugt => IPred::Ule,
        IPred::Uge => IPred::Ult,
        IPred::Slt => IPred::Sge,
        IPred::Sle => IPred::Sgt,
        IPred::Sgt => IPred::Sle,
        IPred::Sge => IPred::Slt,
    }
}

/// Returns the compare that holds of the operands swapped.
///
/// # Arguments
///
/// * `pred` - The compare.
fn swapped(pred: IPred) -> IPred {
    match pred {
        IPred::Eq => IPred::Eq,
        IPred::Ne => IPred::Ne,
        IPred::Ult => IPred::Ugt,
        IPred::Ule => IPred::Uge,
        IPred::Ugt => IPred::Ult,
        IPred::Uge => IPred::Ule,
        IPred::Slt => IPred::Sgt,
        IPred::Sle => IPred::Sge,
        IPred::Sgt => IPred::Slt,
        IPred::Sge => IPred::Sle,
    }
}

/// Folds an integer op whose operands are all constants.
///
/// The op runs on the MIR evaluator, so the fold has its semantics
/// exactly; a zero divisor stays unfolded.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `w` - The result's width.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn fold(g: &mut EGraph, w: u8, p: Prov, node: &Inst) -> Option<Val> {
    let integer = matches!(
        node,
        Inst::Bin { .. }
            | Inst::Un { .. }
            | Inst::Ext { .. }
            | Inst::Trunc { .. }
            | Inst::ICmp { .. }
            | Inst::Ovf { .. }
            | Inst::Wide { .. }
    );
    let ops = super::operands(node);
    if !integer || ops.is_empty() || w > 64 {
        return None;
    }
    let mut body = Body::new(g.word());
    let mut seen = Vec::with_capacity(ops.len());
    for v in ops {
        let bits = g.konst(v)?;
        let cw = width(g, v)?;
        let at = body.push(Inst::Const { w: cw, bits }, MTy::I(cw), Prov::ENTRY);
        seen.push((v, at));
    }
    let inst = remap(node, |v| {
        seen.iter()
            .find(|(c, _)| g.same(*c, v))
            .map_or(v, |&(_, at)| at)
    });
    let top = body.push(inst, MTy::I(w), Prov::ENTRY);
    let bits = eval(&body, top, &mut Nothing)?;
    konst(g, w, bits, p)
}

/// Moves a constant to the right of a commutative op or a compare.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn commute(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    match node {
        Inst::Bin { op, w, l, r }
            if matches!(
                op,
                BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
            ) && g.konst(*l).is_some()
                && g.konst(*r).is_none() =>
        {
            bin(g, *op, *w, *r, *l, p)
        }
        Inst::ICmp { pred, w, l, r } if g.konst(*l).is_some() && g.konst(*r).is_none() => g.add(
            &Inst::ICmp {
                pred: swapped(*pred),
                w: *w,
                l: *r,
                r: *l,
            },
            MTy::I(1),
            p,
        ),
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Trunc { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }
}

/// Relates shifts, doubling and sums of multiples to one multiply.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn scale(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    let Inst::Bin { op, w, l, r } = node else {
        return None;
    };
    let (w, l, r) = (*w, *l, *r);
    match op {
        BinOp::Shl => {
            let k = g.konst(r)?;
            (k > 0 && k < u64::from(w)).then_some(())?;
            bin_k(g, BinOp::Mul, w, l, 1u64 << k, p)
        }
        BinOp::Mul => {
            let c = g.konst(r)?;
            if let Some((_, x, c1)) = with_const(g, l, BinOp::Mul).into_iter().next() {
                return bin_k(g, BinOp::Mul, w, x, c1.wrapping_mul(c), p);
            }
            (c.is_power_of_two() && c > 1).then_some(())?;
            bin_k(g, BinOp::Shl, w, l, u64::from(c.trailing_zeros()), p)
        }
        BinOp::Add => {
            if g.same(l, r) {
                return bin_k(g, BinOp::Mul, w, l, 2, p);
            }
            for (a, b) in [(l, r), (r, l)] {
                for (_, x, c) in with_const(g, a, BinOp::Mul) {
                    if g.same(x, b) {
                        return bin_k(g, BinOp::Mul, w, x, c.wrapping_add(1), p);
                    }
                    if let Some((_, _, c2)) = with_const(g, b, BinOp::Mul)
                        .into_iter()
                        .find(|&(_, y, _)| g.same(x, y))
                    {
                        return bin_k(g, BinOp::Mul, w, x, c.wrapping_add(c2), p);
                    }
                }
            }
            None
        }
        BinOp::Sub => {
            let (_, x, c) = with_const(g, l, BinOp::Mul)
                .into_iter()
                .find(|&(_, x, _)| g.same(x, r))?;
            bin_k(g, BinOp::Mul, w, x, c.wrapping_sub(1), p)
        }
        BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::Rotl
        | BinOp::Rotr => None,
    }
}

/// Returns `2^n`, or `None` past 127.
///
/// # Arguments
///
/// * `n` - The power.
fn pow2(n: u32) -> Option<u128> {
    1u128.checked_shl(n).filter(|_| n < 128)
}

/// Returns the divisor `d` with `floor(x * m / 2^n) == floor(x / d)` for
/// every unsigned `k`-bit `x`.
///
/// With `d = ceil(2^n / m)` and `e = m * d - 2^n`, the product is
/// `x / d + x * e / (d * 2^n)`, whose floor is `floor(x / d)` whenever
/// `x * e < 2^n`; that holding for the largest `x` proves every one.
///
/// # Arguments
///
/// * `m` - The multiplier.
/// * `n` - The power of two divided by.
/// * `k` - The dividend's width.
///
/// # Returns
///
/// The divisor, at least 2 and below `2^k`, or `None` when the bound
/// fails.
fn udivisor(m: u128, n: u32, k: u8) -> Option<u64> {
    let two_n = pow2(n)?;
    if m == 0 || k == 0 || k > 64 {
        return None;
    }
    let d = two_n.div_ceil(m);
    let e = m.checked_mul(d)?.checked_sub(two_n)?;
    let xmax = u128::from(low(k));
    (d >= 2 && d <= xmax && e.checked_mul(xmax)? < two_n).then_some(())?;
    u64::try_from(d).ok()
}

/// Returns the divisor `d` with `floor(x * m / 2^n)` plus one for a
/// negative `x` equal to the truncated `x / d` for every signed `k`-bit
/// `x`.
///
/// The bound is [`udivisor`]'s over magnitudes up to `2^(k-1)`: a
/// non-negative `x` floors to `x / d`, and a negative one floors one
/// below the quotient rounded toward zero, which the sign fix adds back.
/// That needs `x * m / 2^n` never an integer for a negative `x`, so `e`
/// must be positive: a power-of-two divisor has an exact multiplier and
/// no such quotient.
///
/// # Arguments
///
/// * `m` - The multiplier, positive.
/// * `n` - The power of two divided by.
/// * `k` - The dividend's width.
///
/// # Returns
///
/// The divisor, at least 2 and below `2^(k-1)`, or `None` when the bound
/// fails.
fn sdivisor(m: u128, n: u32, k: u8) -> Option<u64> {
    let two_n = pow2(n)?;
    if m == 0 || !(2..=64).contains(&k) {
        return None;
    }
    let d = two_n.div_ceil(m);
    let e = m.checked_mul(d)?.checked_sub(two_n)?;
    let half = 1u128 << (k - 1);
    (e > 0 && d >= 2 && d < half && e.checked_mul(half)? < two_n).then_some(())?;
    u64::try_from(d).ok()
}

/// Recognizes a class as an unsigned `floor(x * m / 2^n)`.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `depth` - How much deeper to look.
fn ufloor(g: &EGraph, v: Val, depth: u8) -> Option<Floor> {
    let d = depth.checked_sub(1)?;
    g.nodes(v).iter().find_map(|n| ufloor_node(g, n, d))
}

/// Recognizes an e-node as an unsigned `floor(x * m / 2^n)`.
///
/// The forms are a multiply-high, a multiply of a zero-extended value that cannot wrap,
/// the add-and-halve fix of a multiplier past the width, a logical shift
/// of one or a truncation that keeps it whole.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `node` - The e-node.
/// * `depth` - How much deeper to look.
fn ufloor_node(g: &EGraph, node: &Inst, depth: u8) -> Option<Floor> {
    match node {
        Inst::Wide {
            op: WideOp::UMulHi,
            w,
            l,
            r,
        } => {
            let (x, m) = match (g.konst(*l), g.konst(*r)) {
                (_, Some(m)) => (*l, m),
                (Some(m), None) => (*r, m),
                (None, None) => return None,
            };
            Some(Floor {
                x,
                k: *w,
                m: u128::from(m),
                n: u32::from(*w),
            })
        }
        Inst::Bin {
            op: BinOp::Mul,
            w,
            l,
            r,
        } => {
            let (xv, m) = match (g.konst(*l), g.konst(*r)) {
                (_, Some(m)) => (*l, m),
                (Some(m), None) => (*r, m),
                (None, None) => return None,
            };
            let (_, k, _, x) = exts(g, xv)
                .into_iter()
                .find(|&(signed, k, to, _)| !signed && to == *w && k < *w)?;
            let top = u128::from(m).checked_mul(u128::from(low(k)))?;
            (top <= u128::from(low(*w))).then_some(Floor {
                x,
                k,
                m: u128::from(m),
                n: 0,
            })
        }
        Inst::Bin {
            op: BinOp::LShr,
            w,
            l,
            r,
        } => {
            let s = u32::try_from(g.konst(*r)?).ok()?;
            (s < u32::from(*w)).then_some(())?;
            let f = ufloor(g, *l, depth)?;
            Some(Floor { n: f.n + s, ..f })
        }
        Inst::Trunc { to, x } => ufloor(g, *x, depth).filter(|f| f.k <= *to),
        Inst::Bin {
            op: BinOp::Add,
            w,
            l,
            r,
        } => [(*l, *r), (*r, *l)].into_iter().find_map(|(t, h)| {
            let (_, x, m) = wides(g, t, WideOp::UMulHi)
                .into_iter()
                .find(|&(tw, _, _)| tw == *w)?;
            with_const(g, h, BinOp::LShr)
                .into_iter()
                .filter(|&(_, _, s)| s == 1)
                .any(|(_, q, _)| {
                    bins(g, q, BinOp::Sub)
                        .into_iter()
                        .any(|(_, a, b)| g.same(a, x) && g.same(b, t))
                })
                .then(|| Floor {
                    x,
                    k: *w,
                    m: (1u128 << *w) + u128::from(m),
                    n: u32::from(*w) + 1,
                })
        }),
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }
}

/// Turns a multiply-high and shift by a magic constant into an unsigned
/// quotient, when [`udivisor`] proves the constant.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `w` - The e-node's width.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn udiv_magic(g: &mut EGraph, w: u8, p: Prov, node: &Inst) -> Option<Val> {
    let f = ufloor_node(g, node, DEPTH)?;
    let d = udivisor(f.m, f.n, f.k)?;
    let q = bin_k(g, BinOp::UDiv, f.k, f.x, d, p)?;
    match w.cmp(&f.k) {
        std::cmp::Ordering::Equal => Some(q),
        std::cmp::Ordering::Greater => ext(g, false, f.k, w, q, p),
        std::cmp::Ordering::Less => None,
    }
}

/// Recognizes a class as a signed `floor(x * m / 2^n)` with `m`
/// positive.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
/// * `depth` - How much deeper to look.
fn sfloor(g: &EGraph, v: Val, depth: u8) -> Option<Floor> {
    let d = depth.checked_sub(1)?;
    g.nodes(v).iter().find_map(|n| sfloor_node(g, n, d))
}

/// Recognizes an e-node as a signed `floor(x * m / 2^n)`.
///
/// The forms are a signed multiply-high by a positive constant, one by a negative constant plus
/// the dividend, a multiply of a sign-extended value that cannot
/// overflow, an arithmetic shift of one or a truncation that keeps it
/// whole.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `node` - The e-node.
/// * `depth` - How much deeper to look.
fn sfloor_node(g: &EGraph, node: &Inst, depth: u8) -> Option<Floor> {
    match node {
        Inst::Wide {
            op: WideOp::SMulHi,
            w,
            l,
            r,
        } => {
            let (x, m) = match (g.konst(*l), g.konst(*r)) {
                (_, Some(m)) => (*l, m),
                (Some(m), None) => (*r, m),
                (None, None) => return None,
            };
            let m = sext(m, *w).cast_signed();
            (m > 0).then(|| Floor {
                x,
                k: *w,
                m: u128::from(m.unsigned_abs()),
                n: u32::from(*w),
            })
        }
        Inst::Bin {
            op: BinOp::Add,
            w,
            l,
            r,
        } => [(*l, *r), (*r, *l)].into_iter().find_map(|(t, x)| {
            let (_, _, m) = wides(g, t, WideOp::SMulHi)
                .into_iter()
                .find(|&(tw, y, _)| tw == *w && g.same(y, x))?;
            let m = sext(m, *w).cast_signed();
            (m < 0).then(|| Floor {
                x,
                k: *w,
                m: (1u128 << *w) - u128::from(m.unsigned_abs()),
                n: u32::from(*w),
            })
        }),
        Inst::Bin {
            op: BinOp::Mul,
            w,
            l,
            r,
        } => {
            let (xv, m) = match (g.konst(*l), g.konst(*r)) {
                (_, Some(m)) => (*l, m),
                (Some(m), None) => (*r, m),
                (None, None) => return None,
            };
            let m = sext(m, *w).cast_signed();
            let (_, k, _, x) = exts(g, xv)
                .into_iter()
                .find(|&(signed, k, to, _)| signed && to == *w && k < *w && k > 0)?;
            let top = u128::from(m.unsigned_abs()).checked_shl(u32::from(k) - 1)?;
            (m > 0 && top < 1u128 << (*w - 1)).then(|| Floor {
                x,
                k,
                m: u128::from(m.unsigned_abs()),
                n: 0,
            })
        }
        Inst::Bin {
            op: BinOp::AShr,
            w,
            l,
            r,
        } => {
            let s = u32::try_from(g.konst(*r)?).ok()?;
            (s < u32::from(*w)).then_some(())?;
            let f = sfloor(g, *l, depth)?;
            Some(Floor { n: f.n + s, ..f })
        }
        Inst::Trunc { to, x } => sfloor(g, *x, depth).filter(|f| f.k <= *to),
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }
}

/// Tells whether a class has the sign of a dividend: the dividend itself,
/// its sign extension, or a signed floor of it by a positive multiplier.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `y` - The class.
/// * `x` - The dividend.
fn signed_like(g: &EGraph, y: Val, x: Val) -> bool {
    g.same(y, x)
        || exts(g, y)
            .into_iter()
            .any(|(signed, _, _, z)| signed && g.same(z, x))
        || sfloor(g, y, DEPTH).is_some_and(|f| g.same(f.x, x))
}

/// Returns each value whose sign bit, as 0 or 1, a class holds: a logical
/// shift by its width less one, or a truncation of one.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `v` - The class.
fn sign_bits(g: &EGraph, v: Val) -> Vec<Val> {
    let direct = |c: Val| {
        with_const(g, c, BinOp::LShr)
            .into_iter()
            .filter(|&(w, _, s)| s + 1 == u64::from(w))
            .map(|(_, y, _)| y)
            .collect::<Vec<_>>()
    };
    let mut out = direct(v);
    for (_, u) in truncs(g, v) {
        out.extend(direct(u));
    }
    out
}

/// Turns a signed multiply-high, shift and sign fix into a signed
/// quotient, when [`sdivisor`] proves the constant.
///
/// The fix adds the sign bit (`q + (q >> (w - 1))`, logical) or subtracts
/// the sign mask (`q - (x >> (w - 1))`, arithmetic) of the dividend or of
/// a floor of it, which share its sign.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn sdiv_magic(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    let Inst::Bin { op, w, l, r } = node else {
        return None;
    };
    let w = *w;
    let floor = match op {
        BinOp::Add => [(*l, *r), (*r, *l)].into_iter().find_map(|(q, s)| {
            let f = sfloor(g, q, DEPTH)?;
            sign_bits(g, s)
                .into_iter()
                .any(|y| signed_like(g, y, f.x))
                .then_some(f)
        }),
        BinOp::Sub => {
            let f = sfloor(g, *l, DEPTH)?;
            with_const(g, *r, BinOp::AShr)
                .into_iter()
                .any(|(sw, y, s)| sw == w && s + 1 == u64::from(w) && signed_like(g, y, f.x))
                .then_some(f)
        }
        BinOp::Mul
        | BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::Rotl
        | BinOp::Rotr => None,
    }?;
    (floor.k == w).then_some(())?;
    let d = sdivisor(floor.m, floor.n, w)?;
    bin_k(g, BinOp::SDiv, w, floor.x, d, p)
}

/// Turns `x - (x / d) * d` (or `x + (x / d) * -d`) into a remainder.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn rem(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    let Inst::Bin { op, w, l, r } = node else {
        return None;
    };
    let w = *w;
    let candidates: Vec<(Val, Val, u64)> = match op {
        BinOp::Sub => vec![(*l, *r, 1)],
        BinOp::Add => vec![(*l, *r, u64::MAX), (*r, *l, u64::MAX)],
        BinOp::Mul
        | BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::Rotl
        | BinOp::Rotr => return None,
    };
    for (x, prod, sign) in candidates {
        for (_, q, c) in with_const(g, prod, BinOp::Mul) {
            let d = c.wrapping_mul(sign) & low(w);
            for (div, rem) in [(BinOp::UDiv, BinOp::URem), (BinOp::SDiv, BinOp::SRem)] {
                let hit = with_const(g, q, div)
                    .into_iter()
                    .any(|(qw, y, dd)| qw == w && dd == d && g.same(y, x));
                if hit {
                    return bin_k(g, rem, w, x, d, p);
                }
            }
        }
    }
    None
}

/// Turns `(x << k) | (x >> (w - k))` (or `+`, `^`) into a rotate.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn rotate(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    let Inst::Bin { op, w, l, r } = node else {
        return None;
    };
    if !matches!(op, BinOp::Or | BinOp::Add | BinOp::Xor) {
        return None;
    }
    let w = *w;
    for (a, b) in [(*l, *r), (*r, *l)] {
        for (sw, x, k) in with_const(g, a, BinOp::Shl) {
            let hit = with_const(g, b, BinOp::LShr)
                .into_iter()
                .any(|(rw, y, k2)| rw == w && g.same(x, y) && k + k2 == u64::from(w));
            if sw == w && k > 0 && k < u64::from(w) && hit {
                return bin_k(g, BinOp::Rotl, w, x, k, p);
            }
        }
    }
    None
}

/// Returns the class of the sign mask of `x` (`x >> (w - 1)`,
/// arithmetic) when a class is one.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `m` - The class.
/// * `w` - The width.
fn mask_of(g: &EGraph, m: Val, w: u8) -> Option<Val> {
    with_const(g, m, BinOp::AShr)
        .into_iter()
        .find(|&(mw, _, s)| mw == w && s + 1 == u64::from(w))
        .map(|(_, x, _)| x)
}

/// Turns the absolute-value idioms into `llabs` at the machine word, or
/// into `x < 0 ? -x : x` at another width.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `w` - The e-node's width.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn abs(g: &mut EGraph, w: u8, p: Prov, node: &Inst) -> Option<Val> {
    let x = match node {
        Inst::Select { c, t, f } => icmps(g, *c).into_iter().find_map(|(pred, cw, x, z)| {
            if cw != w || g.konst(z) != Some(0) {
                return None;
            }
            let neg = |v: Val| uns(g, v, UnOp::Neg).into_iter().any(|y| g.same(y, x));
            match pred {
                IPred::Slt | IPred::Sle => (neg(*t) && g.same(*f, x)).then_some(x),
                IPred::Sgt | IPred::Sge => (neg(*f) && g.same(*t, x)).then_some(x),
                IPred::Eq | IPred::Ne | IPred::Ult | IPred::Ule | IPred::Ugt | IPred::Uge => None,
            }
        }),
        Inst::Bin {
            op: BinOp::Sub,
            w: bw,
            l,
            r,
        } if *bw == w => {
            let x = mask_of(g, *r, w)?;
            holds(g, *l, BinOp::Xor, x, *r).then_some(x)
        }
        Inst::Bin {
            op: BinOp::Xor,
            w: bw,
            l,
            r,
        } if *bw == w => [(*l, *r), (*r, *l)].into_iter().find_map(|(a, m)| {
            let x = mask_of(g, m, w)?;
            holds(g, a, BinOp::Add, x, m).then_some(x)
        }),
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Trunc { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }?;
    if w == g.word() {
        return helper(g, Helper::Llabs, w, vec![x], p);
    }
    let zero = konst(g, w, 0, p)?;
    let c = g.add(
        &Inst::ICmp {
            pred: IPred::Slt,
            w,
            l: x,
            r: zero,
        },
        MTy::I(1),
        p,
    )?;
    let t = un(g, UnOp::Neg, w, x, p)?;
    g.add(&Inst::Select { c, t, f: x }, MTy::I(w), p)
}

/// Turns a select of the lesser or greater of two word-wide values into
/// `min`, `max`, `umin` or `umax`.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `w` - The e-node's width.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn min_max(g: &mut EGraph, w: u8, p: Prov, node: &Inst) -> Option<Val> {
    let Inst::Select { c, t, f } = node else {
        return None;
    };
    if w != g.word() {
        return None;
    }
    let (h, a, b) = icmps(g, *c).into_iter().find_map(|(pred, cw, a, b)| {
        if cw != w {
            return None;
        }
        let straight = g.same(*t, a) && g.same(*f, b);
        let crossed = g.same(*t, b) && g.same(*f, a);
        let (lesser, greater) = match pred {
            IPred::Slt | IPred::Sle => (Helper::Min, Helper::Max),
            IPred::Sgt | IPred::Sge => (Helper::Max, Helper::Min),
            IPred::Ult | IPred::Ule => (Helper::UMin, Helper::UMax),
            IPred::Ugt | IPred::Uge => (Helper::UMax, Helper::UMin),
            IPred::Eq | IPred::Ne => return None,
        };
        if straight {
            Some((lesser, a, b))
        } else if crossed {
            Some((greater, a, b))
        } else {
            None
        }
    })?;
    helper(g, h, w, vec![a, b], p)
}

/// Folds chains of extensions and truncations, turns a zero extension of
/// a truncation into a mask and back, and a shift pair into an
/// extension.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn extend(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    match node {
        Inst::Ext {
            signed,
            from,
            to,
            x,
        } => {
            for (s1, k, m, y) in exts(g, *x) {
                if m != *from {
                    continue;
                }
                let joined = match (s1, *signed) {
                    (false, false | true) => Some(false),
                    (true, true) => Some(true),
                    (true, false) => None,
                };
                if let Some(s) = joined {
                    return ext(g, s, k, *to, y, p);
                }
            }
            if !*signed
                && let Some((_, y)) = truncs(g, *x)
                    .into_iter()
                    .find(|&(k, y)| k == *from && width(g, y) == Some(*to))
            {
                return bin_k(g, BinOp::And, *to, y, low(*from), p);
            }
            None
        }
        Inst::Trunc { to, x } => {
            if let Some((s, from, _, y)) = exts(g, *x).into_iter().next() {
                return match to.cmp(&from) {
                    std::cmp::Ordering::Equal => Some(y),
                    std::cmp::Ordering::Less => trunc(g, *to, y, p),
                    std::cmp::Ordering::Greater => ext(g, s, from, *to, y, p),
                };
            }
            let (_, y) = truncs(g, *x).into_iter().next()?;
            trunc(g, *to, y, p)
        }
        Inst::Bin {
            op: BinOp::And,
            w,
            l,
            r,
        } => {
            let m = g.konst(*r)?;
            let k = u8::try_from(m.trailing_ones()).ok()?;
            if !matches!(k, 8 | 16 | 32) || k >= *w || m != low(k) {
                return None;
            }
            let t = trunc(g, k, *l, p)?;
            ext(g, false, k, *w, t, p)
        }
        Inst::Bin {
            op: op @ (BinOp::AShr | BinOp::LShr),
            w,
            l,
            r,
        } => {
            let s = g.konst(*r)?;
            let (_, x, _) = with_const(g, *l, BinOp::Shl)
                .into_iter()
                .find(|&(sw, _, k)| sw == *w && k == s)?;
            if s == 0 || s >= u64::from(*w) {
                return None;
            }
            let k = *w - u8::try_from(s).ok()?;
            if *op == BinOp::LShr {
                return bin_k(g, BinOp::And, *w, x, low(k), p);
            }
            let t = trunc(g, k, x, p)?;
            ext(g, true, k, *w, t, p)
        }
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }
}

/// Folds the shifts and masks of a bit-field read.
///
/// A left then a right shift into one shift and a mask, a mask that keeps every bit a shift
/// left or the whole width, two masks into one, a mask a truncation
/// drops, and `x & x` or `x | x` into `x`.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn field(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    match node {
        Inst::Bin {
            op: BinOp::LShr,
            w,
            l,
            r,
        } => {
            let b = g.konst(*r)?;
            let (_, x, a) = with_const(g, *l, BinOp::Shl)
                .into_iter()
                .find(|&(sw, _, a)| sw == *w && a < b)?;
            if b >= u64::from(*w) {
                return None;
            }
            let keep = *w - u8::try_from(b).ok()?;
            let s = bin_k(g, BinOp::LShr, *w, x, b - a, p)?;
            bin_k(g, BinOp::And, *w, s, low(keep), p)
        }
        Inst::Bin {
            op: BinOp::And | BinOp::Or,
            l,
            r,
            ..
        } if g.same(*l, *r) => Some(*l),
        Inst::Bin {
            op: BinOp::And,
            w,
            l,
            r,
        } => {
            let m = g.konst(*r)?;
            if m == low(*w) {
                return Some(*l);
            }
            let shifted = with_const(g, *l, BinOp::LShr)
                .into_iter()
                .any(|(sw, _, s)| {
                    sw == *w
                        && s > 0
                        && s < u64::from(*w)
                        && u8::try_from(s).is_ok_and(|s| low(*w - s) & !m == 0)
                });
            let extended = exts(g, *l)
                .into_iter()
                .any(|(signed, k, to, _)| !signed && to == *w && low(k) & !m == 0);
            if shifted || extended {
                return Some(*l);
            }
            let (_, x, m2) = with_const(g, *l, BinOp::And).into_iter().next()?;
            bin_k(g, BinOp::And, *w, x, m & m2, p)
        }
        Inst::Trunc { to, x } => {
            let (_, y, _) = with_const(g, *x, BinOp::And)
                .into_iter()
                .find(|&(_, _, m)| low(*to) & !m == 0)?;
            trunc(g, *to, y, p)
        }
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }
}

/// Returns the 1-bit negation of a condition: the inverse compare when
/// it is one, else `c ^ 1`.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `c` - The 1-bit condition.
/// * `p` - The provenance.
fn negate(g: &mut EGraph, c: Val, p: Prov) -> Option<Val> {
    if let Some((pred, w, l, r)) = icmps(g, c).into_iter().next() {
        return g.add(
            &Inst::ICmp {
                pred: inverse(pred),
                w,
                l,
                r,
            },
            MTy::I(1),
            p,
        );
    }
    bin_k(g, BinOp::Xor, 1, c, 1, p)
}

/// Normalizes booleans: a negated compare is the inverse compare, a test
/// of a zero-extended condition is the condition, an equality of a
/// difference is an equality, and a 0/1 select is its condition.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `w` - The e-node's width.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn boolean(g: &mut EGraph, w: u8, p: Prov, node: &Inst) -> Option<Val> {
    match node {
        Inst::Bin {
            op: BinOp::Xor,
            w: 1,
            l,
            r,
        } if g.konst(*r) == Some(1) && !icmps(g, *l).is_empty() => negate(g, *l, p),
        Inst::Un {
            op: UnOp::Not,
            w: 1,
            x,
        } => negate(g, *x, p),
        Inst::ICmp {
            pred: pred @ (IPred::Eq | IPred::Ne),
            w: cw,
            l,
            r,
        } if g.konst(*r) == Some(0) => {
            if *cw == 1 {
                return if *pred == IPred::Ne {
                    Some(*l)
                } else {
                    negate(g, *l, p)
                };
            }
            if let Some((_, _, _, b)) = exts(g, *l)
                .into_iter()
                .find(|&(signed, k, to, _)| !signed && k == 1 && to == *cw)
            {
                return if *pred == IPred::Ne {
                    Some(b)
                } else {
                    negate(g, b, p)
                };
            }
            let (a, b) = bins(g, *l, BinOp::Xor)
                .into_iter()
                .chain(bins(g, *l, BinOp::Sub))
                .find(|&(bw, _, _)| bw == *cw)
                .map(|(_, a, b)| (a, b))?;
            g.add(
                &Inst::ICmp {
                    pred: *pred,
                    w: *cw,
                    l: a,
                    r: b,
                },
                MTy::I(1),
                p,
            )
        }
        Inst::Select { c, t, f } => {
            match (g.konst(*t), g.konst(*f)) {
                (Some(1), Some(0)) if w == 1 => return Some(*c),
                (Some(1), Some(0)) => return ext(g, false, 1, w, *c, p),
                (Some(0), Some(1)) => {
                    let n = negate(g, *c, p)?;
                    return if w == 1 {
                        Some(n)
                    } else {
                        ext(g, false, 1, w, n, p)
                    };
                }
                (Some(_) | None, Some(_) | None) => {}
            }
            let (_, c2, _) = with_const(g, *c, BinOp::Xor)
                .into_iter()
                .find(|&(bw, _, k)| bw == 1 && k == 1)?;
            g.add(
                &Inst::Select {
                    c: c2,
                    t: *f,
                    f: *t,
                },
                MTy::I(w),
                p,
            )
        }
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Bin { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Trunc { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => None,
    }
}

/// The simpler form a mixed boolean-arithmetic identity gives.
#[derive(Debug, Clone, Copy)]
enum Mba {
    /// One binary op of the two values.
    Bin(BinOp, Val, Val),
    /// The first value and the complement of the second.
    AndNot(Val, Val),
    /// The value negated.
    Neg(Val),
    /// The value's complement.
    Not(Val),
}

/// Applies the mixed boolean-arithmetic identities of two values:
///
/// * `(x ^ y) + 2 * (x & y)`, `(x | y) + (x & y)` and
///   `2 * (x | y) - (x ^ y)` are `x + y`;
/// * `(x & y) + (x ^ y)`, `(x + y) - (x & y)` and `(x & ~y) + y` are
///   `x | y`;
/// * `(x | y) - (x & y)`, `(x + y) - 2 * (x & y)` and
///   `(x & ~y) | (~x & y)` are `x ^ y`;
/// * `(x + y) - (x | y)` is `x & y`, and `x - (x & y)` is `x & ~y`;
/// * `~x + 1`, `~(x - 1)` and `0 - x` are `-x`, and `x ^ -1` is `~x`.
///
/// # Arguments
///
/// * `g` - The graph.
/// * `p` - The provenance.
/// * `node` - The e-node.
fn mba(g: &mut EGraph, p: Prov, node: &Inst) -> Option<Val> {
    let (op, w, l, r) = match node {
        Inst::Bin { op, w, l, r } => (*op, *w, *l, *r),
        Inst::Un {
            op: UnOp::Not,
            w,
            x,
        } => {
            let minus_one = with_const(g, *x, BinOp::Sub)
                .into_iter()
                .chain(
                    with_const(g, *x, BinOp::Add)
                        .into_iter()
                        .map(|(bw, y, c)| (bw, y, c.wrapping_neg() & low(bw))),
                )
                .find(|&(bw, _, c)| bw == *w && c == 1);
            let (_, y, _) = minus_one?;
            return un(g, UnOp::Neg, *w, y, p);
        }
        Inst::Const { .. }
        | Inst::FConst { .. }
        | Inst::Reg(_)
        | Inst::Frame(_)
        | Inst::Tls
        | Inst::Load { .. }
        | Inst::Ovf { .. }
        | Inst::Wide { .. }
        | Inst::Un { .. }
        | Inst::Ext { .. }
        | Inst::Trunc { .. }
        | Inst::Bitcast { .. }
        | Inst::Convert { .. }
        | Inst::FBin { .. }
        | Inst::FUn { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Select { .. }
        | Inst::Splat { .. }
        | Inst::Helper { .. }
        | Inst::Undef(_) => return None,
    };
    let and_not = |g: &EGraph, v: Val| -> Vec<(Val, Val)> {
        pairs(g, v, BinOp::And)
            .into_iter()
            .flat_map(|(x, n)| {
                uns(g, n, UnOp::Not)
                    .into_iter()
                    .map(move |y| (x, y))
                    .collect::<Vec<_>>()
            })
            .collect()
    };
    let found = match op {
        BinOp::Add => [(l, r), (r, l)].into_iter().find_map(|(a, b)| {
            if g.konst(b) == Some(1)
                && let Some(x) = uns(g, a, UnOp::Not).into_iter().next()
            {
                return Some(Mba::Neg(x));
            }
            for (x, y) in pairs(g, a, BinOp::Xor) {
                if halves(g, b)
                    .into_iter()
                    .any(|h| holds(g, h, BinOp::And, x, y))
                {
                    return Some(Mba::Bin(BinOp::Add, x, y));
                }
            }
            for (x, y) in pairs(g, a, BinOp::Or) {
                if holds(g, b, BinOp::And, x, y) {
                    return Some(Mba::Bin(BinOp::Add, x, y));
                }
            }
            for (x, y) in pairs(g, a, BinOp::And) {
                if holds(g, b, BinOp::Xor, x, y) {
                    return Some(Mba::Bin(BinOp::Or, x, y));
                }
            }
            and_not(g, a)
                .into_iter()
                .find(|&(_, y)| g.same(y, b))
                .map(|(x, y)| Mba::Bin(BinOp::Or, x, y))
        }),
        BinOp::Sub => {
            let mut hit = None;
            if g.konst(l) == Some(0) {
                hit = Some(Mba::Neg(r));
            }
            for (x, y) in pairs(g, l, BinOp::Or) {
                if hit.is_none() && holds(g, r, BinOp::And, x, y) {
                    hit = Some(Mba::Bin(BinOp::Xor, x, y));
                }
            }
            for (x, y) in pairs(g, l, BinOp::Add) {
                if hit.is_some() {
                    break;
                }
                if halves(g, r)
                    .into_iter()
                    .any(|h| holds(g, h, BinOp::And, x, y))
                {
                    hit = Some(Mba::Bin(BinOp::Xor, x, y));
                } else if holds(g, r, BinOp::And, x, y) {
                    hit = Some(Mba::Bin(BinOp::Or, x, y));
                } else if holds(g, r, BinOp::Or, x, y) {
                    hit = Some(Mba::Bin(BinOp::And, x, y));
                }
            }
            for h in halves(g, l) {
                for (x, y) in pairs(g, h, BinOp::Or) {
                    if hit.is_none() && holds(g, r, BinOp::Xor, x, y) {
                        hit = Some(Mba::Bin(BinOp::Add, x, y));
                    }
                }
            }
            if hit.is_none()
                && let Some((_, y)) = pairs(g, r, BinOp::And)
                    .into_iter()
                    .find(|&(x, _)| g.same(x, l))
            {
                hit = Some(Mba::AndNot(l, y));
            }
            hit
        }
        BinOp::Or => and_not(g, l).into_iter().find_map(|(x, y)| {
            and_not(g, r)
                .into_iter()
                .any(|(y2, x2)| g.same(x, x2) && g.same(y, y2))
                .then_some(Mba::Bin(BinOp::Xor, x, y))
        }),
        BinOp::Xor => (g.konst(r) == Some(low(w))).then_some(Mba::Not(l)),
        BinOp::Mul
        | BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::And
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::Rotl
        | BinOp::Rotr => None,
    };
    match found? {
        Mba::Bin(out, x, y) => bin(g, out, w, x, y, p),
        Mba::AndNot(x, y) => {
            let n = un(g, UnOp::Not, w, y, p)?;
            bin(g, BinOp::And, w, x, n, p)
        }
        Mba::Neg(x) => un(g, UnOp::Neg, w, x, p),
        Mba::Not(x) => un(g, UnOp::Not, w, x, p),
    }
}
