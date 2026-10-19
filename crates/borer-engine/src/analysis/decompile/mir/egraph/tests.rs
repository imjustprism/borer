//! Tests of the e-graph: each rule checked against the MIR evaluator.
//!
//! A rule's check seeds a graph with the forms it rewrites, saturates it
//! with that rule alone, and then evaluates every form of every class
//! against the class's extracted form, operands read through their own
//! classes' extracted forms, on edge and seeded random inputs: every pair
//! of 8-bit operands at 8 bits, and the edge values of every width paired
//! with each other and with random values above it. A form that computes
//! other bits than its class fails the rule.

use super::super::eval::{Inputs, eval};
use super::super::{BinOp, Body, IPred, Inst, MTy, Prov, UnOp, Val, WideOp};
use super::{EGraph, Rule, simplify};
use crate::analysis::decompile::expr::Key;
use crate::analysis::decompile::helper::Helper;
use crate::analysis::decompile::verify::low;
use crate::isa::x86::Register;

/// The registers a seed's leaves read, in order.
const LEAVES: [Register; 3] = [Register::RAX, Register::RCX, Register::RDX];

/// The random inputs each check adds to its edge values.
const RANDOM: usize = 3000;

/// The values every width is checked at, before they are cut to it.
const EDGES: [u64; 22] = [
    0,
    1,
    2,
    3,
    7,
    10,
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
    u64::MAX,
    u64::MAX - 1,
    u64::MAX - 6,
    1000,
    0x1234_5678_9abc_def0,
];

/// A starting state of fixed registers.
struct Regs([u64; 3]);

impl Inputs for Regs {
    fn reg(&self, k: Key) -> Option<u64> {
        LEAVES
            .iter()
            .zip(self.0)
            .find(|&(r, _)| Key::Reg(*r) == k)
            .map(|(_, v)| v)
    }

    fn sp(&self) -> u64 {
        0x1000
    }

    fn tls(&self) -> u64 {
        0x9000
    }

    fn load(&mut self, _: u64, _: u64) -> Option<u64> {
        None
    }
}

/// A small seeded generator.
struct Rng(u64);

impl Rng {
    /// Returns the next value.
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// Builds one seed body.
struct Seed {
    /// The body built so far.
    body: Body,
    /// How many leaves it reads.
    vars: usize,
}

impl Seed {
    /// Starts a seed at a machine word.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word's width.
    fn new(word: u8) -> Self {
        Self {
            body: Body::new(word),
            vars: 0,
        }
    }

    /// Appends a value.
    ///
    /// # Arguments
    ///
    /// * `inst` - Its operation.
    /// * `ty` - Its type.
    fn push(&mut self, inst: Inst, ty: MTy) -> Val {
        self.body.push(inst, ty, Prov::ENTRY)
    }

    /// Appends the low `w` bits of leaf register `i`.
    ///
    /// # Arguments
    ///
    /// * `i` - The leaf, below [`LEAVES`]'s length.
    /// * `w` - The width.
    fn leaf(&mut self, i: usize, w: u8) -> Val {
        self.vars = self.vars.max(i + 1);
        let r = self.push(Inst::Reg(Key::Reg(LEAVES[i])), MTy::I(64));
        if w == 64 {
            r
        } else {
            self.push(Inst::Trunc { to: w, x: r }, MTy::I(w))
        }
    }

    /// Appends a constant.
    ///
    /// # Arguments
    ///
    /// * `w` - The width.
    /// * `bits` - The value, cut to the width.
    fn k(&mut self, w: u8, bits: u64) -> Val {
        self.push(
            Inst::Const {
                w,
                bits: bits & low(w),
            },
            MTy::I(w),
        )
    }

    /// Appends a binary op.
    ///
    /// # Arguments
    ///
    /// * `op` - The op.
    /// * `w` - The width.
    /// * `l` - The left operand.
    /// * `r` - The right operand.
    fn bin(&mut self, op: BinOp, w: u8, l: Val, r: Val) -> Val {
        self.push(Inst::Bin { op, w, l, r }, MTy::I(w))
    }

    /// Appends a binary op by a constant.
    ///
    /// # Arguments
    ///
    /// * `op` - The op.
    /// * `w` - The width.
    /// * `l` - The left operand.
    /// * `c` - The constant.
    fn bk(&mut self, op: BinOp, w: u8, l: Val, c: u64) -> Val {
        let r = self.k(w, c);
        self.bin(op, w, l, r)
    }

    /// Appends a unary op.
    ///
    /// # Arguments
    ///
    /// * `op` - The op.
    /// * `w` - The width.
    /// * `x` - The operand.
    fn un(&mut self, op: UnOp, w: u8, x: Val) -> Val {
        self.push(Inst::Un { op, w, x }, MTy::I(w))
    }

    /// Appends a multiply-high by a constant.
    ///
    /// # Arguments
    ///
    /// * `op` - The signedness.
    /// * `w` - The width.
    /// * `x` - The operand.
    /// * `m` - The constant.
    fn wide(&mut self, op: WideOp, w: u8, x: Val, m: u64) -> Val {
        let r = self.k(w, m);
        self.push(Inst::Wide { op, w, l: x, r }, MTy::I(w))
    }

    /// Appends an extension.
    ///
    /// # Arguments
    ///
    /// * `signed` - Sign- rather than zero-extend.
    /// * `from` - The operand's width.
    /// * `to` - The result's width.
    /// * `x` - The operand.
    fn ext(&mut self, signed: bool, from: u8, to: u8, x: Val) -> Val {
        self.push(
            Inst::Ext {
                signed,
                from,
                to,
                x,
            },
            MTy::I(to),
        )
    }

    /// Appends a truncation.
    ///
    /// # Arguments
    ///
    /// * `to` - The width kept.
    /// * `x` - The operand.
    fn trunc(&mut self, to: u8, x: Val) -> Val {
        self.push(Inst::Trunc { to, x }, MTy::I(to))
    }

    /// Appends a compare.
    ///
    /// # Arguments
    ///
    /// * `pred` - The predicate.
    /// * `w` - The operands' width.
    /// * `l` - The left operand.
    /// * `r` - The right operand.
    fn icmp(&mut self, pred: IPred, w: u8, l: Val, r: Val) -> Val {
        self.push(Inst::ICmp { pred, w, l, r }, MTy::I(1))
    }

    /// Appends a select.
    ///
    /// # Arguments
    ///
    /// * `w` - The width.
    /// * `c` - The condition.
    /// * `t` - The value when set.
    /// * `f` - The value when clear.
    fn select(&mut self, w: u8, c: Val, t: Val, f: Val) -> Val {
        self.push(Inst::Select { c, t, f }, MTy::I(w))
    }

    /// Finishes the seed with its root.
    ///
    /// # Arguments
    ///
    /// * `root` - The value checked.
    /// * `w` - The width its operands are drawn at, which picks the inputs.
    fn done(self, root: Val, w: u8) -> Case {
        Case {
            body: self.body,
            root,
            w,
            vars: self.vars,
        }
    }
}

/// One seed to check.
struct Case {
    /// The body.
    body: Body,
    /// The value the rule should rewrite.
    root: Val,
    /// The width its operands are drawn at.
    w: u8,
    /// How many leaves it reads.
    vars: usize,
}

/// Returns the inputs a case is checked on.
///
/// # Arguments
///
/// * `w` - The operands' width: every value of the leaves at 8 bits, else
///   the edges paired and seeded random values.
/// * `vars` - How many leaves the values read.
fn inputs(w: u8, vars: usize) -> Vec<[u64; 3]> {
    if w <= 8 {
        let all: u64 = if vars <= 1 { 0xff } else { 0xffff };
        return (0..=all)
            .map(|v| [v & 0xff, v >> 8, v.wrapping_mul(0x9e37)])
            .collect();
    }
    let mut rng = Rng(0x2545_f491_4f6c_dd1d ^ u64::from(w));
    let mut out: Vec<[u64; 3]> = EDGES
        .iter()
        .flat_map(|&a| EDGES.iter().map(move |&b| [a, b, a ^ b]))
        .collect();
    for _ in 0..RANDOM {
        let (a, b, c) = (rng.next(), rng.next(), rng.next());
        let pick = rng.next();
        let a = if pick & 3 == 0 {
            EDGES[usize::try_from(pick >> 8).unwrap_or(0) % EDGES.len()]
        } else {
            a
        };
        out.push([a, b, c]);
    }
    out
}

/// Writes every class's cheapest form into one body, then each other form
/// of the class over those, and returns the pairs that must agree.
///
/// # Arguments
///
/// * `g` - The graph.
fn pairs(g: &EGraph) -> (Body, Vec<(Val, Val)>) {
    let best = g.best();
    let mut order: Vec<(u32, usize)> = best
        .iter()
        .enumerate()
        .filter_map(|(i, b)| b.map(|(c, _)| (c, i)))
        .collect();
    order.sort_unstable();
    let mut body = Body::new(g.word);
    let mut emitted: Vec<Option<Val>> = vec![None; g.classes.len()];
    let map = |emitted: &[Option<Val>], v: Val| emitted[super::index(g.find(v))].expect("emitted");
    for &(_, i) in &order {
        let (_, k) = best[i].expect("costed");
        let node = &g.classes[i].nodes[k];
        let inst = super::remap(node, |v| map(&emitted, v));
        emitted[i] = Some(body.push(inst, g.classes[i].ty, Prov::ENTRY));
    }
    let mut out = Vec::new();
    for &(_, i) in &order {
        let rep = emitted[i].expect("emitted");
        for node in &g.classes[i].nodes {
            let ready = super::operands(node)
                .into_iter()
                .all(|v| emitted[super::index(g.find(v))].is_some());
            if ready {
                let inst = super::remap(node, |v| map(&emitted, v));
                out.push((rep, body.push(inst, g.classes[i].ty, Prov::ENTRY)));
            }
        }
    }
    (body, out)
}

/// Checks a rule on its cases.
///
/// # Arguments
///
/// * `rule` - The rule.
/// * `cases` - The seeds.
///
/// # Returns
///
/// For each case, whether the rule added a form to its root's class.
fn check(rule: Rule, cases: &[Case]) -> Vec<bool> {
    cases
        .iter()
        .map(|case| {
            let (mut g, root) = EGraph::seed(&case.body, case.root).expect("seed");
            g.saturate(&[rule]);
            let (body, agree) = pairs(&g);
            for input in inputs(case.w, case.vars) {
                for &(a, b) in &agree {
                    let va = eval(&body, a, &mut Regs(input));
                    let vb = eval(&body, b, &mut Regs(input));
                    assert_eq!(
                        va,
                        vb,
                        "{rule:?} at {} bits on {input:x?}: {:?} vs {:?}",
                        case.w,
                        body.nodes[super::index(a)].inst,
                        body.nodes[super::index(b)].inst
                    );
                }
            }
            g.nodes(root).len() > 1
        })
        .collect()
}

/// Tells whether a class's forms include an op.
///
/// # Arguments
///
/// * `case` - The seed.
/// * `rule` - The rule saturated with.
/// * `want` - Picks the op looked for.
fn makes(case: &Case, rule: Rule, want: impl Fn(&Inst) -> bool) -> bool {
    let (mut g, root) = EGraph::seed(&case.body, case.root).expect("seed");
    g.saturate(&[rule]);
    g.nodes(root).iter().any(want)
}

/// The widths every rule is checked at.
const WIDTHS: [u8; 4] = [8, 16, 32, 64];

/// Returns the multiplier and post-shift a compiler uses for an unsigned
/// division, and whether it needs the add-and-halve fix.
///
/// # Arguments
///
/// * `w` - The width.
/// * `d` - The divisor, at least 2.
fn umagic(w: u8, d: u64) -> (u64, u32, bool) {
    let wn = u32::from(w);
    for s in 0..wn {
        let two = 1u128 << (wn + s);
        let m = two.div_ceil(u128::from(d));
        let e = m * u128::from(d) - two;
        if m < 1u128 << wn && e * u128::from(low(w)) < two {
            return (u64::try_from(m).expect("fits"), s, false);
        }
    }
    let s = 64 - (d - 1).leading_zeros();
    let two = 1u128 << (wn + s);
    let m = two.div_ceil(u128::from(d)) - (1u128 << wn);
    (u64::try_from(m).expect("fits"), s, true)
}

/// Builds the unsigned quotient by a compiler's magic constant.
///
/// # Arguments
///
/// * `w` - The width.
/// * `d` - The divisor.
/// * `nudge` - Added to the multiplier, to seed a wrong constant.
fn udiv_case(w: u8, d: u64, nudge: u64) -> Case {
    let (m, s, fix) = umagic(w, d);
    let m = m.wrapping_add(nudge);
    let mut b = Seed::new(64);
    let x = b.leaf(0, w);
    let t = b.wide(WideOp::UMulHi, w, x, m);
    let root = if fix {
        let diff = b.bin(BinOp::Sub, w, x, t);
        let half = b.bk(BinOp::LShr, w, diff, 1);
        let sum = b.bin(BinOp::Add, w, half, t);
        if s > 1 {
            b.bk(BinOp::LShr, w, sum, u64::from(s - 1))
        } else {
            sum
        }
    } else if s > 0 {
        b.bk(BinOp::LShr, w, t, u64::from(s))
    } else {
        t
    };
    b.done(root, w)
}

/// Tells whether a compiler's multiplier for a `k`-bit unsigned division
/// by `d` times the largest dividend fits in `w` bits, so one `w`-bit
/// multiply computes the product whole.
///
/// # Arguments
///
/// * `k` - The dividend's width.
/// * `w` - The multiply's width.
/// * `d` - The divisor.
fn wide_fits(k: u8, w: u8, d: u64) -> bool {
    let (m, _, fix) = umagic(k, d);
    let full = u128::from(m) + if fix { 1u128 << k } else { 0 };
    full * u128::from(low(k)) <= u128::from(low(w))
}

/// Builds the unsigned quotient of a `k`-bit value computed with one
/// `w`-bit multiply of its zero extension, then truncated back.
///
/// # Arguments
///
/// * `k` - The dividend's width.
/// * `w` - The multiply's width.
/// * `d` - The divisor.
fn udiv_wide_case(k: u8, w: u8, d: u64) -> Case {
    let (m, s, fix) = umagic(k, d);
    let m = if fix { m + (1 << k) } else { m };
    let mut b = Seed::new(64);
    let x = b.leaf(0, k);
    let z = b.ext(false, k, w, x);
    let prod = b.bk(BinOp::Mul, w, z, m);
    let q = b.bk(BinOp::LShr, w, prod, u64::from(k) + u64::from(s));
    let root = b.trunc(k, q);
    b.done(root, k)
}

/// Returns the multiplier and post-shift a compiler uses for a signed
/// division by a positive constant.
///
/// # Arguments
///
/// * `w` - The width.
/// * `d` - The divisor, at least 2 and below `2^(w-1)`.
fn smagic(w: u8, d: u64) -> (u128, u32) {
    let wn = u32::from(w);
    for s in 0..wn {
        let two = 1u128 << (wn + s);
        let m = two.div_ceil(u128::from(d));
        let e = m * u128::from(d) - two;
        if e > 0 && m < 1u128 << wn && e << (wn - 1) < two {
            return (m, s);
        }
    }
    panic!("no magic for {d} at {w}");
}

/// The sign fix a signed quotient ends with.
#[derive(Debug, Clone, Copy)]
enum Fix {
    /// Adds the quotient's sign bit.
    QuotientBit,
    /// Adds the dividend's sign bit.
    DividendBit,
    /// Subtracts the dividend's sign mask.
    DividendMask,
}

/// Builds the signed quotient by a compiler's magic constant.
///
/// # Arguments
///
/// * `w` - The width.
/// * `d` - The divisor.
/// * `fix` - The sign fix.
/// * `nudge` - Added to the multiplier, to seed a wrong constant.
fn sdiv_case(w: u8, d: u64, fix: Fix, nudge: u64) -> Case {
    let (m, s) = smagic(w, d);
    let m = u64::try_from(m & u128::from(low(w)))
        .expect("fits")
        .wrapping_add(nudge);
    let mut b = Seed::new(64);
    let x = b.leaf(0, w);
    let mut t = b.wide(WideOp::SMulHi, w, x, m);
    if m & (1 << (w - 1)) != 0 {
        t = b.bin(BinOp::Add, w, t, x);
    }
    let q = if s > 0 {
        b.bk(BinOp::AShr, w, t, u64::from(s))
    } else {
        t
    };
    let root = match fix {
        Fix::QuotientBit => {
            let sign = b.bk(BinOp::LShr, w, q, u64::from(w) - 1);
            b.bin(BinOp::Add, w, q, sign)
        }
        Fix::DividendBit => {
            let sign = b.bk(BinOp::LShr, w, x, u64::from(w) - 1);
            b.bin(BinOp::Add, w, sign, q)
        }
        Fix::DividendMask => {
            let mask = b.bk(BinOp::AShr, w, x, u64::from(w) - 1);
            b.bin(BinOp::Sub, w, q, mask)
        }
    };
    b.done(root, w)
}

/// Builds the signed quotient of a `k`-bit value computed with one `w`-bit
/// multiply of its sign extension, as `movsxd; imul; shr 63; sar; add`.
///
/// # Arguments
///
/// * `k` - The dividend's width.
/// * `w` - The multiply's width.
/// * `d` - The divisor.
fn sdiv_wide_case(k: u8, w: u8, d: u64) -> Case {
    let (m, s) = smagic(k, d);
    let m = u64::try_from(m).expect("fits");
    let mut b = Seed::new(64);
    let x = b.leaf(0, k);
    let z = b.ext(true, k, w, x);
    let prod = b.bk(BinOp::Mul, w, z, m);
    let sign = b.bk(BinOp::LShr, w, prod, u64::from(w) - 1);
    let sign = b.trunc(k, sign);
    let q = b.bk(BinOp::AShr, w, prod, u64::from(k) + u64::from(s));
    let q = b.trunc(k, q);
    let root = b.bin(BinOp::Add, k, q, sign);
    b.done(root, k)
}

/// The divisors the division rules are checked with.
const DIVISORS: [u64; 12] = [2, 3, 5, 6, 7, 9, 10, 12, 25, 100, 641, 1000];

/// Tells whether a form is an unsigned quotient, or one zero-extended.
///
/// # Arguments
///
/// * `n` - The form.
fn is_udiv(n: &Inst) -> bool {
    matches!(
        n,
        Inst::Bin {
            op: BinOp::UDiv,
            ..
        } | Inst::Ext { signed: false, .. }
    )
}

/// An unsigned multiply-high and shift by a compiler's constant is the
/// quotient at every width, with and without the add fix; a constant one
/// off is never taken for a quotient it does not compute.
#[test]
fn an_unsigned_magic_division_is_the_quotient() {
    let mut good = Vec::new();
    let mut wrong = Vec::new();
    for w in WIDTHS {
        for d in DIVISORS.into_iter().filter(|&d| d < low(w)) {
            good.push(udiv_case(w, d, 0));
            wrong.push(udiv_case(w, d, 1));
            wrong.push(udiv_case(w, d, u64::MAX));
        }
    }
    for (k, w) in [(8, 32), (16, 32), (8, 64), (32, 64)] {
        for d in DIVISORS
            .into_iter()
            .filter(|&d| d < low(k) && wide_fits(k, w, d))
        {
            good.push(udiv_wide_case(k, w, d));
        }
    }
    check(Rule::UDivMagic, &good);
    check(Rule::UDivMagic, &wrong);
    for case in &good {
        assert!(makes(case, Rule::UDivMagic, is_udiv), "{:?}", case.body);
    }
}

/// A signed multiply-high, shift and either sign fix by a compiler's
/// constant is the signed quotient at every width.
#[test]
fn a_signed_magic_division_is_the_quotient() {
    let mut good = Vec::new();
    let mut wrong = Vec::new();
    for w in WIDTHS {
        for d in DIVISORS
            .into_iter()
            .filter(|&d| d < low(w) >> 1 && !d.is_power_of_two())
        {
            for fix in [Fix::QuotientBit, Fix::DividendBit, Fix::DividendMask] {
                good.push(sdiv_case(w, d, fix, 0));
                wrong.push(sdiv_case(w, d, fix, 1));
                wrong.push(sdiv_case(w, d, fix, u64::MAX));
            }
        }
    }
    for (k, w) in [(8, 32), (16, 32), (8, 64), (32, 64)] {
        for d in DIVISORS
            .into_iter()
            .filter(|&d| d < low(k) >> 1 && !d.is_power_of_two())
        {
            good.push(sdiv_wide_case(k, w, d));
        }
    }
    check(Rule::SDivMagic, &good);
    check(Rule::SDivMagic, &wrong);
    for case in &good {
        let sdiv = |n: &Inst| {
            matches!(
                n,
                Inst::Bin {
                    op: BinOp::SDiv,
                    ..
                }
            )
        };
        assert!(makes(case, Rule::SDivMagic, sdiv), "{:?}", case.body);
    }
}

/// `x - (x / d) * d` and `x + (x / d) * -d` are the remainder, signed and
/// unsigned.
#[test]
fn a_dividend_less_its_multiple_is_the_remainder() {
    let mut cases = Vec::new();
    for w in WIDTHS {
        for (div, neg) in [
            (BinOp::UDiv, false),
            (BinOp::SDiv, false),
            (BinOp::UDiv, true),
            (BinOp::SDiv, true),
        ] {
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let q = b.bk(div, w, x, 10);
            let root = if neg {
                let prod = b.bk(BinOp::Mul, w, q, 10u64.wrapping_neg());
                b.bin(BinOp::Add, w, x, prod)
            } else {
                let prod = b.bk(BinOp::Mul, w, q, 10);
                b.bin(BinOp::Sub, w, x, prod)
            };
            cases.push(b.done(root, w));
        }
    }
    assert!(check(Rule::Rem, &cases).into_iter().all(|f| f));
}

/// A shift by a power of two is a multiply, and a sum of multiples of
/// one value (a `lea` chain) is one multiply.
#[test]
fn shifts_and_sums_of_multiples_are_one_multiply() {
    let mut cases = Vec::new();
    for w in WIDTHS {
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let root = b.bk(BinOp::Shl, w, x, 3);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let root = b.bk(BinOp::Mul, w, x, 16);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let root = b.bin(BinOp::Add, w, x, x);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let four = b.bk(BinOp::Shl, w, x, 2);
        let five = b.bin(BinOp::Add, w, four, x);
        let root = b.bin(BinOp::Add, w, five, five);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let three = b.bk(BinOp::Mul, w, x, 3);
        let root = b.bk(BinOp::Mul, w, three, 5);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let sixteen = b.bk(BinOp::Shl, w, x, 4);
        let root = b.bin(BinOp::Sub, w, sixteen, x);
        cases.push(b.done(root, w));
    }
    assert!(check(Rule::Scale, &cases).into_iter().all(|f| f));
}

/// A left shift or'ed, added or xor'ed with the complementary right shift
/// is a rotate; shifts that do not add up to the width are not.
#[test]
fn complementary_shifts_are_a_rotate() {
    let mut cases = Vec::new();
    let mut misses = Vec::new();
    for w in WIDTHS {
        for op in [BinOp::Or, BinOp::Add, BinOp::Xor] {
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let hi = b.bk(BinOp::Shl, w, x, 3);
            let lo = b.bk(BinOp::LShr, w, x, u64::from(w) - 3);
            let root = b.bin(op, w, lo, hi);
            cases.push(b.done(root, w));
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let hi = b.bk(BinOp::Shl, w, x, 3);
            let lo = b.bk(BinOp::LShr, w, x, u64::from(w) - 4);
            let root = b.bin(op, w, hi, lo);
            misses.push(b.done(root, w));
        }
    }
    assert!(check(Rule::Rotate, &cases).into_iter().all(|f| f));
    assert!(check(Rule::Rotate, &misses).into_iter().all(|f| !f));
}

/// A form of one value at a width.
type Form1 = fn(&mut Seed, u8, Val) -> Val;

/// A form of two values at a width.
type Form2 = fn(&mut Seed, u8, Val, Val) -> Val;

/// The absolute-value idioms: two selects and two sign-mask forms.
const ABS_FORMS: [Form1; 4] = [
    |b, w, x| {
        let zero = b.k(w, 0);
        let neg = b.un(UnOp::Neg, w, x);
        let c = b.icmp(IPred::Slt, w, x, zero);
        b.select(w, c, neg, x)
    },
    |b, w, x| {
        let zero = b.k(w, 0);
        let neg = b.un(UnOp::Neg, w, x);
        let c = b.icmp(IPred::Sge, w, x, zero);
        b.select(w, c, x, neg)
    },
    |b, w, x| {
        let m = b.bk(BinOp::AShr, w, x, u64::from(w) - 1);
        let flip = b.bin(BinOp::Xor, w, x, m);
        b.bin(BinOp::Sub, w, flip, m)
    },
    |b, w, x| {
        let m = b.bk(BinOp::AShr, w, x, u64::from(w) - 1);
        let sum = b.bin(BinOp::Add, w, m, x);
        b.bin(BinOp::Xor, w, sum, m)
    },
];

/// The select and sign-mask forms of an absolute value are `llabs` at the
/// word and the select at another width.
#[test]
fn absolute_value_idioms_are_one_form() {
    let mut cases = Vec::new();
    for (word, w) in [(64, 64), (32, 32), (64, 32), (64, 8), (64, 16)] {
        for form in ABS_FORMS {
            let mut b = Seed::new(word);
            let x = b.leaf(0, w);
            let root = form(&mut b, w, x);
            cases.push(b.done(root, w));
        }
    }
    let fired = check(Rule::Abs, &cases);
    for (case, fired) in cases.iter().zip(fired) {
        let select_at_word = case.body.word != case.w
            && matches!(
                case.body.nodes[super::index(case.root)].inst,
                Inst::Select { .. }
            );
        assert!(fired || select_at_word, "{:?}", case.body);
    }
}

/// A select of the lesser or greater of two word-wide values is `min`,
/// `max`, `umin` or `umax`, whichever way round the compare is.
#[test]
fn a_select_of_the_lesser_is_min() {
    let mut cases = Vec::new();
    for word in [32, 64] {
        for pred in [
            IPred::Slt,
            IPred::Sle,
            IPred::Sgt,
            IPred::Sge,
            IPred::Ult,
            IPred::Ule,
            IPred::Ugt,
            IPred::Uge,
        ] {
            for crossed in [false, true] {
                let mut b = Seed::new(word);
                let x = b.leaf(0, word);
                let y = b.leaf(1, word);
                let c = b.icmp(pred, word, x, y);
                let root = if crossed {
                    b.select(word, c, y, x)
                } else {
                    b.select(word, c, x, y)
                };
                cases.push(b.done(root, word));
            }
        }
    }
    assert!(check(Rule::MinMax, &cases).into_iter().all(|f| f));
    let helper = |n: &Inst| {
        matches!(
            n,
            Inst::Helper {
                h: Helper::Min | Helper::Max | Helper::UMin | Helper::UMax,
                ..
            }
        )
    };
    assert!(cases.iter().all(|c| makes(c, Rule::MinMax, helper)));
}

/// Chains of extensions and truncations fold, a zero extension of a
/// truncation is a mask and back, and a shift pair is an extension.
#[test]
fn extension_chains_fold() {
    let mut cases = Vec::new();
    for (k, m, w) in [(8, 16, 32), (8, 32, 64), (16, 32, 64)] {
        for (s1, s2) in [(false, false), (true, true), (false, true), (true, false)] {
            let mut b = Seed::new(64);
            let x = b.leaf(0, k);
            let e = b.ext(s1, k, m, x);
            let root = b.ext(s2, m, w, e);
            cases.push(b.done(root, k));
        }
        for to in [k, (k + m) / 2, m] {
            for signed in [false, true] {
                let mut b = Seed::new(64);
                let x = b.leaf(0, k);
                let e = b.ext(signed, k, w, x);
                let root = b.trunc(to, e);
                cases.push(b.done(root, k));
            }
        }
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let t = b.trunc(m, x);
        let root = b.trunc(k, t);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let t = b.trunc(k, x);
        let root = b.ext(false, k, w, t);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let root = b.bk(BinOp::And, w, x, low(k));
        cases.push(b.done(root, w));
        for op in [BinOp::AShr, BinOp::LShr] {
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let s = u64::from(w - k);
            let up = b.bk(BinOp::Shl, w, x, s);
            let root = b.bk(op, w, up, s);
            cases.push(b.done(root, w));
        }
    }
    let fired = check(Rule::Extend, &cases);
    assert!(fired.iter().filter(|&&f| f).count() >= cases.len() - 3);
}

/// The shifts and masks of a bit-field read fold to one shift and mask.
#[test]
fn field_reads_fold_to_one_shift_and_mask() {
    let mut cases = Vec::new();
    for w in WIDTHS {
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let up = b.bk(BinOp::Shl, w, x, 2);
        let root = b.bk(BinOp::LShr, w, up, 5);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let down = b.bk(BinOp::LShr, w, x, 3);
        let root = b.bk(BinOp::And, w, down, low(w));
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let inner = b.bk(BinOp::And, w, x, 0x7ff0);
        let root = b.bk(BinOp::And, w, inner, 0xff3);
        cases.push(b.done(root, w));
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let root = b.bk(BinOp::And, w, x, u64::MAX);
        cases.push(b.done(root, w));
        for op in [BinOp::And, BinOp::Or] {
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let y = b.leaf(0, w);
            let root = b.bin(op, w, x, y);
            cases.push(b.done(root, w));
        }
        if w > 8 {
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let masked = b.bk(BinOp::And, w, x, 0xff);
            let root = b.trunc(8, masked);
            cases.push(b.done(root, w));
        }
    }
    assert!(check(Rule::Field, &cases).into_iter().all(|f| f));
}

/// A negated compare is the inverse compare, a test of a zero-extended
/// condition is the condition, an equality of a difference or an `xor` is
/// an equality, and a 0/1 select is its condition.
#[test]
fn booleans_normalize() {
    let preds = [
        IPred::Eq,
        IPred::Ne,
        IPred::Ult,
        IPred::Ule,
        IPred::Ugt,
        IPred::Uge,
        IPred::Slt,
        IPred::Sle,
        IPred::Sgt,
        IPred::Sge,
    ];
    let mut cases = Vec::new();
    for w in WIDTHS {
        for pred in preds {
            let mut b = Seed::new(64);
            let (x, y) = (b.leaf(0, w), b.leaf(1, w));
            let c = b.icmp(pred, w, x, y);
            let root = b.bk(BinOp::Xor, 1, c, 1);
            cases.push(b.done(root, w));
            let mut b = Seed::new(64);
            let (x, y) = (b.leaf(0, w), b.leaf(1, w));
            let c = b.icmp(pred, w, x, y);
            let root = b.un(UnOp::Not, 1, c);
            cases.push(b.done(root, w));
        }
        for (pred, op) in [
            (IPred::Eq, BinOp::Xor),
            (IPred::Ne, BinOp::Sub),
            (IPred::Eq, BinOp::Sub),
        ] {
            let mut b = Seed::new(64);
            let (x, y) = (b.leaf(0, w), b.leaf(1, w));
            let diff = b.bin(op, w, x, y);
            let zero = b.k(w, 0);
            let root = b.icmp(pred, w, diff, zero);
            cases.push(b.done(root, w));
        }
        for pred in [IPred::Eq, IPred::Ne] {
            let mut b = Seed::new(64);
            let (x, y) = (b.leaf(0, w), b.leaf(1, w));
            let c = b.icmp(IPred::Ult, w, x, y);
            let z = b.ext(false, 1, 32, c);
            let zero = b.k(32, 0);
            let root = b.icmp(pred, 32, z, zero);
            cases.push(b.done(root, w));
        }
        for (t, f) in [(1, 0), (0, 1)] {
            let mut b = Seed::new(64);
            let (x, y) = (b.leaf(0, w), b.leaf(1, w));
            let c = b.icmp(IPred::Slt, w, x, y);
            let (t, f) = (b.k(w, t), b.k(w, f));
            let root = b.select(w, c, t, f);
            cases.push(b.done(root, w));
        }
        let mut b = Seed::new(64);
        let (x, y) = (b.leaf(0, w), b.leaf(1, w));
        let c = b.icmp(IPred::Slt, w, x, y);
        let n = b.bk(BinOp::Xor, 1, c, 1);
        let root = b.select(w, n, x, y);
        cases.push(b.done(root, w));
    }
    assert!(check(Rule::Bool, &cases).into_iter().all(|f| f));
}

/// The mixed boolean-arithmetic forms, each equal to a single op.
const MBA_FORMS: [Form2; 15] = [
    |b, w, x, y| {
        let xor = b.bin(BinOp::Xor, w, x, y);
        let and = b.bin(BinOp::And, w, y, x);
        let two = b.bk(BinOp::Shl, w, and, 1);
        b.bin(BinOp::Add, w, two, xor)
    },
    |b, w, x, y| {
        let or = b.bin(BinOp::Or, w, x, y);
        let and = b.bin(BinOp::And, w, x, y);
        b.bin(BinOp::Add, w, or, and)
    },
    |b, w, x, y| {
        let and = b.bin(BinOp::And, w, x, y);
        let xor = b.bin(BinOp::Xor, w, y, x);
        b.bin(BinOp::Add, w, and, xor)
    },
    |b, w, x, y| {
        let or = b.bin(BinOp::Or, w, x, y);
        let and = b.bin(BinOp::And, w, x, y);
        b.bin(BinOp::Sub, w, or, and)
    },
    |b, w, x, y| {
        let add = b.bin(BinOp::Add, w, x, y);
        let and = b.bin(BinOp::And, w, x, y);
        let two = b.bk(BinOp::Mul, w, and, 2);
        b.bin(BinOp::Sub, w, add, two)
    },
    |b, w, x, y| {
        let add = b.bin(BinOp::Add, w, x, y);
        let and = b.bin(BinOp::And, w, x, y);
        b.bin(BinOp::Sub, w, add, and)
    },
    |b, w, x, y| {
        let or = b.bin(BinOp::Or, w, x, y);
        let two = b.bin(BinOp::Add, w, or, or);
        let xor = b.bin(BinOp::Xor, w, x, y);
        b.bin(BinOp::Sub, w, two, xor)
    },
    |b, w, x, y| {
        let add = b.bin(BinOp::Add, w, x, y);
        let or = b.bin(BinOp::Or, w, y, x);
        b.bin(BinOp::Sub, w, add, or)
    },
    |b, w, x, y| {
        let and = b.bin(BinOp::And, w, x, y);
        b.bin(BinOp::Sub, w, x, and)
    },
    |b, w, x, y| {
        let n = b.un(UnOp::Not, w, y);
        let and = b.bin(BinOp::And, w, x, n);
        b.bin(BinOp::Add, w, and, y)
    },
    |b, w, x, y| {
        let ny = b.un(UnOp::Not, w, y);
        let nx = b.un(UnOp::Not, w, x);
        let a = b.bin(BinOp::And, w, x, ny);
        let c = b.bin(BinOp::And, w, nx, y);
        b.bin(BinOp::Or, w, a, c)
    },
    |b, w, x, _| {
        let n = b.un(UnOp::Not, w, x);
        b.bk(BinOp::Add, w, n, 1)
    },
    |b, w, x, _| {
        let dec = b.bk(BinOp::Sub, w, x, 1);
        b.un(UnOp::Not, w, dec)
    },
    |b, w, x, _| {
        let zero = b.k(w, 0);
        b.bin(BinOp::Sub, w, zero, x)
    },
    |b, w, x, _| b.bk(BinOp::Xor, w, x, u64::MAX),
];

/// The mixed boolean-arithmetic identities hold and fire, whichever way
/// round their operands come.
#[test]
fn mixed_boolean_arithmetic_simplifies() {
    let mut cases = Vec::new();
    for w in WIDTHS {
        for form in MBA_FORMS {
            let mut b = Seed::new(64);
            let (x, y) = (b.leaf(0, w), b.leaf(1, w));
            let root = form(&mut b, w, x, y);
            cases.push(b.done(root, w));
        }
    }
    assert!(check(Rule::Mba, &cases).into_iter().all(|f| f));
}

/// An op of constants folds to its value, a quotient by zero does not,
/// and a constant moves to the right of a commutative op or a compare.
#[test]
fn constants_fold_and_move_right() {
    let mut folds = Vec::new();
    let mut moves = Vec::new();
    for w in WIDTHS {
        for op in [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::AShr,
            BinOp::Rotr,
        ] {
            let mut b = Seed::new(64);
            let x = b.k(w, 0xfedc_ba98_7654_3219);
            let root = b.bk(op, w, x, 5);
            folds.push(b.done(root, w));
        }
        let mut b = Seed::new(64);
        let x = b.k(w, 7);
        let e = b.ext(true, w, 64, x);
        let root = b.trunc(8, e);
        folds.push(b.done(root, w));
        for op in [BinOp::Add, BinOp::Mul, BinOp::And, BinOp::Or, BinOp::Xor] {
            let mut b = Seed::new(64);
            let x = b.leaf(0, w);
            let k = b.k(w, 9);
            let root = b.bin(op, w, k, x);
            moves.push(b.done(root, w));
        }
        let mut b = Seed::new(64);
        let x = b.leaf(0, w);
        let k = b.k(w, 9);
        let root = b.icmp(IPred::Slt, w, k, x);
        moves.push(b.done(root, w));
    }
    assert!(check(Rule::Fold, &folds).into_iter().all(|f| f));
    assert!(check(Rule::Commute, &moves).into_iter().all(|f| f));
    let mut b = Seed::new(64);
    let x = b.k(32, 5);
    let root = b.bk(BinOp::UDiv, 32, x, 0);
    assert!(!check(Rule::Fold, &[b.done(root, 32)])[0]);
}

/// Every rule together keeps every class sound on a mix of idioms.
#[test]
fn every_rule_together_is_sound() {
    let mut cases = vec![
        udiv_case(32, 10, 0),
        sdiv_case(32, 7, Fix::QuotientBit, 0),
        udiv_case(64, 1000, 0),
    ];
    let mut b = Seed::new(64);
    let x = b.leaf(0, 32);
    let q = b.bk(BinOp::UDiv, 32, x, 10);
    let four = b.bk(BinOp::Shl, 32, q, 2);
    let five = b.bin(BinOp::Add, 32, four, q);
    let ten = b.bin(BinOp::Add, 32, five, five);
    let root = b.bin(BinOp::Sub, 32, x, ten);
    cases.push(b.done(root, 32));
    for case in &cases {
        let (mut g, _) = EGraph::seed(&case.body, case.root).expect("seed");
        g.saturate(&Rule::ALL);
        let (body, agree) = pairs(&g);
        for input in inputs(case.w, case.vars) {
            for &(a, b) in &agree {
                assert_eq!(
                    eval(&body, a, &mut Regs(input)),
                    eval(&body, b, &mut Regs(input))
                );
            }
        }
    }
    let out = simplify(&cases[3].body, cases[3].root, &Rule::ALL).expect("simplify");
    assert!(
        out.body.nodes.iter().any(|n| matches!(
            n.inst,
            Inst::Bin {
                op: BinOp::URem,
                ..
            }
        )),
        "{:?}",
        out.body
    );
    assert!(out.cost < out.input_cost);
}

/// The same body simplifies to the same bytes twice, and the graph never
/// holds more than its budget.
#[test]
fn simplifying_is_deterministic_and_bounded() {
    let case = sdiv_case(64, 1000, Fix::DividendBit, 0);
    let one = simplify(&case.body, case.root, &Rule::ALL).expect("simplify");
    let two = simplify(&case.body, case.root, &Rule::ALL).expect("simplify");
    assert_eq!(one.body, two.body);
    assert_eq!(one.root, two.root);
    let (mut g, _) = EGraph::seed(&case.body, case.root).expect("seed");
    let budget = g.budget;
    g.saturate(&Rule::ALL);
    assert!(g.count <= budget);
}
