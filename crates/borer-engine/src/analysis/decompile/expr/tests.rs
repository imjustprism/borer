/// A bit scan against the width is a leading-zero count.
///
/// A compiler writes `clz` as `(width - 1) - bsr(x)` and spells the
/// subtraction as an exclusive or, so both forms have to read as the
/// count, and the width has to match the operands.
#[test]
fn a_bit_scan_against_the_width_is_a_count() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let scan = Expr::Un(super::UnOp::Bsr, Box::new(x.clone()));
    let want = Expr::Un(super::UnOp::Lzcnt, Box::new(x));
    assert_eq!(
        super::fold(Op::Xor, scan.clone(), Expr::Const(63), 64),
        want
    );
    assert_eq!(
        super::fold(Op::Xor, Expr::Const(63), scan.clone(), 64),
        want
    );
    assert_eq!(
        super::fold(Op::Sub, Expr::Const(63), scan.clone(), 64),
        want
    );
    assert_eq!(
        super::fold(Op::Xor, scan.clone(), Expr::Const(31), 32),
        want
    );
    assert_ne!(super::fold(Op::Xor, scan.clone(), Expr::Const(7), 64), want);
    assert_ne!(super::fold(Op::Xor, scan, Expr::Const(31), 64), want);
}

/// Every rewritten identity is true for all inputs, checked numerically.
///
/// A rewrite that is merely believed changes what the code does, silently
/// and everywhere. These are the five the folder applies, evaluated over
/// a spread of values including the edges where carries wrap.
#[test]
fn the_rewritten_identities_hold() {
    let values: Vec<u64> = vec![
        0,
        1,
        2,
        3,
        0xff,
        0x100,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x7fff_ffff_ffff_ffff,
        0x8000_0000_0000_0000,
        u64::MAX,
        0xdead_beef_cafe_babe,
        0x0123_4567_89ab_cdef,
    ];
    for &x in &values {
        for &y in &values {
            assert_eq!(
                (x ^ y).wrapping_add(2u64.wrapping_mul(x & y)),
                x.wrapping_add(y),
                "(x^y) + 2*(x&y) == x+y at {x:#x}, {y:#x}"
            );
            assert_eq!(
                (x ^ y).wrapping_add((x & y) << 1),
                x.wrapping_add(y),
                "(x^y) + ((x&y)<<1) == x+y at {x:#x}, {y:#x}"
            );
            assert_eq!(
                (x & y).wrapping_add(x | y),
                x.wrapping_add(y),
                "(x&y) + (x|y) == x+y at {x:#x}, {y:#x}"
            );
            assert_eq!(
                (x ^ y).wrapping_add(x & y),
                x | y,
                "(x^y) + (x&y) == x|y at {x:#x}, {y:#x}"
            );
            assert_eq!(
                (x | y).wrapping_sub(x & y),
                x ^ y,
                "(x|y) - (x&y) == x^y at {x:#x}, {y:#x}"
            );
            assert_eq!(
                (x | y).wrapping_sub(x ^ y),
                x & y,
                "(x|y) - (x^y) == x&y at {x:#x}, {y:#x}"
            );
        }
    }
}

/// The folder applies those identities to the expressions it builds.
#[test]
fn an_obfuscated_addition_folds_back() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let y = Expr::Var(Key::Reg(crate::isa::x86::Register::RCX));
    let bin = |o: Op, a: &Expr, b: &Expr| Expr::Bin(o, Box::new(a.clone()), Box::new(b.clone()));
    let plain = bin(Op::Add, &x, &y);
    let doubled = bin(Op::Mul, &bin(Op::And, &x, &y), &Expr::Const(2));
    assert_eq!(
        super::fold(Op::Add, bin(Op::Xor, &x, &y), doubled, 64),
        plain
    );
    let shifted = bin(Op::Shl, &bin(Op::And, &x, &y), &Expr::Const(1));
    assert_eq!(
        super::fold(Op::Add, bin(Op::Xor, &x, &y), shifted, 64),
        plain
    );
    assert_eq!(
        super::fold(Op::Sub, bin(Op::Or, &x, &y), bin(Op::And, &x, &y), 64),
        bin(Op::Xor, &x, &y)
    );
    let doubled = bin(Op::Mul, &Expr::Const(2), &bin(Op::And, &y, &x));
    assert_eq!(
        super::fold(Op::Add, doubled, bin(Op::Xor, &x, &y), 64),
        plain
    );
}

/// A division by a constant whose bits within the width are all zero
/// is a division by zero, and stays as it is written.
///
/// The divisor `0x100` of an 8-bit division is zero in that width:
/// folding it divides by its low bits, which are zero.
#[test]
fn a_divisor_zero_in_its_width_is_no_constant() {
    for op in [Op::Div, Op::Rem] {
        let folded = super::fold(op, Expr::Const(5), Expr::Const(0x100), 8);
        assert_eq!(
            folded,
            Expr::Bin(op, Box::new(Expr::Const(5)), Box::new(Expr::Const(0x100)))
        );
    }
    assert_eq!(
        super::fold(Op::Div, Expr::Const(0x205), Expr::Const(0x102), 8),
        Expr::Const(2)
    );
}

/// A multiply and shift is a division only when it divides every
/// dividend of its width.
///
/// `0x92492493` is `2^34 / 7` rounded up, but a shift of two leaves its
/// error too large: at `0xfffffffb` the high half shifted is
/// `0x24924924`, one more than the quotient by seven. Compilers divide by
/// seven with the 33-bit magic instead; `0xaaaaaaab >> 1`, a third,
/// holds everywhere and still reads as the division, of the 32 bits the
/// multiply read.
#[test]
fn a_magic_that_misses_a_dividend_is_no_division() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let shifted = |m: u64, s: u64| {
        let hi = Expr::Bin(Op::MulHi(32), Box::new(Expr::Const(m)), Box::new(x.clone()));
        super::fold(Op::Shr, hi, Expr::Const(s), 32)
    };
    assert!(
        !matches!(shifted(0x9249_2493, 2), Expr::Bin(Op::Div, ..)),
        "{:?}",
        shifted(0x9249_2493, 2)
    );
    let word = Expr::Bin(
        Op::And,
        Box::new(x.clone()),
        Box::new(Expr::Const(0xffff_ffff)),
    );
    assert_eq!(
        shifted(0xaaaa_aaab, 1),
        Expr::Bin(Op::Div, Box::new(word), Box::new(Expr::Const(3)))
    );
    let wrong = (0x9249_2493u128 * 0xffff_fffb) >> 34;
    assert_eq!((wrong, 0xffff_fffbu128 / 7), (0x2492_4924, 0x2492_4923));
}

/// A quotient times its divisor less the dividend is the remainder's
/// negation, no remainder: `7 * (x / 7) - x` stays as it is.
#[test]
fn a_product_less_its_dividend_is_no_remainder() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let q = Expr::Bin(Op::SDiv, Box::new(x.clone()), Box::new(Expr::Const(7)));
    let product = Expr::Bin(Op::Mul, Box::new(q), Box::new(Expr::Const(7)));
    for bits in [32, 64] {
        let folded = super::fold(Op::Sub, product.clone(), x.clone(), bits);
        assert!(
            !matches!(folded, Expr::Bin(Op::SRem | Op::Rem, ..)),
            "{folded:?}"
        );
        let rem = super::fold(Op::Sub, x.clone(), product.clone(), bits);
        assert!(matches!(rem, Expr::Bin(Op::SRem, ..)), "{rem:?}");
    }
}

/// A signed magic quotient is a division only when its magic has the
/// sign its shape expects and rounds every negative dividend toward
/// zero.
///
/// `0x92492493` is the negative magic of a division by seven, the one
/// whose shape adds the dividend back; without that, at `x = 7` the
/// product shifted is `-1` and its sign fix makes `0`, not `1`. `2^30`
/// divides by four exactly, so at `x = -4` the high half is already the
/// quotient `-1` and the sign fix makes it `0`. `0x66666667 >> 1` with
/// its fix is a fifth on every dividend and still reads as the division.
#[test]
fn a_signed_magic_that_misses_a_dividend_is_no_division() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let fixed = |m: u64, s: u64| {
        let hi = Expr::Bin(
            Op::SMulHi(32),
            Box::new(Expr::Const(m)),
            Box::new(x.clone()),
        );
        let q = super::fold(Op::Sar, hi, Expr::Const(s), 32);
        let sign = super::fold(Op::Shr, q.clone(), Expr::Const(31), 32);
        super::fold(Op::Add, q, sign, 32)
    };
    for (m, s) in [(0x9249_2493, 2), (0x4000_0000, 0)] {
        let out = fixed(m, s);
        assert!(!matches!(out, Expr::Bin(Op::SDiv, ..)), "{m:#x}: {out:?}");
    }
    let fifth = Expr::Bin(
        Op::SDiv,
        Box::new(Expr::Sext(Box::new(x.clone()), 32)),
        Box::new(Expr::Const(5)),
    );
    assert_eq!(fixed(0x6666_6667, 1), fifth);
    let wrong = |m: i64, s: u32, v: i64| {
        let q = (m * v) >> (32 + s);
        q + i64::from(q < 0)
    };
    let negative = i64::from(0x9249_2493u32.cast_signed());
    assert_eq!((wrong(negative, 2, 7), wrong(0x4000_0000, 0, -4)), (0, 0));
}

/// A halving through a sign is a division only at the sign's width.
///
/// `(x + (x >>> 63)) >> 1` as a 32-bit shift adds a sign bit the 32-bit
/// value does not have: at `x = 0x80000001` it is `0xc0000000`, where
/// the quotient by two is `0xc0000001`. The same shape as a 64-bit shift
/// is the division.
#[test]
fn a_halving_through_another_widths_sign_is_no_division() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let halved = |bits: u8| {
        let sign = Expr::Bin(Op::Shr, Box::new(x.clone()), Box::new(Expr::Const(63)));
        let sum = Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(sign));
        super::fold(Op::Sar, sum, Expr::Const(1), bits)
    };
    assert!(
        !matches!(halved(32), Expr::Bin(Op::SDiv, ..)),
        "{:?}",
        halved(32)
    );
    assert_eq!(
        halved(64),
        Expr::Bin(Op::SDiv, Box::new(x), Box::new(Expr::Const(2)))
    );
}

/// A 32-bit shift by 31 through the sign is no division by `2^31`.
///
/// `(x + ((int32_t)x >> 31 & 0x7fffffff)) >> 31` is `-1` at
/// `x = INT_MIN`; a 32-bit division by `0x80000000` is a division by
/// `INT_MIN`, which gives `1`. A shift by 30 is still a quotient.
#[test]
fn a_shift_by_the_sign_bit_is_no_power_quotient() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let quotient = |k: u64| {
        let lane = Expr::Sext(Box::new(x.clone()), 32);
        let sign = Expr::Bin(Op::Sar, Box::new(lane), Box::new(Expr::Const(31)));
        let fix = Expr::Bin(Op::And, Box::new(sign), Box::new(Expr::Const((1 << k) - 1)));
        let sum = Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(fix));
        super::fold(Op::Sar, sum, Expr::Const(k), 32)
    };
    assert!(
        !matches!(quotient(31), Expr::Bin(Op::SDiv, ..)),
        "{:?}",
        quotient(31)
    );
    assert!(
        matches!(quotient(30), Expr::Bin(Op::SDiv, ..)),
        "{:?}",
        quotient(30)
    );
}

/// A shift of a sign-extended lane halves through the lane's sign.
///
/// `(int32_t)(x + ((x >> 63) & 1)) >> 1` keeps the low 32 bits of a sum
/// fixed by the 64-bit sign: at `x = 0x80000000` it is `0xc0000000`
/// sign-extended, where `x / 2` is `0x40000000`. Fixed by the lane's own
/// sign it is `(int32_t)x / 2`.
#[test]
fn a_lane_halves_through_its_own_sign() {
    let x = Expr::Var(Key::Reg(crate::isa::x86::Register::RAX));
    let halved = |sign: Expr| {
        let fix = Expr::Bin(Op::And, Box::new(sign), Box::new(Expr::Const(1)));
        let sum = Expr::Bin(Op::Add, Box::new(x.clone()), Box::new(fix));
        super::fold(Op::Sar, Expr::Sext(Box::new(sum), 32), Expr::Const(1), 64)
    };
    let wide = Expr::Bin(Op::Sar, Box::new(x.clone()), Box::new(Expr::Const(63)));
    assert!(
        !matches!(halved(wide.clone()), Expr::Bin(Op::SDiv, ..)),
        "{:?}",
        halved(wide)
    );
    let lane = Expr::Sext(Box::new(x.clone()), 32);
    let own = Expr::Bin(Op::Sar, Box::new(lane.clone()), Box::new(Expr::Const(31)));
    assert_eq!(
        halved(own),
        Expr::Bin(Op::SDiv, Box::new(lane), Box::new(Expr::Const(2)))
    );
}

use super::{Expr, Key, Op};
use crate::analysis::decompile::expr_render::{compact_literal, vector_equality};

/// A float constant renders compactly, never as a 336-character decimal.
///
/// A value with many digits takes an exponent, and the bytes of a wide
/// string moved through `movsd` (or a subnormal) take the exact
/// hexadecimal literal.
#[test]
fn float_constants_render_compactly() {
    use super::Ty;
    use crate::analysis::decompile::expr_render::render_fconst;
    let f64s = |v: f64| render_fconst(v.to_bits(), Ty::F64);
    assert_eq!(f64s(2.0), "2.0");
    assert_eq!(f64s(0.1), "0.1");
    assert_eq!(f64s(-1.5), "-1.5");
    assert_eq!(f64s(1e30), "1e30");
    assert_eq!(f64s(1.25e-25), "1.25e-25");
    assert_eq!(
        render_fconst(0x0073_0074_006e_0065, Ty::F64),
        "0x1.30074006e0065p-1016"
    );
    assert_eq!(render_fconst(1, Ty::F64), "0x0.0000000000001p-1022");
    assert_eq!(render_fconst(0x41, Ty::F32), "0x0.000082p-126f");
    assert_eq!(render_fconst(0x3f80_0000, Ty::F32), "1.0f");
}

/// Builds the gathered-mask expression a fixed string compare produces.
///
/// # Arguments
///
/// * `gather` - The mask-gathering mnemonic.
/// * `lanes` - The lane-comparing mnemonic.
fn mask_of(gather: &str, lanes: &str) -> Expr {
    Expr::Call(
        gather.to_owned(),
        vec![Expr::Call(
            lanes.to_owned(),
            vec![Expr::Const(1), Expr::Const(2)],
        )],
    )
}

/// An all-lanes-equal mask test is the two vectors being equal.
///
/// # Panics
///
/// When the fold does not recognise the idiom.
#[test]
fn a_lane_mask_test_is_a_vector_comparison() {
    let m = mask_of("pmovmskb", "pcmpeqb");
    assert_eq!(
        vector_equality(&m, &Expr::Const(0xffff)),
        Some((&Expr::Const(1), &Expr::Const(2)))
    );
    let v = mask_of("vpmovmskb", "vpcmpeqb");
    assert!(vector_equality(&v, &Expr::Const(0xffff_ffff)).is_some());
}

/// A mask tested against anything but all ones is some other test.
///
/// # Panics
///
/// When the fold claims an idiom that is not there.
#[test]
fn a_partial_lane_mask_test_is_not_a_vector_comparison() {
    let m = mask_of("pmovmskb", "pcmpeqb");
    assert_eq!(vector_equality(&m, &Expr::Const(0x8000)), None);
    assert_eq!(vector_equality(&m, &Expr::Const(0)), None);
    let other = mask_of("pmovmskb", "pcmpgtb");
    assert_eq!(vector_equality(&other, &Expr::Const(0xffff)), None);
}

/// Signature literals become `__FUNCSIG__`, foreign ones keep the name,
/// paths keep two components, prose stays.
///
/// # Panics
///
/// When a rendering disagrees with its expectation.
#[test]
fn literals_compact() {
    let sig = "\"int __cdecl Foo::Bar(void)\"";
    assert_eq!(compact_literal(sig, "Foo::Bar"), "__FUNCSIG__");
    assert_eq!(compact_literal(sig, "Baz"), "__FUNCSIG__(Foo::Bar)");
    let path = "\"C:\\\\ws\\\\code\\\\foundation\\\\util/fourcc.h\"";
    assert_eq!(compact_literal(path, "x"), "\"util/fourcc.h\"");
    assert_eq!(compact_literal("\"f.IsValid()\"", "x"), "\"f.IsValid()\"");
    assert_eq!(compact_literal("\"a/b.h\"", "x"), "\"a/b.h\"");
}
