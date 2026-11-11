//! The builder rewrites, each checked against the evaluator.

use super::*;

/// The constructors beside [`fold`]: masks, unary operators, sign
/// extension, partial writes, selects, the equality folds of
/// [`Cond::simplify`], and taking an addend out of a sum.
///
/// # Arguments
///
/// * `t` - The tally.
/// * `d` - The values.
pub(super) fn builders(t: &mut Tally, d: &Domain) {
    let (w, xs, ys, one) = (d.w, d.xs.as_slice(), d.ys.as_slice(), &[0u64][..]);
    let cut = |e: &Expr, m: u64| b(Op::And, e, &k(m));
    let inner = b(
        Op::Add,
        &cut(&X, 0xffff_ffff),
        &b(Op::Mul, &cut(&Y, 0xffff), &k(3)),
    );
    t.same(
        "sext(x) reads through low cuts",
        &Expr::Sext(Box::new(inner.clone()), 16),
        &sign_extend(inner.clone(), 16),
        w,
        xs,
        ys,
    );
    t.same(
        "mask reads through low cuts",
        &cut(&inner, 0xff),
        &mask(inner, 0xff),
        w,
        xs,
        ys,
    );
    for (name, e) in [
        ("mulhi fits its width", b(Op::MulHi(w), &X, &Y)),
        ("rotate fits its width", b(Op::Rol(w), &X, &k(3))),
    ] {
        t.same(
            name,
            &cut(&e, lane(w)),
            &mask(e.clone(), lane(w)),
            w,
            xs,
            ys,
        );
    }
    let unops = [
        UnOp::Neg,
        UnOp::Not,
        UnOp::Bswap,
        UnOp::Tzcnt,
        UnOp::Lzcnt,
        UnOp::Popcnt,
        UnOp::Bsf,
        UnOp::Bsr,
    ];
    for op in unops {
        for &c in xs {
            let before = Expr::Un(op, Box::new(k(c)));
            t.same("unary folding", &before, &unary(op, k(c), w), w, one, one);
        }
    }
    for op in [UnOp::Neg, UnOp::Not] {
        let twice = Expr::Un(op, Box::new(Expr::Un(op, Box::new(X))));
        t.same(
            "op(op(x))",
            &twice,
            &unary(op, Expr::Un(op, Box::new(X)), w),
            w,
            xs,
            one,
        );
    }
    for from in [8u8, 16, 32] {
        for &c in &d.cs {
            let before = Expr::Sext(Box::new(k(c)), from);
            t.same("sext(c)", &before, &sign_extend(k(c), from), w, one, one);
        }
        for inner in [8u8, 16, 32].into_iter().filter(|b| *b <= from) {
            let x = Expr::Sext(Box::new(X), inner);
            let before = Expr::Sext(Box::new(x.clone()), from);
            t.same("sext(sext(x))", &before, &sign_extend(x, from), w, xs, one);
        }
    }
    for (bits, shift) in [(8u8, 0u8), (8, 8), (16, 0), (32, 0)]
        .into_iter()
        .filter(|&(bits, shift)| bits + shift <= w)
    {
        let field = lane(bits) << shift;
        let placed = b(
            Op::Shl,
            &b(Op::And, &Y, &k(lane(bits))),
            &k(u64::from(shift)),
        );
        let before = b(Op::Or, &b(Op::And, &X, &k(!field)), &placed);
        t.same(
            "merge_bits",
            &before,
            &merge_bits(X, Y, bits, shift),
            64,
            xs,
            ys,
        );
    }
    let test = Expr::Cond(Box::new(cond(C::l, Flags::Cmp(X, Y, w))));
    for &c in &d.cs {
        for &e in &d.ds {
            for (name, l) in [
                ("(x & e) & c", b(Op::And, &X, &k(e))),
                ("(x << e) & c", b(Op::Shl, &X, &k(e % 64))),
                ("(x >> e) & c", b(Op::Shr, &X, &k(e % 64))),
            ] {
                t.fold(name, (Op::And, l, k(c)), w, xs, one);
            }
            let l = b(Op::Or, &b(Op::And, &X, &k(e)), &Y);
            t.fold(
                "((x & e) | y) & c",
                (Op::And, l, k(c)),
                w,
                xs,
                &[0, 0xa5, lane(w)],
            );
        }
        t.fold(
            "(x | y) & c",
            (Op::And, b(Op::Or, &X, &Y), k(c)),
            w,
            xs,
            &d.ds,
        );
        for (name, l) in [
            ("cond & c", test.clone()),
            ("*(uint8_t*)x & c", Expr::Deref(Box::new(X), Ty::U8)),
            ("*(uint16_t*)x & c", Expr::Deref(Box::new(X), Ty::U16)),
            ("eax & c", Expr::Var(Key::Reg(Register::EAX))),
        ] {
            t.fold(name, (Op::And, l, k(c)), w, xs, one);
        }
    }
    for cc in CCS {
        let test = cond(cc, Flags::Cmp(X, Y, w));
        for (name, a, z) in [
            ("c ? 1 : 0", k(1), k(0)),
            ("c ? 0 : 1", k(0), k(1)),
            ("c ? x : x", X, X),
        ] {
            let before = Expr::Ternary(
                Box::new(test.clone()),
                Box::new(a.clone()),
                Box::new(z.clone()),
            );
            t.same(name, &before, &ternary(test.clone(), a, z), w, xs, ys);
        }
        for &c in &d.cs {
            for &e in &d.ds {
                let decided = cond(cc, Flags::Cmp(k(c), k(e), w));
                let before = Expr::Ternary(Box::new(decided.clone()), Box::new(X), Box::new(Y));
                t.same(
                    "decided ? x : y",
                    &before,
                    &ternary(decided, X, Y),
                    w,
                    &[0x12],
                    &[0x34],
                );
            }
        }
    }
    let all = k(lane(w));
    for (cc, sat) in [(C::b, true), (C::o, true), (C::ae, false), (C::no, false)] {
        let carry = cond(cc, Flags::Carry(b(Op::MulHi(w), &X, &Y)));
        for product in [b(Op::Mul, &X, &Y), b(Op::Mul, &Y, &X)] {
            let (a, z) = if sat {
                (all.clone(), product)
            } else {
                (product, all.clone())
            };
            let before = Expr::Ternary(
                Box::new(carry.clone()),
                Box::new(a.clone()),
                Box::new(z.clone()),
            );
            t.same("mul_sat", &before, &ternary(carry.clone(), a, z), w, xs, ys);
        }
    }
    for (cc, sat) in [(C::b, true), (C::ae, false)] {
        let carry = cond(cc, Flags::Add(X, Y, w));
        let sum = b(Op::Add, &X, &Y);
        let (a, z) = if sat {
            (all.clone(), sum)
        } else {
            (sum, all.clone())
        };
        let before = Expr::Ternary(
            Box::new(carry.clone()),
            Box::new(a.clone()),
            Box::new(z.clone()),
        );
        t.same("add_sat", &before, &ternary(carry, a, z), w, xs, ys);
    }
    let diff = b(Op::Sub, &X, &Y);
    for (cc, zero_first) in [(C::b, true), (C::be, true), (C::a, false), (C::ae, false)] {
        let test = cond(cc, Flags::Cmp(X, Y, w));
        let (arm_t, arm_f) = if zero_first {
            (k(0), diff.clone())
        } else {
            (diff.clone(), k(0))
        };
        let before = Expr::Ternary(
            Box::new(test.clone()),
            Box::new(arm_t.clone()),
            Box::new(arm_f.clone()),
        );
        let after = ternary(test, arm_t, arm_f);
        if w >= 64 {
            t.same("sub sat", &before, &after, w, xs, ys);
            assert!(
                matches!(&after, Expr::Helper(Helper::SubSat, args) if args.len() == 2 && args[0] == X && args[1] == Y),
                "{cc:?} at {w}: {after:?}"
            );
        } else {
            assert!(
                matches!(after, Expr::Ternary(..)),
                "{cc:?} at {w} folded: {after:?}"
            );
        }
    }
    let signed = ternary(cond(C::l, Flags::Cmp(X, Y, w)), k(0), diff);
    let swapped = ternary(cond(C::b, Flags::Cmp(X, Y, w)), k(0), b(Op::Sub, &Y, &X));
    let other = ternary(cond(C::b, Flags::Cmp(X, Y, w)), k(0), b(Op::Sub, &X, &k(1)));
    let called = Expr::Call("g".to_owned(), vec![X]);
    let calling = ternary(
        cond(C::b, Flags::Cmp(called.clone(), Y, w)),
        k(0),
        b(Op::Sub, &called, &Y),
    );
    assert!(
        matches!(signed, Expr::Ternary(..))
            && !matches!(swapped, Expr::Helper(Helper::SubSat, _))
            && !matches!(other, Expr::Helper(Helper::SubSat, _)),
        "width {w}: {signed:?} {swapped:?} {other:?}"
    );
    if w >= 64 {
        assert!(
            matches!(calling, Expr::Helper(Helper::SubSat, ref args) if args.len() == 2 && args[0] == called && args[1] == Y),
            "{calling:?}"
        );
    } else {
        assert!(
            matches!(calling, Expr::Ternary(..)),
            "width {w} folded a call: {calling:?}"
        );
    }
    for cc in [C::l, C::le, C::g, C::ge, C::b, C::be, C::a, C::ae] {
        let test = cond(cc, Flags::Cmp(X, Y, w));
        for (a, z) in [(X, Y), (Y, X)] {
            let before = Expr::Ternary(
                Box::new(test.clone()),
                Box::new(a.clone()),
                Box::new(z.clone()),
            );
            let after = ternary(test.clone(), a, z);
            if w >= 64 {
                t.same("extremum", &before, &after, w, xs, ys);
                assert!(
                    matches!(&after, Expr::Helper(_, args) if args.len() == 2 && args[0] == X && args[1] == Y),
                    "{cc:?} at {w}: {after:?}"
                );
            } else {
                assert!(
                    matches!(after, Expr::Ternary(..)),
                    "{cc:?} at {w} folded: {after:?}"
                );
            }
        }
    }
    for cc in [C::e, C::ne] {
        let stayed = ternary(cond(cc, Flags::Cmp(X, Y, w)), X, Y);
        assert!(
            !matches!(stayed, Expr::Helper(..)),
            "{cc:?} at {w} became {stayed:?}"
        );
    }
    let third = ternary(cond(C::a, Flags::Cmp(X, Y, w)), X, k(1));
    assert!(
        matches!(third, Expr::Ternary(..)),
        "a third value at {w} became {third:?}"
    );
    let neg = Expr::Un(UnOp::Neg, Box::new(X));
    for cc in [C::l, C::le, C::g, C::ge, C::s, C::ns] {
        for flags in [Flags::Cmp(X, k(0), w), Flags::Cmp(k(0), X, w)] {
            let test = cond(cc, flags);
            for (a, z) in [(neg.clone(), X), (X, neg.clone())] {
                let before = Expr::Ternary(
                    Box::new(test.clone()),
                    Box::new(a.clone()),
                    Box::new(z.clone()),
                );
                let after = ternary(test.clone(), a, z);
                let is_abs = match &after {
                    Expr::Helper(Helper::Llabs, args) => args.len() == 1 && args[0] == X,
                    Expr::Un(UnOp::Neg, inner) => {
                        matches!(inner.as_ref(), Expr::Helper(Helper::Llabs, args) if args.len() == 1 && args[0] == X)
                    }
                    _ => false,
                };
                if w >= 64 {
                    t.same("absolute", &before, &after, w, xs, ys);
                    assert!(is_abs, "{cc:?} at {w}: {after:?}");
                } else {
                    assert!(
                        matches!(after, Expr::Ternary(..)),
                        "{cc:?} at {w} folded: {after:?}"
                    );
                }
            }
        }
    }
    for cc in [C::e, C::ne, C::b, C::a] {
        let stayed = ternary(cond(cc, Flags::Cmp(X, k(0), w)), neg.clone(), X);
        assert!(
            !matches!(stayed, Expr::Helper(..) | Expr::Un(UnOp::Neg, _)),
            "{cc:?} at {w} became {stayed:?}"
        );
    }
    let other = ternary(cond(C::s, Flags::Cmp(k(0), X, w)), Y, neg);
    assert!(
        matches!(other, Expr::Ternary(..)),
        "a third value at {w} became {other:?}"
    );
    let sign = b(Op::Sar, &X, &k(63));
    let is_sign_abs = |e: &Expr| matches!(e, Expr::Helper(Helper::Llabs, args) if args.len() == 1 && args[0] == X);
    for (before, after) in [
        (
            b(Op::Sub, &b(Op::Xor, &X, &sign), &sign),
            fold(Op::Sub, b(Op::Xor, &X, &sign), sign.clone(), w),
        ),
        (
            b(Op::Xor, &b(Op::Add, &X, &sign), &sign),
            fold(Op::Xor, b(Op::Add, &X, &sign), sign.clone(), w),
        ),
    ] {
        if w >= 64 {
            t.same("sign absolute", &before, &after, w, xs, ys);
            assert!(is_sign_abs(&after), "{after:?}");
        } else {
            assert!(!is_sign_abs(&after), "width {w} folded: {after:?}");
        }
    }
    let shifted = b(Op::Sar, &X, &k(31));
    let narrow = fold(Op::Sub, b(Op::Xor, &X, &shifted), shifted, w);
    assert!(
        !is_sign_abs(&narrow),
        "a 31-bit splat at {w} became {narrow:?}"
    );
    let foreign = fold(Op::Sub, b(Op::Xor, &Y, &sign), sign, w);
    assert!(
        !matches!(foreign, Expr::Helper(Helper::Llabs, _)),
        "a different value at {w} became {foreign:?}"
    );
    let width = u64::from(w);
    let is_rotate = |e: &Expr, n: u64, right: bool| match e {
        Expr::Bin(op, v, c) => {
            v.as_ref() == &X
                && c.as_ref() == &k(n)
                && match op {
                    Op::Ror(b) => right && *b == w,
                    Op::Rol(b) => !right && *b == w,
                    _ => false,
                }
        }
        _ => false,
    };
    let turned = fold(
        Op::Or,
        b(Op::Shl, &X, &k(1)),
        b(Op::Shr, &X, &k(width - 1)),
        w,
    );
    let other_way = fold(
        Op::Or,
        b(Op::Shr, &X, &k(1)),
        b(Op::Shl, &X, &k(width - 1)),
        w,
    );
    t.same(
        "rotate",
        &b(
            Op::Or,
            &b(Op::Shl, &X, &k(1)),
            &b(Op::Shr, &X, &k(width - 1)),
        ),
        &turned,
        w,
        xs,
        one,
    );
    t.same(
        "rotate",
        &b(
            Op::Or,
            &b(Op::Shr, &X, &k(1)),
            &b(Op::Shl, &X, &k(width - 1)),
        ),
        &other_way,
        w,
        xs,
        one,
    );
    assert!(is_rotate(&turned, 1, false), "{turned:?}");
    assert!(is_rotate(&other_way, 1, true), "{other_way:?}");
    let mixed = fold(
        Op::Or,
        b(Op::Shl, &X, &k(1)),
        b(Op::Shr, &Y, &k(width - 1)),
        w,
    );
    let arithmetic = fold(
        Op::Or,
        b(Op::Shl, &X, &k(1)),
        b(Op::Sar, &X, &k(width - 1)),
        w,
    );
    let called = Expr::Call("f".to_owned(), vec![X]);
    let calling = fold(
        Op::Or,
        b(Op::Shl, &called, &k(1)),
        b(Op::Shr, &called, &k(width - 1)),
        w,
    );
    assert!(
        !matches!(mixed, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
            && !matches!(arithmetic, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
            && !matches!(calling, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..)),
        "width {w}: {mixed:?} {arithmetic:?} {calling:?}"
    );
    let mask_n = u64::from(w) - 1;
    let cnt = b(Op::And, &X, &k(mask_n));
    let rest = b(Op::Sub, &k(mask_n), &cnt);
    let spun = fold(
        Op::Or,
        b(Op::Shl, &Y, &cnt),
        b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &rest),
        w,
    );
    let spun_r = fold(
        Op::Or,
        b(Op::Shr, &Y, &cnt),
        b(Op::Shl, &b(Op::Shl, &Y, &k(1)), &rest),
        w,
    );
    let is_var = |e: &Expr, right: bool| match e {
        Expr::Bin(op, v, c) => {
            v.as_ref() == &Y
                && c.as_ref() == &X
                && match op {
                    Op::Ror(b) => right && *b == w,
                    Op::Rol(b) => !right && *b == w,
                    _ => false,
                }
        }
        _ => false,
    };
    if matches!(w, 32 | 64) {
        t.same(
            "variable rotate",
            &b(
                Op::Or,
                &b(Op::Shl, &Y, &cnt),
                &b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &rest),
            ),
            &spun,
            w,
            xs,
            ys,
        );
        t.same(
            "variable rotate",
            &b(
                Op::Or,
                &b(Op::Shr, &Y, &cnt),
                &b(Op::Shl, &b(Op::Shl, &Y, &k(1)), &rest),
            ),
            &spun_r,
            w,
            xs,
            ys,
        );
        assert!(
            is_var(&spun, false) && is_var(&spun_r, true),
            "{spun:?} {spun_r:?}"
        );
    } else {
        assert!(
            !matches!(spun, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
                && !matches!(spun_r, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..)),
            "width {w} folded: {spun:?} {spun_r:?}"
        );
    }
    let unmasked = fold(
        Op::Or,
        b(Op::Shl, &Y, &X),
        b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &b(Op::Sub, &k(mask_n), &X)),
        w,
    );
    let other = fold(
        Op::Or,
        b(Op::Shl, &X, &cnt),
        b(Op::Shr, &b(Op::Shr, &Y, &k(1)), &rest),
        w,
    );
    let called_y = Expr::Call("g".to_owned(), vec![Y]);
    let calling_y = fold(
        Op::Or,
        b(Op::Shl, &called_y, &cnt),
        b(Op::Shr, &b(Op::Shr, &called_y, &k(1)), &rest),
        w,
    );
    assert!(
        !matches!(unmasked, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
            && !matches!(other, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..))
            && !matches!(calling_y, Expr::Bin(Op::Rol(_) | Op::Ror(_), ..)),
        "width {w}: {unmasked:?} {other:?} {calling_y:?}"
    );
    let average = b(
        Op::Add,
        &b(Op::And, &X, &Y),
        &b(Op::Shr, &b(Op::Xor, &Y, &X), &k(1)),
    );
    let averaged = fold(
        Op::Add,
        b(Op::And, &X, &Y),
        b(Op::Shr, &b(Op::Xor, &Y, &X), &k(1)),
        w,
    );
    let is_mid = |e: &Expr| {
        matches!(e, Expr::Helper(Helper::Midpoint, args)
            if args.len() == 2 && args[0] == X && args[1] == Y)
    };
    if w >= 64 {
        t.same("midpoint", &average, &averaged, w, xs, ys);
        assert!(is_mid(&averaged), "{averaged:?}");
    } else {
        assert!(!is_mid(&averaged), "width {w} folded: {averaged:?}");
    }
    let signed_avg = fold(
        Op::Add,
        b(Op::And, &X, &Y),
        b(Op::Sar, &b(Op::Xor, &X, &Y), &k(1)),
        w,
    );
    let called_avg = fold(
        Op::Add,
        b(Op::And, &called, &Y),
        b(Op::Shr, &b(Op::Xor, &called, &Y), &k(1)),
        w,
    );
    assert!(
        !is_mid(&signed_avg) && !matches!(called_avg, Expr::Helper(Helper::Midpoint, _)),
        "width {w}: {signed_avg:?} {called_avg:?}"
    );
    let rounded = fold(Op::And, b(Op::Add, &X, &k(15)), k(!15u64), w);
    let is_align = |e: &Expr| {
        matches!(e, Expr::Helper(Helper::AlignUp, args)
            if args.len() == 2 && args[0] == X && args[1] == k(16))
    };
    if w >= 64 {
        t.same(
            "align up",
            &b(Op::And, &b(Op::Add, &X, &k(15)), &k(!15u64)),
            &rounded,
            w,
            xs,
            one,
        );
        assert!(is_align(&rounded), "{rounded:?}");
    } else {
        assert!(!is_align(&rounded), "width {w} folded: {rounded:?}");
    }
    let bare = fold(Op::And, X.clone(), k(!15u64), w);
    let bumped = fold(Op::And, b(Op::Add, &X, &k(16)), k(!15u64), w);
    let pair = fold(Op::And, b(Op::Add, &X, &k(1)), k(!1u64), w);
    assert!(
        !matches!(bare, Expr::Helper(..))
            && !matches!(bumped, Expr::Helper(..))
            && !matches!(pair, Expr::Helper(..)),
        "width {w}: {bare:?} {bumped:?} {pair:?}"
    );
    for cc in [C::e, C::ne] {
        for &c in &d.cs {
            for &e in &d.ds {
                let less = b(Op::Sub, &X, &k(c));
                let more = b(Op::Add, &X, &k(c));
                for (name, flags) in [
                    ("x - c == e", Flags::Cmp(less.clone(), k(e), w)),
                    ("x + c == e", Flags::Cmp(more.clone(), k(e), w)),
                    ("test x - c", Flags::Test(less.clone(), less.clone(), w)),
                    ("test x + c", Flags::Test(more.clone(), more.clone(), w)),
                    ("x - c sets zf", Flags::Result(less.clone(), w)),
                    ("x + c sets zf", Flags::Result(more.clone(), w)),
                    ("add x, c", Flags::Add(X, k(c), w)),
                ] {
                    let c0 = cond(cc, flags);
                    let Some(s) = c0.simplify() else { continue };
                    let before = Expr::Cond(Box::new(c0));
                    t.same(name, &before, &Expr::Cond(Box::new(s)), w, xs, one);
                }
            }
        }
    }
    for &c in &d.cs {
        for (sum, term) in [
            (b(Op::Add, &X, &Y), X),
            (b(Op::Add, &X, &Y), Y),
            (b(Op::Add, &b(Op::Add, &X, &k(c)), &Y), X),
            (b(Op::Add, &X, &b(Op::Add, &Y, &k(c))), Y),
            (b(Op::Add, &b(Op::Add, &X, &Y), &k(c)), Y),
        ] {
            let Some(rest) = without_addend(&sum, &term, w) else {
                continue;
            };
            t.same(
                "without_addend",
                &sum,
                &b(Op::Add, &rest, &term),
                w,
                xs,
                &d.ds,
            );
        }
    }
}
