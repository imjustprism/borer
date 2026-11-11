use super::{Flagged, compare, fcmp_pred, flags_pred, float_pred};
use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, float_cc};
use crate::analysis::decompile::fcmp::FPred;
use crate::analysis::decompile::floats::float_of;
use crate::analysis::decompile::replay::term::{Point, Term, holds};
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

/// Every float compare predicate, over the flags a float compare sets
/// or as one compare of its own, holds as its outcome set where the
/// lifter's condition logic says it does.
#[test]
fn every_float_predicate_holds_as_its_outcome_set() {
    let floats = [0.0f64, -0.0, 1.0, -1.0, f64::INFINITY, f64::NAN];
    let (x, y) = (Expr::Var(KEYS[0]), Expr::Var(KEYS[1]));
    let term = |e: &Expr| {
        Ok(Term::In(
            if *e == Expr::Var(KEYS[0]) {
                KEYS[0]
            } else {
                KEYS[1]
            },
            64,
        ))
    };
    let mut conds: Vec<(ConditionCode, Flags, Flags)> = Vec::new();
    for &cc in &CODES {
        conds.push((
            cc,
            Flags::Float(x.clone(), y.clone(), 64),
            Flags::Float(x.clone(), y.clone(), 64),
        ));
    }
    for p in FPred::ALL {
        for cc in [ConditionCode::e, ConditionCode::ne] {
            conds.push((
                cc,
                Flags::FCmp(p, x.clone(), y.clone(), 64),
                Flags::FCmp(p, x.clone(), y.clone(), 64),
            ));
        }
    }
    for (cc, symbolic, shape) in conds {
        let p = fcmp_pred(
            &Cond {
                cc: Cc(cc),
                flags: symbolic,
            },
            term,
        )
        .expect("modeled");
        for &a in &floats {
            for &b in &floats {
                let (a_bits, b_bits) = (a.to_bits(), b.to_bits());
                let ins: FxHashMap<Key, u64> = KEYS.iter().copied().zip([a_bits, b_bits]).collect();
                let at = Point {
                    ins: &ins,
                    seed: 1,
                    width: 64,
                };
                let flags = if let Flags::FCmp(q, ..) = &shape {
                    Flags::FCmp(*q, Expr::Const(a_bits), Expr::Const(b_bits), 64)
                } else {
                    Flags::Float(Expr::Const(a_bits), Expr::Const(b_bits), 64)
                };
                let want = Cond { cc: Cc(cc), flags }.eval();
                assert_eq!(holds(&p, &at), want, "{cc:?} {shape:?} {a} {b}");
            }
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
                let (a_bits, b_bits) = (a.to_bits(), b.to_bits());
                let ins: FxHashMap<Key, u64> = KEYS.iter().copied().zip([a_bits, b_bits]).collect();
                let at = Point {
                    ins: &ins,
                    seed: 1,
                    width: 64,
                };
                let want = float_cc(cc, float_of(a_bits, 64), float_of(b_bits, 64));
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
