//! Tests of the MIR lowering and evaluator.

use std::collections::BTreeMap;

use super::build::Builder;
use super::eval::{Inputs, eval};
use super::{Hole, Inst, MTy};
use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, Op, Ty};
use crate::analysis::decompile::fcmp::FPred;
use crate::isa::x86::{ConditionCode, Register};

/// A starting state of fixed registers and memory that reads every byte
/// as its address's low byte.
struct Fixed {
    /// Each register's value.
    regs: BTreeMap<Key, u64>,
    /// The memory ranges read.
    reads: Vec<(u64, u64)>,
}

impl Inputs for Fixed {
    fn reg(&self, k: Key) -> Option<u64> {
        self.regs.get(&k).copied()
    }

    fn sp(&self) -> u64 {
        0x1000
    }

    fn tls(&self) -> u64 {
        0x9000
    }

    fn load(&mut self, at: u64, n: u64) -> Option<u64> {
        self.reads.push((at, n));
        (1..=8).contains(&n).then(|| {
            (0..n)
                .rev()
                .fold(0, |v, i| (v << 8) | (at.wrapping_add(i) & 0xff))
        })
    }
}

/// Builds a state where `rax` and `rcx` hold the given values.
///
/// # Arguments
///
/// * `rax` - The value of `rax`.
/// * `rcx` - The value of `rcx`.
fn state(rax: u64, rcx: u64) -> Fixed {
    Fixed {
        regs: BTreeMap::from([
            (Key::Reg(Register::RAX), rax),
            (Key::Reg(Register::RCX), rcx),
        ]),
        reads: Vec::new(),
    }
}

/// The register `rax` as an expression.
fn rax() -> Expr {
    Expr::Var(Key::Reg(Register::RAX))
}

/// The register `rcx` as an expression.
fn rcx() -> Expr {
    Expr::Var(Key::Reg(Register::RCX))
}

/// Lowers one value at a word width and evaluates it.
///
/// # Arguments
///
/// * `word` - The machine word's width.
/// * `e` - The value.
/// * `inputs` - The starting state.
fn run(word: u8, e: &Expr, inputs: &mut Fixed) -> Option<u64> {
    let temps = BTreeMap::new();
    let mut b = Builder::new(word, &temps, &[0x10, 0x14]);
    let v = b.value(e);
    eval(&b.body, v, inputs)
}

/// Lowers one condition and evaluates it.
///
/// # Arguments
///
/// * `c` - The condition.
/// * `inputs` - The starting state.
fn decide(c: &Cond, inputs: &mut Fixed) -> Option<bool> {
    let temps = BTreeMap::new();
    let mut b = Builder::new(64, &temps, &[0x10]);
    let v = b.condition(c);
    eval(&b.body, v, inputs).map(|v| v != 0)
}

/// Every integer operator of a lowered expression computes at the word.
///
/// The same difference wraps at 32 bits in 32-bit code and at 64 in
/// 64-bit code, and a quotient by zero is unknown rather than a guess.
#[test]
fn an_operator_computes_at_the_width_it_holds() {
    let diff = Expr::Bin(Op::Sub, Box::new(rax()), Box::new(rcx()));
    assert_eq!(run(32, &diff, &mut state(1, 2)), Some(0xffff_ffff));
    assert_eq!(run(64, &diff, &mut state(1, 2)), Some(u64::MAX));
    let quot = Expr::Bin(Op::Div, Box::new(rax()), Box::new(rcx()));
    assert_eq!(run(64, &quot, &mut state(7, 0)), None);
    let sdiv = Expr::Bin(Op::SDiv, Box::new(rax()), Box::new(rcx()));
    assert_eq!(
        run(32, &sdiv, &mut state(0xffff_fffa, 3)),
        Some(0xffff_fffe)
    );
}

/// A flags record compares at the width it was set at: `sub eax, ecx; je`
/// is taken when the low halves agree, whatever the upper halves hold.
#[test]
fn a_condition_compares_at_its_flags_width() {
    let diff = Expr::Bin(Op::Sub, Box::new(rax()), Box::new(rcx()));
    let zero = Cond {
        cc: Cc(ConditionCode::e),
        flags: Flags::Result(diff, 32),
    };
    assert_eq!(decide(&zero, &mut state(0x1_0000_0005, 5)), Some(true));
    let less = Cond {
        cc: Cc(ConditionCode::l),
        flags: Flags::Cmp(rax(), rcx(), 32),
    };
    assert_eq!(decide(&less, &mut state(0xffff_ffff, 0)), Some(true));
    assert_eq!(
        decide(&less, &mut state(0xffff_ffff, 0x8000_0000)),
        Some(false)
    );
    let carry = Cond {
        cc: Cc(ConditionCode::b),
        flags: Flags::Add(rax(), rcx(), 8),
    };
    assert_eq!(decide(&carry, &mut state(0xf0, 0x10)), Some(true));
}

/// A float compare reads the predicate the flags give a NaN: `jb` after
/// `ucomisd` is taken for an unordered pair, `ja` is not.
#[test]
fn a_float_compare_keeps_the_unordered_rule() {
    let nan = f64::NAN.to_bits();
    let one = 1f64.to_bits();
    for (cc, want) in [(ConditionCode::b, true), (ConditionCode::a, false)] {
        let c = Cond {
            cc: Cc(cc),
            flags: Flags::Float(rax(), rcx(), 64),
        };
        assert_eq!(decide(&c, &mut state(nan, one)), Some(want), "{cc:?}");
    }
    assert_eq!(FPred::Ogt.negate(), FPred::Ule);
    assert_eq!(FPred::Uno.negate().negate(), FPred::Uno);
}

/// A predicate the lifter recorded is the compare's own: `ne` asks it and
/// `e` its negation, so `one` is false for a NaN and its negation true.
/// A bitcast keeps the bits and reads them as its type.
#[test]
fn a_recorded_predicate_and_a_bitcast_lower_as_they_read() {
    let nan = f64::NAN.to_bits();
    let one = 1f64.to_bits();
    for (cc, want) in [(ConditionCode::ne, false), (ConditionCode::e, true)] {
        let c = Cond {
            cc: Cc(cc),
            flags: Flags::FCmp(FPred::One, rax(), rcx(), 64),
        };
        assert_eq!(decide(&c, &mut state(nan, one)), Some(want), "{cc:?}");
    }
    let low = Expr::Bitcast(Box::new(rax()), Ty::F32);
    let bits = u64::from(2.5f32.to_bits());
    assert_eq!(
        run(64, &low, &mut state(0xdead_0000_0000 | bits, 0)),
        Some(bits)
    );
    let sum = Expr::Bin(Op::FAdd, Box::new(low.clone()), Box::new(low));
    assert_eq!(
        run(64, &sum, &mut state(bits, 0)),
        Some(u64::from(5f32.to_bits()))
    );
}

/// A memory read records its range, a stack slot reads at the starting
/// stack pointer plus its offset, and a value the state does not hold is
/// unknown.
#[test]
fn a_load_reads_the_starting_memory() {
    let mut st = state(0, 0);
    let slot = Expr::Var(Key::Slot(-8));
    assert_eq!(run(64, &slot, &mut st), Some(0xff_fe_fd_fc_fb_fa_f9_f8));
    assert_eq!(st.reads, vec![(0xff8, 8)]);
    let byte = Expr::Deref(Box::new(Expr::Const(0x1234)), Ty::U8);
    assert_eq!(run(64, &byte, &mut st), Some(0x34));
    let param = Expr::Var(Key::Param(1));
    assert_eq!(run(64, &param, &mut st), None);
}

/// A float operation computes at its operands' type, a single rounding as
/// a single, and one whose operands carry no float type is unknown.
#[test]
fn a_float_operation_computes_at_its_type() {
    let third = Expr::Bin(
        Op::FDiv,
        Box::new(Expr::FConst(u64::from(1f32.to_bits()), Ty::F32)),
        Box::new(Expr::FConst(u64::from(3f32.to_bits()), Ty::F32)),
    );
    assert_eq!(
        run(64, &third, &mut state(0, 0)),
        Some(u64::from((1f32 / 3f32).to_bits()))
    );
    let untyped = Expr::Bin(Op::FAdd, Box::new(rax()), Box::new(rcx()));
    let temps = BTreeMap::new();
    let mut b = Builder::new(64, &temps, &[]);
    let v = b.value(&untyped);
    assert!(matches!(
        b.body.node(v).map(|n| &n.inst),
        Some(Inst::Undef(Hole::Width))
    ));
    let cast = Expr::Cast(Box::new(Expr::Sext(Box::new(rax()), 32)), Ty::F64);
    assert_eq!(
        run(64, &cast, &mut state(0xffff_fffe, 0)),
        Some((-2f64).to_bits())
    );
}

/// Every value keeps the provenance of the region it was built for: the
/// instruction addresses it came from.
#[test]
fn a_value_keeps_its_provenance() {
    let temps = BTreeMap::new();
    let mut b = Builder::new(64, &temps, &[0x14, 0x10, 0x14]);
    let v = b.value(&Expr::Bin(
        Op::Add,
        Box::new(rax()),
        Box::new(Expr::Const(1)),
    ));
    let node = b.body.node(v).cloned();
    assert_eq!(node.as_ref().map(|n| n.ty), Some(MTy::I(64)));
    let prov = node.map(|n| n.prov);
    assert_eq!(prov.map(|p| b.body.vas(p).to_vec()), Some(vec![0x10, 0x14]));
}
