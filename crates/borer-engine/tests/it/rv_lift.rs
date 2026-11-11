//! The RISC-V lifter against the RISC-V machine.
//!
//! Routines hand-encoded from the ISA manual's tables (each instruction's
//! text checked against the decoder) are lifted block by block and run on
//! [`borer_engine::emulate::rv::Machine`] from the same seeded states
//! ([`verify`]): every register, slot, store and branch outcome the lifter
//! computes must equal the machine's, for the integer operations and their
//! `w` forms, the multiplies and divides, the loads and stores of every
//! width and extension, each conditional branch, and the float
//! instructions at both widths.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
use borer_engine::isa::rv::{Xlen, decode, text};
use borer_engine::program::Arch;

use crate::rv_emulate::{AT, assemble, image};

/// `ret`.
const RET: (u32, &str) = (0x0000_8067, "ret");

/// Integer operations on registers and immediates.
const ALU: &[(u32, &str)] = &[
    (0x00b5_0633, "add a2, a0, a1"),
    (0x40b5_06b3, "sub a3, a0, a1"),
    (0x00b5_4733, "xor a4, a0, a1"),
    (0x00b5_27b3, "slt a5, a0, a1"),
    (0x00b5_3833, "sltu a6, a0, a1"),
    (0x40b5_58b3, "sra a7, a0, a1"),
    (0x00b5_5e33, "srl t3, a0, a1"),
    (0x00b5_1eb3, "sll t4, a0, a1"),
    (0xffb5_3f13, "sltiu t5, a0, -5"),
    (0x0645_2f93, "slti t6, a0, 100"),
    (0xff05_7913, "andi s2, a0, -16"),
    (0x43f5_5993, "srai s3, a0, 0x3f"),
    (0x8000_0a37, "lui s4, 0x80000"),
    (0x0000_1a97, "auipc s5, 0x1"),
];

/// The RV64 `w` forms.
const WORDS: &[(u32, &str)] = &[
    (0x00b5_063b, "addw a2, a0, a1"),
    (0x40b5_06bb, "subw a3, a0, a1"),
    (0x00b5_173b, "sllw a4, a0, a1"),
    (0x00b5_57bb, "srlw a5, a0, a1"),
    (0x40b5_583b, "sraw a6, a0, a1"),
    (0xfff5_089b, "addiw a7, a0, -1"),
    (0x41f5_5e1b, "sraiw t3, a0, 0x1f"),
    (0x02b5_0ebb, "mulw t4, a0, a1"),
];

/// The multiplies and divides.
const MULDIV: &[(u32, &str)] = &[
    (0x02b5_0633, "mul a2, a0, a1"),
    (0x02b5_16b3, "mulh a3, a0, a1"),
    (0x02b5_3733, "mulhu a4, a0, a1"),
    (0x02b5_47b3, "div a5, a0, a1"),
    (0x02b5_5833, "divu a6, a0, a1"),
    (0x02b5_68b3, "rem a7, a0, a1"),
    (0x02b5_7e33, "remu t3, a0, a1"),
];

/// Divisions and remainders by a register that holds zero, and by `x0`.
const BY_ZERO: &[(u32, &str)] = &[
    (0x00a5_35b3, "sltu a1, a0, a0"),
    (0x02b5_5633, "divu a2, a0, a1"),
    (0x02b5_76b3, "remu a3, a0, a1"),
    (0x02b5_4733, "div a4, a0, a1"),
    (0x02b5_67b3, "rem a5, a0, a1"),
    (0x02b5_583b, "divuw a6, a0, a1"),
    (0x02b5_68bb, "remw a7, a0, a1"),
    (0x0205_5e33, "divu t3, a0, zero"),
];

/// Stores and loads of every width on the stack and through a pointer.
const MEMORY: &[(u32, &str)] = &[
    (0xfe01_0113, "addi sp, sp, -32"),
    (0x00a1_3423, "sd a0, 8(sp)"),
    (0x00b1_2823, "sw a1, 16(sp)"),
    (0x00b1_0a23, "sb a1, 20(sp)"),
    (0x0081_0603, "lb a2, 8(sp)"),
    (0x0081_1683, "lh a3, 8(sp)"),
    (0x0101_2703, "lw a4, 16(sp)"),
    (0x0141_4783, "lbu a5, 20(sp)"),
    (0x0101_6803, "lwu a6, 16(sp)"),
    (0x0081_3883, "ld a7, 8(sp)"),
    (0x00b5_3023, "sd a1, 0(a0)"),
    (0x0025_5e03, "lhu t3, 2(a0)"),
    (0x0201_0113, "addi sp, sp, 32"),
];

/// Double arithmetic, square root, sign injections, compares and
/// conversions, a move in and out of an integer register, and a store
/// and load through the stack.
const DOUBLES: &[(u32, &str)] = &[
    (0xfe01_0113, "addi sp, sp, -32"),
    (0xf205_0553, "fmv.d.x fa0, a0"),
    (0xf205_85d3, "fmv.d.x fa1, a1"),
    (0x02b5_7653, "fadd.d fa2, fa0, fa1"),
    (0x0ab5_76d3, "fsub.d fa3, fa0, fa1"),
    (0x12b5_7753, "fmul.d fa4, fa0, fa1"),
    (0x1ab5_77d3, "fdiv.d fa5, fa0, fa1"),
    (0x5a05_7853, "fsqrt.d fa6, fa0"),
    (0x22a5_18d3, "fneg.d fa7, fa0"),
    (0x22b5_a053, "fabs.d ft0, fa1"),
    (0x22a5_00d3, "fmv.d ft1, fa0"),
    (0xa2b5_2653, "feq.d a2, fa0, fa1"),
    (0xa2b5_16d3, "flt.d a3, fa0, fa1"),
    (0xa2b5_0753, "fle.d a4, fa0, fa1"),
    (0xc205_17d3, "fcvt.w.d a5, fa0, rtz"),
    (0xc225_9853, "fcvt.l.d a6, fa1, rtz"),
    (0xc215_18d3, "fcvt.wu.d a7, fa0, rtz"),
    (0xd205_7153, "fcvt.d.w ft2, a0"),
    (0xd225_f1d3, "fcvt.d.l ft3, a1"),
    (0xd235_f253, "fcvt.d.lu ft4, a1"),
    (0x4015_73d3, "fcvt.s.d ft7, fa0"),
    (0x2ab5_0453, "fmin.d fs0, fa0, fa1"),
    (0x62b5_74c3, "fmadd.d fs1, fa0, fa1, fa2"),
    (0xe205_0e53, "fmv.x.d t3, fa0"),
    (0x00a1_3427, "fsd fa0, 8(sp)"),
    (0x0081_3307, "fld ft6, 8(sp)"),
    (0x0201_0113, "addi sp, sp, 32"),
];

/// Single arithmetic, square root, a compare and conversions, the moves,
/// and a store and load through the stack.
const SINGLES: &[(u32, &str)] = &[
    (0xfe01_0113, "addi sp, sp, -32"),
    (0xf005_0553, "fmv.w.x fa0, a0"),
    (0xf005_85d3, "fmv.w.x fa1, a1"),
    (0x00b5_7653, "fadd.s fa2, fa0, fa1"),
    (0x10b5_76d3, "fmul.s fa3, fa0, fa1"),
    (0x18b5_7753, "fdiv.s fa4, fa0, fa1"),
    (0x5805_77d3, "fsqrt.s fa5, fa0"),
    (0xa0b5_1653, "flt.s a2, fa0, fa1"),
    (0xc005_16d3, "fcvt.w.s a3, fa0, rtz"),
    (0xd005_7053, "fcvt.s.w ft0, a0"),
    (0x4205_00d3, "fcvt.d.s ft1, fa0"),
    (0xe005_0e53, "fmv.x.w t3, fa0"),
    (0x00a1_2427, "fsw fa0, 8(sp)"),
    (0x0081_2207, "flw ft4, 8(sp)"),
    (0x0201_0113, "addi sp, sp, 32"),
];

/// Floats an incoming register holds, read without a move first: the
/// seeds put a double or a boxed single there.
const INCOMING: &[(u32, &str)] = &[
    (0x02b5_7653, "fadd.d fa2, fa0, fa1"),
    (0x00d7_f753, "fadd.s fa4, fa5, fa3"),
    (0x22a5_1653, "fneg.d fa2, fa0"),
    (0x22b5_a6d3, "fabs.d fa3, fa1"),
];

/// A negation and an absolute value of what a minimum and a fused
/// multiply-add computed, moved out to integer registers.
const SIGNS_OF_CALLS: &[(u32, &str)] = &[
    (0xf205_0553, "fmv.d.x fa0, a0"),
    (0xf205_85d3, "fmv.d.x fa1, a1"),
    (0xf206_0653, "fmv.d.x fa2, a2"),
    (0x2ab5_0453, "fmin.d fs0, fa0, fa1"),
    (0x2284_1653, "fneg.d fa2, fs0"),
    (0x62b5_74c3, "fmadd.d fs1, fa0, fa1, fa2"),
    (0x2294_a6d3, "fabs.d fa3, fs1"),
    (0xe206_0553, "fmv.x.d a0, fa2"),
    (0xe206_85d3, "fmv.x.d a1, fa3"),
];

/// Checks one routine: its text reads as listed, and every block the
/// lifter and the machine both model agrees on every seed tried.
///
/// # Arguments
///
/// * `body` - The routine's instructions before its `ret`.
fn agrees(body: &[(u32, &str)]) {
    for &(w, want) in body.iter().chain([&RET]) {
        let i = decode(&w.to_le_bytes(), AT, Xlen::X64).expect("decodes");
        assert_eq!(text(&i), want, "{w:#010x}");
    }
    let parts: Vec<(u32, usize)> = body.iter().chain([&RET]).map(|&(w, _)| (w, 4)).collect();
    let p = image(&assemble(&parts), Arch::RiscV64);
    let a = Analysis::compute(&p);
    for seed in 1..=8 {
        let v = verify(&p, &a, &[AT], seed);
        assert!(v.checked >= 1, "{}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "{}", verify_tsv(&v));
    }
}

/// The integer operations agree with the emulator.
#[test]
fn the_integer_operations_agree_with_the_emulator() {
    agrees(ALU);
}

/// The `w` forms agree with the emulator.
#[test]
fn the_word_forms_agree_with_the_emulator() {
    agrees(WORDS);
}

/// The multiplies and divides agree with the emulator.
#[test]
fn the_multiplies_and_divides_agree_with_the_emulator() {
    agrees(MULDIV);
}

/// A zero divisor gives what RISC-V defines, all ones or the dividend, as
/// on the emulator.
#[test]
fn division_by_zero_agrees_with_the_emulator() {
    agrees(BY_ZERO);
}

/// The loads and stores agree with the emulator.
#[test]
fn the_loads_and_stores_agree_with_the_emulator() {
    agrees(MEMORY);
}

/// Each conditional branch takes the side the emulator takes.
#[test]
fn each_branch_agrees_with_the_emulator() {
    let branches: [(u32, &str); 6] = [
        (0x00b5_0463, "beq a0, a1, 0x10008"),
        (0x00b5_1463, "bne a0, a1, 0x10008"),
        (0x00b5_4463, "blt a0, a1, 0x10008"),
        (0x00b5_5463, "bge a0, a1, 0x10008"),
        (0x00b5_6463, "bltu a0, a1, 0x10008"),
        (0x00b5_7463, "bgeu a0, a1, 0x10008"),
    ];
    for (w, want) in branches {
        agrees(&[(w, want), (0x0010_0513, "li a0, 1")]);
    }
}

/// The double instructions agree with the emulator.
#[test]
fn the_double_instructions_agree_with_the_emulator() {
    agrees(DOUBLES);
}

/// The single instructions agree with the emulator.
#[test]
fn the_single_instructions_agree_with_the_emulator() {
    agrees(SINGLES);
}

/// Floats incoming in their registers agree with the emulator.
#[test]
fn incoming_floats_agree_with_the_emulator() {
    agrees(INCOMING);
}

/// A negation and an absolute value of a minimum's and a fused
/// multiply-add's result agree with the emulator.
#[test]
fn signs_of_library_results_agree_with_the_emulator() {
    agrees(SIGNS_OF_CALLS);
}

/// `2^63 + 2^39 + 1`, built in `a0`, converted to a single: rounded once
/// it is `2^63 + 2^40`, while a double first rounds it to the halfway
/// point and then to `2^63`.
const ROUNDED_ONCE: &[(u32, &str)] = &[
    (0x0010_0513, "li a0, 1"),
    (0x03f5_1513, "slli a0, a0, 0x3f"),
    (0x0010_0293, "li t0, 1"),
    (0x0272_9293, "slli t0, t0, 0x27"),
    (0x0055_6533, "or a0, a0, t0"),
    (0x0015_6513, "ori a0, a0, 1"),
    (0xd035_7553, "fcvt.s.lu fa0, a0"),
    (0xe005_05d3, "fmv.x.w a1, fa0"),
];

/// A float converted in the register it arrived in agrees with the
/// emulator.
///
/// The register is only its name in the lifted value, and the width it was
/// read at is what says the cast converts a float: a double narrowed, a
/// single widened, not the integer its bits happen to be.
#[test]
fn a_float_converted_where_it_arrived_agrees_with_the_emulator() {
    agrees(&[(0x4015_7553, "fcvt.s.d fa0, fa0")]);
    agrees(&[(0x4205_0553, "fcvt.d.s fa0, fa0")]);
}

/// A single widened in a register an earlier block read as a double
/// agrees with the emulator.
///
/// The first block declares `fa0` a double for the whole function. The
/// last finds a single in it, as after a call that returns one: its name
/// there is the single that block reads, not the declared double.
#[test]
fn a_single_in_a_register_declared_a_double_agrees_with_the_emulator() {
    agrees(&[
        (0x02b5_7653, "fadd.d fa2, fa0, fa1"),
        (0x00b5_1463, "bne a0, a1, 0x10008"),
        (0x0010_0513, "li a0, 1"),
        (0x4205_0553, "fcvt.d.s fa0, fa0"),
    ]);
}

/// A 64-bit integer converted to a single rounds once, as the machine
/// does.
#[test]
fn a_wide_integer_to_a_single_rounds_once() {
    agrees(ROUNDED_ONCE);
}

/// Every atomic memory operation at both widths, the load-reserveds and a
/// store-conditional, each through the pointer in `a0`.
///
/// Each runs alone in its routine: a later one would read the bytes an
/// earlier one wrote, which the check does not compare. One destination
/// is also the operand.
const ATOMICS: &[(u32, &str)] = &[
    (0x00b5_362f, "amoadd.d a2, a1, (a0)"),
    (0x08b5_26af, "amoswap.w a3, a1, (a0)"),
    (0x80c5_272f, "amomin.w a4, a2, (a0)"),
    (0x80c5_372f, "amomin.d a4, a2, (a0)"),
    (0xe0b5_37af, "amomaxu.d a5, a1, (a0)"),
    (0x20b5_282f, "amoxor.w a6, a1, (a0)"),
    (0x60b5_38af, "amoand.d a7, a1, (a0)"),
    (0x40c5_232f, "amoor.w t1, a2, (a0)"),
    (0xa0b5_33af, "amomax.d t2, a1, (a0)"),
    (0xc0b5_2e2f, "amominu.w t3, a1, (a0)"),
    (0x00b5_25af, "amoadd.w a1, a1, (a0)"),
    (0x1005_3eaf, "lr.d t4, (a0)"),
    (0x1005_2faf, "lr.w t6, (a0)"),
    (0x18c5_2f2f, "sc.w t5, a2, (a0)"),
];

/// The atomics agree with the emulator.
#[test]
fn the_atomics_agree_with_the_emulator() {
    for one in ATOMICS {
        agrees(std::slice::from_ref(one));
    }
}
