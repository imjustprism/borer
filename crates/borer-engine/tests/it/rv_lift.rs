//! The RISC-V lifter against the RISC-V machine.
//!
//! Routines hand-encoded from the ISA manual's tables (each instruction's
//! text checked against the decoder) are lifted block by block and run on
//! [`borer_engine::emulate::rv::Machine`] from the same seeded states
//! ([`verify`]): every register, slot, store and branch outcome the lifter
//! computes must equal the machine's, for the integer operations and their
//! `w` forms, the multiplies and divides, the loads and stores of every
//! width and extension, and each conditional branch.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::verify_rv::{verify, verify_tsv};
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
