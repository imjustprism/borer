//! The ARM32 lifter, checked against the ARM32 machine block by block.
//!
//! Every routine of the machine's table ([`crate::a32_emulate`]) and a few
//! of the forms the lifter maps (a 64-bit compare through `subs` and
//! `sbcs`, the loads of a literal pool, the sign operations on a double's
//! bits), assembled by LLVM (`clang --target=armv7a-linux-gnueabihf
//! -mcpu=cortex-a15 -mfpu=vfpv4`) and checked against `llvm-objdump`, is
//! lifted and run from the same seeded states, and every register, VFP
//! register, slot, store and branch must agree on every seed.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::verify::{Fact, Verified};
use borer_engine::analysis::decompile::verify_a32::{verify, verify_tsv};

use crate::a32_emulate::{CASES, Code, image};

/// Seeds each routine is checked from.
const SEEDS: u64 = 24;

/// Checks the routine at `at` from every seed and requires every fact to
/// agree.
///
/// # Arguments
///
/// * `at` - Where it is placed and entered.
/// * `code` - The routine.
///
/// # Returns
///
/// What each seed found.
fn agrees(at: u64, code: Code<'_>) -> Vec<Verified> {
    let p = image(at, code);
    let a = Analysis::compute(&p);
    (1..=SEEDS)
        .map(|seed| {
            let v = verify(&p, &a, &[at], seed);
            assert!(
                v.mismatches.is_empty(),
                "{at:#x} seed {seed}: {}",
                verify_tsv(&v)
            );
            v
        })
        .collect()
}

/// How many facts of a kind one seed compared.
///
/// # Arguments
///
/// * `v` - What the seed found.
/// * `fact` - The kind.
fn compared(v: &Verified, fact: Fact) -> usize {
    v.facts.get(&fact).map_or(0, |t| t.compared)
}

/// Every routine of the machine's table lifts as the machine runs it, and
/// the check compares blocks of each but the bare `tbb` and `tbh`, whose
/// one block is the dispatch through a table no guard bounds.
#[test]
fn every_machine_routine_lifts_as_the_machine_runs_it() {
    let mut seen = std::collections::BTreeSet::new();
    for c in CASES.iter().filter(|c| seen.insert(c.at)) {
        let vs = agrees(c.at, c.code);
        let dispatch = c.name.starts_with("tbb") || c.name.starts_with("tbh");
        assert!(
            dispatch || vs.iter().all(|v| v.checked > 0),
            "{}: nothing checked",
            c.name
        );
    }
}

/// A compare of two pairs through `subs` and `sbcs` reads as the 64-bit
/// order its `lt` and `lo` readers ask, from every seed.
#[test]
fn a_pair_compare_reads_the_64_bit_order() {
    for v in agrees(0x2_0000, Code::Thumb(T_COMPARE_PAIRS)) {
        assert_eq!(v.checked, 1, "{}", verify_tsv(&v));
        assert!(compared(&v, Fact::Register) > 0, "{}", verify_tsv(&v));
    }
}

/// A load from a literal pool is the word the pool holds, a core and a
/// double register alike.
#[test]
fn a_literal_pool_load_is_its_constant() {
    for v in agrees(0x2_0028, Code::Thumb(T_LITERALS)) {
        assert_eq!(v.checked, 1, "{}", verify_tsv(&v));
        assert!(compared(&v, Fact::Vector) > 0, "{}", verify_tsv(&v));
    }
}

/// The sign operations of a double read as its bits flip a negative zero
/// out of a zero, the whole 64 bits wide, and clear it again.
#[test]
fn a_negation_of_a_double_flips_its_sign_bit() {
    for v in agrees(0x2_0044, Code::Arm(A_NEGATE_BITS)) {
        assert_eq!(v.checked, 1, "{}", verify_tsv(&v));
        assert!(compared(&v, Fact::Vector) >= 2, "{}", verify_tsv(&v));
    }
}

/// The routine `t_compare_pairs`, in T32.
const T_COMPARE_PAIRS: &[u16] = &[
    // ASM: subs.w r4, r0, r2
    0xebb0, 0x0402, // ASM: mov.w r5, #0x0
    0xf04f, 0x0500, // ASM: sbcs.w r4, r1, r3
    0xeb71, 0x0403, // ASM: mov.w r4, #0x0
    0xf04f, 0x0400, // ASM: it lt
    0xbfb8, // ASM: movlt.w r4, #0x1
    0xf04f, 0x0401, // ASM: subs r0, r2, r0
    0x1a10, // ASM: sbcs.w r0, r3, r1
    0xeb73, 0x0001, // ASM: it lo
    0xbf38, // ASM: movlo.w r5, #0x1
    0xf04f, 0x0501, // ASM: sub.w r0, r5, r4
    0xeba5, 0x0004, // ASM: bx lr
    0x4770,
];

/// The routine `t_literals`, in T32.
const T_LITERALS: &[u16] = &[
    // ASM: ldr r1, [pc, #0xc]
    0x4903, // ASM: vldr d1, [pc, #16]
    0xed9f, 0x1b04, // ASM: add r0, r1
    0x4408, // ASM: vadd.f64 d0, d0, d1
    0xee30, 0x0b01, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00, // ASM: .word 0x12345678
    0x5678, 0x1234, // ASM: .word 0, 0x40080000
    0x0000, 0x0000, 0x0000, 0x4008,
];

/// The routine `a_negate_bits`, in A32.
const A_NEGATE_BITS: &[u32] = &[
    // ASM: vneg.f64 d16, d0
    0xeef1_0b40,
    // ASM: vabs.f64 d17, d16
    0xeef0_1be0,
    // ASM: vneg.f32 s2, s0
    0xeeb1_1a40,
    // ASM: vnmls.f64 d1, d0, d1
    0xee10_1b01,
    // ASM: vmov r0, r1, d16
    0xec51_0b30,
    // ASM: vmov r2, s2
    0xee11_2a10,
    // ASM: bx lr
    0xe12f_ff1e,
];
