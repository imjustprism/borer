//! T32 shapes an unoptimized build leaves.

use super::*;
use crate::a32_emulate::{Code, image};
use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

/// Where each routine is placed and entered.
const AT: u64 = 0x2_0000;

/// Decompiles a T32 routine at [`AT`] and requires its lift and its text
/// to agree with the ARM32 machine.
///
/// # Arguments
///
/// * `code` - The routine.
///
/// # Returns
///
/// The text.
fn agreed(code: &[u16]) -> String {
    let p = image(AT, Code::Thumb(code));
    let a = Analysis::compute(&p);
    for seed in 1..=8 {
        let v = verify(&p, &a, &[AT], seed);
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
        assert!(v.checked > 0, "seed {seed}: {}", verify_tsv(&v));
    }
    let r = replay_function(&p, &a, AT, 1);
    assert!(r.wrong().is_empty(), "{}", replay_tsv(&r));
    decompile(&p, &a, &Overlay::default(), AT).unwrap_or_default()
}

/// A compare tree whose last miss jumps to the default through a block
/// holding only that jump is one `switch`: the jump is a detour to the one
/// default the range split also reaches.
#[test]
fn a_compare_tree_through_a_jump_to_its_default_is_a_switch() {
    let text = agreed(&[
        0x2804, // ASM: cmp r0, #4
        0xd00a, // ASM: beq 0x1a
        0x2804, // ASM: cmp r0, #4
        0xdc0a, // ASM: bgt 0x1e
        0x2800, // ASM: cmp r0, #0
        0xd002, // ASM: beq 0x12
        0x2803, // ASM: cmp r0, #3
        0xd002, // ASM: beq 0x16
        0xe005, // ASM: b 0x1e
        0x200a, // ASM: movs r0, #10
        0x4770, // ASM: bx lr
        0x201e, // ASM: movs r0, #30
        0x4770, // ASM: bx lr
        0x2028, // ASM: movs r0, #40
        0x4770, // ASM: bx lr
        0x2000, // ASM: movs r0, #0
        0x4770, // ASM: bx lr
    ]);
    assert!(text.contains("switch (a1) {"), "{text}");
    for case in ["case 0:", "case 3:", "case 4:"] {
        assert!(text.contains(case), "{text}");
    }
    assert!(!text.contains("if ("), "{text}");
}
