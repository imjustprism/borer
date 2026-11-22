//! Tests of the ARM32 walk's own bookkeeping, on Thumb code laid out in a
//! raw image.

use std::collections::BTreeSet;

use super::walk;
use crate::isa::a32::{Mode, Modes};
use crate::num::from_usize;
use crate::program::{Arch, Program, Section};

/// Where the code is mapped.
const BASE: u64 = 0x1000;

/// Returns a raw image holding `code` at [`BASE`], all of it Thumb.
///
/// # Arguments
///
/// * `code` - The halfwords.
fn thumb(code: &[u16]) -> Program {
    let bytes: Vec<u8> = code.iter().flat_map(|h| h.to_le_bytes()).collect();
    let text = Section::mapped(".text", BASE, 0, from_usize(bytes.len()), false, true);
    let mut p = Program::raw(bytes, Arch::Arm, 0, Some(BASE), vec![text]);
    p.modes = Modes(vec![(BASE, Mode::Thumb)]);
    p
}

/// A walk made again, its call stopped at the literal after it, costs both
/// times it was made.
///
/// # Panics
///
/// When the walk is not made again or costs only its last time.
#[test]
fn a_walk_made_again_costs_every_time() {
    let p = thumb(&[
        0xb508, // ASM: push {r3, lr}
        0x4901, // ASM: ldr r1, [pc, #4]
        0xf000, 0xf802, // ASM: bl 0xc
        0x0000, 0x2000, // ASM: .word 0x20000000
        0xe7fe, // ASM: b .
    ]);
    let w = walk(&p, BASE, &BTreeSet::new(), &BTreeSet::new(), None);
    assert_eq!(w.seen.len(), 3, "push, ldr and bl, nothing after them");
    assert!(w.spent > w.seen.len(), "spent {}", w.spent);
    assert!(w.ends.contains(&(BASE + 0xc)));
}
