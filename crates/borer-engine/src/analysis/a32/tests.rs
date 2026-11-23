//! Tests of the ARM32 walk's own bookkeeping, on Thumb code laid out in a
//! raw image.

use std::collections::BTreeSet;

use super::{Walks, walk};
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

/// A stop an earlier walk found through a call it decoded from data is
/// dropped when no call of the last walk runs into it: the code a real
/// branch reaches there is walked.
///
/// # Panics
///
/// When the branch target is left out of the walk.
#[test]
fn a_stop_no_call_runs_into_ends_no_path() {
    let p = thumb(&[
        0xb508, // ASM: push {r3, lr}
        0x4902, // ASM: ldr r1, [pc, #8]
        0x4a02, // ASM: ldr r2, [pc, #8]
        0xb118, // ASM: cbz r0, 0x10
        0xf000, 0xf805, // ASM: bl 0x16
        0xf000, 0xf802, // ASM: .word (reads as bl 0x14)
        0x2005, // ASM: movs r0, #5
        0xbd08, // ASM: pop {r3, pc}
        0x4770, // ASM: bx lr
        0xe7fe, // ASM: b .
    ]);
    let w = walk(&p, BASE, &BTreeSet::new(), &BTreeSet::new(), None);
    assert!(w.seen.contains_key(&(BASE + 0x10)), "{:x?}", w.seen.keys());
    assert!(!w.seen.contains_key(&(BASE + 0xc)));
}

/// A function marked never to return on evidence no walk holds any more
/// is unmarked, and its caller cut at the call walked again.
///
/// # Panics
///
/// When the mark stays or the caller's code after the call stays out.
#[test]
fn a_noreturn_mark_without_evidence_goes() {
    let p = thumb(&[
        0xb508, // ASM: push {r3, lr}
        0xf000, 0xf802, // ASM: bl 0xa
        0x2005, // ASM: movs r0, #5
        0xbd08, // ASM: pop {r3, pc}
        0x4770, // ASM: bx lr
    ]);
    let callee = BASE + 0xa;
    let marked = BTreeSet::from([callee]);
    let caller = walk(&p, BASE, &BTreeSet::new(), &marked, None);
    assert!(
        !caller.seen.contains_key(&(BASE + 6)),
        "cut at the call first"
    );
    let ret = walk(&p, callee, &BTreeSet::new(), &BTreeSet::new(), None);
    let imports = std::collections::BTreeMap::new();
    let mut walks = Walks {
        starts: BTreeSet::from([BASE, callee]),
        guessed: BTreeSet::new(),
        labels: std::collections::BTreeMap::new(),
        noreturn: marked,
        named: BTreeSet::new(),
        walked: std::collections::BTreeMap::from([(BASE, caller), (callee, ret)]),
        covered: std::collections::BTreeMap::new(),
        data: std::collections::BTreeMap::new(),
        fuel: 1 << 20,
        incomplete: false,
        imports: &imports,
    };
    walks.settle(&p);
    assert!(walks.noreturn.is_empty());
    assert!(walks.walked[&BASE].seen.contains_key(&(BASE + 6)));
}
