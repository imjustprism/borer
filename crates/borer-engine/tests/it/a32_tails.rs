//! ARM32 tail calls whose target lies past a start the jumper itself runs
//! through.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::a32::thumb_entries;

/// A start the jumper itself falls into is no function between the jump
/// and its target: the target stays a block of the jumper.
///
/// Another function calls into the middle of the jumper's straight code,
/// which makes that address a start the jumper's walk runs through.
#[test]
fn a_start_inside_the_jumper_steps_over_nothing() {
    let text: [u16; 18] = [
        0xb508, // ASM: push {r3, lr}
        0xf000, 0xf803, // ASM: bl 0xc
        0xf000, 0xf809, // ASM: bl 0x1c
        0xbd08, // ASM: pop {r3, pc}
        0x2001, // ASM: movs r0, #1
        0x2002, // ASM: movs r0, #2
        0xe000, // ASM: b 0x14
        0xbf00, // ASM: nop
        0xb510, // ASM: push {r4, lr}
        0x3001, // ASM: adds r0, #1
        0xbd10, // ASM: pop {r4, pc}
        0xbf00, // ASM: nop
        0xb508, // ASM: push {r3, lr}
        0xf7ff, 0xfff6, // ASM: bl 0xe
        0xbd08, // ASM: pop {r3, pc}
    ];
    assert_eq!(thumb_entries("inside.elf", &text), [0, 0xc, 0xe, 0x1c]);
}

/// A start the jumper falls into does not make a straight run after it a
/// tail call either: the run stays a block of the jumper.
#[test]
fn a_start_inside_the_jumper_makes_no_straight_run_a_function() {
    let text: [u16; 17] = [
        0xb508, // ASM: push {r3, lr}
        0xf000, 0xf803, // ASM: bl 0xc
        0xf000, 0xf808, // ASM: bl 0x1a
        0xbd08, // ASM: pop {r3, pc}
        0x2001, // ASM: movs r0, #1
        0x2002, // ASM: movs r0, #2
        0xe000, // ASM: b 0x14
        0xbf00, // ASM: nop
        0x2003, // ASM: movs r0, #3
        0x4770, // ASM: bx lr
        0xbf00, // ASM: nop
        0xb508, // ASM: push {r3, lr}
        0xf7ff, 0xfff7, // ASM: bl 0xe
        0xbd08, // ASM: pop {r3, pc}
    ];
    assert_eq!(thumb_entries("straight.elf", &text), [0, 0xc, 0xe, 0x1a]);
}
