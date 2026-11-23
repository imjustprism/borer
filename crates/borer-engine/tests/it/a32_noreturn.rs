//! ARM32 callees a caller's literal follows, whose own walk says nothing
//! about whether they return.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use crate::a32::{ELF_TEXT, elf32};

/// A callee whose own path ends where a call of it runs into a start is
/// not taken to never return, though one caller's literal follows a call
/// of it: another caller keeps the code after its call.
#[test]
fn a_call_into_a_start_is_no_evidence_of_noreturn() {
    let text: [u16; 25] = [
        0xb508, // ASM: push {r3, lr}
        0xf000, 0xf805, // ASM: bl 0x10
        0xf000, 0xf80e, // ASM: bl 0x26
        0xf000, 0xf80a, // ASM: bl 0x22
        0xbd08, // ASM: pop {r3, pc}
        0xb508, // ASM: push {r3, lr}
        0x4901, // ASM: ldr r1, [pc, #4]
        0xf000, 0xf802, // ASM: bl 0x1c
        0x0000, 0x2000, // ASM: .word 0x20000000
        0xb508, // ASM: push {r3, lr}
        0xf000, 0xf807, // ASM: bl 0x30
        0xb510, // ASM: push {r4, lr}
        0xbd10, // ASM: pop {r4, pc}
        0xb510, // ASM: push {r4, lr}
        0xf7ff, 0xfff8, // ASM: bl 0x1c
        0x2005, // ASM: movs r0, #5
        0xbd10, // ASM: pop {r4, pc}
        0x4770, // ASM: bx lr
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("start.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let b = a.function_at(ELF_TEXT + 0x26).expect("the other caller");
    assert!(
        b.blocks
            .iter()
            .any(|k| k.start <= ELF_TEXT + 0x2c && ELF_TEXT + 0x2c < k.end)
    );
}

/// A callee that stops at a breakpoint is not taken to never return:
/// `bkpt 0xab` asks a debugger for a service and goes on.
#[test]
fn a_breakpoint_is_no_evidence_of_noreturn() {
    let text: [u16; 20] = [
        0xb508, // ASM: push {r3, lr}
        0xf000, 0xf803, // ASM: bl 0xc
        0xf000, 0xf80a, // ASM: bl 0x1e
        0xbd08, // ASM: pop {r3, pc}
        0xb508, // ASM: push {r3, lr}
        0x4901, // ASM: ldr r1, [pc, #4]
        0xf000, 0xf802, // ASM: bl 0x18
        0x0000, 0x2000, // ASM: .word 0x20000000
        0xb508, // ASM: push {r3, lr}
        0xbeab, // ASM: bkpt #0xab
        0xbd08, // ASM: pop {r3, pc}
        0xb510, // ASM: push {r4, lr}
        0xf7ff, 0xfffa, // ASM: bl 0x18
        0x2005, // ASM: movs r0, #5
        0xbd10, // ASM: pop {r4, pc}
    ];
    let bytes: Vec<u8> = text.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("bkpt.elf"), elf32(&bytes, &[], ELF_TEXT | 1))
        .expect("parses");
    let a = Analysis::compute(&p);
    let b = a.function_at(ELF_TEXT + 0x1e).expect("the other caller");
    assert!(
        b.blocks
            .iter()
            .any(|k| k.start <= ELF_TEXT + 0x24 && ELF_TEXT + 0x24 < k.end)
    );
}
