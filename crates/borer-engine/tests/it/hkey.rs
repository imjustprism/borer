//! A stack slot stored and loaded at 8 bytes is `uint64_t`.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Symbol, SymbolKind};

use crate::decompiled::{decompiled, program64_with_data};

/// A slot written as a dword and then as a qword is declared `uint64_t`.
///
/// The call sees the dword, so that store stays, and the qword store
/// after it is a second width of the same slot. The 8-byte read back is
/// the name, not a cast through a 4-byte local.
#[test]
fn an_eight_byte_slot_is_not_a_narrow_local() {
    let code = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xc7, 0x44, 0x24, 0x20, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x20], 1
        0x48, 0x8d, 0x4c, 0x24, 0x20, // ASM: lea rcx, [rsp+0x20]
        0xff, 0x15, 0xe9, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0xfe9]
        0x48, 0x89, 0x54, 0x24, 0x20, // ASM: mov [rsp+0x20], rdx
        0x48, 0x8d, 0x4c, 0x24, 0x20, // ASM: lea rcx, [rsp+0x20]
        0xff, 0x15, 0xd9, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0xfd9]
        0x48, 0x8b, 0x44, 0x24, 0x20, // ASM: mov rax, [rsp+0x20]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let mut program = program64_with_data(&code, &[0u8; 8]);
    program.symbols.push(Symbol {
        name: "KERNEL32.dll!SlotSink".to_owned(),
        addr: 0x1_4000_2000,
        kind: SymbolKind::Import,
    });
    let text = decompiled(&program, 0x1_4000_1000);
    assert!(!text.contains("*(uint64_t*)&"), "{text}");
    assert!(text.contains("uint64_t local_8"), "{text}");
}
