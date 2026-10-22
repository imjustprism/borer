//! Control-flow shapes written as a source spells them.
//!
//! A jump table's bound check is the `switch`'s `default`.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;

use crate::decompiled::{decompiled, program64_with_data, replays_clean};

/// Where the hand-assembled functions start.
const F: u64 = 0x1_4000_1000;

/// The bound check in front of a jump table is the `switch`'s `default`.
///
/// `cmp ecx,2; ja D; lea r8,[F]; lea rdx,[T]; movsxd rax,[rdx+rcx*4]; add
/// rax,r8; jmp rax` with three cases returning 1, 2 and 3 and `D: mov
/// eax,-1; ret`: every value past the table, a negative one read unsigned
/// too, takes `D`, which is what a `default:` does.
#[test]
fn a_jump_table_bound_is_the_switch_default() {
    let code: &[u8] = &[
        0x83, 0xf9, 0x02, // ASM: cmp ecx,2
        0x77, 0x29, // ASM: ja 0x2e
        0x4c, 0x8d, 0x05, 0xf4, 0xff, 0xff, 0xff, // ASM: lea r8,[rip-0xc]
        0x48, 0x8d, 0x15, 0xed, 0x0f, 0x00, 0x00, // ASM: lea rdx,[rip+0xfed]
        0x48, 0x63, 0x04, 0x8a, // ASM: movsxd rax,dword [rdx+rcx*4]
        0x4c, 0x01, 0xc0, // ASM: add rax,r8
        0xff, 0xe0, // ASM: jmp rax
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0xc3, // ASM: ret
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: mov eax,3
        0xc3, // ASM: ret
        0xb8, 0xff, 0xff, 0xff, 0xff, // ASM: mov eax,-1
        0xc3, // ASM: ret
    ];
    let entries: Vec<u8> = [0x1cu32, 0x22, 0x28]
        .iter()
        .flat_map(|o| o.to_le_bytes())
        .collect();
    let p = program64_with_data(code, &entries);
    let a = Analysis::compute(&p);
    let text = decompiled(&p, F);
    assert!(text.contains("switch (a1)"), "{text}");
    assert!(text.contains("default:"), "{text}");
    assert!(!text.contains("if ("), "{text}");
    replays_clean(&p, &a, &[F]);
}
