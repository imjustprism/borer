//! `cpuid` keeps the leaf it was given and the registers it writes.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::warnings;
use borer_engine::analysis::{Analysis, Overlay};

use crate::decompiled::{decompiled, program64};

/// Two `cpuid` instructions keep their own leaves. A copy taken between
/// them is the first instruction's `ebx`, and the result registers are
/// declared.
#[test]
fn cpuid_keeps_the_leaf_and_the_copy_taken_before_the_next() {
    let code = [
        0x31, 0xc0, // ASM: xor eax, eax
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x0f, 0xa2, // ASM: cpuid
        0x41, 0x89, 0xd8, // ASM: mov r8d, ebx
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x0f, 0xa2, // ASM: cpuid
        0x44, 0x31, 0xc0, // ASM: xor eax, r8d
        0xc3, // ASM: ret
    ];
    let program = program64(&code);
    let entry = 0x1_4000_1000;
    let text = decompiled(&program, entry);
    assert!(
        text.contains("cpuid_ebx(0, 0)") || text.contains("cpuid_ebx(0x0, 0x0)"),
        "{text}"
    );
    assert!(
        text.contains("cpuid(1, 0)")
            || text.contains("cpuid(0x1, 0)")
            || text.contains("cpuid(1, 0x0)"),
        "{text}"
    );
    let analysis = Analysis::compute(&program);
    let warn =
        warnings(&program, &analysis, &Overlay::default(), entry, &text, None).unwrap_or_default();
    assert!(!warn.contains("undeclared"), "{text}\n{warn}");
}
