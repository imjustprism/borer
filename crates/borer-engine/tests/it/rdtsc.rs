//! A live `rdtsc` result stays in the C. A dead one writes no bare call.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::warnings;
use borer_engine::analysis::{Analysis, Overlay};

use crate::decompiled::{decompiled, program64};

/// `rdtsc` then `shl` / `or` returns both halves. Nothing that reads the
/// counters emits no call.
#[test]
fn a_live_rdtsc_is_kept_and_a_dead_one_is_not_a_call() {
    let live = [
        0x0f, 0x31, // ASM: rdtsc
        0x48, 0xc1, 0xe2, 0x20, // ASM: shl rdx, 32
        0x48, 0x09, 0xd0, // ASM: or rax, rdx
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(&live), 0x1_4000_1000);
    assert!(text.contains("rdtsc_hi"), "{text}");
    assert!(text.contains("rdtsc("), "{text}");
    assert!(!text.contains("rdtsc();"), "{text}");
    let dead = [
        0x0f, 0x31, // ASM: rdtsc
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let dropped = decompiled(&program64(&dead), 0x1_4000_1000);
    assert!(!dropped.contains("rdtsc"), "{dropped}");
    let program = program64(&live);
    let analysis = Analysis::compute(&program);
    let warn = warnings(
        &program,
        &analysis,
        &Overlay::default(),
        0x1_4000_1000,
        &text,
        None,
    )
    .unwrap_or_default();
    assert!(!warn.contains("undeclared"), "{text}\n{warn}");
}

/// `rdtscp` keeps its timestamp and the processor id when both are used.
#[test]
fn rdtscp_keeps_the_aux_register_it_writes() {
    let code = [
        0x0f, 0x01, 0xf9, // ASM: rdtscp
        0x48, 0xc1, 0xe2, 0x20, // ASM: shl rdx, 32
        0x48, 0x09, 0xd0, // ASM: or rax, rdx
        0x48, 0x01, 0xc8, // ASM: add rax, rcx
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("rdtscp_hi"), "{text}");
    assert!(text.contains("rdtscp_ecx"), "{text}");
    assert!(!text.contains("rdtscp();"), "{text}");
}

/// `rdtsc` writes `edx:eax` and leaves `ecx` alone.
#[test]
fn a_plain_rdtsc_keeps_the_ecx_it_did_not_write() {
    let code = [
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0x0f, 0x31, // ASM: rdtsc
        0x01, 0xc8, // ASM: add eax, ecx
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("rdtsc"), "{text}");
    assert!(text.contains('5'), "{text}");
}

/// Two `rdtsc` reads keep a difference. One read xor-ed with itself is zero.
#[test]
fn a_timestamp_delta_is_not_zero_and_one_read_xor_itself_is() {
    let delta = [
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc3, // ASM: mov ebx, eax
        0x0f, 0x31, // ASM: rdtsc
        0x29, 0xd8, // ASM: sub eax, ebx
        0xc3, // ASM: ret
    ];
    let program = program64(&delta);
    let text = decompiled(&program, 0x1_4000_1000);
    assert!(text.matches("rdtsc(").count() >= 2, "{text}");
    assert!(!text.contains("return 0"), "{text}");
    let analysis = Analysis::compute(&program);
    let warn = warnings(
        &program,
        &analysis,
        &Overlay::default(),
        0x1_4000_1000,
        &text,
        None,
    )
    .unwrap_or_default();
    assert!(!warn.contains("contradict"), "{text}\n{warn}");
    let same = [
        0x0f, 0x31, // ASM: rdtsc
        0x89, 0xc3, // ASM: mov ebx, eax
        0x31, 0xd8, // ASM: xor eax, ebx
        0xc3, // ASM: ret
    ];
    let folded = decompiled(&program64(&same), 0x1_4000_1000);
    assert!(folded.contains("return 0"), "{folded}");
}
