//! Statements whose text once disagreed with the machine on a block of a
//! system library, each cut down to the instructions that disagreed.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use crate::decompiled::{decompiled, program64, replays_clean};

/// Decompiles the function at the start of `p` and requires its text to
/// agree with the machine on every block.
///
/// # Arguments
///
/// * `p` - The program, its function at 0x140001000.
///
/// # Returns
///
/// The text, for the caller's own assertions.
fn replayed(p: &Program) -> String {
    let text = decompiled(p, 0x1_4000_1000);
    let a = Analysis::compute(p);
    replays_clean(p, &a, &[0x1_4000_1000]);
    text
}

/// A `movq` between vector registers keeps the low qword and clears the
/// rest, so packed work over the copy sees zero upper lanes.
///
/// `movdqu xmm7,[rcx]; movq xmm3,xmm7; paddd xmm3,xmm3; movdqu
/// [rdx],xmm3; ret`, the copy of a loop's constant vector a system
/// library's allocator makes, once copied all sixteen bytes; and the
/// truncated copy widened back into the vector is zero-extended, not
/// sign-extended through `int64_t`.
#[test]
fn a_qword_move_between_vector_registers_clears_the_upper_lanes() {
    let code = [
        0xf3, 0x0f, 0x6f, 0x39, // ASM: movdqu xmm7,[rcx]
        0xf3, 0x0f, 0x7e, 0xdf, // ASM: movq xmm3,xmm7
        0x66, 0x0f, 0xfe, 0xdb, // ASM: paddd xmm3,xmm3
        0xf3, 0x0f, 0x7f, 0x1a, // ASM: movdqu [rdx],xmm3
        0xc3, // ASM: ret
    ];
    let text = replayed(&program64(&code));
    assert!(
        text.contains("(uint128_t)(uint64_t)*(uint128_t*)a1"),
        "{text}"
    );
}

/// A dword stored over a slot whose wider store is still pending keeps
/// the value it read from the slot before that store.
///
/// `mov [rsp+8],rcx; mov ecx,[rsp+8]; mov [rsp+8],rdx; and ecx,0x100;
/// btr edx,8; or ecx,edx; mov [rsp+8],ecx; mov rax,[rsp+8]`, how a
/// feature toggle's flags merge one bit into a configuration word: the
/// write-out of `[rsp+8] = rdx` once came before the merged value that
/// reads the old `[rsp+8]`.
#[test]
fn a_dword_merged_into_a_wider_slot_store_keeps_what_it_read() {
    let code = [
        0x48, 0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8],rcx
        0x8b, 0x4c, 0x24, 0x08, // ASM: mov ecx,[rsp+8]
        0x48, 0x89, 0x54, 0x24, 0x08, // ASM: mov [rsp+8],rdx
        0x81, 0xe1, 0x00, 0x01, 0x00, 0x00, // ASM: and ecx,0x100
        0x0f, 0xba, 0xf2, 0x08, // ASM: btr edx,8
        0x0b, 0xca, // ASM: or ecx,edx
        0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8],ecx
        0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax,[rsp+8]
        0xc3, // ASM: ret
    ];
    replayed(&program64(&code));
}

/// A call into a thunk that jumps through `rax` reads `rax`, so the load
/// into it before an intervening store is kept, not dropped as dead.
///
/// `mov rax,[rcx+0x38]; mov dword [rcx+0x20],0; call T; ret` with `T:
/// jmp rax`, the control-flow-guard dispatch a generic table's delete
/// makes to its free routine: the store once wrote out every value read
/// from memory but forgot `rax`, which no instruction seemed to read, and
/// the call went through a stale `rax`.
#[test]
fn a_call_through_a_dispatch_thunk_keeps_the_register_it_jumps_through() {
    let mut code = vec![
        0x48, 0x8b, 0x41, 0x38, // ASM: mov rax,[rcx+0x38]
        0xc7, 0x41, 0x20, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rcx+0x20],0
        0xe8, 0x30, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([0xff, 0xe0]);
    let text = replayed(&program64(&code));
    assert!(text.contains("(a1 + 0x38)"), "{text}");
}
