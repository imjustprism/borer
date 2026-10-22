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

/// A frame read through a sign-extended index may read a slot below the
/// array it indexes.
///
/// A store pending in that slot is written before the read, and a later
/// store to it is not moved before the read.
///
/// `mov [rsp],rdx; mov [rsp+8],r8; movsxd rax,ecx; mov
/// rax,[rsp+rax*8+8]; ...; mov [rsp],r9; mov [r9],rax`: an index of -1
/// reads `[rsp]`, as `movsxd` indexing a local table may.
#[test]
fn a_signed_index_into_the_frame_may_read_a_slot_below_it() {
    let code = [
        0x48, 0x83, 0xec, 0x38, // ASM: sub rsp,0x38
        0x48, 0x89, 0x14, 0x24, // ASM: mov [rsp],rdx
        0x4c, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8],r8
        0x48, 0x63, 0xc1, // ASM: movsxd rax,ecx
        0x48, 0x8b, 0x44, 0xc4, 0x08, // ASM: mov rax,[rsp+rax*8+8]
        0x4d, 0x85, 0xc9, // ASM: test r9,r9
        0x74, 0x05, // ASM: je +5
        0x4c, 0x89, 0x0c, 0x24, 0x90, // ASM: mov [rsp],r9; nop
        0x49, 0x89, 0x01, // ASM: mov [r9],rax
        0x48, 0x8b, 0x04, 0x24, 0x90, // ASM: mov rax,[rsp]; nop
        0x48, 0x83, 0xc4, 0x38, // ASM: add rsp,0x38
        0xc3, // ASM: ret
    ];
    replayed(&program64(&code));
}

/// A frame read through an index that may wrap the address space reads
/// whatever slot it lands on, so the store pending in a slot below the
/// array is written before it.
///
/// `mov [rsp+0x10],rdx; sub rcx,1; mov [rsp],rcx; mov
/// rax,[rsp+rcx*8+0x10]`, the pop of `qsort`'s explicit stack: an index
/// of `2^63 - 2` reads `[rsp]`, the index itself.
#[test]
fn an_index_into_the_frame_that_wraps_reads_the_slot_it_lands_on() {
    let code = [
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp,0x48
        0x48, 0x89, 0x54, 0x24, 0x10, // ASM: mov [rsp+0x10],rdx
        0x48, 0x83, 0xe9, 0x01, // ASM: sub rcx,1
        0x48, 0x89, 0x0c, 0x24, // ASM: mov [rsp],rcx
        0x48, 0x8b, 0x44, 0xcc, 0x10, // ASM: mov rax,[rsp+rcx*8+0x10]
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp,0x48
        0xc3, // ASM: ret
    ];
    replayed(&program64(&code));
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

/// A frame store through an index read from a slot keeps the index the
/// slot held, though the store writes out a later store to that slot.
///
/// `mov rax,[rsp+0x30]; mov qword [rsp+0x30],0; mov [rsp+rax+0x40],cx`,
/// the terminator a system library writes into a local buffer at the
/// length a call left in a local it then clears.
#[test]
fn a_frame_store_through_an_index_read_from_a_slot_keeps_the_index() {
    let code = [
        0x48, 0x83, 0xec, 0x68, // ASM: sub rsp,0x68
        0x48, 0x8b, 0x44, 0x24, 0x30, // ASM: mov rax,[rsp+0x30]
        0x48, 0xc7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+0x30],0
        0x66, 0x89, 0x4c, 0x04, 0x40, // ASM: mov [rsp+rax+0x40],cx
        0x48, 0x8b, 0x44, 0x24, 0x40, // ASM: mov rax,[rsp+0x40]
        0x48, 0x83, 0xc4, 0x68, // ASM: add rsp,0x68
        0xc3, // ASM: ret
    ];
    replayed(&program64(&code));
}

/// A frame store through an index computed from a register keeps the
/// register's old value, though the store writes out the register's newer
/// one, read from a slot the store may land on.
///
/// `call f; lea r8,[rax+2]; mov rax,[rsp+0x60]; mov byte
/// [rsp+r8+0x86],0x7b`, a formatter writing a `{` into a local buffer: the
/// write-out of `rax = local_60` once came before the store whose index
/// reads the `rax` the call returned.
#[test]
fn a_frame_store_through_an_index_keeps_the_register_it_read() {
    let mut code = vec![
        0x48, 0x81, 0xec, 0x08, 0x01, 0x00, 0x00, // ASM: sub rsp,0x108
        0xe8, 0x34, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0x4c, 0x8d, 0x40, 0x02, // ASM: lea r8,[rax+2]
        0x48, 0x8b, 0x44, 0x24, 0x60, // ASM: mov rax,[rsp+0x60]
        0x48, 0xc7, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+0x88],1
        0x42, 0xc6, 0x84, 0x04, 0x86, 0x00, 0x00, 0x00,
        0x7b, // ASM: mov byte [rsp+r8+0x86],0x7b
        0x48, 0x03, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, // ASM: add rax,[rsp+0x88]
        0x48, 0x81, 0xc4, 0x08, 0x01, 0x00, 0x00, // ASM: add rsp,0x108
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend([
        0x48, 0x8b, 0x01, // ASM: mov rax,[rcx]
        0xc3, // ASM: ret
    ]);
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
