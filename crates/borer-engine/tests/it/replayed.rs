//! Shapes from the corpus whose text once disagreed with the machine in
//! the replay: each is decompiled and replayed against the emulator.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

use crate::decompiled::{program64, replays_clean, runs_agree};

/// Decompiles the function at the start of `code` and replays it against
/// the machine.
///
/// # Arguments
///
/// * `code` - The function's bytes.
///
/// # Returns
///
/// The text, for a test to assert on.
fn replayed(code: &[u8]) -> String {
    let p = program64(code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    replays_clean(&p, &a, &[0x1_4000_1000]);
    text
}

/// A rotated scan whose guard makes the loop's own test is no jump back
/// to the guard: the scan still turns until it finds the element or the
/// end, and its text runs as the binary does.
#[test]
fn a_rotated_scan_keeps_turning() {
    let code = [
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0x44, 0x39, 0xc0, // ASM: cmp eax,r8d
        0x7d, 0x10, // ASM: jge done
        0x48, 0x83, 0xc1, 0x04, // ASM: add rcx,4
        0x48, 0x39, 0xd1, // ASM: cmp rcx,rdx
        0x74, 0x08, // ASM: je out
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0x44, 0x39, 0xc0, // ASM: cmp eax,r8d
        0x7c, 0xf0, // ASM: jl -0x10
        0xc3, // ASM: done: ret
        0x31, 0xc0, // ASM: out: xor eax,eax
        0xc3, // ASM: ret
    ];
    replayed(&code);
    runs_agree(&program64(&code), 0x1_4000_1000);
}

/// A scan whose element register only the join's flags read, after a
/// loop-carried pointer the block also steps, writes the element out
/// before the comparison is lifted again over it: the loop's test reads
/// the element just loaded, not the one before.
#[test]
fn a_join_compare_reads_the_fresh_element() {
    replayed(&[
        0x33, 0xd2, // ASM: xor edx,edx
        0x44, 0x8b, 0xda, // ASM: mov r11d,edx
        0x4c, 0x3b, 0xce, // ASM: cmp r9,rsi
        0x73, 0x3a, // ASM: jae end
        0x41, 0x0f, 0xb6, 0x09, // ASM: top: movzx ecx,byte [r9]
        0x49, 0xff, 0xc1, // ASM: inc r9
        0x83, 0xc1, 0xfe, // ASM: add ecx,-2
        0x03, 0xd1, // ASM: add edx,ecx
        0x8b, 0x08, // ASM: mov ecx,[rax]
        0x3b, 0xca, // ASM: cmp ecx,edx
        0x7d, 0x0f, // ASM: jge join
        0x48, 0x83, 0xc0, 0x04, // ASM: step: add rax,4
        0x49, 0x3b, 0xc0, // ASM: cmp rax,r8
        0x74, 0x1f, // ASM: je end
        0x8b, 0x08, // ASM: mov ecx,[rax]
        0x3b, 0xca, // ASM: cmp ecx,edx
        0x7c, 0xf1, // ASM: jl step
        0x75, 0x12, // ASM: join: jne next
        0x0f, 0xb6, 0xca, // ASM: movzx ecx,dl
        0x41, 0x2a, 0xcb, // ASM: sub cl,r11b
        0x44, 0x8b, 0xda, // ASM: mov r11d,edx
        0x80, 0xc1, 0x02, // ASM: add cl,2
        0x41, 0x88, 0x0a, // ASM: mov [r10],cl
        0x49, 0xff, 0xc2, // ASM: inc r10
        0x4c, 0x3b, 0xce, // ASM: next: cmp r9,rsi
        0x72, 0xc6, // ASM: jb top
        0x44, 0x89, 0xd8, // ASM: end: mov eax,r11d
        0xc3, // ASM: ret
    ]);
}

/// A store to a local that a read through a choice of pointers may land
/// on (`a1 ?: &local`) is written before the read: the read is the
/// local's zero when the pointer is null.
#[test]
fn a_read_through_a_choice_of_a_local_sees_its_store() {
    let text = replayed(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xc6, 0x44, 0x24, 0x20, 0x00, // ASM: mov byte [rsp+0x20],0
        0x48, 0x8d, 0x44, 0x24, 0x20, // ASM: lea rax,[rsp+0x20]
        0x48, 0x85, 0xc9, // ASM: test rcx,rcx
        0x48, 0x0f, 0x45, 0xc1, // ASM: cmovne rax,rcx
        0x0f, 0xb6, 0x00, // ASM: movzx eax,byte [rax]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ]);
    let store = text.find(" = 0;").unwrap_or(usize::MAX);
    let read = text.find("return ").unwrap_or(0);
    assert!(store < read, "{text}");
}

/// A double product narrowed to a single (`mulsd; cvtsd2ss`) is the
/// conversion of the double one, though both factors are registers that
/// carry no width of their own.
#[test]
fn a_narrowed_double_product_is_the_double_one() {
    let mut code = vec![
        0x85, 0xd2, // ASM: test edx,edx
        0x74, 0x06, // ASM: je second
        0xf2, 0x0f, 0x10, 0x09, // ASM: movsd xmm1,[rcx]
        0xeb, 0x05, // ASM: jmp have
        0xf2, 0x0f, 0x10, 0x49, 0x08, // ASM: second: movsd xmm1,[rcx+8]
        0x0f, 0x57, 0xff, // ASM: have: xorps xmm7,xmm7
        0xf2, 0x44, 0x0f, 0x10, 0x05, 0xe5, 0x00, 0x00, 0x00, // ASM: movsd xmm8,[rip+0xe5]
        0xf2, 0x44, 0x0f, 0x10, 0x0d, 0xe4, 0x00, 0x00, 0x00, // ASM: movsd xmm9,[rip+0xe4]
        0x0f, 0x57, 0xf6, // ASM: xorps xmm6,xmm6
        0xf2, 0x0f, 0x5a, 0xf1, // ASM: cvtsd2ss xmm6,xmm1
        0x0f, 0x5a, 0xc6, // ASM: cvtps2pd xmm0,xmm6
        0x66, 0x0f, 0x2f, 0xc1, // ASM: comisd xmm0,xmm1
        0x76, 0x1b, // ASM: jbe store
        0x66, 0x0f, 0x2f, 0xf9, // ASM: comisd xmm7,xmm1
        0x76, 0x06, // ASM: jbe down
        0x41, 0x0f, 0x28, 0xc0, // ASM: movaps xmm0,xmm8
        0xeb, 0x04, // ASM: jmp scale
        0x41, 0x0f, 0x28, 0xc1, // ASM: down: movaps xmm0,xmm9
        0xf2, 0x0f, 0x59, 0xc1, // ASM: scale: mulsd xmm0,xmm1
        0x0f, 0x57, 0xf6, // ASM: xorps xmm6,xmm6
        0xf2, 0x0f, 0x5a, 0xf0, // ASM: cvtsd2ss xmm6,xmm0
        0xf3, 0x41, 0x0f, 0x11, 0x30, // ASM: store: movss [r8],xmm6
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[
        0, 0, 0, 0x20, 0, 0, 0xf0, 0x3f, 0, 0, 0, 0xc0, 0xff, 0xff, 0xef, 0x3f,
    ]);
    replayed(&code);
}

/// A switch through a byte table whose compared register the dispatch
/// block rewrites with the byte (`cmp eax, 3; ja D; cdqe; movzx eax, byte
/// [r9+rax+B]`) switches on the index the cases number, not the byte: the
/// slot the byte picks is the case's, as the machine jumps.
#[test]
fn a_byte_table_switch_reads_the_index_the_compare_bounds() {
    let code = [
        0x44, 0x0f, 0xbe, 0x5c, 0x11, 0x01, // ASM: movsx r11d,byte [rcx+rdx+1]
        0x48, 0xff, 0xc2, // ASM: inc rdx
        0x41, 0x8d, 0x43, 0xdb, // ASM: lea eax,[r11-0x25]
        0x83, 0xf8, 0x03, // ASM: cmp eax,3
        0x77, 0x2b, // ASM: ja default
        0x48, 0x98, // ASM: cdqe
        0x4c, 0x8d, 0x0d, 0xe5, 0xef, 0xff, 0xff, // ASM: lea r9,[rip-0x101b] (the image base)
        0x41, 0x0f, 0xb6, 0x84, 0x01, 0x40, 0x10, 0x00,
        0x00, // ASM: movzx eax,byte [r9+rax+0x1040]
        0x41, 0x8b, 0x8c, 0x81, 0x44, 0x10, 0x00, 0x00, // ASM: mov ecx,[r9+rax*4+0x1044]
        0x4c, 0x01, 0xc9, // ASM: add rcx,r9
        0xff, 0xe1, // ASM: jmp rcx
        0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: one: mov eax,10
        0xc3, // ASM: ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: zero: mov eax,20
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: default: xor eax,eax
        0xc3, // ASM: ret
        0x01, 0x00, 0x02, 0x00, // ASM: the byte table, a slot per index
        0x31, 0x10, 0x00, 0x00, 0x37, 0x10, 0x00, 0x00, 0x3d, 0x10, 0x00,
        0x00, // ASM: the slots
    ];
    let mut bytes = vec![0u8; 0x2000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![Section::mapped(
            ".text",
            0x1_4000_0000,
            0,
            0x2000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    replays_clean(&p, &a, &[0x1_4000_1000]);
}
