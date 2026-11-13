//! Shapes from the corpus whose text once disagreed with the machine in
//! the replay: each is decompiled and replayed against the emulator.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::replay::{
    Claim, Replayed, replay, replay_function, replay_tsv,
};
use borer_engine::analysis::decompile::{checked_header, decompile};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

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

/// A loop's test after a join on its compare reads the element just loaded.
///
/// The element register only the join's flags read, beside a loop-carried
/// pointer the block also steps, is written out before the comparison is
/// lifted again over it, not left at the element loaded before.
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

/// A switch through a byte table switches on the index the cases number.
///
/// The dispatch block rewrites the compared register with the byte
/// (`cmp eax, 3; ja D; cdqe; movzx eax, byte [r9+rax+B]`); the switch reads
/// the index, not the byte, and the slot the byte picks is the case's, as
/// the machine jumps.
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

/// Replays a function from four seeds and requires that every block was
/// compared, none refuted and no value wrong.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `entry` - The function.
///
/// # Returns
///
/// Each seed's replay, for a test to assert on.
fn checks_every_block(p: &Program, a: &Analysis, entry: u64) -> Vec<Replayed> {
    (1..=4)
        .map(|seed| {
            let r = replay(p, a, &[entry], seed);
            let tsv = replay_tsv(&r);
            assert_eq!(r.functions, 1, "seed {seed}:\n{tsv}");
            assert!(r.blocks > 0 && r.checked == r.blocks, "seed {seed}:\n{tsv}");
            assert!(r.refuted.is_empty(), "seed {seed}:\n{tsv}");
            assert!(r.wrong().is_empty(), "seed {seed}:\n{tsv}");
            r
        })
        .collect()
}

/// A read through a pointer parameter beside the function's own stack
/// writes is not refuted by a pointer into that frame.
///
/// The frame's addresses are constants of the proof's terms, so its search
/// once started `a1` just below the stack pointer, where `*(a1 + 2)` reads
/// the locals the machine wrote and the text keeps as their own variables.
/// No caller can pass the address of a frame allocated after the call.
#[test]
fn a_pointer_parameter_never_points_into_the_callee_frame() {
    let p = program64(&[
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp,0x18
        0x48, 0x8b, 0x05, 0x75, 0x00, 0x00, 0x00, // ASM: mov rax,[rip+0x75]
        0x48, 0x33, 0xc4, // ASM: xor rax,rsp
        0x48, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8],rax
        0x45, 0x33, 0xc0, // ASM: xor r8d,r8d
        0x66, 0xc7, 0x44, 0x24, 0x04, 0x00, 0x13, // ASM: mov word [rsp+4],0x1300
        0x80, 0x79, 0x01, 0x02, // ASM: cmp byte [rcx+1],2
        0x44, 0x89, 0x04, 0x24, // ASM: mov [rsp],r8d
        0x75, 0x1c, // ASM: jne fail
        0x80, 0x39, 0x01, // ASM: cmp byte [rcx],1
        0x75, 0x17, // ASM: jne fail
        0x8b, 0x51, 0x02, // ASM: mov edx,[rcx+2]
        0x41, 0x2b, 0xd0, // ASM: sub edx,r8d
        0x75, 0x0b, // ASM: jne test
        0x0f, 0xb7, 0x51, 0x06, // ASM: movzx edx,word [rcx+6]
        0x0f, 0xb7, 0x44, 0x24, 0x04, // ASM: movzx eax,word [rsp+4]
        0x2b, 0xd0, // ASM: sub edx,eax
        0x85, 0xd2, // ASM: test: test edx,edx
        0x74, 0x04, // ASM: je ok
        0x32, 0xc0, // ASM: fail: xor al,al
        0xeb, 0x02, // ASM: jmp out
        0xb0, 0x01, // ASM: ok: mov al,1
        0x48, 0x8b, 0x4c, 0x24, 0x08, // ASM: out: mov rcx,[rsp+8]
        0x48, 0x33, 0xcc, // ASM: xor rcx,rsp
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp,0x18
        0xc3, // ASM: ret
    ]);
    checks_every_block(&p, &Analysis::compute(&p), 0x1_4000_1000);
}

/// A read through a pointer parameter beside a stack argument is not
/// refuted by a pointer at that argument.
///
/// The return address, the shadow space and the stack arguments above
/// them are the callee's: the text names the fifth argument `a5`, and no
/// caller passes a pointer to the arguments it hands over.
#[test]
fn a_pointer_parameter_never_points_at_the_callee_arguments() {
    let p = program64(&[
        0x4c, 0x89, 0x4c, 0x24, 0x20, // ASM: mov [rsp+0x20],r9
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x85, 0xd2, // ASM: test edx,edx
        0x74, 0x11, // ASM: je out
        0x48, 0x8b, 0x4c, 0x24, 0x50, // ASM: mov rcx,[rsp+0x50]
        0x41, 0x0f, 0xb7, 0x00, // ASM: movzx eax,word [r8]
        0x48, 0x01, 0xc8, // ASM: add rax,rcx
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: out: xor eax,eax
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ]);
    checks_every_block(&p, &Analysis::compute(&p), 0x1_4000_1000);
}

/// A switch on a class picked by conditional moves switches on the class,
/// though its table's first bytes read as a string.
///
/// The table in read-only data starts `65 00 ff ff`, so the lift reads
/// its address as the string "e"; the index is still the one the table is
/// read at, the class the moves chose (`cmove r12d, edi; cmp r14, rsi;
/// cmove r12d, r15d; movzx esi, r12b`), not the register the last compare
/// read, which only picks one of the classes.
#[test]
fn a_switch_through_a_table_that_reads_as_a_string_reads_its_index() {
    let mut code = vec![
        0x48, 0xbe, 0, 0, 0, 0, 0, 0, 0xf0, 0x7f, // ASM: mov rsi,0x7ff0000000000000
        0x49, 0x89, 0xce, // ASM: mov r14,rcx
        0x49, 0x21, 0xf6, // ASM: and r14,rsi
        0x45, 0x31, 0xff, // ASM: xor r15d,r15d
        0x48, 0x85, 0xd2, // ASM: test rdx,rdx
        0x41, 0x0f, 0x94, 0xc7, // ASM: sete r15b
        0x44, 0x89, 0xff, // ASM: mov edi,r15d
        0x40, 0x80, 0xf7, 0x03, // ASM: xor dil,3
        0x40, 0x0f, 0xb6, 0xff, // ASM: movzx edi,dil
        0x4d, 0x85, 0xf6, // ASM: test r14,r14
        0x41, 0xbc, 0x04, 0x00, 0x00, 0x00, // ASM: mov r12d,4
        0x44, 0x0f, 0x44, 0xe7, // ASM: cmove r12d,edi
        0x49, 0x39, 0xf6, // ASM: cmp r14,rsi
        0x45, 0x0f, 0x44, 0xe7, // ASM: cmove r12d,r15d
        0x41, 0x0f, 0xb6, 0xf4, // ASM: movzx esi,r12b
        0x48, 0x8d, 0x3d, 0xbc, 0xff, 0x00, 0x00, // ASM: lea rdi,[rip+0xffbc] (the table)
        0x48, 0x63, 0x34, 0xb7, // ASM: movsxd rsi,[rdi+rsi*4]
        0x48, 0x01, 0xfe, // ASM: add rsi,rdi
        0xff, 0xe6, // ASM: jmp rsi
    ];
    code.resize(0x65, 0xcc);
    for class in 10..15 {
        code.extend_from_slice(&[0xb8, class, 0, 0, 0, 0xc3]); // ASM: mov eax,class; ret
    }
    let mut bytes = vec![0u8; 0x12000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    for (slot, at) in (0x11000..).step_by(4).take(5).enumerate() {
        let offset = 0xffff_0065_u32 + 6 * u32::try_from(slot).unwrap_or(0);
        bytes[at..at + 4].copy_from_slice(&offset.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x1_4001_1000, 0x11000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).expect("decompiles");
    let class = text
        .lines()
        .find(|l| l.starts_with("var1 = "))
        .expect("the class is assigned");
    assert!(
        class.contains("== 0x7ff0000000000000 ? a2 == 0 :") && class.ends_with(": 4));"),
        "{text}"
    );
    assert!(text.contains("switch (var1) {"), "{text}");
    for (case, value) in (0..5).zip(10..15) {
        let arm = format!("case {case}: {{\n  return {value};\n}}");
        assert!(text.contains(&arm), "{text}");
    }
    for r in checks_every_block(&p, &a, 0x1_4000_1000) {
        let switches = r.compared.get(&Claim::Switch).copied().unwrap_or(0);
        assert!(switches > 0, "{}", replay_tsv(&r));
    }
}

/// A block that writes over its own later instructions is not checked:
/// the machine runs the bytes the block wrote, the text the bytes the
/// image holds, so no lifting of the image's bytes could agree.
#[test]
fn a_block_writing_over_its_own_code_is_not_checked() {
    let p = program64(&[
        0x48, 0x8d, 0x05, 0x00, 0x00, 0x00, 0x00, // ASM: lea rax,[rip]
        0x66, 0xc7, 0x40, 0x08, 0x90, 0x90, // ASM: mov word [rax+8],0x9090
        0x31, 0xc0, // ASM: xor eax,eax
        0xff, 0xc0, // ASM: inc eax
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let r = replay(&p, &a, &[0x1_4000_1000], 1);
    assert_eq!((r.functions, r.blocks), (1, 1), "{}", replay_tsv(&r));
    assert_eq!(
        r.skipped.get("the block writes over its own code"),
        Some(&1),
        "{}",
        replay_tsv(&r)
    );
    assert!(r.wrong().is_empty(), "{}", replay_tsv(&r));
}

/// The lift line of the function at 0x401000 of `code`, decompiled as an
/// image of `arch` and `format`.
///
/// # Arguments
///
/// * `code` - The function's bytes.
/// * `arch` - The instruction set, which picks the block's width.
/// * `format` - The image's format, whose system lays out the thread block.
fn checked_as(code: &[u8], arch: Arch, format: BinaryFormat) -> String {
    let mut bytes = code.to_vec();
    bytes.resize(0x1000, 0xcc);
    let text = Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true);
    let mut p = Program::raw(bytes, arch, 0x40_0000, Some(0x40_1000), vec![text]);
    p.format = format;
    let a = Analysis::compute(&p);
    checked_header(&p, &a, &Overlay::default(), 0x40_1000).unwrap_or_default()
}

/// A function guarded with a Linux stack canary, at 0x140001000.
///
/// The prologue copies `fs:[0x28]` into a slot and the epilogue subtracts
/// the word from the slot, calling `__stack_chk_fail` at 0x140001040 when
/// they differ.
fn canary_function() -> Program {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
        0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: mov rax, fs:[0x28]
        0x48, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp + 0x8], rax
        0x31, 0xc0, // ASM: xor eax, eax
        0x8d, 0x41, 0x01, // ASM: lea eax, [rcx + 1]
        0x48, 0x8b, 0x54, 0x24, 0x08, // ASM: mov rdx, [rsp + 0x8]
        0x64, 0x48, 0x2b, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: sub rdx, fs:[0x28]
        0x75, 0x05, // ASM: jne fail
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
        0xc3, // ASM: ret
        0xe8, 0x0f, 0x00, 0x00, 0x00, // ASM: fail: call __stack_chk_fail
    ];
    code.resize(0x40, 0xcc);
    code.extend([0x0f, 0x0b]); // ASM: ud2 (__stack_chk_fail)
    let mut p = program64(&code);
    p.symbols.push(Symbol {
        name: "__stack_chk_fail".to_owned(),
        addr: 0x1_4000_1040,
        kind: SymbolKind::Local,
    });
    p
}

/// A Linux stack canary is checked against the machine.
///
/// The replay plants glibc's canary word at `fs:[0x28]` and the text reads
/// that word, so the prologue's copy and the epilogue's compare are
/// compared and proved, not left unknown. As a Windows image, whose `fs`
/// reads no thread block on x64, the same blocks stay unknown, and the
/// return that the epilogue's `fs` read is pending into is tried, not
/// proved: the proof states no value for that segment.
#[test]
fn a_canary_prologue_and_epilogue_are_checked() {
    let mut p = canary_function();
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let header = checked_header(&p, &a, &Overlay::default(), 0x1_4000_1000).expect("checked");
    assert!(
        header.contains("2/3 blocks: 2 proved vs lift, 1 unknown; unchecked: 1 not in text,"),
        "{header}"
    );
    replays_clean(&p, &a, &[0x1_4000_1000]);
    let r = replay_function(&p, &a, 0x1_4000_1000, 1);
    assert!(r.unreadable.is_empty(), "{}", replay_tsv(&r));
    assert_eq!(
        r.compared.get(&Claim::Branch),
        Some(&3),
        "{}",
        replay_tsv(&r)
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let header = checked_header(&p, &a, &Overlay::default(), 0x1_4000_1000).expect("checked");
    assert!(
        header.contains(
            "1/3 blocks: 0 proved vs lift, 1 tested x3 states, 2 unknown; unchecked: 1 fs/gs access, 1 not in text,"
        ),
        "{header}"
    );
}

/// A thread block read is checked where the machine plants the field.
///
/// Those are Windows' stack bounds, the block's own address and the
/// process block's, and glibc's canary. The process block's contents,
/// planted as zero rather than as Windows fills them, read as unknown to
/// the text, so no claim agrees on them by accident, while memory past the
/// planted span reads as any memory nothing backs. A field planted as
/// zero, a write, a computed offset and glibc's pointer guard leave their
/// blocks unknown.
#[test]
fn a_thread_block_field_is_checked_where_the_machine_plants_it() {
    let windows_64: [&[u8]; 4] = [
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x08, 0, 0, 0], // ASM: mov rax, gs:[0x8]
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x10, 0, 0, 0], // ASM: mov rax, gs:[0x10]
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x30, 0, 0, 0], // ASM: mov rax, gs:[0x30]
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x60, 0, 0, 0], // ASM: mov rax, gs:[0x60]
    ];
    let windows_32: [&[u8]; 4] = [
        &[0x64, 0xa1, 0x04, 0, 0, 0], // ASM: mov eax, fs:[0x4]
        &[0x64, 0xa1, 0x08, 0, 0, 0], // ASM: mov eax, fs:[0x8]
        &[0x64, 0xa1, 0x18, 0, 0, 0], // ASM: mov eax, fs:[0x18]
        &[0x64, 0xa1, 0x30, 0, 0, 0], // ASM: mov eax, fs:[0x30]
    ];
    let glibc_32: [&[u8]; 1] = [
        &[0x65, 0xa1, 0x14, 0, 0, 0], // ASM: mov eax, gs:[0x14]
    ];
    let planted = windows_64
        .iter()
        .map(|c| (c, Arch::X86_64, BinaryFormat::Pe))
        .chain(windows_32.iter().map(|c| (c, Arch::X86, BinaryFormat::Pe)))
        .chain(glibc_32.iter().map(|c| (c, Arch::X86, BinaryFormat::Elf)));
    for (code, arch, format) in planted {
        let mut code = code.to_vec();
        code.push(0xc3); // ASM: ret
        let header = checked_as(&code, arch, format);
        assert!(
            header.contains("1/1 blocks: 1 proved vs lift;"),
            "{code:x?}: {header}"
        );
    }
    let read_through = |field: u8, offset: u32| {
        let mut code = vec![
            0x65, 0x48, 0x8b, 0x04, 0x25, field, 0, 0, 0, // ASM: mov rax, gs:[field]
            0x48, 0x8b, 0x80, // ASM: mov rax, [rax + offset]
        ];
        code.extend(offset.to_le_bytes());
        code.push(0xc3); // ASM: ret
        let p = program64(&code);
        let a = Analysis::compute(&p);
        let header = checked_header(&p, &a, &Overlay::default(), 0x1_4000_1000);
        (
            header.unwrap_or_default(),
            replay_function(&p, &a, 0x1_4000_1000, 1),
        )
    };
    let (header, r) = read_through(0x60, 0x30);
    assert!(header.contains("1/1 blocks: 1 proved vs lift;"), "{header}");
    assert_eq!(
        r.unreadable.get(&Claim::Return),
        Some(&3),
        "{}",
        replay_tsv(&r)
    );
    let (_, r) = read_through(0x30, 0x2000);
    assert!(r.unreadable.is_empty(), "{}", replay_tsv(&r));
    assert_eq!(
        r.compared.get(&Claim::Return),
        Some(&3),
        "{}",
        replay_tsv(&r)
    );
    let windows_unknown: [&[u8]; 4] = [
        &[0x65, 0x8b, 0x04, 0x25, 0x68, 0, 0, 0], // ASM: mov eax, gs:[0x68]
        &[0x65, 0x48, 0x89, 0x04, 0x25, 0x30, 0, 0, 0], // ASM: mov gs:[0x30], rax
        &[0x65, 0x48, 0x8b, 0x41, 0x30],          // ASM: mov rax, gs:[rcx + 0x30]
        &[0x65, 0x48, 0x8b, 0x04, 0xcd, 0x30, 0, 0, 0], // ASM: mov rax, gs:[rcx*8 + 0x30]
    ];
    let glibc_unknown: [&[u8]; 1] = [
        &[0x64, 0x48, 0x8b, 0x04, 0x25, 0x30, 0, 0, 0], // ASM: mov rax, fs:[0x30]
    ];
    let unknown = windows_unknown
        .iter()
        .map(|c| (c, BinaryFormat::Pe))
        .chain(glibc_unknown.iter().map(|c| (c, BinaryFormat::Elf)));
    for (code, format) in unknown {
        let mut code = code.to_vec();
        code.push(0xc3); // ASM: ret
        let header = checked_as(&code, Arch::X86_64, format);
        assert!(
            header.contains("0/1 blocks: 0 proved vs lift, 1 unknown; unchecked: 1 fs/gs access,"),
            "{code:x?}: {header}"
        );
    }
}

/// The replay's report names what a proved block is measured against, the
/// lift, as the decompile header does: the proof shares the lifter's
/// reading of each instruction.
#[test]
fn the_replay_report_says_proved_vs_lift() {
    let p = program64(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let report = replay_tsv(&replay_function(&p, &a, 0x1_4000_1000, 1));
    assert!(
        report.contains("\n# proved vs lift over every state: "),
        "{report}"
    );
}
