//! Control-flow shapes written as a source spells them.
//!
//! A jump table's bound check is the `switch`'s `default`, an endless
//! loop's way out follows the loop, a loop that only computes its own
//! test is the empty `while (test);`, and a loop the function starts with
//! is entered from the caller as well as from its back edge.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::traces::{Structure, check_structure};
use borer_engine::analysis::render::function_summary;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

use crate::decompiled::{decompiled, program64, program64_with_data, replays_clean, runs_agree};

/// Where the hand-assembled functions start.
const F: u64 = 0x1_4000_1000;

/// Decompiles `code` as a 64-bit function, requires its text to hold
/// `want`, and requires the structure check to read the text's paths as
/// the binary's, the empty `while` a loop.
///
/// # Arguments
///
/// * `code` - The function's bytes, placed at [`F`].
/// * `want` - Lines the text holds, their newlines included.
fn spins_as(code: &[u8], want: &str) {
    let p = program64(code);
    let text = decompiled(&p, F);
    assert!(text.contains(want), "{text}");
    let a = Analysis::compute(&p);
    assert_eq!(
        check_structure(&p, &a, &Overlay::default(), F, &text),
        Structure::Agrees,
        "{text}"
    );
}

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

/// A loop that polls a load with nothing in its body is the empty `while`
/// a source spells it as.
///
/// `L: mov eax,[0x40023808]; test al,2; je L; xor eax,eax; ret` waits for
/// bit 1 of a device word: the structurer's empty `do` reads as `while
/// (test);`.
#[test]
fn a_wait_on_a_load_is_an_empty_while() {
    let code: &[u8] = &[
        0x8b, 0x04, 0x25, 0x08, 0x38, 0x02, 0x40, // ASM: mov eax,[0x40023808]
        0xa8, 0x02, // ASM: test al,2
        0x74, 0xf5, // ASM: je 0x0
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    spins_as(
        code,
        "\nwhile ((*(uint32_t*)0x40023808 & 2) == 0);\nreturn 0;\n",
    );
}

/// A loop that only calls for the value its test reads is the empty
/// `while` with the call standing where its result did.
///
/// `sub rsp,0x28; L: call G; test al,1; je L; xor eax,eax; add rsp,0x28;
/// ret`, `G` loading a device word: the test alone reads the register the
/// call sets.
#[test]
fn a_wait_on_a_call_is_an_empty_while() {
    let code: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x14
        0xa8, 0x01, // ASM: test al,1
        0x74, 0xf7, // ASM: je 0x4
        0x31, 0xc0, // ASM: xor eax,eax
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
        0x8b, 0x04, 0x25, 0x08, 0x38, 0x02, 0x40, // ASM: mov eax,[0x40023808]
        0xc3, // ASM: ret
    ];
    spins_as(code, "\nwhile ((sub_140001014() & 1) == 0);\nreturn 0;\n");
}

/// An endless loop whose one way out returns is the empty `while` of the
/// negated exit test, the exit's statements after it.
///
/// `L: test ecx,ecx; je X; mov eax,[0x40000000]; cmp eax,[0x40000004]; je
/// L; X: mov byte [0x40000008],1; ret` waits while its argument is set and
/// two words agree, then stores once.
#[test]
fn a_wait_left_by_one_return_is_an_empty_while_then_the_exit() {
    let code: &[u8] = &[
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x10, // ASM: je 0x14
        0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x40, // ASM: mov eax,[0x40000000]
        0x3b, 0x04, 0x25, 0x04, 0x00, 0x00, 0x40, // ASM: cmp eax,[0x40000004]
        0x74, 0xec, // ASM: je 0x0
        0xc6, 0x04, 0x25, 0x08, 0x00, 0x00, 0x40, 0x01, // ASM: mov byte [0x40000008],1
        0xc3, // ASM: ret
    ];
    spins_as(
        code,
        "\nwhile (a1 != 0 && *(uint32_t*)0x40000000 == *(uint32_t*)0x40000004);\n*(uint8_t*)0x40000008 = 1;\n",
    );
}

/// The empty `while` runs as the loop it is: the final text of a wait on
/// a byte the argument points at returns wherever the binary does.
///
/// `L: test byte [rcx],1; je L; xor eax,eax; ret` returns 0 once bit 0
/// of the byte is set and waits for it forever otherwise.
#[test]
fn an_empty_while_runs_as_the_loop() {
    let code: &[u8] = &[
        0xf6, 0x01, 0x01, // ASM: test byte [rcx],1
        0x74, 0xfb, // ASM: je 0x0
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(code), F);
    assert!(
        text.contains("\nwhile ((*(uint8_t*)a1 & 1) == 0);\nreturn 0;\n"),
        "{text}"
    );
}

/// What an endless loop runs on its one way out is written after it.
///
/// `test rcx,rcx; je R; L: call H(rbx); test rax,rax; je X; call G(rbx);
/// jmp L; X: call G(rbx); R: xor eax,eax; ret`, `H` reading through its
/// argument and `G` writing through it: the second `call G` runs once the
/// loop is left, so it follows the loop rather than sitting in the arm
/// that breaks out of it.
#[test]
fn an_endless_loop_s_way_out_follows_it() {
    let code: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x85, 0xc9, // ASM: test rcx,rcx
        0x74, 0x22, // ASM: je 0x28
        0x48, 0x89, 0xcb, // ASM: mov rbx,rcx
        0x48, 0x89, 0xd9, // ASM: mov rcx,rbx
        0xe8, 0x1f, 0x00, 0x00, 0x00, // ASM: call 0x30
        0x48, 0x85, 0xc0, // ASM: test rax,rax
        0x74, 0x0a, // ASM: je 0x20
        0x48, 0x89, 0xd9, // ASM: mov rcx,rbx
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x34
        0xeb, 0xe9, // ASM: jmp 0x9
        0x48, 0x89, 0xd9, // ASM: mov rcx,rbx
        0xe8, 0x0c, 0x00, 0x00, 0x00, // ASM: call 0x34
        0x31, 0xc0, // ASM: xor eax,eax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
        0x48, 0x8b, 0x01, // ASM: mov rax,[rcx]
        0xc3, // ASM: ret
        0x48, 0x89, 0x01, // ASM: mov [rcx],rax
        0xc3, // ASM: ret
    ];
    let p = program64(code);
    let a = Analysis::compute(&p);
    let text = decompiled(&p, F);
    assert!(text.contains("while (1) {"), "{text}");
    assert!(
        text.contains(
            "
  }
  sub_140001034("
        ),
        "{text}"
    );
    replays_clean(&p, &a, &[F]);
}

/// A loop the function starts with waits only while its test holds: the
/// caller enters it with any argument, not only the one its back edge
/// brings.
///
/// `L: cmp ecx,5; je L; xor eax,eax; ret` returns 0 for every argument
/// but 5, and `E: cmp ecx,5; jne R; add edx,1; cmp ecx,5; je E; R: mov
/// eax,edx; ret` returns its second argument for every first but 5. Each
/// entry's one predecessor is a back edge on `ecx == 5`: read as the only
/// way in, it folded the entry's test, and neither text ever returned.
#[test]
fn a_loop_at_the_entry_is_entered_with_any_argument() {
    let self_loop: &[u8] = &[
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x74, 0xfb, // ASM: je 0x0
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(self_loop), F);
    assert!(
        text.contains("uint32_t sub_140001000(uint32_t a1)"),
        "{text}"
    );
    assert!(
        text.contains("\nwhile ((uint32_t)a1 == 5);\nreturn 0;\n"),
        "{text}"
    );
    let two_blocks: &[u8] = &[
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x75, 0x08, // ASM: jne 0xd
        0x83, 0xc2, 0x01, // ASM: add edx,1
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x74, 0xf3, // ASM: je 0x0
        0x89, 0xd0, // ASM: mov eax,edx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(two_blocks), F);
    assert!(
        text.contains("\nwhile ((uint32_t)a1 == 5) {\n  var1 += 1;\n}\nreturn var1;\n"),
        "{text}"
    );
}

/// The way out of a loop at the entry reaches every answer read off the
/// text: the header's effects, the summary, and a caller's copy of the
/// body.
///
/// `g: sub rsp,0x28; call f; mov eax,7; add rsp,0x28; ret` calls `f: L:
/// cmp ecx,5; je L; mov byte [rdx+8],1; xor eax,eax; ret`. With the exit
/// dropped, `f` read `void`, wrote nothing, and `g` inlined it as a loop
/// that never ends.
#[test]
fn a_loop_at_the_entry_keeps_its_way_out_in_every_answer() {
    let mut code = vec![0xcc; 0x2c];
    code[..0x13].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x20
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ]);
    code[0x20..].copy_from_slice(&[
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x74, 0xfb, // ASM: je 0x20
        0xc6, 0x42, 0x08, 0x01, // ASM: mov byte [rdx+8],1
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let f = runs_agree(&p, F + 0x20);
    assert!(f.contains("\n// effects: writes a2+8\n"), "{f}");
    let a = Analysis::compute(&p);
    let summary = function_summary(&p, &a, &Overlay::default(), F + 0x20).unwrap_or_default();
    assert!(summary.contains("\neffects:  writes a2+8\n"), "{summary}");
    let g = decompiled(&p, F);
    assert!(
        g.contains("{ while ((uint32_t)a1 == 5); *(uint8_t*)(a2 + 8) = 1; return 0; }"),
        "{g}"
    );
    assert!(g.contains("\nreturn 7;\n"), "{g}");
}

/// A loop at an arm64 or A32 entry waits only while its test holds too:
/// the lifters share the assumption a block reads under.
///
/// `L: cmp w0,#5; b.eq L; mov w0,#0; ret` and `L: cmp r0,#5; beq L; mov
/// r0,#0; bx lr` each read `while (1) { }`, the return dropped.
#[test]
fn an_arm_loop_at_the_entry_is_entered_with_any_argument() {
    let a64: [u32; 4] = [
        0x7100_141f, // ASM: cmp w0, #0x5
        0x54ff_ffe0, // ASM: b.eq 0x401000
        0x5280_0000, // ASM: mov w0, #0x0
        0xd65f_03c0, // ASM: ret
    ];
    let a32: [u32; 4] = [
        0xe350_0005, // ASM: cmp r0, #0x5
        0x0aff_fffd, // ASM: beq 0x401000
        0xe3a0_0000, // ASM: mov r0, #0x0
        0xe12f_ff1e, // ASM: bx lr
    ];
    for (arch, words, want) in [
        (
            Arch::Arm64,
            a64,
            "\nwhile ((uint32_t)a1 == 5);\nreturn 0;\n",
        ),
        (Arch::Arm, a32, "\nwhile (a1 == 5);\nreturn 0;\n"),
    ] {
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let text = decompiled(&crate::raw::image(arch, &code, &[]), 0x40_1000);
        assert!(text.contains(want), "{text}");
    }
}

/// A register read after an arm64 or A32 count-down loop holds what the
/// loop left in it: the lifters share the fact a block reads under, and
/// what ends it.
///
/// `mov x9,x0; mov x0,#0; L: ldr x10,[x1],#8; add x0,x0,x10; subs x9,x9,#1;
/// b.ne L; add w11,w9,#8; str w11,[x2]; ret` and its A32 twin leave the
/// loop when the counter was 1 where `subs` read it, and `subs` leaves it
/// zero: the store after the loop is the counter the loop counted down
/// plus 8, which read 9, and is not the copy of it the loop's test reads.
#[test]
fn a_register_read_after_an_arm_loop_holds_what_the_loop_left() {
    let a64: [u32; 9] = [
        0xaa00_03e9, // ASM: mov x9, x0
        0xd280_0000, // ASM: mov x0, #0
        0xf840_842a, // ASM: ldr x10, [x1], #8
        0x8b0a_0000, // ASM: add x0, x0, x10
        0xf100_0529, // ASM: subs x9, x9, #1
        0x54ff_ffa1, // ASM: b.ne 0x401008
        0x1100_212b, // ASM: add w11, w9, #8
        0xb900_004b, // ASM: str w11, [x2]
        0xd65f_03c0, // ASM: ret
    ];
    let a32: [u32; 9] = [
        0xe1a0_3000, // ASM: mov r3, r0
        0xe3a0_0000, // ASM: mov r0, #0
        0xe491_c004, // ASM: ldr ip, [r1], #4
        0xe080_000c, // ASM: add r0, r0, ip
        0xe253_3001, // ASM: subs r3, r3, #1
        0x1aff_fffb, // ASM: bne 0x401008
        0xe283_c008, // ASM: add ip, r3, #8
        0xe582_c000, // ASM: str ip, [r2]
        0xe12f_ff1e, // ASM: bx lr
    ];
    let cases = [
        (Arch::Arm64, a64, "var3", "var4"),
        (Arch::Arm, a32, "r3", "var1"),
    ];
    for (arch, words, counter, read) in cases {
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let text = decompiled(&crate::raw::image(arch, &code, &[]), 0x40_1000);
        let store = format!(
            "  {counter} -= 1;\n}} while ({read} != 1);\n*(uint32_t*)a3 = {counter} + 8;\n"
        );
        assert!(text.contains(&store), "{text}");
    }
}

/// A function that only waits on a global is the empty `while` of its
/// test, entered with whatever the global holds.
///
/// `L: cmp byte [rip+G],0; je L; xor eax,eax; ret`, `G` a byte of a
/// writable `.data`, is `while (!ready);`. The loop is the entry, so its
/// back edge's `G == 0` is no fact on the way in: taken as one, the text
/// read `while (1) { }`, never returned and never read `G`.
#[test]
fn a_wait_on_a_global_at_the_entry_is_an_empty_while() {
    let mut bytes = vec![0u8; 0x2000];
    bytes[..12].copy_from_slice(&[
        0x80, 0x3d, 0xf9, 0x0f, 0x00, 0x00, 0x00, // ASM: cmp byte [rip+0xff9],0
        0x74, 0xf7, // ASM: je 0x0
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(F),
        vec![
            Section::mapped(".text", F, 0, 0x1000, false, true),
            Section::mapped(".data", F + 0x1000, 0x1000, 0x1000, true, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, F);
    assert!(
        text.contains("\n// effects: reads g8_140002000\n"),
        "{text}"
    );
    assert!(
        text.contains("\nwhile (g8_140002000 == 0);\nreturn 0;\n"),
        "{text}"
    );
    replays_clean(&p, &Analysis::compute(&p), &[F]);
}

/// An arm64 compare of a `w` register says nothing of the upper half of
/// its `x` register.
///
/// `cbz w0,L; .. L: str x0,[x1]` and `cmp w0,#5; b.ne X; str x0,[x1]` store
/// `x0` whole: read as a fact of the whole register, each compare made the
/// store its constant at 64 bits.
#[test]
fn an_arm_compare_of_a_registers_low_half_says_nothing_of_the_rest() {
    let zero: [u32; 6] = [
        0x3400_0060, // ASM: cbz w0, 0x40100c
        0x5280_0020, // ASM: mov w0, #1
        0xd65f_03c0, // ASM: ret
        0xf900_0020, // ASM: str x0, [x1]
        0x5280_0000, // ASM: mov w0, #0
        0xd65f_03c0, // ASM: ret
    ];
    let five: [u32; 7] = [
        0x7100_141f, // ASM: cmp w0, #5
        0x5400_0081, // ASM: b.ne 0x401014
        0xf900_0020, // ASM: str x0, [x1]
        0x5280_0000, // ASM: mov w0, #0
        0xd65f_03c0, // ASM: ret
        0x5280_0020, // ASM: mov w0, #1
        0xd65f_03c0, // ASM: ret
    ];
    for words in [&zero[..], &five] {
        let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
        let text = decompiled(&crate::raw::image(Arch::Arm64, &code, &[]), 0x40_1000);
        assert!(text.contains("*(uint64_t*)a2 = a1;\n"), "{text}");
    }
}
