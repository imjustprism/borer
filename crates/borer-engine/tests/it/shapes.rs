//! Control-flow shapes written as a source spells them.
//!
//! A jump table's bound check is the `switch`'s `default`, an endless
//! loop's way out follows the loop, and a loop that only computes its own
//! test is the empty `while (test);`.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::traces::{Structure, check_structure};
use borer_engine::analysis::{Analysis, Overlay};

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
