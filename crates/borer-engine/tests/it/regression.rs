//! Recorded regressions: bytes lifted from a real binary that once produced
//! malformed pseudo-C, kept as fixed inputs so the defect cannot return.
//!
//! Unlike the synthetic graphs in `structure.rs`, these are exact machine code
//! captured from the field. A block-shape a random graph almost never lands on
//! is trivial to keep once it has been seen once.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::gotos;

use borer_engine::analysis::{
    Analysis, Overlay,
    decompile::{decompile, decompile_raw},
};
use borer_engine::num::saturating_usize;
use borer_engine::program::{Arch, Program, Section};
use gotos::dangling_gotos;

/// Where the recorded code is placed; the bytes are position-independent
/// (relative jumps and rip-relative loads), so any base decodes the same
/// control flow.
const BASE: u64 = 0x1000;

/// Builds a flat executable image holding `code` at [`BASE`].
///
/// The image spans a megabyte so a rip-relative load that reaches outside the
/// captured slice resolves to a mapped-but-empty address and renders as a
/// pointer rather than panicking.
///
/// # Arguments
///
/// * `code` - The recorded machine code.
fn raw_program(code: &[u8]) -> Program {
    let mut bytes = vec![0xccu8; saturating_usize(BASE)];
    bytes.extend_from_slice(code);
    bytes.resize(0x100000, 0);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(BASE),
        vec![Section::mapped(".text", 0, 0, 0x100000, false, true)],
    )
}

/// The inner loop of a `core::fmt`/demangle routine: a `while` whose only
/// non-looping exits are a `return`, a returning one-way tail reached from
/// three sites, and a noreturn panic call ending in `ud2`.
///
/// The loop absorbed the panic exit and, because its text ends on the call
/// rather than a `return`, wrongly gained a `break;` to the loop's join. The
/// join was the returning tail, which a nested `if`/`else` had already folded
/// in as a shared dup (so no label was ever written for it), and the phantom
/// break made the loop emit a trailing `goto` to that never-labelled block.
/// The fix withholds that `break;` unless the absorbed region actually reaches
/// the join.
const DEMANGLE_LOOP: &[u8] = &[
    0x48, 0x89, 0xf1, 0xe8, 0x45, 0x05, 0x00, 0x00, 0x3d, 0x01, 0x00, 0x11, 0x00, 0x0f, 0x84, 0xf1,
    0x00, 0x00, 0x00, 0x83, 0xf8, 0x27, 0x74, 0x4a, 0x3d, 0x00, 0x00, 0x11, 0x00, 0x0f, 0x84, 0x02,
    0x01, 0x00, 0x00, 0x48, 0x89, 0xf9, 0x89, 0xc2, 0xe8, 0x00, 0x09, 0x00, 0x00, 0x44, 0x0f, 0xb6,
    0x7c, 0x24, 0x45, 0x0f, 0xb6, 0x6c, 0x24, 0x44, 0x49, 0x81, 0xff, 0x81, 0x00, 0x00, 0x00, 0x72,
    0x36, 0x8b, 0x5c, 0x24, 0x38, 0x40, 0xfe, 0xcd, 0x40, 0xfe, 0xc5, 0x44, 0x38, 0xfd, 0x73, 0xb0,
    0x49, 0x8b, 0x0e, 0x49, 0x8b, 0x46, 0x08, 0x89, 0xda, 0xff, 0x50, 0x20, 0x84, 0xc0, 0x74, 0xe8,
    0xeb, 0x34, 0x49, 0x8b, 0x0e, 0x49, 0x8b, 0x46, 0x08, 0xba, 0x27, 0x00, 0x00, 0x00, 0xff, 0x50,
    0x20, 0x84, 0xc0, 0x74, 0x8b, 0xeb, 0x1f, 0x40, 0x0f, 0xb6, 0xdd, 0x4c, 0x39, 0xfb, 0x73, 0x80,
    0x0f, 0xb6, 0x54, 0x1c, 0x38, 0x48, 0xff, 0xc3, 0x49, 0x8b, 0x0e, 0x49, 0x8b, 0x46, 0x08, 0xff,
    0x50, 0x20, 0x84, 0xc0, 0x74, 0xe5, 0xb0, 0x01, 0xeb, 0x5b, 0x48, 0x8b, 0x4e, 0x20, 0x48, 0x85,
    0xc9, 0x74, 0x1a, 0x48, 0x8d, 0x15, 0xc3, 0x51, 0x0a, 0x00, 0x41, 0xb8, 0x10, 0x00, 0x00, 0x00,
    0xe8, 0x18, 0xfe, 0xf0, 0xff, 0x89, 0xc1, 0xb0, 0x01, 0x84, 0xc9, 0x75, 0x38, 0x48, 0xc7, 0x06,
    0x00, 0x00, 0x00, 0x00, 0xc6, 0x46, 0x08, 0x00, 0xeb, 0x29, 0x48, 0x8b, 0x4e, 0x20, 0x48, 0x85,
    0xc9, 0x74, 0x20, 0x48, 0x8d, 0x15, 0xbc, 0x51, 0x0a, 0x00, 0x41, 0xb8, 0x01, 0x00, 0x00, 0x00,
    0x48, 0x83, 0xc4, 0x70, 0x5b, 0x5d, 0x5f, 0x5e, 0x41, 0x5c, 0x41, 0x5e, 0x41, 0x5f, 0xe9, 0xda,
    0xfd, 0xf0, 0xff, 0x31, 0xc0, 0x48, 0x83, 0xc4, 0x70, 0x5b, 0x5d, 0x5f, 0x5e, 0x41, 0x5c, 0x41,
    0x5e, 0x41, 0x5f, 0xc3, 0x49, 0x8b, 0x0e, 0x49, 0x8b, 0x46, 0x08, 0x48, 0x8b, 0x40, 0x20, 0xba,
    0x22, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x70, 0x5b, 0x5d, 0x5f, 0x5e, 0x41, 0x5c, 0x41, 0x5e,
    0x41, 0x5f, 0x48, 0xff, 0xe0, 0x48, 0x8d, 0x05, 0x99, 0x4e, 0x0a, 0x00, 0x48, 0x89, 0x44, 0x24,
    0x20, 0x48, 0x8d, 0x0d, 0x95, 0xe0, 0x0a, 0x00, 0x4c, 0x8d, 0x0d, 0x46, 0x4f, 0x0a, 0x00, 0x4c,
    0x8d, 0x44, 0x24, 0x37, 0xba, 0x2b, 0x00, 0x00, 0x00, 0xe8, 0x2f, 0x18, 0x05, 0x00, 0x0f, 0x0b,
    0x48, 0x8d, 0x05, 0x66, 0x4b, 0x0a, 0x00, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x89, 0xf9, 0xe8,
    0x39, 0x17, 0x05, 0x00, 0x0f, 0x0b,
];

/// A loop that absorbs a noreturn exit still leaves every `goto` with a label.
#[test]
fn noreturn_loop_exit_leaves_no_dangling_goto() {
    let p = raw_program(DEMANGLE_LOOP);
    let a = Analysis::compute(&p);
    let text = decompile_raw(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        dangling_gotos(&text).is_empty(),
        "dangling gotos {:?}:\n{text}",
        dangling_gotos(&text)
    );
}

/// A conditional branch into a known function is a conditional tail call, not a
/// jump into that function's body.
///
/// `d3d11.dll!sub_18013eaf0` was `test; jne f; jmp f` where `f` is a real
/// function reached from 133 sites. Only the unconditional `jmp` got the
/// tail-call test, so the `jne` absorbed `f`'s `ret` as a block of the caller;
/// the whole call then collapsed to a bare `return;` and `f` vanished from the
/// text. Here `A` (entry) does `test dl,dl; jne B; call C; ret`, `C` calls `B`
/// so `B` is a discovered function, and `A`'s decompilation must still name
/// `B` — the conditional edge to it is a call, not a swallowed block.
#[test]
fn conditional_branch_into_a_function_is_a_tail_call() {
    // A @ 0x1000: test dl,dl; jne 0x1040(B); call 0x1060(C); ret
    // B @ 0x1040: mov eax, 7; ret
    // C @ 0x1060: call 0x1040(B); ret
    let mut code = vec![0xccu8; 0x66];
    code[0x00..0x0e].copy_from_slice(&[
        0x84, 0xd2, // test dl, dl
        0x0f, 0x85, 0x38, 0x00, 0x00, 0x00, // jne 0x1040
        0xe8, 0x53, 0x00, 0x00, 0x00, // call 0x1060
        0xc3, // ret
    ]);
    code[0x40..0x46].copy_from_slice(&[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]); // mov eax,7; ret
    code[0x60..0x66].copy_from_slice(&[0xe8, 0xdb, 0xff, 0xff, 0xff, 0xc3]); // call 0x1040; ret
    let p = raw_program(&code);
    let a = Analysis::compute(&p);
    let text = decompile_raw(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        text.contains("sub_1040") || text.contains("0x1040"),
        "the conditional tail call to B was dropped:\n{text}"
    );
    assert!(
        !text.contains("L_1040:"),
        "B was absorbed as a block of A instead of staying a callee:\n{text}"
    );
}

/// Migrating a function's offsets across two builds finds a moved field.
///
/// The same function reads two 32-bit fields off its first argument; in the
/// "new" build the second field's displacement moved from `0x20` to `0x28`. The
/// two functions match by shape (only a displacement byte differs), so the
/// migration must report `0x10` unchanged and `0x20` moved to `0x28`, which a
/// byte search for the old displacement could never say.
#[test]
fn migrate_reports_a_field_that_moved_between_builds() {
    use borer_engine::analysis::render::migrate_function_tsv;
    // mov eax,[rcx+0x10]; add eax,[rcx+OFF]; ret
    let build = |off: u8| {
        let mut code = vec![0xccu8; 8];
        code[..7].copy_from_slice(&[0x8b, 0x41, 0x10, 0x03, 0x41, off, 0xc3]);
        raw_program(&code)
    };
    let old = build(0x20);
    let new = build(0x28);
    let (oa, na) = (Analysis::compute(&old), Analysis::compute(&new));
    let o = Overlay::default();
    let out = migrate_function_tsv(&old, &oa, &o, &new, &na, &o, "0x1000", "old", "new")
        .expect("0x1000 is a baseline function");
    assert!(
        out.contains("0x10\tr/4\tr/4\tsame"),
        "the unmoved field was not reported same:\n{out}"
    );
    assert!(
        out.contains("0x20\tr/4\t-\tmoved -> 0x28"),
        "the moved field was not tracked:\n{out}"
    );
    assert!(
        out.contains("0x28\t-\tr/4\tmoved <- 0x20"),
        "the destination was not tracked:\n{out}"
    );
}

/// A per-function comparison refuses an unknown function and uses set names.
///
/// Its header names each side as its own names do, the user's first, and
/// says how the two were paired once. It answered `# no function` as a
/// success, named the baseline by the analysis over the user's name, and
/// read `[matched by by name]`.
#[test]
fn per_function_comparisons_refuse_an_unknown_function_and_use_set_names() {
    use borer_engine::analysis::render::{diff_function_tsv, migrate_function_tsv};
    let build = |off: u8| {
        let mut code = vec![0xccu8; 8];
        code[..7].copy_from_slice(&[0x8b, 0x41, 0x10, 0x03, 0x41, off, 0xc3]);
        raw_program(&code)
    };
    let old = build(0x20);
    let new = build(0x28);
    let (oa, na) = (Analysis::compute(&old), Analysis::compute(&new));
    let plain = Overlay::default();
    for render in [diff_function_tsv, migrate_function_tsv] {
        assert_eq!(
            render(&old, &oa, &plain, &new, &na, &plain, "nosuch", "old", "new"),
            Err("no function nosuch in old".to_owned())
        );
    }
    let mut named = Overlay::default();
    named.names.insert(0x1000, "Player::Update".to_owned());
    for render in [diff_function_tsv, migrate_function_tsv] {
        let out = render(&old, &oa, &named, &new, &na, &plain, "0x1004", "old", "new")
            .expect("an interior address names its function");
        let header = out.lines().next().unwrap_or_default();
        assert!(
            header.contains(" Player::Update (old) ") && header.contains(" sub_1000 (new) "),
            "{out}"
        );
        assert!(!header.contains("matched by"), "{out}");
    }
}

/// Overwritten `/homeparams` spills and local escapes stay scoped to their
/// frames.
///
/// An overwritten shadow slot neither triggers variadic (`...`) nor emits a
/// dead `home_* = aN` store, a local escape below the return address does not
/// expose caller-frame `home_*` slots across calls, and a callee-skipped
/// register slot does not report `// !unset:`.
#[test]
fn overwritten_shadow_home_and_local_escape_stay_clean() {
    let mut code = vec![0xccu8; 0x50];
    code[0x00..0x2f].copy_from_slice(&[
        0x48, 0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8], rcx
        0x4c, 0x89, 0x44, 0x24, 0x18, // ASM: mov [rsp+18h], r8
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x30, // ASM: sub rsp, 30h
        0x48, 0x89, 0xcb, // ASM: mov rbx, rcx
        0x83, 0x64, 0x24, 0x50, 0x00, // ASM: and dword ptr [rsp+50h], 0
        0x48, 0x8d, 0x4c, 0x24, 0x20, // ASM: lea rcx, [rsp+20h]
        0x4c, 0x8d, 0x44, 0x24, 0x50, // ASM: lea r8, [rsp+50h]
        0xe8, 0x1a, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x01, 0xd8, // ASM: add rax, rbx
        0x48, 0x83, 0xc4, 0x30, // ASM: add rsp, 30h
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ]);
    code[0x40..0x47].copy_from_slice(&[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0x49, 0x03, 0x00, // ASM: add rax, [r8]
        0xc3, // ASM: ret
    ]);
    let mut p = raw_program(&code);
    p.function_ranges = vec![(0x1000, 0x102f), (0x1040, 0x1047)];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        !text.contains("..."),
        "overwritten home slot falsely marked function variadic:\n{text}"
    );
    assert!(
        !text.contains("home_0"),
        "local escape below return address exposed caller-frame home_0:\n{text}"
    );
    assert!(
        !text.contains("!unset"),
        "callee-skipped register slot triggered false !unset warning:\n{text}"
    );
}

/// A 64-bit call with a fifth argument on the stack bridges unset `r8` and
/// `r9` register slots instead of dropping the outgoing stack argument.
#[test]
fn sixty_four_bit_call_bridges_clobbered_registers_to_reach_stack_argument() {
    let mut code = vec![0xccu8; 0x50];
    code[0x00..0x18].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x38, // ASM: sub rsp, 38h
        0x48, 0x8d, 0x44, 0x24, 0x28, // ASM: lea rax, [rsp+28h]
        0x48, 0x89, 0x44, 0x24, 0x20, // ASM: mov [rsp+20h], rax
        0xe8, 0x2d, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x38, // ASM: add rsp, 38h
        0xc3, // ASM: ret
    ]);
    code[0x40..0x4c].copy_from_slice(&[
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x48, 0x01, 0xd0, // ASM: add rax, rdx
        0x48, 0x03, 0x44, 0x24, 0x28, // ASM: add rax, [rsp+28h]
        0xc3, // ASM: ret
    ]);
    let mut p = raw_program(&code);
    p.function_ranges = vec![(0x1000, 0x1018), (0x1040, 0x104c)];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        !text.contains("call args dropped"),
        "stack argument after unset register slots was dropped:\n{text}"
    );
    assert!(
        text.contains("&local_10)"),
        "fifth stack argument was not rendered in the call:\n{text}"
    );
}

/// An 8-byte `movsd` block copy of UTF-16LE characters from read-only memory
/// renders as an integer store rather than a subnormal `double` literal.
#[test]
fn movsd_from_utf16_rodata_renders_integer_instead_of_subnormal_double() {
    let mut bytes = vec![0xccu8; 0x3000];
    bytes[0x1000..0x1021].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0xf2, 0x0f, 0x10, 0x05, 0xf4, 0x0f, 0x00, 0x00, // ASM: movsd xmm0, [rip+0ff4h]
        0xf2, 0x0f, 0x11, 0x44, 0x24, 0x10, // ASM: movsd [rsp+10h], xmm0
        0x48, 0x8d, 0x4c, 0x24, 0x10, // ASM: lea rcx, [rsp+10h]
        0xe8, 0x24, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ]);
    bytes[0x1040..0x1044].copy_from_slice(&[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0xc3, // ASM: ret
    ]);
    bytes[0x2000..0x2008].copy_from_slice(b"u\0s\0e\0r\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(BASE),
        vec![
            Section::mapped(".text", 0, 0, 0x2000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.function_ranges = vec![(0x1000, 0x1021), (0x1040, 0x1044)];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        !text.contains("double") && !text.contains("p-1016"),
        "UTF-16LE block copy rendered as subnormal double:\n{text}"
    );
    assert!(
        text.contains("0x72006500730075") && text.contains("/* L\"user\" */"),
        "UTF-16LE block copy did not preserve 64-bit integer bits and string note:\n{text}"
    );
}

/// Non-escaping stack slots drop dead stores, fold single-use spills, and
/// split reused slots across independent value webs.
#[test]
fn non_escaping_stack_slots_drop_dead_stores_and_fold_spills() {
    let mut code = vec![0xccu8; 0x60];
    code[0x00..0x3a].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0x48, 0xc7, 0x44, 0x24, 0x18, 0x77, 0x00, 0x00,
        0x00, // ASM: mov qword ptr [rsp+18h], 77h
        0xe8, 0x2e, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x89, 0x44, 0x24, 0x10, // ASM: mov [rsp+10h], rax
        0x48, 0x8b, 0x4c, 0x24, 0x10, // ASM: mov rcx, [rsp+10h]
        0xe8, 0x27, 0x00, 0x00, 0x00, // ASM: call 0x1048
        0x48, 0x89, 0x44, 0x24, 0x10, // ASM: mov [rsp+10h], rax
        0x48, 0x8b, 0x4c, 0x24, 0x10, // ASM: mov rcx, [rsp+10h]
        0x48, 0x8b, 0x54, 0x24, 0x10, // ASM: mov rdx, [rsp+10h]
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x1050
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ]);
    code[0x40..0x46].copy_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    code[0x48..0x4d].copy_from_slice(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xc3, // ASM: ret
    ]);
    code[0x50..0x55].copy_from_slice(&[
        0x48, 0x8d, 0x04, 0x11, // ASM: lea rax, [rcx+rdx]
        0xc3, // ASM: ret
    ]);
    let mut p = raw_program(&code);
    p.function_ranges = vec![
        (0x1000, 0x103a),
        (0x1040, 0x1046),
        (0x1048, 0x104d),
        (0x1050, 0x1055),
    ];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        !text.contains("0x77"),
        "dead stack slot store was not eliminated:\n{text}"
    );
    assert!(
        text.contains("sub_1048(sub_1040())"),
        "single-use stack spill did not fold into its call:\n{text}"
    );
}

/// A struct pointer stepped by a constant stride in a loop still receives
/// its `// layout` header and `->field_0xN` projections.
#[test]
fn loop_strided_pointer_projects_struct_fields() {
    let code: &[u8] = &[
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x48, 0x39, 0xd0, // ASM: cmp rax, rdx
        0x74, 0x10, // ASM: je 0x101a
        0x03, 0x48, 0x04, // ASM: add ecx, [rax+4]
        0x48, 0x03, 0x48, 0x08, // ASM: add rcx, [rax+8]
        0x03, 0x48, 0x10, // ASM: add ecx, [rax+10h]
        0x48, 0x83, 0xc0, 0x18, // ASM: add rax, 18h
        0xeb, 0xeb, // ASM: jmp 0x1005
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx (0x101a)
        0xc3, // ASM: ret
    ];
    let p = raw_program(code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        text.contains("// layout ") && text.contains("->field_0x4"),
        "loop-strided pointer did not project struct fields:\n{text}"
    );
}

/// A callee that skips `rcx` renders `0` for the unused slot, and read-only
/// `g32_` string globals are annotated with their decoded wide string literal.
#[test]
fn skipped_callee_slot_and_rodata_global_string_annotations() {
    let mut bytes = vec![0xccu8; 0x100];
    bytes[0x00..0x2c].copy_from_slice(&[
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 20h
        0x48, 0x89, 0xd3, // ASM: mov rbx, rdx
        0x8b, 0x05, 0x72, 0x00, 0x00, 0x00, // ASM: mov eax, [rip+0x72] (0x1080)
        0x89, 0x44, 0x24, 0x18, // ASM: mov [rsp+18h], eax
        0x48, 0x8b, 0x09, // ASM: mov rcx, [rcx]
        0xe8, 0x26, 0x00, 0x00, 0x00, // ASM: call 0x1040
        0x48, 0x89, 0xda, // ASM: mov rdx, rbx
        0xe8, 0x26, 0x00, 0x00, 0x00, // ASM: call 0x1048
        0x8b, 0x44, 0x24, 0x18, // ASM: mov eax, [rsp+18h]
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 20h
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ]);
    bytes[0x40..0x45].copy_from_slice(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xc3, // ASM: ret
    ]);
    bytes[0x48..0x4d].copy_from_slice(&[
        0x48, 0x8d, 0x42, 0x02, // ASM: lea rax, [rdx+2]
        0xc3, // ASM: ret
    ]);
    bytes[0x80..0x86].copy_from_slice(&[b'n', 0, b'o', 0, 0, 0]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        BASE,
        Some(BASE),
        vec![
            Section::mapped(".text", BASE, 0, 0x80, false, true),
            Section::mapped(".rdata", BASE + 0x80, 0x80, 0x80, false, false),
        ],
    );
    p.function_ranges = vec![(0x1000, 0x102c), (0x1040, 0x1045), (0x1048, 0x104d)];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        text.contains("sub_1048(0, a2)"),
        "skipped rcx slot did not render 0:\n{text}"
    );
    assert!(
        text.contains("/* L\"no\" */"),
        "read-only g32 string global was not annotated:\n{text}"
    );
}

/// An out-parameter stack slot (`&home_8`) splits its later disjoint value web.
#[test]
fn out_param_home_slot_splits_disjoint_value_web() {
    let mut bytes = vec![0xccu8; 0x100];
    bytes[0x00..0x38].copy_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0xc7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+30h], 0
        0x48, 0x8d, 0x4c, 0x24, 0x30, // ASM: lea rcx, [rsp+30h] (&home_8)
        0xe8, 0x3a, 0x00, 0x00, 0x00, // ASM: call 0x1050
        0x8b, 0x4c, 0x24, 0x30, // ASM: mov ecx, [rsp+30h]
        0xe8, 0x39, 0x00, 0x00, 0x00, // ASM: call 0x1058
        0x48, 0x89, 0x44, 0x24, 0x30, // ASM: mov [rsp+30h], rax
        0x48, 0x8b, 0x4c, 0x24, 0x30, // ASM: mov rcx, [rsp+30h]
        0x48, 0x8b, 0x54, 0x24, 0x30, // ASM: mov rdx, [rsp+30h]
        0xe8, 0x2d, 0x00, 0x00, 0x00, // ASM: call 0x1060
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ]);
    bytes[0x50..0x57].copy_from_slice(&[
        0xc7, 0x01, 0x07, 0x00, 0x00, 0x00, // ASM: mov dword [rcx], 7
        0xc3, // ASM: ret
    ]);
    bytes[0x58..0x5d].copy_from_slice(&[
        0x48, 0x8d, 0x41, 0x10, // ASM: lea rax, [rcx+10h]
        0xc3, // ASM: ret
    ]);
    bytes[0x60..0x65].copy_from_slice(&[
        0x48, 0x8d, 0x04, 0x11, // ASM: lea rax, [rcx+rdx]
        0xc3, // ASM: ret
    ]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        BASE,
        Some(BASE),
        vec![Section::mapped(".text", BASE, 0, 0x100, false, true)],
    );
    p.function_ranges = vec![
        (0x1000, 0x1038),
        (0x1050, 0x1057),
        (0x1058, 0x105d),
        (0x1060, 0x1065),
    ];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        text.contains("sub_1050(&home_0)"),
        "out-parameter web did not keep &home_0:\n{text}"
    );
    assert!(
        text.contains("sub_1060(var1, var1)") && !text.contains("sub_1060(home_0"),
        "disjoint value web on home_0 did not split into an independent variable:\n{text}"
    );
}

/// Multi-piece stack strings, `&local_X` string pointer provenance, and
/// repeating stack struct-arrays receive structured header and inline comments.
#[test]
fn stack_string_coalescing_and_stack_array_annotations() {
    let mut bytes = vec![0xccu8; 0x100];
    bytes[0x00..0x6d].copy_from_slice(&[
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x48, 0x81, 0xec, 0x80, 0x00, 0x00, 0x00, // ASM: sub rsp, 80h
        // Multi-piece wide string L"user" at [rbp-10h]..[rbp-8h] (local_18, local_10)
        0x48, 0xb8, 0x75, 0x00, 0x73, 0x00, 0x65, 0x00, 0x72,
        0x00, // ASM: movabs rax, 0x0072_0065_0073_0075
        0x48, 0x89, 0x45, 0xf0, // ASM: mov [rbp-10h], rax
        0x66, 0xc7, 0x45, 0xf8, 0x00, 0x00, // ASM: mov word [rbp-8h], 0
        // 3-element struct array at [rbp-70h..-28h], stride 0x18 (24 bytes):
        // element 0: [rbp-70h], [rbp-68h], [rbp-60h]
        0x48, 0xc7, 0x45, 0x90, 0x01, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-70h], 1
        0x48, 0x8d, 0x45, 0xf0, // ASM: lea rax, [rbp-10h]
        0x48, 0x89, 0x45, 0x98, // ASM: mov [rbp-68h], rax
        0x48, 0xc7, 0x45, 0xa0, 0x10, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-60h], 10h
        // element 1: [rbp-58h], [rbp-50h], [rbp-48h]
        0x48, 0xc7, 0x45, 0xa8, 0x02, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-58h], 2
        0x48, 0x89, 0x45, 0xb0, // ASM: mov [rbp-50h], rax
        0x48, 0xc7, 0x45, 0xb8, 0x20, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-48h], 20h
        // element 2: [rbp-40h], [rbp-38h], [rbp-30h]
        0x48, 0xc7, 0x45, 0xc0, 0x03, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-40h], 3
        0x48, 0x89, 0x45, 0xc8, // ASM: mov [rbp-38h], rax
        0x48, 0xc7, 0x45, 0xd0, 0x30, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-30h], 30h
        // Pass &local_78 ([rbp-70h]) to sub_1080
        0x48, 0x8d, 0x4d, 0x90, // ASM: lea rcx, [rbp-70h]
        0xe8, 0x18, 0x00, 0x00, 0x00, // ASM: call 0x1080
        0x48, 0x89, 0xec, // ASM: mov rsp, rbp
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ]);
    bytes[0x80..0x84].copy_from_slice(&[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0xc3, // ASM: ret
    ]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        BASE,
        Some(BASE),
        vec![Section::mapped(".text", BASE, 0, 0x100, false, true)],
    );
    p.function_ranges = vec![(0x1000, 0x106d), (0x1080, 0x1084)];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), BASE).expect("decompile");
    assert!(
        text.contains("// stack array local_78[3] (stride 0x18)"),
        "stack struct-array header was not emitted:\n{text}"
    );
    assert!(
        text.contains("local_78[0].field_0x8 = L\"user\""),
        "stack array field + wide string provenance annotation was not emitted:\n{text}"
    );
}
