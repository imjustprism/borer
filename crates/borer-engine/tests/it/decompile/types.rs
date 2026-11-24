//! Parameter and local types that need a witness: a narrow type is printed
//! only when the code shows that width, and a wide fact vetoes it.

use super::{
    Analysis, Overlay, decompile, decompile_scenario, polish, program64, replays_clean, runs_agree,
};
use borer_engine::pack::Packs;
use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};

/// The entry every x64 image here is decompiled at.
const ENTRY: u64 = 0x1_4000_1000;

/// The entry of the raw arm64 and A32 images ([`crate::raw::image`]).
const RAW_ENTRY: u64 = 0x40_1000;

/// Returns a System V image of `code` at [`ENTRY`].
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
fn sysv(code: &[u8]) -> Program {
    let mut p = program64(code);
    p.format = BinaryFormat::Elf;
    p
}

/// Decompiles a function and replays its lift on the machine.
///
/// # Arguments
///
/// * `p` - The image.
/// * `entry` - The function.
///
/// # Returns
///
/// The text, empty when it does not decompile.
fn checked_at(p: &Program, entry: u64) -> String {
    let a = Analysis::compute(p);
    let text = decompile(p, &a, &Overlay::default(), entry).unwrap_or_default();
    replays_clean(p, &a, &[entry]);
    text
}

/// [`checked_at`] for a System V x64 function at [`ENTRY`].
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn checked(code: &[u8]) -> String {
    checked_at(&sysv(code), ENTRY)
}

/// [`checked_at`] for a raw image of 32-bit words at [`RAW_ENTRY`].
///
/// # Arguments
///
/// * `arch` - [`Arch::Arm64`] or [`Arch::Arm`].
/// * `words` - The instructions.
fn checked_words(arch: Arch, words: &[u32]) -> String {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    checked_at(&crate::raw::image(arch, &code, &[]), RAW_ENTRY)
}

/// An unoptimized prologue spilling `rdi` and then `rsi` (`spill` bytes)
/// to the frame, and a body storing the low half of the second to a field
/// of the first.
///
/// # Arguments
///
/// * `spill` - The bytes of the `rsi` spill and its reload.
fn spilled_store(spill: &[u8]) -> Vec<u8> {
    let mut code = vec![
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x48, 0x89, 0x7d, 0xf8, // ASM: mov [rbp-0x8], rdi
    ];
    code.extend_from_slice(spill);
    code.extend_from_slice(&[
        0x48, 0x8b, 0x55, 0xf8, // ASM: mov rdx, [rbp-0x8]
        0x89, 0x42, 0x04, // ASM: mov [rdx+0x4], eax
        0x90, // ASM: nop
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ]);
    code
}

/// An eight-byte home spill keeps a parameter 64 bits wide.
///
/// The spill reads the whole register, so storing only its low half to a
/// field does not make it a `uint32_t`: the header keeps the word, the
/// 32-bit store is what truncates it, and the final text runs as the
/// binary does.
#[test]
fn an_eight_byte_home_spill_keeps_the_parameter_wide() {
    let code = spilled_store(&[
        0x48, 0x89, 0x75, 0xf0, // ASM: mov [rbp-0x10], rsi
        0x48, 0x8b, 0x45, 0xf0, // ASM: mov rax, [rbp-0x10]
    ]);
    let text = checked(&code);
    assert!(text.contains("uint64_t a2"), "{text}");
    assert!(text.contains("*(uint32_t*)(a1 + 4) = a2;"), "{text}");
    runs_agree(&sysv(&code), ENTRY);
}

/// A four-byte home spill is the narrow witness: the parameter was 32 bits.
#[test]
fn a_four_byte_home_spill_keeps_the_parameter_narrow() {
    let code = spilled_store(&[
        0x89, 0x75, 0xf4, // ASM: mov [rbp-0xc], esi
        0x8b, 0x45, 0xf4, // ASM: mov eax, [rbp-0xc]
    ]);
    let text = checked(&code);
    assert!(text.contains("uint32_t a2"), "{text}");
    runs_agree(&sysv(&code), ENTRY);
}

/// A prologue homing every argument register as a word shows nothing of
/// any one's width: the store's narrow type stands.
#[test]
fn a_prologue_homing_every_register_is_no_wide_witness() {
    let code = [
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x48, 0x89, 0x7d, 0xf8, // ASM: mov [rbp-0x8], rdi
        0x48, 0x89, 0x75, 0xf0, // ASM: mov [rbp-0x10], rsi
        0x48, 0x89, 0x55, 0xe8, // ASM: mov [rbp-0x18], rdx
        0x48, 0x89, 0x4d, 0xe0, // ASM: mov [rbp-0x20], rcx
        0x4c, 0x89, 0x45, 0xd8, // ASM: mov [rbp-0x28], r8
        0x4c, 0x89, 0x4d, 0xd0, // ASM: mov [rbp-0x30], r9
        0x48, 0x8b, 0x45, 0xf0, // ASM: mov rax, [rbp-0x10]
        0x48, 0x8b, 0x55, 0xf8, // ASM: mov rdx, [rbp-0x8]
        0x89, 0x42, 0x04, // ASM: mov [rdx+0x4], eax
        0x31, 0xc0, // ASM: xor eax, eax
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    let text = checked(&code);
    assert!(text.contains("uint32_t a2"), "{text}");
    runs_agree(&sysv(&code), ENTRY);
}

/// A narrow store with no wide witness keeps the narrow type.
///
/// Nothing shows the upper half of a parameter only ever stored at 32 bits.
#[test]
fn a_narrow_store_with_no_wide_witness_stays_narrow() {
    let code = [
        0x89, 0x77, 0x04, // ASM: mov [rdi+0x4], esi
        0xc3, // ASM: ret
    ];
    let text = checked(&code);
    assert!(text.contains("uint32_t a2"), "{text}");
    runs_agree(&sysv(&code), ENTRY);
}

/// Bytes at several constant offsets are fields, so the pointer is `void *`.
#[test]
fn bytes_at_constant_offsets_make_no_byte_pointer() {
    let text = checked(&[
        0x0f, 0xb6, 0x07, // ASM: movzx eax, byte [rdi]
        0x0f, 0xb6, 0x57, 0x01, // ASM: movzx edx, byte [rdi+0x1]
        0x01, 0xd0, // ASM: add eax, edx
        0x0f, 0xb6, 0x57, 0x04, // ASM: movzx edx, byte [rdi+0x4]
        0x01, 0xd0, // ASM: add eax, edx
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("void *a1"), "{text}");
    assert!(!text.contains("uint8_t *a1"), "{text}");
}

/// A computed index walks the pointer, so bytes read through it at two
/// offsets still make a byte pointer: only the walk decides.
#[test]
fn bytes_read_through_an_index_make_a_byte_pointer() {
    let text = checked(&[
        0x0f, 0xb6, 0x04, 0x37, // ASM: movzx eax, byte [rdi+rsi]
        0x0f, 0xb6, 0x57, 0x01, // ASM: movzx edx, byte [rdi+0x1]
        0x01, 0xd0, // ASM: add eax, edx
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("uint8_t *a1"), "{text}");
}

/// A copy of a parameter that is only read through holds the parameter:
/// its constant offsets are the parameter's fields.
#[test]
fn an_unstepped_copy_reads_fields() {
    let raw = concat!(
        "// signature: uint32_t f(uint64_t a1)\n",
        "uint64_t local_10;\n",
        "\n",
        "local_10 = a1;\n",
        "return *(uint8_t*)(local_10 + 4) + *(uint8_t*)(local_10 + 8);\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("void *a1"), "{out}");
    assert!(!out.contains("uint8_t *a1"), "{out}");
}

/// A copy stepped by itself walks the bytes: the parameter is a byte
/// pointer.
#[test]
fn a_stepped_copy_walks_bytes() {
    let raw = concat!(
        "// signature: uint64_t f(uint64_t a1)\n",
        "uint64_t local_10;\n",
        "\n",
        "local_10 = a1;\n",
        "while (*(uint8_t*)local_10 != 0) {\n",
        "  local_10 += 1;\n",
        "}\n",
        "return local_10;\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("uint8_t *a1"), "{out}");
}

/// arm64: bytes at constant offsets are fields; a register index or a
/// post-indexed load walks the bytes.
#[test]
fn arm64_byte_pointers_need_a_walk() {
    let fields = checked_words(
        Arch::Arm64,
        &[
            0x3940_0001, // ASM: ldrb w1, [x0]
            0x3940_0402, // ASM: ldrb w2, [x0, #1]
            0x3940_1003, // ASM: ldrb w3, [x0, #4]
            0x0b02_0020, // ASM: add w0, w1, w2
            0x0b03_0000, // ASM: add w0, w0, w3
            0xd65f_03c0, // ASM: ret
        ],
    );
    assert!(fields.contains("void *a1"), "{fields}");
    let indexed = checked_words(
        Arch::Arm64,
        &[
            0x3861_6803, // ASM: ldrb w3, [x0, x1]
            0x3940_0002, // ASM: ldrb w2, [x0]
            0x3940_0404, // ASM: ldrb w4, [x0, #1]
            0x0b03_0040, // ASM: add w0, w2, w3
            0x0b04_0000, // ASM: add w0, w0, w4
            0xd65f_03c0, // ASM: ret
        ],
    );
    assert!(indexed.contains("uint8_t *a1"), "{indexed}");
    let post = checked_words(
        Arch::Arm64,
        &[
            0x3940_0402, // ASM: ldrb w2, [x0, #1]
            0x3840_1401, // ASM: ldrb w1, [x0], #1
            0x0b02_0020, // ASM: add w0, w1, w2
            0xd65f_03c0, // ASM: ret
        ],
    );
    assert!(post.contains("uint8_t *a1"), "{post}");
}

/// A32: bytes at constant offsets are fields; a post-indexed load reads at
/// the base and walks; a register offset walks.
#[test]
fn a32_byte_pointers_need_a_walk() {
    let fields = checked_words(
        Arch::Arm,
        &[
            0xe5d0_1000, // ASM: ldrb r1, [r0]
            0xe5d0_2001, // ASM: ldrb r2, [r0, #1]
            0xe5d0_3004, // ASM: ldrb r3, [r0, #4]
            0xe081_0002, // ASM: add r0, r1, r2
            0xe080_0003, // ASM: add r0, r0, r3
            0xe12f_ff1e, // ASM: bx lr
        ],
    );
    assert!(fields.contains("void *a1"), "{fields}");
    let post = checked_words(
        Arch::Arm,
        &[
            0xe4d0_1001, // ASM: ldrb r1, [r0], #1
            0xe1a0_0001, // ASM: mov r0, r1
            0xe12f_ff1e, // ASM: bx lr
        ],
    );
    assert!(post.contains("uint8_t *a1"), "{post}");
    let walked = checked_words(
        Arch::Arm,
        &[
            0xe5d0_2001, // ASM: ldrb r2, [r0, #1]
            0xe4d0_1001, // ASM: ldrb r1, [r0], #1
            0xe081_0002, // ASM: add r0, r1, r2
            0xe12f_ff1e, // ASM: bx lr
        ],
    );
    assert!(walked.contains("uint8_t *a1"), "{walked}");
    let indexed = checked_words(
        Arch::Arm,
        &[
            0xe7d0_3001, // ASM: ldrb r3, [r0, r1]
            0xe5d0_2001, // ASM: ldrb r2, [r0, #1]
            0xe082_0003, // ASM: add r0, r2, r3
            0xe12f_ff1e, // ASM: bx lr
        ],
    );
    assert!(indexed.contains("uint8_t *a1"), "{indexed}");
}

/// A chain write shares its constant, not a type.
///
/// The slot `getenv` fills is a `char *`; the one zeroed with it is not.
#[test]
fn a_chain_write_shares_no_type() {
    let raw = concat!(
        "// signature: void f(void)\n",
        "uint64_t local_10;\n",
        "uint64_t local_8;\n",
        "\n",
        "local_10 = local_8 = 0;\n",
        "local_8 = getenv(\"HOME\");\n",
        "puts(local_8);\n",
        "sub_2000(local_10);\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("char* local_8;"), "{out}");
    assert!(!out.contains("char* local_10"), "{out}");
}

/// A copy of a located global the text declares `char *` types the slot;
/// one the text declares only by its width does not.
///
/// The type comes from the copy, not from the chain that zeroed it.
#[test]
fn a_copy_of_a_char_pointer_global_types_the_slot() {
    let raw = |declared: &str| {
        [
            "// signature: void f(void)",
            "uint64_t local_10;",
            "uint64_t local_8;",
            &format!("extern {declared}optarg; // @ 0x8040"),
            "",
            "local_10 = local_8 = 0;",
            "local_8 = optarg;",
            "sub_2000(local_8);",
            "sub_2000(local_10);",
        ]
        .join("\n")
    };
    let out = polish(&raw("char *"), 64, &Packs::default());
    assert!(out.contains("char* local_8;"), "{out}");
    assert!(!out.contains("char* local_10"), "{out}");
    let untyped = polish(&raw("uint64_t "), 64, &Packs::default());
    assert!(!untyped.contains("char* local_8"), "{untyped}");
}

/// A scenario's text keeps the wide parameter the plain decompile keeps:
/// it is polished from the same decompilation, machine facts included.
#[test]
fn a_scenario_keeps_the_wide_parameter() {
    let p = sysv(&spilled_store(&[
        0x48, 0x89, 0x75, 0xf0, // ASM: mov [rbp-0x10], rsi
        0x48, 0x8b, 0x45, 0xf0, // ASM: mov rax, [rbp-0x10]
    ]));
    let a = Analysis::compute(&p);
    let text = decompile_scenario(&p, &a, &Overlay::default(), ENTRY, &[]).unwrap_or_default();
    assert!(text.contains("uint64_t a2"), "{text}");
}

/// A declared `void *` read through an unstepped copy at two byte offsets
/// points at fields: it stays `void *`.
#[test]
fn a_void_pointer_read_through_an_unstepped_copy_stays_void() {
    let raw = concat!(
        "// signature: uint32_t f(void *a1)\n",
        "uint64_t local_10;\n",
        "\n",
        "local_10 = a1;\n",
        "return *(uint8_t*)(local_10 + 4) + *(uint8_t*)(local_10 + 8);\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("void *a1"), "{out}");
    assert!(!out.contains("uint8_t *a1"), "{out}");
}

/// A copy stepped by its load's width walks elements of that width; one
/// stepped by another amount, or read only away from where it points,
/// shows no element: `void *`.
#[test]
fn a_stepped_copy_names_its_element_only_when_the_step_fits() {
    let walk = |load: &str, step: &str| {
        let raw = [
            "// signature: uint64_t f(uint64_t a1)",
            "uint64_t local_10;",
            "",
            "local_10 = a1;",
            &format!("while ({load} != 0) {{"),
            &format!("  local_10 += {step};"),
            "}",
            "return local_10;",
        ]
        .join("\n");
        polish(&raw, 64, &Packs::default())
    };
    let fits = walk("*(uint16_t*)local_10", "2");
    assert!(fits.contains("uint16_t *a1"), "{fits}");
    let wider = walk("*(uint16_t*)local_10", "4");
    assert!(wider.contains("void *a1"), "{wider}");
    let away = walk("*(uint8_t*)(local_10 + 5)", "1");
    assert!(away.contains("void *a1"), "{away}");
}

/// A string walk that reads the next byte and then steps onto it reads
/// where its step lands: the parameter is a byte pointer.
#[test]
fn a_copy_read_where_its_step_lands_walks_bytes() {
    let raw = concat!(
        "// signature: uint32_t f(uint64_t a1)\n",
        "uint64_t var3;\n",
        "uint8_t var1;\n",
        "\n",
        "var1 = *(uint8_t*)a1;\n",
        "var3 = a1;\n",
        "while (var1 != 0) {\n",
        "  var1 = *(uint8_t*)(var3 + 1);\n",
        "  var3 += 1;\n",
        "}\n",
        "return var1;\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("uint8_t *a1"), "{out}");
}

/// Byte stores through a copy stepped by 2 on one path and by 1 on
/// another walk bytes: every step is a whole number of them.
#[test]
fn byte_stores_through_unequal_steps_walk_bytes() {
    let raw = concat!(
        "// signature: void f(uint64_t a1, uint32_t a2)\n",
        "uint64_t local_8;\n",
        "\n",
        "local_8 = a1;\n",
        "if (a2 != 0) {\n",
        "  *(uint8_t*)local_8 = 77;\n",
        "  *(uint8_t*)(local_8 + 1) = 45;\n",
        "  local_8 += 2;\n",
        "}\n",
        "*(uint8_t*)local_8 = 94;\n",
        "local_8 += 1;\n",
        "*(uint8_t*)local_8 = 0;\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("uint8_t *a1"), "{out}");
}

/// A `for` header's step is a step like a body line's: two-byte loads
/// stepped by 4 there name no element, and bytes stepped by 1 there walk.
#[test]
fn a_for_header_step_counts_as_a_step() {
    let walk = |init: &str, head: &str| {
        let raw = [
            "// signature: uint64_t f(uint64_t a1)",
            "uint64_t p;",
            "",
            init,
            &format!("for ({head}) {{"),
            "}",
            "return p;",
        ]
        .join("\n");
        polish(&raw, 64, &Packs::default())
    };
    let wider = walk("p = a1;", "; *(uint16_t*)p != 0; p += 4");
    assert!(wider.contains("void *a1"), "{wider}");
    let bytes = walk(
        "p = a1;",
        "; *(uint8_t*)p != 0 && *(uint8_t*)(p + 1) != 0; p += 1",
    );
    assert!(bytes.contains("uint8_t *a1"), "{bytes}");
    let header_copy = walk(
        "",
        "p = a1; *(uint8_t*)p != 0 && *(uint8_t*)(p + 1) != 0; p += 1",
    );
    assert!(header_copy.contains("uint8_t *a1"), "{header_copy}");
}

/// A copy stepped back by one and read one byte back reads where its step
/// lands: a backward string walk is a byte pointer.
#[test]
fn a_backward_step_lands_on_its_read() {
    let raw = concat!(
        "// signature: uint64_t f(uint64_t a1)\n",
        "uint64_t p;\n",
        "\n",
        "p = a1;\n",
        "while (*(uint8_t*)(p - 1) != 0) {\n",
        "  p -= 1;\n",
        "}\n",
        "return p;\n",
    );
    let out = polish(raw, 64, &Packs::default());
    assert!(out.contains("uint8_t *a1"), "{out}");
}

/// The callee at `ENTRY + 0x20` of [`call_site_image`]: it stores the low
/// half of its second parameter to a field of its first and returns.
const CALLEE: u64 = ENTRY + 0x20;

/// Returns an image of one or two callers of [`CALLEE`].
///
/// The callers at [`ENTRY`] and `ENTRY + 0x10` run their setup, then call
/// [`CALLEE`], which stores `esi` to `[rdi+4]`.
///
/// # Arguments
///
/// * `first` - The setup of the first caller, 3 bytes.
/// * `second` - The setup of the second caller, 3 bytes, or `None` for
///   one caller only.
fn call_site_image(first: [u8; 3], second: Option<[u8; 3]>) -> Program {
    let mut code = first.to_vec();
    code.extend_from_slice(&[0xe8, 0x18, 0x00, 0x00, 0x00, 0xc3]); // ASM: call CALLEE; ret
    code.resize(0x10, 0xcc);
    if let Some(s) = second {
        code.extend_from_slice(&s);
        code.extend_from_slice(&[0xe8, 0x08, 0x00, 0x00, 0x00, 0xc3]); // ASM: call CALLEE; ret
    }
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x89, 0x77, 0x04, // ASM: mov [rdi+0x4], esi
        0xc3, // ASM: ret
    ]);
    let mut p = sysv(&code);
    p.symbols = [
        ("first", ENTRY),
        ("second", ENTRY + 0x10),
        ("callee", CALLEE),
    ]
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Local,
    })
    .to_vec();
    p
}

/// A caller's sign extension keeps the callee's parameter 64 bits wide.
///
/// The callee reads only the low half; a caller passing a 32-bit value says
/// nothing, and one such caller vetoes another's extension.
#[test]
fn a_callers_sign_extension_keeps_the_parameter_wide() {
    let movsxd = [0x48, 0x63, 0xf0]; // ASM: movsxd rsi, eax
    let narrow = [0x89, 0xc6, 0x90]; // ASM: mov esi, eax; nop
    let wide = checked_at(&call_site_image(movsxd, None), CALLEE);
    assert!(wide.contains("uint64_t a2"), "{wide}");
    assert!(wide.contains("*(uint32_t*)(a1 + 4) = a2;"), "{wide}");
    runs_agree(&call_site_image(movsxd, None), CALLEE);
    let plain = checked_at(&call_site_image(narrow, None), CALLEE);
    assert!(plain.contains("uint32_t a2"), "{plain}");
    let mixed = checked_at(&call_site_image(movsxd, Some(narrow)), CALLEE);
    assert!(mixed.contains("uint32_t a2"), "{mixed}");
}
