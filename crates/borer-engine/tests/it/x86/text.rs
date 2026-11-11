//! Literals, tables, constants and idioms in 32-bit text.

use super::*;

/// A guarded assert names the variable it tests: `if (a1 == 0) {
/// assert("reader.isvalid()", "x.cc", 7); }` makes `a1` `reader` in the
/// signature and the body.
#[test]
fn asserts_name_the_variables_they_test() {
    let p = image_with_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x85, 0xc0, 0x75, 0x14, 0x6a, 0x07, 0x68, 0x12, 0x20, 0x40,
            0x00, 0x68, 0x00, 0x20, 0x40, 0x00, 0xe8, 0x06, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x0c,
            0x8b, 0x00, 0xc3, 0xc3,
        ],
        b"reader.isvalid()\0\0src/reader.cc\0",
    );
    let a = Analysis::compute(&p);
    let text = decompile_named(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("var1 = reader;"), "{text}");
    assert!(
        text.contains(
            "reader)
"
        ),
        "{text}"
    );
    assert!(!text.contains("a1"), "{text}");
}

/// A table whose first entry is zero is an address, not the empty string:
/// `mov eax,[ecx*4+0x402000]; ret` over sixteen zero bytes.
#[test]
fn a_zero_led_table_is_an_address_not_an_empty_string() {
    let text = dc_data(
        &[0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0xc3],
        &[0u8; 16],
        &[],
    );
    assert!(text.contains("0x402000"), "{text}");
    assert!(!text.contains("\"\""), "{text}");
}

/// The empty string in a string pool still reads as `""`:
/// `lea eax,[0x402003]; ret` over `"ab\0" "" "cd\0"`.
#[test]
fn an_empty_string_in_a_pool_is_still_a_literal() {
    let text = dc_data(
        &[0x8d, 0x05, 0x03, 0x20, 0x40, 0x00, 0xc3],
        b"ab\0\0cd\0",
        &[],
    );
    assert!(text.contains("return \"\";"), "{text}");
}

/// A global the user named keeps its name where `lea` takes its address,
/// even when a literal could be read there: `lea eax,[0x402000]; ret`
/// over `"abc\0"` with 0x402000 named `greeting`.
#[test]
fn a_named_global_beats_the_literal_at_its_address() {
    let text = dc_data(
        &[0x8d, 0x05, 0x00, 0x20, 0x40, 0x00, 0xc3],
        b"abc\0",
        &[(0x402000, "greeting")],
    );
    assert!(text.contains("&greeting"), "{text}");
}

/// An instruction the lifter does not model keeps the `asm` marker on its
/// comment, so a count of unmodeled instructions counts it: the port read
/// `in al,dx; ret`.
#[test]
fn an_unmodeled_instruction_carries_the_asm_marker() {
    // ASM: mov eax, 1; in al, dx; ret: a port read no compiler emits is
    // left as asm, past an opening that makes the entry a function.
    let text = dc(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xec, 0xc3]);
    assert!(text.contains("/* asm: in al"), "{text}");
}

/// A 32-bit switch, `cmp eax,2; ja default; jmp dword [eax*4+table]` over a
/// table of four-byte case addresses, is resolved and structured.
#[test]
fn a_32_bit_jump_table_becomes_a_switch() {
    let mut code = vec![
        0x8b, 0x44, 0x24, 0x04, 0x83, 0xf8, 0x02, 0x77, 0x44, 0xff, 0x24, 0x85, 0x00, 0x20, 0x40,
        0x00,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x0a, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x14, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x1e, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]);
    let table = [
        0x20, 0x10, 0x40, 0x00, 0x30, 0x10, 0x40, 0x00, 0x40, 0x10, 0x40, 0x00,
    ];
    let p = image_with_data(&code, &table);
    let a = Analysis::compute(&p);
    assert!(
        a.jump_tables.contains_key(&0x401009),
        "the dispatch is not a jump table"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("switch ("), "{text}");
    assert!(text.contains("case 1:"), "{text}");
    assert!(text.contains("return 20;"), "{text}");
}

/// A compare ladder that steps with `dec` folds like one that steps with
/// `sub`: `sub eax,0x1e1; dec eax; je` tests `a1 == 0x1e2`, in the same
/// radix as its siblings.
#[test]
fn a_dec_step_in_a_compare_ladder_folds_to_an_equality() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x2d, 0xe1, 0x01, 0x00, 0x00, 0x48, 0x74, 0x03, 0x33, 0xc0, 0xc3,
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("a1 == 0x1e2") || text.contains("a1 != 0x1e2"),
        "{text}"
    );
    assert!(!text.contains("== 0)"), "{text}");
}

/// A comparison against a Windows status code reads the code's name:
/// `cmp eax, 0x800b0100` is `TRUST_E_NOSIGNATURE`, and `0xc0000005` in a
/// return is `STATUS_ACCESS_VIOLATION`.
#[test]
fn a_status_code_is_named_where_it_is_compared_or_returned() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x3d, 0x00, 0x01, 0x0b, 0x80, 0x75, 0x03, 0x33, 0xc0, 0xc3, 0xb8,
        0x05, 0x00, 0x00, 0xc0, 0xc3,
    ]);
    assert!(text.contains("TRUST_E_NOSIGNATURE"), "{text}");
    assert!(text.contains("STATUS_ACCESS_VIOLATION"), "{text}");
}

/// An operator with a `!` in its name keeps it: `QString::operator!=`
/// called through its slot is not `=`.
#[test]
fn an_operator_with_a_bang_keeps_its_name() {
    use borer_engine::analysis::bare_name;
    assert_eq!(
        bare_name("Qt5Core.dll!QString::operator!="),
        "QString::operator!="
    );
    assert_eq!(bare_name("QString::operator!="), "QString::operator!=");
    assert_eq!(bare_name("KERNEL32.dll!CreateFileW"), "CreateFileW");
    let text = dc_with(
        &[
            0x8b, 0x4c, 0x24, 0x04, 0x68, 0x00, 0x20, 0x40, 0x00, 0xff, 0x15, 0x00, 0x21, 0x40,
            0x00, 0xc3,
        ],
        &[(0x402100, "Qt5Core.dll!??9QString@@QBE_NPBD@Z")],
    );
    assert!(text.contains("QString::operator!=("), "{text}");
}

/// An empty string that follows another literal in the pool is `""` even
/// when padding zeros follow it, the way the compiler lays `"/aid_"`, `""`
/// and `"."` out.
///
/// `push 0x402006; call 0x401010; ret`, with `mov eax,[esp+4]; ret 4` at
/// 0x401010 and the pool `"/aid_\0" "\0" "\0" ".\0"` at 0x402000.
#[test]
fn an_empty_string_after_a_literal_is_a_literal() {
    let mut code = vec![
        0x68, 0x06, 0x20, 0x40, 0x00, 0xe8, 0x06, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let p = image_with_data(&code, b"/aid_\0\0\0.\0");
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401010(\"\")"), "{text}");
}

/// A read through a recognized constant table names the table, and the
/// slicing tables laid out after a CRC-32 table are named after it.
///
/// `mov eax,[esp+4]; mov eax,[eax*4+0x402000]; ret` with a CRC-32 table
/// at 0x402000 and its first slicing table at 0x402400.
#[test]
fn a_known_constant_table_renders_by_name() {
    let code = [
        0x8b, 0x44, 0x24, 0x04, 0x8b, 0x04, 0x85, 0x00, 0x20, 0x40, 0x00, 0xc3,
    ];
    let mut t0 = [0u32; 256];
    for (i, slot) in t0.iter_mut().enumerate() {
        let mut c = u32::try_from(i).unwrap_or(0);
        for _ in 0..8 {
            c = if c & 1 == 1 {
                0xedb8_8320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
        *slot = c;
    }
    let mut data = Vec::new();
    for c in t0 {
        data.extend_from_slice(&c.to_le_bytes());
    }
    for c in t0 {
        data.extend_from_slice(&((c >> 8) ^ t0[(c & 0xff) as usize]).to_le_bytes());
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.crypto.get(&0x402000).copied(),
        Some("CRC-32 (IEEE 802.3) table")
    );
    assert_eq!(
        a.crypto.get(&0x402400).copied(),
        Some("CRC-32 slicing table 1")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("crc_32_table"), "{text}");
}

/// The address of a variable in writable data passed to a call renders as
/// the variable's address, not as a number.
///
/// `push 0x402000; call 0x401020; add esp,4; ret`, with 0x402000 in a
/// writable `.data` section holding zeros and a callee reading its one
/// argument.
#[test]
fn a_writable_data_address_renders_as_a_globals_address() {
    let mut code = vec![
        0x68, 0x00, 0x20, 0x40, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x04, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let mut p = image_with_data(&code, &[0u8; 16]);
    p.sections[1].name = ".data".to_owned();
    p.sections[1].writable = true;
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401020(&g32_402000)"), "{text}");
}

/// A `test r, r` whose operand changes before the jump copies the value
/// into one temporary, not two, and the condition reads `t == 0`.
///
/// The loop of the thiscall-copy test: `mov ecx,esi; add esi,16; test
/// ecx,ecx; je` with `ecx` holding `esi` when the test runs.
#[test]
fn a_test_of_a_value_against_itself_copies_it_once() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x56, 0x8b, 0x75, 0x08, 0xeb, 0x0e, 0x8b, 0xce, 0x83, 0xc6, 0x10, 0x85,
        0xc9, 0x74, 0x05, 0xe8, 0x29, 0x00, 0x00, 0x00, 0x3b, 0x75, 0x0c, 0x75, 0xed, 0x5e, 0x5d,
        0xc2, 0x08, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0xc3]);
    let text = dc(&code);
    assert!(!text.contains("tmp_4"), "{text}");
    assert!(!text.contains(" & "), "{text}");
    assert!(text.contains("== 0) continue;"), "{text}");
}

/// A PE's image base renders as `&__ImageBase`, the linker's name for it.
///
/// `mov ax,[0x400000]; ret` in a PE based at 0x400000.
#[test]
fn a_pes_image_base_renders_as_image_base() {
    let mut p = image(&[0x66, 0xa1, 0x00, 0x00, 0x40, 0x00, 0xc3]);
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("*(uint16_t*)&__ImageBase"), "{text}");
}

/// A constant spelling four printable characters is the multi-character
/// literal the source wrote.
///
/// `mov eax,0x41554556; ret` returns `'AUEV'`, while `mov
/// eax,0x3f800000; ret` (a float's bits) stays a number.
#[test]
fn a_four_character_code_renders_as_its_literal() {
    let text = dc(&[0xb8, 0x56, 0x45, 0x55, 0x41, 0xc3]);
    assert!(text.contains("return 'AUEV';"), "{text}");
    let text = dc(&[0xb8, 0x00, 0x00, 0x80, 0x3f, 0xc3]);
    assert!(text.contains("return 0x3f800000;"), "{text}");
}

/// A parameter or result nothing narrows is the machine word: `uint32_t`
/// on a 32-bit target, where every one of 2,200 functions read `uint64_t`.
///
/// `mov eax,[esp+4]; ret`.
#[test]
fn the_default_type_is_the_machine_word() {
    let text = dc(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    assert!(text.contains("uint32_t sub_401000(uint32_t a1)"), "{text}");
    assert!(!text.contains("uint64_t"), "{text}");
}

/// A constant a bitwise operator applies is a mask, even where its value
/// is the address of a string in the image.
///
/// `mov eax,[esp+4]; and eax,0x402000; ret` with "abcde" at 0x402000.
#[test]
fn a_mask_is_not_named_as_the_string_at_its_value() {
    let text = dc_data(
        &[0x8b, 0x44, 0x24, 0x04, 0x25, 0x00, 0x20, 0x40, 0x00, 0xc3],
        b"abcde\0",
        &[],
    );
    assert!(text.contains("return a1 & 0x402000;"), "{text}");
    assert!(!text.contains('"'), "{text}");
}

/// A sum indexing a string from its first character keeps the literal;
/// the same address multiplied stays a number.
///
/// `"SunMon"` at 0x402001 after a terminator, `a1 = [esp+4]`: `mov
/// eax,[esp+4]; lea eax,[eax+eax*2]; add eax,0x402001; ret` and `imul
/// eax,[esp+4],0x402001; ret`.
#[test]
fn a_sum_from_a_string_start_keeps_the_literal() {
    let data = b"\0SunMon\0";
    let sum = dc_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x8d, 0x04, 0x40, 0x05, 0x01, 0x20, 0x40, 0x00, 0xc3,
        ],
        data,
        &[],
    );
    assert!(sum.contains("\"SunMon\""), "{sum}");
    let mul = dc_data(
        &[0x69, 0x44, 0x24, 0x04, 0x01, 0x20, 0x40, 0x00, 0xc3],
        data,
        &[],
    );
    assert!(mul.contains("0x402001"), "{mul}");
    assert!(!mul.contains('"'), "{mul}");
}

/// A multiplier is a number even where its bytes spell four characters;
/// a value compared with or returned keeps the code it spells.
///
/// `mov eax,0x55555556; imul dword [esp+4]; mov eax,edx; ret` (a division
/// by three), `imul eax,[esp+4],0x55555556; ret`, `cmp dword [esp+4],'GSTG';
/// jne L; mov eax,1; ret; L: xor eax,eax; ret` and `mov eax,'MESH'; ret`.
#[test]
fn a_multiplier_spelling_four_characters_is_a_number() {
    let high = dc(&[
        0xb8, 0x56, 0x55, 0x55, 0x55, 0xf7, 0x6c, 0x24, 0x04, 0x8b, 0xc2, 0xc3,
    ]);
    assert!(high.contains("0x55555556"), "{high}");
    assert!(!high.contains("'UUUV'"), "{high}");
    let mul = dc(&[0x69, 0x44, 0x24, 0x04, 0x56, 0x55, 0x55, 0x55, 0xc3]);
    assert!(mul.contains("0x55555556"), "{mul}");
    assert!(!mul.contains("'UUUV'"), "{mul}");
    let tag = dc(&[
        0x81, 0x7c, 0x24, 0x04, 0x47, 0x54, 0x53, 0x47, 0x75, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
        0xc3, 0x33, 0xc0, 0xc3,
    ]);
    assert!(tag.contains("'GSTG'"), "{tag}");
    let returned = dc(&[0xb8, 0x48, 0x53, 0x45, 0x4d, 0xc3]);
    assert!(returned.contains("return 'MESH';"), "{returned}");
}

/// A stored value read from the register the protection writes out
/// first reads that register's new name, not the load again through the
/// rewritten index (`g[g[i]]`).
///
/// `mov ecx,[esp+4]; mov edx,[esp+8]; test ecx,ecx; je +1; inc ecx; mov
/// ecx,[edx+ecx*4]; mov [edx+0x24],ecx; test edx,edx; je +2; mov eax,ecx;
/// ret`.
#[test]
fn a_stored_value_survives_the_write_out_of_its_index() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0x8b, 0x54, 0x24, 0x08, 0x85, 0xc9, 0x74, 0x01, 0x41, 0x8b, 0x0c,
        0x8a, 0x89, 0x4a, 0x24, 0x85, 0xd2, 0x74, 0x02, 0x8b, 0xc1, 0xc3,
    ]);
    assert!(text.contains("var2 = ((uint32_t*)a2)[var1];"), "{text}");
    assert!(text.contains("*(uint32_t*)(a2 + 0x24) = var2;"), "{text}");
    assert_eq!(text.matches("((uint32_t*)a2)[var1]").count(), 1, "{text}");
}

/// `bt [ecx], eax` tests a bit of the string at `ecx`: the dword `eax >>
/// 5` from it, bit `eax & 31`, not the first dword shifted by all of `eax`.
///
/// `mov eax,[esp+4]; mov ecx,[esp+8]; bt [ecx],eax; setb al; movzx
/// eax,al; ret`.
#[test]
fn a_bit_test_on_memory_indexes_the_bit_string() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x8b, 0x4c, 0x24, 0x08, 0x0f, 0xa3, 0x01, 0x0f, 0x92, 0xc0, 0x0f,
        0xb6, 0xc0, 0xc3,
    ]);
    assert!(
        text.contains("a2[(int64_t)(int32_t)a1 >> 5] >> (a1 & 0x1f)"),
        "{text}"
    );
    assert!(text.contains("uint32_t *a2"), "{text}");
}

/// A jump from an inner switch's arm to the join of the switch around it
/// stays a jump: no loop holds either switch, so it is no `continue`, and
/// a `break` there would leave only the inner switch.
///
/// The shape of `BasepProcessInvalidImage`'s `case 2: { rcx = 21; ... }`:
/// an outer switch on `ecx` whose second arm switches on `edx`; that
/// switch's second arm jumps to the code after the outer switch, while its
/// other arms meet at a tail of their own that returns 1. Both joins are
/// ten stores long, too long to copy into an arm.
#[test]
fn a_jump_to_an_outer_switch_join_stays_a_jump() {
    let mut code = vec![
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0x8b, 0x54, 0x24, 0x08, // ASM: mov edx,[esp+8]
        0x33, 0xc0, // ASM: xor eax,eax
        0x83, 0xf9, 0x02, // ASM: cmp ecx,2
        0x77, 0x6a, // ASM: ja join
        0xff, 0x24, 0x8d, 0x00, 0x20, 0x40, 0x00, // ASM: jmp [ecx*4+0x402000]
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: outer case 0: mov eax,1
        0xeb, 0x5c, // ASM: jmp join
        0x83, 0xfa, 0x02, // ASM: outer case 1: cmp edx,2
        0x77, 0x1a, // ASM: ja tail
        0xff, 0x24, 0x95, 0x0c, 0x20, 0x40, 0x00, // ASM: jmp [edx*4+0x40200c]
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: inner case 0: mov eax,3
        0xeb, 0x0c, // ASM: jmp tail
        0xb8, 0x15, 0x00, 0x00, 0x00, // ASM: inner case 1: mov eax,21
        0xeb, 0x42, // ASM: jmp join
        0xb8, 0x04, 0x00, 0x00, 0x00, // ASM: inner case 2: mov eax,4
    ];
    for k in 0..10u8 {
        code.extend_from_slice(&[0xa3, k * 4, 0x31, 0x40, 0x00]); // ASM: tail: mov [0x403100+4k],eax
    }
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    code.extend_from_slice(&[0xb8, 0x09, 0x00, 0x00, 0x00]); // ASM: outer case 2: mov eax,9
    for k in 0..10u8 {
        code.extend_from_slice(&[0xa3, k * 4, 0x30, 0x40, 0x00]); // ASM: join: mov [0x403000+4k],eax
    }
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    let table = [
        0x16, 0x10, 0x40, 0x00, 0x1d, 0x10, 0x40, 0x00, 0x74, 0x10, 0x40, 0x00, 0x29, 0x10, 0x40,
        0x00, 0x30, 0x10, 0x40, 0x00, 0x37, 0x10, 0x40, 0x00,
    ];
    let text = dc_data(&code, &table, &[]);
    assert!(!text.contains("continue;"), "{text}");
    let arm = text.find("= 21;").unwrap_or(0);
    let jump = text.get(arm..).and_then(|t| t.lines().nth(1)).unwrap_or("");
    assert_eq!(jump.trim(), "goto L_401079;", "{text}");
}

/// A loop-exit jump inside a later arm of a switch the loop holds stays a
/// jump: the arms' braces sit at the switch's own indentation, and a
/// `break` there would leave the switch and run the loop on.
///
/// A loop over `*ecx` dispatching through a three-entry jump table whose
/// second arm jumps to the shared tail after the loop, which the entry
/// also reaches.
#[test]
fn a_loop_exit_in_a_switch_arm_stays_a_jump() {
    let mut code = vec![
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0x33, 0xc0, // ASM: xor eax,eax
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x23, // ASM: je tail
        0x8b, 0x11, // ASM: top: mov edx,[ecx]
        0x83, 0xfa, 0x02, // ASM: cmp edx,2
        0x77, 0x14, // ASM: ja latch
        0xff, 0x24, 0x95, 0x00, 0x20, 0x40, 0x00, // ASM: jmp [edx*4+0x402000]
        0x83, 0xc0, 0x01, // ASM: case 0: add eax,1
        0xeb, 0x08, // ASM: jmp latch
        0x83, 0xc0, 0x05, // ASM: case 1: add eax,5
        0xeb, 0x0b, // ASM: jmp tail
        0x83, 0xc0, 0x07, // ASM: case 2: add eax,7
        0x83, 0xc1, 0x04, // ASM: latch: add ecx,4
        0x83, 0x39, 0x00, // ASM: cmp dword [ecx],0
        0x75, 0xdd, // ASM: jne top
    ];
    for k in 0..9u8 {
        code.extend_from_slice(&[0xa3, k * 4, 0x30, 0x40, 0x00]); // ASM: tail: mov [0x403000+4k],eax
    }
    code.push(0xc3);
    let table = [
        0x18, 0x10, 0x40, 0x00, 0x1d, 0x10, 0x40, 0x00, 0x22, 0x10, 0x40, 0x00,
    ];
    let text = dc_data(&code, &table, &[]);
    let arm = text.find("case 1: {").unwrap_or(0);
    let next = text.find("case 2: {").unwrap_or(0);
    let body = text.get(arm..next).unwrap_or("");
    assert!(body.contains("goto L_40102d;"), "{text}");
    assert!(!body.contains("break;"), "{text}");
}

/// A 32-bit global read into a register in 64-bit code is no wider than
/// 32 bits, so an index read from it needs no mask.
///
/// `mov ecx,[rip+0x402000]; mov rax,[rdx+rcx*8]; ret` in a 64-bit image.
#[test]
fn a_32_bit_global_index_needs_no_mask() {
    let p = raw::image(
        Arch::X86_64,
        &[
            0x8b, 0x0d, 0xfa, 0x0f, 0x00, 0x00, 0x48, 0x8b, 0x04, 0xca, 0xc3,
        ],
        &[0; 8],
    );
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("g32_402000"), "{text}");
    assert!(!text.contains("& 0xffffffff"), "{text}");
}
