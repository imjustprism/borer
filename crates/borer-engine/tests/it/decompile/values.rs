//! Values: widths, casts, idioms, literals, globals and folded checks.

use super::*;

/// Three arms that name three literals under one value are a flag tested
/// three times, not a name table.
#[test]
fn one_value_under_every_name_is_not_a_table() {
    let body = "if (a1 == 0) {\n  return \"x\";\n}\nif (a1 == 0) {\n  return \"y\";\n}\nif (a1 == 0) {\n  return \"z\";\n}\n";
    assert!(enum_table(body, &[]).is_none());
    let real = "if (a1 == 1) {\n  return \"x\";\n}\nif (a1 == 2) {\n  return \"y\";\n}\nif (a1 == 3) {\n  return \"z\";\n}\n";
    assert_eq!(enum_table(real, &[]).map(|t| t.members.len()), Some(3));
}

/// A 32-bit load feeding a 64-bit subtract keeps the machine's borrow
/// width: the load widens, and `0 - 4` is `0xffff_ffff_ffff_fffc`.
///
/// # Panics
///
/// When the widening does not survive the text.
#[test]
fn a_32_bit_load_feeding_a_64_bit_subtract_widens() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let code = [
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0x48, 0x83, 0xe8, 0x04, // ASM: sub rax,4
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let text = runs_agree(&p, 0x401_000);
    assert!(
        text.contains("64_t)*(uint32_t*)a1 - 4") || text.contains("int64_t)*(uint32_t*)a1 - 4"),
        "the widening: {text}"
    );
}

/// A logical shift or an unsigned division of a sign-extended value works
/// on its unsigned bits, which C's `>>` and `/` on the `int64_t` the
/// extension spells would not.
///
/// # Panics
///
/// When the text shifts or divides the signed value.
#[test]
fn an_unsigned_operation_on_a_sign_extension_casts_it_unsigned() {
    let shift = [
        0x48, 0x63, 0xc1, // ASM: movsxd rax,ecx
        0x48, 0xd1, 0xe8, // ASM: shr rax,1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&shift), 0x1_4000_1000);
    assert!(
        text.contains("(uint64_t)") && text.contains(">> 1"),
        "{text}"
    );
    let division = [
        0x48, 0x63, 0xc1, // ASM: movsxd rax,ecx
        0x48, 0x63, 0xca, // ASM: movsxd rcx,edx
        0x33, 0xd2, // ASM: xor edx,edx
        0x48, 0xf7, 0xf1, // ASM: div rcx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&division), 0x1_4000_1000);
    assert!(
        text.contains("(uint64_t)") && text.contains(" / "),
        "{text}"
    );
}

/// A wide difference of sign-extended loads converts each side, for the
/// machine subtracts the extensions at the register's width where C's
/// `int` arithmetic on the loads wraps at 32 bits.
///
/// `movsxd rax,[rcx]; movsxd rdx,[rdx]; sub rax,rdx; ret` of loads whose
/// difference overflows an `int` once answered the wrapped value
/// sign-extended.
///
/// # Panics
///
/// When the text subtracts the loads without converting them.
#[test]
fn a_wide_difference_of_extensions_converts_each_side() {
    let code = [
        0x48, 0x63, 0x01, // ASM: movsxd rax,qword [rcx] (a 32-bit load)
        0x48, 0x63, 0x12, // ASM: movsxd rdx,qword [rdx] (a 32-bit load)
        0x48, 0x29, 0xd0, // ASM: sub rax,rdx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(int64_t)"), "{text}");
}

/// A 32-bit table whose first unit reads as a short string renders as its
/// address, not the string.
///
/// A Rust `Range<u32>` of `[0x20u32, 0x21]` is not the literal `" "`,
/// whose copy elsewhere the callee would read.
///
/// `lea rax,[0x140002000]; ret` over `20 00 00 00 21 00 00 00` once
/// returned `" "`, sending the reader to whichever copy of a space the
/// image holds first.
///
/// # Panics
///
/// When the table renders as the string.
#[test]
fn a_table_of_32_bit_values_is_no_short_string() {
    let code = [
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax,[rip+0xff9]
        0xc3, // ASM: ret
    ];
    let p = program64_with_data(&code, &[0x20, 0, 0, 0, 0x21, 0, 0, 0]);
    let text = runs_agree(&p, 0x1_4000_1000);
    assert!(!text.contains("\" \""), "{text}");
    assert!(text.contains("0x140002000"), "{text}");
}

/// A term of an address that lands on a zero byte keeps its number: a
/// table's leading zero is no empty string, and even a real one holds a
/// single byte no index reads text past.
///
/// `lea rdx,[0x140002011]; movzx eax,byte [rcx+rdx-1]; ret` reads the byte
/// table at `0x140002011` from one byte before it: once a zero then `03 00
/// 5a`, and once the empty string the literal `"AB"` ends just before.
///
/// # Panics
///
/// When the address renders as `""`.
#[test]
fn an_address_term_on_a_zero_byte_is_no_empty_string() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let code = [
        0x48, 0x8d, 0x15, 0x0a, 0x10, 0x00, 0x00, // ASM: lea rdx,[rip+0x100a]
        0x0f, 0xb6, 0x44, 0x11, 0xff, // ASM: movzx eax,byte [rcx+rdx-1]
        0xc3, // ASM: ret
    ];
    let tables: [(usize, &[u8]); 2] = [(0x1010, &[0, 3, 0, 0x5a]), (0x100d, b"AB\0\0\x03")];
    for (at, table) in tables {
        let mut bytes = vec![0u8; 0x2000];
        bytes[..code.len()].copy_from_slice(&code);
        bytes[at..at + table.len()].copy_from_slice(table);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0x1_4000_0000,
            Some(0x1_4000_1000),
            vec![
                Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x1_4000_2000, 0x1000, 0x1000, false, false),
            ],
        );
        p.format = BinaryFormat::Pe;
        let a = Analysis::compute(&p);
        let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
        assert!(!text.contains("\"\""), "{table:?}: {text}");
        assert!(text.contains("0x140002010"), "{table:?}: {text}");
    }
}

/// The lifter agrees with the emulator, register by register, on the
/// shapes it once got wrong.
///
/// Whole-binary verification found each of these on a real client: an
/// absolute value as `neg` then `cmovs` (the emulator's `neg` set no
/// flags), a register saved, clobbered at 32 bits and restored (the
/// restore kept the 32-bit lane), a byte `sar` (lifted without its sign),
/// a 32-bit shift by `cl` of 32 or more (the count was not masked to 5
/// bits), a 32-bit `div` of registers with upper bits set (lifted as a
/// 64-bit division), an `idiv` after `cdq` (the emulator divided
/// unsigned), a one-operand `imul` of a word and of a byte (the high half
/// and the byte product were lifted unsigned), a `cmovae` after an
/// `inc` (which keeps the carry of the `cmp` before it), a 32-bit `bt` by
/// a register (the offset wraps at 32), and double shifts by a count of
/// zero (the far operand's shift by the whole width wrapped to no shift).
/// Every seed starts the block from other random registers.
#[test]
fn the_lifter_agrees_with_the_emulator_where_it_once_did_not() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let code: &[u8] = &[
        0x48, 0x89, 0xf9, 0x48, 0xf7, 0xd9, 0x48, 0x0f, 0x48, 0xcf, 0x4d, 0x89, 0xca, 0x46, 0x8d,
        0x0c, 0x29, 0x4d, 0x89, 0xd1, 0xc0, 0xfb, 0x07, 0xd3, 0xe6, 0x44, 0x89, 0xc0, 0x31, 0xd2,
        0x41, 0xf7, 0xf3, 0x49, 0x89, 0xc4, 0x44, 0x89, 0xf0, 0x99, 0xf7, 0xff, 0x89, 0xf8, 0xf7,
        0xeb, 0x41, 0x89, 0xd7, 0x88, 0xd8, 0xf6, 0xe9, 0x4c, 0x3b, 0xe9, 0xff, 0xc0, 0x4d, 0x0f,
        0x43, 0xf5, 0x0f, 0xa3, 0xc8, 0x0f, 0x92, 0xc0, 0x31, 0xc9, 0x4c, 0x0f, 0xa5, 0xca, 0x4c,
        0x0f, 0xad, 0xc6, 0xc3,
    ];
    let p = program64(code);
    let a = Analysis::compute(&p);
    for seed in 1..=16 {
        let v = verify(&p, &a, &[0x1_4000_1000], seed);
        assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
}

/// An `xadd`'s block checks against the emulator.
///
/// Its register result counts as unreadable (the environment does not
/// hold the old value it received) while the branch after it compares on
/// the addition's flags: both the zero flag (`jz`) and the signed pair
/// (`jl`) read as the sum of the value the block stored and the addend;
/// before the flags were modeled, every signed branch on them came back
/// undecided.
#[test]
fn the_lifter_agrees_with_the_emulator_after_an_xadd() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let code: &[u8] = &[
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x140001020
        0x89, 0x54, 0x24, 0x18, // ASM: mov [rsp+0x18],edx
        0xb8, 0x10, 0x00, 0x00, 0x00, // ASM: mov eax,0x10
        0x0f, 0xc1, 0x44, 0x24, 0x18, // ASM: xadd [rsp+0x18],eax
        0x74, 0x06, // ASM: jz 0x14000101b
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xcc, 0xcc, // ASM: padding
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0x89, 0x54, 0x24, 0x18, // ASM: mov [rsp+0x18],edx
        0xb8, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax,0x30
        0x0f, 0xc1, 0x44, 0x24, 0x18, // ASM: xadd [rsp+0x18],eax
        0x7c, 0x06, // ASM: jl 0x14000103b
        0xb8, 0x04, 0x00, 0x00, 0x00, // ASM: mov eax,4
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xcc, 0xcc, // ASM: padding
        0xc3, // ASM: ret
    ];
    let p = program64(code);
    let a = Analysis::compute(&p);
    for seed in 1..=16 {
        let v = verify(&p, &a, &[0x1_4000_1000, 0x1_4000_1020], seed);
        let branches = v
            .facts
            .get(&borer_engine::analysis::decompile::verify::Fact::Branch)
            .map_or(0, |t| t.compared);
        assert!(v.checked >= 2, "seed {seed}: {}", verify_tsv(&v));
        assert!(branches >= 2, "seed {seed}: {}", verify_tsv(&v));
        assert_eq!(v.undecided, 0, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
}

/// A 64-bit signed division reads as the division; telling what rdx held
/// ahead of it once shifted a lane mask out of a 64-bit word.
#[test]
fn a_64_bit_division_reads_as_the_division() {
    let code: &[u8] = &[0x48, 0x89, 0xf8, 0x48, 0x99, 0x48, 0xf7, 0xfe, 0xc3];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains(" / "), "{text}");
}

/// A signed division by a constant, as a compiler spells it with the high
/// half of a signed multiply, reads as the division.
#[test]
fn a_signed_magic_division_reads_as_the_division() {
    let code: &[u8] = &[
        0xb8, 0x1f, 0x85, 0xeb, 0x51, 0xf7, 0xe9, 0xc1, 0xfa, 0x05, 0x8b, 0xc2, 0xc1, 0xe8, 0x1f,
        0x03, 0xc2, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("/ 100"), "{text}");
    assert!(!text.contains("mulhi"), "{text}");
}

/// String instructions step backward under `std` and forward again after
/// `cld`, in the lifter as in the emulator: the pointers `rep movs`, `movs`
/// and `stos` leave behind agree for every seed.
#[test]
fn string_steps_follow_the_direction_flag() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let code: &[u8] = &[
        0xfd, 0xb9, 0x04, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x74, 0x24, 0xc0, 0x48, 0x8d, 0x7c, 0x24,
        0xe0, 0xf3, 0xa4, 0x48, 0xa5, 0xaa, 0xfc, 0xb9, 0x02, 0x00, 0x00, 0x00, 0xf3, 0x48, 0xab,
        0xa4, 0xc3,
    ];
    let p = program64(code);
    let a = Analysis::compute(&p);
    for seed in 1..=16 {
        let v = verify(&p, &a, &[0x1_4000_1000], seed);
        assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
}

/// The overlapping-copy idiom (`std`, pointers at the last byte, `rep
/// movsb`, `cld`) reads as the `memmove` it is, over the buffers' starts.
#[test]
fn a_backward_copy_reads_as_memmove() {
    let code: &[u8] = &[
        0x56, 0x57, 0x4a, 0x8d, 0x74, 0x02, 0xff, 0x4a, 0x8d, 0x7c, 0x01, 0xff, 0x4c, 0x89, 0xc1,
        0xfd, 0xf3, 0xa4, 0xfc, 0x5f, 0x5e, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("memmove(a1, a2, a3);"), "{text}");
    assert!(!text.contains("memcpy"), "{text}");
    assert!(!text.contains("asm"), "{text}");
}

/// A copy reached with `std` on one path and not the other has no known
/// direction: it is written forward and says so rather than guessing
/// silently.
#[test]
fn a_copy_of_unknown_direction_says_so() {
    let code: &[u8] = &[0x85, 0xc9, 0x74, 0x01, 0xfd, 0xf3, 0xa4, 0xfc, 0xc3];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("direction flag unknown"), "{text}");
    assert!(text.contains("memcpy("), "{text}");
}

/// A read-only global the text only reads is declared with its value.
///
/// `mov rax,[rip+...]; ret` loads a constant from `.rdata`: the text
/// declares `static const uint64_t g64_140002000 = 0x1122334455667788;`,
/// so the value is in the text and compiles to what the machine reads.
#[test]
fn a_read_only_constant_is_declared_with_its_value() {
    let code = [
        0x48, 0x8b, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: mov rax,[rip+0xff9]
        0xc3, // ASM: ret
    ];
    let p = program64_with_data(&code, &0x1122_3344_5566_7788_u64.to_le_bytes());
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(
        text.contains("static const uint64_t g64_140002000 = 0x1122334455667788;"),
        "{text}"
    );
}

/// A bounded index into a read-only table reads the table the file holds.
///
/// `cmp ecx,6; ja def; mov eax,ecx; lea rdx,[table]; mov eax,[rdx+rax*4];
/// ret; def: mov eax,-1; ret` is a `switch` the compiler turned into a
/// lookup; the text names the table and declares its seven entries, the
/// bound's, as the bytes in `.rdata` are.
#[test]
fn a_bounded_lookup_declares_its_table() {
    let code = [
        0x83, 0xf9, 0x06, // ASM: cmp ecx,6
        0x77, 0x0d, // ASM: ja 0x140001012
        0x89, 0xc8, // ASM: mov eax,ecx
        0x48, 0x8d, 0x15, 0xf2, 0x0f, 0x00, 0x00, // ASM: lea rdx,[rip+0xff2]
        0x8b, 0x04, 0x82, // ASM: mov eax,[rdx+rax*4]
        0xc3, // ASM: ret
        0xb8, 0xff, 0xff, 0xff, 0xff, // ASM: mov eax,-1
        0xc3, // ASM: ret
    ];
    let mut data = Vec::new();
    for v in [2u32, 10, 11, 12, 13, 14, 2, 0xdead] {
        data.extend_from_slice(&v.to_le_bytes());
    }
    let p = program64_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(
        text.contains("static const uint32_t g32_140002000[7] = {2, 10, 11, 12, 13, 14, 2};"),
        "{text}"
    );
    assert!(text.contains("g32_140002000[a1]"), "{text}");
}

/// A signed division by a negative constant prints the constant signed.
///
/// `idiv` by -5 is `a1 / -5`. The constant's 64-bit encoding,
/// `18446744073709551611`, is an unsigned literal in C and would turn the
/// division unsigned.
#[test]
fn a_signed_division_by_a_negative_constant_stays_signed() {
    let code = [
        0x89, 0xc8, // ASM: mov eax,ecx
        0xb9, 0xfb, 0xff, 0xff, 0xff, // ASM: mov ecx,-5
        0x99, // ASM: cdq
        0xf7, 0xf9, // ASM: idiv ecx
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("/ -5"), "{text}");
    assert!(!text.contains("18446744073709551611"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A padding `nop` is no dereference: `mov eax,ecx; nop word
/// [rax+rax]; add eax,1; ret` takes a number, not a pointer.
#[test]
fn a_padding_nop_makes_no_pointer() {
    let code = [
        0x89, 0xc8, // ASM: mov eax,ecx
        0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00, // ASM: nop word [rax+rax]
        0x83, 0xc0, 0x01, // ASM: add eax,1
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    let sig = text
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .unwrap_or("");
    assert!(!sig.contains('*'), "{text}");
}

/// An early exit's epilogue does not move the stack pointer of the code
/// after it: a home-slot read there is no stack argument.
///
/// `sub rsp,0x28; mov rax,[rcx]; test rax,rax; je L; add rsp,0x28; jmp
/// rax; L: mov rax,[rsp+0x30]; add rsp,0x28; ret` reads its own first
/// home slot, and takes no stack argument.
#[test]
fn an_early_epilogue_moves_nothing_for_the_code_after_it() {
    let code = [
        0x48, 0x83, 0xec, 0x28, 0x48, 0x8b, 0x01, 0x48, 0x85, 0xc0, 0x74, 0x06, 0x48, 0x83, 0xc4,
        0x28, 0xff, 0xe0, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let stack_args = a.function(0x1_4000_1000).map(|f| f.stack_args);
    assert_eq!(stack_args, Some(0));
}

/// A bare `ret` becomes a plain `return;`.
#[test]
fn bare_ret_function() {
    let out = dc(0x10e0);
    assert!(out.contains("return;"), "no plain return:\n{out}");
}

/// Decompiling the same function twice yields byte-identical text.
#[test]
fn deterministic_output() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for entry in [0x1000u64, 0x1020, 0x1060, 0x1100, 0x1130] {
        let first = decompile(&p, &a, &o, entry);
        let second = decompile(&p, &a, &o, entry);
        assert_eq!(first, second, "decompile not deterministic for {entry:#x}");
    }
}

/// An overlay comment on an instruction appears in the pseudo-C.
#[test]
fn overlay_comments_appear_in_output() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.comments.insert(0x1005, "branch on arg1".to_owned());
    let out = decompile(&p, &a, &o, 0x1000).unwrap_or_default();
    assert!(
        out.contains("// branch on arg1"),
        "comment missing:
{out}"
    );
}

/// `S`: `lea rcx,[string]; call Q` renders the literal as the call argument.
#[test]
fn string_literal_in_lea() {
    let out = dc(0x1200);
    assert!(
        out.contains("Base::vfunc_1(\"hello, borer world\");"),
        "string literal missing from call args:
{out}"
    );
}

/// `M`: a memory exchange keeps the old value in a temporary, a memory bit set
/// is a compound read-modify-write (`|=`), AVX moves copy, and the MXCSR
/// store is a call.
///
/// `bts [rcx+8], rax` takes its register offset into a bit string (verifier
/// R3): it sets bit `rax & 63` of the quadword `rax >> 6` quadwords past
/// `a1 + 8`, so the update indexes that word rather than shifting the
/// first one by the whole offset, and the bit is a 64-bit one: `1 << 40`
/// of an `int` loses it.
#[test]
fn memory_exchange_bit_set_and_avx_moves() {
    let out = dc(0x1360);
    assert!(out.contains("a1->field_0x0 = a2;"), "{out}");
    assert!(out.contains("return var1"), "old value lost:\n{out}");
    assert!(
        out.contains("((uint64_t*)(a1 + 8))[(int64_t)var1 >> 6] |= (uint64_t)1 << (var1 & 0x3f);"),
        "{out}"
    );
    assert!(out.contains("a1->field_0x20 = a1->field_0x10;"), "{out}");
    assert!(out.contains("a1->field_0x30 = stmxcsr();"), "{out}");
    assert!(
        !out.contains("/*"),
        "unmodeled instruction survived:\n{out}"
    );
}

/// `AC2`: the carry an `adc` reads after a join comes from a different
/// addition on each edge, so each edge computes it into the shared truth
/// temporary and the `adc` adds that.
#[test]
fn carry_from_different_additions_reaches_the_adc_as_a_truth() {
    let out = dc(0x1510);
    assert!(!out.contains("/* adc"), "{out}");
    assert!(out.contains("uaddo64("), "{out}");
    assert!(out.contains("+ var2;"), "{out}");
}

/// A value that provably fits a byte keeps that width once written out.
///
/// `MB` keeps `*(uint32_t*)a1 == 1` in `bl` across a call: the compare is
/// written out as `rbx = ... == 1;` before the call, and the `test bl, bl`
/// after it reads `rbx` with no `& 0xff`.
#[test]
fn written_out_truth_values_read_without_a_mask() {
    let out = dc(0x1fe4);
    assert!(out.contains("var1 = *(uint32_t*)a1 == 1;"), "{out}");
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A short literal in read-only data renders as a string when a terminator
/// follows it.
///
/// `SS` passes `"%d"`, two characters long, to `Q`.
#[test]
fn short_read_only_literals_render_as_strings() {
    let out = dc(0x4160);
    assert!(out.contains("\"%d\""), "{out}");
}

/// A UTF-16LE literal in read-only data renders wide, not as its first
/// character.
///
/// `WL` passes `L"AES"`, whose bytes also read as the one-character narrow
/// string `"A"` because the high byte of the first code unit terminates it.
/// Read-only data accepts a one-character literal, so the narrow reading
/// wins unless the two are weighed; then every wide Windows API constant
/// (`L"SHA256"`, `L"ChainingModeGCM"`) renders as a single letter.
#[test]
fn wide_read_only_literals_render_wide() {
    let out = dc(0x4170);
    assert!(out.contains("L\"AES\""), "{out}");
}

/// The byte multiply and divide lift, keeping both halves in `ax`.
///
/// `ML8` returns `al * dl` from `ax`, and `DV8` returns the remainder
/// `ah` of `ax / dl`.
#[test]
fn byte_multiply_and_divide_lift() {
    let mul = dc(0x4200);
    assert!(!mul.contains("/*"), "{mul}");
    assert!(mul.contains(" * "), "{mul}");
    let div = dc(0x4210);
    assert!(!div.contains("/*"), "{div}");
    assert!(div.contains(" % "), "{div}");
}

/// A `lock`-prefixed read-modify-write renders as an atomic intrinsic
/// whose result the following branch reads.
///
/// `LK` drops a reference count with `lock dec` and returns one when it
/// reached zero.
#[test]
fn locked_read_modify_writes_render_as_atomics() {
    let out = dc(0x4790);
    assert!(
        out.contains("var1 = atomic_sub32(*(uint32_t*)(a1 + 8), 1);"),
        "{out}"
    );
    assert!(
        out.contains("if (var1 == 0)") || out.contains("if (var1 != 0)"),
        "{out}"
    );
}

/// The logic flavor of a locked read-modify-write renders as the same
/// atomic statement the arithmetic one does.
///
/// `LKO` sets a flag bit with `lock or` and returns one; no branch
/// follows, so the atomic is a statement and not a value, the way a bit
/// taken is.
#[test]
fn locked_logic_reads_as_the_same_atomic_statement() {
    let out = dc(0x5900);
    assert!(
        out.contains("atomic_or32(*(uint32_t*)(a1 + 0x10), 64);"),
        "{out}"
    );
    assert!(!out.contains("tmp_"), "{out}");
}

/// Decompiling every fixture function at once matches doing it one by one.
///
/// The parallel path takes the entries from one queue, largest function
/// first, and must return the same text in the order of the entries as
/// the sequential call, whatever that order is.
#[test]
fn parallel_decompile_matches_sequential() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let mut entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    for _ in 0..2 {
        let all = decompile_all(&p, &a, &o, &entries);
        assert_eq!(all.len(), entries.len());
        for (entry, got) in entries.iter().zip(&all) {
            assert_eq!(*got, decompile(&p, &a, &o, *entry), "{entry:#x}");
        }
        entries.reverse();
    }
}

/// A range test joined to a bit test of a constant reads as the values it
/// lists.
///
/// `lea eax,[rcx-5]; cmp eax,54; ja N; mov rdx,0x40000008000001; bt
/// rdx,rax; jae N; mov eax,1; ret; N: xor eax,eax; ret` is `x == 5 || x ==
/// 32 || x == 59` as a compiler writes it, and the guard that returns 0 is
/// its negation, one comparison per member with no shift left. A range
/// that lets everything above it through keeps its test in front of the
/// members.
#[test]
fn a_bit_test_of_a_constant_reads_as_its_members() {
    let code = [
        0x8d, 0x41, 0xfb, 0x83, 0xf8, 0x36, 0x77, 0x16, 0x48, 0xba, 0x01, 0x00, 0x00, 0x08, 0x00,
        0x00, 0x40, 0x00, 0x48, 0x0f, 0xa3, 0xc2, 0x73, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        0x31, 0xc0, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains(">>"), "{text}");
    assert!(text.contains("a1 != 5 && "), "{text}");
    assert!(text.contains("a1 != 32 && "), "{text}");
    assert!(text.contains("a1 != 59) {"), "{text}");
    // ASM: cmp cl,28; ja Y; mov eax,0x1410004; bt eax,ecx; jb Y; xor eax,eax; ret; Y: mov eax,1; ret
    let code = [
        0x80, 0xf9, 0x1c, 0x77, 0x0d, 0xb8, 0x04, 0x00, 0x41, 0x01, 0x0f, 0xa3, 0xc8, 0x72, 0x03,
        0x31, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains(">>"), "{text}");
    assert!(text.contains(" > 28 || "), "{text}");
    for member in ["== 2 || ", "== 16 || ", "== 22 || ", "== 24) {"] {
        assert!(text.contains(member), "{member}: {text}");
    }
}

/// A pointer compared with zero is `nullptr`, and an `int32_t` in the same
/// function stays `0`.
///
/// The signature already names the pointer and the integer. The body also
/// loads through `rcx` and tests `edx`, so the decompiler's own types take
/// the same spelling: the pointer is `nullptr` and the integer is `0`.
#[test]
fn a_pointer_and_an_int_keep_their_own_zero() {
    let raw = concat!(
        "// signature: int32_t f(uint32_t*a1, int32_t a2)\n",
        "if (a1 == 0) {\n",
        "  return 0;\n",
        "}\n",
        "if (a2 == 0) {\n",
        "  return 1;\n",
        "}\n",
        "return *(uint32_t*)a1;\n",
    );
    let out = polish(raw, 64, &borer_engine::pack::Packs::default());
    assert!(out.contains("if (a1 == nullptr)"), "{out}");
    assert!(out.contains("if (a2 == 0)"), "{out}");
    assert!(out.contains("return 0;"), "{out}");
    assert!(!out.contains("a2 == nullptr"), "{out}");
    assert!(!out.contains("NULL"), "{out}");
    let code = &[
        0x48, 0x85, 0xc9, // ASM: test rcx, rcx
        0x74, 0x09, // ASM: jz zero
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x05, // ASM: jz zero
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(code), 0x1_4000_1000);
    assert!(text.contains("uint32_t *a1, uint32_t a2"), "{text}");
    assert!(text.contains("if (a1 == nullptr || a2 == 0)"), "{text}");
    assert!(!text.contains("NULL"), "{text}");
}

/// `((T*)base)[i]` is `base[i]` when `base` is already a `T *`.
///
/// A `uint8_t *` read as `uint32_t`, a `void *`, a `uint64_t *`, and the
/// machine word keep the cast. `IX` is the matching pointer: `a1[a2]`.
#[test]
fn an_index_of_a_matching_pointer_drops_the_element_cast() {
    let raw = concat!(
        "// signature: uint32_t f(uint32_t *a1, uint8_t *a2, void *a3, uint64_t a4, uint64_t *a5)\n",
        "return ((uint32_t*)a1)[a4] + ((uint32_t*)a2)[a4] + ((uint32_t*)a3)[a4] + ((uint32_t*)a4)[a4] + ((uint32_t*)a5)[a4];\n",
    );
    let out = polish(raw, 64, &borer_engine::pack::Packs::default());
    assert!(out.contains("a1[a4]"), "{out}");
    assert!(out.contains("((uint32_t*)a2)[a4]"), "{out}");
    assert!(out.contains("((uint32_t*)a3)[a4]"), "{out}");
    assert!(out.contains("((uint32_t*)a4)[a4]"), "{out}");
    assert!(out.contains("((uint32_t*)a5)[a4]"), "{out}");
    assert!(!out.contains("((uint32_t*)a1)"), "{out}");
    let ix = dc(0x4b10);
    assert!(ix.contains("return a1[a2];"), "{ix}");
}

/// Division by a constant comes back from its magic multiply.
///
/// `DV5` is the signed form (high multiply, arithmetic shift, sign-bit fix)
/// of `a1 / 5`; `DV10` the unsigned form (high multiply and shift) of
/// `a1 / 10`; `DM10` subtracts ten times that quotient, `a1 % 10`.
#[test]
fn divisions_by_constants_come_back_from_their_magic() {
    let signed = dc(0x4aa0);
    assert!(
        signed.contains("(int64_t a1)") && signed.contains("a1 / 5;"),
        "{signed}"
    );
    let unsigned = dc(0x4ac0);
    assert!(unsigned.contains("return a1 / 10;"), "{unsigned}");
    let remainder = dc(0x4ae0);
    assert!(remainder.contains("return a1 % 10;"), "{remainder}");
}

/// `x | -1` is `-1` whatever `x` is.
///
/// `OR`'s `or rax, -1` seeds a register the compiler's way; it reads as the
/// constant, not as `rax | 0xffffffffffffffff`.
#[test]
fn or_with_all_ones_folds_to_all_ones() {
    let out = dc(0x4b30);
    assert!(out.contains("return -1;"), "{out}");
}

/// A branchless select comes back as the ternary it stands for.
///
/// `SE` builds `(-(0 < a1)) & 0x22` from `setg`, `neg` and `and`: the mask
/// is all ones or none, so the value is `a1 > 0 ? 34 : 0`.
#[test]
fn selects_through_masks_render_as_ternaries() {
    let out = dc(0x4b20);
    assert!(out.contains(" > 0 ? 34 : 0);"), "{out}");
    assert!(!out.contains(" & "), "{out}");
}

/// A load at `base + index * sizeof(T)` is element `index` of a `T` array.
///
/// `IX` reads `[rcx + rdx * 4]` as a dword. The parameter is a `uint32_t *`,
/// so the element cast is the declaration: `a1[a2]`, not
/// `*(uint32_t*)(a1 + a2 * 4)` and not `((uint32_t*)a1)[a2]`.
#[test]
fn indexed_loads_render_as_arrays() {
    let out = dc(0x4b10);
    assert!(out.contains("uint32_t *a1"), "{out}");
    assert!(out.contains("return a1[a2];"), "{out}");
    assert!(!out.contains("((uint32_t*)a1)"), "{out}");
}

/// The sign bit of a quotient by a constant is the sign bit of its dividend.
///
/// `QS` takes the magic quotient of `a1 / 208` and shifts its sign bit down;
/// a positive divisor never changes the sign, so it is `a1 >> 63`.
#[test]
fn a_quotients_sign_bit_is_its_dividends() {
    let out = dc(0x4b40);
    assert!(out.contains("return a1 >> 63;"), "{out}");
}

/// A ternary that is an index needs no parentheses of its own.
///
/// `TI` reads element `a2 != 3 ? a2 + 1 : 0` of the array at `a1`; the
/// brackets already delimit it.
#[test]
fn ternary_indexes_drop_their_parentheses() {
    let out = dc(0x4b90);
    assert!(out.contains("return a1[a2 != 3 ? a2 + 1 : 0];"), "{out}");
}

/// A mask that clears low bits renders as the complement of those bits.
///
/// `AM` aligns `a1` down to sixteen: `a1 & ~0xf`, not
/// `a1 & 0xfffffffffffffff0`.
#[test]
fn clearing_masks_render_as_complements() {
    let out = dc(0x4bb0);
    assert!(out.contains("return a1 & ~0xf;"), "{out}");
}

/// An unsigned division whose magic needs 65 bits comes back too.
///
/// `DV7` computes `a1 / 7` the overflow way: `((x - mulhi) >> 1) + mulhi`
/// stands in for the 65th bit of the magic.
#[test]
fn overflow_form_divisions_come_back_from_their_magic() {
    let out = dc(0x4bc0);
    assert!(out.contains("return a1 / 7;"), "{out}");
}

/// A sign-extended load is a load of the signed type.
///
/// `SX` reads a dword and sign-extends it: `*(int32_t*)a1`, not
/// `(int64_t)(int32_t)*(uint32_t*)a1`; `SX2` indexes: `((int32_t*)a1)[a2]`.
#[test]
fn sign_extended_loads_render_as_signed_loads() {
    let out = dc(0x4be0);
    assert!(out.contains("return *(int32_t*)a1;"), "{out}");
    let out = dc(0x4bf0);
    assert!(out.contains("return ((int32_t*)a1)[a2];"), "{out}");
}

/// A signed compare casts an operand once.
///
/// `SC` compares the sign-extended `a1` with `a2`, now an `int64_t`: the
/// left side reads `(int64_t)(int32_t)a1`, so no `(int64_t)` stacks on it.
#[test]
fn signed_compares_cast_once() {
    let out = dc(0x4c00);
    assert!(
        out.contains("(int32_t)a1 > a2") && out.contains("int64_t a2)"),
        "{out}"
    );
    assert!(!out.contains("(int64_t)(int64_t)"), "{out}");
}

/// A value a block reads twice is written to its register once.
///
/// `RU` computes `a1 + a2 * 8 + 0x10` and stores it twice: the body assigns
/// `rax` once and stores `rax`, instead of spelling the sum at each store.
#[test]
fn values_read_twice_are_written_once() {
    let out = dc(0x4c40);
    assert_eq!(out.matches("a2 * 8").count(), 1, "{out}");
    assert_eq!(out.matches("= var1;").count(), 2, "{out}");
}

/// A magic multiply stays inlined until its division folds.
///
/// `DV208`'s quotient is over the reuse threshold and the block reads it
/// twice, by the shift that takes its sign bit and by the add that applies
/// it; writing it to a variable there would leave the magic multiply
/// spelled out instead of the `/ 208` it is.
#[test]
fn half_idioms_are_not_written_out_early() {
    let out = dc(0x4c60);
    assert!(out.contains("/ 208;"), "{out}");
    assert!(!out.contains("mulhi"), "{out}");
}

/// A value computed for nobody goes, and a call whose result nobody reads
/// stays as a call.
///
/// `r9` is assigned once and never read, so the line is noise; `rax` holds
/// a call's result nothing reads, so the call stands alone, and `rcx` is
/// read by the loop's back edge.
#[test]
fn assignments_nothing_reads_are_dropped() {
    let text = "r9 = a2 - a1;\nrax = sub_1000(a1);\nrcx = 0;\ndo {\n  rcx += 1;\n} while (rcx != a2);\nreturn a1;\n";
    let out = cleanup(text);
    assert!(!out.contains("r9"), "{out}");
    assert!(out.contains("sub_1000(a1);"), "{out}");
    assert!(!out.contains("rax"), "{out}");
    assert!(out.contains("rcx = 0;"), "{out}");
    let escaped = "rdx = &local_18;\nsub_1000(rdx);\nreturn 0;\n";
    assert!(cleanup(escaped).contains("rdx = &local_18;"), "{escaped}");
}

/// A lone terminator in read-only data is the empty string.
///
/// `ES` hands back the address of a zero byte in `.rdata`, which is what a
/// compiler emits for `""`; printing the address instead says nothing.
#[test]
fn the_empty_string_reads_as_one() {
    let out = dc(0x4de0);
    assert!(out.contains("return \"\";"), "{out}");
}

/// A literal holding a tab is still one string.
///
/// `TB` names a charset table that starts with a space and a tab, the shape
/// a number parser carries; stopping at the tab leaves an address where the
/// source had a string.
#[test]
fn literals_may_hold_a_tab() {
    let out = dc(0x4e00);
    assert!(out.contains(r#"return " \t-+0";"#), "{out}");
}

/// A local every use reads narrowly is declared that narrow.
///
/// `rbx` holds a call's result but every read sign-extends it from 32 bits,
/// so it was an `int32_t` and the casts say nothing the declaration does
/// not; `rdx` is read whole and stays as it is.
#[test]
fn locals_used_at_one_width_are_typed() {
    let text = concat!(
        "// signature: uint64_t f(uint64_t a1)\n",
        "uint64_t rbx, rdx;\n",
        "rbx = sub_1000(a1);\n",
        "rdx = (int64_t)(int32_t)rbx + a1;\n",
        "return (int64_t)(int32_t)rbx + rdx;\n",
    );
    let out = polish(text, 64, &borer_engine::pack::Packs::default());
    assert!(out.contains("int32_t rbx;"), "{out}");
    assert!(out.contains("uint64_t rdx;"), "{out}");
    assert!(out.contains("rdx = rbx + a1;"), "{out}");
    assert!(out.contains("return rbx + rdx;"), "{out}");
}

/// A shift by a constant records the bit it shifted out, and rotates
/// through carry lift.
///
/// `SC`'s `adc` adds bit 4 of `a1`; `RR`'s `rcr` rotates the compare's carry
/// in and its `cmovae` reads the bit rotated out; neither leaves an asm
/// comment.
#[test]
fn shift_carry_and_rotate_through_carry_lift() {
    let sc = dc(0x1880);
    assert!(!sc.contains("/*"), "{sc}");
    assert!(sc.contains(">> 4) & 1"), "{sc}");
    let rr = dc(0x1890);
    assert!(!rr.contains("/*"), "{rr}");
    assert!(rr.contains(">> 1)"), "{rr}");
    assert!(rr.contains("!(a3 & 1)"), "{rr}");
}

/// Scratch.
#[test]
fn scratch_tr() {
    println!("TR:\n{}", dc(0x5550));
    println!("TC:\n{}", dc(0x5570));
}

/// Scratch.
#[test]
fn scratch_tr2() {
    println!("TR:\n{}", dc(0x5550));
}

/// Scratch.
#[test]
fn scratch_fp() {
    println!("FP:\n{}\nFC:\n{}", dc(0x5580), dc(0x5590));
}

/// An unsigned comparison of a sign-extended value compares its unsigned
/// bits.
///
/// `movsxd rbx,ecx; cmp ebx,0x40f; ja L; mov eax,1; ret; L: xor eax,eax;
/// ret`, as `LZClose` opens: `ja` compares `ebx` unsigned, so `-1` is
/// above `0x40f`, where the text once compared the signed value, `a1 <=
/// 0x40f`, and took the other branch for every negative argument.
#[test]
fn an_unsigned_compare_of_a_signed_value_reads_its_bits_unsigned() {
    let code = [
        0x48, 0x63, 0xd9, 0x81, 0xfb, 0x0f, 0x04, 0x00, 0x00, 0x77, 0x06, 0xb8, 0x01, 0x00, 0x00,
        0x00, 0xc3, 0x31, 0xc0, 0xc3,
    ];
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(
        text.lines()
            .any(|l| l.contains("(uint32_t)a1 <= 0x40f") || l.contains("(uint32_t)a1 > 0x40f")),
        "{text}"
    );
}

/// A 32-bit field multiplied in 64 bits keeps the product's high half.
///
/// `mov eax,[rcx+8]; imul rax,rax,0x431bde83; shr rax,0x32; ret` divides
/// the field by a magic multiply whose product needs 63 bits, where the
/// text's `*(uint32_t*)(a1 + 8) * 0x431bde83` wrapped in `unsigned int`;
/// the high word of the whole product is the division it computes.
#[test]
fn a_32_bit_load_multiplied_in_64_bits_keeps_the_high_half() {
    let code = [
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0x48, 0x69, 0xc0, 0x83, 0xde, 0x1b, 0x43, // ASM: imul rax, rax, 0x431bde83
        0x48, 0xc1, 0xe8, 0x32, // ASM: shr rax, 0x32
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("*(uint32_t*)(a1 + 8) / 1000000"), "{text}");
}

/// clang's signed division by a constant reads as the division.
///
/// The whole product of the sign-extended word is formed once, its high
/// word shifted arithmetically and its sign added; the high word read off
/// the product is the quotient's magic multiply, and the sum of it and
/// the product's sign is `(int32_t)a1 / 10`.
#[test]
fn clangs_wide_product_division_reads_as_the_division() {
    let code = [
        0x48, 0x63, 0xc1, // ASM: movsxd rax, ecx
        0x48, 0x69, 0xc0, 0x67, 0x66, 0x66, 0x66, // ASM: imul rax, rax, 0x66666667
        0x48, 0x89, 0xc1, // ASM: mov rcx, rax
        0x48, 0xc1, 0xe9, 0x3f, // ASM: shr rcx, 0x3f
        0x48, 0xc1, 0xf8, 0x22, // ASM: sar rax, 0x22
        0x01, 0xc8, // ASM: add eax, ecx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("/ 10;"), "{text}");
    assert!(!text.contains("0x66666667"), "{text}");
}

/// A remainder whose quotient is subtracted through a negative multiplier
/// at 32 bits reads as the remainder.
///
/// adler32's `a %= 65521` multiplies the quotient by `0xffff000f`, minus
/// 65521 in the low word only, and adds.
#[test]
fn a_remainder_through_a_32_bit_negative_multiplier_reads_as_the_remainder() {
    let code = [
        0x89, 0xc8, // ASM: mov eax, ecx
        0xba, 0x71, 0x80, 0x07, 0x80, // ASM: mov edx, 0x80078071
        0xf7, 0xe2, // ASM: mul edx
        0xc1, 0xea, 0x0f, // ASM: shr edx, 0xf
        0x69, 0xd2, 0x0f, 0x00, 0xff, 0xff, // ASM: imul edx, edx, 0xffff000f
        0x01, 0xd1, // ASM: add ecx, edx
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("% 65521"), "{text}");
    assert!(!text.contains("mulhi"), "{text}");
}

/// The `/GS` cookie leaves the text, and the header says it was folded.
///
/// The prologue stores the cookie mixed with the stack pointer into a
/// slot and the epilogue hands the slot, mixed again, to the cookie check,
/// an unnamed function of the CRT's shape (`cmp rcx, [cookie]; jne fail;
/// rol rcx, 16`), which is named for it; the text keeps the function's
/// work and runs as the binary does.
#[test]
fn a_gs_cookie_folds_out_of_the_text() {
    let code = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x8b, 0x05, 0xf5, 0x0f, 0x00, 0x00, // ASM: mov rax, [rip + 0xff5] (cookie)
        0x48, 0x31, 0xe0, // ASM: xor rax, rsp
        0x48, 0x89, 0x44, 0x24, 0x20, // ASM: mov [rsp + 0x20], rax
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx + 1]
        0x48, 0x8b, 0x4c, 0x24, 0x20, // ASM: mov rcx, [rsp + 0x20]
        0x48, 0x31, 0xe1, // ASM: xor rcx, rsp
        0xe8, 0x1c, 0x00, 0x00, 0x00, // ASM: call checker
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0x48, 0x3b, 0x0d, 0xb9, 0x0f, 0x00, 0x00, // ASM: cmp rcx, [rip + 0xfb9] (checker)
        0x75, 0x10, // ASM: jne fail
        0x48, 0xc1, 0xc1, 0x10, // ASM: rol rcx, 0x10
        0x66, 0xf7, 0xc1, 0xff, 0xff, // ASM: test cx, 0xffff
        0x75, 0x01, // ASM: jne fail2
        0xc3, // ASM: ret
        0x48, 0xc1, 0xc9, 0x10, // ASM: ror rcx, 0x10 (fail2)
        0xcc, // ASM: int3 (fail)
    ];
    let cookie = 0x2b99_2ddf_a232u64.to_le_bytes();
    let p = program64_with_data(&code, &cookie);
    let text = runs_agree(&p, 0x1_4000_1000);
    assert!(text.contains("// folded: /GS cookie"), "{text}");
    assert!(!text.contains("security_check_cookie("), "{text}");
    assert!(!text.contains(" ^ "), "{text}");
    assert!(text.contains("return a1 + 1;"), "{text}");
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x1_4000_1040).and_then(|f| f.name.clone()),
        Some("__security_check_cookie".to_owned())
    );
}

/// A Linux stack canary leaves the text, and the header says it was folded.
///
/// The prologue copies `fs:0x28` into a slot and the epilogue compares the
/// slot with it, calling `__stack_chk_fail` on a mismatch; the text keeps
/// the function's work alone.
#[test]
fn a_linux_stack_canary_folds_out_of_the_text() {
    use borer_engine::program::{Symbol, SymbolKind};
    let code = [
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
        0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: mov rax, fs:[0x28]
        0x48, 0x89, 0x44, 0x24, 0x10, // ASM: mov [rsp + 0x10], rax
        0x8d, 0x41, 0x01, // ASM: lea eax, [rcx + 1]
        0x64, 0x48, 0x8b, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: mov rdx, fs:[0x28]
        0x48, 0x3b, 0x54, 0x24, 0x10, // ASM: cmp rdx, [rsp + 0x10]
        0x75, 0x05, // ASM: jne fail
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
        0xc3, // ASM: ret
        0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: call __stack_chk_fail (fail)
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0xcc, // ASM: int3 (padding)
        0x0f, 0x0b, // ASM: ud2 (__stack_chk_fail)
    ];
    let mut p = program64(&code);
    p.symbols.push(Symbol {
        name: "__stack_chk_fail".to_owned(),
        addr: 0x1_4000_1040,
        kind: SymbolKind::Local,
    });
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("// folded: stack canary"), "{text}");
    assert!(!text.contains("fs + 0x28"), "{text}");
    assert!(!text.contains("__stack_chk_fail("), "{text}");
    assert!(text.contains("return a1 + 1;"), "{text}");
}

/// A Rust bounds check folds onto the indexing it guards.
///
/// `f` indexes `a3[a1]` after `cmp rcx, rdx; jae fail`, the failing path
/// handing `panic_bounds_check` the index, the length and a
/// `core::panic::Location`; the entry is a function that loads the
/// message's format template and calls on without returning, which names
/// it. The check's diamond leaves whole, the indexing statement after it
/// gains `/* bounds-checked */`, and a header note says whose calls left,
/// so the structure check still agrees.
#[test]
fn a_rust_bounds_check_reads_as_its_panic_and_location() {
    let mut code = vec![
        0x48, 0x39, 0xd1, // ASM: cmp rcx, rdx
        0x73, 0x05, // ASM: jae fail
        0x49, 0x8b, 0x04, 0xc8, // ASM: mov rax, [r8 + rcx*8]
        0xc3, // ASM: ret
        0x4c, 0x8d, 0x05, 0xef, 0x11, 0x00, 0x00, // ASM: lea r8, [rip + 0x11ef] (location)
        0xe8, 0x2a, 0x00, 0x00, 0x00, // ASM: call panic_bounds_check
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x55, // ASM: push rbp
        0x48, 0x83, 0xec, 0x50, // ASM: sub rsp, 0x50
        0x48, 0x89, 0x4c, 0x24, 0x48, // ASM: mov [rsp + 0x48], rcx
        0x48, 0x89, 0x54, 0x24, 0x40, // ASM: mov [rsp + 0x40], rdx
        0x4c, 0x89, 0x44, 0x24, 0x38, // ASM: mov [rsp + 0x38], r8
        0x48, 0x8d, 0x0d, 0xa5, 0x10, 0x00, 0x00, // ASM: lea rcx, [rip + 0x10a5] (message)
        0xe8, 0x20, 0x00, 0x00, 0x00, // ASM: call panic_fmt
    ]);
    code.resize(0x80, 0xcc);
    code.extend_from_slice(&[0x0f, 0x0b]); // ASM: ud2
    let file = br"C:\Users\me\.cargo\registry\src\index.crates.io-1949cf8c6b5b557f\rhai-1.26.1\src\parser.rs";
    let mut data = vec![0u8; 0x220];
    data[0x10..0x10 + file.len()].copy_from_slice(file);
    let message = b"\x20index out of bounds: the len is \xc0\x12 but the index is ";
    data[0x100..0x100 + message.len()].copy_from_slice(message);
    let len = u64::try_from(file.len()).expect("a short path");
    data[0x200..0x208].copy_from_slice(&0x1_4000_2010u64.to_le_bytes());
    data[0x208..0x210].copy_from_slice(&len.to_le_bytes());
    data[0x210..0x214].copy_from_slice(&1015u32.to_le_bytes());
    data[0x214..0x218].copy_from_slice(&32u32.to_le_bytes());
    let p = program64_with_data(&code, &data);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("return a3[a1];  /* bounds-checked */"),
        "{text}"
    );
    assert!(
        text.contains("// note: calls to panic_bounds_check are left out"),
        "{text}"
    );
    assert!(!text.contains("panic_bounds_check("), "{text}");
    assert!(
        borer_engine::analysis::decompile::traces::check_structure(
            &p,
            &Analysis::compute(&p),
            &Overlay::default(),
            0x1_4000_1000,
            &text
        ) == borer_engine::analysis::decompile::traces::Structure::Agrees,
        "{text}"
    );
}

/// A 16-bit rotate by 8 swaps the half word's bytes and reads as `bswap`.
#[test]
fn a_half_word_rotate_by_eight_reads_as_a_byte_swap() {
    let code = [
        0x0f, 0xb7, 0x01, // ASM: movzx eax, word ptr [rcx]
        0x66, 0xc1, 0xc0, 0x08, // ASM: rol ax, 0x8
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("bswap("), "{text}");
    assert!(!text.contains("rotl16"), "{text}");
}

/// A logical shift of all ones shifts its unsigned bits.
///
/// `mov rax,-1; shr rax,cl; ret` builds a mask of the low `64 - cl` bits,
/// where the text's `-1 >> n` shifted an `int` arithmetically and stayed
/// all ones.
#[test]
fn a_logical_shift_of_all_ones_shifts_in_zeros() {
    let code = [
        0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, // ASM: mov rax, -1
        0x48, 0xd3, 0xe8, // ASM: shr rax, cl
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("0xffffffffffffffff >> "), "{text}");
}

/// A byte loaded and compared after a subtraction compares unsigned, as
/// the machine does.
///
/// `movzx eax,byte [rcx]; sub rax,12; cmp rax,2; jb L; xor eax,eax; ret;
/// L: mov eax,1; ret` tests the byte for 12 or 13. `*(uint8_t*)a1 - 12`
/// is an `int` in C, negative below 12, and compared signed it held for
/// every such byte.
#[test]
fn a_loaded_byte_compares_its_difference_unsigned() {
    let code = [
        0x0f, 0xb6, 0x01, // ASM: movzx eax, byte [rcx]
        0x48, 0x83, 0xe8, 0x0c, // ASM: sub rax, 12
        0x48, 0x83, 0xf8, 0x02, // ASM: cmp rax, 2
        0x72, 0x03, // ASM: jb 0x140001010
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(
        text.contains("(uint64_t)(*(uint8_t*)a1 - 12) < 2"),
        "{text}"
    );
}

/// A compare of the low halves of two 64-bit values compares only them.
///
/// `cmp ecx,edx; ja L; xor eax,eax; ret; L: mov eax,1; ret` orders the low
/// 32 bits of `a1` and `a2`, where the text once compared the whole
/// parameters and took the other branch whenever their high halves
/// decided; read only so, both are `uint32_t`.
#[test]
fn a_compare_of_low_halves_compares_only_them() {
    let code = [
        0x39, 0xd1, // ASM: cmp ecx, edx
        0x77, 0x03, // ASM: ja 0x140001007
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(uint32_t a1, uint32_t a2)"), "{text}");
}

/// A call to a compiler's clone names it as C can: GCC's
/// `helper.constprop.0` reads `helper_constprop_0`, so the text and the
/// declaration the unit gives it are valid identifiers.
#[test]
fn a_clone_s_dotted_name_reads_as_a_c_identifier() {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x1_4000_1020
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([0x8d, 0x41, 0x01, 0xc3]); // ASM: lea eax, [rcx + 1]; ret
    let mut p = program64(&code);
    p.symbols.push(Symbol {
        name: "helper.constprop.0".to_owned(),
        addr: 0x1_4000_1020,
        kind: SymbolKind::Local,
    });
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("helper_constprop_0("), "{text}");
    assert!(!text.contains("helper.constprop"), "{text}");
}

/// A global the C library exports is declared at the type it gives the
/// object of that name.
///
/// `mov rax,[rip+stdout]; ret` reads the copy of `stdout` an ELF keeps in
/// its own data: the text declares `FILE *stdout;`, not `uint64_t
/// stdout;`.
#[test]
fn a_library_object_is_declared_at_its_library_type() {
    let p = program64_with_globals(&READ_GLOBAL, false, &[("stdout", 0x1_4000_3000)]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("FILE *stdout;"), "{text}");
    assert!(text.contains("return stdout;"), "{text}");
}

/// A global in `.bss` is a declared variable like one in `.data`.
///
/// `mov rax,[rip+stdout]; ret` where the copy of `stdout` sits in a
/// section the file holds no bytes for: the text returns `stdout`, not
/// `*(uint64_t*)&stdout`.
#[test]
fn a_zero_filled_global_is_a_variable() {
    let p = program64_with_globals(&READ_GLOBAL, true, &[("stdout", 0x1_4000_3000)]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("FILE *stdout;"), "{text}");
    assert!(text.contains("return stdout;"), "{text}");
}

/// A global read at two widths is one variable, declared at the first.
///
/// `mov rax,[rip+g]; mov ecx,[rip+g]; add rax,rcx; ret` reads the same
/// eight bytes whole and then their low half: one declaration, the second
/// read through its address, as C reads part of an object.
#[test]
fn a_global_read_at_two_widths_is_declared_once() {
    let code = [
        0x48, 0x8b, 0x05, 0xf9, 0x1f, 0x00, 0x00, // ASM: mov rax,[rip+0x1ff9]
        0x8b, 0x0d, 0xf3, 0x1f, 0x00, 0x00, // ASM: mov ecx,[rip+0x1ff3]
        0x48, 0x01, 0xc8, // ASM: add rax,rcx
        0xc3, // ASM: ret
    ];
    let p = program64_with_globals(&code, false, &[("counter", 0x1_4000_3000)]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert_eq!(text.matches(" counter;").count(), 1, "{text}");
    assert!(text.contains("uint64_t counter;"), "{text}");
    assert!(text.contains("*(uint32_t*)&counter"), "{text}");
}

/// A read of one element of a stated array global is that element, and
/// the array is declared once, whole.
///
/// `mov eax,[rip+fds+4]; add eax,[rip+fds]; ret` reads both elements of
/// `int fds[2]`: the text declares `uint32_t fds[2];` and returns `fds[1] +
/// fds[0]`, where two scalars named after one array would not compile.
#[test]
fn a_stated_array_global_is_declared_whole() {
    use borer_engine::analysis::utypes::TypeExpr;
    use borer_engine::dwarf::Global;
    let code = [
        0x8b, 0x05, 0xfe, 0x1f, 0x00, 0x00, // ASM: mov eax,[rip+0x1ffe]
        0x03, 0x05, 0xf4, 0x1f, 0x00, 0x00, // ASM: add eax,[rip+0x1ff4]
        0xc3, // ASM: ret
    ];
    let mut p = program64_with_globals(&code, true, &[("fds", 0x1_4000_3000)]);
    p.debug_globals = vec![Global {
        name: "fds".to_owned(),
        addr: Some(0x1_4000_3000),
        type_name: Some("int[]".to_owned()),
        ty: Some(TypeExpr::Array(Box::new(TypeExpr::I32), 2)),
    }];
    let text = decompiled(&p, 0x1_4000_1000);
    assert_eq!(text.matches("fds[2];").count(), 1, "{text}");
    assert!(text.contains("uint32_t fds[2];"), "{text}");
    assert!(text.contains("fds[1]") && text.contains("fds[0]"), "{text}");
}

/// A global's equality ends where memory changes.
///
/// After `cmp dword [g],5; jne` the block starts under `g == 5`. Its `mov
/// dword [g],7` changes `g`, and so may its `mov [rdx],eax`, whose pointer
/// can be `&g`: a read of `g` after either is the read it is, where the
/// text returned 5.
#[test]
fn a_global_read_after_a_store_is_not_what_the_branch_compared() {
    let own: &[u8] = &[
        0x83, 0x3d, 0xf9, 0x1f, 0x00, 0x00, 0x05, // ASM: cmp dword [rip+0x1ff9],5
        0x75, 0x11, // ASM: jne 0x14000101a
        0xc7, 0x05, 0xed, 0x1f, 0x00, 0x00, // ASM: mov dword [rip+0x1fed],7
        0x07, 0x00, 0x00, 0x00, // ASM: (the 7)
        0x8b, 0x05, 0xe7, 0x1f, 0x00, 0x00, // ASM: mov eax,[rip+0x1fe7]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let through: &[u8] = &[
        0x83, 0x3d, 0xf9, 0x1f, 0x00, 0x00, 0x05, // ASM: cmp dword [rip+0x1ff9],5
        0x75, 0x09, // ASM: jne 0x140001012
        0x89, 0x02, // ASM: mov [rdx],eax
        0x8b, 0x05, 0xef, 0x1f, 0x00, 0x00, // ASM: mov eax,[rip+0x1fef]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    for code in [own, through] {
        let p = program64_with_globals(code, false, &[]);
        let a = Analysis::compute(&p);
        let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
        assert!(text.contains("\nreturn g32_140003000;\n"), "{text}");
        replays_clean(&p, &a, &[0x1_4000_1000]);
    }
}

/// A compare of a register's low half says nothing of the rest of it.
///
/// `cmp ecx,-1; jne X; mov [rdx],rcx` stores `rcx` whole, its upper half
/// whatever the caller left there. Read as a fact of the whole register,
/// the compare made the store `-1` at 64 bits, which the binary writes
/// only when it was handed all ones. A read no wider than the compare is
/// still the constant: after `mov eax,ecx; cmp eax,5`, `mov [rdx],rax`
/// stores the 5 the 32-bit move left in `rax`, its upper half clear. A
/// value that reads the bits above the compare, the `rcx >> 32` kept in
/// `rax`, keeps the variable.
#[test]
fn a_compare_of_a_registers_low_half_says_nothing_of_the_rest() {
    let whole = [
        0x83, 0xf9, 0xff, // ASM: cmp ecx,-1
        0x75, 0x06, // ASM: jne 0x14000100b
        0x48, 0x89, 0x0a, // ASM: mov [rdx],rcx
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&whole), 0x1_4000_1000);
    assert!(text.contains("\n*(uint64_t*)a2 = a1;\n"), "{text}");
    let low = [
        0x89, 0xc8, // ASM: mov eax,ecx
        0x83, 0xf8, 0x05, // ASM: cmp eax,5
        0x75, 0x04, // ASM: jne 0x14000100b
        0x48, 0x89, 0x02, // ASM: mov [rdx],rax
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&low), 0x1_4000_1000);
    assert!(text.contains("\n*(uint64_t*)a2 = 5;\n"), "{text}");
    let above = [
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x48, 0xc1, 0xe8, 0x20, // ASM: shr rax,32
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x75, 0x05, // ASM: jne 0x140001011
        0x89, 0x02, // ASM: mov [rdx],eax
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&above), 0x1_4000_1000);
    assert!(text.contains("\n*(uint32_t*)a2 = a1 >> 32;\n"), "{text}");
}

/// A fact of a block's own temporary stays in its block.
///
/// `cmp qword [g],0; mov [h],rcx; je S` keeps `g` in a temporary across the
/// store, and its `je` compares that temporary with 0. `S: cmp qword
/// [i],7; mov [j],rdx; sete al; movzx eax,al; jmp T` keeps `i` in a
/// temporary of its own, which the dataflow numbers as it numbered the
/// first block's. Read on that number, the fact made `i` zero in `S`, and
/// `T` stored and returned `0 == 7` where the binary, run with `i` 7,
/// returns 1.
#[test]
fn a_fact_of_a_blocks_own_temporary_stays_in_its_block() {
    let code = [
        0x48, 0x83, 0x3d, 0xf8, 0x1f, 0x00, 0x00, 0x00, // ASM: cmp qword [rip+0x1ff8],0
        0x48, 0x89, 0x0d, 0xf9, 0x1f, 0x00, 0x00, // ASM: mov [rip+0x1ff9],rcx
        0x74, 0x03, // ASM: je 0x140001014
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0x48, 0x83, 0x3d, 0xf4, 0x1f, 0x00, 0x00, 0x07, // ASM: cmp qword [rip+0x1ff4],7
        0x48, 0x89, 0x15, 0xf5, 0x1f, 0x00, 0x00, // ASM: mov [rip+0x1ff5],rdx
        0x0f, 0x94, 0xc0, // ASM: sete al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax,al
        0xeb, 0x01, // ASM: jmp 0x14000102c
        0xcc, // ASM: int3
        0x89, 0x05, 0xee, 0x1f, 0x00, 0x00, // ASM: mov [rip+0x1fee],eax
        0xc3, // ASM: ret
    ];
    let mut p = program64_with_globals(&code, false, &[]);
    p.bytes[0x1010] = 7;
    let text = runs_agree(&p, 0x1_4000_1000);
    assert!(!text.contains("0 == 7"), "{text}");
}

/// A `lea` into a 32-bit register reads its registers as far as it keeps
/// their sum.
///
/// Under `ecx == 5`, `lea eax,[rcx+8]` is 13 whatever the upper half of
/// `rcx` holds: the low half of the sum is all `eax` takes. `lea
/// rax,[rcx+8]` keeps the whole sum, so it keeps the variable. Under `ecx
/// == -1` the sum carries out of the low half, which `eax` does not take:
/// 7, where the folded sum read `0x100000007`.
#[test]
fn a_lea_into_a_low_half_reads_its_registers_that_far() {
    let half = [
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x75, 0x04, // ASM: jne 0x140001009
        0x8d, 0x41, 0x08, // ASM: lea eax,[rcx+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&half), 0x1_4000_1000);
    assert!(text.contains("\nreturn 13;\n"), "{text}");
    let whole = [
        0x83, 0xf9, 0x05, // ASM: cmp ecx,5
        0x75, 0x0a, // ASM: jne 0x14000100f
        0x48, 0x8d, 0x41, 0x08, // ASM: lea rax,[rcx+8]
        0x48, 0x89, 0x02, // ASM: mov [rdx],rax
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&whole), 0x1_4000_1000);
    assert!(text.contains("\n*(uint64_t*)a2 = a1 + 8;\n"), "{text}");
    let carried = [
        0x83, 0xf9, 0xff, // ASM: cmp ecx,-1
        0x75, 0x04, // ASM: jne 0x140001009
        0x8d, 0x41, 0x08, // ASM: lea eax,[rcx+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&carried), 0x1_4000_1000);
    assert!(text.contains("\nreturn 7;\n"), "{text}");
}

/// A read under an equality reads the constant at the width of what was
/// compared.
///
/// `cmp word [g],-1; jne X; movzx eax, word [g]; ret` returns `0xffff`
/// where the two bytes are all ones. The decoder extends the immediate to
/// 64 bits, and read so the text returned `0xffffffffffffffff`.
#[test]
fn a_fact_of_a_narrow_global_reads_at_its_width() {
    let code = [
        0x66, 0x83, 0x3d, 0xf8, 0x1f, 0x00, 0x00, 0xff, // ASM: cmp word [rip+0x1ff8],-1
        0x75, 0x08, // ASM: jne 0x140001012
        0x0f, 0xb7, 0x05, 0xef, 0x1f, 0x00, 0x00, // ASM: movzx eax,word [rip+0x1fef]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64_with_globals(&code, false, &[]);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("\nreturn 0xffff;\n"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// An address folds no wider than the machine sums it.
///
/// 32-bit code wraps an address at 4 GiB: `xor ecx,ecx; mov eax,[ecx-4]`
/// reads `0xfffffffc`, where the sum taken at 64 bits read as a thread
/// slot. `lea rax,[ecx+8]` of 64-bit code wraps there too: under `ecx ==
/// -1` it is 7, where the sum read `0x100000007`.
#[test]
fn a_32_bit_address_agrees_with_the_emulator() {
    let wrapped = [
        0x31, 0xc9, // ASM: xor ecx,ecx
        0x8b, 0x41, 0xfc, // ASM: mov eax,[ecx-4]
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program32(&wrapped), 0x40_1000);
    assert!(
        text.contains("\nreturn *(uint32_t*)0xfffffffc;\n"),
        "{text}"
    );
    let prefixed = [
        0x83, 0xf9, 0xff, // ASM: cmp ecx,-1
        0x75, 0x06, // ASM: jne 0x14000100b
        0x67, 0x48, 0x8d, 0x41, 0x08, // ASM: lea rax,[ecx+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&prefixed), 0x1_4000_1000);
    assert!(
        text.contains(
            "
return 7;
"
        ),
        "{text}"
    );
}
