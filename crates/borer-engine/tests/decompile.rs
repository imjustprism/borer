//! Decompiler tests on the shared fixture (see `common`).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

mod common;
#[path = "common/decompiled.rs"]
mod decompiled;
#[path = "common/nebula.rs"]
mod nebula;

use borer_engine::analysis::decompile::enum_table;
use borer_engine::analysis::{
    Analysis, EnumSource, Overlay,
    decompile::{
        asserts_of, cleanup, decompile, decompile_all, decompile_scenario, enum_tables,
        enums_by_name, polish, skeleton,
    },
};
use common::fixture;
use decompiled::decompiled;
use nebula::nebula;

/// Three arms that name three literals under one value are a flag tested
/// three times, not a name table.
#[test]
fn one_value_under_every_name_is_not_a_table() {
    let body = "if (a1 == 0) {\n  return \"x\";\n}\nif (a1 == 0) {\n  return \"y\";\n}\nif (a1 == 0) {\n  return \"z\";\n}\n";
    assert!(enum_table(body, &[]).is_none());
    let real = "if (a1 == 1) {\n  return \"x\";\n}\nif (a1 == 2) {\n  return \"y\";\n}\nif (a1 == 3) {\n  return \"z\";\n}\n";
    assert_eq!(enum_table(real, &[]).map(|t| t.members.len()), Some(3));
}

/// Decompiles one fixture function with an empty overlay.
///
/// # Arguments
///
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or an empty string when decompilation fails.
fn dc(entry: u64) -> String {
    decompiled(&fixture(), entry)
}

/// Decompiles one fixture function with the Nebula pack loaded.
fn dc_nebula(entry: u64) -> String {
    let p = fixture();
    let a = Analysis::compute_with(&p, nebula());
    decompile(&p, &a, &Overlay::default(), entry).unwrap_or_default()
}

/// A callee some caller reads `rdx` after is noted as handing a second
/// value back, and one no caller reads is not.
///
/// The calling convention leaves `rdx` to the callee to clobber, so a read
/// before a write after the call wants the callee's own value there: the
/// note is what tells a reader the register is a second result and not
/// stale.
#[test]
fn a_callee_whose_callers_read_rdx_hands_it_back() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    // caller 0x401000: call PAIR; mov rbx,rdx; mov rax,rbx; ret
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    // PAIR 0x401020: mov eax,1; mov edx,2; ret
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xc3, // ASM: ret
    ]);
    code.resize(0x30, 0xcc);
    // SOLO 0x401030: mov eax,3; ret — called by a caller that ignores rdx
    code.extend_from_slice(&[
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: mov eax,3
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    // IGNORE 0x401040: call SOLO; ret
    code.extend_from_slice(&[
        0xe8, 0xeb, 0xff, 0xff, 0xff, // ASM: call 0x401030
        0xc3, // ASM: ret
    ]);
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
    let pair = decompiled(&p, 0x401_020);
    assert!(pair.contains("// hands back rdx"), "{pair}");
    let solo = decompiled(&p, 0x401_030);
    assert!(!solo.contains("hands back rdx"), "{solo}");
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
    // mov eax,[rcx]; sub rax,4; ret
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

/// A 32-bit load widened into a 64-bit range ladder keeps its unsigned
/// reading.
///
/// `mov eax,[rdx]; add rax,-29; sub rax,2; jb` tests the widened value for
/// 29 or 30, and the wrap the compare's unsigned treatment adds says so
/// whatever the cast inside spells.
///
/// # Panics
///
/// When the range reads signed.
#[test]
fn a_widened_range_ladder_compares_unsigned() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    // mov eax,[rdx]; add rax,-29; sub rax,2; jb L; xor eax,eax; ret; L: mov eax,1; ret
    let code = [
        0x8b, 0x02, // ASM: mov eax,[rdx]
        0x48, 0x83, 0xc0, 0xe3, // ASM: add rax,-29
        0x48, 0x83, 0xe8, 0x02, // ASM: sub rax,2
        0x72, 0x03, // ASM: jb +3
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
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
        text.contains("(uint64_t)") && text.contains("< 2"),
        "the unsigned wrap: {text}"
    );
}

/// A call to a callee that hands `rdx` back renders its second result as
/// its own assignment under the callee's name with a `__rdx` suffix.
///
/// The register the caller reads after the call is set by the text, and
/// the interpreter answers it from the call it is the second half of.
///
/// # Panics
///
/// When the second result is not rendered.
#[test]
fn a_second_result_renders_as_its_own_assignment() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    // caller 0x401000: call PAIR; mov rbx,rdx; mov rax,rbx; ret
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    // PAIR 0x401020: mov eax,1; mov edx,2; ret
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xc3, // ASM: ret
    ]);
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
    let text = decompiled(&p, 0x401_000);
    assert!(
        text.contains("sub_401020__rdx"),
        "the second result: {text}"
    );
}

/// An argument register an earlier call left unknown does not drop the
/// arguments set behind it.
///
/// `call SPLIT; mov rcx,rax; mov r8,-1; call THREE; ret`, where `SPLIT`
/// returns only in `rax` and `THREE` reads `rcx`, `rdx` and `r8`: `rdx` is
/// the first call's unknown second result, and the text names the register
/// rather than closing the list at it, so `r8`'s `-1` survives as the third
/// argument.
#[test]
fn an_unknown_second_result_does_not_drop_the_set_arguments_behind_it() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xc1, // ASM: mov rcx,rax
        0x49, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, // ASM: mov r8,-1
        0xe8, 0x1c, 0x00, 0x00, 0x00, // ASM: call 0x401030
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax,5
        0xc3, // ASM: ret
    ]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0x4c, 0x89, 0xc0, // ASM: mov rax,r8
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0x48, 0x01, 0xc8, // ASM: add rax,rcx
        0xc3, // ASM: ret
    ]);
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
    let text = decompiled(&p, 0x401_000);
    assert!(text.contains("sub_401030(rax, rdx, -1)"), "{text}");
}

/// A register written out under its own name, because its value is long
/// and read twice, is still the second argument of the call in the next
/// block.
///
/// `mov rdx,[rcx+r8*8+0x10]; mov r9,rdx; test rdx,rdx; je L; mov ecx,7;
/// call 0x140001040; L: ret`: the load is too long to inline for the two
/// reads its block makes, so `rdx = …` is written out before the test; the
/// callee, `mov rax,rdx; add rax,rcx; ret`, reads both argument registers,
/// and `rdx` is no parameter of the caller.
#[test]
fn a_register_written_out_before_the_call_is_still_its_argument() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0x4a, 0x8b, 0x54, 0xc1, 0x10, 0x4c, 0x8b, 0xca, 0x48, 0x85, 0xd2, 0x74, 0x0a, 0xb9, 0x07,
        0x00, 0x00, 0x00, 0xe8, 0x29, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x48, 0x8b, 0xc2, 0x48, 0x03, 0xc1, 0xc3]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![Section::mapped(
            ".text",
            0x1_4000_1000,
            0,
            0x1000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("rdx = ((uint64_t*)(a1 + 0x10))[a3];"),
        "{text}"
    );
    assert!(text.contains("sub_140001040(7, rdx)"), "{text}");
}

/// A class's field names are read from its methods once: the second
/// call answers from the memo on the analysis, with the same names.
#[test]
fn field_names_are_read_once_per_class() {
    use borer_engine::analysis::classes::field_names;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let first = field_names(&p, &a, &o, "Nothing::Here");
    let second = field_names(&p, &a, &o, "Nothing::Here");
    assert_eq!(first, second);
    assert_eq!(a.derived.held("field_names"), 1, "{:?}", a.derived);
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
        0x48, 0x89, 0xf9, // mov rcx,rdi
        0x48, 0xf7, 0xd9, // neg rcx
        0x48, 0x0f, 0x48, 0xcf, // cmovs rcx,rdi
        0x4d, 0x89, 0xca, // mov r10,r9
        0x46, 0x8d, 0x0c, 0x29, // lea r9d,[rcx+r13]
        0x4d, 0x89, 0xd1, // mov r9,r10
        0xc0, 0xfb, 0x07, // sar bl,7
        0xd3, 0xe6, // shl esi,cl
        0x44, 0x89, 0xc0, // mov eax,r8d
        0x31, 0xd2, // xor edx,edx
        0x41, 0xf7, 0xf3, // div r11d
        0x49, 0x89, 0xc4, // mov r12,rax
        0x44, 0x89, 0xf0, // mov eax,r14d
        0x99, // cdq
        0xf7, 0xff, // idiv edi
        0x89, 0xf8, // mov eax,edi
        0xf7, 0xeb, // imul ebx
        0x41, 0x89, 0xd7, // mov r15d,edx
        0x88, 0xd8, // mov al,bl
        0xf6, 0xe9, // imul cl
        0x4c, 0x3b, 0xe9, // cmp r13,rcx
        0xff, 0xc0, // inc eax
        0x4d, 0x0f, 0x43, 0xf5, // cmovae r14,r13
        0x0f, 0xa3, 0xc8, // bt eax,ecx
        0x0f, 0x92, 0xc0, // setb al
        0x31, 0xc9, // xor ecx,ecx
        0x4c, 0x0f, 0xa5, 0xca, // shld rdx,r9,cl
        0x4c, 0x0f, 0xad, 0xc6, // shrd rsi,r8,cl
        0xc3, // ret
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
    let code: &[u8] = &[
        0x48, 0x89, 0xf8, // mov rax,rdi
        0x48, 0x99, // cqo
        0x48, 0xf7, 0xfe, // idiv rsi
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains(" / "), "{text}");
}

/// A signed division by a constant, as a compiler spells it with the high
/// half of a signed multiply, reads as the division.
#[test]
fn a_signed_magic_division_reads_as_the_division() {
    let code: &[u8] = &[
        0xb8, 0x1f, 0x85, 0xeb, 0x51, // mov eax,0x51eb851f
        0xf7, 0xe9, // imul ecx
        0xc1, 0xfa, 0x05, // sar edx,5
        0x8b, 0xc2, // mov eax,edx
        0xc1, 0xe8, 0x1f, // shr eax,31
        0x03, 0xc2, // add eax,edx
        0xc3, // ret
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
        0xfd, // std
        0xb9, 0x04, 0x00, 0x00, 0x00, // mov ecx,4
        0x48, 0x8d, 0x74, 0x24, 0xc0, // lea rsi,[rsp-0x40]
        0x48, 0x8d, 0x7c, 0x24, 0xe0, // lea rdi,[rsp-0x20]
        0xf3, 0xa4, // rep movsb
        0x48, 0xa5, // movsq
        0xaa, // stosb
        0xfc, // cld
        0xb9, 0x02, 0x00, 0x00, 0x00, // mov ecx,2
        0xf3, 0x48, 0xab, // rep stosq
        0xa4, // movsb
        0xc3, // ret
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
        0x56, // push rsi
        0x57, // push rdi
        0x4a, 0x8d, 0x74, 0x02, 0xff, // lea rsi,[rdx+r8-1]
        0x4a, 0x8d, 0x7c, 0x01, 0xff, // lea rdi,[rcx+r8-1]
        0x4c, 0x89, 0xc1, // mov rcx,r8
        0xfd, // std
        0xf3, 0xa4, // rep movsb
        0xfc, // cld
        0x5f, // pop rdi
        0x5e, // pop rsi
        0xc3, // ret
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
    let code: &[u8] = &[
        0x85, 0xc9, // test ecx,ecx
        0x74, 0x01, // je +1
        0xfd, // std
        0xf3, 0xa4, // rep movsb
        0xfc, // cld
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("direction flag unknown"), "{text}");
    assert!(text.contains("memcpy("), "{text}");
}

/// Builds a 64-bit PE-shaped program of `code` at 0x140001000 with no
/// symbols.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
fn program64(code: &[u8]) -> borer_engine::program::Program {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![Section::mapped(
            ".text",
            0x1_4000_1000,
            0,
            0x1000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    p
}

/// The frame idiom `mov rax, rsp` is no result: a function whose one
/// path to `ret` writes rax nowhere else returns nothing.
///
/// `mov rax,rsp; mov [rax+8],rbx; sub rsp,0x28; test ecx,ecx; je L; call
/// 0x140001040; L: add rsp,0x28; mov rbx,[rsp+8]; ret`; the callee `mov
/// eax,1; ret`.
#[test]
fn the_frame_idiom_returns_nothing() {
    let mut code = vec![
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x58, 0x08, 0x48, 0x83, 0xec, 0x28, 0x85, 0xc9, 0x74, 0x05,
        0xe8, 0x2c, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0x48, 0x8b, 0x5c, 0x24, 0x08, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains("retaddr"), "{text}");
    assert!(text.contains("return;"), "{text}");
}

/// A call site's scan follows a jump within the caller.
///
/// `call 0x140001040; jmp L; int3; L: xor eax,eax; ret` overwrites the
/// result unread, so the callee `call 0x140001060; ret`, which hands back
/// what `mov eax,1; ret` left, returns nothing anyone reads.
#[test]
fn a_call_site_scan_follows_a_jump() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, 0xeb, 0x01, 0xcc, 0x33, 0xc0, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
}

/// A call site's scan goes down both sides of a branch.
///
/// `call 0x140001040; test ebx,ebx; je L; xor eax,eax; ret; L: mov eax,2;
/// ret` overwrites the result on each, so the callee `call 0x140001060;
/// ret` returns nothing anyone reads.
#[test]
fn a_call_site_scan_follows_both_sides_of_a_branch() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, 0x85, 0xdb, 0x74, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x02, 0x00,
        0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
}

/// A double handed back in xmm0 is a result, though nothing writes rax.
///
/// `call 0x140001020; movsd [rdx],xmm0; ret` reads xmm0 after calling the
/// wrapper `sub rsp,0x28; call 0x140001040; add rsp,0x28; ret`, which hands
/// on what `test rcx,rcx; jne L; xorps xmm0,xmm0; jmp E; L: cvtsi2sd
/// xmm0,rcx; E: ret` leaves there: both return a double.
#[test]
fn a_double_in_xmm0_is_a_result() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x85, 0xc9, 0x75, 0x05, 0x0f, 0x57, 0xc0, 0xeb, 0x05, 0xf2, 0x48, 0x0f, 0x2a, 0xc1,
        0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    for entry in [0x1_4000_1020, 0x1_4000_1040] {
        let f = a.function(entry).map(|f| (f.returns_value, f.ret_float));
        assert_eq!(f, Some((Some(true), Some(64))), "{entry:#x}");
    }
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1040).unwrap_or_default();
    assert!(text.contains("// signature: double "), "{text}");
    assert!(text.contains("return (double)"), "{text}");
    assert!(!text.contains("return;"), "{text}");
    let wrapper = decompile(&p, &a, &Overlay::default(), 0x1_4000_1020).unwrap_or_default();
    assert!(wrapper.contains("// signature: double "), "{wrapper}");
    assert!(wrapper.contains("return sub_140001040("), "{wrapper}");
}

/// A double reaching the exit past a check is a result, never the check's.
///
/// `call 0x140001020; movsd [rdx],xmm0; ret` reads xmm0 after calling the
/// wrapper `sub rsp,0x28; call 0x140001040; call 0x140001060; add
/// rsp,0x28; ret`, whose double from `cvtsi2sd xmm0,rcx; ret` passes the
/// check `cmp rcx,rdx; jne F; ret; F: int3`, which touches no register a
/// result comes back in: the leaf takes the double's type, the wrapper
/// returns a value, and its text never returns the check's result.
#[test]
fn a_double_past_a_check_is_a_result() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x48,
        0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x48, 0x3b, 0xca, 0x75, 0x01, 0xc3, 0xcc]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let leaf = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(leaf, Some(Some(64)));
    let wrapper = a.function(0x1_4000_1020).map(|f| f.returns_value);
    assert_eq!(wrapper, Some(Some(true)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1020).unwrap_or_default();
    assert!(!text.contains("return sub_140001060"), "{text}");
}

/// A function whose double passes a check on its way out returns that
/// double, typed so: the check leaves `xmm0` as it found it, so the double
/// is still there at the `ret`.
///
/// The wrapper of [`a_double_past_a_check_is_a_result`], `sub rsp,0x28;
/// call 0x140001040; call 0x140001060; add rsp,0x28; ret`, keeps the
/// leaf's double across the check `cmp rcx,rdx; jne F; ret; F: int3`.
#[test]
fn a_double_past_a_check_types_its_function() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x48,
        0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x48, 0x3b, 0xca, 0x75, 0x01, 0xc3, 0xcc]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let wrapper = a.function(0x1_4000_1020).map(|f| f.ret_float);
    assert_eq!(wrapper, Some(Some(64)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1020).unwrap_or_default();
    assert!(text.contains("// signature: double "), "{text}");
    assert!(text.contains("xmm0 = sub_140001040("), "{text}");
    assert!(text.contains("return xmm0;"), "{text}");
}

/// What a float function's callee leaves in rax is no result.
///
/// `call 0x140001020; movsd [rdx],xmm0; ret` takes a double from `sub
/// rsp,0x28; call 0x140001040; xorps xmm0,xmm0; add rsp,0x28; ret`, whose
/// call hands rax on unread to its `ret`; the callee there, `sub rsp,0x28;
/// call 0x140001060; add rsp,0x28; ret`, hands back only what `mov dword
/// [rcx],0; mov eax,5; ret` left, so it returns nothing.
#[test]
fn rax_handed_to_a_float_function_is_no_result() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0x0f, 0x57, 0xc0, 0x48, 0x83, 0xc4,
        0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, 0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let float = a.function(0x1_4000_1020).map(|f| f.ret_float);
    assert_eq!(float, Some(Some(64)));
    let inner = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(inner, Some(Some(false)));
}

/// A function forwarding a double returns it, whoever reads it.
///
/// `call 0x140001020; call 0x140001060; movsd [rdx],xmm0; ret` reads the
/// double `cvtsi2sd xmm0,rcx; ret` leaves; `jmp 0x140001060` forwards it
/// though its one caller, `call 0x140001040; xor eax,eax; ret`, drops it.
#[test]
fn forwarding_a_double_returns_it() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, 0xe8, 0x56, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0x33, 0xc0, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let forward = a
        .function(0x1_4000_1040)
        .map(|f| (f.returns_value, f.ret_float));
    assert_eq!(forward, Some((Some(true), Some(64))));
}

/// What a function returning a double leaves in rax is nothing.
///
/// `call 0x140001040; movsd [rdx],xmm0; ret` reads the double `cvtsi2sd
/// xmm0,rcx; ret` leaves, so the entry, `sub rsp,0x28; call 0x140001020;
/// call 0x140001040; addsd xmm0,xmm0; add rsp,0x28; ret`, which nothing
/// calls, hands back no value in rax.
#[test]
fn a_float_callee_leaves_nothing_in_rax() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xe8, 0x32, 0x00, 0x00, 0x00, 0xf2,
        0x0f, 0x58, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let leaf = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(leaf, Some(Some(64)));
    let entry = a.function(0x1_4000_1000).map(|f| f.returns_value);
    assert_eq!(entry, Some(Some(false)));
}

/// A float written to xmm0 and stored is no result when no caller reads
/// it: `movsd xmm0,[rcx]; addsd xmm0,xmm0; movsd [rcx],xmm0; ret` called
/// by `call 0x140001040; xor eax,eax; ret` stays `void`.
#[test]
fn a_float_no_caller_reads_is_no_result() {
    let mut code = vec![0xe8, 0x3b, 0x00, 0x00, 0x00, 0x33, 0xc0, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x10, 0x01, 0xf2, 0x0f, 0x58, 0xc0, 0xf2, 0x0f, 0x11, 0x01, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(f, Some(None));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1040).unwrap_or_default();
    assert!(text.contains("// signature: void "), "{text}");
}

/// A call through the result reads it: after `call 0x140001040; call
/// [rax+0x10]; ret` the callee `mov eax,1; ret` returns a value.
#[test]
fn a_call_through_the_result_reads_it() {
    let mut code = vec![0xe8, 0x3b, 0x00, 0x00, 0x00, 0xff, 0x50, 0x10, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(true)));
}

/// A tail jump hands the callee's result on.
///
/// `call 0x140001060; call 0x140001040; mov [rcx],eax; ret` reads what
/// `jmp 0x140001060` hands back, which is the `mov eax,7; ret` of the
/// function jumped to, so that one returns a value though its one call
/// drops the result.
#[test]
fn a_tail_jump_hands_the_result_on() {
    let mut code = vec![
        0xe8, 0x5b, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x89, 0x01, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1060).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(true)));
}

/// Handing back what a callee returning nothing left returns nothing.
///
/// `jmp 0x140001060` over `test ecx,ecx; je L; mov eax,1; mov [rdx],eax;
/// L: ret`, which reaches its `ret` without writing rax, is `void` and
/// drops the `return` of the tail call, whatever its callers do: its one
/// caller, `call 0x140001060; call 0x140001040; ret`, hands its rax on to
/// callers unknown.
#[test]
fn passing_on_a_callee_that_returns_nothing_returns_nothing() {
    let mut code = vec![
        0xe8, 0x5b, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, 0x74, 0x07, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x89, 0x02, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1040).unwrap_or_default();
    assert!(text.contains("// signature: void "), "{text}");
    assert!(!text.contains("return sub_"), "{text}");
}

/// A prologue store of `xmm6`, callee-saved under the Microsoft x64
/// convention, is a save and not a local, even where a call would
/// reload the locals around it.
///
/// `sub rsp,0x38; movaps [rsp+0x20],xmm6; lea rcx,[rsp+0x10]; call
/// 0x140001040; xorps xmm6,xmm6; addss xmm6,xmm0; movaps xmm0,xmm6;
/// movaps xmm6,[rsp+0x20]; add rsp,0x38; ret`; the callee `mov eax,1;
/// ret`.
#[test]
fn a_saved_xmm_register_is_not_a_local() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x38, 0x0f, 0x29, 0x74, 0x24, 0x20, 0x48, 0x8d, 0x4c, 0x24, 0x10, 0xe8,
        0x2d, 0x00, 0x00, 0x00, 0x0f, 0x57, 0xf6, 0xf3, 0x0f, 0x58, 0xf0, 0x0f, 0x28, 0xc6, 0x0f,
        0x28, 0x74, 0x24, 0x20, 0x48, 0x83, 0xc4, 0x38, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("uint128_t"), "{text}");
    assert!(!text.contains("= xmm6;"), "{text}");
}

/// Two paths each ending in a call through a table, joining at the
/// epilogue of a function nobody calls: the function returns nothing,
/// and neither call's result is assigned to the return register.
///
/// `sub rsp,0x28; mov r10,[rcx]; test edx,edx; je L; call [r10+8]; jmp
/// M; L: call [r10+0x10]; M: add rsp,0x28; ret`.
#[test]
fn a_dead_result_before_a_bare_return_is_dropped() {
    let code = [
        0x48, 0x83, 0xec, 0x28, 0x4c, 0x8b, 0x11, 0x85, 0xd2, 0x74, 0x06, 0x41, 0xff, 0x52, 0x08,
        0xeb, 0x04, 0x41, 0xff, 0x52, 0x10, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("return;"), "{text}");
    assert!(!text.contains("rax"), "{text}");
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

/// A byte moved into an argument register right before a call is the
/// whole argument.
///
/// `mov r8b,1; mov edx,2; mov ecx,3; call 0x140001020; ret` passes `1`,
/// not a merge with what `r8` held; the callee is `movzx eax,r8b; ret`.
#[test]
fn a_byte_moved_into_an_argument_register_is_the_argument() {
    let mut code = vec![
        0x41, 0xb0, 0x01, 0xba, 0x02, 0x00, 0x00, 0x00, 0xb9, 0x03, 0x00, 0x00, 0x00, 0xe8, 0x0e,
        0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x41, 0x0f, 0xb6, 0xc0, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("sub_140001020(3, 2, 1)"), "{text}");
}

/// An argument register read on a path no call precedes is a parameter,
/// though a call sits before the read in the image.
///
/// `test ecx,ecx; je L; call 0x140001020; ret; L: mov eax,[r8+8]; ret`
/// reads `r8` on the second path; the callee is `mov eax,1; ret`.
#[test]
fn a_register_read_on_a_call_free_path_is_a_parameter() {
    let mut code = vec![
        0x85, 0xc9, 0x74, 0x06, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xc3, 0x41, 0x8b, 0x40, 0x08, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("a3 + 8") || text.contains("a3->"), "{text}");
    assert!(!text.contains("r8"), "{text}");
}

/// A callee that homes its argument registers for `va_start` is
/// variadic.
///
/// A caller passes what it set past the fixed arguments and nothing by
/// name, forwards none of them as its own parameters, and the callee's
/// own signature ends in `...`.
///
/// The callee at 0x140001040 is `mov rax,rsp; mov [rax+8],rcx; mov
/// [rax+10h],rdx; mov [rax+18h],r8; mov [rax+20h],r9; lea rax,[rax+10h];
/// ret`; the entry sets `ecx` and `edx`, calls it, then calls the
/// function at 0x140001020, which sets only `ecx` before calling it.
#[test]
fn a_variadic_callee_takes_what_the_caller_set() {
    let mut code = vec![
        0xb9, 0x07, 0x00, 0x00, 0x00, 0xba, 0x08, 0x00, 0x00, 0x00, 0xe8, 0x31, 0x00, 0x00, 0x00,
        0xe8, 0x0c, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb9, 0x07, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x48, 0x08, 0x48, 0x89, 0x50, 0x10, 0x4c, 0x89, 0x40, 0x18,
        0x4c, 0x89, 0x48, 0x20, 0x48, 0x8d, 0x40, 0x10, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let both = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(both.contains("sub_140001040(7, 8)"), "{both}");
    let one = decompile(&p, &a, &o, 0x1_4000_1020).unwrap_or_default();
    assert!(one.contains("sub_140001040(7)"), "{one}");
    assert!(!one.contains("rdx"), "{one}");
    assert!(one.contains("sub_140001020()"), "{one}");
    let callee = decompile(&p, &a, &o, 0x1_4000_1040).unwrap_or_default();
    assert!(
        callee.contains("sub_140001040(uint64_t a1, ...)"),
        "{callee}"
    );
}

/// A thunk that sets one argument register and jumps on forwards the
/// rest, so its caller passes them.
///
/// The entry is both the target and the caller: `cmp ecx,1; jne L; mov
/// eax,edx; add eax,ecx; ret; L: mov ecx,7; mov edx,5; call 0x140001020;
/// ret`, and the thunk is `mov ecx,1; jmp 0x140001000`.
#[test]
fn a_thunk_that_sets_a_register_forwards_the_rest() {
    let mut code = vec![
        0x83, 0xf9, 0x01, 0x75, 0x05, 0x8b, 0xc2, 0x03, 0xc1, 0xc3, 0xb9, 0x07, 0x00, 0x00, 0x00,
        0xba, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x07, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb9, 0x01, 0x00, 0x00, 0x00, 0xe9, 0xd6, 0xff, 0xff, 0xff]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("sub_140001020(7, 5)"), "{text}");
}

/// A frame pointer set from `rax` after `mov rax, rsp` places a read
/// through it against the entry stack pointer: the byte at `[rbp+0x40]`
/// is the first stack argument.
///
/// `mov rax,rsp; mov [rax+8],rbx; push rbp; lea rbp,[rax-0x18]; sub
/// rsp,0x20; movzx eax,byte [rbp+0x40]; add rsp,0x20; pop rbp; mov
/// rbx,[rsp+8]; ret`.
#[test]
fn a_frame_pointer_set_from_the_rax_alias_places_stack_arguments() {
    let code = [
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x58, 0x08, 0x55, 0x48, 0x8d, 0x68, 0xe8, 0x48, 0x83, 0xec,
        0x20, 0x0f, 0xb6, 0x45, 0x40, 0x48, 0x83, 0xc4, 0x20, 0x5d, 0x48, 0x8b, 0x5c, 0x24, 0x08,
        0xc3,
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let stack_args = a.function(0x1_4000_1000).map(|f| f.stack_args);
    assert_eq!(stack_args, Some(1));
}

/// Builds a 64-bit program of `code` at 0x140001000 with `data` at
/// 0x140002000, read-only, and no symbols.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
/// * `data` - The bytes of `.rdata`, at most a page.
fn program64_with_data(code: &[u8], data: &[u8]) -> borer_engine::program::Program {
    use borer_engine::program::Section;
    let mut p = program64(code);
    p.bytes.resize(0x2000, 0);
    p.bytes[0x1000..0x1000 + data.len()].copy_from_slice(data);
    p.sections.push(Section::mapped(
        ".rdata",
        0x1_4000_2000,
        0x1000,
        0x1000,
        false,
        false,
    ));
    p
}

/// A method returning by hidden pointer with three declared parameters
/// needs five positions, one on the stack, so it has `this` though only
/// four registers are read.
///
/// `mov rax,[rcx]; mov [rdx],eax; mov eax,[rsp+0x28]; add eax,r9d; add
/// eax,r8d; mov [rdx+4],eax; lea r10,[rip+sig]; mov rax,rdx; ret` under
/// `class Util::String __cdecl Cls::Name(int,int,int)`.
#[test]
fn a_method_whose_positions_overflow_the_registers_has_this() {
    let code = [
        0x48, 0x8b, 0x01, 0x89, 0x02, 0x8b, 0x44, 0x24, 0x28, 0x41, 0x03, 0xc1, 0x41, 0x03, 0xc0,
        0x89, 0x42, 0x04, 0x4c, 0x8d, 0x15, 0xe7, 0x0f, 0x00, 0x00, 0x48, 0x8b, 0xc2, 0xc3,
    ];
    let p = program64_with_data(
        &code,
        b"class Util::String __cdecl Cls::Name(int,int,int)\0",
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("Cls::Name(Cls *this, Util::String *result, int a3, int a4, int a5)"),
        "{text}"
    );
}

/// A home slot the function uses as a local is `home_N`, not `arg_N`: a
/// write there changes no argument.
///
/// `sub rsp,0x28; mov dword [rsp+0x30],0x41554556; lea rcx,[rsp+0x30];
/// call 0x140001040; add rsp,0x28; ret`, the callee `mov eax,[rcx]; ret`.
#[test]
fn a_home_slot_used_as_a_local_is_named_home() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xc7, 0x44, 0x24, 0x30, 0x56, 0x45, 0x55, 0x41, 0x48, 0x8d, 0x4c,
        0x24, 0x30, 0xe8, 0x2a, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("home_0 = 'AUEV';"), "{text}");
    assert!(text.contains("sub_140001040(&home_0)"), "{text}");
    assert!(!text.contains("arg_0"), "{text}");
}

/// A wrapper that sets every argument register and jumps to a variadic
/// function is not variadic itself: its caller passes nothing.
///
/// `mov ecx,7; mov edx,8; call 0x140001020; call 0x140001040; ret`
/// calls `mov ecx,1; mov edx,2; mov r8d,3; mov r9d,4; jmp 0x140001040`,
/// which lands in a function that homes its registers for `va_start`
/// (called directly too, so it is a function of its own).
#[test]
fn a_wrapper_that_sets_every_register_is_not_variadic() {
    let mut code = vec![
        0xb9, 0x07, 0x00, 0x00, 0x00, 0xba, 0x08, 0x00, 0x00, 0x00, 0xe8, 0x11, 0x00, 0x00, 0x00,
        0xe8, 0x2c, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x02, 0x00, 0x00, 0x00, 0x41, 0xb8, 0x03, 0x00, 0x00,
        0x00, 0x41, 0xb9, 0x04, 0x00, 0x00, 0x00, 0xe9, 0x05, 0x00, 0x00, 0x00,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x48, 0x08, 0x48, 0x89, 0x50, 0x10, 0x4c, 0x89, 0x40, 0x18,
        0x4c, 0x89, 0x48, 0x20, 0x48, 0x8d, 0x40, 0x10, 0xc3,
    ]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("sub_140001020()"), "{text}");
}

/// The register a virtual call goes through is no argument.
///
/// `mov rax,rcx; mov r9d,edx; mov rcx,rax; mov r8,[rax]; call qword
/// [r8]; ret` calls through `a1`'s vtable, a slot nothing states the
/// arity of: the receiver goes first, `rdx` still holds the caller's own
/// `a2` and was not written for the call, and neither the vtable pointer
/// in `r8` nor the copy in `r9` is an argument.
#[test]
fn the_register_a_call_goes_through_is_no_argument() {
    let code = [
        0x48, 0x8b, 0xc1, 0x44, 0x8b, 0xca, 0x48, 0x8b, 0xc8, 0x4c, 0x8b, 0x00, 0x41, 0xff, 0x10,
        0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("a1->vtable[0]();"), "{text}");
}

/// A float parked in a home slot and read back as bits is a float
/// parameter: the callee takes `float a1` and the caller passes the
/// float, not `rcx`.
///
/// The caller is `movss xmm0,[rip+c]; call 0x140001040; ret` with `c`
/// holding 2.0f, the callee `movss [rsp+8],xmm0; mov eax,[rsp+8]; ret`.
#[test]
fn a_float_parked_in_a_home_slot_is_a_float_parameter() {
    // movss xmm0,[rip+0xff8]: eight bytes long, so the constant it reaches is
    // 0x140001008 + 0xff8, the first word of .rdata at 0x140002000.
    let mut code = vec![
        0xf3, 0x0f, 0x10, 0x05, 0xf8, 0x0f, 0x00, 0x00, 0xe8, 0x33, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xf3, 0x0f, 0x11, 0x44, 0x24, 0x08, 0x8b, 0x44, 0x24, 0x08, 0xc3,
    ]);
    let p = program64_with_data(&code, &2.0f32.to_le_bytes());
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let caller = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(caller.contains("sub_140001040(2."), "{caller}");
    assert!(!caller.contains("rcx"), "{caller}");
    let callee = decompile(&p, &a, &o, 0x1_4000_1040).unwrap_or_default();
    assert!(callee.contains("sub_140001040(float a1)"), "{callee}");
}

/// `mov eax,1; ret`: the constant flows straight into the return and no dead
/// `rax = 1;` line survives.
#[test]
fn leaf_function_constant_return() {
    let out = dc(0x1020);
    assert!(out.contains("return 1;"), "no folded return:\n{out}");
    assert!(
        !out.contains("rax = 1;"),
        "dead register copy survived:\n{out}"
    );
}

/// `main` renders both calls, a conditional, the `xor eax,eax` zero idiom as
/// `return 0;`, and no goto to the fall-through block after cleanup.
#[test]
fn main_calls_condition_and_zero_idiom() {
    let out = dc(0x1000);
    assert!(out.contains("sub_1020();"), "missing call A:\n{out}");
    assert!(out.contains("sub_1030();"), "missing call B:\n{out}");
    assert!(out.contains("if ("), "no conditional:\n{out}");
    assert!(
        out.contains("return 0;"),
        "xor-zero idiom not folded:\n{out}"
    );
    assert!(
        !out.contains("goto L_1009;"),
        "fallthrough goto survived:\n{out}"
    );
}

/// A bare `ret` becomes a plain `return;`.
#[test]
fn bare_ret_function() {
    let out = dc(0x10e0);
    assert!(out.contains("return;"), "no plain return:\n{out}");
}

/// `D` becomes a `switch (a1)` (the `movsxd` on the index must not leak)
/// with all cases, their bodies, and the default bound check.
#[test]
fn switch_function_cases() {
    let out = dc(0x1060);
    assert!(
        out.contains("switch (a1)"),
        "no switch construct (movsxd on the index must not leak):
{out}"
    );
    assert!(
        out.contains("case 0:"),
        "no case 0:
{out}"
    );
    assert!(
        out.contains("case 3:"),
        "no case 3:
{out}"
    );
    assert!(
        out.contains("return 1;") && out.contains("return 4;"),
        "case bodies missing:
{out}"
    );
    assert!(
        out.contains("if ("),
        "default bound-check lost:
{out}"
    );
}

/// `G`: `eax` is untouched on both paths of the branch, so the join keeps the
/// constant and the function returns 7.
#[test]
fn const_survives_join() {
    let out = dc(0x1130);
    assert!(
        out.contains("return 7;"),
        "join dropped the constant:\n{out}"
    );
}

/// `F` becomes a `for` loop; `cmp ecx,5; jge` is a signed 32-bit compare, so
/// the cast is the honest rendering on a `uint64_t` variable. No temporaries
/// and no back-edge goto survive.
#[test]
fn while_loop_structured() {
    let out = dc(0x1100);
    assert!(
        out.contains("for (rcx = 0; (int32_t)rcx < 5; rcx += 1)"),
        "no for sugar:\n{out}"
    );
    assert!(out.contains("rax += rcx;"), "loop body missing:\n{out}");
    assert!(!out.contains("tmp_"), "spurious temporaries:\n{out}");
    assert!(
        !out.contains("goto L_1107;"),
        "back-edge goto survived structuring:\n{out}"
    );
    assert!(out.contains("return rax;"), "return missing:\n{out}");
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

/// `K` is a loop; the inner `if (rbx != 0) return rax;` may fold into the
/// loop guard (`while (rax < 5 && rbx == 0)`), which is the same program. The
/// latch goto never survives.
#[test]
fn nested_if_inside_while() {
    let out = dc(0x1180);
    assert!(
        out.contains("for (rax = 0; (int32_t)rax < 5; rax += 1)") || out.contains("while ("),
        "no loop:
{out}"
    );
    assert!(
        out.contains("if (") || out.contains(" && "),
        "neither nested if nor merged guard:
{out}"
    );
    assert!(
        !out.contains("goto L_1185;"),
        "latch goto survived:
{out}"
    );
    assert!(
        out.contains("return rax;"),
        "no return:
{out}"
    );
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

/// `P`: the argument registers flow into the call as `Base::vfunc_1(10, 20);`
/// without redundant assignments, and the signature is `void`.
#[test]
fn call_arguments_rendered() {
    let out = dc(0x11c0);
    assert!(
        out.contains("Base::vfunc_1(10, 20);"),
        "call args missing:
{out}"
    );
    assert!(
        !out.contains("rcx = 10;"),
        "redundant arg assignment survived:
{out}"
    );
    assert!(
        !out.contains("rdx = 20;"),
        "redundant arg assignment survived:
{out}"
    );
    assert!(
        out.contains("// signature: uint64_t exported_p()")
            && out.contains("return Base::vfunc_1(10, 20);"),
        "P passes Q's result through (Q's result is read by another caller):
{out}"
    );
}

/// A value-returning leaf gets the width it writes, `uint32_t` for its
/// `mov eax, 1`; a bare `ret` gets `void`.
#[test]
fn value_returning_signature() {
    let out = dc(0x1020);
    assert!(
        out.contains("// signature: uint32_t sub_1020()"),
        "leaf signature wrong:
{out}"
    );
    let bare = dc(0x10e0);
    assert!(
        bare.contains("// signature: void sub_10e0()"),
        "void signature wrong:
{bare}"
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

/// `H`: `if (ecx == 0) goto ret; *a2 = ecx; ret:`. The `ret` block has two
/// predecessors, so it is the join, not the if-body: an inverted `if` with the
/// store, and exactly one `return` after it.
#[test]
fn if_body_with_shared_join_is_not_swallowed() {
    let out = dc(0x1150);
    assert!(
        out.contains("if (a1 != 0) {"),
        "inverted if expected:\n{out}"
    );
    assert!(
        out.contains("*(uint32_t*)a2 = a1;"),
        "store body missing:\n{out}"
    );
    assert_eq!(
        out.matches("return").count(),
        1,
        "return must appear once, after the if:\n{out}"
    );
}

/// `G`: the branch's only effect is `inc ecx`, dead at the return, so no empty
/// `if` survives and the constant still flows to the return.
#[test]
fn dead_if_body_is_dropped() {
    let out = dc(0x1130);
    assert!(!out.contains("if ("), "empty if survived:\n{out}");
    assert!(out.contains("return 7;"), "constant lost:\n{out}");
}

/// `test ecx,ecx; jz` renders as a plain zero test on `rcx` (read after a call,
/// so not a parameter), not as an `and`.
#[test]
fn test_same_register_simplifies() {
    let out = dc(0x1000);
    assert!(
        out.contains("rcx == 0") || out.contains("rcx != 0"),
        "test-same not simplified:
{out}"
    );
    assert!(
        !out.contains("& rcx"),
        "test-same rendered as an and:\n{out}"
    );
}

/// `W`: `mov ecx, 1; jmp A` renders as a tail call, `return sub_1020(...)`.
#[test]
fn tail_call_renders_as_return_call() {
    let out = dc(0x1240);
    assert!(out.contains("return sub_1020("), "{out}");
    assert!(!out.contains("return 1;"), "A's body leaked into W:\n{out}");
}

/// `X`: a function address and a string address passed as arguments render
/// as the function's name and the literal.
#[test]
fn function_pointer_and_string_arguments_are_named() {
    let out = dc(0x1250);
    assert!(
        out.contains("Base::vfunc_1(sub_10e0, \"hello, borer world\");"),
        "{out}"
    );
}

/// `FL`: scalar float loads, arithmetic, square root and a truncating
/// conversion render as typed C with a `float` register.
#[test]
fn scalar_float_arithmetic_renders_typed() {
    let out = dc(0x1300);
    assert!(
        !out.contains("uint128_t"),
        "vector register left untyped:
{out}"
    );
    assert!(
        out.contains("return (int32_t)sqrt((a1->field_0x0 + a1->field_0x4) * a1->field_0x8);"),
        "{out}"
    );
    assert!(
        !out.contains("/*"),
        "unmodeled instruction survived:\n{out}"
    );
}

/// `FL2`: `xorps` with the sign mask negates, `andps` with the magnitude mask
/// is `fabs`; the mask constants never appear.
///
/// `FL2` has no `ret` of its own and runs up to `FL3`, a function in its
/// own right. The walk once fell through into it and rendered both as one,
/// which is where the extra field accesses came from that earned `a1` a
/// layout; a fall-through into another function's start is now where a
/// function ends, so `FL2` is its own six instructions.
#[test]
fn float_sign_and_magnitude_masks_render_as_neg_and_fabs() {
    let out = dc(0x1320);
    assert!(
        out.contains("6 instructions"),
        "FL3 was absorbed again:
{out}"
    );
    assert!(out.contains("*(float*)a2 = -*(float*)a1;"), "{out}");
    assert!(
        out.contains("*(float*)(a2 + 4) = fabs(*(float*)(a1 + 4));"),
        "{out}"
    );
    assert!(!out.contains("0x2070") && !out.contains("0x2080"), "{out}");
}

/// `FL3`: integer-to-float and float-to-double conversions render as casts, a
/// double store is typed, and an unmodeled vector op becomes an intrinsic call.
#[test]
fn float_conversions_and_vector_intrinsics() {
    let out = dc(0x1340);
    assert!(
        out.contains("*(double*)a2 = (double)((float)a1 * (float)a1);"),
        "{out}"
    );
    assert!(
        out.contains("*(uint128_t*)(a2 + 0x10) = shufps(xmm1, ") && out.contains(", 0x1b);"),
        "{out}"
    );
    assert!(
        !out.contains("/*"),
        "unmodeled instruction survived:\n{out}"
    );
}

/// `FL`, `FL2` and `FR`: scalar-float blocks are checked against the
/// binary, not counted as float/vector; `FL3`, whose `shufps` is a packed
/// operation the text names as an intrinsic, still is.
#[test]
fn scalar_float_blocks_are_checked_not_counted() {
    use borer_engine::analysis::decompile::checked_header;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let header = |entry: u64| checked_header(&p, &a, &o, entry).unwrap_or_default();
    for entry in [0x1300, 0x1320] {
        assert_eq!(
            header(entry),
            "// checked vs binary: statements as emitted, 1/1 blocks x3 states; unchecked: later text passes",
            "{entry:#x}"
        );
    }
    assert_eq!(
        header(0x13f0),
        "// checked vs binary: statements as emitted, 2/2 blocks x3 states; unchecked: later text passes",
        "FR"
    );
    let fl3 = header(0x1340);
    assert!(
        fl3.contains("0/1 blocks") && fl3.contains("1 float/vector"),
        "FL3's packed shuffle stays out: {fl3}"
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
    assert!(out.contains("return tmp_"), "old value lost:\n{out}");
    assert!(
        out.contains(
            "((uint64_t*)(a1 + 8))[(int64_t)tmp_1 >> 6] |= (uint64_t)1 << (tmp_1 & 0x3f);"
        ),
        "{out}"
    );
    assert!(out.contains("a1->field_0x20 = a1->field_0x10;"), "{out}");
    assert!(out.contains("a1->field_0x30 = stmxcsr();"), "{out}");
    assert!(
        !out.contains("/*"),
        "unmodeled instruction survived:\n{out}"
    );
}

/// `AC`: the callee reads only its first argument register, so the call shows
/// one argument even though two were set up.
#[test]
fn call_arguments_stop_at_the_callee_arity() {
    let out = dc(0x13b0);
    assert!(out.contains("Glob::vfunc_1(1);"), "{out}");
    assert!(!out.contains("Glob::vfunc_1(1, 2)"), "{out}");
}

/// `D1`: the copy of the parameter into `rdi` stays symbolic across the call
/// (the parameter is `a2`, not the volatile register), so nothing is written
/// and the return reads the parameter.
///
/// The callee is a bare `ret`, so nothing states its arity, and `rcx` and
/// `rdx` hold the caller's own parameters, not values written for the
/// call: it takes none.
#[test]
fn parameter_copy_stays_symbolic_across_a_call() {
    let out = dc(0x1380);
    assert!(!out.contains("rdi ="), "{out}");
    assert!(out.contains("return a2;"), "{out}");
    assert!(out.contains("Base::vfunc_1();"), "{out}");
}

/// `E1`: on the edge where `rcx` is known to be zero, `rcx + 25` folds to `25`.
#[test]
fn equality_branch_makes_the_variable_a_constant_inside() {
    let out = dc(0x13c0);
    assert!(out.contains("return 25;"), "{out}");
    assert!(!out.contains("rcx + 25"), "{out}");
    assert!(out.contains("return 1;"), "{out}");
}

/// `FR`: a call whose result the next instruction reads from `xmm0` binds a
/// typed float result instead of leaving a stale register name.
#[test]
fn float_call_result_is_bound_to_xmm0() {
    let out = dc(0x13f0);
    assert!(out.contains("xmm0 = sub_1400();"), "{out}");
    assert!(out.contains("*(float*)rcx = xmm0;"), "{out}");
    assert!(out.contains("float xmm0;"), "{out}");
}

/// `CS`: the prologue save of `rbx` and its epilogue restore never render,
/// and the parameter copied into `rbx` survives the call as `a1`.
#[test]
fn callee_saved_register_saves_are_hidden() {
    let out = dc(0x13d0);
    assert!(
        !out.contains("arg_0 = rbx;") && !out.contains("home_0 = rbx;"),
        "save rendered:
{out}"
    );
    assert!(
        !out.contains("rbx = arg_0;") && !out.contains("rbx = home_0;"),
        "restore rendered:
{out}"
    );
    assert!(
        !out.contains("rbx ="),
        "parameter copy rendered:
{out}"
    );
    assert!(out.contains("return a1;"), "{out}");
}

/// `ES`: the address of a local passed in `r9` escapes although the callee
/// reads only `rcx`, so the local is stored before the call and reloaded
/// after it instead of staying the constant `0`.
#[test]
fn stack_address_in_an_uncounted_argument_register_escapes() {
    let out = dc(0x1410);
    assert!(out.contains("local_8 = 0;"), "{out}");
    assert!(out.contains("return local_8;"), "{out}");
    assert!(!out.contains("return 0;"), "{out}");
}

/// `CC`: a chain block whose condition is constant is not merged into the
/// guard as `a1 != 0 || 0 == 0`; its dead edge is pruned, so the merged form
/// left a `goto` to a block that was never emitted.
#[test]
fn constant_condition_block_is_not_merged_into_a_guard() {
    let out = dc(0x1430);
    for label in out.lines().filter_map(|l| l.trim().strip_prefix("goto L_")) {
        let label = label.trim_end_matches(';');
        assert!(
            out.contains(&format!("L_{label}:")),
            "dangling goto L_{label}:\n{out}"
        );
    }
    assert!(!out.contains("0 == 0"), "{out}");
    assert!(out.contains("return 0;"), "{out}");
}

/// `FJ`: `test eax, eax` on both edges into the join that reads the flags
/// is re-expressed over `rax`, so the flags agree at the join and the `sete`
/// lifts instead of staying an `/* asm */` comment.
#[test]
fn same_comparison_on_both_edges_survives_the_join() {
    let out = dc(0x1450);
    assert!(!out.contains("/* sete"), "{out}");
    assert!(out.contains("rax == 0"), "{out}");
}

/// `E2`: the fall-through edge of `test eax, eax; jne` makes `rax` zero, but
/// the block then loads `rax` and the store writes it out; the `lea` after
/// that reads the new `rax`, not the assumed zero.
#[test]
fn equality_assumption_ends_when_the_register_is_written_out() {
    let out = dc(0x14b0);
    assert!(out.contains("rax + 25"), "{out}");
    assert!(!out.contains("return 25;"), "{out}");
}

/// `FJ8`: the byte form of `FJ`; the compared operand is `rax` on both
/// edges once `rax` is written out (its value is a masked byte, so the byte
/// test needs no mask), so the `sete` lifts.
#[test]
fn byte_comparison_on_both_edges_survives_the_join() {
    let out = dc(0x1490);
    assert!(!out.contains("/* sete"), "{out}");
    assert!(out.contains("return rax == 0;"), "{out}");
    assert!(!out.contains("(rax & 0xff) == 0"), "{out}");
}

/// `FM`: the edges compare memory at different addresses, so no register can
/// carry the agreement.
///
/// Each edge computes the join's condition, the `setl` lifts, and with the
/// joined `setl; ret` copied into each arm every arm returns its own
/// comparison with no temporary left.
#[test]
fn differing_comparisons_reach_the_join_as_a_truth_temporary() {
    let out = dc(0x14d0);
    assert!(!out.contains("/* setl"), "{out}");
    assert!(
        out.contains("return (int32_t)*(uint32_t*)(a2 + 4) < 5;"),
        "{out}"
    );
    assert!(out.contains("return (int32_t)*(uint32_t*)a2 < 5;"), "{out}");
    assert!(!out.contains("tmp_"), "{out}");
}

/// `FS`: flags over a register the block rewrites reach the next block as a
/// truth temporary.
///
/// The `cmp` reads `rax` and the block then assigns `rax`, which the join
/// after it writes out at the block's end; the flags over the old `rax`
/// cannot cross into the `setl` block as they are.
#[test]
fn flags_over_a_rewritten_register_reach_the_next_block_as_a_truth() {
    let out = dc(0x14f0);
    assert!(!out.contains("/* setl"), "{out}");
    assert!(out.contains("tmp_1 = "), "{out}");
}

/// `AC2`: the carry an `adc` reads after a join comes from a different
/// addition on each edge, so each edge computes it into the shared truth
/// temporary and the `adc` adds that.
#[test]
fn carry_from_different_additions_reaches_the_adc_as_a_truth() {
    let out = dc(0x1510);
    assert!(!out.contains("/* adc"), "{out}");
    assert!(out.contains("uaddo64("), "{out}");
    assert!(out.contains("+ tmp_1;"), "{out}");
}

/// `ADC3`: a multiword add chains its carry through two `adc` into memory
/// and `setb` reads the carry out of the second; the carry out of an `adc`
/// is `uaddo(l, r) | uaddo(l + r, cf)`.
#[test]
fn adc_chain_carries_out_of_each_add() {
    let out = dc(0x1520);
    assert!(!out.contains("/* adc"), "{out}");
    assert!(!out.contains("/* setb"), "{out}");
    assert!(out.matches("uaddo32(").count() >= 2, "{out}");
}

/// `DC`: `sub ecx, 1; cmp ecx, 1` tests `a1 - 1 == 1`, which renders as
/// `a1 == 2` (and the edge assumption folds the taken arm's return to `2`).
#[test]
fn dec_chain_comparison_folds_onto_the_variable() {
    let out = dc(0x1530);
    assert!(out.contains("a1 == 2") || out.contains("a1 != 2"), "{out}");
    assert!(!out.contains("a1 - 1"), "{out}");
}

/// `LD`: a ladder split in two by an ordered compare, both halves sharing
/// the default arm, is one `switch` whose default is that arm, written
/// once, and every arm reaches the one tail with no goto.
#[test]
fn shared_default_arm_is_copied_so_the_ladder_structures() {
    let out = dc(0x1550);
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("rdx = 0;").count(), 1, "{out}");
    assert!(
        out.contains("rdx = 60;") && out.contains("rdx = 20;"),
        "{out}"
    );
    assert!(out.contains("Base::vfunc_1("), "{out}");
    assert!(out.contains("switch (a1) {"), "{out}");
    assert!(out.contains("case 6: {"), "{out}");
    assert!(out.contains("default: {"), "{out}");
}

/// `LD2`: a shared block that is both a branch target and a fall-through.
///
/// `D` must not be split across a copy that loses its jump: each arm returns
/// its own constant (`rdx = 60; return rdx;` folds to `return 60;`), the
/// `ecx == 6` arm returns 60 inside its branch, comparing the low half of
/// `a1`, the fall-through returns 0 once, and nothing is a goto.
#[test]
fn shared_block_heads_an_arm_and_its_copy_keeps_its_jump() {
    let out = dc(0x1590);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("*(uint32_t*)a2 = 1;"), "{out}");
    assert!(
        out.contains("if ((uint32_t)a1 == 6) {\n    return 60;\n  }"),
        "{out}"
    );
    assert_eq!(out.matches("return 0;").count(), 1, "{out}");
    assert!(out.trim_end().ends_with("return 0;"), "{out}");
}

/// `LX`: the scan loop leaves through its condition, written as a
/// `do { ... } while (c);`.
///
/// The loop's exit block is shared with the other arm and ends in a call;
/// it is the loop's continuation, the body ends `if (c) continue; break;`,
/// and the block is written once after the `if`.
#[test]
fn loop_exit_shared_with_the_other_arm_is_a_break() {
    let out = dc(0x15b0);
    assert!(
        out.contains("} while (*(uint8_t*)(a1 + rax) != 32);"),
        "{out}"
    );
    assert!(
        !out.contains("break;") && !out.contains("continue;"),
        "{out}"
    );
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("Base::vfunc_1(").count(), 1, "{out}");
}

/// `NM2`: the inferred names show in the header and at the call site.
#[test]
fn inferred_names_render_in_headers_and_calls() {
    let out = dc(0x15e0);
    assert!(out.starts_with("// Foo::Baz @ 0x15e0"), "{out}");
    assert!(out.contains("Foo::Bar("), "{out}");
}

/// `VD2`: its only caller overwrites `rax` right after the call, so the stale
/// `rax` left by `AR` is not a return value and the function is `void`.
#[test]
fn stale_return_register_no_caller_reads_is_void() {
    let out = dc(0x1600);
    assert!(out.contains("// signature: void exported_vd2("), "{out}");
    assert!(out.contains("return;"), "{out}");
    assert!(!out.contains("return rax"), "{out}");
}

/// `VT`: `call VD2; ret` hands `VD2`'s result to its own caller, which
/// discards it, so `VT` is `void` and the call is not bound to `rax`.
#[test]
fn tail_return_after_a_call_is_void_when_the_callers_result_is_unused() {
    let out = dc(0x1620);
    assert!(out.contains("// signature: void exported_vt("), "{out}");
    assert!(!out.contains("rax = exported_vd2"), "{out}");
    assert!(!out.contains("return rax"), "{out}");
}

/// The skeleton of the ladder `LD` keeps its switch and the tail call and
/// elides the assignments.
#[test]
fn skeleton_keeps_flow_and_calls_only() {
    let out = dc(0x1550);
    let sk = skeleton(&out);
    assert!(sk.contains("switch (a1) {"), "{sk}");
    assert!(sk.contains("case 6: {"), "{sk}");
    assert!(sk.contains("Base::vfunc_1("), "{sk}");
    assert!(!sk.contains("rdx = 60;"), "{sk}");
    assert!(sk.contains("..."), "{sk}");
    assert!(sk.len() < out.len(), "{sk}");
}

/// Declared signatures type the header and name the object `this`.
///
/// `CL1` carries `void __cdecl Cls::Set(int)` and reads two registers, so it
/// is a member function: the header shows the declared types with `this`,
/// the body reads `this`, and the `void` return holds; `NM`
/// (`int Foo::Bar(void)`, no register read) is a plain function with the
/// declared return type.
#[test]
fn signatures_from_asserts_type_the_header_and_name_this() {
    let out = dc(0x1640);
    assert!(
        out.contains("// signature: void Cls::Set(Cls *this, int a2)"),
        "{out}"
    );
    assert!(out.contains("this->field_0x8 = a2;"), "{out}");
    assert!(!out.contains("return rax"), "{out}");
    let bar = dc(0x15d0);
    assert!(bar.contains("// signature: int Foo::Bar()"), "{bar}");
    let has = dc(0x1660);
    assert!(
        has.contains("// signature: bool Cls::Has(Cls *this, int a2) const"),
        "{has}"
    );
    assert!(has.contains("*(uint32_t*)((uintptr_t)this + 8)"), "{has}");
    let of = dc(0x1680);
    assert!(
        of.contains("// signature: Util::String Name::Of(Util::String *result, int a2)"),
        "{of}"
    );
    assert!(of.contains("*(uint32_t*)result = a2;"), "{of}");
    assert!(of.contains("return result;"), "{of}");
}

/// A byte write defines only the lane later code reads.
///
/// The chain in `PC` renders as plain byte stores with no `rax` merge or
/// declaration, while `PW`, whose join reads `eax` after the byte writes,
/// keeps the `0x100` the upper bits carry.
#[test]
fn byte_writes_take_only_the_lane_that_is_read() {
    let pc = dc(0x16b0);
    assert!(pc.contains("*(uint8_t*)a2 = *(uint8_t*)a1;"), "{pc}");
    assert!(
        pc.contains("*(uint8_t*)(a2 + 1) = *(uint8_t*)(a1 + 1);"),
        "{pc}"
    );
    assert!(!pc.contains("rax"), "{pc}");
    let pw = dc(0x1690);
    assert!(pw.contains("0x100"), "{pw}");
}

/// A function whose every path to `ret` ends with a byte write of `rax`
/// returns that lane.
///
/// `RL` gets a `uint8_t` header and returns `1` or `0` with no upper-bit
/// merge, although its shared `ret` block writes nothing.
#[test]
fn byte_returns_are_the_low_lane() {
    let rl = dc(0x16c0);
    assert!(
        rl.contains("// signature: uint8_t sub_16c0(uint64_t a1)"),
        "{rl}"
    );
    assert!(rl.contains("1;") && rl.contains("0;"), "{rl}");
    assert!(
        !rl.contains("0xffffffffffffff00") && !rl.contains("-256"),
        "{rl}"
    );
}

/// A constructor's vtable store names the table: `Der::Der` renders
/// `Base::Base(this);` then `*(uint64_t*)this = &Der::vftable;`.
#[test]
fn constructors_store_named_vtables() {
    let cc = dc(0x16f0);
    assert!(cc.contains("Base::Base(this);"), "{cc}");
    assert!(cc.contains("*(uint64_t*)this = &Der::vftable;"), "{cc}");
}

/// A call through slot 1 of a receiver's vtable resolves to the slot's
/// function and renders in source form.
///
/// In `Der::Run` the receiver is `this`; in `VR2` it is the result of
/// `Fac::Get`, declared to return `Der *`; in `PU` it is the word a
/// `const Core::Ptr<Der> &` parameter holds, copied into `rax`.
#[test]
fn virtual_calls_resolve_through_the_receiver_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x1770).unwrap_or_default();
    assert!(
        text.contains("// signature: void Der::Run(Der *this)"),
        "{text}"
    );
    let callee = borer_engine::analysis::name_of(&a, &o, 0x1200);
    assert!(text.contains(&format!("this->{callee}(")), "{text}");
    let vr2 = decompile(&p, &a, &o, 0x1780).unwrap_or_default();
    assert!(vr2.contains("rax = Fac::Get();"), "{vr2}");
    assert!(vr2.contains(&format!("rax->{callee}(")), "{vr2}");
    let pu = decompile(&p, &a, &o, 0x17b0).unwrap_or_default();
    assert!(pu.contains("rax = *(uint64_t*)a2;"), "{pu}");
    assert!(pu.contains(&format!("rax->{callee}(")), "{pu}");
}

/// A word of data between a vtable's methods does not end the table: the
/// methods after it stay at the indexes their byte offsets give, and a
/// virtual call through them still resolves.
///
/// `F1` sits at slot 2 of the table `RM` stores, past the datum `0x9999`
/// at slot 1, and its call through slot 0 of its own table reaches `F0`.
#[test]
fn a_data_slot_inside_a_vtable_keeps_the_methods_after_it() {
    let text = dc(0x5660);
    assert!(
        text.contains("// signature: uint64_t class_3730::vfunc_2(class_3730 *this)"),
        "{text}"
    );
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    // The datum keeps its slot, so the method after it stays at index 2.
    let slots = a.classes.by_name.get("class_3730").map(|c| c.slots.clone());
    assert_eq!(slots, Some(vec![0x5650, 0, 0x5660]));
    let callee = borer_engine::analysis::name_of(&a, &o, 0x5650);
    assert_eq!(callee, "class_3730::vfunc_0");
    assert!(text.contains("this->vfunc_0("), "{text}");
}

/// A vtable a constructor stores is named by its locator, and the class
/// that names it reaches the methods' own calls.
///
/// `Ns::Solo`'s table holds one slot, which a constructor must store
/// before it counts as a table at all, and `X`, the helper its
/// constructor hands `this` to after the store, resolves its call through
/// the class rather than an address-built name; `Ns::Rtti`'s two-slot
/// table gives `M1` the same resolution in its own body.
#[test]
fn a_locator_named_class_reaches_the_methods_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.vtables.get(&0x3678).map(String::as_str),
        Some("Ns::Rtti")
    );
    assert_eq!(
        a.classes.vtables.get(&0x3718).map(String::as_str),
        Some("Ns::Solo")
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x56a0),
        "Ns::Solo::vfunc_0"
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x5680),
        "Ns::Solo::ctor_or_dtor"
    );
    let x = decompile(&p, &a, &o, 0x56b0).unwrap_or_default();
    assert!(
        x.contains("// signature: uint64_t sub_56b0(Ns::Solo *a1)"),
        "{x}"
    );
    assert!(x.contains("a1->vfunc_0("), "{x}");
    let m1 = decompile(&p, &a, &o, 0x5630).unwrap_or_default();
    assert!(
        m1.contains("// signature: uint64_t Ns::Rtti::vfunc_1(Ns::Rtti *this)"),
        "{m1}"
    );
    assert!(m1.contains("this->vfunc_0("), "{m1}");
}

/// A further base's table under multiple inheritance is named after its
/// base, and the base's methods it holds carry the base's class.
///
/// `Ns::Wide` stores `Ns::Tail`'s table at `[this+0x10]`; the table is
/// named `Ns::Wide::vftable_Ns::Tail`, its slots name `Ns::Tail`'s
/// methods and give the class its layout, although `Ns::Tail` has no
/// table of its own in the image.
#[test]
fn a_further_bases_vtable_is_named_after_its_base() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.secondary_vtables.get(&0x32f0).map(String::as_str),
        Some("Ns::Wide::vftable_Ns::Tail")
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x5740),
        "Ns::Tail::vfunc_0"
    );
    assert_eq!(
        borer_engine::analysis::name_of(&a, &o, 0x5750),
        "Ns::Tail::vfunc_1"
    );
    let layout = borer_engine::analysis::classes::class_layout(&p, &a, &o, "Ns::Tail");
    let fields = layout.map(|l| l.fields.keys().copied().collect::<Vec<u64>>());
    assert_eq!(fields, Some(vec![4, 8]));
}

/// A method that never reads `this` is still a member when a parameter
/// arrives past the first argument register.
///
/// `Pk::Pick` declares one `int` and reads only `edx`, so `this` fills the
/// first slot and the body's `a2` matches the header.
#[test]
fn unused_this_still_counts_as_a_parameter() {
    let text = dc(0x17f0);
    assert!(
        text.contains("// signature: int Pk::Pick(Pk *this, int a2)"),
        "{text}"
    );
    assert!(text.contains("return a2;"), "{text}");
}

/// A call whose `ret` follows returns the callee's result when the callee
/// is known to produce one.
///
/// `RC` renders `return Foo::Bar();` under a `uint64_t` header, not
/// `rax = Foo::Bar(); return;`.
#[test]
fn a_call_before_ret_returns_its_result() {
    let text = dc(0x1800);
    assert!(text.contains("return Foo::Bar();"), "{text}");
    assert!(text.contains("// signature: uint64_t sub_1800()"), "{text}");
    assert!(!text.contains("rax ="), "{text}");
}

/// Assert literals render compactly: the function's own signature string
/// is `__FUNCSIG__`, the source path keeps its last two components, and
/// the asserted expression and line stay as they are.
#[test]
fn assert_literals_render_compactly() {
    let text = dc(0x1810);
    assert!(text.contains("// signature: void As::Chk()"), "{text}");
    assert!(
        text.contains("ReportAssertFailure(\"f.IsValid()\", \"util/fourcc.h\", 191, __FUNCSIG__);"),
        "{text}"
    );
}

/// A shared one-way block that falls into a shared return is copied whole
/// into each guard's arm.
///
/// `TC`'s two guards jump to `L: rax |= -1;`, which falls into `R: return
/// rax;`; the guard gets a copy of both, so no `goto` remains and the two
/// guards merge into one condition.
#[test]
fn one_way_chains_into_a_return_are_copied_into_arms() {
    let out = dc(0x1c60);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("if (a1 == 0 || a2 == 0) {"), "{out}");
    assert!(out.contains("return a1;"), "{out}");
}

/// A loop whose break arms and fall-through share one return keeps every
/// label it jumps to.
///
/// `LP`'s arms `rax = 1;` and `rax = 2;` and its fall-through `rax = -1;`
/// all reach `R: return rax;` (its first arm now serves as the loop's
/// condition), and `LP2` puts the arms inside an if/else whose copies of
/// the return once left the loop's `goto` dangling; whatever the
/// structurer copies, no `goto` may be left without its label.
#[test]
fn loop_arms_sharing_a_return_keep_their_labels() {
    for entry in [0x1c80, 0x1cb0] {
        let out = dc(entry);
        for line in out.lines() {
            let t = line.trim();
            if let Some(target) = t.strip_prefix("goto ").and_then(|g| g.strip_suffix(';')) {
                assert!(
                    out.contains(&format!("{target}:")),
                    "dangling {target}: {out}"
                );
            }
        }
        assert!(out.contains("while ("), "{out}");
    }
}

/// A loop exit that only returns is written inline even when the loop has
/// no single continuation.
///
/// `LP3`'s fall-through `F` is also the prologue's target, so the loop's
/// exits meet nowhere; its other exit `E` sets the result and returns, so
/// it is written in place of its `goto`.
#[test]
fn returning_loop_exits_are_inlined_without_a_single_continuation() {
    let out = dc(0x1cf0);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while (1) {"), "{out}");
    assert!(out.contains("break;"), "{out}");
    assert!(out.contains("return a1;"), "{out}");
}

/// A shared return block is as small as its `return`, whatever its epilogue.
///
/// `TE` is `LP3` with eight callee-saved registers to restore: the return
/// block holds ten instructions but renders as one statement, so the
/// chains into it are still copied, the returning exit is still written
/// inline and no `goto` remains.
#[test]
fn epilogue_instructions_do_not_count_against_copies() {
    let out = dc(0x1d30);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while (1) {"), "{out}");
    assert!(out.contains("return a1;"), "{out}");
}

/// A tail with a call is copied when nothing else structures.
///
/// `TL`'s loop exit `E` reaches `return Base::vfunc_1(1, ...)` through a tail
/// whose call keeps it out of the first attempt, and the loop's exits meet
/// nowhere, so only a copy of the calling tail writes the exit inline; the
/// second attempt copies it and no `goto` remains, while `LD`'s ladder,
/// which structures at the first attempt, still writes its call once.
#[test]
fn tails_with_a_call_are_copied_as_a_last_resort() {
    let out = dc(0x1d90);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while (1) {"), "{out}");
    assert!(out.matches("Base::vfunc_1(").count() >= 2, "{out}");
    let ladder = dc(0x1550);
    assert_eq!(ladder.matches("Base::vfunc_1(").count(), 1, "{ladder}");
}

/// A shared return jumped to from two sites of one arm is copied to both,
/// so the arms still meet at their tail.
///
/// `JT`'s second arm returns early from two places; with the return copied
/// into each, both arms leave only into the two-call tail, which is written
/// once after the if/else instead of being copied into an arm.
#[test]
fn shared_return_from_two_sites_still_joins() {
    let out = dc(0x1e70);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("} else {"), "{out}");
    assert_eq!(out.matches("Base::vfunc_1(").count(), 4, "{out}");
}

/// A loop whose condition sits after its body structures from its header.
///
/// `RL` enters its loop by a jump to the condition at the bottom, so the
/// body precedes the header in address order; the emitter reaches the body
/// first, finds the loop it belongs to and writes it from the header as a
/// `while`.
#[test]
fn rotated_loops_structure_from_their_header() {
    let out = dc(0x1ee0);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while ("), "{out}");
    assert!(out.contains("Base::vfunc_1("), "{out}");
}

/// A small one-way block two guards share is copied into each guard's arm,
/// the other arm's start included.
///
/// `GX`'s guards both jump to `X: rdi = 0;`, which leads into the join the
/// main path falls into; `X` starts the first guard's arm and is reached
/// again inside the other arm, where it is copied rather than absorbed, so
/// both arms meet at the join and no `goto` remains.
#[test]
fn shared_one_way_block_is_copied_into_the_other_arm() {
    let out = dc(0x1f00);
    assert!(!out.contains("goto "), "{out}");
    assert_eq!(out.matches("rdi = 0;").count(), 2, "{out}");
    assert!(out.contains("return rdi"), "{out}");
}

/// A result every caller tests as a byte reads without a mask.
///
/// `CW` calls `BL`, whose only caller reads `al`, so `BL` returns a byte and
/// `test al, al` renders as `rax == 0` rather than `(rax & 0xff) == 0`.
#[test]
fn byte_wide_call_results_read_without_a_mask() {
    let out = dc(0x1f40);
    assert!(!out.contains("& 0xff"), "{out}");
    assert!(
        out.contains("rax == 0") || out.contains("rax != 0"),
        "{out}"
    );
}

/// A copy of a byte-wide result keeps its width, so a byte test of the
/// copy needs no mask either.
///
/// `CB2` copies the result of `BB`, which ends `sete al`, into `ecx` and
/// tests `cl`: the copy carries the byte width and the test renders with
/// no `& 0xff`.
#[test]
fn copies_of_byte_wide_results_read_without_a_mask() {
    let out = dc(0x1f70);
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A result whose every last write fits a byte reads without a mask.
///
/// `CZ` copies the result of `BZ`, a zero-extended byte load, into `edx`
/// and tests `dl`: the value fits a byte, so the test renders with no
/// `& 0xff`.
#[test]
fn results_that_fit_a_byte_read_without_a_mask() {
    let out = dc(0x1fa0);
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A result whose only wide return is a null pointer reads without a mask.
///
/// `CN` copies the result of `BN`, which returns either a zero-extended
/// byte or the null pointer it checked, into `edx` and tests `dl`: every
/// value fits a byte, so the test renders with no `& 0xff`.
#[test]
fn results_wide_only_when_null_read_without_a_mask() {
    let out = dc(0x1fd0);
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A value that provably fits a byte keeps that width once written out.
///
/// `MB` keeps `*(uint32_t*)a1 == 1` in `bl` across a call: the compare is
/// written out as `rbx = ... == 1;` before the call, and the `test bl, bl`
/// after it reads `rbx` with no `& 0xff`.
#[test]
fn written_out_truth_values_read_without_a_mask() {
    let out = dc(0x1fe4);
    assert!(out.contains("rbx = *(uint32_t*)a1 == 1;"), "{out}");
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A parameter typed as a smart pointer by its callers resolves the
/// virtual call through it.
///
/// `UP`'s first parameter points at the `Core::Ptr<Der>` field `Der::Pass`
/// passes, so its header reads `Core::Ptr<Der> *a1` and the call through
/// the object the pointer holds resolves to slot 1 of `Der`'s table.
#[test]
fn smart_pointer_parameters_resolve_virtual_calls() {
    let out = dc(0x12f0);
    assert!(out.contains("Core::Ptr<Der> *a1"), "{out}");
    assert!(!out.contains("->vtable["), "{out}");
}

/// A `goto` whose label follows across the closing brace of its `if` is
/// dropped.
///
/// `GJ`'s outer arm holds an inner branch and ends in a jump to the block
/// the other path takes, so the arm's text ends `goto L;` right before `}`
/// and `L:`; falling out of the `if` reaches the label anyway.
#[test]
fn a_goto_into_the_label_after_its_branch_is_dropped() {
    let out = dc(0x4000);
    assert!(out.contains("if (a1 == 0) {"), "{out}");
    assert!(!out.contains("goto "), "{out}");
    assert!(!out.contains("L_"), "{out}");
}

/// A call that preserves `rax` is not the result: the value set before it
/// is what the function returns.
///
/// `CC` sets `eax` to 7 and calls the cookie-check-shaped `CK` before
/// returning, so it returns 7 and the check is a statement.
#[test]
fn calls_preserving_rax_do_not_replace_the_result() {
    let out = dc(0x4050);
    assert!(out.contains("return 7;"), "{out}");
    assert!(out.contains("sub_4041("), "{out}");
    assert!(!out.contains("= sub_4041("), "{out}");
}

/// A ladder whose arms share a tail and whose last test escapes to a
/// returning block is a `switch` with a `default`.
///
/// `LD3`'s ladder arms set `rdx` and jump to the shared tail while its last
/// test skips to a block an outer guard reaches too: the arms are the cases,
/// the skip's target the default, and the tail follows the switch once. The
/// tail's callee is a bare `ret` and `rcx` still holds the caller's own
/// `a1`, so the call passes nothing.
#[test]
fn ladders_with_a_shared_tail_and_an_escape_structure_around_the_tail() {
    let out = dc(0x4090);
    assert_eq!(out.matches("goto ").count(), 0, "{out}");
    assert_eq!(out.matches("return 13;").count(), 1, "{out}");
    assert!(out.contains("switch (a1) {"), "{out}");
    assert!(out.contains("default: {"), "{out}");
    assert_eq!(out.matches("Base::vfunc_1()").count(), 1, "{out}");
    assert!(
        out.contains("rdx = 1;") && out.contains("rdx = 3;"),
        "{out}"
    );
}

/// A declared return type keeps the result even when no caller reads it.
///
/// `IG`, `IG2` and `IG3` call `Cls::Has`, `Ns::Flag` and `Ns::Flag2` and
/// overwrite `eax` at once, so no caller reads the results; the signatures
/// say `bool`, so the field read and the bytes kept in `rbx` across a call
/// are still returned, `Ns::Flag2`'s set on two paths.
#[test]
fn declared_return_types_keep_their_result() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_ne!(a.function(0x1660).and_then(|f| f.returns_value), Some(true));
    let out = dc(0x1660);
    assert!(
        out.contains("return *(uint32_t*)((uintptr_t)this + 8)"),
        "{out}"
    );
    assert_ne!(a.function(0x4100).and_then(|f| f.returns_value), Some(true));
    let flag = dc(0x4100);
    assert!(flag.contains("// signature: bool Ns::Flag("), "{flag}");
    assert!(!flag.contains("return;"), "{flag}");
    assert!(flag.contains("return "), "{flag}");
    assert_ne!(a.function(0x4130).and_then(|f| f.returns_value), Some(true));
    let flag2 = dc(0x4130);
    assert!(flag2.contains("// signature: bool Ns::Flag2("), "{flag2}");
    assert!(!flag2.contains("return;"), "{flag2}");
    assert!(flag2.contains("return rbx"), "{flag2}");
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

/// A conditional `goto` over a short flat run becomes an `if` around it.
///
/// `GC`'s guarded arm has two exits, so neither side structures and the
/// guard is emitted as a jump over the arm's two lines to the join's
/// label; the run becomes the arm of the inverted guard, and the arm's own
/// escape, a jump to a returning line, is copied in place. The callee is a
/// bare `ret`, which leaves `rcx` and `rdx` as it found them, so the stores
/// after the join still read the parameters.
#[test]
fn conditional_gotos_over_a_short_run_become_an_if() {
    let out = dc(0x4180);
    assert!(out.contains("if (a1 != 0) {"), "{out}");
    assert!(out.contains("  rax = Base::vfunc_1("), "{out}");
    assert_eq!(out.matches("goto ").count(), 0, "{out}");
    assert!(out.contains("    return 13;"), "{out}");
    assert!(out.contains("*(uint32_t*)a2 = a1;"), "{out}");
}

/// The double-width shifts lift instead of leaving an assembly comment.
///
/// `SH` is `shld rax, rdx, cl` and `SH2` is `shrd rax, rdx, cl`: each
/// combines the two registers around a count masked to the operand's
/// width.
#[test]
fn double_width_shifts_lift() {
    let shld = dc(0x41d0);
    assert!(!shld.contains("/*"), "{shld}");
    assert!(
        shld.contains("<<") && shld.contains(">>") && shld.contains(" | "),
        "{shld}"
    );
    let shrd = dc(0x41e0);
    assert!(!shrd.contains("/*"), "{shrd}");
    assert!(
        shrd.contains("<<") && shrd.contains(">>") && shrd.contains(" | "),
        "{shrd}"
    );
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

/// A function whose code another copies says so in its header, and one
/// that stands alone says nothing.
///
/// `CL_A` and `CL_B` are clones, so both name the class and its first
/// member; `CL_C` differs by an instruction and carries no such line.
#[test]
fn cloned_functions_name_their_class_in_the_header() {
    let a = dc(0x4220);
    assert!(
        a.contains("// clones: 2 functions run this code, the first at 0x4220"),
        "{a}"
    );
    let b = dc(0x4240);
    assert!(
        b.contains("// clones: 2 functions run this code, the first at 0x4220"),
        "{b}"
    );
    assert!(!dc(0x4260).contains("// clones:"), "{}", dc(0x4260));
}

/// A ladder nesting past sixty-four levels still structures without gotos.
///
/// `DEEP` nests seventy-two compare levels whose arms all jump to one
/// shared `ret`; every arm copies the tail as `return k;` and none falls
/// back to a jump.
#[test]
fn ladders_deeper_than_sixty_four_levels_structure() {
    let out = dc(0x4300);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("return 70;"), "{out}");
    assert!(out.contains("return 255;"), "{out}");
}

/// A compare ladder renders as a run of early returns, not nested levels.
///
/// `DEEP`'s seventy-two levels each test a byte and return a constant when
/// it is set; every level's body ends in a return, so each `if` inverts to
/// `if (*(uint8_t*)(a1 + k) != 0) { return k; }` and the next level follows
/// at the same indentation.
#[test]
fn compare_ladders_render_as_early_returns() {
    let out = dc(0x4300);
    assert!(out.contains("if (*(uint8_t*)a1 != 0) {"), "{out}");
    assert!(
        out.lines().all(|l| l.len() - l.trim_start().len() <= 2),
        "nested deeper than one level:\n{out}"
    );
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
        out.contains("tmp_1 = atomic_sub32(*(uint32_t*)(a1 + 8), 1);"),
        "{out}"
    );
    assert!(
        out.contains("if (tmp_1 == 0)") || out.contains("if (tmp_1 != 0)"),
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

/// An `xadd` leaves the flags of the addition it performed, so the branch
/// after it reads the sum and not an opaque condition.
///
/// `XA` stores the addend's partner on the stack, adds `0x10` through the
/// exchange, and branches on the sum reaching zero.
#[test]
fn an_xadd_branch_reads_the_additions_flags() {
    let out = dc(0x5910);
    assert!(out.contains("xadd32(home_10, 16);"), "{out}");
    assert!(out.contains("a2 == 0xfffffff0"), "{out}");
}

/// A `cmpxchg` leaves the flags of the compare that decided the exchange,
/// so the branch after it reads whether the old value matched the
/// accumulator.
///
/// `CX` compares the accumulator with `5` and exchanges `a2` in; the
/// branch reads the match through `rax`, which the exchange leaves
/// holding the old value either way.
#[test]
fn a_cmpxchg_branch_reads_the_compares_zero_flag() {
    let out = dc(0x5930);
    assert!(out.contains("cmpxchg32(*(uint32_t*)a1, 5, a2);"), "{out}");
    assert!(out.contains("rax == 5"), "{out}");
}

/// Decompiling every fixture function at once matches doing it one by one.
///
/// The parallel path stripes the entries over the cores and must return
/// the same text in the same order as the sequential call.
#[test]
fn parallel_decompile_matches_sequential() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let all = decompile_all(&p, &a, &o, &entries);
    assert_eq!(all.len(), entries.len());
    for (entry, got) in entries.iter().zip(&all) {
        assert_eq!(*got, decompile(&p, &a, &o, *entry), "{entry:#x}");
    }
}

/// A loop whose head is the entry block structures and carries its
/// parameter correctly.
///
/// `LP` walks a list and jumps back to its first instruction. The entry
/// block's environment joins with the back edge like any other join, so
/// the register the loop advances is written from the parameter once at
/// the top (`rcx = a1;`) and the body reads and advances that register,
/// never the parameter's original value; and the loop structures instead
/// of jumping to a label the emitter used to omit.
#[test]
fn loops_headed_by_the_entry_block_carry_their_parameter() {
    let out = dc(0x47a0);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("rcx = a1;"), "{out}");
    assert!(out.contains("do {"), "{out}");
    assert!(out.contains("} while (rcx != 0);"), "{out}");
    assert!(out.contains("rcx = *(uint64_t*)rcx;"), "{out}");
    assert!(out.contains("*(uint8_t*)(rcx + 0x34) ^= 1;"), "{out}");
}

/// A string-compare ladder and a constant-to-string table both yield an
/// enum in the header.
///
/// `EN` compares its argument against four literals through `Q` and
/// returns a constant for each; `EN2` returns a literal for each of four
/// constants.
#[test]
fn name_tables_recover_as_enums() {
    let to_string = dc(0x4830);
    assert!(
        to_string.contains(
            "// enum values of a1: 4 values, Normal = 0, Pressed = 1, Over = 2, Down = 3"
        ),
        "{to_string}"
    );
    let parser = dc(0x47b0);
    assert!(
        parser.contains(
            "// enum by Base::vfunc_1 compare: 4 values, Back = 1, Tab = 2, Clear = 3, Return = 4"
        ),
        "{parser}"
    );
}

/// The header names what a body writes, reads and stores through.
///
/// `LK` drops a count through an atomic on `a1 + 8`; `CL_A` only reads a
/// global; `GC` stores nine words through `rdx`, which still holds `a2`
/// after a call to a bare `ret`, so the header names the first eight and
/// counts the rest.
#[test]
fn headers_summarize_effects() {
    let lk = dc(0x4790);
    assert!(lk.contains("// effects: writes a1+8"), "{lk}");
    let cl = dc(0x4220);
    assert!(cl.contains("// effects: reads g64_3090"), "{cl}");
    let gc = dc(0x4180);
    assert!(
        gc.contains("// effects: writes a2, a2+4, a2+8, a2+0xc") && gc.contains("(+1 more)"),
        "{gc}"
    );
}

/// A loop's escapes to one returning tail each carry the tail.
///
/// `ET3`'s loop escapes twice to one error tail holding a call. The loop
/// emitter copies such a tail into every escape (`if (rax == 0) {
/// Base::vfunc_1(rcx); return 7; }`), so this pins that no jump is left; the
/// text-level copy of returning tails covers the jumps the structurer
/// leaves elsewhere (`GC`, `LD3`).
#[test]
fn loop_escapes_to_a_returning_tail_carry_it() {
    let out = dc(0x4900);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("while"), "{out}");
    assert_eq!(out.matches("return 7;").count(), 2, "{out}");
}

/// A conditional `goto` over a run holding a nested block becomes an `if`
/// around the run.
///
/// `FC`'s guarded arm holds its own `if`; the arm's run is label-free, so
/// the guard inverts around it and the nested block sits one level deeper.
/// The call before it is to a bare `ret`, which leaves `rcx` and `rdx` the
/// parameters they were.
#[test]
fn conditional_gotos_over_nested_blocks_become_an_if() {
    let out = dc(0x4930);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("if (a1 != 0) {"), "{out}");
    assert!(out.contains("  if (rax != 0) {"), "{out}");
    assert!(out.contains("    *(uint32_t*)a2 = a1;"), "{out}");
}

/// A function whose instruction shape others share names one of them.
///
/// `SP1` and `SP2` differ only in constants; each header points at the
/// other.
#[test]
fn near_clones_name_their_shape_class_in_the_header() {
    let out = dc(0x4990);
    assert!(
        out.contains("// shape: ") && out.contains("e.g. 0x49a0"),
        "{out}"
    );
    assert!(!out.contains("// clones:"), "{out}");
}

/// A conditional `goto` over a run with internal jumps still folds when
/// the run's labels are targeted only from inside it.
///
/// The text is the shape of the client's `sub_140d36f00`: a ladder whose
/// first arm jumps past the other arms to a label, while one of those arms
/// jumps to a label inside the skipped run. The guard inverts around the
/// run, the returning tails the inner jumps reach are copied to them, and
/// the first arm's short tail becomes the early return, so no jump is
/// left.
#[test]
fn conditional_gotos_over_self_contained_runs_become_an_if() {
    let body = "if (a1 == 1) goto L_7f;
if (a1 == 2) {
  r9 = 1;
} else {
  r9 = 2;
  if (a1 == 3) goto L_86;
  r9 = 2;
  if (a1 == 4) goto L_76;
  return Base::vfunc_1(a1);
}
L_76:
rax = 3;
goto L_8d;
L_7f:
r9 = 1;
L_86:
rax = 4;
L_8d:
return rax + r9;
";
    let out = cleanup(body);
    assert!(out.contains("if (a1 == 1) {"), "{out}");
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("return Base::vfunc_1(a1);").count(), 1, "{out}");
}

/// The binary-wide table listing finds every function that encodes a name
/// table, and nothing else.
///
/// `EN` (a parser), `EN2` and `EN3` (constant-to-string tables) are the
/// fixture's three tables.
#[test]
fn enum_tables_list_every_name_table_once() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let tables = enum_tables(&p, &a, &Overlay::default());
    let entries: Vec<u64> = tables.iter().map(|(e, _)| *e).collect();
    assert_eq!(entries, vec![0x47b0, 0x4830, 0x4a50], "{tables:?}");
    assert!(
        tables.iter().all(|(_, t)| t.members.len() == 4),
        "{tables:?}"
    );
    assert_eq!(tables[0].1.name, "by Base::vfunc_1 compare");
}

/// With the binary's tables in the overlay, callers render constants by
/// their member names.
///
/// `CE1` compares `EN`'s result with 3, which `EN` maps from `"Clear"`;
/// `CE2` passes 2 to `EN2`, which names it `"Over"`.
#[test]
fn callers_render_constants_by_their_enum_names() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.enums = enums_by_name(&a, &o, &enum_tables(&p, &a, &o));
    let compare = decompile(&p, &a, &o, 0x4a20).expect("decompile");
    assert!(compare.contains("Clear"), "{compare}");
    assert!(
        !compare.contains("== 3") && !compare.contains("!= 3"),
        "{compare}"
    );
    let pass = decompile(&p, &a, &o, 0x4a40).expect("decompile");
    assert!(pass.contains("sub_4830(Over)"), "{pass}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x4a20).expect("decompile");
    assert!(plain.contains("rax != 3"), "{plain}");
}

/// The binary's own tables, each read when a body names its function,
/// render every function as the whole binary's tables do.
///
/// Besides the fixture's own names, one overlay names `EN2` and `EN3`
/// alike (the later function's table wins the name) and one names `EN`
/// `TryGet` and `EN3` `Get`, so `CE1`'s call is found by a name's tail as
/// well: the tie and the tail are both looked up as the whole tables would.
#[test]
fn tables_read_on_demand_render_as_the_whole_binarys() {
    use borer_engine::analysis::decompile::decompile_named;
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut tie = Overlay::default();
    tie.names.insert(0x4830, "Pick".to_owned());
    tie.names.insert(0x4a50, "Pick".to_owned());
    let mut tail = Overlay::default();
    tail.names.insert(0x47b0, "TryGet".to_owned());
    tail.names.insert(0x4a50, "Get".to_owned());
    for o in [Overlay::default(), tie, tail] {
        let mut given = o.clone();
        given.enums = enums_by_name(&a, &o, &enum_tables(&p, &a, &o));
        let binary = Overlay {
            enum_source: EnumSource::Binary,
            ..o.clone()
        };
        for f in &a.functions {
            assert_eq!(
                decompile(&p, &a, &binary, f.entry),
                decompile(&p, &a, &given, f.entry),
                "{:#x} under {:?}",
                f.entry,
                o.names
            );
            assert_eq!(
                decompile_named(&p, &a, &binary, f.entry),
                decompile_named(&p, &a, &given, f.entry),
                "{:#x} under {:?}",
                f.entry,
                o.names
            );
        }
    }
    let binary = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let compare = decompile(&p, &a, &binary, 0x4a20).expect("decompile");
    assert!(compare.contains("Clear"), "{compare}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x4a20).expect("decompile");
    assert!(plain.contains("rax != 3"), "{plain}");
}

/// A decompilation reads the tables of the functions it calls and no
/// others: `CE2` calls `EN2` alone, so one table is read of the fixture's
/// three.
#[test]
fn a_decompilation_reads_only_the_tables_it_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    assert_eq!(a.derived.held("enum_table"), 0);
    let pass = decompile(&p, &a, &o, 0x4a40).expect("decompile");
    assert!(pass.contains("sub_4830(Over)"), "{pass}");
    assert_eq!(a.derived.held("enum_table"), 1);
}

/// The `else` of an `else if (v != K)` arm names `K`.
///
/// `EN3`'s chain ends `else if (a1 != 4) { rdx = "Normal"; } else { rdx =
/// "Down"; }`, so `Down = 4` joins the table and the default does not.
#[test]
fn else_defaults_name_their_constant() {
    let out = dc(0x4a50);
    assert!(
        out.contains("// enum values of a1: 4 values, Normal = 0, Pressed = 1, Over = 2, Down = 4"),
        "{out}"
    );
}

/// Division by a constant comes back from its magic multiply.
///
/// `DV5` is the signed form (high multiply, arithmetic shift, sign-bit fix)
/// of `a1 / 5`; `DV10` the unsigned form (high multiply and shift) of
/// `a1 / 10`; `DM10` subtracts ten times that quotient, `a1 % 10`.
#[test]
fn divisions_by_constants_come_back_from_their_magic() {
    let signed = dc(0x4aa0);
    assert!(signed.contains("return (int64_t)a1 / 5;"), "{signed}");
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
/// `IX` reads `[rcx + rdx * 4]` as a dword: `((uint32_t*)a1)[a2]`, not
/// `*(uint32_t*)(a1 + a2 * 4)`.
#[test]
fn indexed_loads_render_as_arrays() {
    let out = dc(0x4b10);
    assert!(out.contains("return ((uint32_t*)a1)[a2];"), "{out}");
}

/// A byte-counting loop is the `strlen` it compiles from.
///
/// `SL` seeds `rax` with all ones, then bumps it until the byte at
/// `a1 + rax` is zero: `return strlen(a1);`. The text form pins the rule
/// itself: a base loaded between the seed and the loop, and a loop over
/// 16-bit elements for `wcslen`.
#[test]
fn strlen_loops_render_as_calls() {
    let out = dc(0x4b00);
    assert!(out.contains("return strlen(a1);"), "{out}");
    assert!(!out.contains("do {"), "{out}");
    let text = "r8 |= -1;\nrdx = *(uint64_t*)rcx;\ndo {\n    r8 += 1;\n} while (*(uint8_t*)(rdx + r8) != 0);\nr9 = 0xffffffff;\ndo {\n    r9 += 1;\n} while (((uint16_t*)a2)[r9] != 0);\nreturn r8 + r9;\n";
    let out = cleanup(text);
    assert!(
        out.contains(
            "rdx = *(uint64_t*)rcx;\nr8 = strlen(rdx);\nr9 = wcslen(a2);\nreturn r8 + r9;"
        ),
        "{out}"
    );
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

/// A carry-guarded multiply or add is the saturating operation.
///
/// `SA` multiplies `a1` by 16 and adds 8, each time moving all ones in on
/// the carry: `add_sat(mul_sat(0x10, a1), 8)`, the allocation-size guard a
/// standard library compiles to.
#[test]
fn carry_guarded_arithmetic_saturates() {
    let out = dc(0x4b60);
    assert!(
        out.contains("return add_sat(mul_sat(0x10, a1), 8);"),
        "{out}"
    );
}

/// A ternary that is an index needs no parentheses of its own.
///
/// `TI` reads element `a2 != 3 ? a2 + 1 : 0` of the array at `a1`; the
/// brackets already delimit it.
#[test]
fn ternary_indexes_drop_their_parentheses() {
    let out = dc(0x4b90);
    assert!(
        out.contains("return ((uint32_t*)a1)[a2 != 3 ? a2 + 1 : 0];"),
        "{out}"
    );
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
/// `SC` compares the sign-extended `a1` with `a2`: the left side already
/// reads `(int64_t)(int32_t)a1`, so no `(int64_t)` stacks on it.
#[test]
fn signed_compares_cast_once() {
    let out = dc(0x4c00);
    assert!(out.contains("(int64_t)(int32_t)a1 > (int64_t)a2"), "{out}");
    assert!(!out.contains("(int64_t)(int64_t)"), "{out}");
}

/// A pointer read through often enough gets a layout and named fields.
///
/// `LY` touches three dword fields of `a1`: the header lists them with
/// their widths and each access reads as `a1->field_0x18`; the sum is
/// stored and returned, so it is computed once.
#[test]
fn pointers_read_often_get_a_layout() {
    let out = dc(0x4c10);
    assert!(
        out.contains("// layout a1: 0x18 u32, 0x1c u32, 0x20 u32"),
        "{out}"
    );
    assert!(
        out.contains("rax = a1->field_0x18 + a1->field_0x1c;"),
        "{out}"
    );
    assert!(out.contains("a1->field_0x20 = rax;"), "{out}");
    assert!(!out.contains("*(uint32_t*)"), "{out}");
}

/// A struct the user applied to a global's pointer names the fields read
/// through it, at the width each field states.
///
/// `UT` reads the object the global at 0x3400 points at: with `Player`
/// applied there as a `Player *`, each dword load at a stated `u32` field
/// renders by that field's name, and a field stated wider than the read
/// (`gold` an `i64` over a dword load) stays an offset access the layout
/// pass names, since reading it as the field would state a width the type
/// does not.
#[test]
fn an_applied_struct_names_the_fields_it_reads() {
    use borer_engine::analysis::utypes::{build_struct, parse_type};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let fields = vec![
        (0x18, "hp".to_owned(), parse_type("u32").unwrap()),
        (0x1c, "mp".to_owned(), parse_type("u32").unwrap()),
        (0x20, "gold".to_owned(), parse_type("i64").unwrap()),
    ];
    o.types.insert(
        "Player".to_owned(),
        build_struct("Player", None, &fields, &o.types, 8).unwrap(),
    );
    o.applied.insert(0x3400, parse_type("Player *").unwrap());
    let text = decompile(&p, &a, &o, 0x55c0).unwrap_or_default();
    assert!(text.contains("g64_3400->hp"), "{text}");
    assert!(text.contains("g64_3400->mp"), "{text}");
    assert!(
        !text.contains("->gold"),
        "a dword read named as an i64 field:\n{text}"
    );
    assert!(text.contains("->field_0x20"), "{text}");
}

/// An enum the user applied to a global names the constants a function
/// compares it with.
///
/// `EN` compares the dword global at 0x3420 with 1 and 2: with `State`
/// applied there, each compare renders by its member name, a value the enum
/// does not state stays a number, and without the application the constants
/// stay numbers too.
#[test]
fn an_applied_enum_names_compared_constants() {
    use borer_engine::analysis::utypes::{build_enum, parse_type};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let stated = [
        (2u64, "Done".to_owned()),
        (0u64, "Idle".to_owned()),
        (1u64, "Run".to_owned()),
    ];
    o.types
        .insert("State".to_owned(), build_enum("State", 4, &stated).unwrap());
    o.applied.insert(0x3420, parse_type("State").unwrap());
    let text = decompile(&p, &a, &o, 0x55e0).unwrap_or_default();
    assert!(text.contains("Run"), "{text}");
    assert!(text.contains("Done"), "{text}");
    assert!(!text.contains("== 1") && !text.contains("== 2"), "{text}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x55e0).unwrap_or_default();
    assert!(plain.contains("== 1") && plain.contains("== 2"), "{plain}");
}

/// An enum-typed field of a user-applied struct names the constants its
/// accesses are compared with.
///
/// `EF` reads the dword at offset 8 of the object the global at 0x3430
/// points at and compares it with 1 and 2: with `Item` applied there
/// carrying an `ItemState` field at 8, the access renders `->state` and
/// each compare names its member; without the application the field is a
/// raw dereference and the constants stay numbers.
#[test]
fn an_applied_enum_field_names_its_accesses() {
    use borer_engine::analysis::utypes::{build_enum, build_struct, parse_type};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let stated = [
        (2u64, "Broken".to_owned()),
        (0u64, "Off".to_owned()),
        (1u64, "On".to_owned()),
    ];
    o.types.insert(
        "ItemState".to_owned(),
        build_enum("ItemState", 4, &stated).unwrap(),
    );
    let fields = vec![(8u64, "state".to_owned(), parse_type("ItemState").unwrap())];
    o.types.insert(
        "Item".to_owned(),
        build_struct("Item", None, &fields, &o.types, 8).unwrap(),
    );
    o.applied.insert(0x3490, parse_type("Item *").unwrap());
    let text = decompile(&p, &a, &o, 0x56c0).unwrap_or_default();
    assert!(text.contains("->state == On"), "{text}");
    assert!(text.contains("->state == Broken"), "{text}");
    let plain = decompile(&p, &a, &Overlay::default(), 0x56c0).unwrap_or_default();
    assert!(plain.contains("== 1") && plain.contains("== 2"), "{plain}");
    assert!(!plain.contains("->state"), "{plain}");
}

/// A parameter used only at one narrower width is declared at that width.
///
/// `TP` sign-extends `a1` from 32 bits before every use, so the header says
/// `int32_t a1` and the body drops the cast, but for the 64-bit product,
/// which an `int` would overflow; `TP2` masks `a1` to a byte, so it is
/// `uint8_t a1` and the mask goes.
#[test]
fn parameters_used_at_one_width_are_typed() {
    let out = dc(0x4c20);
    assert!(
        out.contains("// signature: uint64_t sub_4c20(int32_t a1)"),
        "{out}"
    );
    assert!(out.contains("return (int64_t)a1 * 3;"), "{out}");
    let out = dc(0x4c30);
    assert!(out.contains("(uint8_t a1)"), "{out}");
    assert!(out.contains("return a1 + 1;"), "{out}");
}

/// A declared narrow parameter type drops the casts that agree with it.
///
/// An assert-typed `int a1` needs no `(int64_t)(int32_t)` at its uses and
/// a `bool a2` no `& 0xff`; a `uint64_t a3` used whole stays as it is.
#[test]
fn declared_parameter_types_drop_their_casts() {
    let text = "// signature: void f(int a1, bool a2, uint64_t a3)\nif ((int64_t)(int32_t)a1 < 0) {\n  return;\n}\nrax = (a2 & 0xff) + a3;\n";
    let out = polish(text, 64, &borer_engine::pack::Packs::default());
    assert!(
        out.contains("// signature: void f(int a1, bool a2, uint64_t a3)"),
        "{out}"
    );
    assert!(out.contains("if (a1 < 0) {"), "{out}");
    assert!(out.contains("rax = a2 + a3;"), "{out}");
}

/// A value a block reads twice is written to its register once.
///
/// `RU` computes `a1 + a2 * 8 + 0x10` and stores it twice: the body assigns
/// `rax` once and stores `rax`, instead of spelling the sum at each store.
#[test]
fn values_read_twice_are_written_once() {
    let out = dc(0x4c40);
    assert_eq!(out.matches("a2 * 8").count(), 1, "{out}");
    assert_eq!(out.matches("= rax;").count(), 2, "{out}");
}

/// The trailing jump of an `if` arm becomes the `else` around what it skips.
///
/// The arm ends `goto L_1;` and `L_1:` follows the run at the `if`'s own
/// indentation, so the run is what runs when the condition is false.
#[test]
fn trailing_jumps_of_an_arm_become_an_else() {
    let text = "if (a1 == 1) {\n  rax = sub_1000(a1);\n  goto L_1;\n}\nrax = 20;\nsub_1010(rax);\nL_1:\nreturn rax;\n";
    let out = cleanup(text);
    assert!(
        out.contains("} else {\n  rax = 20;\n  sub_1010(rax);\n}\nreturn rax;"),
        "{out}"
    );
    assert!(!out.contains("goto"), "{out}");
    let entered = "if (a1 == 1) {\n  goto L_1;\n}\nL_2:\nrax = 20;\nif (rax != 0) goto L_2;\nL_1:\nreturn rax;\n";
    let out = cleanup(entered);
    assert!(
        out.contains("L_2:"),
        "a run entered from outside was absorbed:\n{out}"
    );
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

/// A value computed for nobody goes, and a call's result stays.
///
/// `r9` is assigned once and never read, so the line is noise; `rax` holds
/// a call's result, which is dropped only if the call goes with it, and
/// `rcx` is read by the loop's back edge.
#[test]
fn assignments_nothing_reads_are_dropped() {
    let text = "r9 = a2 - a1;\nrax = sub_1000(a1);\nrcx = 0;\ndo {\n  rcx += 1;\n} while (rcx != a2);\nreturn a1;\n";
    let out = cleanup(text);
    assert!(!out.contains("r9"), "{out}");
    assert!(out.contains("rax = sub_1000(a1);"), "{out}");
    assert!(out.contains("rcx = 0;"), "{out}");
    let escaped = "rdx = &local_18;\nsub_1000(rdx);\nreturn 0;\n";
    assert!(cleanup(escaped).contains("rdx = &local_18;"), "{escaped}");
}

/// A float comparison drops the unordered test the compiler branched on.
///
/// `x != y` on floats compiles to a parity branch and then a not-equal
/// branch; C's `!=` is already true when an operand is NaN, so the pair is
/// the comparison alone, and a parity test with no partner is
/// `isunordered`. An integer parity test keeps its marker.
#[test]
fn unordered_float_compares_fold_to_the_comparison() {
    let text = "if (/*p*/ (xmm8, 0) || xmm8 != 0) {\n  return 1;\n}\nif (/*np*/ (xmm6, local_3f0) && xmm6 == local_3f0) {\n  return 2;\n}\nif (rax > 0 || (/*p*/ (rcx, rdx) || rcx != rdx)) {\n  return 3;\n}\nreturn 0;\n";
    let out = cleanup(text);
    assert!(out.contains("if (xmm8 != 0) {"), "{out}");
    assert!(out.contains("if (xmm6 == local_3f0) {"), "{out}");
    assert!(
        out.contains("/*p*/ (rcx, rdx)"),
        "integer parity folded:\n{out}"
    );
    let lone = "if (/*p*/ (xmm6, xmm0)) {\n  return 1;\n}\nif (/*np*/ (xmm3, 0.0f)) {\n  return 2;\n}\nreturn 0;\n";
    let out = cleanup(lone);
    assert!(out.contains("if (isunordered(xmm6, xmm0)) {"), "{out}");
    assert!(out.contains("if (!isunordered(xmm3, 0.0f)) {"), "{out}");
}

/// Stack-passed arguments are parameters, not stack slots.
///
/// `SP5` reads the two words above the shadow space: on the Microsoft
/// convention those are the fifth and sixth arguments, so the header
/// declares them, the body names them, and no local declaration repeats
/// them.
#[test]
fn stack_passed_arguments_are_named_parameters() {
    let out = dc(0x4c90);
    assert!(
        out.contains(
            "sub_4c90(uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5, uint64_t a6)"
        ),
        "{out}"
    );
    assert!(out.contains("return a5 + a6;"), "{out}");
    assert!(!out.contains("arg_"), "{out}");
    assert!(
        !out.contains("uint64_t a5, a6;"),
        "declared as a local:\n{out}"
    );
}

/// Jump tables the jump's operand names, and tables of offsets from a base.
///
/// `JTG` jumps through `[rax * 8 + T]`, the shape GCC emits, and `JTM`
/// loads a 32-bit offset from a table a `lea` addresses and adds the base
/// back, the shape MSVC emits. Both recover as a switch over three cases.
#[test]
fn relative_and_operand_named_jump_tables_resolve() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&0x4cb7).map(Vec::as_slice),
        Some(&[0x4cbe, 0x4cc4, 0x4cca][..])
    );
    assert_eq!(
        a.jump_tables.get(&0x4cf6).map(Vec::as_slice),
        Some(&[0x4cf8, 0x4cfe, 0x4d04][..])
    );
}

/// The conditions a function asserts head its body as its contract.
///
/// `As::Chk` calls an assert macro whose first argument is the text of the
/// condition, so the header lists it without the reader opening the body.
/// A condition naming a string literal carries single quotes, one carrying
/// a brace is left out, and a call whose second argument is not a source
/// path is not an assert.
#[test]
fn asserted_conditions_head_the_body() {
    let out = dc(0x1810);
    assert!(out.contains("// asserts: f.IsValid()"), "{out}");
    let none = dc(0x11c0);
    assert!(!none.contains("// asserts:"), "{none}");
    let text = concat!(
        "sub_1000(\"StringAtom(\\\"empty\\\") != this->name\", \"util/a.h\", 12);\n",
        "sub_1000(\"lambda { x }\", \"util/a.h\", 13);\n",
        "sub_1000(\"plain\", \"not a path\", 14);\n",
        "sub_1000(\"res\", \"util/a.h\", 15);\n",
    );
    let line = asserts_of(text).unwrap_or_default();
    assert_eq!(line, "StringAtom('empty') != this->name, res", "{line}");
    let quoted = dc(0x4d20);
    assert!(
        quoted.contains("// asserts: StringAtom('x') != f"),
        "{quoted}"
    );
    assert!(
        !quoted
            .lines()
            .any(|l| l.starts_with("//") && l.contains('"'))
    );
}

/// A class flows from a typed parameter into the callee it is passed to.
///
/// `PF`'s signature string types its second parameter `Ns::Thing *`, and it
/// passes that parameter straight to `PG`, which no string names: `PG`'s own
/// parameter is that class.
#[test]
fn a_typed_parameter_carries_its_class_into_the_callee() {
    let out = dc(0x4d70);
    assert!(
        out.contains("// signature: uint64_t sub_4d70(Ns::Thing *a1)"),
        "{out}"
    );
}

/// A switch arm that jumps to a returning tail takes the tail in place.
///
/// A compiler's `ToString` dispatches every case to its own one-line
/// return; leaving the jumps in place would put a `goto` on every arm and
/// the answers below the switch.
#[test]
fn switch_arms_take_the_tail_they_jump_to() {
    let text = concat!(
        "switch (a1) {\n",
        "case 0: goto L_1;\n",
        "case 1: goto L_2;\n",
        "case 2: goto L_3;\n",
        "}\n",
        "L_1:\n",
        "return \"zero\";\n",
        "L_2:\n",
        "return \"one\";\n",
        "L_3:\n",
        "sub_1000(a1);\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(out.contains("case 0: return \"zero\";"), "{out}");
    assert!(out.contains("case 1: return \"one\";"), "{out}");
    assert!(
        out.contains("case 2: {\n  sub_1000(a1);\n  return 0;\n}"),
        "{out}"
    );
    assert!(!out.contains("goto"), "{out}");
}

/// A block one jump reaches moves to where the jump is.
///
/// The label is not a shared exit, so the jump and the label both go and
/// nothing is duplicated. A one-line returning tail is copied by the tail
/// rule instead; this one moves the block the tail rule is too small for.
/// A block that can be fallen into from above stays where it is, since
/// moving it would change what runs; the one here is also too long for the
/// tail rule to copy, so nothing else touches it either.
#[test]
fn blocks_one_jump_reaches_move_to_it() {
    let text = concat!(
        "switch (a1) {\n",
        "case 0: goto L_1;\n",
        "case 1: goto L_2;\n",
        "}\n",
        "return 9;\n",
        "L_1:\n",
        "sub_1000(a1);\n",
        "sub_1001(a1);\n",
        "sub_1002(a1);\n",
        "sub_1003(a1);\n",
        "sub_1004(a1);\n",
        "return 1;\n",
        "L_2:\n",
        "return 2;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert!(!out.contains("L_1:") && !out.contains("L_2:"), "{out}");
    assert!(out.contains("case 0: {"), "{out}");
    assert!(out.contains("  sub_1004(a1);"), "{out}");
    assert!(out.contains("case 1: return 2;"), "{out}");
    let falls = concat!(
        "switch (a1) {\n",
        "case 0: goto L_3;\n",
        "}\n",
        "sub_1000(a1);\n",
        "L_3:\n",
        "sub_1001(a1);\n",
        "sub_1002(a1);\n",
        "sub_1003(a1);\n",
        "sub_1004(a1);\n",
        "sub_1005(a1);\n",
        "sub_1006(a1);\n",
        "sub_1007(a1);\n",
        "sub_1008(a1);\n",
        "sub_1009(a1);\n",
        "return 1;\n",
    );
    let out = cleanup(falls);
    assert!(
        out.contains("L_3:") && out.contains("goto L_3;"),
        "a block reachable from above moved: {out}"
    );
}

/// A shared tail that nests still copies to the jumps that share it.
///
/// The exit tests a flag before returning, so the run holds a block; its
/// braces balance before the `return`, which is what makes copying it safe.
#[test]
fn shared_tails_may_nest() {
    let text = concat!(
        "if (a1 == 0) goto L_1;\n",
        "if (a1 == 1) goto L_1;\n",
        "rax = sub_2000(a1);\n",
        "return rax;\n",
        "L_1:\n",
        "if (a2 != 0) {\n",
        "  sub_1000(a2);\n",
        "}\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("sub_1000(a2);").count(), 2, "{out}");
    assert!(out.contains("if (a2 != 0) {"), "{out}");
}

/// A value the body computes is returned though no caller reads it.
///
/// `NR`'s only caller drops its result, but every exit of `NR` returns the
/// product it computed itself: an unread result is still a result, so the
/// header keeps it rather than call the function `void`.
#[test]
fn a_computed_result_no_caller_reads_is_kept() {
    let out = dc(0x4da0);
    assert!(!out.contains("// signature: void "), "{out}");
    assert!(!out.contains("return;"), "{out}");
    assert!(out.contains("return 5 * a1;"), "{out}");
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

/// A callee that only passes its arguments on still takes them.
///
/// `FW2` reads no argument register in its own body, it makes room on the
/// stack and calls `FW3`, which reads `rcx`; counting only what `FW2` reads
/// would drop the `0x77` from the call and lose what was passed.
#[test]
fn a_forwarded_argument_survives_the_call_that_forwards_it() {
    let out = dc(0x4e90);
    assert!(out.contains("sub_4eb0(119)"), "{out}");
}

/// A function names its own fields from its own assertions.
///
/// `Der::Chk` guards on the field at 8 and asserts `this->count` about it,
/// which is both halves of the name inside one function; knowing the class
/// is what the named decompile needs, and most functions have no name to
/// take a class from, so the plain decompile names it too.
#[test]
fn a_function_names_the_fields_its_own_asserts_name() {
    let out = dc(0x19a0);
    assert!(out.contains("if (this->count == 0) {"), "{out}");
    assert!(!out.contains("field_0x8"), "{out}");
}

/// A dispatch through a byte index table switches on the value.
///
/// `JTX`'s byte table folds five values onto two bodies, and the case
/// labels the resolver produces are those values; writing the switch on the
/// byte load would make `case 1` mean the second slot of the jump table
/// rather than the value 1.
#[test]
fn a_switch_through_an_index_table_reads_the_value() {
    let out = dc(0x4f20);
    assert!(!out.contains("uint8_t*"), "{out}");
    assert!(out.contains("case 0: case 2: case 4:"), "{out}");
    assert!(out.contains("case 1: case 3:"), "{out}");
}

/// A call through a one-instruction thunk takes the arguments it reads.
///
/// `TJ` is a bare `jmp`, so it reads no argument register itself; counting
/// only what it reads left the call open-ended and it printed `edx` too,
/// which `FW3` at the end of the jump never reads.
#[test]
fn a_call_through_a_jump_thunk_stops_at_what_it_reads() {
    let out = dc(0x4f70);
    assert!(out.contains("sub_4f60(85)"), "{out}");
    assert!(!out.contains("102"), "{out}");
}

/// A function's header says what its callers pass it.
///
/// `PT` reads one argument and its two callers set it to 7 and to 9, so the
/// values a parameter is called with are in the header rather than in every
/// call site a reader would otherwise have to visit.
#[test]
fn the_header_says_what_callers_pass() {
    let out = dc(0x4fd0);
    assert!(out.contains("// callers pass: a1 = 7, 9"), "{out}");
}

/// A field at offset zero takes its name from an assertion too.
///
/// `GZ` guards on `*(uint32_t*)this` and asserts `this->head` about it; the
/// offset-zero spelling has no `+ 0` for the renamer to find, so it needs
/// the form of its own that the layout pass already uses.
#[test]
fn an_assert_names_the_field_at_offset_zero() {
    let out = dc(0x5000);
    assert!(out.contains("if (this->head == 0) {"), "{out}");
}

/// The assertion need not be the line after its guard.
///
/// `GG` calls `ReportAssertFailure` between the two, which is what a caller that
/// spells its own signature out first looks like; the guard is still the
/// nearest line above that opens a block.
#[test]
fn an_assert_a_line_below_its_guard_still_names_the_field() {
    let out = dc(0x5040);
    assert!(out.contains("if (this->tail == 0) {"), "{out}");
}

/// A serializer's header states the message's wire format.
///
/// `EC` hands its stream a 32-bit field and then a 1-bit one; recovering
/// that from an encoder is the work an analyst does by hand for every
/// message in a protocol, and the encoder already states it. Its stream
/// class `Network::Bs` carries no stream word, so the line needs the Nebula
/// pack's `stream Network::`.
#[test]
fn a_serializer_header_states_the_wire_format() {
    assert!(!dc(0x50c0).contains("// wire:"));
    let out = dc_nebula(0x50c0);
    assert!(
        out.contains("// wire: 32 bits a1+0x20, 1 bit a1+0x24"),
        "{out}"
    );
}

/// A function returning floating point hands the value back in xmm0.
///
/// `Fr::Get` multiplies two of its own floats and returns the product,
/// which never touches `rax`; reading `rax` at the return leaves the
/// multiply dead and hands back a register the function never set.
#[test]
fn a_float_return_comes_back_in_the_float_register() {
    let out = dc(0x5130);
    assert!(
        out.contains(
            "return *(float*)((uintptr_t)this + 0x10) * *(float*)((uintptr_t)this + 0x14);"
        ),
        "{out}"
    );
}

/// A function's header names the source file it came from.
///
/// `Der::Chk` asserts, and an assertion cites the file it was written in,
/// so the function says which subsystem it belongs to; answering that
/// otherwise means reading its callers.
#[test]
fn a_function_header_names_its_source_file() {
    let out = dc(0x19a0);
    assert!(out.contains("// source: util/fourcc.h"), "{out}");
}

/// An indexed read keeps its expression when its base has a layout.
///
/// `CM` reads three plain fields, which earns its object a layout, and then
/// indexes an array beginning at the first of them; taking the offset from
/// the front of that operand rewrote half the expression away and left text
/// that does not parse.
#[test]
fn an_indexed_read_is_not_rewritten_as_a_field() {
    let out = dc(0x5200);
    for line in out.lines() {
        assert_eq!(
            line.matches('(').count(),
            line.matches(')').count(),
            "unbalanced: {out}"
        );
    }
    assert!(out.contains("a2 * 8"), "{out}");
}

/// Every goto lands on a label when a loop is entered below its lowest
/// block.
///
/// `LB`'s loop begins at 0x5247 but is only ever entered at 0x525f, and the
/// blocks between them are written before either. The emitter used to hand
/// 0x5247 to the loop's entry, take the entry's word that the block was
/// written, and drop its label while the jump back to it stayed.
#[test]
fn a_loop_entered_below_its_first_block_keeps_its_label() {
    let out = dc(0x5240);
    let labels: std::collections::BTreeSet<&str> = out
        .lines()
        .filter_map(|l| l.trim().strip_suffix(':'))
        .filter(|l| l.starts_with("L_"))
        .collect();
    for line in out.lines() {
        let t = line.trim();
        let Some(target) = t
            .strip_prefix("goto ")
            .or_else(|| t.rsplit_once(") goto ").map(|(_, g)| g))
            .and_then(|g| g.strip_suffix(';'))
            .filter(|g| g.starts_with("L_"))
        else {
            continue;
        };
        assert!(labels.contains(target), "{target} has no label: {out}");
    }
}

/// A branch that leaves the function is a computed goto, not a label.
///
/// `JO` branches to 0x3000, which is `.data`: no block of the function
/// starts there, so a `goto L_3000;` would name a label the text never
/// writes.
#[test]
fn a_branch_that_leaves_is_a_computed_goto() {
    let out = dc(0x52a0);
    assert!(out.contains("goto *0x3000;"), "{out}");
    assert!(!out.contains("L_3000"), "{out}");
}

/// The code a loop breaks to is still there.
///
/// `BC`'s loops are left only by a `break` under a condition. Reading that
/// as no break at all made the loop endless, and everything after it was
/// dropped as text nothing reaches: the call to `E` disappeared.
#[test]
fn a_loop_left_by_a_conditional_break_keeps_what_follows() {
    let out = dc(0x52c0);
    assert!(
        out.contains("sub_5312"),
        "the call after the loops is gone: {out}"
    );
    for callee in ["sub_5300", "sub_5306", "sub_530c"] {
        assert!(out.contains(callee), "{callee} is missing: {out}");
    }
}

/// A loop two levels deep does not swallow the outer loop's break.
///
/// `NL` nests three loops, so the outer one's `break` stands below a brace
/// that closes two levels in. Counting nested loops without minding the
/// indent each closes at left that break unseen, the outer loop endless,
/// and the last call dropped as text nothing reaches.
#[test]
fn a_break_below_a_nested_loop_still_leaves_the_outer_one() {
    let out = dc(0x5320);
    assert!(
        out.contains("sub_5378"),
        "the call after the loops is gone: {out}"
    );
}

/// A break belongs to the loop it stands in.
///
/// `NB` runs a loop inside a loop, and the inner body jumps both back to
/// the outer loop's header and out past it. Written as the inner loop's
/// `continue` and `break` those jumps left the wrong loop, and the block
/// after the outer loop, which nothing else reaches, went with them. Each
/// block hands its own number to 0x5445, so a missing one is plain.
#[test]
fn a_break_leaves_the_loop_it_stands_in() {
    let out = dc(0x5390);
    for n in 1..=11 {
        assert!(
            out.contains(&format!("({n})")),
            "block {n} is missing: {out}"
        );
    }
    assert!(
        out.contains("goto L_5390;"),
        "the jump back to the outer loop reads as the inner one's continue: {out}"
    );
}

/// A block that continues its own loop is not moved into another one.
///
/// `SL` runs two loops side by side inside a third, and one jumps into the
/// middle of the other. The block it lands on ends by continuing its own
/// loop; moved to the jump it continued the loop there instead, and the
/// rest of its loop was left reachable by nothing. Each block hands its own
/// number to 0x54cd, so a missing one is plain.
#[test]
fn a_block_that_continues_its_loop_stays_in_it() {
    let out = dc(0x5450);
    for n in 1..=8 {
        assert!(
            out.contains(&format!("({n})")),
            "block {n} is missing: {out}"
        );
    }
}

/// A float moved into a vector register leaves the rest of it alone.
///
/// `MS` loads four floats from `rcx+0x10`, then writes one from `rdx+0x20`
/// over the lowest of them. Read as a whole-register copy, the four loaded
/// floats were lost and the store wrote only the single one.
#[test]
fn a_movss_between_registers_keeps_the_rest() {
    let out = dc(0x54e0);
    assert!(out.contains("movss("), "the merge is gone: {out}");
    assert!(
        out.contains("a1 + 0x10"),
        "the vector it merges into is gone: {out}"
    );
}

/// A switch arm whose block is already written keeps its case.
///
/// `SW` reaches its arms before the dispatch is printed, so every arm the
/// table names is already on the page by then. Skipping those arms left an
/// empty `switch` and two blocks nothing reached. Each block hands its own
/// number to 0x553f, so a missing one is plain.
#[test]
fn a_switch_arm_already_written_keeps_its_case() {
    let out = dc(0x5500);
    for n in 1..=4 {
        assert!(
            out.contains(&format!("({n})")),
            "block {n} is missing: {out}"
        );
    }
    assert!(out.contains("case "), "the switch has no arms: {out}");
}

/// Dropping a returned value keeps the call that produced it.
///
/// `TR` tail-calls `TG` and its only caller ignores what comes back, so the
/// value is not worth printing. The call is: rewriting `return f(x);` as
/// `return;` took the call with it.
#[test]
fn a_dropped_return_value_keeps_its_call() {
    let out = dc(0x5550);
    assert!(out.contains("sub_5560("), "the tail call is gone: {out}");
}

/// An argument that travels in a vector register is still an argument.
///
/// `FP` reads `xmm1`, which is where the second argument goes when it is a
/// float, and `FC` passes one there. Reading only `rcx`, `rdx`, `r8` and
/// `r9` left the argument out of the signature and out of the call.
#[test]
fn a_float_argument_is_a_parameter_and_shows_at_the_call() {
    let callee = dc(0x5580);
    assert!(callee.contains("float a2"), "{callee}");
    let caller = dc(0x5590);
    assert!(
        caller.contains("sub_5580(a2, *(float*)a2)"),
        "the float is missing: {caller}"
    );
}

/// A System V floating argument is still an argument.
///
/// The convention counts its integer and floating arguments separately:
/// `SF` takes an integer in `rdi` and a double in `xmm0`, and `SC` passes
/// one of each. The float mask left the double out of the callee's
/// signature and out of the call, as no register carried it.
///
/// # Panics
///
/// When the double is missing from either text.
#[test]
fn a_sysv_float_argument_is_a_parameter_and_shows_at_the_call() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    // SC 0x140001000: mov edi,5; movsd xmm0,[2.5]; call SF; ret
    let mut code = vec![
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xf2, 0x0f, 0x10, 0x05, 0xf3, 0x0f, 0x00,
        0x00, // ASM: movsd xmm0,[rip+0xff3] -> 0x140002000
        0xe8, 0x0e, 0x00, 0x00, 0x00, // ASM: call 0x140001020 (SF)
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    // SF 0x140001020: mulsd xmm0,xmm0; cvttsd2si rax,xmm0; add rax,rdi; ret
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x59, 0xc0, // ASM: mulsd xmm0,xmm0
        0xf2, 0x48, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si rax,xmm0
        0x48, 0x01, 0xf8, // ASM: add rax,rdi
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    // 2.5 as a double at 0x140002000.
    bytes.extend_from_slice(&2.5f64.to_le_bytes());
    bytes.resize(0x2000, 0);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
            Section::mapped(".rodata", 0x1_4000_2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    let callee = decompiled(&p, 0x1_4000_1020);
    assert!(callee.contains("float a2"), "{callee}");
    let caller = decompiled(&p, 0x1_4000_1000);
    assert!(
        caller.contains("sub_140001020(5, 2.5)"),
        "the double is missing: {caller}"
    );
}

/// A singleton getter's result resolves the virtual call on it.
///
/// `GV` calls slot 1 through the result of `GG`, which returns the global
/// that holds a `Ns::Thing`, so the call resolves to the table's slot 1
/// (`S4`) instead of `->vtable[1]`.
#[test]
fn getter_results_resolve_virtual_calls() {
    let out = dc(0x1c20);
    assert!(out.contains("->sub_1bf0("), "{out}");
    assert!(!out.contains("->vtable["), "{out}");
}

/// A smart pointer's arrow operator types the call it feeds.
///
/// `PA` is declared `class Der *__cdecl Core::Ptr<class Der>::operator
/// ->(void) const`, a signature whose `->` once broke the parse, so it is
/// named and returns `Der *`; `PB` calls slot 1 through its result, which
/// resolves to `Der`'s method.
#[test]
fn arrow_operator_signatures_type_their_results() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let pa = a.function(0x1b90).expect("PA");
    assert_eq!(pa.name.as_deref(), Some("Core::Ptr<Der>::operator ->"));
    let pb = decompile(&p, &a, &o, 0x1ba0).unwrap_or_default();
    let der_slot1 = borer_engine::analysis::name_of(&a, &o, 0x1200);
    assert!(pb.contains(&format!("->{der_slot1}(")), "{pb}");
    assert!(!pb.contains("->vtable["), "{pb}");
}

/// A virtual call nothing resolves names its slot.
///
/// `VU` calls slot 2 of `a1`'s vtable and no declaration types `a1`, so
/// the call reads `a1->vtable[2]()` with the receiver dropped from the
/// arguments instead of the double dereference.
#[test]
fn unresolved_virtual_calls_name_their_slot() {
    let out = dc(0x1b80);
    assert!(out.contains("a1->vtable[2]()"), "{out}");
    assert!(!out.contains("(*(uint64_t*)(*(uint64_t*)"), "{out}");
}

/// The skeleton's header is one line.
///
/// `ES`'s full text opens with the `// exported_es @ ...` line, the
/// `// signature:` line and an escape note; its skeleton folds the
/// signature into the header and drops the note.
#[test]
fn skeleton_header_is_one_line_without_notes() {
    let full = dc(0x1410);
    assert!(full.contains("// signature: "), "{full}");
    assert!(full.contains("// note: "), "{full}");
    let sk = skeleton(&full);
    let head = sk.lines().next().unwrap_or_default();
    assert!(
        head.starts_with("// uint64_t exported_es(") && head.contains(") @ 0x1410: "),
        "{sk}"
    );
    assert!(!sk.contains("// signature: "), "{sk}");
    assert!(!sk.contains("// note: "), "{sk}");
}

/// Template arguments shrink to `<..>` in the skeleton.
///
/// `Der::Use` is declared `void Der::Use(const class Core::Ptr<class Der>
/// &)`, so its full text names the parameter `Core::Ptr<Der>` and its
/// skeleton `Core::Ptr<..>`.
#[test]
fn skeleton_elides_template_arguments() {
    let full = dc(0x17b0);
    assert!(full.contains("Core::Ptr<Der>"), "{full}");
    let sk = skeleton(&full);
    assert!(sk.contains("Core::Ptr<..>"), "{sk}");
    assert!(!sk.contains("Core::Ptr<Der>"), "{sk}");
}

/// The skeleton folds an assert helper called outright.
///
/// `AH` calls `AK("n == 1", "n must be one", "src/ah.cc", 0x1c2)`, which
/// the full text shows as the call and the skeleton as `assert(n == 1);`.
#[test]
fn skeleton_folds_assert_helper_calls() {
    let full = dc(0x1b50);
    assert!(
        full.contains("sub_1b40(\"n == 1\", \"n must be one\", \"src/ah.cc\", 0x1c2);"),
        "{full}"
    );
    let sk = skeleton(&full);
    assert!(sk.contains("assert(n == 1);"), "{sk}");
    assert!(!sk.contains("sub_1b40"), "{sk}");
}

/// The skeleton folds a guarded assert into one line: `AG`'s
/// `if (this == 0) { ReportAssertFailure("f.IsValid()", ...); }` becomes
/// `assert(f.IsValid());` while the full text keeps the guard.
#[test]
fn skeleton_folds_guarded_asserts() {
    let full = dc(0x1840);
    assert!(full.contains("if (this == 0) {"), "{full}");
    let skel = skeleton(&full);
    assert!(skel.contains("assert(f.IsValid());"), "{skel}");
    assert!(!skel.contains("ReportAssertFailure"), "{skel}");
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

/// Double-precision shifts by a constant and `xgetbv` lift.
///
/// `SD` renders `(a1 << 8) | (a2 >> 0x18)` and `XG` returns `xgetbv(a1)`,
/// neither with an asm comment.
#[test]
fn double_shifts_and_xgetbv_lift() {
    let sd = dc(0x18a0);
    assert!(!sd.contains("/*"), "{sd}");
    assert!(sd.contains("(a1 << 8) | (a2 >> 0x18)"), "{sd}");
    let xg = dc(0x18b0);
    assert!(!xg.contains("/*"), "{xg}");
    assert!(xg.contains("xgetbv("), "{xg}");
}

/// A parameter class hinted by callers shows in the header: `HT`, called
/// by `Der::Tick` with its `this`, renders `uint32_t sub_18d0(Der *a1)`.
#[test]
fn hinted_parameter_classes_render_in_the_header() {
    let text = dc(0x18d0);
    assert!(
        text.contains("// signature: uint32_t sub_18d0(Der *a1)"),
        "{text}"
    );
}

/// Hinted result and field classes drive headers and virtual calls.
///
/// `GT` heads `Base *sub_18e0(Der *a1)`, and `Der::Poll`'s call through the
/// vtable of its field at 0x10 resolves to `Base`'s slot 1.
#[test]
fn hinted_results_and_fields_resolve_virtual_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let gt = decompile(&p, &a, &o, 0x18e0).unwrap_or_default();
    assert!(gt.contains("// signature: Base *sub_18e0(Der *a1)"), "{gt}");
    let poll = decompile(&p, &a, &o, 0x18f0).unwrap_or_default();
    let method = |va: u64| {
        let full = borer_engine::analysis::name_of(&a, &o, va);
        full.rsplit("::").next().unwrap_or(&full).to_owned()
    };
    let slot = method(0x11e0);
    assert!(poll.contains(&format!("->{slot}(")), "{poll}");
    let wait = decompile(&p, &a, &o, 0x1920).unwrap_or_default();
    let der_slot1 = method(0x1200);
    assert!(wait.contains(&format!("->{der_slot1}(")), "{wait}");
    let peek = decompile(&p, &a, &o, 0x1960).unwrap_or_default();
    assert!(peek.contains(&format!("rax->{der_slot1}(")), "{peek}");
    let local = decompile(&p, &a, &o, 0x1a00).unwrap_or_default();
    assert!(local.contains("Fac::Make(&local_"), "{local}");
    assert!(local.contains(&format!("->{der_slot1}(")), "{local}");
}

/// A function named after a class through its vtable slot, with that class
/// hinted for its first parameter, is a method: `Der::Foo` heads
/// `uint32_t Der::Foo(Der *this)`.
#[test]
fn slot_named_methods_get_this() {
    let text = dc(0x1870);
    assert!(
        text.contains("// signature: uint32_t Der::Foo(Der *this)"),
        "{text}"
    );
}

/// The named variant renders fields by their assert-derived names.
///
/// `Der::Chk`'s guard reads `this->count`, and `Der::Cmp` copies
/// `a2->count` from its `Der *` parameter. `Der::Cmp` asserts nothing
/// itself, so only the class knows what its field is called and the plain
/// decompile leaves it an offset.
#[test]
fn named_decompile_renders_fields_by_name() {
    use borer_engine::analysis::decompile::decompile_named;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile_named(&p, &a, &o, 0x19a0).unwrap_or_default();
    assert!(text.contains("if (this->count == 0) {"), "{text}");
    let plain = decompile(&p, &a, &o, 0x19d0).unwrap_or_default();
    assert!(!plain.contains("->count"), "{plain}");
    let cmp = decompile_named(&p, &a, &o, 0x19d0).unwrap_or_default();
    assert!(cmp.contains("this->count = a2->count;"), "{cmp}");
}

/// Singletons render by their class, under the name a pack gives the
/// static.
///
/// `Tls::Tls` stores `Tls::instance = this;` and `TU` reads `Tls::instance`
/// through the same TLS walk; a pack naming the static `Singleton` makes it
/// `Tls::Singleton`. A global singleton (`GU` through `Glob::Glob`'s global)
/// resolves its virtual call.
#[test]
fn tls_singletons_render_by_class() {
    let tc = dc(0x1a60);
    assert!(tc.contains("Tls::instance = this;"), "{tc}");
    let tu = dc(0x1a90);
    assert!(tu.contains("Tls::instance"), "{tu}");
    assert!(!tu.contains("gs + 0x58"), "{tu}");
    let gu = dc(0x1b00);
    assert!(gu.contains("g64_27c0->"), "{gu}");
    let named = dc_nebula(0x1a60);
    assert!(named.contains("Tls::Singleton = this;"), "{named}");
}

/// A receiver the class machinery names as a singleton resolves its virtual
/// call, and one whose class holds no table does not.
///
/// `GU` calls slot 1 through the global that holds the one `Glob`, and `TW`
/// walks `TU`'s TLS path for the singleton of `T2`, a class whose
/// constructor stores a vtable, so both calls resolve to the slot's
/// function; `TU`'s `Tls` registered a singleton but has no table, so its
/// call still names the slot.
#[test]
fn singleton_receivers_resolve_their_virtual_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let method = |va: u64| {
        let full = borer_engine::analysis::name_of(&a, &o, va);
        full.rsplit("::").next().unwrap_or(&full).to_owned()
    };
    let gu = decompile(&p, &a, &o, 0x1b00).unwrap_or_default();
    let glob_slot1 = method(0x13a0);
    assert!(gu.contains(&format!("g64_27c0->{glob_slot1}(")), "{gu}");
    let tw = decompile(&p, &a, &o, 0x57a0).unwrap_or_default();
    let t2_slot1 = method(0x57c6);
    assert!(tw.contains(&format!("T2::instance->{t2_slot1}(")), "{tw}");
    assert!(!tw.contains("->vtable["), "{tw}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x57a0),
        vec![0x57c6]
    );
    let tu = decompile(&p, &a, &o, 0x1a90).unwrap_or_default();
    assert!(tu.contains("Tls::instance->vtable[1]()"), "{tu}");
}

/// A member field a constructor types resolves the calls made through it.
///
/// `Wrap::Wrap` inlines the base's initializing store, writing `WBase`'s
/// vtable at `[this+8]`, so the embedded subobject at 8 is a `WBase`:
/// `Wrap::Call`'s call through that field's vtable resolves to `WBase`'s
/// slot 1. `Wrap::Miss` calls through the field at 0x10, which nothing
/// types, and its call still names the slot.
#[test]
fn embedded_field_receivers_resolve_their_virtual_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let ctor = decompile(&p, &a, &o, 0x5800).unwrap_or_default();
    assert!(ctor.contains("&WBase::vftable;"), "{ctor}");
    let call = decompile(&p, &a, &o, 0x5830).unwrap_or_default();
    let slot1 = borer_engine::analysis::name_of(&a, &o, 0x5876);
    assert!(call.contains(&format!("{slot1}(this);")), "{call}");
    assert!(!call.contains("->vtable["), "{call}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x5830),
        vec![0x5876]
    );
    let miss = decompile(&p, &a, &o, 0x5850).unwrap_or_default();
    assert!(miss.contains("->vtable[1]()"), "{miss}");
}

/// A call result read two instructions later is still the call's result:
/// `UR` assigns `rax = P();` before `mov edx, 5` and passes it to `Q`.
#[test]
fn call_results_read_later_are_assigned() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x17d0).unwrap_or_default();
    let callee = borer_engine::analysis::name_of(&a, &o, 0x1200);
    assert!(text.contains(&format!("rax = {callee}(")), "{text}");
}

/// `FA`: one edge compares `eax` while `edx` holds the same value, the other
/// compares `edx`; both are re-expressed over `edx` and the `setl` lifts.
#[test]
fn aliased_comparison_on_both_edges_survives_the_join() {
    let out = dc(0x1470);
    assert!(!out.contains("/* setl"), "{out}");
    assert!(out.contains("rdx < 5"), "{out}");
}

/// `Y` and `W3` end at their noreturn calls: nothing after the call is rendered.
#[test]
fn noreturn_calls_end_the_text() {
    let y = dc(0x1270);
    assert!(y.contains("ExitProcess(1);"), "{y}");
    assert!(!y.contains("return 3;"), "Z's body leaked into Y:\n{y}");
    let w3 = dc(0x12d0);
    assert!(w3.contains("sub_12b0(3);"), "{w3}");
    assert!(!w3.contains("return 5;"), "dead tail survived:\n{w3}");
}

/// `U` (call through the thunk) and `V` (call through the IAT slot) both
/// render as `ReportAssertFailure();`, never as an indirect call.
#[test]
fn import_calls_render_by_name() {
    let u = dc(0x1220);
    assert!(
        u.contains("ReportAssertFailure();"),
        "thunk call not named:\n{u}"
    );
    let v = dc(0x1230);
    assert!(
        v.contains("ReportAssertFailure();"),
        "IAT call not named:\n{v}"
    );
    assert!(!v.contains("indirect"), "IAT call left indirect:\n{v}");
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

/// An import call stops at the arity its prototype declares.
///
/// A call to an import lands on a thunk or a table slot, so nothing in the
/// binary says how many arguments it takes and the renderer pads the call to
/// the four register slots with whatever the caller's own parameters hold.
/// `Y` sets one argument and calls `ExitProcess`, which takes one.
#[test]
fn an_import_call_stops_at_its_declared_arity() {
    let out = dc(0x1270);
    assert!(out.contains("ExitProcess(1)"), "{out}");
}

/// A switch on a parameter decompiled under a value of it reads as that
/// one case: `D`'s table sends 2 to the case returning 3.
#[test]
fn a_scenario_takes_one_case_of_a_switch() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = decompile(&p, &a, &o, 0x1060).unwrap_or_default();
    assert!(all.contains("switch"), "{all}");
    let two = decompile_scenario(&p, &a, &o, 0x1060, &[(0, 2)]).unwrap_or_default();
    assert!(two.starts_with("// scenario: a1 = 2; "), "{two}");
    assert!(!two.contains("switch"), "{two}");
    assert!(two.contains("return 3;"), "{two}");
    assert!(!two.contains("return 4;"), "{two}");
}

/// `ptest` lifts to the test of the lanes the code reads, and a lane
/// extracted into memory to the extract; neither is left as asm.
#[test]
fn packed_tests_and_extracts_lift() {
    let code: &[u8] = &[
        0xf3, 0x0f, 0x6f, 0x01, // movdqu xmm0,[rcx]
        0xf3, 0x0f, 0x6f, 0x0a, // movdqu xmm1,[rdx]
        0x66, 0x0f, 0x38, 0x17, 0xc1, // ptest xmm0,xmm1
        0x0f, 0x94, 0xc0, // sete al
        0x66, 0x41, 0x0f, 0x3a, 0x16, 0x00, 0x01, // pextrd [r8],xmm0,1
        0x0f, 0xb6, 0xc0, // movzx eax,al
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("/*"), "{text}");
    assert!(text.contains("== 0"), "{text}");
    assert!(text.contains("pextrd("), "{text}");
}

/// Inside a loop, a branch whose one side leaves the loop (here to a
/// return) and whose other side stays is `if (leaves) { return 1; }`,
/// with the staying side following, not a goto to the staying side.
#[test]
fn a_loop_exit_is_the_arm_and_the_staying_side_follows() {
    let code: &[u8] = &[
        0xbb, 0x03, 0x00, 0x00, 0x00, // mov ebx,3
        0xe8, 0x36, 0x00, 0x00, 0x00, // loop: call g
        0x85, 0xc0, // test eax,eax
        0x74, 0x09, // jz join
        0xe8, 0x3d, 0x00, 0x00, 0x00, // call h
        0x85, 0xc0, // test eax,eax
        0x75, 0x19, // jne exit
        0xff, 0xcb, // join: dec ebx
        0x75, 0xea, // jne loop
        0x31, 0xc0, // xor eax,eax
        0xc3, // ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, //
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, //
        0xb8, 0x01, 0x00, 0x00, 0x00, // exit: mov eax,1
        0xc3, // ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, //
        0x8b, 0x01, // g: mov eax,[rcx]
        0xc3, // ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, //
        0x8b, 0x41, 0x04, // h: mov eax,[rcx+4]
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("return 1;"), "{text}");
}

/// A branch at the end of an `if` arm whose jump side is the arm's join
/// falls into the join.
///
/// The other side is the guarded statement (`if (ecx == 7) break;`), not
/// `if (ecx != 7) goto L_join; break;`.
#[test]
fn a_branch_ending_an_arm_falls_into_the_join() {
    let code: &[u8] = &[
        0x31, 0xc0, // xor eax,eax
        0x8b, 0x0a, // loop: mov ecx,[rdx]
        0x85, 0xc9, // test ecx,ecx
        0x75, 0x0b, // jnz cold
        0x48, 0x83, 0xc2, 0x04, // tail: add rdx,4
        0x41, 0xff, 0xc8, // dec r8d
        0x75, 0xf1, // jnz loop
        0xeb, 0x07, // jmp exit
        0x01, 0xc8, // cold: add eax,ecx
        0x83, 0xf9, 0x07, // cmp ecx,7
        0x75, 0xee, // jne tail
        0x83, 0xf9, 0x01, // exit: cmp ecx,1 (too many blocks to absorb)
        0x74, 0x2a, // je done
        0x83, 0xf9, 0x02, // cmp ecx,2
        0x74, 0x25, // je done
        0x83, 0xf9, 0x03, // cmp ecx,3
        0x74, 0x20, // je done
        0x83, 0xf9, 0x04, // cmp ecx,4
        0x74, 0x1b, // je done
        0x83, 0xf9, 0x05, // cmp ecx,5
        0x74, 0x16, // je done
        0x83, 0xf9, 0x06, // cmp ecx,6
        0x74, 0x11, // je done
        0x83, 0xf9, 0x07, // cmp ecx,7
        0x74, 0x0c, // je done
        0x83, 0xf9, 0x08, // cmp ecx,8
        0x74, 0x07, // je done
        0x83, 0xf9, 0x09, // cmp ecx,9
        0x74, 0x02, // je done
        0x31, 0xc0, // xor eax,eax
        0xc3, // done: ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("== 7) break;"), "{text}");
}

/// A compare ladder on one value with three or more bodies is a `switch`,
/// whether the compiler compared the value each time or counted it down.
#[test]
fn a_compare_ladder_is_a_switch() {
    let cmp: &[u8] = &[
        0x83, 0xf9, 0x01, // cmp ecx,1
        0x74, 0x0d, // je one
        0x83, 0xf9, 0x02, // cmp ecx,2
        0x74, 0x0e, // je two
        0x83, 0xf9, 0x03, // cmp ecx,3
        0x74, 0x0f, // je three
        0x31, 0xc0, // xor eax,eax
        0xc3, // ret
        0xb8, 0x0a, 0x00, 0x00, 0x00, // one: mov eax,10
        0xc3, // ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // two: mov eax,20
        0xc3, // ret
        0xb8, 0x1e, 0x00, 0x00, 0x00, // three: mov eax,30
        0xc3, // ret
    ];
    let sub: &[u8] = &[
        0x83, 0xe9, 0x01, // sub ecx,1
        0x74, 0x0d, // je one
        0x83, 0xe9, 0x01, // sub ecx,1
        0x74, 0x0e, // je two
        0x83, 0xe9, 0x01, // sub ecx,1
        0x74, 0x0f, // je three
        0x31, 0xc0, // xor eax,eax
        0xc3, // ret
        0xb8, 0x0a, 0x00, 0x00, 0x00, // one: mov eax,10
        0xc3, // ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // two: mov eax,20
        0xc3, // ret
        0xb8, 0x1e, 0x00, 0x00, 0x00, // three: mov eax,30
        0xc3, // ret
    ];
    for code in [cmp, sub] {
        let p = program64(code);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(!text.contains("goto"), "{text}");
        assert!(text.contains("switch (a1)"), "{text}");
        for label in ["case 1:", "case 2:", "case 3:", "default:"] {
            assert!(text.contains(label), "{label}\n{text}");
        }
        assert!(text.contains("return 20;"), "{text}");
    }
}

/// A compare tree whose misses land in two different blocks (a range
/// split to one, the last compare's miss to another) is no `switch`, which
/// has one default: it stays an `if` chain.
#[test]
fn a_tree_with_two_residual_leaves_stays_an_if_chain() {
    let code: &[u8] = &[
        0x83, 0xf9, 0x01, // cmp ecx,1
        0x74, 0x12, // je one
        0x83, 0xf9, 0x0a, // cmp ecx,10
        0x7f, 0x13, // jg big
        0x83, 0xf9, 0x02, // cmp ecx,2
        0x74, 0x14, // je two
        0x83, 0xf9, 0x03, // cmp ecx,3
        0x74, 0x15, // je three
        0x31, 0xc0, // xor eax,eax
        0xc3, // ret
        0xb8, 0x0a, 0x00, 0x00, 0x00, // one: mov eax,10
        0xc3, // ret
        0xb8, 0x63, 0x00, 0x00, 0x00, // big: mov eax,99
        0xc3, // ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // two: mov eax,20
        0xc3, // ret
        0xb8, 0x1e, 0x00, 0x00, 0x00, // three: mov eax,30
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("switch ("), "{text}");
    assert!(text.contains("return 99;"), "{text}");
    assert!(text.contains("return 30;"), "{text}");
}

/// Inside a `do` loop, a switch arm that jumps to the loop's condition
/// `continue`s.
///
/// The jump passes through the switch, which only a `break` binds to, and
/// the condition is where a do-while's `continue` goes.
#[test]
fn a_switch_arm_jumping_to_the_latch_continues() {
    let code: &[u8] = &[
        0x31, 0xc0, // xor eax,eax
        0x8b, 0x0a, // loop: mov ecx,[rdx]
        0x83, 0xf9, 0x01, // cmp ecx,1
        0x74, 0x0e, // je one
        0x83, 0xf9, 0x02, // cmp ecx,2
        0x74, 0x0e, // je two
        0x83, 0xf9, 0x03, // cmp ecx,3
        0x74, 0x0e, // je three
        0x01, 0xc8, // add eax,ecx
        0xeb, 0x0d, // jmp post
        0x83, 0xc0, 0x0a, // one: add eax,10
        0xeb, 0x08, // jmp post
        0x83, 0xc0, 0x14, // two: add eax,20
        0xeb, 0x0c, // jmp latch
        0x83, 0xc0, 0x1e, // three: add eax,30
        0xff, 0xc0, // post: inc eax
        0x48, 0x83, 0xc2, 0x04, // add rdx,4
        0x41, 0xff, 0xc0, // inc r8d
        0x45, 0x39, 0xc8, // latch: cmp r8d,r9d
        0x75, 0xd0, // jne loop
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("switch ("), "{text}");
    assert!(text.contains("continue;"), "{text}");
    assert!(text.contains("} while ("), "{text}");
}

/// A loop whose address range holds a block that is not the loop's is still
/// a loop.
///
/// Here a return the function's head jumps to lies between the loop's
/// blocks; it is left to the head, not folded into the body and not a
/// reason to give the loop up.
#[test]
fn a_loop_skips_the_block_in_its_range_that_is_not_its_own() {
    let code: &[u8] = &[
        0x31, 0xc0, // xor eax,eax
        0x85, 0xc9, // test ecx,ecx
        0x7e, 0x0c, // jle done
        0x03, 0x02, // loop: add eax,[rdx]
        0x48, 0x83, 0xc2, 0x04, // add rdx,4
        0x85, 0xc0, // test eax,eax
        0x78, 0x02, // js done
        0xeb, 0x01, // jmp next
        0xc3, // done: ret
        0xff, 0xc9, // next: dec ecx
        0x75, 0xef, // jne loop
        0xc3, // ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("while"), "{text}");
}

/// Builds a 64-bit program of `code` with an `.rdata` page of `data` and
/// an import symbol at each given address table slot.
///
/// # Arguments
///
/// * `code` - The bytes of `.text` at 0x140001000.
/// * `data` - The bytes of `.rdata` at 0x140002000.
/// * `imports` - `(slot, "DLL!name")` per import.
fn program64_with_imports(
    code: &[u8],
    data: &[u8],
    imports: &[(u64, &str)],
) -> borer_engine::program::Program {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut p = program64_with_data(code, data);
    p.symbols = imports
        .iter()
        .map(|(addr, name)| Symbol {
            name: (*name).to_owned(),
            addr: *addr,
            kind: SymbolKind::Import,
        })
        .collect();
    p
}

/// An import call passes what the SDK declares: `SetLastError` takes one
/// argument though `edx` was set too, and `sin` takes its `double` in
/// `xmm0`.
///
/// `sub rsp,0x28; mov ecx,5; mov edx,7; call [SetLastError]; movsd
/// xmm0,[two]; call [sin]; add rsp,0x28; ret`.
#[test]
fn an_import_call_takes_its_declared_arity() {
    let code = [
        0x48, 0x83, 0xec, 0x28, 0xb9, 0x05, 0x00, 0x00, 0x00, 0xba, 0x07, 0x00, 0x00, 0x00, 0xff,
        0x15, 0xec, 0x0f, 0x00, 0x00, 0xf2, 0x0f, 0x10, 0x05, 0xf4, 0x0f, 0x00, 0x00, 0xff, 0x15,
        0xe6, 0x0f, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    let mut data = vec![0u8; 0x10];
    data.extend_from_slice(&2.0f64.to_bits().to_le_bytes());
    let p = program64_with_imports(
        &code,
        &data,
        &[
            (0x1_4000_2000, "KERNEL32.dll!SetLastError"),
            (0x1_4000_2008, "api-ms-win-crt-math-l1-1-0.dll!sin"),
        ],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("SetLastError(5);"), "{text}");
    assert!(text.contains("sin(") && !text.contains("sin()"), "{text}");
}

/// A register a call clobbered is no argument of a later call.
///
/// `mov rax,rdx; sub rsp,0x28; call leaf; mov ecx,87; call
/// [RtlSetLastWin32Error]; mov ecx,5; call [SetLastError]; add rsp,0x28;
/// ret`, the leaf `mov edx,5; ret`: `rdx` held the caller's own `a2` until
/// the leaf clobbered it, so the undocumented import gets the one register
/// written for it and `SetLastError` its one declared argument, where both
/// once rendered `(87, rdx)` and `(5, rdx)`.
#[test]
fn a_clobbered_register_is_no_argument() {
    let mut code = vec![
        0x48, 0x89, 0xd0, 0x48, 0x83, 0xec, 0x28, 0xe8, 0x34, 0x00, 0x00, 0x00, 0xb9, 0x57, 0x00,
        0x00, 0x00, 0xff, 0x15, 0xe9, 0x0f, 0x00, 0x00, 0xb9, 0x05, 0x00, 0x00, 0x00, 0xff, 0x15,
        0xe6, 0x0f, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xba, 0x05, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64_with_imports(
        &code,
        &[0; 16],
        &[
            (0x1_4000_2000, "ntdll.dll!RtlSetLastWin32Error"),
            (0x1_4000_2008, "KERNEL32.dll!SetLastError"),
        ],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("RtlSetLastWin32Error(87);"), "{text}");
    assert!(text.contains("SetLastError(5);"), "{text}");
    assert!(!text.contains("rdx"), "{text}");
}

/// A forwarder passes its own parameters through.
///
/// `jmp [MultiByteToWideChar]` takes the import's six arguments, four in
/// registers and two on the stack above the return address the jump
/// leaves, and its signature lists the same six.
#[test]
fn a_forwarder_passes_its_parameters_through() {
    let code = [0xff, 0x25, 0xfa, 0x0f, 0x00, 0x00];
    let p = program64_with_imports(
        &code,
        &[0; 8],
        &[(0x1_4000_2000, "KERNEL32.dll!MultiByteToWideChar")],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("return MultiByteToWideChar(a1, a2, a3, a4, a5, a6);"),
        "{text}"
    );
    assert!(text.contains("uint64_t a6)"), "{text}");
}

/// A function's signature and every call to it print one arity.
///
/// The callee reads `r8` only on the path that skips its call: `test
/// ecx,ecx; je L; call leaf; ret; L: mov eax,r8d; ret`. Read in address
/// order up to the first call it seemed to take one argument, while its
/// own signature lists three; the caller, which sets four registers,
/// passes the three the signature lists.
#[test]
fn a_call_passes_what_the_callee_signature_lists() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x02, 0x00, 0x00, 0x00, 0x41,
        0xb8, 0x03, 0x00, 0x00, 0x00, 0x41, 0xb9, 0x04, 0x00, 0x00, 0x00, 0xe8, 0x21, 0x00, 0x00,
        0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, 0x74, 0x06, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xc3, 0x44, 0x89, 0xc0, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let caller = decompiled(&p, 0x1_4000_1000);
    assert!(caller.contains("sub_140001040(1, 2, 3);"), "{caller}");
    let callee = decompiled(&p, 0x1_4000_1040);
    assert!(
        callee.contains("sub_140001040(uint64_t a1, uint64_t a2, uint64_t a3)"),
        "{callee}"
    );
}

/// A register the body reads past an attributed signature stays a
/// parameter.
///
/// `void __cdecl Cls::Two(int,int)`, attributed from the text the body
/// references, lists two parameters, while the body reads `rdx`, `r8`,
/// `r9` and a stack argument: the attribution understates the arity, so
/// the signature lists all five positions, `this` first, and its caller
/// passes five, where the signature once stopped at three and the body
/// read `r9` and the stack argument as registers nothing defined.
#[test]
fn a_register_read_past_an_attributed_signature_stays_a_parameter() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x38, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x02, 0x00, 0x00, 0x00, 0x41,
        0xb8, 0x03, 0x00, 0x00, 0x00, 0x41, 0xb9, 0x04, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24,
        0x20, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x18, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x38, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x4c, 0x8d, 0x15, 0xb9, 0x0f, 0x00, 0x00, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x4c, 0x01, 0xc8,
        0x4c, 0x01, 0xc0, 0x48, 0x01, 0xd0, 0xc3,
    ]);
    let p = program64_with_data(&code, b"void __cdecl Cls::Two(int,int)\0");
    let callee = decompiled(&p, 0x1_4000_1040);
    assert!(
        callee.contains("Cls::Two(Cls *this, int a2, int a3, uint64_t a4, uint64_t a5)"),
        "{callee}"
    );
    let caller = decompiled(&p, 0x1_4000_1000);
    assert!(caller.contains("Cls::Two(1, 2, 3, 4, 5);"), "{caller}");
}

/// An export named after an API takes the API's arity.
///
/// Kernel32's `SetLastError` is one `jmp [RtlSetLastWin32Error]` to an
/// import no header declares, and it takes the one argument
/// `SetLastError` takes, which it passes on.
#[test]
fn an_export_named_after_an_api_takes_its_arity() {
    let code = [0xff, 0x25, 0xfa, 0x0f, 0x00, 0x00];
    let p = program64_with_imports(
        &code,
        &[0; 8],
        &[(0x1_4000_2000, "ntdll.dll!RtlSetLastWin32Error")],
    );
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1_4000_1000, "SetLastError".to_owned());
    let text = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("SetLastError(uint64_t a1)"), "{text}");
    assert!(text.contains("return RtlSetLastWin32Error(a1);"), "{text}");
}

/// A call into a dispatch thunk is the call through its register.
///
/// A thunk that only jumps through `rax` (the CFG dispatcher) is called
/// as the call through `rax`, with the arguments set for it, and a call
/// through a read-only pointer to a function that only returns (the CFG
/// check's default) is no statement.
///
/// `sub rsp,0x28; lea rax,[target]; mov ecx,9; call [check]; call
/// dispatch; add rsp,0x28; ret` with `dispatch` `jmp rax`, `target` `mov
/// eax,ecx; ret`, and `check` holding the address of a bare `ret`.
#[test]
fn a_dispatch_thunk_call_is_the_call_through_its_register() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0x48, 0x8d, 0x05, 0x55, 0x00, 0x00, 0x00, 0xb9, 0x09, 0x00, 0x00,
        0x00, 0xff, 0x15, 0xea, 0x0f, 0x00, 0x00, 0xe8, 0x25, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4,
        0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xff, 0xe0]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x89, 0xc8, 0xc3]);
    code.resize(0x70, 0xcc);
    code.push(0xc3);
    let p = program64_with_data(&code, &0x1_4000_1070u64.to_le_bytes());
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("(9);"), "{text}");
    assert!(!text.contains("sub_140001040()"), "{text}");
    assert!(text.contains("only jumps through rax"), "{text}");
    assert!(text.contains("are left out"), "{text}");
}

/// A register a leaf callee never writes keeps its value across the call.
///
/// `mov r8,rcx; xor edx,edx; call leaf; mov [r8+0xc0],dl; ret` with the
/// leaf `mov eax,1; ret` stores a zero into `a1`, where it once stored the
/// never-assigned `rdx` through the never-assigned `r8`.
#[test]
fn a_register_the_callee_leaves_alone_survives_the_call() {
    let mut code = vec![
        0x49, 0x89, 0xc8, 0x31, 0xd2, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x41, 0x88, 0x90, 0xc0, 0x00,
        0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("= 0;"), "{text}");
    assert!(!text.contains("r8"), "{text}");
    assert!(!text.contains("rdx"), "{text}");
}

/// An argument renders after the write-outs its call forces.
///
/// Once `rdi += rax;` is in the text, the argument that was `rdi + rax`
/// reads `rdi`, not `rdi + rax` a second time.
///
/// `push rdi; sub rsp,0x20; mov rdi,rcx; call f; add rdi,rax; mov rcx,rdi;
/// call g; add rdi,rax; mov rcx,rdi; call g; mov rax,rdi; add rsp,0x20;
/// pop rdi; ret`, `f` `mov eax,5; ret`, `g` `mov rax,rcx; ret`.
#[test]
fn an_argument_reads_the_text_its_call_leaves() {
    let mut code = vec![
        0x57, 0x48, 0x83, 0xec, 0x20, 0x48, 0x89, 0xcf, 0xe8, 0x33, 0x00, 0x00, 0x00, 0x48, 0x01,
        0xc7, 0x48, 0x89, 0xf9, 0xe8, 0x38, 0x00, 0x00, 0x00, 0x48, 0x01, 0xc7, 0x48, 0x89, 0xf9,
        0xe8, 0x2d, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf8, 0x48, 0x83, 0xc4, 0x20, 0x5f, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x48, 0x89, 0xc8, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("rdi += rax;"), "{text}");
    assert!(!text.contains("sub_140001050(rdi + rax)"), "{text}");
}

/// A home slot whose address escaped is written out before the call that
/// reads it renders.
///
/// `mov [rsp+8],rbx; push rdi; sub rsp,0x20; mov rdi,rcx; mov ebx,edx; lea
/// rdx,[rsp+0x38]; call f; mov edx,[rsp+0x38]; mov rcx,rdi; add edx,ebx;
/// mov [rsp+0x38],edx; call g; ...` with `f` storing through `rdx`: the
/// second call passes the slot's new value, where it once passed `home_8 +
/// a2` after `home_8 += a2;` and so added `a2` twice.
#[test]
fn an_escaped_home_slot_is_written_out_before_the_call_reads_it() {
    let mut code = vec![
        0x48, 0x89, 0x5c, 0x24, 0x08, 0x57, 0x48, 0x83, 0xec, 0x20, 0x48, 0x8b, 0xf9, 0x8b, 0xda,
        0x48, 0x8d, 0x54, 0x24, 0x38, 0xe8, 0x27, 0x00, 0x00, 0x00, 0x8b, 0x54, 0x24, 0x38, 0x48,
        0x8b, 0xcf, 0x03, 0xd3, 0x89, 0x54, 0x24, 0x38, 0xe8, 0x35, 0x00, 0x00, 0x00, 0x48, 0x8b,
        0x5c, 0x24, 0x30, 0x48, 0x83, 0xc4, 0x20, 0x5f, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc7, 0x02, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x89, 0xd0, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("home_8 += a2;"), "{text}");
    assert!(text.contains("sub_140001060(a1, home_8);"), "{text}");
}

/// A float argument a call takes keeps its value up to the call.
///
/// `sub rsp,0x28; movss xmm1,[rcx+0x10]; movss [rcx+0x20],xmm1; mov dword
/// [rcx+0x30],0; call f; add rsp,0x28; ret` with `f` taking `xmm1`: the
/// value loaded is written out before the store and passed, where the
/// store once dropped it as unread and the call passed `xmm1`, a variable
/// the text never assigned.
#[test]
fn a_float_argument_keeps_its_value_up_to_the_call() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xf3, 0x0f, 0x10, 0x49, 0x10, 0xf3, 0x0f, 0x11, 0x49, 0x20, 0xc7,
        0x41, 0x30, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x26, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28,
        0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x0f, 0x28, 0xc1, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("xmm1 = a1->field_0x10;"), "{text}");
    assert!(text.contains("sub_140001040(a1, xmm1);"), "{text}");
}

/// A stack parameter loaded through the stack pointer and dereferenced is
/// a pointer.
///
/// `mov rax,[rsp+0x28]; mov eax,[rax+8]; ret` reads a word through its
/// fifth parameter, the first on the stack: the signature calls it a
/// pointer, a `void *` since the word lies past its start.
#[test]
fn a_stack_parameter_loaded_through_the_stack_pointer_is_typed() {
    let code = [0x48, 0x8b, 0x44, 0x24, 0x28, 0x8b, 0x40, 0x08, 0xc3];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("void *a5)"), "{text}");
}

/// A parameter a `lea` only adds to is no pointer.
///
/// `lea eax,[rcx-0x30]; ret` is `c - '0'`: the sum names no memory, so the
/// parameter stays a number, where the signature once called it a `void *`.
#[test]
fn a_parameter_a_lea_only_adds_to_is_no_pointer() {
    let p = program64(&[0x8d, 0x41, 0xd0, 0xc3]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("(uint64_t a1)"), "{text}");
}

/// Parameters parked home are no variable argument list.
///
/// A function that parks its parameters home without taking an address
/// past them is not variadic: `mov [rsp+0x10],rdx; mov [rsp+0x18],r8; mov
/// [rsp+0x20],r9; mov rax,[rsp+0x18]; add rax,rcx; ret` takes four.
#[test]
fn parameters_parked_home_are_no_variable_list() {
    let code = [
        0x48, 0x89, 0x54, 0x24, 0x10, 0x4c, 0x89, 0x44, 0x24, 0x18, 0x4c, 0x89, 0x4c, 0x24, 0x20,
        0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x01, 0xc8, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("uint64_t a4)"), "{text}");
    assert!(!text.contains("..."), "{text}");
}

/// A stack argument read through a copy of the stack pointer counts.
///
/// `mov r11,rsp; sub rsp,0x28; mov eax,[r11+0x28]; add rsp,0x28; ret`
/// reads the first stack argument, as `push ebx; mov ebx,esp; and
/// esp,-16` code reads its arguments through `ebx`.
#[test]
fn a_stack_argument_read_through_a_copy_of_the_stack_pointer_counts() {
    let code = [
        0x4c, 0x8b, 0xdc, 0x48, 0x83, 0xec, 0x28, 0x41, 0x8b, 0x43, 0x28, 0x48, 0x83, 0xc4, 0x28,
        0xc3,
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x1_4000_1000).map(|f| f.stack_args), Some(1));
}

/// A virtual call whose slot holds the pure-call stub prints the slot.
///
/// No object of the class runs the stub, so naming it misleads.
#[test]
fn a_pure_virtual_slot_prints_as_the_slot() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1200, "_purecall".to_owned());
    let text = decompile(&p, &a, &o, 0x1770).unwrap_or_default();
    assert!(text.contains("this->vtable[1]("), "{text}");
    assert!(!text.contains("_purecall"), "{text}");
}

/// A function whose every exit writes a 32-bit register returns that wide.
///
/// On a 64-bit target `mov eax, 0xc000000d` leaves `0x00000000c000000d`
/// in `rax`, where a `uint64_t` header turns the text's `return
/// STATUS_INVALID_PARAMETER;` (or `return ~rcx;` of a value kept whole)
/// into `0xffffffffc000000d`. `test ecx,ecx; je L; mov eax,0xc000000d;
/// ret; L: not ecx; mov eax,ecx; ret` returns a `uint32_t`; an exit that
/// writes all of `rax` (`mov rax,[rcx]`) or hands over to another function
/// whose width is unknown (`jmp sub`) keeps the whole register, and a byte
/// returned beside a handover to a function returning a byte stays a byte.
#[test]
fn a_result_every_exit_writes_as_32_bits_is_32_bits_wide() {
    let narrow = [
        0x85, 0xc9, 0x74, 0x06, 0xb8, 0x0d, 0x00, 0x00, 0xc0, 0xc3, 0xf7, 0xd1, 0x89, 0xc8, 0xc3,
    ];
    let text = decompiled(&program64(&narrow), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint32_t sub_140001000("),
        "{text}"
    );
    let mixed = [
        0x48, 0x85, 0xc9, 0x74, 0x04, 0x48, 0x8b, 0x01, 0xc3, 0x31, 0xc0, 0xc3,
    ];
    let text = decompiled(&program64(&mixed), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint64_t sub_140001000("),
        "{text}"
    );
    let mut tail = vec![
        0x85, 0xc9, 0x75, 0x0b, 0xe8, 0x37, 0x00, 0x00, 0x00, 0xb8, 0x57, 0x00, 0x00, 0x00, 0xc3,
        0xe9, 0x2c, 0x00, 0x00, 0x00,
    ];
    tail.resize(0x40, 0xcc);
    tail.extend_from_slice(&[0x48, 0x8b, 0x01, 0xc3]);
    let text = decompiled(&program64(&tail), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint64_t sub_140001000("),
        "{text}"
    );
    let mut byte = vec![
        0x85, 0xc9, 0x75, 0x08, 0xe8, 0x37, 0x00, 0x00, 0x00, 0x30, 0xc0, 0xc3, 0xe9, 0x2f, 0x00,
        0x00, 0x00,
    ];
    byte.resize(0x40, 0xcc);
    byte.extend_from_slice(&[0xb0, 0x01, 0xc3]);
    let text = decompiled(&program64(&byte), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint8_t sub_140001000("),
        "{text}"
    );
}

/// A byte result stays a byte beside a tail jump to a function whose width
/// nothing states.
///
/// `test ecx,ecx; jne L; call g; xor al,al; ret; L: jmp g`, with `g` at
/// 0x1040 loading `rax` whole: the exit the function writes itself hands
/// back `al`, and the jump hands on whatever `g` leaves, which no lane
/// bounds. Only a 32-bit lane needs the jump's width to hold; a byte one
/// is the function's own, as it was before the 32-bit lane existed, and
/// without it the exit printed `return rax & ~0xff;`.
#[test]
fn a_byte_result_beside_a_tail_jump_of_unknown_width_stays_a_byte() {
    let mut code = vec![
        0x85, 0xc9, 0x75, 0x08, 0xe8, 0x37, 0x00, 0x00, 0x00, 0x30, 0xc0, 0xc3, 0xe9, 0x2f, 0x00,
        0x00, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x48, 0x8b, 0x01, 0xc3]);
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint8_t sub_140001000("),
        "{text}"
    );
    assert!(!text.contains("& ~0xff"), "{text}");
}

/// A call passes every argument up to the last the callee reads.
///
/// `sub rsp,0x28; lea rdx,[rsp+0x20]; call f; mov eax,[rsp+0x20]; add
/// rsp,0x28; ret`, with `f` writing through `rdx` alone: the callee's
/// first slot is one it never reads, and the register the caller left in
/// it is what the call passes there, so the list goes on to the address
/// the callee writes through, where it once stopped at the empty slot and
/// left the local unset. A tail jump hands on the caller's own parameters
/// in the registers it never wrote: `mov rcx,[rcx]; jmp g` at 0x1020,
/// with `g` reading `r9` past a call and a stack argument, passes all
/// five.
#[test]
fn a_call_passes_its_arguments_past_a_slot_the_callee_skips() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x20, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x8b,
        0x44, 0x24, 0x20, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc7, 0x02, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(
        text.lines()
            .any(|l| l.contains("sub_140001040(rcx, &local_")),
        "{text}"
    );
    assert!(
        text.lines()
            .any(|l| l.starts_with("uint64_t ") && l.contains("rcx")),
        "{text}"
    );
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x48, 0x8b, 0x09, 0xe9, 0x18, 0x00, 0x00, 0x00]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, 0x74, 0x06, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xc3, 0x4c, 0x89, 0xc8, 0x48, 0x03,
        0x44, 0x24, 0x28, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.push(0xc3);
    let text = decompiled(&program64(&code), 0x1_4000_1020);
    assert!(
        text.contains("sub_140001040(*(uint64_t*)a1, a2, a3, a4, a5);"),
        "{text}"
    );
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

/// Runs a function's final text as C beside the binary in the emulator on
/// 64 inputs its signature types, and requires every run the binary
/// returns from to agree.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function.
///
/// # Returns
///
/// The final text, for the caller's own assertions.
fn runs_agree(p: &borer_engine::program::Program, entry: u64) -> String {
    use borer_engine::analysis::decompile::decompile_named;
    use borer_engine::analysis::render::{Verdict, check_generated};
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let text = decompile_named(p, &a, &o, entry).unwrap_or_default();
    let runs = check_generated(p, &a, &o, entry, 64, 1, 20_000).unwrap_or_default();
    let differ: Vec<String> = runs
        .iter()
        .filter_map(|(args, v)| match v {
            Verdict::Differs(line, what) => Some(format!("{args}: L{line} {what}")),
            Verdict::Agrees | Verdict::Unchecked(..) => None,
        })
        .collect();
    assert!(differ.is_empty(), "{}\n{text}", differ.join("\n"));
    assert!(
        runs.iter().any(|(_, v)| *v == Verdict::Agrees),
        "{runs:?}\n{text}"
    );
    text
}

/// A callee whose result is only the low byte of `rax` merges into what
/// the caller had there, and a caller that returns it returns the merge.
///
/// `mov rax,rcx; mov dl,[rcx]; and dl,1; call BYTESET; ret`, where
/// `BYTESET` is `mov al,dl; mov [rcx],dl; ret`, leaves the machine's `rax`
/// as the caller's pointer with the callee's byte in its low lane; the
/// text once claimed the byte alone, and a run answered without the
/// pointer's bits.
#[test]
fn a_narrow_callee_result_merges_into_the_callers_rax() {
    let mut code = vec![
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x8a, 0x11, // ASM: mov dl,[rcx]
        0x80, 0xe2, 0x01, // ASM: and dl,1
        0xe8, 0x13, 0x00, 0x00, 0x00, // ASM: call 0x140001020
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x88, 0xd0, // ASM: mov al,dl
        0x88, 0x11, // ASM: mov [rcx],dl
        0xc3, // ASM: ret
    ]);
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(a1 & ~0xff) | ("), "the merge: {text}");
}

/// A word shifted into the high half of a 64-bit result keeps its bits.
///
/// `mov eax,[rcx]; movzx edx,word [rcx+4]; shl rdx,0x20; or rax,rdx; ret`
/// shifts in 64 bits, where the text's `*(uint16_t*)(a1 + 4) << 0x20`
/// shifted an `int` by 32 and lost the word: the shift is cast to
/// `uint64_t` first.
#[test]
fn a_narrow_load_shifted_into_the_high_half_keeps_its_bits() {
    let code = [
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0x0f, 0xb7, 0x51, 0x04, // ASM: movzx edx, word [rcx+4]
        0x48, 0xc1, 0xe2, 0x20, // ASM: shl rdx, 0x20
        0x48, 0x09, 0xd0, // ASM: or rax, rdx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(
        text.contains("(uint64_t)*(uint16_t*)(a1 + 4) << 0x20"),
        "{text}"
    );
}

/// A 32-bit field multiplied in 64 bits keeps the product's high half.
///
/// `mov eax,[rcx+8]; imul rax,rax,0x431bde83; shr rax,0x32; ret` divides
/// the field by a magic multiply whose product needs 63 bits, where the
/// text's `*(uint32_t*)(a1 + 8) * 0x431bde83` wrapped in `unsigned int`.
#[test]
fn a_32_bit_load_multiplied_in_64_bits_keeps_the_high_half() {
    let code = [
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0x48, 0x69, 0xc0, 0x83, 0xde, 0x1b, 0x43, // ASM: imul rax, rax, 0x431bde83
        0x48, 0xc1, 0xe8, 0x32, // ASM: shr rax, 0x32
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(uint64_t)"), "{text}");
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

/// A load wider than the slot it starts at reads the slots above it too.
///
/// `mov byte [rsp+4],1; mov [rsp+5],r9b; mov [rsp+6],r8w; mov edx,[rsp+4];
/// mov [rcx+8],edx` packs three slots into one dword, as a Rust enum's
/// constructor does: the text's `local_c`, a `uint8_t`, read one byte of
/// the four, and the three above it were lost.
#[test]
fn a_load_wider_than_its_slot_reads_the_slots_above() {
    let code = [
        0x48, 0x83, 0xec, 0x10, // ASM: sub rsp, 0x10
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x88, 0x54, 0x24, 0x0b, // ASM: mov [rsp+0xb], dl
        0x66, 0x44, 0x89, 0x44, 0x24, 0x0c, // ASM: mov [rsp+0xc], r8w
        0x44, 0x88, 0x4c, 0x24, 0x0f, // ASM: mov [rsp+0xf], r9b
        0xc6, 0x44, 0x24, 0x04, 0x01, // ASM: mov byte [rsp+4], 1
        0x44, 0x88, 0x4c, 0x24, 0x05, // ASM: mov [rsp+5], r9b
        0x66, 0x44, 0x89, 0x44, 0x24, 0x06, // ASM: mov [rsp+6], r8w
        0x88, 0x54, 0x24, 0x08, // ASM: mov [rsp+8], dl
        0x88, 0x54, 0x24, 0x09, // ASM: mov [rsp+9], dl
        0x48, 0x8d, 0x15, 0x1b, 0x00, 0x00, 0x00, // ASM: lea rdx, [rel 0x140001040]
        0x48, 0x89, 0x11, // ASM: mov [rcx], rdx
        0x8b, 0x54, 0x24, 0x04, // ASM: mov edx, [rsp+4]
        0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
        0x66, 0x8b, 0x54, 0x24, 0x08, // ASM: mov dx, [rsp+8]
        0x66, 0x89, 0x51, 0x0c, // ASM: mov [rcx+0xc], dx
        0x48, 0x83, 0xc4, 0x10, // ASM: add rsp, 0x10
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("*(uint32_t*)&local_c"), "{text}");
    assert!(text.contains("*(uint16_t*)&local_8"), "{text}");
}

/// A wrapper that reads one argument and calls on passes its callee the
/// others too.
///
/// `f: call g; ret`, `g: mov r8,rcx; call h; ret`, `h: mov rax,rdx; ret`:
/// `g` reads `rcx` and hands `h` the `rdx` it never wrote, so `f`, which
/// hands `g` both, takes two. The scan of `g` once stopped at its own read
/// of `rcx`, `f` took one, and its text called `g` without the `rdx` that
/// `h` returns.
#[test]
fn a_wrapper_passes_on_what_its_callee_reads_beyond_its_own() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x49, 0x89, 0xc8, // ASM: mov r8, rcx
        0xe8, 0x34, 0x00, 0x00, 0x00, // ASM: call 0x140001080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ]);
    code.resize(0x80, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x89, 0xd0, // ASM: mov rax, rdx
        0xc3, // ASM: ret
    ]);
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("sub_140001040(a1, a2)"), "{text}");
}

/// A jump that writes out a store the branch skipped over keeps it.
///
/// The entry stores `[rbp-48h]` (`local_60`) and compares; one side calls,
/// which writes the store out before it, and the other only jumps to the
/// join that reads it. That jump was taken for a detour and dropped with
/// the store it wrote out, so on that side the join read a `local_60`
/// nothing set (a Rust `Vec::push`).
#[test]
fn a_jump_that_writes_out_a_store_is_kept() {
    let mut code = vec![
        0x55, // ASM: push rbp
        0x48, 0x81, 0xec, 0x90, 0x00, 0x00, 0x00, // ASM: sub rsp, 0x90
        0x48, 0x8d, 0xac, 0x24, 0x80, 0x00, 0x00, 0x00, // ASM: lea rbp, [rsp+0x80]
        0x48, 0xc7, 0x45, 0x08, 0xfe, 0xff, 0xff, 0xff, // ASM: mov qword [rbp+8], -2
        0x89, 0x55, 0xac, // ASM: mov [rbp-0x54], edx
        0x48, 0x89, 0x4d, 0xb0, // ASM: mov [rbp-0x50], rcx
        0x48, 0x89, 0x4d, 0xc8, // ASM: mov [rbp-0x38], rcx
        0x89, 0x55, 0xd4, // ASM: mov [rbp-0x2c], edx
        0x48, 0xc7, 0x45, 0xd8, 0x04, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-0x28], 4
        0x48, 0x8b, 0x41, 0x10, // ASM: mov rax, [rcx+0x10]
        0x48, 0x89, 0x45, 0xb8, // ASM: mov [rbp-0x48], rax
        0x48, 0x89, 0x45, 0xe0, // ASM: mov [rbp-0x20], rax
        0x48, 0x8b, 0x09, // ASM: mov rcx, [rcx]
        0x48, 0x89, 0x4d, 0xe8, // ASM: mov [rbp-0x18], rcx
        0x48, 0x89, 0x4d, 0xc0, // ASM: mov [rbp-0x40], rcx
        0x48, 0x3b, 0x45, 0xc0, // ASM: cmp rax, [rbp-0x40]
        0x74, 0x02, // ASM: je 0x14000104d
        0xeb, 0x0c, // ASM: jmp 0x140001059
        0x48, 0x8b, 0x4d, 0xb0, // ASM: mov rcx, [rbp-0x50]
        0xe8, 0xaa, 0x00, 0x00, 0x00, // ASM: call 0x140001100
        0x90, // ASM: nop
        0xeb, 0x00, // ASM: jmp 0x140001059
        0x48, 0x8b, 0x4d, 0xb0, // ASM: mov rcx, [rbp-0x50]
        0x48, 0x8b, 0x55, 0xb8, // ASM: mov rdx, [rbp-0x48]
        0x44, 0x8b, 0x4d, 0xac, // ASM: mov r9d, [rbp-0x54]
        0x4c, 0x8b, 0x41, 0x08, // ASM: mov r8, [rcx+8]
        0x4c, 0x89, 0x45, 0xf0, // ASM: mov [rbp-0x10], r8
        0x49, 0x89, 0xd2, // ASM: mov r10, rdx
        0x49, 0xc1, 0xe2, 0x02, // ASM: shl r10, 2
        0x4c, 0x89, 0xc0, // ASM: mov rax, r8
        0x4c, 0x01, 0xd0, // ASM: add rax, r10
        0x48, 0x89, 0x45, 0xf8, // ASM: mov [rbp-8], rax
        0x44, 0x89, 0x4d, 0x04, // ASM: mov [rbp+4], r9d
        0x48, 0x83, 0xc2, 0x01, // ASM: add rdx, 1
        0x48, 0x89, 0x51, 0x10, // ASM: mov [rcx+0x10], rdx
        0x48, 0x81, 0xc4, 0x90, 0x00, 0x00, 0x00, // ASM: add rsp, 0x90
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0x48, 0x83, 0xc0, 0x04, // ASM: add rax, 4
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0x48, 0x89, 0x49, 0x08, // ASM: mov [rcx+8], rcx
        0xc3, // ASM: ret
    ]);
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("} else {"), "{text}");
}

/// A parameter typed narrow from its masks keeps the bits a shift moves
/// past them.
///
/// `mov eax,edx; shl rax,0xa; and ecx,0x3ff; or rax,rcx; ret` packs `a2`
/// above ten bits of `a1` in 64 bits. Every use of `a2` was masked to 32
/// bits, so the header declares it `uint32_t` and the masks go; the shift
/// then ran in `unsigned int` and lost the bits past 32: it is cast to
/// `uint64_t` in their place.
#[test]
fn a_parameter_typed_narrow_keeps_what_a_shift_moves_past_it() {
    let code = [
        0x89, 0xd0, // ASM: mov eax, edx
        0x48, 0xc1, 0xe0, 0x0a, // ASM: shl rax, 0xa
        0x81, 0xe1, 0xff, 0x03, 0x00, 0x00, // ASM: and ecx, 0x3ff
        0x48, 0x09, 0xc8, // ASM: or rax, rcx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(uint64_t)a2 << 0xa"), "{text}");
}

/// A parameter typed narrow from its masks compares a difference of it as
/// the machine does, unsigned.
///
/// `movzx eax,cl; sub rax,7; cmp rax,3; jb L; xor eax,eax; ret; L: mov
/// eax,1; ret` tests `a1` in 7..10 with one unsigned compare. Typed
/// `uint8_t`, `a1 - 7` was an `int`, negative below 7, and the compare
/// held for every such `a1`.
#[test]
fn a_parameter_typed_narrow_compares_its_difference_unsigned() {
    let code = [
        0x0f, 0xb6, 0xc1, // ASM: movzx eax, cl
        0x48, 0x83, 0xe8, 0x07, // ASM: sub rax, 7
        0x48, 0x83, 0xf8, 0x03, // ASM: cmp rax, 3
        0x72, 0x03, // ASM: jb 0x140001010
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(uint64_t)a1 - 7 < 3"), "{text}");
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

/// A `movd` lane widened back to 64 bits keeps only the source's low 32.
///
/// `movd xmm0,ecx; movq rax,xmm0; add rax,rcx` writes the lane's low 32
/// bits and zeroes the rest, so the value read back is the zero extension
/// of `ecx`, not `rcx` whole: the text masks the source to the bits the
/// machine kept (the whole-read roughness narrowed in the lift), and
/// the runs agree wherever the upper half of `a1` is set.
#[test]
fn a_movd_lane_widened_keeps_the_sources_low_32_bits() {
    let code = [
        0x66, 0x0f, 0x6e, 0xc1, // ASM: movd xmm0,ecx
        0x66, 0x48, 0x0f, 0x7e, 0xc0, // ASM: movq rax,xmm0
        0x48, 0x01, 0xc8, // ASM: add rax,rcx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("return (a1 & 0xffffffff) + a1;"), "{text}");
}

/// A `_longjmp` import ends the text like any noreturn call, taking its
/// two declared arguments.
///
/// `mov ecx,buf; mov edx,1; call [_longjmp]; mov eax,7; ret` never runs
/// past the call, so the MSVC spelling of `longjmp` is among the names the
/// analysis knows never return and the walk ends the block at it: the dead
/// tail is not rendered, and the call renders the two arguments its
/// prototype declares, not four padded register slots.
#[test]
fn a_longjmp_import_ends_the_text_like_a_noreturn_call() {
    let code = [
        0xb9, 0x10, 0x20, 0x00, 0x14, // ASM: mov ecx,0x14002010
        0xba, 0x01, 0x00, 0x00, 0x00, // ASM: mov edx,1
        0xff, 0x15, 0xf0, 0x0f, 0x00, 0x00, // ASM: call [0x14002000]
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
    ];
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[(0x1_4000_2000, "api-ms-win-crt-runtime-l1-1-0.dll!_longjmp")],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.lines()
            .any(|l| l.contains("_longjmp(") && l.contains(", 1);")),
        "{text}"
    );
    assert!(!text.contains("return"), "dead tail survived:\n{text}");
}

/// A `_setjmp` call returns a result: the comparison against zero is a
/// plain condition, and nothing treats the call as noreturn.
///
/// `lea rcx,[buf]; call [_setjmp]; test eax,eax; jne L` binds the result
/// and branches on it, the shape both returns of a `setjmp` land in: the
/// first return reads zero and falls through, the second reads what
/// `longjmp` was handed. The minimal model keeps that honest as an
/// ordinary conditional with both arms live, and the prototype's one
/// argument keeps the call from padding to the register slots.
#[test]
fn a_setjmp_call_still_returns_a_result() {
    let code = [
        0x48, 0x8d, 0x0d, 0x11, 0x10, 0x00, 0x00, // ASM: lea rcx,[0x14002018]
        0xff, 0x15, 0xfb, 0x0f, 0x00, 0x00, // ASM: call [0x14002008]
        0x85, 0xc0, // ASM: test eax,eax
        0x75, 0x06, // ASM: jne 0x140001017
        0xb8, 0x64, 0x00, 0x00, 0x00, // ASM: mov eax,100
        0xc3, // ASM: ret
        0xb8, 0xc8, 0x00, 0x00, 0x00, // ASM: mov eax,200
        0xc3, // ASM: ret
    ];
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[(0x1_4000_2008, "api-ms-win-crt-runtime-l1-1-0.dll!_setjmp")],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("rax = _setjmp("), "{text}");
    assert!(text.contains("rax != 0"), "{text}");
    assert!(text.contains("return 100;"), "{text}");
    assert!(text.contains("return 200;"), "{text}");
}

/// A fiber procedure handed to `CreateFiber` is seeded as a function by
/// the pointer that hands it over.
///
/// Nothing ever calls the fiber proc: `CreateFiber` receives its address
/// and the scheduler enters it, so the only evidence the binary carries
/// is the `lea` that loads it into the second argument slot. That pointer
/// into executable code is a witness on its own, so the proc is
/// discovered and decompiles even where it sits flush after its caller,
/// unaligned and behind no padding a gap seed could read. The seed is the
/// pointer, not the callee's name, so a threadpool callback handed to
/// `TrySubmitThreadpoolCallback` or `QueueUserWorkItem` rides the same
/// path, and the call renders the three arguments the prototype declares.
#[test]
fn a_fiber_proc_handed_to_createfiber_is_seeded() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x48, 0x8d, 0x15, 0x0e, 0x00, 0x00, 0x00, // ASM: lea rdx, [0x14000101b]
        0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
        0xff, 0x15, 0xea, 0x0f, 0x00, 0x00, // ASM: call [0x140002000]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    assert_eq!(code.len(), 0x1b);
    code.extend_from_slice(&[0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 42; ret
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[(0x1_4000_2000, "kernel32.dll!CreateFiber")],
    );
    let a = Analysis::compute(&p);
    assert!(
        a.functions.iter().any(|f| f.entry == 0x1_4000_101b),
        "the fiber proc was not seeded: {:x?}",
        a.functions.iter().map(|f| f.entry).collect::<Vec<_>>()
    );
    let fiber = decompiled(&p, 0x1_4000_101b);
    assert!(fiber.contains("return 42;"), "{fiber}");
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("CreateFiber(0, sub_14000101b, 0);"), "{text}");
}

/// A `SwitchToFiber` call is an ordinary call: one argument, no result,
/// and the text after the swap stays.
///
/// The swap suspends the current fiber and resumes another, and when
/// control comes back it comes back at the call itself, so the block's
/// tail may still run on resume and belongs in the text. Unlike
/// `longjmp` the callee is not noreturn, and the prototype's single
/// parameter keeps the call from padding to the register slots: `mov rcx,
/// rax; call [SwitchToFiber]; mov eax,7; ret` renders one argument and
/// keeps the `return`.
#[test]
fn a_switchtofiber_call_keeps_its_tail_under_one_argument() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x48, 0x8d, 0x15, 0x1c, 0x00, 0x00, 0x00, // ASM: lea rdx, [0x140001029]
        0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
        0xff, 0x15, 0xea, 0x0f, 0x00, 0x00, // ASM: call [0x140002000]
        0x48, 0x89, 0xc1, // ASM: mov rcx, rax
        0xff, 0x15, 0xe9, 0x0f, 0x00, 0x00, // ASM: call [0x140002008]
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax, 7
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    assert_eq!(code.len(), 0x29);
    code.extend_from_slice(&[0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 42; ret
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[
            (0x1_4000_2000, "kernel32.dll!CreateFiber"),
            (0x1_4000_2008, "kernel32.dll!SwitchToFiber"),
        ],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    let swap = text
        .lines()
        .find(|l| l.contains("SwitchToFiber("))
        .unwrap_or_default();
    let args = swap
        .split_once("SwitchToFiber(")
        .and_then(|(_, rest)| rest.split_once(')'))
        .map_or("", |(inside, _)| inside);
    assert!(!swap.is_empty(), "{text}");
    assert!(!args.contains(','), "padded arguments: {swap}");
    assert!(
        text.contains("return 7;"),
        "the tail after the swap was dropped:\n{text}"
    );
}
