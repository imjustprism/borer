//! Conditions read from the flags an instruction leaves.

use super::*;

/// `dec ecx; jl` jumps when SF != OF, which is the counter before the
/// decrement being below one: at `INT_MIN` the decrement overflows, the
/// result is positive, and the jump is still taken.
///
/// `mov ecx,[esp+4]; dec ecx; jl L; xor eax,eax; ret; L: mov eax,1; ret`.
/// The sign test `(int32_t)(a1 - 1) < 0` it used to print says not taken
/// there.
#[test]
fn dec_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0x49, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    assert!(text.contains("if (a1 < 1) {"), "{text}");
    assert!(text.contains("int32_t a1"), "{text}");
    assert!(!text.contains("- 1) < 0"), "{text}");
    for x in boundary_i32() {
        let (r, of) = x.overflowing_sub(1);
        let jl = (r < 0) != of;
        assert_eq!(x < 1, jl, "a1 = {x}");
    }
    assert_ne!(i32::MIN.wrapping_sub(1) < 0, i32::MIN < 1);
}

/// `inc eax; jg` jumps when ZF is clear and SF == OF: the counter before
/// the increment is above minus one, `INT_MAX` included, where the sign
/// of `a1 + 1` says not.
///
/// The `-1` is an `int` literal and takes no cast.
///
/// `mov eax,[esp+4]; inc eax; jg L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn inc_then_jg_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x40, 0x7f, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    assert!(text.contains("if (a1 > -1) {"), "{text}");
    assert!(!text.contains("+ 1) > 0"), "{text}");
    for x in boundary_i32() {
        let (r, of) = x.overflowing_add(1);
        let jg = r != 0 && (r < 0) == of;
        assert_eq!(x > -1, jg, "a1 = {x}");
    }
}

/// `add eax, [esp+8]; jl` jumps on the true sum being negative: where the
/// signed sum overflows it has the sign of either addend, otherwise the
/// sign of the machine sum.
///
/// `mov eax,[esp+4]; add eax,[esp+8]; jl L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn add_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("if ((saddo32(a1, a2) ? (int32_t)a1 : (int32_t)(a1 + a2)) < 0) {"),
        "{text}"
    );
    for x in boundary_i32() {
        for y in boundary_i32() {
            let (r, of) = x.overflowing_add(y);
            let jl = (r < 0) != of;
            let rendered = if of { x < 0 } else { x.wrapping_add(y) < 0 };
            assert_eq!(rendered, jl, "a1 = {x}, a2 = {y}");
        }
    }
}

/// `shl eax, 1; jl` reads the overflow too: SF != OF after a one-bit
/// left shift is the sign of the operand, not bit 30 of it.
///
/// `mov eax,[esp+4]; shl eax,1; jl L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn shl_by_one_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xd1, 0xe0, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00,
        0x00, 0xc3,
    ]);
    assert!(text.contains("if (a1 < 0) {"), "{text}");
    for x in boundary_i32() {
        let r = x.wrapping_shl(1);
        let of = (r < 0) != (x < 0);
        assert_eq!(x < 0, (r < 0) != of, "a1 = {x}");
    }
}

/// `cmp eax, [esp+8]; js` jumps on the sign of the difference at 32 bits,
/// not on an unsigned `a1 < a2`.
///
/// `mov eax,[esp+4]; cmp eax,[esp+8]; js L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn cmp_then_js_is_the_sign_of_the_difference() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x3b, 0x44, 0x24, 0x08, 0x78, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(text.contains("if ((int32_t)(a1 - a2) < 0) {"), "{text}");
}

/// `lock dec dword [ecx]; jl` reads the overflow of the subtraction the
/// atomic made: the old value is the new one plus one, and the jump is
/// taken when that was below one.
///
/// `mov ecx,[esp+4]; lock dec dword [ecx]; jl L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn a_locked_dec_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0xf0, 0xff, 0x09, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00,
        0x00, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("var1 = atomic_sub32(*(uint32_t*)a1, 1);"),
        "{text}"
    );
    assert!(text.contains("if ((int32_t)(var1 + 1) < 1) {"), "{text}");
}

/// `rol` writes only CF and OF, so a `je` after it reads the zero flag of
/// the compare before: `cmp ecx, 7; rol ecx, 5; je` tests `a1 == 7`, not
/// the rotated value.
///
/// `mov ecx,[esp+4]; cmp ecx,7; rol ecx,5; je L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn a_rotate_keeps_the_zero_flag_before_it() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0x83, 0xf9, 0x07, 0xc1, 0xc1, 0x05, 0x74, 0x03, 0x33, 0xc0, 0xc3,
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(text.contains("if (a1 == 7) {"), "{text}");
    assert!(!text.contains("rotl32(a1, 5) == 0"), "{text}");
}

/// A rotate keeps the zero flag of the compare before it, in the emulator
/// as in the lifter: `sete` after `cmp ecx, 7; rol ecx, 5` reads
/// `ecx == 7`. The emulator once set the flag from the rotated value.
#[test]
fn a_rotate_keeps_zf_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x83, 0xf9, 0x07, // ASM: cmp ecx, 7
        0xc1, 0xc1, 0x05, // ASM: rol ecx, 5
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
}

/// `tzcnt` sets CF when its source is zero and ZF when the count is: `jb`
/// after it tests the source, `je` the count.
///
/// `mov ecx,[esp+4]; tzcnt eax,ecx; jcc L; xor eax,eax; ret; L: mov
/// eax,1; ret` with `jb` and with `je`.
#[test]
fn tzcnt_sets_the_carry_on_a_zero_source() {
    let with = |jcc: u8| {
        dc(&[
            0x8b, 0x4c, 0x24, 0x04, 0xf3, 0x0f, 0xbc, 0xc1, jcc, 0x03, 0x33, 0xc0, 0xc3, 0xb8,
            0x01, 0x00, 0x00, 0x00, 0xc3,
        ])
    };
    let below = with(0x72);
    assert!(below.contains("if (a1 == 0) {"), "{below}");
    assert!(!below.contains("/*"), "{below}");
    let equal = with(0x74);
    assert!(equal.contains("if (tzcnt(a1) == 0) {"), "{equal}");
}

/// A below-or-equal after arithmetic reads as C, never as a bare value.
///
/// `add; jbe` is carry or zero, `and; jbe` the zero flag alone (a logical
/// operation clears the carry): both read as C, never as the bare value
/// under a comment, which C would read as `value != 0` both ways.
///
/// `mov eax,[esp+4]; add eax,[esp+8]; jbe L; ...` and `mov eax,[esp+4];
/// shr eax,3; and eax,0x3f; jbe L; ...`.
#[test]
fn below_or_equal_after_arithmetic_reads_as_c() {
    let add = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0x76, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(
        add.contains("if ((uaddo32(a1, a2) != 0 || a1 + a2 == 0)) {"),
        "{add}"
    );
    let and = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xc1, 0xe8, 0x03, 0x83, 0xe0, 0x3f, 0x76, 0x03, 0x33, 0xc0, 0xc3,
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(and.contains("if (((a1 >> 3) & 0x3f) == 0) {"), "{and}");
    assert!(!and.contains("/*"), "{and}");
}

/// `pop es` leaves `eax` alone in the emulator as in the lifter: the
/// emulator once indexed its general registers by the segment register's
/// number, which is `rax`'s, and popped into `ax`.
#[test]
fn pop_es_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0x68, 0x66, 0x55, 0x00, 0x00, // ASM: push 0x5566
        0x07, // ASM: pop es
        0x08, 0x00, // ASM: or [eax],al
        0xc3, // ASM: ret
    ]);
}

/// A shift whose count masks to 0 leaves every flag as it was, in the
/// lifter as in the emulator.
///
/// `shl eax, cl` with `cl` cleared shifts by nothing, so `sete` after it
/// reads the zero flag of `cmp edx, 1`, not the shifted value: the lifter
/// once set the flags from `eax` and read `al` as `eax == 0`.
#[test]
fn a_zero_count_shift_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x33, 0xc9, // ASM: xor ecx, ecx
        0x83, 0xfa, 0x01, // ASM: cmp edx, 1
        0xd3, 0xe0, // ASM: shl eax, cl
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
}

/// A constant count masking to 0 leaves the flags too: `shl eax, 32` is
/// a shift by nothing, and `sete` reads the compare before it.
#[test]
fn a_shift_by_the_width_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x83, 0xfa, 0x01, // ASM: cmp edx, 1
        0xc1, 0xe0, 0x20, // ASM: shl eax, 32
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
}

/// A count no constant gives may mask to 0 and leave every flag, so the
/// lifter states none for it: the `je` after `shl eax, cl` is read
/// neither as the shifted value being zero nor as the compare before.
///
/// The check seeds `ecx` next to the 32 it is compared with, where the
/// count masks to 0 and the machine branches on the compare.
#[test]
fn a_variable_count_shift_agrees_with_the_emulator() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let p = image(&[
        0x83, 0xf9, 0x20, // ASM: cmp ecx, 32
        0xd3, 0xe0, // ASM: shl eax, cl
        0x74, 0x03, // ASM: je 0x40100a
        0x33, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    for seed in 1..=16 {
        let v = verify(&p, &a, &[0x401000], seed);
        assert!(
            v.checked == 3 && v.mismatches.is_empty(),
            "seed {seed}: {}",
            verify_tsv(&v)
        );
    }
}

/// A shift by `cl` that masks to 0 keeps the overflow of the `sub` before
/// it, in the lifter as in the emulator: `setl` after `sub edx, 1; shl
/// eax, cl` with `cl` cleared reads the subtraction's SF != OF.
///
/// The lifter once took the shift for a writer of every flag, lifted the
/// `sub` as if its sign alone were read, and at `edx = 0x80000000` printed
/// a sign test that is 0 where the machine's overflow makes `al` 1.
#[test]
fn a_zero_count_shift_keeps_the_overflow_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x33, 0xc9, // ASM: xor ecx, ecx
        0xba, 0x00, 0x00, 0x00, 0x80, // ASM: mov edx, 0x80000000
        0x83, 0xea, 0x01, // ASM: sub edx, 1
        0xd3, 0xe0, // ASM: shl eax, cl
        0x0f, 0x9c, 0xc0, // ASM: setl al
        0xc3, // ASM: ret
    ]);
}

/// A rotate by `cl` that masks to 0 keeps every flag too: `setl` after
/// `sub edx, 1; rol eax, cl` reads the subtraction's SF != OF, where the
/// lifter once read its sign alone.
#[test]
fn a_zero_count_rotate_keeps_the_overflow_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x33, 0xc9, // ASM: xor ecx, ecx
        0xba, 0x00, 0x00, 0x00, 0x80, // ASM: mov edx, 0x80000000
        0x83, 0xea, 0x01, // ASM: sub edx, 1
        0xd3, 0xc0, // ASM: rol eax, cl
        0x0f, 0x9c, 0xc0, // ASM: setl al
        0xc3, // ASM: ret
    ]);
}

/// A 64-bit shift masks its count to six bits, not five: `shl rax, 32`
/// shifts by 32 and sets the zero flag from the result, so `sete` after
/// `cmp edx, 1; shl rax, 32` reads the low half of `rax`, while `shl rax,
/// 64` masks to 0 and leaves the compare's flags.
#[test]
fn a_64_bit_shift_count_masks_to_six_bits_agrees_with_the_emulator() {
    for count in [0x20, 0x40] {
        agrees_with_the_emulator_64(&[
            0x83, 0xfa, 0x01, // ASM: cmp edx, 1
            0x48, 0xc1, 0xe0, count, // ASM: shl rax, count
            0x0f, 0x94, 0xc0, // ASM: sete al
            0xc3, // ASM: ret
        ]);
    }
}

/// A block that opens with a shift by `cl` still reads the flags the block
/// before it left: `jl` after `sub edx, 1; jmp B; B: shl eax, cl` with
/// `cl` cleared is the compare of the argument with 1. Across the blocks
/// the shift once counted as a writer of every flag, so the first block
/// handed none on and the condition read as unknown.
///
/// `mov edx,[esp+4]; xor ecx,ecx; sub edx,1; jmp B; B: shl eax,cl; jl L;
/// xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn a_shift_by_cl_opening_a_block_reads_the_flags_before_it() {
    let text = dc(&[
        0x8b, 0x54, 0x24, 0x04, 0x33, 0xc9, 0x83, 0xea, 0x01, 0xeb, 0x00, 0xd3, 0xe0, 0x7c, 0x03,
        0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(!text.contains("FLAGS_UNKNOWN"), "{text}");
    assert!(text.contains("a1 < 1"), "{text}");
}

/// A 16-bit address reads the 16-bit registers and wraps at 64 KiB, in the
/// lifter as in the emulator.
///
/// An address-size prefix in 32-bit code makes `[di-1]` the word `di` minus
/// one, modulo 2^16: never `edi`, and never `di` plus the 0xffff the
/// decoder holds the displacement as. Data decoded as code is full of such
/// prefixes (msvcrt's error strings). `mov edi,[esp+4]; mov dh,[esp+8];
/// add [di-1],dh; mov eax,[di+0x10]; ret`.
#[test]
fn a_16_bit_address_wraps_in_the_lifter_and_the_emulator() {
    let code = [
        0x8b, 0x7c, 0x24, 0x04, // ASM: mov edi,[esp+4]
        0x8a, 0x74, 0x24, 0x08, // ASM: mov dh,[esp+8]
        0x67, 0x00, 0x75, 0xff, // ASM: add [di-1],dh
        0x67, 0x8b, 0x45, 0x10, // ASM: mov eax,[di+0x10]
        0xc3, // ASM: ret
    ];
    let text = decompiled(&image(&code), 0x401000);
    assert!(text.contains("- 1) & 0xffff"), "{text}");
    agrees_with_the_emulator(&code);
}
