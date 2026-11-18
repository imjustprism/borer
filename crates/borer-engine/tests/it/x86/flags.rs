//! Conditions read from the flags an instruction leaves.

use super::*;
use borer_engine::emulate::{Emulator, Stop};

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

/// `popcnt` clears CF, OF, SF and PF, in the lifter as in the emulator.
///
/// `popcnt eax, ecx; setcc al; ret` with `sets`, `setp`, `setb` and `seto`
/// sets `al` to 0, and `mov ecx,0x80000000; popcnt eax,ecx; js L` never
/// jumps. The lifter once read the sign and parity of the source.
#[test]
fn popcnt_clears_the_sign_and_parity_agrees_with_the_emulator() {
    for setcc in [0x98u8, 0x9a, 0x92, 0x90] {
        agrees_with_the_emulator(&[
            0xf3, 0x0f, 0xb8, 0xc1, // ASM: popcnt eax, ecx
            0x0f, setcc, 0xc0, // ASM: sets / setp / setb / seto al
            0xc3, // ASM: ret
        ]);
    }
    let text = dc(&[
        0xb9, 0x00, 0x00, 0x00, 0x80, // ASM: mov ecx, 0x80000000
        0xf3, 0x0f, 0xb8, 0xc1, // ASM: popcnt eax, ecx
        0x78, 0x03, // ASM: js 0x40100e
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    assert!(!text.contains("return 1"), "{text}");
}

/// `bsf`, `bsr`, `tzcnt` and `lzcnt` leave SF and PF undecided.
///
/// The manual leaves both undefined, so `sets` and `setp` after them never
/// disagree with the emulator, which keeps the flags of the `or` before,
/// and a `js` reads as an undecided sign test, not the sign of the source
/// or the count.
#[test]
fn a_bit_scan_or_count_leaves_the_sign_and_parity_undecided() {
    for [a, b, c] in [
        [0x90, 0x0f, 0xbc],
        [0x90, 0x0f, 0xbd],
        [0xf3, 0x0f, 0xbc],
        [0xf3, 0x0f, 0xbd],
    ] {
        for setcc in [0x98u8, 0x9a] {
            never_disagrees_with_the_emulator(&image(&[
                0x83, 0xca, 0xff, // ASM: or edx, -1
                a, b, c, 0xc1, // ASM: nop; bsf / bsr, or tzcnt / lzcnt eax, ecx
                0x0f, setcc, 0xc0, // ASM: sets / setp al
                0xc3, // ASM: ret
            ]));
        }
        let text = dc(&[
            0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx, [esp+4]
            a, b, c, 0xc1, // ASM: nop; bsf / bsr, or tzcnt / lzcnt eax, ecx
            0x78, 0x03, // ASM: js 0x40100d
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        assert!(text.contains("flags_"), "{text}");
        assert!(!text.contains("< 0"), "{text}");
    }
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

/// The flags of a result decide only its zero and sign tests.
///
/// `sar al, 8` leaves the sign bit in CF, so `jc` after it is taken at `al =
/// 0x81` and the function returns 1. The decompiler once read the result's
/// carry as 0, decided the branch untaken and dropped the arm.
///
/// `mov eax,0x81; sar al,8; jc L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn a_result_decides_no_carry() {
    let text = dc(&[
        0xb8, 0x81, 0x00, 0x00, 0x00, 0xc0, 0xf8, 0x08, 0x72, 0x03, 0x31, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(text.contains("return 1"), "{text}");
}

/// At the width or past it, `sar` leaves the sign bit in CF.
///
/// The sign bit is the last bit it shifts out: `setb` after `sar al, 8` or
/// `sar ax, 20` is the operand's sign, in the lifter as in the emulator. The
/// lifter once left CF undecided there, as the manual leaves it only for SHL
/// and SHR.
#[test]
fn a_sar_at_or_past_the_width_carries_the_sign_agrees_with_the_emulator() {
    for code in [
        &[0xc0, 0xf8, 0x08, 0x0f, 0x92, 0xc0, 0xc3][..], // ASM: sar al, 8; setb al; ret
        &[0x66, 0xc1, 0xf8, 0x14, 0x0f, 0x92, 0xc0, 0xc3][..], // ASM: sar ax, 20; setb al; ret
    ] {
        agrees_with_the_emulator(code);
        let text = dc(code);
        assert!(!text.contains("flags_"), "{text}");
    }
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

/// A 64-bit shift masks its count to six bits, not five.
///
/// `shl rax, 32` shifts by 32 and sets the zero flag from the result, so
/// `sete` after `cmp edx, 1; shl rax, 32` reads the low half of `rax`, while
/// `shl rax, 64` masks to 0 and leaves the compare's flags.
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

/// A block that opens with a shift by `cl` still reads inherited flags.
///
/// `jl` after `sub edx, 1; jmp B; B: shl eax, cl` with `cl` cleared is the
/// compare of the argument with 1. Across the blocks the shift once counted as
/// a writer of every flag, so the first block handed none on and the condition
/// read as unknown.
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

/// A double shift whose count masks to 0 leaves every flag as it was.
///
/// In the lifter as in the emulator, `shld eax, ebx, 32` shifts by nothing,
/// so `sete` after it reads the zero flag of `cmp edx, 1`. The lifter once
/// set the flags from the shifted value and read `al` as `eax == 0`.
#[test]
fn a_zero_count_double_shift_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x83, 0xfa, 0x01, // ASM: cmp edx, 1
        0x0f, 0xa4, 0xd8, 0x20, // ASM: shld eax, ebx, 32
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
}

/// A double shift by `cl` that masks to 0 keeps the prior `sub`'s overflow.
///
/// `setl` after `sub edx, 1; shrd eax, ebx, cl` with `cl` cleared reads the
/// subtraction's SF != OF, which overflows at `edx = 0x80000000`.
#[test]
fn a_zero_count_double_shift_by_cl_keeps_the_overflow_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x33, 0xc9, // ASM: xor ecx, ecx
        0xba, 0x00, 0x00, 0x00, 0x80, // ASM: mov edx, 0x80000000
        0x83, 0xea, 0x01, // ASM: sub edx, 1
        0x0f, 0xad, 0xd8, // ASM: shrd eax, ebx, cl
        0x0f, 0x9c, 0xc0, // ASM: setl al
        0xc3, // ASM: ret
    ]);
}

/// A 64-bit shift masks a constant count past the width before reading flags.
///
/// `shl rax, 65` shifts by one, so `setl` after it reads the overflow, which
/// makes it the top bit of `rax` before the shift. The lifter once matched the
/// one-bit form against the unmasked 65, missed it, and read bit 62.
#[test]
fn a_64_bit_shift_by_65_reads_the_overflow_agrees_with_the_emulator() {
    agrees_with_the_emulator_64(&[
        0x48, 0xc1, 0xe0, 0x41, // ASM: shl rax, 65
        0x0f, 0x9c, 0xc0, // ASM: setl al
        0xc3, // ASM: ret
    ]);
}

/// `shr rax, 65` shifts by one and lifts to no flags where OF may be read.
///
/// Its overflow is the top bit of `rax` before it, so its `setl` stays asm and
/// the block is not checked, where the lift once read the flags of a wider
/// shift and printed 0 for a top bit of 1.
#[test]
fn a_64_bit_shr_by_65_never_disagrees_with_the_emulator() {
    let code = [
        0x48, 0xc1, 0xe8, 0x41, // ASM: shr rax, 65
        0x0f, 0x9c, 0xc0, // ASM: setl al
        0xc3, // ASM: ret
    ];
    never_disagrees_with_the_emulator(&raw::image(Arch::X86_64, &code, &[]));
}

/// A one-bit double shift lifts to no flags where OF may be read.
///
/// `setl` after `shld eax, ebx, 1` reads the change of sign, which the lift
/// once took as 0, so the text took the branch the CPU does not at `eax =
/// 0x40000000`. The emulator, which sets that OF too, checks the lift.
#[test]
fn a_one_bit_double_shift_never_disagrees_with_the_emulator() {
    never_disagrees_with_the_emulator(&image(&[
        0x0f, 0xa4, 0xd8, 0x01, // ASM: shld eax, ebx, 1
        0x0f, 0x9c, 0xc0, // ASM: setl al
        0xc3, // ASM: ret
    ]));
}

/// A one-bit `shr` whose flags leave the block lifts to no flags either.
///
/// `jl` after `shr eax, 1` is taken when the top bit of `eax` was set (SF is
/// clear and OF is that bit), and with a `je` in the next block reading the
/// same flags the lift once read OF as 0 there, so the text returned 0 where
/// the binary returns 1.
///
/// `mov eax,[esp+4]; shr eax,1; jl L1; je L2; xor eax,eax; ret; L1: mov
/// eax,1; ret; L2: mov eax,2; ret`.
#[test]
fn a_one_bit_shr_whose_flags_leave_the_block_never_differs() {
    use borer_engine::analysis::render::{Verdict, check_generated};
    let p = image(&[
        0x8b, 0x44, 0x24, 0x04, 0xd1, 0xe8, 0x7c, 0x05, 0x74, 0x09, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let runs = check_generated(&p, &a, &o, 0x401000, 64, 1, 20_000).unwrap_or_default();
    assert!(!runs.is_empty(), "no input ran");
    let differ = runs.iter().any(|(_, v)| matches!(v, Verdict::Differs(..)));
    assert!(!differ, "{runs:?}");
}

/// MIR leaves carry and signed-relation branches on a result's flags
/// undecided, and a multi-bit shift leaves a signed branch undecided in C.
///
/// `sar al, 8` sets CF to the sign bit and leaves OF undefined, and `shl
/// eax, 2` on `0x20000000` sets SF with OF undefined: neither decides `jl`.
#[test]
fn a_result_or_multi_bit_shift_leaves_carry_and_overflow_undecided() {
    use borer_engine::analysis::decompile::verify::{verify_mir, verify_tsv};
    use borer_engine::analysis::render::{Verdict, check_generated};
    for jcc in [0x72u8, 0x7cu8] {
        let p = image(&[
            0xc0, 0xf8, 0x08, // ASM: sar al, 8
            jcc, 0x03, // ASM: jc / jl 0x401008
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        for seed in 1..=16 {
            let v = verify_mir(&p, &a, &[0x401000], seed);
            assert!(
                v.mismatches.is_empty(),
                "jcc {jcc:#x} seed {seed}: {}",
                verify_tsv(&v)
            );
        }
    }
    let shl = [
        0xb8, 0x00, 0x00, 0x00, 0x20, // ASM: mov eax, 0x20000000
        0xc1, 0xe0, 0x02, // ASM: shl eax, 2
        0x7c, 0x03, // ASM: jl 0x40100d
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let text = dc(&shl);
    assert!(text.contains("flags_l("), "{text}");
    let p = image(&shl);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let runs = check_generated(&p, &a, &o, 0x401000, 16, 1, 20_000).unwrap_or_default();
    let differ = runs.iter().any(|(_, v)| matches!(v, Verdict::Differs(..)));
    assert!(!differ, "{runs:?}");
}

/// A 16-bit double shift by 16 copies its source and sets CF from the last
/// bit shifted out of its destination, while counts 17 through 31 leave the
/// instruction unmodeled.
///
/// `jb` after `mov cl, 16; shld ax, bx, cl` reads that bit, never an
/// undecided flag.
#[test]
fn a_16_bit_double_shift_at_and_past_the_width_agrees_with_the_emulator() {
    for code in [
        &[0x66, 0x0f, 0xa4, 0xd8, 0x10, 0xc3][..], // ASM: shld ax, bx, 16; ret
        &[0x66, 0x0f, 0xac, 0xd8, 0x10, 0xc3][..], // ASM: shrd ax, bx, 16; ret
        &[0x66, 0x0f, 0xa4, 0xd8, 0x10, 0x0f, 0x92, 0xc0, 0xc3][..], // ASM: shld ax, bx, 16; setb al; ret
        &[0xb1, 0x10, 0x66, 0x0f, 0xa5, 0xd8, 0xc3][..], // ASM: mov cl, 16; shld ax, bx, cl; ret
        &[0xb1, 0x10, 0x66, 0x0f, 0xad, 0xd8, 0xc3][..], // ASM: mov cl, 16; shrd ax, bx, cl; ret
    ] {
        agrees_with_the_emulator(code);
    }
    let by_cl = dc(&[
        0xb1, 0x10, 0x66, 0x0f, 0xa5, 0xd8, 0x72, 0x03, 0x31, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00,
        0x00, 0xc3,
    ]);
    assert!(by_cl.contains("return 1"), "{by_cl}");
    assert!(!by_cl.to_lowercase().contains("flags_"), "{by_cl}");
    let past = [
        0x66, 0x0f, 0xa4, 0xd8, 0x11, // ASM: shld ax, bx, 17
        0x74, 0x03, // ASM: je 0x40100a
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    let text = dc(&past);
    assert!(text.contains("FLAGS_UNKNOWN"), "{text}");
    never_disagrees_with_the_emulator(&image(&past));
}

/// A 16-bit double shift by a loaded count agrees with the emulator.
///
/// It funnels through a 32-bit word, so every count from 0 through 16
/// agrees: `mov ecx, [esp+4]`, then `and ecx, 15; inc ecx` for counts 1 through 16
/// or `and ecx, 1; shl ecx, 4` for 0 or 16, then `shld ax, bx, cl; ret`,
/// and the same with `shrd`.
#[test]
fn a_16_bit_double_shift_by_a_loaded_count_agrees_with_the_emulator() {
    let counts: [&[u8]; 2] = [
        &[0x83, 0xe1, 0x0f, 0x41],             // ASM: and ecx, 15; inc ecx
        &[0x83, 0xe1, 0x01, 0xc1, 0xe1, 0x04], // ASM: and ecx, 1; shl ecx, 4
    ];
    for op in [0xa5u8, 0xad] {
        for count in counts {
            let load = &[0x8b, 0x4c, 0x24, 0x04][..]; // ASM: mov ecx, [esp+4]
            let shift = &[0x66, 0x0f, op, 0xd8, 0xc3][..]; // ASM: shld / shrd ax, bx, cl; ret
            agrees_with_the_emulator(&[load, count, shift].concat());
        }
    }
}

/// Runs 64-bit `code` at 0x401000 of a raw image to its end.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
///
/// # Returns
///
/// How the run stopped and `rax` after it, or `None` when no machine runs
/// the image.
fn emulated_64(code: &[u8]) -> Option<(Stop, u64)> {
    let p = raw::image(Arch::X86_64, code, &[]);
    let mut emu = Emulator::new(&p, 100)?;
    let stop = emu.run(0x401000).stop;
    Some((stop, emu.register("rax")?))
}

/// `inc` sets the overflow at the signed wrap and `pushfq; popfq` keeps it.
///
/// `jo` after `inc` of `0x7fffffff` is taken. The emulator once left the
/// overflow unknown and the push wrote it as a known clear, so the run
/// returned 0.
///
/// `mov eax,0x7fffffff; inc eax; pushfq; popfq; jo L; xor eax,eax; ret;
/// L: mov eax,1; ret`.
#[test]
fn inc_then_jo_agrees_with_the_emulator() {
    let code = [
        0xb8, 0xff, 0xff, 0xff, 0x7f, 0xff, 0xc0, 0x9c, 0x9d, 0x70, 0x03, 0x31, 0xc0, 0xc3, 0xb8,
        0x01, 0x00, 0x00, 0x00, 0xc3,
    ];
    assert_eq!(emulated_64(&code), Some((Stop::Returned, 1)));
    agrees_with_the_emulator_64(&[
        0xb8, 0xff, 0xff, 0xff, 0x7f, // ASM: mov eax, 0x7fffffff
        0xff, 0xc0, // ASM: inc eax
        0x0f, 0x90, 0xc0, // ASM: seto al
        0xc3, // ASM: ret
    ]);
}

/// `dec` sets the overflow when its operand is the smallest signed value,
/// and only then.
///
/// `jo` after `dec` of `0x80000000` is taken, after `dec` of `0x80000001`
/// it is not, and `seto` after each agrees with the lifter.
///
/// `mov eax,imm; dec eax; jo L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn dec_at_int_min_then_jo_agrees_with_the_emulator() {
    for (low, want) in [(0x00, 1), (0x01, 0)] {
        let code = [
            0xb8, low, 0x00, 0x00, 0x80, 0xff, 0xc8, 0x70, 0x03, 0x31, 0xc0, 0xc3, 0xb8, 0x01,
            0x00, 0x00, 0x00, 0xc3,
        ];
        assert_eq!(emulated_64(&code), Some((Stop::Returned, want)), "{low:#x}");
        agrees_with_the_emulator_64(&[
            0xb8, low, 0x00, 0x00, 0x80, // ASM: mov eax, imm
            0xff, 0xc8, // ASM: dec eax
            0x0f, 0x90, 0xc0, // ASM: seto al
            0xc3, // ASM: ret
        ]);
    }
}

/// `dec rbp; jg` runs on, where the emulator once stopped on an overflow
/// it did not set: `rbp` 2 decrements to 1 and the jump is taken.
///
/// `mov ebp,2; dec rbp; jg L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn dec_rbp_then_jg_runs() {
    let code = [
        0xbd, 0x02, 0x00, 0x00, 0x00, 0x48, 0xff, 0xcd, 0x7f, 0x03, 0x31, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ];
    assert_eq!(emulated_64(&code), Some((Stop::Returned, 1)));
}

/// The overflow of `inc` and `dec` is the signed wrap of the operand's own
/// width, at 8, 16, 32 and 64 bits, in the emulator and in the lifter, and
/// neither touches the carry.
///
/// Each case sets an operand and steps it, then `setcc al; movzx eax, al;
/// ret` reads the flag.
#[test]
fn inc_and_dec_overflow_at_every_width_agrees_with_the_emulator() {
    let seto = [0x0f, 0x90];
    let cases: [(&[u8], [u8; 2], u64); 12] = [
        (&[0xb0, 0x7f, 0xfe, 0xc0], seto, 1), // ASM: mov al, 0x7f; inc al
        (&[0xb0, 0x7e, 0xfe, 0xc0], seto, 0), // ASM: mov al, 0x7e; inc al
        (&[0xb0, 0x80, 0xfe, 0xc8], seto, 1), // ASM: mov al, 0x80; dec al
        (&[0x66, 0xb8, 0xff, 0x7f, 0x66, 0xff, 0xc0], seto, 1), // ASM: mov ax, 0x7fff; inc ax
        (&[0x66, 0xb8, 0x00, 0x80, 0x66, 0xff, 0xc8], seto, 1), // ASM: mov ax, 0x8000; dec ax
        (&[0x66, 0xb8, 0x01, 0x80, 0x66, 0xff, 0xc8], seto, 0), // ASM: mov ax, 0x8001; dec ax
        (&[0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc0], seto, 0), // ASM: mov eax, -1; inc eax
        (
            &[
                0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0x48, 0xff, 0xc0,
            ],
            seto,
            1,
        ), // ASM: mov rax, 0x7fffffffffffffff; inc rax
        (
            &[
                0x48, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x48, 0xff, 0xc8,
            ],
            seto,
            1,
        ), // ASM: mov rax, 0x8000000000000000; dec rax
        // ASM: mov eax, 0x7fffffff; inc rax
        (&[0xb8, 0xff, 0xff, 0xff, 0x7f, 0x48, 0xff, 0xc0], seto, 0),
        (&[0xf9, 0xb0, 0xff, 0xfe, 0xc0], [0x0f, 0x92], 1), // ASM: stc; mov al, 0xff; inc al
        (&[0xf9, 0xb0, 0x80, 0xfe, 0xc8], [0x0f, 0x92], 1), // ASM: stc; mov al, 0x80; dec al
    ];
    for (step, setcc, want) in cases {
        // ASM: setcc al; movzx eax, al; ret
        let read = [setcc[0], setcc[1], 0xc0, 0x0f, 0xb6, 0xc0, 0xc3];
        let code = [step, &read[..]].concat();
        assert_eq!(
            emulated_64(&code),
            Some((Stop::Returned, want)),
            "{step:02x?}"
        );
        agrees_with_the_emulator_64(&code);
    }
}

/// `pushfq` of an overflow nothing computed does not come back from `popfq`
/// as a known clear.
///
/// Once a flags word is forged, `popfq` trusts only the slot of the last
/// `pushfq` made with the overflow known: a `jo` after any other
/// word stops, as it does without the push. That takes in a nested push, a
/// word moved to another slot, `syscall`'s `r11`, and a word whose overflow
/// bit the routine set itself, in a forged word or in the trusted one, and
/// a run on the same machine after the one that forged a word, or a poke
/// over the trusted slot between runs. A `popfq` of another word leaves the
/// trusted slot trusted, and a run stopped and resumed answers as one run. A routine that forged
/// nothing restores a known overflow from any word it pushed.
#[test]
fn a_pushed_unknown_overflow_stays_unknown() {
    let unknown = [0xb8, 0x05, 0x00, 0x00, 0x00, 0xc1, 0xe0, 0x02]; // ASM: mov eax, 5; shl eax, 2
    let stops: [&[u8]; 8] = [
        &[0x9c, 0x9d],                   // ASM: pushfq; popfq
        &[0x9c, 0x9c, 0x9d, 0x9d],       // ASM: pushfq; pushfq; popfq; popfq
        &[0x9c, 0x59, 0x53, 0x51, 0x9d], // ASM: pushfq; pop rcx; push rbx; push rcx; popfq
        // ASM: pushfq; or qword [rsp], 0x800; popfq
        &[0x9c, 0x48, 0x81, 0x0c, 0x24, 0x00, 0x08, 0x00, 0x00, 0x9d],
        // ASM: pushfq; xor qword [rsp], 0x800; popfq
        &[0x9c, 0x48, 0x81, 0x34, 0x24, 0x00, 0x08, 0x00, 0x00, 0x9d],
        // ASM: pushfq; pop rcx; xor eax, eax; pushfq; mov [rsp], rcx; popfq
        &[0x9c, 0x59, 0x31, 0xc0, 0x9c, 0x48, 0x89, 0x0c, 0x24, 0x9d],
        // ASM: mov eax, 39; syscall; push r11; popfq
        &[0xb8, 0x27, 0x00, 0x00, 0x00, 0x0f, 0x05, 0x41, 0x53, 0x9d],
        // ASM: pushfq; pop rcx; xor eax, eax; pushfq; or qword [rsp], 0x800; popfq
        &[
            0x9c, 0x59, 0x31, 0xc0, 0x9c, 0x48, 0x81, 0x0c, 0x24, 0x00, 0x08, 0x00, 0x00, 0x9d,
        ],
    ];
    for saved in stops {
        let jo = [0x70, 0x01, 0xc3, 0xc3]; // ASM: jo +1; ret; ret
        let stop = emulated_64(&[&unknown[..], saved, &jo[..]].concat()).map(|(stop, _)| stop);
        assert!(
            matches!(&stop, Some(Stop::Unmodeled(what)) if what.contains("did not set")),
            "{saved:02x?}: {stop:?}"
        );
    }
    let callees = [
        0x9c, 0x58, 0xc3, // ASM: pushfq; pop rax; ret
        0x50, 0x9d, // ASM: push rax; popfq
        0x70, 0x01, 0xc3, 0xc3, // ASM: jo +1; ret; ret
    ];
    let p = raw::image(Arch::X86_64, &callees, &[]);
    let stop = Emulator::new(&p, 100).map(|mut emu| {
        emu.run(0x401000);
        emu.run(0x401003).stop
    });
    assert!(
        matches!(&stop, Some(Stop::Unmodeled(what)) if what.contains("did not set")),
        "a later run: {stop:?}"
    );
    let pushed = [
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
        0xc1, 0xe0, 0x02, // ASM: shl eax, 2
        0x6a, 0x02, // ASM: push 2
        0x9d, // ASM: popfq
        0x70, 0x03, // ASM: jo L
        0x31, 0xc0, 0xc3, // ASM: xor eax, eax; ret
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, // ASM: L: mov eax, 1; ret
    ];
    assert_eq!(emulated_64(&pushed), Some((Stop::Returned, 0)));
    let repushed = [
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
        0xc1, 0xe0, 0x02, // ASM: shl eax, 2
        0x9c, // ASM: pushfq
        0x59, // ASM: pop rcx
        0x31, 0xc0, // ASM: xor eax, eax
        0x9c, // ASM: pushfq
        0x9d, // ASM: popfq
        0x70, 0x03, // ASM: jo L
        0x31, 0xc0, 0xc3, // ASM: xor eax, eax; ret
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, // ASM: L: mov eax, 1; ret
    ];
    assert_eq!(emulated_64(&repushed), Some((Stop::Returned, 0)));
    let p = raw::image(Arch::X86_64, &repushed, &[]);
    for poke in [false, true] {
        let resumed = Emulator::new(&p, 100).and_then(|mut emu| {
            emu.stop_at(Some(0x40100d));
            emu.run(0x401000);
            emu.stop_at(None);
            if poke {
                let sp = emu.register("rsp")?;
                emu.poke(sp.wrapping_add(1), 0);
            }
            let stop = emu.run(0x40100d).stop;
            Some((stop, emu.register("rax")?))
        });
        if poke {
            assert!(
                matches!(&resumed, Some((Stop::Unmodeled(what), _)) if what.contains("did not set")),
                "a poked slot: {resumed:?}"
            );
        } else {
            assert_eq!(resumed, Some((Stop::Returned, 0)), "a resumed run");
        }
    }
    let nested = [
        0x31, 0xc0, // ASM: xor eax, eax
        0x9c, // ASM: pushfq
        0xc1, 0xe0, 0x02, // ASM: shl eax, 2
        0x9c, // ASM: pushfq
        0x9d, 0x9d, // ASM: popfq; popfq
        0x7c, 0x03, // ASM: jl L
        0x31, 0xc0, 0xc3, // ASM: xor eax, eax; ret
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, // ASM: L: mov eax, 1; ret
    ];
    assert_eq!(emulated_64(&nested), Some((Stop::Returned, 0)));
}
