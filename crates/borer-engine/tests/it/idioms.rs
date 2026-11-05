//! Idioms the decompiler reads as the helpers they compute: `abs`,
//! rotates, saturating subtraction, midpoints, alignment, `min` and `max`,
//! each defined at the top of the text that calls it.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::verify::{Fact, verify, verify_tsv};
use borer_engine::program::Arch;

use crate::decompiled::{decompiled, program64};

/// Decompiles `code` as a 64-bit function, requires its text to hold
/// `want`, and requires the verifier to check it clean from eight seeds,
/// every register it compares readable.
///
/// # Arguments
///
/// * `code` - The function's bytes.
/// * `want` - A line the text must hold.
///
/// # Panics
///
/// When the text lacks `want` or a seed finds a mismatch.
fn reads_as(code: &[u8], want: &str) {
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains(want), "{text}");
    let a = Analysis::compute(&p);
    for seed in 1..=8 {
        let v = verify(&p, &a, &[0x1_4000_1000], seed);
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
        assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
        let regs = v.facts.get(&Fact::Register).copied().unwrap_or_default();
        assert_eq!(regs.unreadable, 0, "seed {seed}: {}", verify_tsv(&v));
    }
}

/// `cqo` then `xor`/`sub`, and `cqo` then `add`/`xor`, are `llabs`.
///
/// C's `abs` takes an `int` and would cut the value to 32 bits. A 32-bit
/// `cdq` of the same shape stays arithmetic: that sign splat is 31 bits,
/// not the sign of a 64-bit value.
#[test]
fn a_sign_splat_subtracted_back_is_abs() {
    let cases: &[&[u8]] = &[
        &[
            0x48, 0x89, 0xc8, 0x48, 0x99, 0x48, 0x31, 0xd0, 0x48, 0x29, 0xd0, 0xc3,
        ],
        &[
            0x48, 0x89, 0xc8, 0x48, 0x99, 0x48, 0x01, 0xd0, 0x48, 0x31, 0xd0, 0xc3,
        ],
    ];
    for code in cases {
        reads_as(code, "return llabs(a1);");
    }
    let text = decompiled(
        &program64(&[0x89, 0xc8, 0x99, 0x31, 0xd0, 0x29, 0xd0, 0xc3]),
        0x1_4000_1000,
    );
    assert!(!text.contains("abs("), "{text}");
    assert!(text.contains('^'), "{text}");
}

/// `shld` of a register with itself is a rotate. Two registers stay the
/// shifts, and so does an arithmetic shift written as `sar`.
#[test]
fn a_complementary_shift_of_one_value_is_a_rotate() {
    let cases: &[(&[u8], &str)] = &[
        (
            &[0x48, 0x89, 0xc8, 0x48, 0x0f, 0xa4, 0xc0, 0x08, 0xc3],
            "return rotl64(a1, 8);",
        ),
        (
            &[0x48, 0x89, 0xc8, 0x48, 0x0f, 0xac, 0xc0, 0x08, 0xc3],
            "return rotr64(a1, 8);",
        ),
        (
            &[0x89, 0xc8, 0x0f, 0xa4, 0xc0, 0x08, 0xc3],
            "return rotl32(a1, 8);",
        ),
    ];
    for (code, want) in cases {
        reads_as(code, want);
    }
    let text = decompiled(
        &program64(&[0x48, 0x89, 0xc8, 0x48, 0x0f, 0xa4, 0xd0, 0x08, 0xc3]),
        0x1_4000_1000,
    );
    assert!(
        text.contains("<<") && text.contains(">>") && text.contains(" | "),
        "{text}"
    );
    assert!(!text.contains("rotl") && !text.contains("rotr"), "{text}");
}

/// `shld` of one register by `cl` is a rotate.
///
/// The count is masked to the
/// width, which a rotate already reduces, so the mask is not printed. Two
/// registers, and a 16-bit `shld`, stay the shifts. There is no 8-bit
/// `shld`: the same opcode without a `66` prefix is a 32-bit rotate.
#[test]
fn a_variable_count_of_one_register_is_a_rotate() {
    let cases: &[(&[u8], &str)] = &[
        (
            &[0x48, 0x89, 0xd0, 0x48, 0x0f, 0xa5, 0xc0, 0xc3],
            "return rotl64(a2, a1);",
        ),
        (
            &[0x48, 0x89, 0xd0, 0x48, 0x0f, 0xad, 0xc0, 0xc3],
            "return rotr64(a2, a1);",
        ),
        (
            &[0x89, 0xd0, 0x0f, 0xa5, 0xc0, 0xc3],
            "return rotl32(a2, a1);",
        ),
    ];
    for (code, want) in cases {
        reads_as(code, want);
    }
    for code in [
        &[0x48, 0x89, 0xc8, 0x48, 0x0f, 0xa5, 0xd0, 0xc3][..],
        &[0x66, 0x89, 0xc8, 0x66, 0x0f, 0xa5, 0xc0, 0xc3],
    ] {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert!(!text.contains("rotl") && !text.contains("rotr"), "{text}");
    }
}

/// `cmovb` of zero over an unsigned subtract clamps at zero. A 32-bit
/// subtract, a signed `cmovl`, and a select of the other operand do not.
#[test]
fn an_unsigned_subtract_that_clamps_is_sub_sat() {
    let cases: &[(&[u8], &str)] = &[
        (
            &[
                0x4d, 0x31, 0xc0, 0x48, 0x89, 0xc8, 0x48, 0x29, 0xd0, 0x49, 0x0f, 0x42, 0xc0, 0xc3,
            ],
            "return sub_sat(a1, a2);",
        ),
        (
            &[
                0x4d, 0x31, 0xc0, 0x48, 0x89, 0xc8, 0x48, 0x29, 0xd0, 0x4c, 0x0f, 0x43, 0xc0, 0x4c,
                0x89, 0xc0, 0xc3,
            ],
            "return sub_sat(a1, a2);",
        ),
    ];
    for (code, want) in cases {
        reads_as(code, want);
    }
    for code in [
        &[
            0x45, 0x31, 0xc0, 0x89, 0xc8, 0x29, 0xd0, 0x41, 0x0f, 0x42, 0xc0, 0xc3,
        ][..],
        &[
            0x4d, 0x31, 0xc0, 0x48, 0x89, 0xc8, 0x48, 0x29, 0xd0, 0x49, 0x0f, 0x4c, 0xc0, 0xc3,
        ],
        &[
            0x4d, 0x31, 0xc0, 0x48, 0x89, 0xc8, 0x48, 0x29, 0xd0, 0x48, 0x0f, 0x42, 0xc2, 0xc3,
        ],
    ] {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert!(!text.contains("sub_sat"), "{text}");
        assert!(text.contains('?'), "{text}");
    }
}

/// `(x & y) + ((x ^ y) >> 1)` is the unsigned average, including when the
/// sum would wrap. A 32-bit copy of the same instructions is not the
/// average of the zero-extended values.
#[test]
fn an_unsigned_average_is_midpoint() {
    let code: &[u8] = &[
        0x48, 0x89, 0xc8, 0x48, 0x21, 0xd0, 0x49, 0x89, 0xc8, 0x49, 0x31, 0xd0, 0x49, 0xd1, 0xe8,
        0x4c, 0x01, 0xc0, 0xc3,
    ];
    reads_as(code, "return midpoint(a1, a2);");
    let text = decompiled(
        &program64(&[
            0x89, 0xc8, 0x21, 0xd0, 0x41, 0x89, 0xc8, 0x41, 0x31, 0xd0, 0x41, 0xd1, 0xe8, 0x44,
            0x01, 0xc0, 0xc3,
        ]),
        0x1_4000_1000,
    );
    assert!(!text.contains("midpoint"), "{text}");
    assert!(text.contains(">>"), "{text}");
}

/// `(x + 15) & ~15` rounds up to 16. A bare mask, and the same add in 32
/// bits, do not: the 32-bit mask clears the top half of the register.
#[test]
fn an_added_power_of_two_mask_is_align_up() {
    let code: &[u8] = &[
        0x48, 0x89, 0xc8, 0x48, 0x83, 0xc0, 0x0f, 0x48, 0x83, 0xe0, 0xf0, 0xc3,
    ];
    reads_as(code, "return align_up(a1, 0x10);");
    for code in [
        &[0x48, 0x89, 0xc8, 0x48, 0x83, 0xe0, 0xf0, 0xc3][..],
        &[0x89, 0xc8, 0x83, 0xc0, 0x0f, 0x83, 0xe0, 0xf0, 0xc3],
    ] {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert!(!text.contains("align_up"), "{text}");
        assert!(text.contains('&'), "{text}");
    }
}

/// `neg` then `cmovs` of the original register is `abs`.
///
/// `cmovns` is
/// `-abs`. A 32-bit `neg` and a select of a different register stay the
/// ternary: a negative 32-bit lane is not negative as a 64-bit value.
#[test]
fn a_full_width_negation_select_is_abs() {
    let cases: &[(&[u8], &str)] = &[
        (
            &[
                0x48, 0x89, 0xc8, 0x48, 0xf7, 0xd8, 0x48, 0x0f, 0x48, 0xc1, 0xc3,
            ],
            "return llabs(a1);",
        ),
        (
            &[
                0x48, 0x89, 0xc8, 0x48, 0xf7, 0xd8, 0x48, 0x0f, 0x49, 0xc1, 0xc3,
            ],
            "return -llabs(a1);",
        ),
    ];
    for (code, want) in cases {
        reads_as(code, want);
    }
    for code in [
        &[0x89, 0xc8, 0xf7, 0xd8, 0x0f, 0x48, 0xc1, 0xc3][..],
        &[
            0x48, 0x89, 0xc8, 0x48, 0xf7, 0xd8, 0x48, 0x0f, 0x48, 0xc2, 0xc3,
        ],
    ] {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert!(text.contains('?'), "{text}");
        assert!(!text.contains("abs("), "{text}");
    }
}

/// A helper call comes with its C definition at the top of the text, once.
///
/// The text then compiles as printed: `umin` is a `static inline` function
/// of the machine word, and `min` first drops the `min` macro a C library
/// may define.
///
/// # Panics
///
/// When a definition is missing, doubled, or below the code that calls it.
#[test]
fn a_helper_call_comes_with_its_definition() {
    let cases: &[(&[u8], &str, &str)] = &[
        (
            &[
                0x48, 0x89, 0xc8, 0x48, 0x39, 0xd1, 0x48, 0x0f, 0x47, 0xc2, 0xc3,
            ],
            "static inline uint64_t umin(uint64_t a, uint64_t b) { return a <= b ? a : b; }",
            "return umin(a1, a2);",
        ),
        (
            &[
                0x48, 0x89, 0xc8, 0x48, 0x39, 0xd1, 0x48, 0x0f, 0x4f, 0xc2, 0xc3,
            ],
            "static inline uint64_t min(int64_t a, int64_t b) { return a <= b ? a : b; }",
            "return min(a1, a2);",
        ),
    ];
    for (code, def, call) in cases {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert_eq!(text.matches(def).count(), 1, "{text}");
        let (at_def, at_call) = (text.find(def), text.find(call));
        assert!(at_def.is_some() && at_def < at_call, "{text}");
    }
    let text = decompiled(&program64(cases[1].0), 0x1_4000_1000);
    assert!(
        text.contains("#undef min\nstatic inline uint64_t min("),
        "{text}"
    );
}

/// A full-width compare that keeps one of its own operands is `min` or
/// `max`.
///
/// A 32-bit compare, a third register, and an equality test stay
/// the ternary: a narrower signed minimum is not the minimum of the
/// zero-extended values.
#[test]
fn a_full_width_compare_select_is_min_or_max() {
    let cases: &[(&[u8], &str)] = &[
        (
            &[
                0x48, 0x89, 0xc8, 0x48, 0x39, 0xd1, 0x48, 0x0f, 0x47, 0xc2, 0xc3,
            ],
            "return umin(a1, a2);",
        ),
        (
            &[
                0x48, 0x89, 0xc8, 0x48, 0x39, 0xd1, 0x48, 0x0f, 0x4f, 0xc2, 0xc3,
            ],
            "return min(a1, a2);",
        ),
    ];
    for (code, want) in cases {
        reads_as(code, want);
    }
    for code in [
        &[0x89, 0xc8, 0x39, 0xd1, 0x0f, 0x47, 0xc2, 0xc3][..],
        &[
            0x48, 0x89, 0xc8, 0x48, 0x39, 0xd1, 0x49, 0x0f, 0x47, 0xc0, 0xc3,
        ],
        &[
            0x48, 0x89, 0xc8, 0x48, 0x39, 0xd1, 0x48, 0x0f, 0x45, 0xc2, 0xc3,
        ],
    ] {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert!(text.contains('?'), "{text}");
        assert!(!text.contains("min(") && !text.contains("max("), "{text}");
    }
}

/// A word compare that keeps one of its own operands is `max` on a 32-bit
/// target too, where the helper computes at the 32-bit word.
///
/// The helper takes signed words and returns the unsigned word, so a
/// logical shift of it shifts as `shr` does and an unsigned compare of it
/// compares as `ja` does, uncast, and a
/// 16-bit compare stays the ternary.
#[test]
fn a_word_compare_select_on_a_32_bit_target_is_max() {
    let text = decompiled(
        &crate::raw::image(
            Arch::X86,
            &[
                0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
                0x8b, 0x4c, 0x24, 0x08, // ASM: mov ecx,[esp+8]
                0x39, 0xc8, // ASM: cmp eax,ecx
                0x0f, 0x4c, 0xc1, // ASM: cmovl eax,ecx
                0xc3, // ASM: ret
            ],
            &[],
        ),
        0x401000,
    );
    assert!(text.contains("return max(a1, a2);"), "{text}");
    assert!(
        text.contains("static inline uint32_t max(int32_t a, int32_t b)"),
        "{text}"
    );
    let text = decompiled(
        &crate::raw::image(
            Arch::X86,
            &[
                0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
                0x8b, 0x4c, 0x24, 0x08, // ASM: mov ecx,[esp+8]
                0x39, 0xc8, // ASM: cmp eax,ecx
                0x0f, 0x4c, 0xc1, // ASM: cmovl eax,ecx
                0xd1, 0xe8, // ASM: shr eax,1
                0xc3, // ASM: ret
            ],
            &[],
        ),
        0x401000,
    );
    assert!(text.contains("max(a1, a2) >> 1"), "{text}");
    let text = decompiled(
        &crate::raw::image(
            Arch::X86,
            &[
                0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
                0x8b, 0x4c, 0x24, 0x08, // ASM: mov ecx,[esp+8]
                0x39, 0xc8, // ASM: cmp eax,ecx
                0x0f, 0x4c, 0xc1, // ASM: cmovl eax,ecx
                0x83, 0xf8, 0x01, // ASM: cmp eax,1
                0x77, 0x03, // ASM: ja +3
                0x31, 0xc0, // ASM: xor eax,eax
                0xc3, // ASM: ret
                0xb0, 0x01, // ASM: mov al,1
                0xc3, // ASM: ret
            ],
            &[],
        ),
        0x401000,
    );
    assert!(text.contains("max(a1, a2) > 1"), "{text}");
    let text = decompiled(
        &crate::raw::image(
            Arch::X86,
            &[
                0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
                0x8b, 0x4c, 0x24, 0x08, // ASM: mov ecx,[esp+8]
                0x66, 0x39, 0xc8, // ASM: cmp ax,cx
                0x0f, 0x4c, 0xc1, // ASM: cmovl eax,ecx
                0xc3, // ASM: ret
            ],
            &[],
        ),
        0x401000,
    );
    assert!(text.contains('?') && !text.contains("max("), "{text}");
}

/// A value tested against itself and kept over zero is `max(x, 0)`.
///
/// `test` under a signed code compares it with zero: the trip count a
/// closed-form loop computes. The 64-bit one folds in the lift.
#[test]
fn a_tested_value_kept_over_zero_is_max_with_zero() {
    let text = decompiled(
        &crate::raw::image(
            Arch::X86,
            &[
                0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
                0x31, 0xd2, // ASM: xor edx,edx
                0x85, 0xc0, // ASM: test eax,eax
                0x0f, 0x4f, 0xd0, // ASM: cmovg edx,eax
                0x89, 0xd0, // ASM: mov eax,edx
                0xc3, // ASM: ret
            ],
            &[],
        ),
        0x401000,
    );
    assert!(text.contains("return max(a1, 0);"), "{text}");
    reads_as(
        &[
            0x31, 0xc0, // ASM: xor eax,eax
            0x48, 0x85, 0xc9, // ASM: test rcx,rcx
            0x48, 0x0f, 0x4f, 0xc1, // ASM: cmovg rax,rcx
            0xc3, // ASM: ret
        ],
        "return max(a1, 0);",
    );
}

/// A conditional move whose condition is proven constant by bit demand
/// folds to the arm that runs.
///
/// `(x * x + x) & 1` is always 0, so `cmovne` on `test` of it never moves
/// and `cmove` always moves.
#[test]
fn a_proven_constant_select_folds_to_the_arm_that_runs() {
    let code: &[u8] = &[
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x48, 0x0f, 0xaf, 0xc1, // ASM: imul rax,rcx
        0x48, 0x01, 0xc8, // ASM: add rax,rcx
        0xa8, 0x01, // ASM: test al,1
        0x48, 0x89, 0xd0, // ASM: mov rax,rdx
        0x49, 0x0f, 0x45, 0xc0, // ASM: cmovne rax,r8
        0xc3, // ASM: ret
    ];
    reads_as(code, "return a2;");
}

/// A value masked by its own complemented sign, `x & ~(x >> 31)`, is the
/// value clamped at zero.
///
/// `bic w9, w9, w9, asr #31` and `sar; not; and` are how a compiler
/// spells a loop's trip count `n > 0 ? n : 0`. The text says that as a
/// ternary on the sign, 32-bit or 64-bit (`max` at the machine word), with
/// the complement as `not` or as `xor` with all ones, and runs as the
/// machine does. A shift of another
/// register, a shift short of the sign, or an `xor` that leaves a bit stays
/// the bitwise text.
#[test]
fn a_value_masked_by_its_complemented_sign_is_clamped_at_zero() {
    for complement in [&[0xf7, 0xd0][..], &[0x83, 0xf0, 0xff][..]] {
        let code: Vec<u8> = [
            &[0x89, 0xc8, 0xc1, 0xf8, 0x1f][..],
            complement,
            &[0x21, 0xc8, 0xc3],
        ]
        .concat();
        reads_as(&code, "(int32_t)a1 >= 0 ? a1 : 0");
        let text = crate::decompiled::runs_agree(&program64(&code), 0x1_4000_1000);
        assert!(!text.contains(">>"), "{text}");
    }
    let wide = [
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x48, 0xc1, 0xf8, 0x3f, // ASM: sar rax,0x3f
        0x48, 0xf7, 0xd0, // ASM: not rax
        0x48, 0x21, 0xc8, // ASM: and rax,rcx
        0xc3, // ASM: ret
    ];
    reads_as(&wide, "return max(a1, 0);");
    crate::decompiled::runs_agree(&program64(&wide), 0x1_4000_1000);
    for code in [
        &[0x89, 0xd0, 0xc1, 0xf8, 0x1f, 0xf7, 0xd0, 0x21, 0xc8, 0xc3][..],
        &[0x89, 0xc8, 0xc1, 0xf8, 0x1e, 0xf7, 0xd0, 0x21, 0xc8, 0xc3][..],
        &[
            0x89, 0xc8, 0xc1, 0xf8, 0x1f, 0x35, 0xff, 0xff, 0xff, 0x7f, 0x21, 0xc8, 0xc3,
        ][..],
    ] {
        let text = decompiled(&program64(code), 0x1_4000_1000);
        assert!(text.contains(">>") && !text.contains('?'), "{text}");
    }
}

/// An `int` a test proved positive compares unsigned at `-O2`, which the
/// text spells signed: `if (n <= 0) return 0; if (n < 4) ...` prints no
/// `(uint32_t)n`, and the text still runs as the binary does.
#[test]
fn a_compare_after_a_positive_test_reads_signed() {
    let code = [
        0x85, 0xc9, // ASM: test ecx,ecx
        0x7e, 0x1c, // ASM: jle 0x20
        0x83, 0xf9, 0x04, // ASM: cmp ecx,4
        0x72, 0x11, // ASM: jb 0x1a
        0x83, 0xf9, 0x07, // ASM: cmp ecx,7
        0x72, 0x06, // ASM: jb 0x14
        0xb8, 3, 0, 0, 0,    // ASM: mov eax,3
        0xc3, // ASM: ret
        0xb8, 2, 0, 0, 0,    // ASM: mov eax,2
        0xc3, // ASM: ret
        0xb8, 1, 0, 0, 0,    // ASM: mov eax,1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let text = crate::decompiled::runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("if (a1 < 4) {"), "{text}");
    assert!(text.contains("if (a1 < 7) {"), "{text}");
    assert!(!text.contains("(uint32_t)"), "{text}");
}

/// A 64-bit value every ordered compare reads signed is an `int64_t`.
///
/// `cmp qword [rsp+8], 0; jle` printed `(int64_t)a1 <= 0` under a
/// `uint64_t a1`; the declaration takes the sign, the compare drops the
/// cast, and the text still runs as the binary does.
#[test]
fn a_word_compared_signed_is_declared_signed() {
    let code = [
        0x48, 0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8], rcx
        0x48, 0x83, 0x7c, 0x24, 0x08, 0x00, // ASM: cmp qword [rsp+8], 0
        0x7e, 0x06, // ASM: jle 0x140001013
        0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax, [rsp+8]
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let text = crate::decompiled::runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("(int64_t a1)"), "{text}");
    assert!(!text.contains("(int64_t)"), "{text}");
}
