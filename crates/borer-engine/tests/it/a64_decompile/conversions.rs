//! Float conversions, casts and conditions against the machine.

use super::*;

/// A conditional compare read back by `mrs NZCV` is the compare's flags
/// when its condition holds, and the immediate in bits 31 to 28 when it
/// does not.
///
/// The words are `ccmp`, `ccmn` and `fccmp`, each after a compare that
/// sets the flags and before `mrs NZCV`. A check compares every register
/// the `mrs` writes, from several seeds, and replays the text.
#[test]
fn conditional_compare_nzcv_matches_the_machine() {
    const CCMP_NZCV: [u32; 4] = [
        // ASM: cmp x0, x1
        0xeb01_001f,
        // ASM: ccmp x1, x2, #0x4, ne
        0xfa42_1024,
        // ASM: mrs x3, NZCV
        0xd53b_4203,
        // ASM: ret
        0xd65f_03c0,
    ];
    const CCMN_NZCV: [u32; 4] = [
        // ASM: cmp x0, x1
        0xeb01_001f,
        // ASM: ccmn w1, #0x3, #0x9, hs
        0x3a43_2829,
        // ASM: mrs x4, NZCV
        0xd53b_4204,
        // ASM: ret
        0xd65f_03c0,
    ];
    const FCCMP_NZCV: [u32; 8] = [
        // ASM: fmov d0, x0
        0x9e67_0000,
        // ASM: fmov d1, x1
        0x9e67_0021,
        // ASM: fcmp d0, d1
        0x1e61_2000,
        // ASM: fccmp d1, d0, #0xf, gt
        0x1e60_c42f,
        // ASM: mrs x13, NZCV
        0xd53b_420d,
        // ASM: fccmp d1, d0, #0xf, eq
        0x1e60_042f,
        // ASM: mrs x14, NZCV
        0xd53b_420e,
        // ASM: ret
        0xd65f_03c0,
    ];
    for words in [&CCMP_NZCV[..], &CCMN_NZCV[..], &FCCMP_NZCV[..]] {
        let (p, a, text) = decompiled_words(words);
        assert!(!text.contains("/* asm"), "{text}");
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            let tsv = verify_tsv(&v);
            assert!(v.checked > 0, "seed {seed}: {tsv}");
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{tsv}");
            assert!(v.mismatches.is_empty(), "seed {seed}: {text}\n{tsv}");
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `scvtf` and `ucvtf` print as a cast of the integer's own signedness.
///
/// A signed source keeps the sign extension, so a negative value is not
/// an unsigned bit pattern. A fixed-point form divides in a double and
/// narrows after, which is the conversion's one rounding.
///
/// Each value is stored: a float left only in `d0` is not the integer
/// return, so the listing would drop it. A 32-bit parameter declared at
/// that width drops the redundant integer cast; the store line carries
/// the conversion, and the signature's `int32_t` is not one.
#[test]
fn an_integer_to_float_is_a_cast() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: scvtf d0, x0 / str d0, [x1] / ret
        (
            &[0x9e62_0000, 0xfd00_0020, 0xd65f_03c0],
            &["(double)a1", "(int64_t a1"],
            &["16.0", " & "],
        ),
        // ASM: scvtf s0, w0 / str s0, [x1] / ret
        (
            &[0x1e22_0000, 0xbd00_0020, 0xd65f_03c0],
            &["int32_t a1", "(float)a1"],
            &["16.0", " & ", "(uint32_t)"],
        ),
        // ASM: ucvtf d0, x0 / str d0, [x1] / ret
        (
            &[0x9e63_0000, 0xfd00_0020, 0xd65f_03c0],
            &["(double)a1"],
            &["(int64_t)", "16.0", " & "],
        ),
        // ASM: ucvtf s0, w0 / str s0, [x1] / ret
        (
            &[0x1e23_0000, 0xbd00_0020, 0xd65f_03c0],
            &["uint32_t a1", "(float)a1"],
            &["(int32_t)", " & "],
        ),
        // ASM: scvtf d0, x0, #4 / str d0, [x1] / ret
        (
            &[0x9e42_f000, 0xfd00_0020, 0xd65f_03c0],
            &["(int64_t a1", "16.0"],
            &[" & "],
        ),
        // ASM: ucvtf s0, w0, #4 / str s0, [x1] / ret
        (
            &[0x1e03_f000, 0xbd00_0020, 0xd65f_03c0],
            &["uint32_t a1", "(float)", "16.0"],
            &["(int32_t)", " & "],
        ),
        // ASM: scvtf d0, w0 / str d0, [x1] / ret
        (
            &[0x1e62_0000, 0xfd00_0020, 0xd65f_03c0],
            &["int32_t a1", "(double)a1"],
            &["uint32_t a1", "(int32_t)", " & ", "16.0"],
        ),
        // ASM: ucvtf d0, w0 / str d0, [x1] / ret
        (
            &[0x1e63_0000, 0xfd00_0020, 0xd65f_03c0],
            &["uint32_t a1", "(double)a1"],
            &["(int32_t)", " & ", "16.0"],
        ),
        // ASM: scvtf s0, x0 / str s0, [x1] / ret
        (
            &[0x9e22_0000, 0xbd00_0020, 0xd65f_03c0],
            &["(float)a1", "(int64_t a1"],
            &["int32_t a1", "(int32_t)", "16.0", " & "],
        ),
        // ASM: ucvtf s0, x0 / str s0, [x1] / ret
        (
            &[0x9e23_0000, 0xbd00_0020, 0xd65f_03c0],
            &["(float)a1"],
            &["(int64_t)", "(int32_t)", "16.0", " & "],
        ),
        // ASM: scvtf s0, w0, #4 / str s0, [x1] / ret
        (
            &[0x1e02_f000, 0xbd00_0020, 0xd65f_03c0],
            &["int32_t a1", "(float)", "16.0"],
            &["uint32_t a1", "(int32_t)", " & "],
        ),
        // ASM: scvtf d0, w0, #4 / str d0, [x1] / ret
        (
            &[0x1e42_f000, 0xfd00_0020, 0xd65f_03c0],
            &["int32_t a1", "(double)", "16.0"],
            &["uint32_t a1", "(int32_t)", " & "],
        ),
        // ASM: ucvtf d0, w0, #4 / str d0, [x1] / ret
        (
            &[0x1e43_f000, 0xfd00_0020, 0xd65f_03c0],
            &["uint32_t a1", "(double)", "16.0"],
            &["(int32_t)", " & "],
        ),
        // ASM: scvtf s0, x0, #4 / str s0, [x1] / ret
        (
            &[0x9e02_f000, 0xbd00_0020, 0xd65f_03c0],
            &["(float)", "(int64_t a1", "16.0"],
            &[" & "],
        ),
        // ASM: ucvtf s0, x0, #4 / str s0, [x1] / ret
        (
            &[0x9e03_f000, 0xbd00_0020, 0xd65f_03c0],
            &["(float)", "16.0"],
            &["(int64_t)", "(int32_t)", " & "],
        ),
    ];
    for (words, has, has_not) in cases {
        let (p, a, text) = decompiled_words(words);
        for part in *has {
            assert!(text.contains(part), "{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "{text}");
        }
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert_eq!(v.checked, 1, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `fcvt` converts the float the source operand reads.
///
/// A register whose value is the other width contributes that encoding,
/// then the conversion: the number the expression holds is a different
/// float. An in-place conversion declares the parameter at the width that
/// was read, so the cast is not dropped as the result's type.
#[test]
fn a_float_conversion_reads_the_source_width() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: scvtf d0, x0 / fcvt d1, s0 / str d1, [x1] / ret
        // The low 32 bits of the double, as a single, converted back.
        (
            &[0x9e62_0000, 0x1e22_c001, 0xfd00_0021, 0xd65f_03c0],
            &[
                "*(double*)",
                "(double)",
                "(float)",
                "0xffffffff",
                "(int64_t a1",
            ],
            &["*(uint64_t*)", "*(float*)", "/* asm"],
        ),
        // ASM: scvtf s0, w0 / fcvt s1, d0 / str s1, [x1] / ret
        // The single's bits, zero-extended, read as a double, then narrowed.
        (
            &[0x1e22_0000, 0x1e62_4001, 0xbd00_0021, 0xd65f_03c0],
            &[
                "*(float*)",
                "(float)",
                "(double)",
                "0xffffffff",
                "int32_t a1",
            ],
            &["*(uint32_t*)", "*(double*)", "/* asm"],
        ),
        // ASM: fcvt d0, s0 / str d0, [x0] / ret
        (
            &[0x1e22_c000, 0xfd00_0000, 0xd65f_03c0],
            &["*(double*)", "(double)a", "float a"],
            &["double a", "*(uint64_t*)", "/* asm"],
        ),
        // ASM: fcvt s0, d0 / str s0, [x0] / ret
        (
            &[0x1e62_4000, 0xbd00_0000, 0xd65f_03c0],
            &["*(float*)", "(float)a", "double a"],
            &["float a", "*(uint32_t*)", "/* asm"],
        ),
    ];
    for (words, has, has_not) in cases {
        let (p, a, text) = decompiled_words(words);
        for part in *has {
            assert!(text.contains(part), "{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "{text}");
        }
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert!(v.checked > 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `fcvt` of bits that are not already the source float converts those
/// bits, then the number.
///
/// A narrower name still holds whatever arrived above that lane. A sign
/// bit flipped or cleared on a name is that integer pattern. An integer
/// moved into the lane is those bits, not a cast of the integer. A value
/// the instruction already computed at the source width stays the number,
/// and a single written into the same register is the zero-extended
/// encoding, not the untouched high half.
#[test]
fn a_float_conversion_of_bits_converts_those_bits() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: fadd s1, s0, s1 / fcvt s2, d0 / str s2, [x2] / ret
        // `s0` named v0 a float. `d0` still has the bits above that lane.
        (
            &[0x1e21_2801, 0x1e62_4002, 0xbd00_0042, 0xd65f_03c0],
            &["*(float*)", "(float)", "(double)", "^ 0.0", "float a"],
            &["^ 0.0f", "/* asm"],
        ),
        // ASM: fneg d0, d0 / fcvt s0, d0 / str s0, [x0] / ret
        (
            &[0x1e61_4000, 0x1e62_4000, 0xbd00_0000, 0xd65f_03c0],
            &[
                "*(float*)",
                "(float)",
                "(double)",
                "0x8000000000000000",
                "^ 0.0",
                "double a",
            ],
            &["*(uint32_t*)", "/* asm"],
        ),
        // ASM: fneg s0, s0 / fcvt d0, s0 / str d0, [x0] / ret
        (
            &[0x1e21_4000, 0x1e22_c000, 0xfd00_0000, 0xd65f_03c0],
            &[
                "*(double*)",
                "(double)",
                "(float)",
                "0x80000000",
                "^ 0.0f",
                "float a",
            ],
            &["*(uint64_t*)", "/* asm"],
        ),
        // ASM: fabs d0, d0 / fcvt s0, d0 / str s0, [x0] / ret
        (
            &[0x1e60_c000, 0x1e62_4000, 0xbd00_0000, 0xd65f_03c0],
            &[
                "*(float*)",
                "(float)",
                "0x7fffffffffffffff",
                "^ 0.0",
                "double a",
            ],
            &["*(uint32_t*)", "/* asm"],
        ),
        // ASM: fmov d0, x0 / fcvt s0, d0 / str s0, [x1] / ret
        // The integer stays an integer. The lane's bits are the double.
        (
            &[0x9e67_0000, 0x1e62_4000, 0xbd00_0020, 0xd65f_03c0],
            &["*(float*)", "(float)", "(double)", "^ 0.0"],
            &["double a1", "*(uint32_t*)", "/* asm"],
        ),
        // ASM: fmov s0, w0 / fcvt d0, s0 / str d0, [x1] / ret
        (
            &[0x1e27_0000, 0x1e22_c000, 0xfd00_0020, 0xd65f_03c0],
            &["*(double*)", "(double)", "(float)", "^ 0.0f"],
            &["float a1", "double a1", "*(uint64_t*)", "/* asm"],
        ),
        // ASM: fadd s0, s0, s0 / fcvt s1, d0 / str s1, [x1] / ret
        // The single write cleared the bits above it.
        (
            &[0x1e20_2800, 0x1e62_4001, 0xbd00_0021, 0xd65f_03c0],
            &["*(float*)", "(float)", "(double)", "0xffffffff"],
            &["^ 0.0", "/* asm"],
        ),
        // ASM: scvtf d0, x0 / fneg d0, d0 / fcvt s0, d0 / str s0, [x1] / ret
        // The negation is of the number, not a second encoding of its bits.
        (
            &[
                0x9e62_0000,
                0x1e61_4000,
                0x1e62_4000,
                0xbd00_0020,
                0xd65f_03c0,
            ],
            &["*(float*)", "(float)", "-"],
            &["^ 0.0", "0x8000000000000000", "/* asm"],
        ),
        // ASM: fmov s1, s0 / fcvt d1, s1 / str d1, [x1] / ret
        // The move kept the low half. The conversion is of that single.
        (
            &[0x1e20_4001, 0x1e22_c021, 0xfd00_0021, 0xd65f_03c0],
            &["*(double*)", "(double)", "(float)", "0xffffffff", "^ 0.0f"],
            &["/* asm"],
        ),
        // ASM: scvtf d0, x0 / fmov s1, s0 / fcvt d1, s1 / str d1, [x1] / ret
        (
            &[
                0x9e62_0000,
                0x1e20_4001,
                0x1e22_c021,
                0xfd00_0021,
                0xd65f_03c0,
            ],
            &["*(double*)", "(double)", "(float)", "0xffffffff", "^ 0.0f"],
            &["/* asm"],
        ),
        // ASM: fcmp s0, s1 / fcsel s0, s0, s1, mi / fcvt d0, s0 / str d0, [x0] / ret
        // The select is the single's bits, with zeros above, then the conversion.
        (
            &[
                0x1e21_2000,
                0x1e21_4c00,
                0x1e22_c000,
                0xfd00_0000,
                0xd65f_03c0,
            ],
            &["*(double*)", "(double)", "(float)", "?", "^ 0.0f"],
            &["/* asm"],
        ),
        // ASM: fcmp d0, d1 / fcsel d0, d0, d1, mi / fcvt s0, d0 / str s0, [x0] / ret
        (
            &[
                0x1e61_2000,
                0x1e61_4c00,
                0x1e62_4000,
                0xbd00_0000,
                0xd65f_03c0,
            ],
            &["*(float*)", "(float)", "(double)", "?", "^ 0.0"],
            &["/* asm"],
        ),
    ];
    for (words, has, has_not) in cases {
        let (p, a, text) = decompiled_words(words);
        for part in *has {
            assert!(text.contains(part), "{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "{text}");
        }
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert!(v.checked > 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `fcvtzu` prints with the integer width on the name and the float width
/// as its second argument. A negative value saturates to 0, not to the
/// signed minimum.
#[test]
fn an_unsigned_float_to_int_is_fcvtzu() {
    let cases: &[(&[u32], &str, &str)] = &[
        (&[0x9e79_0000, 0xd65f_03c0], "fcvtzu64(", ", 64)"),
        (&[0x9e39_0000, 0xd65f_03c0], "fcvtzu64(", ", 32)"),
        (&[0x1e79_0000, 0xd65f_03c0], "fcvtzu32(", ", 64)"),
        (&[0x1e39_0000, 0xd65f_03c0], "fcvtzu32(", ", 32)"),
    ];
    for (words, name, width) in cases {
        let (p, a, text) = decompiled_words(words);
        assert!(text.contains(name), "{text}");
        assert!(text.contains(width), "{text}");
        assert!(text.contains("return "), "{text}");
        assert!(!text.contains("__fcvtzu"), "{text}");
        assert!(!text.contains("0xffffffff"), "{text}");
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert_eq!(v.checked, 1, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// A fixed-point `fcvtzu` scales inside the call, at the float's width.
///
/// The register has no float type until the conversion reads it. The scale
/// is a power of two, so the product is exact at that width and the result
/// is the same integer the machine writes.
#[test]
fn a_fixed_point_unsigned_conversion_scales_inside_the_call() {
    let cases: &[(&[u32], &str, &str)] = &[
        // ASM: fcvtzu x0, d0, #4 / ret
        (&[0x9e59_f000, 0xd65f_03c0], "fcvtzu64(", ", 64)"),
        // ASM: fcvtzu w0, s0, #4 / ret
        (&[0x1e19_f000, 0xd65f_03c0], "fcvtzu32(", ", 32)"),
        // ASM: fcvtzs x0, d0, #4 / ret
        (&[0x9e58_f000, 0xd65f_03c0], "fcvtzs64(", ", 64)"),
    ];
    for (words, name, width) in cases {
        let (p, a, text) = decompiled_words(words);
        assert!(text.contains(name), "{text}");
        assert!(text.contains(width), "{text}");
        assert!(text.contains("16.0"), "{text}");
        assert!(!text.contains("__fcvt"), "{text}");
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert_eq!(v.checked, 1, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `fcvtzs` prints with the integer width on the name and the float width
/// as its second argument. A 32-bit destination saturates there, not as a
/// cut 64-bit conversion.
#[test]
fn a_signed_float_to_int_is_fcvtzs() {
    let cases: &[(&[u32], &str, &str)] = &[
        (&[0x9e78_0000, 0xd65f_03c0], "fcvtzs64(", ", 64)"),
        (&[0x9e38_0000, 0xd65f_03c0], "fcvtzs64(", ", 32)"),
        (&[0x1e78_0000, 0xd65f_03c0], "fcvtzs32(", ", 64)"),
        (&[0x1e38_0000, 0xd65f_03c0], "fcvtzs32(", ", 32)"),
    ];
    for (words, name, width) in cases {
        let (p, a, text) = decompiled_words(words);
        assert!(text.contains(name), "{text}");
        assert!(text.contains(width), "{text}");
        assert!(text.contains("return "), "{text}");
        assert!(!text.contains("__fcvtzs"), "{text}");
        assert!(!text.contains("0xffffffff"), "{text}");
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert_eq!(v.checked, 1, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `pl` and `hs` after a float compare are the ordered less-than inverted.
///
/// N is that less-than, and C is its inverse, so `pl` and `hs` hold
/// together. Reading either as the less-than takes the other arm: a
/// branch, an `fcsel` of two bit patterns moved into the lanes, and an
/// `fccmp` whose predicate is `pl`. An immediate of zero would clear Z,
/// so the `b.eq` after that `fccmp` would not be the compare's equality.
#[test]
fn a_float_positive_condition_is_not_the_less_than() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: fcmp d0, d1 / b.pl / mov w0, #2 / ret / mov w0, #1 / ret
        (
            &[
                0x1e61_2000,
                0x5400_0065,
                0x5280_0040,
                0xd65f_03c0,
                0x5280_0020,
                0xd65f_03c0,
            ],
            &["!(a1 < a2)", "float a"],
            &["/* asm", "&&", "isunordered"],
        ),
        // ASM: fcmp d0, d1 / b.hs / mov w0, #2 / ret / mov w0, #1 / ret
        (
            &[
                0x1e61_2000,
                0x5400_0062,
                0x5280_0040,
                0xd65f_03c0,
                0x5280_0020,
                0xd65f_03c0,
            ],
            &["!(a1 < a2)", "float a"],
            &["/* asm", "&&", "isunordered"],
        ),
        // ASM: fcmp s0, s1 / b.pl / mov w0, #2 / ret / mov w0, #1 / ret
        (
            &[
                0x1e21_2000,
                0x5400_0065,
                0x5280_0040,
                0xd65f_03c0,
                0x5280_0020,
                0xd65f_03c0,
            ],
            &["!(a1 < a2)", "float a"],
            &["/* asm", "&&", "isunordered"],
        ),
        // ASM: fmov d0, x0 / fmov d1, x1 / fcmp d0, d1 / fcsel d2, d0, d1, pl
        //      / str d2, [x2] / ret
        (
            &[
                0x9e67_0000,
                0x9e67_0021,
                0x1e61_2000,
                0x1e61_5c02,
                0xfd00_0042,
                0xd65f_03c0,
            ],
            &["!(*(double*)&a1 < *(double*)&a2)", "*(uint64_t*)a3"],
            &["/* asm", "*(double*)a3", "&&"],
        ),
        // ASM: fmov d0, x0 / fmov d1, x1 / fcmp d0, d1 / fcsel d2, d0, d1, hs
        //      / str d2, [x2] / ret
        (
            &[
                0x9e67_0000,
                0x9e67_0021,
                0x1e61_2000,
                0x1e61_2c02,
                0xfd00_0042,
                0xd65f_03c0,
            ],
            &["!(*(double*)&a1 < *(double*)&a2)", "*(uint64_t*)a3"],
            &["/* asm", "*(double*)a3", "&&"],
        ),
        // ASM: fcmp d0, d1 / fccmp d0, d1, #0, pl / b.eq / mov w0, #2 / ret
        // ASM: mov w0, #1 / ret
        (
            &[
                0x1e61_2000,
                0x1e61_5400,
                0x5400_0060,
                0x5280_0040,
                0xd65f_03c0,
                0x5280_0020,
                0xd65f_03c0,
            ],
            &["!(a1 < a2)", "a1 == a2"],
            &["/* asm", "isunordered"],
        ),
    ];
    for (words, has, has_not) in cases {
        let (p, a, text) = decompiled_words(words);
        for part in *has {
            assert!(text.contains(part), "{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "{text}");
        }
        let entry = p.entry.expect("entry");
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            assert!(
                v.mismatches.is_empty(),
                "seed {seed}: {text}\n{}",
                verify_tsv(&v)
            );
            assert!(v.checked > 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {text}\n{}", verify_tsv(&v));
        }
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// One scalar float condition, single and double, against the machine.
///
/// The bits moved in with `fmov` are the operands, so a seed can be a NaN,
/// a zero of either sign, or the value compared with itself. `fcmp` and
/// `fcmpe` leave the same flags. `fcsel` stores the chosen lane. `fccmp`
/// uses the compare only when its predicate holds.
#[test]
fn scalar_float_conditions_match_the_machine() {
    /// Checks eight seeds of verify and one replay, recording a disagreement.
    fn check(failures: &mut String, label: &str, words: &[u32]) {
        let (p, a, text) = decompiled_words(words);
        if text.contains("/* asm") {
            failures.push_str(&format!("{label}: asm\n{text}\n"));
            return;
        }
        let entry = p.entry.expect("entry");
        if label == "fcmp d b.hs" || label == "fcmp d b.pl" {
            let want = "if (!(*(double*)&a1 < *(double*)&a2)) {";
            if !text.contains(want) {
                failures.push_str(&format!("{label} prints\n{text}\n"));
            }
        }
        if label == "fcmp d b.lo" || label == "fcmp d b.mi" {
            let want = "if (*(double*)&a1 < *(double*)&a2) {";
            if !text.contains(want) {
                failures.push_str(&format!("{label} prints\n{text}\n"));
            }
        }
        for seed in 1..=8 {
            let v = verify(&p, &a, &[entry], seed);
            if v.checked == 0 || v.unreadable != 0 || !v.mismatches.is_empty() {
                failures.push_str(&format!(
                    "{label} verify seed {seed}\n{text}\n{}\n",
                    verify_tsv(&v)
                ));
                return;
            }
            let r = replay_function(&p, &a, entry, seed);
            if r.checked == 0 || !r.wrong().is_empty() {
                failures.push_str(&format!(
                    "{label} replay seed {seed}\n{text}\n{}\n",
                    replay_tsv(&r)
                ));
                return;
            }
        }
    }

    let conds: &[(&str, u32)] = &[
        ("eq", 0),
        ("ne", 1),
        ("hs", 2),
        ("lo", 3),
        ("mi", 4),
        ("pl", 5),
        ("vs", 6),
        ("vc", 7),
        ("hi", 8),
        ("ls", 9),
        ("ge", 10),
        ("lt", 11),
        ("gt", 12),
        ("le", 13),
    ];
    let mut failures = String::new();
    for &(name, cond) in conds {
        for (width, fmov, fcmp, fcmpe, fcsel, fmov_back) in [
            (
                "d",
                0x9e67_0000u32,
                0x1e60_2000u32,
                0x1e60_2010u32,
                0x1e60_0c00u32,
                0x9e66_0000u32,
            ),
            (
                "s",
                0x1e27_0000,
                0x1e20_2000,
                0x1e20_2010,
                0x1e20_0c00,
                0x1e26_0000,
            ),
        ] {
            let branch = 0x5400_0060 | cond;
            let mov = |d: u32, n: u32| fmov | (n << 5) | d;
            check(
                &mut failures,
                &format!("fcmp {width} b.{name}"),
                &[
                    mov(0, 0),
                    mov(1, 1),
                    fcmp | (1 << 16),
                    branch,
                    0x5280_0040,
                    0xd65f_03c0,
                    0x5280_0020,
                    0xd65f_03c0,
                ],
            );
            check(
                &mut failures,
                &format!("fcmpe {width} b.{name}"),
                &[
                    mov(0, 0),
                    mov(1, 1),
                    fcmpe | (1 << 16),
                    branch,
                    0x5280_0040,
                    0xd65f_03c0,
                    0x5280_0020,
                    0xd65f_03c0,
                ],
            );
            check(
                &mut failures,
                &format!("fcmp {width} self b.{name}"),
                &[
                    mov(0, 0),
                    fcmp,
                    branch,
                    0x5280_0040,
                    0xd65f_03c0,
                    0x5280_0020,
                    0xd65f_03c0,
                ],
            );
            check(
                &mut failures,
                &format!("fcmp {width} +0 b.{name}"),
                &[
                    mov(0, 0),
                    fmov | (31 << 5) | 1,
                    fcmp | (1 << 16),
                    branch,
                    0x5280_0040,
                    0xd65f_03c0,
                    0x5280_0020,
                    0xd65f_03c0,
                ],
            );
            let select = fcsel | (3 << 16) | (cond << 12) | (2 << 5) | 4;
            let back = fmov_back | (4 << 5);
            check(
                &mut failures,
                &format!("fcsel {width} {name}"),
                &[
                    mov(0, 0),
                    mov(1, 1),
                    mov(2, 2),
                    mov(3, 3),
                    fcmp | (1 << 16),
                    select,
                    back,
                    0xd65f_03c0,
                ],
            );
            for &nzcv in &[0u32, 0x4, 0x8, 0xf] {
                for &(ask, ask_cond) in &[("eq", 0u32), ("ne", 1u32)] {
                    let pred = if width == "d" {
                        0x1e60_0400u32
                    } else {
                        0x1e20_0400u32
                    };
                    let fccmp = pred | (3 << 16) | (cond << 12) | (2 << 5) | nzcv;
                    check(
                        &mut failures,
                        &format!("fccmp {width} {name} #{nzcv:x} b.{ask}"),
                        &[
                            mov(0, 0),
                            mov(1, 1),
                            mov(2, 2),
                            mov(3, 3),
                            fcmp | (1 << 16),
                            fccmp,
                            0x5400_0060 | ask_cond,
                            0x5280_0040,
                            0xd65f_03c0,
                            0x5280_0020,
                            0xd65f_03c0,
                        ],
                    );
                }
            }
        }
    }
    assert!(failures.is_empty(), "{failures}");
}

/// A single written from a 64-bit integer clears bits 63:32. `fcvt`
/// stored at the other width keeps the result's encoding. A sign bit
/// moved through a general register is still that bit.
#[test]
fn scalar_casts_and_moves_match_the_machine() {
    let cases: &[&[u32]] = &[
        // ASM: scvtf s0, x0 / str d0, [x1] / ret
        &[0x9e22_0000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: ucvtf s0, x0 / str d0, [x1] / ret
        &[0x9e23_0000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: scvtf s0, x0, #4 / str d0, [x1] / ret
        &[0x9e02_f000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: ucvtf s0, x0, #4 / str d0, [x1] / ret
        &[0x9e03_f000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: add x2, x0, #0 / scvtf d0, w0 / str d0, [x1] / str x2, [x3] / ret
        &[
            0x9100_0002,
            0x1e62_0000,
            0xfd00_0020,
            0xf900_0062,
            0xd65f_03c0,
        ],
        // ASM: add x2, x0, #0 / ucvtf d0, w0 / str d0, [x1] / str x2, [x3] / ret
        &[
            0x9100_0002,
            0x1e63_0000,
            0xfd00_0020,
            0xf900_0062,
            0xd65f_03c0,
        ],
        // ASM: add x2, x0, #0 / scvtf s0, w0 / str d0, [x1] / str x2, [x3] / ret
        &[
            0x9100_0002,
            0x1e22_0000,
            0xfd00_0020,
            0xf900_0062,
            0xd65f_03c0,
        ],
        // ASM: add x2, x0, #0 / ucvtf s0, w0 / str s0, [x1] / str x2, [x3] / ret
        &[
            0x9100_0002,
            0x1e23_0000,
            0xbd00_0020,
            0xf900_0062,
            0xd65f_03c0,
        ],
        // ASM: add x2, x0, #0 / scvtf d0, w0, #4 / str d0, [x1] / str x2, [x3] / ret
        &[
            0x9100_0002,
            0x1e42_f000,
            0xfd00_0020,
            0xf900_0062,
            0xd65f_03c0,
        ],
        // ASM: add x2, x0, #0 / ucvtf s0, w0, #4 / str d0, [x1] / str x2, [x3] / ret
        &[
            0x9100_0002,
            0x1e03_f000,
            0xfd00_0020,
            0xf900_0062,
            0xd65f_03c0,
        ],
        // ASM: scvtf s0, w0 / fcvt d0, s0 / str s0, [x1] / ret
        &[0x1e22_0000, 0x1e22_c000, 0xbd00_0020, 0xd65f_03c0],
        // ASM: scvtf d0, x0 / fcvt s0, d0 / str d0, [x1] / ret
        &[0x9e62_0000, 0x1e62_4000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: fcvt d0, s0 / str s0, [x0] / ret
        &[0x1e22_c000, 0xbd00_0000, 0xd65f_03c0],
        // ASM: fcvt s0, d0 / str d0, [x0] / ret
        &[0x1e62_4000, 0xfd00_0000, 0xd65f_03c0],
        // ASM: fcvt d1, s0 / str s1, [x1] / ret
        &[0x1e22_c001, 0xbd00_0021, 0xd65f_03c0],
        // ASM: fcvt s1, d0 / str d1, [x1] / ret
        &[0x1e62_4001, 0xfd00_0021, 0xd65f_03c0],
        // ASM: fcvt d0, s0 / str s0, [x1] / str d0, [x2] / ret
        &[0x1e22_c000, 0xbd00_0020, 0xfd00_0040, 0xd65f_03c0],
        // ASM: fcvt s0, d0 / str d0, [x1] / str s0, [x2] / ret
        &[0x1e62_4000, 0xfd00_0020, 0xbd00_0040, 0xd65f_03c0],
        // ASM: fmov d0, x0 / fcvt s0, d0 / str d0, [x1] / ret
        &[0x9e67_0000, 0x1e62_4000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: fmov s0, w0 / fcvt d0, s0 / str s0, [x1] / ret
        &[0x1e27_0000, 0x1e22_c000, 0xbd00_0020, 0xd65f_03c0],
        // ASM: fmov s0, w0 / str d0, [x1] / ret
        &[0x1e27_0000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: fmov d0, x0 / fmov s1, s0 / str d1, [x1] / ret
        &[0x9e67_0000, 0x1e20_4001, 0xfd00_0021, 0xd65f_03c0],
        // ASM: fmov s0, w0 / fmov d1, d0 / str d1, [x1] / ret
        &[0x1e27_0000, 0x1e60_4001, 0xfd00_0021, 0xd65f_03c0],
        // ASM: fadd d0, d0, d0 / fmov s0, s0 / fcvt d0, s0 / str d0, [x1] / ret
        &[
            0x1e60_2800,
            0x1e20_4000,
            0x1e22_c000,
            0xfd00_0020,
            0xd65f_03c0,
        ],
        // ASM: fadd s0, s0, s0 / fmov d0, d0 / fcvt s0, d0 / str s0, [x1] / ret
        &[
            0x1e20_2800,
            0x1e60_4000,
            0x1e62_4000,
            0xbd00_0020,
            0xd65f_03c0,
        ],
        // ASM: fneg d0, d0 / fmov x1, d0 / fmov d1, x1 / str d1, [x1] / ret
        &[
            0x1e61_4000,
            0x9e66_0001,
            0x9e67_0021,
            0xfd00_0021,
            0xd65f_03c0,
        ],
        // ASM: fabs d0, d0 / fmov x1, d0 / fmov d1, x1 / str d1, [x1] / ret
        &[
            0x1e60_c000,
            0x9e66_0001,
            0x9e67_0021,
            0xfd00_0021,
            0xd65f_03c0,
        ],
        // ASM: fneg s0, s0 / fmov w1, s0 / fmov s1, w1 / str d1, [x1] / ret
        &[
            0x1e21_4000,
            0x1e26_0001,
            0x1e27_0021,
            0xfd00_0021,
            0xd65f_03c0,
        ],
        // ASM: scvtf d0, x0 / fneg d0, d0 / fmov x1, d0 / fmov d1, x1 / str d1, [x2] / ret
        &[
            0x9e62_0000,
            0x1e61_4000,
            0x9e66_0001,
            0x9e67_0021,
            0xfd00_0041,
            0xd65f_03c0,
        ],
        // ASM: scvtf d0, x0 / fneg d0, d0 / fmov x1, d0 / fmov d1, x1 / fcvt s1, d1 / str s1, [x2] / ret
        &[
            0x9e62_0000,
            0x1e61_4000,
            0x9e66_0001,
            0x9e67_0021,
            0x1e62_4021,
            0xbd00_0041,
            0xd65f_03c0,
        ],
        // ASM: fneg s0, s0 / fcvt d0, s0 / str s0, [x0] / ret
        &[0x1e21_4000, 0x1e22_c000, 0xbd00_0000, 0xd65f_03c0],
        // ASM: fneg d0, d0 / fcvt s0, d0 / str d0, [x0] / ret
        &[0x1e61_4000, 0x1e62_4000, 0xfd00_0000, 0xd65f_03c0],
        // ASM: scvtf d0, x0 / fmov w0, s0 / str x0, [x1] / ret
        &[0x9e62_0000, 0x1e26_0000, 0xf900_0020, 0xd65f_03c0],
        // ASM: scvtf s0, w0 / fmov x0, d0 / str x0, [x1] / ret
        &[0x1e22_0000, 0x9e66_0000, 0xf900_0020, 0xd65f_03c0],
        // ASM: scvtf s0, x0 / fmov x1, d0 / str x1, [x2] / ret
        &[0x9e22_0000, 0x9e66_0001, 0xf900_0041, 0xd65f_03c0],
        // ASM: ucvtf s0, x0 / fmov x1, d0 / str x1, [x2] / ret
        &[0x9e23_0000, 0x9e66_0001, 0xf900_0041, 0xd65f_03c0],
        // ASM: fsqrt s0, s0 / str d0, [x0] / ret
        &[0x1e21_c000, 0xfd00_0000, 0xd65f_03c0],
        // ASM: fsqrt d0, d0 / str s0, [x0] / ret
        &[0x1e61_c000, 0xbd00_0000, 0xd65f_03c0],
        // ASM: fsqrt s0, s1 / str d0, [x0] / ret
        &[0x1e21_c020, 0xfd00_0000, 0xd65f_03c0],
        // ASM: fsqrt d0, d1 / str s0, [x0] / ret
        &[0x1e61_c020, 0xbd00_0000, 0xd65f_03c0],
    ];
    for words in cases {
        agrees(words);
    }
    let immediates: &[&[u32]] = &[
        // ASM: fmov d0, #1.0 / str s0, [x0] / ret
        &[0x1e6e_1000, 0xbd00_0000, 0xd65f_03c0],
        // ASM: fmov d0, #1.0 / str s0, [x0] / str d0, [x1] / ret
        &[0x1e6e_1000, 0xbd00_0000, 0xfd00_0020, 0xd65f_03c0],
        // ASM: fmov s0, #-2.5 / fmov d1, d0 / str d1, [x0] / ret
        &[0x1e30_9000, 0x1e60_4001, 0xfd00_0001, 0xd65f_03c0],
    ];
    for words in immediates {
        agrees_immediate(words);
    }
}

/// The forms the first structure routine leaves out are C too.
///
/// Three- and four-register interleaves, the replicate loads of one and
/// two registers, the `bit` and `bif` selects, the rounding and unsigned
/// narrowing shifts, a three-register table, and the integer and
/// fixed-point conversions from a `v` register, scalar and vector.
#[test]
fn arm64_interleaves_narrowings_and_conversions_are_c() {
    let words: [u32; 28] = [
        0x4c40_4400, // ASM: ld3 {v0.8h, v1.8h, v2.8h}, [x0]
        0x0d40_c823, // ASM: ld1r {v3.2s}, [x1]
        0x0d60_c424, // ASM: ld2r {v4.4h, v5.4h}, [x1]
        0x4c40_0850, // ASM: ld4 {v16.4s, v17.4s, v18.4s, v19.4s}, [x2]
        0x6ea2_1c20, // ASM: bit v0.16b, v1.16b, v2.16b
        0x6ef1_1e01, // ASM: bif v1.16b, v16.16b, v17.16b
        0x0f0e_8c06, // ASM: rshrn v6.8b, v0.8h, #2
        0x0f1a_9e07, // ASM: sqrshrn v7.4h, v16.4s, #6
        0x6f14_9627, // ASM: uqshrn2 v7.8h, v17.4s, #12
        0x4e13_4214, // ASM: tbl v20.16b, {v16.16b, v17.16b, v18.16b}, v19.16b
        0x4c00_0870, // ASM: st4 {v16.4s, v17.4s, v18.4s, v19.4s}, [x3]
        0x4c00_7094, // ASM: st1 {v20.16b}, [x4]
        0xad00_8480, // ASM: stp q0, q1, [x4, #16]
        0x6d03_1083, // ASM: stp d3, d4, [x4, #48]
        0x6d04_1c86, // ASM: stp d6, d7, [x4, #64]
        0x3d80_1487, // ASM: str q7, [x4, #80]
        0x1e27_00b5, // ASM: fmov s21, w5
        0x5e21_dab6, // ASM: scvtf s22, s21
        0x5f3c_e6b7, // ASM: scvtf s23, s21, #4
        0x9e67_00d8, // ASM: fmov d24, x6
        0x7e61_db19, // ASM: ucvtf d25, d24
        0x6f79_e71a, // ASM: ucvtf v26.2d, v24.2d, #7
        0x3d80_189a, // ASM: str q26, [x4, #96]
        0x1e37_2ac0, // ASM: fadd s0, s22, s23
        0x1e20_8800, // ASM: fnmul s0, s0, s0
        0x1e22_c000, // ASM: fcvt d0, s0
        0x1e79_2800, // ASM: fadd d0, d0, d25
        0xd65f_03c0, // ASM: ret
    ];
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE_STRUCT2, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm64, 0, Some(BASE_STRUCT2), vec![text]);
    p.symbols = vec![local("interleaves", BASE_STRUCT2)];
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), BASE_STRUCT2).expect("decompiles");
    assert!(!out.contains("/* asm"), "{out}");
    for name in [
        "__ld3",
        "__ld4",
        "__st4",
        "__bit",
        "__bif",
        "__rshrn",
        "__sqrshrn",
        "__uqshrn",
        "__tbl",
        "__ucvtf",
        "__dup",
    ] {
        assert!(!out.contains(name), "{name}: {out}");
    }
    for spelled in [
        "__builtin_shufflevector(__builtin_shufflevector(",
        "(u32x2){0} + (uint32_t)",
        " >> 1) & 1)",
        "(i32x4){0} + -32768",
        " < 48 ? (",
        "/ 128.0",
        "(float)",
        "(double)",
        "-(",
    ] {
        assert!(out.contains(spelled), "{spelled}: {out}");
    }
}

/// A sign extension of a field C has no type for shifts it up and back.
///
/// `sbfx x0, x0, #0, #1` makes bit 0 all ones or all zeros. The next C
/// type, `int8_t`, would keep seven bits the field does not have.
#[test]
fn a_one_bit_sign_extension_is_no_byte_cast() {
    // ASM: sbfx x0, x0, #0, #1 / ret
    let (p, a, text) = decompiled_words(&[0x9340_0000, 0xd65f_03c0]);
    assert!(
        text.contains("((int64_t)((uint64_t)a1 << 63) >> 63)"),
        "{text}"
    );
    assert!(!text.contains("int8_t"), "{text}");
    let entry = p.entry.expect("entry");
    for seed in 1..=8 {
        let v = verify(&p, &a, &[entry], seed);
        assert!(
            v.mismatches.is_empty(),
            "seed {seed}: {text}\n{}",
            verify_tsv(&v)
        );
    }
}
