//! Floats at their width: stores, reads, moves and immediates.

use super::*;

/// A float stored at another width keeps the bits, not a rounding cast.
///
/// `str s0` after `scvtf d0` writes the low 32 bits of the double's
/// encoding. `str d0` after `scvtf s0` writes that single's encoding in
/// the low half and zeros above it. Either one as a float store would
/// round, and a mask written against the parameter would be dropped when
/// the parameter is narrowed. A scalar add of two bare registers carries
/// the width the instruction computed it at, so the same cut applies to
/// the sum and a store at that width stays the float. A wider add reads
/// a narrower float as that encoding, zero-extended. The cast of the mask
/// keeps the bits, and `fneg` flips the double's sign bit.
#[test]
fn a_float_stored_at_another_width_keeps_its_bits() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: scvtf d0, x0 / str s0, [x1] / ret
        (
            &[0x9e62_0000, 0xbd00_0020, 0xd65f_03c0],
            &["*(uint32_t*)", "((double)a1)", "0xffffffff"],
            &["*(float*)", "(float)"],
        ),
        // ASM: ucvtf d0, x0 / str s0, [x1] / ret
        (
            &[0x9e63_0000, 0xbd00_0020, 0xd65f_03c0],
            &["*(uint32_t*)", "((double)a1)", "0xffffffff"],
            &["*(float*)", "(int64_t)", "(float)"],
        ),
        // ASM: scvtf s0, w0 / str d0, [x1] / ret
        (
            &[0x1e22_0000, 0xfd00_0020, 0xd65f_03c0],
            &["*(uint64_t*)", "((float)a1)", "0xffffffff", "int32_t a1"],
            &["*(double*)", "(double)", "uint32_t a1"],
        ),
        // ASM: fadd d0, d0, d1 / str s0, [x0] / ret
        (
            &[0x1e61_2800, 0xbd00_0000, 0xd65f_03c0],
            &[
                "*(uint32_t*)",
                "((double)(a2 + a3))",
                "0xffffffff",
                "double a2",
                "double a3",
            ],
            &["*(float*)", "*(double*)", "float a"],
        ),
        // ASM: fadd s0, s0, s1 / str d0, [x0] / ret
        (
            &[0x1e21_2800, 0xfd00_0000, 0xd65f_03c0],
            &[
                "*(uint64_t*)",
                "((float)(a2 + a3))",
                "0xffffffff",
                "float a2",
                "float a3",
            ],
            &["*(double*)", "*(float*)", "double a"],
        ),
        // ASM: fadd d0, d0, d1 / str d0, [x0] / ret
        (
            &[0x1e61_2800, 0xfd00_0000, 0xd65f_03c0],
            &["*(double*)", "double a2", "double a3"],
            &["*(float*)", "*(uint32_t*)", "0xffffffff", "float a"],
        ),
        // ASM: fadd s0, s0, s1 / str s0, [x0] / ret
        (
            &[0x1e21_2800, 0xbd00_0000, 0xd65f_03c0],
            &["*(float*)", "float a2", "float a3"],
            &["*(double*)", "*(uint64_t*)", "0xffffffff", "double a"],
        ),
        // ASM: scvtf s0, w1 / fadd d0, d0, d1 / str d0, [x0] / ret
        // The single's encoding, zero-extended, is what the double add
        // reads. A cast of that single would be the number.
        (
            &[0x1e22_0020, 0x1e61_2800, 0xfd00_0000, 0xd65f_03c0],
            &[
                "*(double*)",
                "(double)(((float)a2) & 0xffffffff)",
                "+ a4",
                "int32_t a2",
                "double a4",
            ],
            &["*(float*)", "*(uint64_t*)", "(double)((float)", "(int32_t)"],
        ),
        // ASM: scvtf s0, w0 / fneg d0, d0 / str d0, [x1] / ret
        // The sign bit flipped is the double's, bit 63 of the zero-extended
        // single, not the negation of the number.
        (
            &[0x1e22_0000, 0x1e61_4000, 0xfd00_0020, 0xd65f_03c0],
            &["*(double*)", "& 0xffffffff", "(float)", "int32_t a1", "-"],
            &["*(float*)", "(double)((float)"],
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

/// A float operation reads its register at the instruction's width.
///
/// `scvtf s0, w0` leaves a single. `fcmp d0, #0.0` compares the
/// zero-extended bits, not the number: the sign bit of that single is bit
/// 31, so a negative number is not a negative double. `fcsel d` of the
/// same register stores those bits as a double. `fcvtzs x0, d0` rounds
/// that double. A single instruction the other way reads the low 32 bits
/// of a double, not a rounded narrowing. `fcsel` of that single and a bare
/// register stores a double select, and a narrower store keeps its low
/// bits. `fcvt` is not this read.
#[test]
fn a_wider_float_read_keeps_the_encoding() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: scvtf s0, w0 / fcmp d0, #0.0 / b.mi / mov w0, #2 / ret / mov w0, #1 / ret
        (
            &[
                0x1e22_0000,
                0x1e60_2008,
                0x5400_0064,
                0x5280_0040,
                0xd65f_03c0,
                0x5280_0020,
                0xd65f_03c0,
            ],
            &["(double)(((float)a1) & 0xffffffff)", "0.0", "int32_t a1"],
            &["(float)a1 <", "(float)a1 >", "(float)a1 =="],
        ),
        // ASM: scvtf s0, w0 / fcmp d0, d0 / fcsel d0, d0, d0, eq / str d0, [x1] / ret
        (
            &[
                0x1e22_0000,
                0x1e60_2000,
                0x1e60_0c00,
                0xfd00_0020,
                0xd65f_03c0,
            ],
            &[
                "*(double*)",
                "(double)(((float)a1) & 0xffffffff)",
                "int32_t a1",
            ],
            &["*(uint64_t*)", "*(float*)"],
        ),
        // ASM: scvtf d0, x0 / fcmp s0, #0.0 / b.mi / mov w0, #2 / ret / mov w0, #1 / ret
        // The low 32 bits of the double are the single compared, not a
        // rounded narrowing of the number.
        (
            &[
                0x9e62_0000,
                0x1e20_2008,
                0x5400_0064,
                0x5280_0040,
                0xd65f_03c0,
                0x5280_0020,
                0xd65f_03c0,
            ],
            &["(float)(((double)a1) & 0xffffffff)", "0.0", "(int64_t a1"],
            &["(double)(int64_t)a1 <", "(double)(int64_t)a1 >"],
        ),
        // ASM: scvtf d0, x0 / fadd s0, s0, s0 / str d0, [x1] / ret
        (
            &[0x9e62_0000, 0x1e20_2800, 0xfd00_0020, 0xd65f_03c0],
            &[
                "*(uint64_t*)",
                "(float)(((double)a1) & 0xffffffff)",
                "(int64_t a1",
            ],
            &["*(double*)", "*(float*)"],
        ),
        // ASM: scvtf s0, w0 / fcmp d0, d1 / fcsel d0, d0, d1, mi / str d0, [x1] / ret
        // The other arm is a bare register. It is a double, not an integer
        // converted by the store. The compare is register against register:
        // a `#0.0` compare is outside the replay's checked subset.
        (
            &[
                0x1e22_0000,
                0x1e61_2000,
                0x1e61_4c00,
                0xfd00_0020,
                0xd65f_03c0,
            ],
            &[
                "*(double*)",
                "(double)(((float)a1) & 0xffffffff)",
                "double a",
                "int32_t a1",
            ],
            &["*(float*)", "*(uint64_t*)", "float a4"],
        ),
        // ASM: scvtf s0, w0 / fcmp d0, d1 / fcsel d0, d0, d1, mi / str s0, [x1] / ret
        // A narrower store keeps the low bits of that select.
        (
            &[
                0x1e22_0000,
                0x1e61_2000,
                0x1e61_4c00,
                0xbd00_0020,
                0xd65f_03c0,
            ],
            &[
                "*(uint32_t*)",
                "(double)(((float)",
                "double a",
                "0xffffffff",
            ],
            &["*(float*)", "*(double*)", "float a4"],
        ),
        // ASM: scvtf s0, w0 / fcvtzs x0, d0 / ret
        (
            &[0x1e22_0000, 0x9e78_0000, 0xd65f_03c0],
            &[
                "fcvtzs64(",
                "(double)(((float)a1) & 0xffffffff)",
                "int32_t a1",
            ],
            &["fcvtzs64((float)", "__fcvtzs"],
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

/// A float forced out by a store keeps its width for the next store.
///
/// `ldr s` then `str s` writes the single out, because the load reads
/// memory and the store has to keep that read. The register is only its
/// name afterwards. `str d` still stores that single's encoding in the
/// low half and zeros above it, not a double conversion of the name.
#[test]
fn a_float_written_out_by_a_store_keeps_its_width() {
    // ASM: ldr s0, [x0] / str s0, [x1] / str d0, [x2] / ret
    let (p, a, text) = decompiled_words(&[0xbd40_0000, 0xbd00_0020, 0xfd00_0040, 0xd65f_03c0]);
    assert!(text.contains("*(uint64_t*)"), "{text}");
    assert!(text.contains("0xffffffff"), "{text}");
    assert!(text.contains("*(float*)"), "{text}");
    assert!(!text.contains("*(double*)"), "{text}");
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

/// `fneg` and `fabs` of a register's name flip or clear the lane's sign
/// bit. The name is not a float, so a negation of it would be a different
/// value, and a float store of the bits would convert them.
#[test]
fn a_float_sign_of_a_name_keeps_the_bits() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: fneg d0, d0 / str d0, [x0] / ret
        (
            &[0x1e61_4000, 0xfd00_0000, 0xd65f_03c0],
            &["*(uint64_t*)", "0x8000000000000000", "double a"],
            &["*(double*)", "/* asm"],
        ),
        // ASM: fabs d0, d0 / str d0, [x0] / ret
        (
            &[0x1e60_c000, 0xfd00_0000, 0xd65f_03c0],
            &["*(uint64_t*)", "0x7fffffffffffffff", "double a"],
            &["*(double*)", "/* asm"],
        ),
        // ASM: fneg s0, s0 / str s0, [x0] / ret
        (
            &[0x1e21_4000, 0xbd00_0000, 0xd65f_03c0],
            &["*(uint32_t*)", "0x80000000", "float a"],
            &["*(float*)", "/* asm"],
        ),
        // ASM: fneg s0, s0 / str d0, [x0] / ret
        // The single's sign flip, zero-extended. A double store would
        // convert the integer.
        (
            &[0x1e21_4000, 0xfd00_0000, 0xd65f_03c0],
            &["*(uint64_t*)", "0x80000000"],
            &["*(double*)", "*(float*)", "/* asm"],
        ),
        // ASM: fabs s0, s0 / str s0, [x0] / ret
        // The low-half cut folds the sign clear into `& 0x7fffffff`.
        (
            &[0x1e20_c000, 0xbd00_0000, 0xd65f_03c0],
            &["*(uint32_t*)", "0x7fffffff", "float a"],
            &["*(float*)", "/* asm"],
        ),
        // ASM: fabs s0, s0 / str d0, [x0] / ret
        (
            &[0x1e20_c000, 0xfd00_0000, 0xd65f_03c0],
            &["*(uint64_t*)", "0x7fffffff"],
            &["*(double*)", "*(float*)", "/* asm"],
        ),
        // ASM: scvtf s0, w0 / fcmp d0, d1 / fcsel d0, d0, d1, mi / fneg d0, d0 / str d0, [x1] / ret
        // The select stays inline, a double, so `fneg` negates it: the
        // same flip of bit 63.
        (
            &[
                0x1e22_0000,
                0x1e61_2000,
                0x1e61_4c00,
                0x1e61_4000,
                0xfd00_0020,
                0xd65f_03c0,
            ],
            &["-(", "(double)(((float)"],
            &["*(float*)", "/* asm"],
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

/// A 32-bit `fcsel` clears the bits above the lane.
///
/// One arm that is already a float does not keep the other arm's high
/// bits. The machine writes zeros there. The select is moved into a
/// general register so the replay compares all 64 bits.
#[test]
fn a_narrow_select_of_a_mixed_pair_keeps_the_low_bits() {
    // ASM: fmov d0, x0 / scvtf s1, w1 / fcmp s1, s1 / fcsel s2, s0, s1, eq
    //      / fmov x0, d2 / ret
    let words = &[
        0x9e67_0000,
        0x1e22_0021,
        0x1e21_2020,
        0x1e21_0c02,
        0x9e66_0040,
        0xd65f_03c0,
    ];
    let (p, a, text) = decompiled_words(words);
    assert!(text.contains("0xffffffff"), "{text}");
    assert!(!text.contains("/* asm"), "{text}");
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
        let r = replay_function(&p, &a, entry, seed);
        assert!(r.checked > 0, "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// A scalar `fmov` immediate stored at its width is that float.
///
/// The bits are the encoding. Storing them as an integer assigned to a
/// float converts the integer, which is a different number. The immediate
/// is an operand the replay does not enter, so the machine check is the
/// block verify; a replay that does enter must not disagree.
#[test]
fn a_float_immediate_stores_its_value() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: fmov d0, #1.0 / str d0, [x0] / ret
        (
            &[0x1e6e_1000, 0xfd00_0000, 0xd65f_03c0],
            &["*(double*)", "1.0"],
            &["*(uint64_t*)", "0x3ff0000000000000", "/* asm"],
        ),
        // ASM: fmov s0, #-2.5 / str s0, [x0] / ret
        (
            &[0x1e30_9000, 0xbd00_0000, 0xd65f_03c0],
            &["*(float*)", "-2.5f"],
            &["*(uint32_t*)", "/* asm"],
        ),
        // ASM: fmov s0, #-2.5 / str d0, [x0] / ret
        // The immediate is an operand the replay does not enter.
        (
            &[0x1e30_9000, 0xfd00_0000, 0xd65f_03c0],
            &["*(uint64_t*)", "-2.5f"],
            &["*(double*)", "/* asm"],
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
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `fmov` of a general register into a lane stores those bits.
///
/// The move does not convert. A float store of the integer would.
#[test]
fn a_float_bit_move_stores_the_bits() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: fmov d0, x0 / str d0, [x1] / ret
        (
            &[0x9e67_0000, 0xfd00_0020, 0xd65f_03c0],
            &["*(uint64_t*)"],
            &["*(double*)", "/* asm"],
        ),
        // ASM: fmov s0, w0 / str s0, [x1] / ret
        (
            &[0x1e27_0000, 0xbd00_0020, 0xd65f_03c0],
            &["*(uint32_t*)"],
            &["*(float*)", "/* asm"],
        ),
        // ASM: fmov d0, x0 / str s0, [x1] / ret
        (
            &[0x9e67_0000, 0xbd00_0020, 0xd65f_03c0],
            &["*(uint32_t*)"],
            &["*(float*)", "*(double*)", "/* asm"],
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

/// `fmov` of a float into a general register, or into a narrower lane,
/// stores the lane's bits.
///
/// A cast of the number is a different value.
/// An immediate stored at another width is that immediate's encoding,
/// not a float of the store's width.
#[test]
fn a_float_moved_into_an_integer_keeps_the_bits() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: scvtf d0, x0 / fmov x0, d0 / str x0, [x1] / ret
        (
            &[0x9e62_0000, 0x9e66_0000, 0xf900_0020, 0xd65f_03c0],
            &["*(uint64_t*)", "|"],
            &["*(double*)", "/* asm"],
        ),
        // ASM: scvtf s0, w0 / fmov w0, s0 / str w0, [x1] / ret
        (
            &[0x1e22_0000, 0x1e26_0000, 0xb900_0020, 0xd65f_03c0],
            &["*(uint32_t*)"],
            &["*(float*)", "/* asm"],
        ),
        // ASM: scvtf d0, x0 / fmov s1, s0 / str d1, [x1] / ret
        (
            &[0x9e62_0000, 0x1e20_4001, 0xfd00_0021, 0xd65f_03c0],
            &["*(uint64_t*)", "0xffffffff"],
            &["*(double*)", "/* asm"],
        ),
        // ASM: fmov d0, x0 / fadd d0, d0, d0 / ucvtf d1, x0 / str d1, [x1] / ret
        // The add reads the moved bits as a float. It must not declare the
        // integer parameter as that float: the conversion is still of the
        // integer.
        (
            &[
                0x9e67_0000,
                0x1e60_2800,
                0x9e63_0001,
                0xfd00_0021,
                0xd65f_03c0,
            ],
            &["*(double*)", "(double)a1"],
            &["double a1", "/* asm"],
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

/// A store of an incoming lane is that float. An integer store of the
/// name would convert the number.
#[test]
fn a_float_parameter_stored_keeps_its_value() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: str d0, [x0] / ret
        (
            &[0xfd00_0000, 0xd65f_03c0],
            &["*(double*)", "double a"],
            &["*(uint64_t*)", "float a", "/* asm"],
        ),
        // ASM: str s0, [x0] / ret
        (
            &[0xbd00_0000, 0xd65f_03c0],
            &["*(float*)", "float a"],
            &["*(uint32_t*)", "double a", "/* asm"],
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

/// A later narrower read of a double parameter uses the low bits of that
/// double, not a rounded narrowing of the number.
#[test]
fn a_float_reread_at_the_other_width_keeps_the_bits() {
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: fadd d2, d0, d0 / fadd s0, s0, s0 / str s0, [x1] / ret
        (
            &[0x1e60_2802, 0x1e20_2800, 0xbd00_0020, 0xd65f_03c0],
            &["*(float*)", "double a", "0xffffffff"],
            &["*(uint32_t*)", "float a2", "/* asm"],
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

/// A function nothing calls returns the float its body leaves in `v0`.
///
/// `fmadd s0, s1, s2, s0; ret` is `lerp`'s arm64 body: no caller says what
/// it reads, so the write nearest the `ret` answers, and it is a `float`.
/// Storing that value instead, `fadd s0, s0, s1; str s0, [x0]; ret`, is a
/// `void` function's work.
#[test]
fn an_uncalled_arm64_function_returns_the_float_it_computes() {
    // ASM: fmadd s0, s1, s2, s0
    let fmadd = 0x1f02_0020;
    // ASM: ret
    let ret = 0xd65f_03c0;
    let (_, _, text) = decompiled_words(&[fmadd, ret]);
    assert!(text.contains("// signature: float "), "{text}");
    assert!(!text.contains("/* asm"), "{text}");
    // ASM: fadd s0, s0, s1
    let fadd = 0x1e21_2800;
    // ASM: str s0, [x0]
    let store = 0xbd00_0000;
    let (_, _, text) = decompiled_words(&[fadd, store, ret]);
    assert!(text.contains("// signature: void "), "{text}");
}

/// A slot every access but an integer zero reads and writes as a single
/// is a `float`, whatever touched it first.
#[test]
fn a_float_slot_first_zeroed_as_an_integer_is_a_float() {
    let (_, _, text) = decompiled_words(&HORNERF_O0);
    let sum = text
        .lines()
        .find_map(|l| {
            let (lhs, rhs) = l.trim().split_once(" = ")?;
            rhs.contains(" * ").then_some(lhs)
        })
        .expect("the accumulator's update");
    assert!(
        text.lines()
            .any(|l| l.starts_with("float ") && l.contains(sum)),
        "{text}"
    );
}
