//! Scalar and packed work in vector registers: lanes and widths kept bit for bit.

use super::*;

/// A byte swap's lane widens unsigned, for the register the swap works on
/// zeroes the bits above it where a signed operand's conversion would
/// sign-extend them.
///
/// `mov rax,rcx; shr rax,20h; mov edx,ecx; bswap edx; add rax,rdx; ret` of
/// a low half above `0x7fffffff` once answered its sign-extension.
///
/// # Panics
///
/// When the text swaps a signed lane.
#[test]
fn a_byte_swap_widens_its_lane_unsigned() {
    let code = [
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x48, 0xc1, 0xe8, 0x20, // ASM: shr rax,0x20
        0x8b, 0xd1, // ASM: mov edx,ecx
        0x0f, 0xca, // ASM: bswap edx
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("bswap((uint32_t)"), "{text}");
}

/// Vector work left in xmm0 is no float result: `paddd xmm0,xmm1; ret`,
/// which nothing calls, adds packed integers.
#[test]
fn vector_work_left_in_xmm0_is_no_float_result() {
    let code = [
        0x66, 0x0f, 0xfe, 0xc1, // ASM: paddd xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
    assert_eq!(f, Some(None));
}

/// A test of `movd`'s low lane says nothing of the bits above it.
///
/// `movd eax,xmm0; cmp eax,0; jne; psrlq xmm0,32; movd eax,xmm0; mov
/// [ecx],eax` stores the upper half on the path where the lower one is
/// zero; taking
/// `eax == 0` there for `xmm0 == 0` made that half zero too.
#[test]
fn a_zero_low_lane_leaves_the_upper_lanes_unknown() {
    let code = [
        0x66, 0x0f, 0x7e, 0xc0, // ASM: movd eax,xmm0
        0x83, 0xf8, 0x00, // ASM: cmp eax,0
        0x75, 0x0c, // ASM: jne 0x401015
        0x66, 0x0f, 0x73, 0xd0, 0x20, // ASM: psrlq xmm0,32
        0x66, 0x0f, 0x7e, 0xc0, // ASM: movd eax,xmm0
        0x89, 0x01, // ASM: mov [ecx],eax
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program32(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401_000).unwrap_or_default();
    assert!(!text.contains("psrlq(0,"), "{text}");
    replays_clean(&p, &a, &[0x401_000]);
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

/// `FL3`: integer-to-float and float-to-double conversions render as casts, a
/// double store is typed, and a packed shuffle is C's vector shuffle over
/// the lanes it reads, the double's bits among them.
#[test]
fn float_conversions_and_vector_intrinsics() {
    let out = dc(0x1340);
    assert!(
        out.contains("*(double*)a2 = (double)((float)a1 * (float)a1);"),
        "{out}"
    );
    assert!(
        out.contains(
            "*(uint128_t*)(a2 + 0x10) = (uint128_t)__builtin_shufflevector((f32x4)xmm1, (f32x4)(f64x2){"
        ) && out.contains("}, 3, 2, 5, 4);"),
        "{out}"
    );
    assert!(!out.contains("shufps("), "{out}");
    assert!(
        !out.contains("/*"),
        "unmodeled instruction survived:\n{out}"
    );
}

/// `FL`, `FL2` and `FR`: scalar-float blocks are checked against the
/// binary, not counted as float/vector.
///
/// `FL3`, whose `shufps` is a packed operation the text writes as a vector
/// shuffle, still is. `FL`'s block is proved over every state, its float
/// operations the same on both sides; `FL2`'s whole-lane masks are only
/// tested.
#[test]
fn scalar_float_blocks_are_checked_not_counted() {
    use borer_engine::analysis::decompile::checked_header;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let header = |entry: u64| checked_header(&p, &a, &o, entry).unwrap_or_default();
    assert_eq!(
        header(0x1300),
        "// checked vs binary: statements as emitted, 1/1 blocks: 1 proved; unchecked: C spelling, later text passes",
        "FL"
    );
    assert_eq!(
        header(0x1320),
        "// checked vs binary: statements as emitted, 1/1 blocks: 0 proved, 1 tested x3 states; unchecked: C spelling, later text passes",
        "FL2"
    );
    assert_eq!(
        header(0x13f0),
        "// checked vs binary: statements as emitted, 2/2 blocks: 1 proved, 1 tested x3 states; unchecked: C spelling, later text passes",
        "FR"
    );
    let fl3 = header(0x1340);
    assert!(
        fl3.contains("0/1 blocks") && fl3.contains("1 float/vector"),
        "FL3's packed shuffle stays out: {fl3}"
    );
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
/// merge, although its shared `ret` block writes nothing. The argument is
/// the 32-bit register `test ecx, ecx` reads.
#[test]
fn byte_returns_are_the_low_lane() {
    let rl = dc(0x16c0);
    assert!(
        rl.contains("// signature: uint8_t sub_16c0(uint32_t a1)"),
        "{rl}"
    );
    assert!(rl.contains("1;") && rl.contains("0;"), "{rl}");
    assert!(
        !rl.contains("0xffffffffffffff00") && !rl.contains("-256"),
        "{rl}"
    );
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

/// `ptest` lifts to the test of the lanes the code reads, and a lane
/// extracted into memory to the extract; neither is left as asm.
#[test]
fn packed_tests_and_extracts_lift() {
    let code: &[u8] = &[
        0xf3, 0x0f, 0x6f, 0x01, 0xf3, 0x0f, 0x6f, 0x0a, 0x66, 0x0f, 0x38, 0x17, 0xc1, 0x0f, 0x94,
        0xc0, 0x66, 0x41, 0x0f, 0x3a, 0x16, 0x00, 0x01, 0x0f, 0xb6, 0xc0, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("/*"), "{text}");
    assert!(text.contains("== 0"), "{text}");
    assert!(text.contains("pextrd("), "{text}");
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

/// A scalar `double` operation reads a `movss` load as that load's bits,
/// with zeros above the lane, not as the number converted to a double.
///
/// `cvtss2sd` still converts the number. `cvtsd2ss` of a `movss` load
/// converts the zero-extended bits, and of a `movsd` load converts the
/// double. `addss` of a double uses the low 32 bits as a float. A single
/// add that kept those zeros is the same encoding when a double add reads
/// it. `cvttsd2si` of a `movss` load truncates that encoding, and
/// `cvttss2si` of a double truncates its low 32 bits. `comisd` compares
/// the encoding, not the number. Each case is the bytes, a text that
/// must appear and a text that must not.
#[test]
fn a_scalar_float_read_at_another_width_keeps_the_bits() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &str, &str)] = &[
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf2, 0x41, 0x0f, 0x10, 0x08, // ASM: movsd xmm1,[r8]
                0xf2, 0x0f, 0x58, 0xc1, // ASM: addsd xmm0,xmm1
                0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
                0xc3, // ASM: ret
            ],
            "*(double*)a2 = (double)((*(float*)a1) & 0xffffffff) + *(double*)a3;",
            "(double)*(float*)a1",
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf3, 0x41, 0x0f, 0x11, 0x00, // ASM: movss [r8],xmm0
                0xc3, // ASM: ret
            ],
            "*(float*)a3 = (float)((*(double*)a1) & 0xffffffff) + *(float*)a2;",
            "(float)*(double*)a1 +",
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
                0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
                0xc3, // ASM: ret
            ],
            "*(double*)a2 = (double)*(float*)a1;",
            "0xffffffff",
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
                0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
                0xc3, // ASM: ret
            ],
            "*(double*)a2 = (double)(float)((*(double*)a1) & 0xffffffff);",
            "(double)*(double*)",
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
                0xf3, 0x0f, 0x11, 0x02, // ASM: movss [rdx],xmm0
                0xc3, // ASM: ret
            ],
            "*(float*)a2 = (float)*(double*)a1;",
            "0xffffffff",
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
                0xf3, 0x0f, 0x11, 0x02, // ASM: movss [rdx],xmm0
                0xc3, // ASM: ret
            ],
            "*(float*)a2 = (float)(double)((*(float*)a1) & 0xffffffff);",
            "(float)*(float*)a1;",
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf2, 0x0f, 0x51, 0xc0, // ASM: sqrtsd xmm0,xmm0
                0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
                0xc3, // ASM: ret
            ],
            "*(double*)a2 = sqrt((double)((*(float*)a1) & 0xffffffff));",
            "sqrt((double)*(float*)",
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf2, 0x41, 0x0f, 0x10, 0x08, // ASM: movsd xmm1,[r8]
                0xf2, 0x0f, 0x58, 0xc1, // ASM: addsd xmm0,xmm1
                0xf2, 0x41, 0x0f, 0x11, 0x01, // ASM: movsd [r9],xmm0
                0xc3, // ASM: ret
            ],
            "*(double*)a4 = (double)((*(float*)a1 + *(float*)a2) & 0xffffffff) + *(double*)a3;",
            "(double)(*(float*)a1 + *(float*)a2)",
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf2, 0x48, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si rax,xmm0
                0xc3, // ASM: ret
            ],
            "return (int64_t)(double)((*(float*)a1) & 0xffffffff);",
            "return (int64_t)*(float*)a1;",
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x2c, 0xc0, // ASM: cvttss2si eax,xmm0
                0xc3, // ASM: ret
            ],
            "return (int32_t)(float)((*(double*)a1) & 0xffffffff);",
            "return (int32_t)*(double*)a1;",
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0x66, 0x0f, 0x2f, 0x02, // ASM: comisd xmm0,[rdx]
                0x77, 0x03, // ASM: ja taken
                0x31, 0xc0, // ASM: xor eax,eax
                0xc3, // ASM: ret
                0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
                0xc3, // ASM: ret
            ],
            "if ((double)((*(float*)a1) & 0xffffffff) > *(double*)a2)",
            "if (*(float*)a1 >",
        ),
    ];
    for (code, want, absent) in cases {
        let p = program64(code);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(
            text.contains(want),
            "missing `{want}`\nforbidden `{absent}`\n{text}"
        );
        assert!(!text.contains(absent), "still has `{absent}`\n{text}");
        let a = Analysis::compute(&p);
        for seed in 1..=8 {
            let v = verify(&p, &a, &[0x1_4000_1000], seed);
            assert!(
                v.checked > 0 && v.mismatches.is_empty(),
                "{text}\nseed {seed}: {}",
                verify_tsv(&v)
            );
            let r = replay_function(&p, &a, 0x1_4000_1000, seed);
            assert!(
                r.checked > 0 && r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// A `movss` or `movsd` into memory copies the lane's bytes.
///
/// A single stored as a double is the zero-extended encoding, not the
/// number widened. A double stored as a single is its low 32 bits, not a
/// rounded float. The same width stays that float. `addss` of a double
/// keeps bits 63:32, so a later `movsd` is those bits beside the new lane.
/// `addsd` after that single adds those bits. It does not convert the
/// integer they form. `sqrtss` keeps the same half. `cvttsd2si` truncates
/// that double, not the integer the bits happen to be. `cvtsd2ss` of a
/// double rounds the number and still keeps bits 63:32. A three-operand
/// `vmovss` takes its low lane from the second source and bits 63:32 from
/// the first.
#[test]
fn a_scalar_float_store_at_another_width_keeps_the_bits() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &[&str], &[&str])] = &[
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint64_t*)", "*(float*)", "0xffffffff"],
            &["*(double*)"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x11, 0x02, // ASM: movss [rdx],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint32_t*)", "*(double*)", "0xffffffff"],
            &["*(float*)"],
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint64_t*)", "0xffffffff", "+"],
            &["*(double*)"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint64_t*)", "0xffffffff00000000", "+"],
            &["*(double*)a3 ="],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf2, 0x41, 0x0f, 0x10, 0x08, // ASM: movsd xmm1,[r8]
                0xf2, 0x0f, 0x58, 0xc1, // ASM: addsd xmm0,xmm1
                0xf2, 0x41, 0x0f, 0x11, 0x01, // ASM: movsd [r9],xmm0
                0xc3, // ASM: ret
            ],
            &["*(double*)", "0xffffffff00000000", "+"],
            &["*(uint64_t*)", "/* asm"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x51, 0x02, // ASM: sqrtss xmm0,[rdx]
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint64_t*)", "0xffffffff00000000", "sqrt"],
            &["*(double*)a3 =", "/* asm"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf2, 0x48, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si rax,xmm0
                0xc3, // ASM: ret
            ],
            &["return (int64_t)", "0xffffffff00000000"],
            &["/* asm"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
                0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint64_t*)", "0xffffffff00000000", "(float)"],
            &["*(double*)a2 =", "/* asm"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x09, // ASM: movsd xmm1,[rcx]
                0xf3, 0x0f, 0x10, 0x12, // ASM: movss xmm2,[rdx]
                0xc5, 0xf2, 0x10, 0xc2, // ASM: vmovss xmm0,xmm1,xmm2
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["*(uint64_t*)", "0xffffffff00000000", "*(float*)"],
            &["/* asm", "movss("],
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf3, 0x0f, 0x11, 0x02, // ASM: movss [rdx],xmm0
                0xc3, // ASM: ret
            ],
            &["*(float*)a2 = *(float*)a1;"],
            &["0xffffffff", "*(uint32_t*)", "*(double*)"],
        ),
    ];
    for (code, has, has_not) in cases {
        let p = program64(code);
        let text = decompiled(&p, 0x1_4000_1000);
        for part in *has {
            assert!(text.contains(part), "missing `{part}`\n{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "still has `{part}`\n{text}");
        }
        let a = Analysis::compute(&p);
        for seed in 1..=8 {
            let v = verify(&p, &a, &[0x1_4000_1000], seed);
            assert!(
                v.checked > 0 && v.mismatches.is_empty() && v.unreadable == 0,
                "{text}\nseed {seed}: {}",
                verify_tsv(&v)
            );
            let r = replay_function(&p, &a, 0x1_4000_1000, seed);
            assert!(
                r.checked > 0 && r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// A 32-bit sign or magnitude mask is not a negation with zeros above it
/// unless the later lanes really are zero.
///
/// A broadcast sign mask sets bit 63 of a `movss` load. The 32-bit store
/// is still the negation; the 64-bit store keeps that bit, and `addsd`
/// adds those bits. A scalar single (`addss`, `minss`, `sqrtss`, `vaddss`,
/// `cvtsd2ss`) replaces the low lane and leaves bit 63, so a later `movsd`
/// still has it and a later `movss` is only the new lane. `addss` after a
/// broadcast magnitude mask on a double keeps that double's high half. A
/// scalar sign mask on the same load leaves the zeros.
/// On a double, a scalar sign mask flips only bit 31, a broadcast one
/// flips bit 31 and bit 63, a scalar magnitude mask clears the high half,
/// and a broadcast one clears both lanes' signs. The mask constant sits
/// at `0x140002000`. `xorps` is at `0x140001004` and ends at
/// `0x14000100b`, so the displacement is `0xff5`.
#[test]
fn a_broadcast_sign_mask_keeps_the_high_bit() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let xorps = [0x0f, 0x57, 0x05, 0xf5, 0x0f, 0x00, 0x00];
    let andps = [0x0f, 0x54, 0x05, 0xf5, 0x0f, 0x00, 0x00];
    let mut broadcast_sign = vec![0xf3, 0x0f, 0x10, 0x01];
    broadcast_sign.extend_from_slice(&xorps);
    broadcast_sign.extend_from_slice(&[0xf2, 0x0f, 0x11, 0x02, 0xc3]);
    let scalar_sign = broadcast_sign.clone();
    let mut broadcast_add = vec![0xf3, 0x0f, 0x10, 0x01];
    broadcast_add.extend_from_slice(&xorps);
    broadcast_add.extend_from_slice(&[
        0xf2, 0x41, 0x0f, 0x10, 0x08, // ASM: movsd xmm1,[r8]
        0xf2, 0x0f, 0x58, 0xc1, // ASM: addsd xmm0,xmm1
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
        0xc3,
    ]);
    let mut double_broadcast = vec![0xf2, 0x0f, 0x10, 0x01];
    double_broadcast.extend_from_slice(&xorps);
    double_broadcast.extend_from_slice(&[
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
        0xf3, 0x41, 0x0f, 0x11, 0x00, // ASM: movss [r8],xmm0
        0xc3,
    ]);
    let double_scalar_sign = double_broadcast.clone();
    let mut double_scalar_mag = vec![0xf2, 0x0f, 0x10, 0x01];
    double_scalar_mag.extend_from_slice(&andps);
    double_scalar_mag.extend_from_slice(&[0xf2, 0x0f, 0x11, 0x02, 0xc3]);
    let double_broadcast_mag = double_scalar_mag.clone();
    let mut addss_wide = vec![0xf3, 0x0f, 0x10, 0x01];
    addss_wide.extend_from_slice(&xorps);
    addss_wide.extend_from_slice(&[
        0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xc3,
    ]);
    let mut addss_narrow = vec![0xf3, 0x0f, 0x10, 0x01];
    addss_narrow.extend_from_slice(&xorps);
    addss_narrow.extend_from_slice(&[
        0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
        0xf3, 0x41, 0x0f, 0x11, 0x00, // ASM: movss [r8],xmm0
        0xc3,
    ]);
    let mut addss_both = vec![0xf3, 0x0f, 0x10, 0x01];
    addss_both.extend_from_slice(&xorps);
    addss_both.extend_from_slice(&[
        0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xf3, 0x41, 0x0f, 0x11, 0x01, // ASM: movss [r9],xmm0
        0xc3,
    ]);
    let mut minss_wide = vec![0xf3, 0x0f, 0x10, 0x01];
    minss_wide.extend_from_slice(&xorps);
    minss_wide.extend_from_slice(&[
        0xf3, 0x0f, 0x5d, 0x02, // ASM: minss xmm0,[rdx]
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xc3,
    ]);
    let mut sqrtss_wide = vec![0xf3, 0x0f, 0x10, 0x01];
    sqrtss_wide.extend_from_slice(&xorps);
    sqrtss_wide.extend_from_slice(&[
        0xf3, 0x0f, 0x51, 0x02, // ASM: sqrtss xmm0,[rdx]
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xc3,
    ]);
    let mut vaddss_wide = vec![0xf3, 0x0f, 0x10, 0x01];
    vaddss_wide.extend_from_slice(&xorps);
    vaddss_wide.extend_from_slice(&[
        0xc5, 0xfa, 0x58, 0x02, // ASM: vaddss xmm0,xmm0,[rdx]
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xc3,
    ]);
    let mut mag_addss = vec![0xf2, 0x0f, 0x10, 0x01];
    mag_addss.extend_from_slice(&andps);
    mag_addss.extend_from_slice(&[
        0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xc3,
    ]);
    let mut cvtsd_wide = vec![0xf3, 0x0f, 0x10, 0x01];
    cvtsd_wide.extend_from_slice(&xorps);
    cvtsd_wide.extend_from_slice(&[
        0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
        0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
        0xc3,
    ]);

    let sign = 0x8000_0000u32.to_le_bytes();
    let mag = 0x7fff_ffffu32.to_le_bytes();
    let zero = [0u8; 4];
    let mut bsign = Vec::new();
    let mut ssign = Vec::new();
    let mut bmag = Vec::new();
    let mut smag = Vec::new();
    for _ in 0..4 {
        bsign.extend_from_slice(&sign);
        bmag.extend_from_slice(&mag);
    }
    ssign.extend_from_slice(&sign);
    smag.extend_from_slice(&mag);
    for _ in 0..3 {
        ssign.extend_from_slice(&zero);
        smag.extend_from_slice(&zero);
    }

    /// The code, the data, the spellings the text must hold and those it
    /// must not.
    type Case<'a> = (&'a [u8], &'a [u8], &'a [&'a str], &'a [&'a str]);
    let cases: &[Case<'_>] = &[
        (
            &broadcast_sign,
            &bsign,
            &["*(uint64_t*)", "-", "0xffffffff", "0x8000000000000000"],
            &["*(double*)", "/* asm"],
        ),
        (
            &scalar_sign,
            &ssign,
            &["*(uint64_t*)", "-", "0xffffffff"],
            &["*(double*)", "0x8000000000000000", "/* asm"],
        ),
        (
            &broadcast_add,
            &bsign,
            &["*(double*)", "-", "0xffffffff", "0x8000000000000000", "+"],
            &["(double)-", "/* asm"],
        ),
        (
            &double_broadcast,
            &bsign,
            &["*(uint64_t*)", "0x8000000080000000", "*(uint32_t*)"],
            &["*(double*)a2 =", "*(float*)", "/* asm"],
        ),
        (
            &double_scalar_sign,
            &ssign,
            &["*(uint64_t*)", "0x80000000", "*(uint32_t*)"],
            &[
                "0x8000000080000000",
                "0x8000000000000000",
                "*(float*)",
                "/* asm",
            ],
        ),
        (
            &double_scalar_mag,
            &smag,
            &["*(uint64_t*)", "0x7fffffff"],
            &["0x7fffffff7fffffff", "*(double*)a2 =", "/* asm"],
        ),
        (
            &double_broadcast_mag,
            &bmag,
            &["*(uint64_t*)", "0x7fffffff7fffffff"],
            &["*(double*)a2 =", "/* asm"],
        ),
        (
            &addss_wide,
            &bsign,
            &["*(uint64_t*)", "0x8000000000000000", "+"],
            &["*(double*)", "/* asm"],
        ),
        (
            &addss_narrow,
            &bsign,
            &["*(float*)", "+"],
            &["0x8000000000000000", "*(uint64_t*)", "/* asm"],
        ),
        (
            &addss_both,
            &bsign,
            &["*(uint64_t*)", "0x8000000000000000", "*(float*)", "+"],
            &["/* asm"],
        ),
        (
            &minss_wide,
            &bsign,
            &["*(uint64_t*)", "0x8000000000000000", "?"],
            &["*(double*)", "fmin", "/* asm"],
        ),
        (
            &sqrtss_wide,
            &bsign,
            &["*(uint64_t*)", "0x8000000000000000", "sqrt"],
            &["*(double*)", "/* asm"],
        ),
        (
            &vaddss_wide,
            &bsign,
            &["*(uint64_t*)", "0x8000000000000000", "+"],
            &["*(double*)", "/* asm"],
        ),
        (
            &cvtsd_wide,
            &bsign,
            &["*(uint64_t*)", "0x8000000000000000"],
            &["/* asm"],
        ),
        (
            &mag_addss,
            &bmag,
            &["*(uint64_t*)", "+"],
            &["*(double*)a3 =", "/* asm"],
        ),
    ];
    for (code, data, has, has_not) in cases {
        let p = program64_with_data(code, data);
        let text = decompiled(&p, 0x1_4000_1000);
        for part in *has {
            assert!(text.contains(part), "missing `{part}`\n{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "still has `{part}`\n{text}");
        }
        let a = Analysis::compute(&p);
        for seed in 1..=8 {
            let v = verify(&p, &a, &[0x1_4000_1000], seed);
            assert!(
                v.checked > 0 && v.mismatches.is_empty() && v.unreadable == 0,
                "{text}\nseed {seed}: {}",
                verify_tsv(&v)
            );
            let r = replay_function(&p, &a, 0x1_4000_1000, seed);
            assert!(
                r.checked > 0 && r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// `minss` and `maxss` keep the second operand when the compare does not hold.
///
/// C's `fmin` returns the number and prefers `-0`. The machine returns the
/// second operand: `+0` with `-0` is `-0`, and `1.0` with a NaN is that NaN.
/// The constants sit at `0x140002000`. Each load ends eight bytes later, so
/// the displacements are `0xff8` and `0xff4`.
#[test]
fn a_scalar_min_or_max_keeps_the_operand_the_compare_misses() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let load = |op: u8| -> Vec<u8> {
        let mut code = vec![
            0xf3, 0x0f, 0x10, 0x05, 0xf8, 0x0f, 0x00, 0x00, // ASM: movss xmm0,[rip+0xff8]
        ];
        code.extend_from_slice(&[
            0xf3, 0x0f, op, 0x05, 0xf4, 0x0f, 0x00, 0x00, // ASM: minss/maxss xmm0,[rip+0xff4]
            0xf3, 0x0f, 0x11, 0x01, // ASM: movss [rcx],xmm0
            0xc3, // ASM: ret
        ]);
        code
    };
    let nan = 0x7fc0_0000u32;
    let pos = 0u32;
    let neg = 0x8000_0000u32;
    let one = 0x3f80_0000u32;
    /// The opcode, the two operands' bits, the spellings the text must
    /// hold and those it must not.
    type Case<'a> = (u8, u32, u32, &'a [&'a str], &'a [&'a str]);
    let cases: &[Case<'_>] = &[
        (0x5d, pos, neg, &["?", "<"], &["fmin"]),
        (0x5d, neg, pos, &["?", "<"], &["fmin"]),
        (0x5d, one, nan, &["?", "<", "NAN"], &["fmin"]),
        (0x5d, nan, one, &["?", "<"], &["fmin"]),
        (0x5f, pos, neg, &["?", ">"], &["fmax"]),
        (0x5f, one, nan, &["?", ">", "NAN"], &["fmax"]),
    ];
    for (op, left, right, has, has_not) in cases {
        let mut data = Vec::new();
        data.extend_from_slice(&left.to_le_bytes());
        data.extend_from_slice(&right.to_le_bytes());
        let p = program64_with_data(&load(*op), &data);
        let text = decompiled(&p, 0x1_4000_1000);
        for part in *has {
            assert!(text.contains(part), "missing `{part}`\n{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "still has `{part}`\n{text}");
        }
        assert!(!text.contains("/* asm"), "{text}");
        let a = Analysis::compute(&p);
        let v = verify(&p, &a, &[0x1_4000_1000], 1);
        assert!(
            v.checked > 0 && v.mismatches.is_empty() && v.unreadable == 0,
            "{text}\n{}",
            verify_tsv(&v)
        );
        let r = replay_function(&p, &a, 0x1_4000_1000, 1);
        assert!(
            r.checked > 0 && r.wrong().is_empty(),
            "{text}\n{}",
            replay_tsv(&r)
        );
    }
}

/// `minss xmm0, xmm1; ret` returns the `minss` result, not nothing.
///
/// Nobody in the image reads xmm0, and the function writes no integer
/// result, so the value it leaves is what a caller outside the image gets.
/// The compare keeps the second operand when it does not hold: `+0` with
/// `-0` is `-0`, and `1.0` with a NaN is that NaN. C's `fmin` returns the
/// number and prefers `-0`, so the text is the ternary, not `fmin`. The
/// register form also keeps the bits above the lane of the first operand,
/// which `minss` does not clear.
#[test]
fn a_minss_return_keeps_the_operand_the_compare_misses() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let code = &[
        0xf3, 0x0f, 0x5d, 0xc1, // ASM: minss xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("// signature: float "), "{text}");
    assert!(text.contains("a1 < a2 ? a1 : a2"), "{text}");
    assert!(text.contains("return "), "{text}");
    assert!(!text.contains("return;"), "{text}");
    assert!(!text.contains("fmin"), "{text}");
    assert!(!text.contains("/* asm"), "{text}");
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x1_4000_1000).map(|f| f.ret_float),
        Some(Some(32))
    );
    for seed in 1..=8 {
        let v = verify(&p, &a, &[0x1_4000_1000], seed);
        assert!(
            v.checked > 0 && v.mismatches.is_empty(),
            "{text}\nseed {seed}: {}",
            verify_tsv(&v)
        );
        let r = replay_function(&p, &a, 0x1_4000_1000, seed);
        assert!(
            r.checked > 0 && r.wrong().is_empty(),
            "{text}\nseed {seed}: {}",
            replay_tsv(&r)
        );
    }

    let load = |op: u8| -> Vec<u8> {
        let mut code = vec![
            0xf3, 0x0f, 0x10, 0x05, 0xf8, 0x0f, 0x00, 0x00, // ASM: movss xmm0,[rip+0xff8]
            0xf3, 0x0f, 0x10, 0x0d, 0xf4, 0x0f, 0x00, 0x00, // ASM: movss xmm1,[rip+0xff4]
        ];
        code.extend_from_slice(&[
            0xf3, 0x0f, op, 0xc1, // ASM: minss/maxss xmm0,xmm1
            0xc3, // ASM: ret
        ]);
        code
    };
    let nan = 0x7fc0_0000u32;
    let pos = 0u32;
    let neg = 0x8000_0000u32;
    let one = 0x3f80_0000u32;
    type Case<'a> = (u8, u32, u32, &'a [&'a str], &'a [&'a str]);
    let cases: &[Case<'_>] = &[
        (0x5d, pos, neg, &["?", "<"], &["fmin"]),
        (0x5d, neg, pos, &["?", "<"], &["fmin"]),
        (0x5d, one, nan, &["?", "<", "NAN"], &["fmin"]),
        (0x5d, nan, one, &["?", "<"], &["fmin"]),
        (0x5f, pos, neg, &["?", ">"], &["fmax"]),
        (0x5f, one, nan, &["?", ">", "NAN"], &["fmax"]),
    ];
    for (op, left, right, has, has_not) in cases {
        let mut data = Vec::new();
        data.extend_from_slice(&left.to_le_bytes());
        data.extend_from_slice(&right.to_le_bytes());
        let p = program64_with_data(&load(*op), &data);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(text.contains("// signature: float "), "{text}");
        assert!(!text.contains("return;"), "{text}");
        for part in *has {
            assert!(text.contains(part), "missing `{part}`\n{text}");
        }
        for part in *has_not {
            assert!(!text.contains(part), "still has `{part}`\n{text}");
        }
        assert!(!text.contains("/* asm"), "{text}");
        let a = Analysis::compute(&p);
        let v = verify(&p, &a, &[0x1_4000_1000], 1);
        assert!(
            v.checked > 0 && v.mismatches.is_empty() && v.unreadable == 0,
            "{text}\n{}",
            verify_tsv(&v)
        );
        let r = replay_function(&p, &a, 0x1_4000_1000, 1);
        assert!(
            r.checked > 0 && r.wrong().is_empty(),
            "{text}\n{}",
            replay_tsv(&r)
        );
    }
}

/// The low bit of `cmpeqss` is C's `==`, not the instruction.
///
/// `cmpeqss xmm0, xmm1; movd eax, xmm0; and eax, 1; ret` leaves 1 when the
/// ordered equality holds. A NaN compares false, so the bit is 0, and the
/// two zeros compare true. `comiss` then `je` is the other test, equal or
/// unordered, and this one is not that.
#[test]
fn a_cmpeqss_low_bit_is_ordered_equality() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let code = &[
        0xf3, 0x0f, 0xc2, 0xc1, 0x00, // ASM: cmpeqss xmm0,xmm1
        0x66, 0x0f, 0x7e, 0xc0, // ASM: movd eax,xmm0
        0x83, 0xe0, 0x01, // ASM: and eax,1
        0xc3, // ASM: ret
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("a1 == a2"), "{text}");
    assert!(!text.contains("cmpss"), "{text}");
    assert!(!text.contains("isunordered"), "{text}");
    assert!(!text.contains("/* asm"), "{text}");
    let a = Analysis::compute(&p);
    for seed in 1..=8 {
        let v = verify(&p, &a, &[0x1_4000_1000], seed);
        assert!(
            v.checked > 0 && v.mismatches.is_empty(),
            "{text}\nseed {seed}: {}",
            verify_tsv(&v)
        );
        let r = replay_function(&p, &a, 0x1_4000_1000, seed);
        assert!(
            r.checked > 0 && r.wrong().is_empty(),
            "{text}\nseed {seed}: {}",
            replay_tsv(&r)
        );
    }

    let load = || -> Vec<u8> {
        vec![
            0xf3, 0x0f, 0x10, 0x05, 0xf8, 0x0f, 0x00, 0x00, // ASM: movss xmm0,[rip+0xff8]
            0xf3, 0x0f, 0x10, 0x0d, 0xf4, 0x0f, 0x00, 0x00, // ASM: movss xmm1,[rip+0xff4]
            0xf3, 0x0f, 0xc2, 0xc1, 0x00, // ASM: cmpeqss xmm0,xmm1
            0x66, 0x0f, 0x7e, 0xc0, // ASM: movd eax,xmm0
            0x83, 0xe0, 0x01, // ASM: and eax,1
            0xc3, // ASM: ret
        ]
    };
    let nan = 0x7fc0_0000u32;
    let pos = 0u32;
    let neg = 0x8000_0000u32;
    let one = 0x3f80_0000u32;
    let two = 0x4000_0000u32;
    let cases: &[(u32, u32)] = &[
        (pos, neg),
        (neg, pos),
        (one, one),
        (one, two),
        (one, nan),
        (nan, one),
        (nan, nan),
    ];
    for (left, right) in cases {
        let mut data = Vec::new();
        data.extend_from_slice(&left.to_le_bytes());
        data.extend_from_slice(&right.to_le_bytes());
        let p = program64_with_data(&load(), &data);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(text.contains("=="), "{text}");
        assert!(!text.contains("cmpss"), "{text}");
        assert!(!text.contains("isunordered"), "{text}");
        assert!(!text.contains("/* asm"), "{text}");
        let a = Analysis::compute(&p);
        let v = verify(&p, &a, &[0x1_4000_1000], 1);
        assert!(
            v.checked > 0 && v.mismatches.is_empty() && v.unreadable == 0,
            "{text}\n{}",
            verify_tsv(&v)
        );
        let r = replay_function(&p, &a, 0x1_4000_1000, 1);
        assert!(
            r.checked > 0 && r.wrong().is_empty(),
            "{text}\n{}",
            replay_tsv(&r)
        );
    }
}

/// Packed integer work is C over vector types, and the 128-bit constant it
/// reads is declared with the value the image holds.
///
/// `movdqa xmm0,[rip+k]; paddd xmm0,[rcx]; pshufd xmm1,xmm0,0xee; paddd
/// xmm0,xmm1; movd eax,xmm0; ret` sums lanes, the tail of a vectorized
/// reduction. Each instruction once printed as a call to its mnemonic,
/// which no compiler knows, and the constant as an uninitialized local.
#[test]
fn packed_integer_work_is_c_over_vector_types() {
    let code = [
        0x66, 0x0f, 0x6f, 0x05, 0xf8, 0x0f, 0x00, 0x00, // ASM: movdqa xmm0,[rip+0xff8]
        0x66, 0x0f, 0xfe, 0x01, // ASM: paddd xmm0,[rcx]
        0x66, 0x0f, 0x70, 0xc8, 0xee, // ASM: pshufd xmm1,xmm0,0xee
        0x66, 0x0f, 0xfe, 0xc1, // ASM: paddd xmm0,xmm1
        0x66, 0x0f, 0x7e, 0xc0, // ASM: movd eax,xmm0
        0xc3, // ASM: ret
    ];
    let data: Vec<u8> = [1u32, 2, 3, 4]
        .iter()
        .flat_map(|v| v.to_le_bytes())
        .collect();
    let p = program64_with_data(&code, &data);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("typedef uint32_t u32x4 __attribute__((vector_size(16), aligned(1)));"),
        "{text}"
    );
    assert!(
        text.contains(
            "static const uint128_t g128_140002000 = (uint128_t)0x400000003 << 64 | 0x200000001; // @ 0x140002000"
        ),
        "{text}"
    );
    assert!(text.contains("*(u32x4*)a1"), "{text}");
    assert!(text.contains("__builtin_shufflevector("), "{text}");
    for name in ["paddd(", "pshufd("] {
        assert!(!text.contains(name), "{text}");
    }
    let a = Analysis::compute(&p);
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// Every SSE predicate of `cmpsd` is a lane the lifter computes, as the
/// emulator does, and none prints as a call to the mnemonic.
///
/// `cmpsd xmm0,xmm1,imm; movq rax,xmm0; ret` for the predicates past
/// `eq`, which once stayed `cmpsd(a1, a2, 4)`.
#[test]
fn every_cmpsd_predicate_agrees_with_the_emulator() {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    for predicate in 1..=7u8 {
        let code = [
            0xf2, 0x0f, 0xc2, 0xc1, predicate, // ASM: cmpsd xmm0,xmm1,predicate
            0x66, 0x48, 0x0f, 0x7e, 0xc0, // ASM: movq rax,xmm0
            0xc3, // ASM: ret
        ];
        let p = program64(&code);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(!text.contains("cmpsd("), "{predicate}: {text}");
        let a = Analysis::compute(&p);
        for seed in 1..=8 {
            let v = verify(&p, &a, &[0x1_4000_1000], seed);
            assert_eq!(v.checked, 1, "{predicate} seed {seed}: {}", verify_tsv(&v));
            assert!(
                v.mismatches.is_empty(),
                "{predicate} seed {seed}: {}",
                verify_tsv(&v)
            );
        }
    }
}

/// A scalar float instruction reading a packed result reads its lowest
/// lane as a float, not the 128-bit integer the register is held in.
///
/// `pshufd xmm1,xmm0,0x55; addss xmm0,xmm1; ret` adds lane 1 to lane 0.
/// The shuffle once printed as an integer in the float sum, which C
/// converts by value.
#[test]
fn a_scalar_float_reads_a_packed_lane_as_a_float() {
    let code = [
        0x66, 0x0f, 0x70, 0xc8, 0x55, // ASM: pshufd xmm1,xmm0,0x55
        0xf3, 0x0f, 0x58, 0xc1, // ASM: addss xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("(f32x4)__builtin_shufflevector("), "{text}");
    assert!(text.contains(")[0]"), "{text}");
    assert!(!text.contains("+ (uint128_t)"), "{text}");
}

/// A scalar float instruction reading a pseudo-call the text does not spell
/// as vector code reads it as it stands: a lane of it would dress a call no
/// compiler knows as vector code.
///
/// `movlps xmm0,[rcx]; addss xmm0,xmm1; ret`.
#[test]
fn a_lane_is_read_only_out_of_vector_code() {
    let code = [
        0x0f, 0x12, 0x01, // ASM: movlps xmm0,[rcx]
        0xf3, 0x0f, 0x58, 0xc1, // ASM: addss xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("movlps("), "{text}");
    assert!(!text.contains(")movlps("), "{text}");
}
