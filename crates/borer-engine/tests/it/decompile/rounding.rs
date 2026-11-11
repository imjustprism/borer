//! The x87 stack's loads and stores, and float to integer rounding.

use super::*;

/// A ladder whose arms share a tail and whose last test escapes to a
/// returning block is a `switch` with a `default`.
///
/// `LD3`'s ladder arms set `rdx` and jump to the shared tail while its last
/// test skips to a block an outer guard reaches too: the arms are the cases,
/// the skip's target the default, and the tail follows the switch once. The
/// tail's callee is a bare `ret` and `rcx` still holds the caller's own
/// `a1`, so the call passes nothing, and the `rdx` the arms set is a value
/// nothing reads.
#[test]
fn ladders_with_a_shared_tail_and_an_escape_structure_around_the_tail() {
    let out = dc(0x4090);
    assert_eq!(out.matches("goto ").count(), 0, "{out}");
    assert_eq!(out.matches("return 13;").count(), 1, "{out}");
    assert!(out.contains("switch (a1) {"), "{out}");
    assert!(out.contains("default: {"), "{out}");
    assert_eq!(out.matches("Base::vfunc_1()").count(), 1, "{out}");
    assert!(
        out.contains("case 1: {") && out.contains("case 3: {"),
        "{out}"
    );
}

/// A loop that goes round on `if (c) continue;` and runs a tail once it
/// stops is a `do`/`while` followed by that tail.
///
/// `test rcx,rcx; je J; mov rax,rcx; L: mov rcx,rax; mov rax,[rax]; test
/// rax,rax; jne L; mov [rcx],edx; J: xor eax,eax; ret` walks a list to its
/// last node and stores through it: the store moves after the loop.
#[test]
fn a_loop_going_round_on_continue_keeps_its_tail_after_it() {
    let code = [
        0x48, 0x85, 0xc9, 0x74, 0x10, 0x48, 0x89, 0xc8, 0x48, 0x89, 0xc1, 0x48, 0x8b, 0x00, 0x48,
        0x85, 0xc0, 0x75, 0xf5, 0x89, 0x11, 0x31, 0xc0, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("while (1)"), "{text}");
    assert!(!text.contains("continue;"), "{text}");
    assert!(
        text.contains("} while (var1 != 0);\n  *(uint32_t*)var2 = a2;"),
        "{text}"
    );
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

/// A `printf` whose format is a literal passes what the format asks for.
///
/// The `double` a `%f` reads goes in `xmm1`, so the call shows the value
/// and not the copy the variadic convention also leaves in `rdx`.
#[test]
fn a_printf_format_types_its_variable_arguments() {
    let code = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0xf2, 0x0f, 0x10, 0x0d, 0xfc, 0x0f, 0x00, 0x00, // ASM: movsd xmm1, [0x140002008]
        0x66, 0x48, 0x0f, 0x7e, 0xca, // ASM: movq rdx, xmm1
        0x48, 0x8d, 0x0d, 0xf8, 0x0f, 0x00, 0x00, // ASM: lea rcx, [0x140002010]
        0xff, 0x15, 0xe2, 0x0f, 0x00, 0x00, // ASM: call [0x140002000]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    let mut data = vec![0u8; 0x20];
    data[8..16].copy_from_slice(&1.5f64.to_le_bytes());
    data[0x10..0x14].copy_from_slice(b"%f\n\0");
    let p = program64_with_imports(&code, &data, &[(0x1_4000_2000, "msvcrt.dll!printf")]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains(r#"printf("%f\n", 1.5);"#), "{text}");
}

/// `fist` and `fistp` round to nearest, ties to even, then store that integer.
///
/// A truncating cast is a different value: `2.5` becomes `2`, and a word
/// that cannot hold the number is the indefinite integer, not the low bits
/// of a wider conversion. `fisttp` still truncates toward zero. Replay does
/// not enter an x87 block, so the machine check is the block verify; a
/// replay that does enter must not disagree.
#[test]
fn an_x87_integer_store_rounds_to_nearest_even() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &[&str], &[&str])] = &[
        // ASM: fld qword [rcx] / fistp dword [rdx] / ret
        (
            &[0xdd, 0x01, 0xdb, 0x1a, 0xc3],
            &["*(uint32_t*)", "rint("],
            &["/* asm"],
        ),
        // ASM: fld qword [rcx] / fistp word [rdx] / ret
        (
            &[0xdd, 0x01, 0xdf, 0x1a, 0xc3],
            &["*(uint16_t*)", "rint("],
            &["/* asm"],
        ),
        // ASM: fld qword [rcx] / fistp qword [rdx] / ret
        (
            &[0xdd, 0x01, 0xdf, 0x3a, 0xc3],
            &["*(uint64_t*)", "rint("],
            &["/* asm"],
        ),
        // ASM: fld qword [rcx] / fisttp dword [rdx] / ret
        (
            &[0xdd, 0x01, 0xdb, 0x0a, 0xc3],
            &["*(uint32_t*)"],
            &["rint(", "/* asm"],
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
                r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// `fild` sign-extends the integer it loads.
///
/// An unsigned cast of a dword `0xffffffff` is not `-1.0`. A single
/// multiplied on the x87 stack is widened first, so a double store keeps
/// the double product, not the single one.
#[test]
fn an_x87_integer_load_is_signed_and_a_single_widens() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &[&str], &[&str])] = &[
        // ASM: fild dword [rcx] / fstp qword [rdx] / ret
        (
            &[0xdb, 0x01, 0xdd, 0x1a, 0xc3],
            &["*(double*)", "(int32_t)"],
            &["/* asm"],
        ),
        // ASM: fild word [rcx] / fstp qword [rdx] / ret
        (
            &[0xdf, 0x01, 0xdd, 0x1a, 0xc3],
            &["*(double*)", "(int16_t)"],
            &["/* asm"],
        ),
        // ASM: fld dword [rcx] / fmul dword [rcx+4] / fstp qword [rdx] / ret
        (
            &[0xd9, 0x01, 0xd8, 0x49, 0x04, 0xdd, 0x1a, 0xc3],
            &["*(double*)", "(double)", "*"],
            &["/* asm"],
        ),
        // ASM: fld dword [rcx] / fmul dword [rcx+4] / fstp dword [rdx] / ret
        (
            &[0xd9, 0x01, 0xd8, 0x49, 0x04, 0xd9, 0x1a, 0xc3],
            &["*(float*)", "(double)", "*"],
            &["/* asm"],
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
                r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// An x87 operation on two writable singles widens each one first.
///
/// The product of `8388609.0f` with itself is not the single-precision
/// product widened afterwards, and neither is `1.0f / 3.0f`. A named
/// `float` global has no lane, so the listing used to multiply them as
/// `float`. Replay does not enter an x87 block; a replay that does enter
/// must not disagree.
#[test]
fn an_x87_writable_single_widens_before_the_operation() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};

    let image = |code: &[u8], data: &[u8]| {
        let mut bytes = vec![0u8; 0x2000];
        bytes[..code.len()].copy_from_slice(code);
        bytes[0x1000..0x1000 + data.len()].copy_from_slice(data);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0x1_4000_0000,
            Some(0x1_4000_1000),
            vec![
                Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
                Section::mapped(".data", 0x1_4000_2000, 0x1000, 0x1000, true, false),
            ],
        );
        p.format = BinaryFormat::Pe;
        p
    };
    let cases: &[(&[u8], [f32; 2], &str)] = &[
        // ASM: fld dword [rip+0xffa] / fmul dword [rip+0xff8] / fstp qword [rdx] / ret
        (
            &[
                0xd9, 0x05, 0xfa, 0x0f, 0x00, 0x00, 0xd8, 0x0d, 0xf8, 0x0f, 0x00, 0x00, 0xdd, 0x1a,
                0xc3,
            ],
            [8388609.0, 8388609.0],
            "*",
        ),
        // ASM: fld dword [rip+0xffa] / fdiv dword [rip+0xff8] / fstp qword [rdx] / ret
        (
            &[
                0xd9, 0x05, 0xfa, 0x0f, 0x00, 0x00, 0xd8, 0x35, 0xf8, 0x0f, 0x00, 0x00, 0xdd, 0x1a,
                0xc3,
            ],
            [1.0, 3.0],
            "/",
        ),
    ];
    for (code, values, op) in cases {
        let mut data = Vec::new();
        data.extend_from_slice(&values[0].to_le_bytes());
        data.extend_from_slice(&values[1].to_le_bytes());
        let p = image(code, &data);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(
            text.matches("(double)*(float*)").count() >= 2,
            "singles were not widened\n{text}"
        );
        assert!(text.contains(op), "{text}");
        assert!(
            !text.contains("g32_"),
            "multiplied named float globals\n{text}"
        );
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
                r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// `cvtss2si` and `cvtsd2si` round to nearest, ties to even, then cast.
///
/// That is a cast of `rint`. The truncating forms stay a cast with no
/// `rint`. A value the integer cannot hold is the indefinite integer.
#[test]
fn a_nearest_float_to_int_is_a_cast_of_rint() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &[&str], &[&str])] = &[
        // ASM: cvtss2si eax, dword [rcx] / ret
        (
            &[0xf3, 0x0f, 0x2d, 0x01, 0xc3],
            &["rint", "(int32_t)"],
            &["/* asm"],
        ),
        // ASM: cvtsd2si rax, qword [rcx] / ret
        (
            &[0xf2, 0x48, 0x0f, 0x2d, 0x01, 0xc3],
            &["rint", "(int64_t)"],
            &["/* asm"],
        ),
        // ASM: cvttss2si eax, dword [rcx] / ret
        (
            &[0xf3, 0x0f, 0x2c, 0x01, 0xc3],
            &["(int32_t)"],
            &["rint", "/* asm"],
        ),
        // ASM: cvttsd2si rax, qword [rcx] / ret
        (
            &[0xf2, 0x48, 0x0f, 0x2c, 0x01, 0xc3],
            &["(int64_t)"],
            &["rint", "/* asm"],
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

/// `cvtss2si` and `cvtsd2si` round to nearest, ties to even.
///
/// A truncating cast is a different integer: `1.5` becomes `2`, and
/// `2147483647.5` does not fit in 32 bits, so the result is the indefinite
/// integer rather than `2147483647`. The same rounding is what the VEX
/// forms do. A 32-bit destination zero-extends, so a later 64-bit store of
/// `-1.5` rounded is `0xfffffffe`, not a sign-extended word. `cvtsd2si` of
/// a `movss` load rounds the zero-extended bits, and `cvtss2si` of a
/// `cvtsd2ss` result rounds that single, not the double the bits form.
#[test]
fn a_nearest_float_to_int_rounds_ties_to_even() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let one_half = [0x00u8, 0x00, 0xc0, 0x3f];
    let neg_half = [0x00u8, 0x00, 0xc0, 0xbf];
    let dbl_half = [0x00u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf8, 0x3f];
    let past_i32 = [0x00u8, 0x00, 0xe0, 0xff, 0xff, 0xff, 0xdf, 0x41];
    let cases: &[(&[u8], &[u8], &[&str])] = &[
        (
            &[
                0xf3, 0x0f, 0x2d, 0x05, 0xf8, 0x0f, 0x00,
                0x00, // ASM: cvtss2si eax,[rip+0xff8]
                0xc3,
            ],
            &one_half,
            &["rint("],
        ),
        (
            &[
                0xf2, 0x0f, 0x2d, 0x05, 0xf8, 0x0f, 0x00,
                0x00, // ASM: cvtsd2si eax,[rip+0xff8]
                0xc3,
            ],
            &past_i32,
            &["rint("],
        ),
        (
            &[
                0xf2, 0x48, 0x0f, 0x2d, 0x05, 0xf7, 0x0f, 0x00,
                0x00, // ASM: cvtsd2si rax,[rip+0xff7]
                0xc3,
            ],
            &dbl_half,
            &["rint("],
        ),
        (
            &[
                0xf3, 0x48, 0x0f, 0x2d, 0x05, 0xf7, 0x0f, 0x00,
                0x00, // ASM: cvtss2si rax,[rip+0xff7]
                0xc3,
            ],
            &one_half,
            &["rint("],
        ),
        (
            &[
                0xc5, 0xfa, 0x2d, 0x05, 0xf8, 0x0f, 0x00,
                0x00, // ASM: vcvtss2si eax,[rip+0xff8]
                0xc3,
            ],
            &one_half,
            &["rint("],
        ),
        (
            &[
                0xc4, 0xe1, 0xfb, 0x2d, 0x05, 0xf7, 0x0f, 0x00,
                0x00, // ASM: vcvtsd2si rax,[rip+0xff7]
                0xc3,
            ],
            &dbl_half,
            &["rint("],
        ),
        (
            &[
                0xf3, 0x0f, 0x2d, 0x05, 0xf8, 0x0f, 0x00,
                0x00, // ASM: cvtss2si eax,[rip+0xff8]
                0x48, 0x89, 0x01, // ASM: mov [rcx],rax
                0xc3,
            ],
            &neg_half,
            &["rint(", "0xffffffff"],
        ),
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
                0xf2, 0x48, 0x0f, 0x2d, 0xc0, // ASM: cvtsd2si rax,xmm0
                0xc3,
            ],
            &[],
            &["rint(", "0xffffffff"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
                0xf3, 0x0f, 0x2d, 0xc0, // ASM: cvtss2si eax,xmm0
                0xc3,
            ],
            &[],
            &["rint(", "(float)"],
        ),
    ];
    for (code, data, parts) in cases {
        let p = if data.is_empty() {
            program64(code)
        } else {
            program64_with_data(code, data)
        };
        let text = decompiled(&p, 0x1_4000_1000);
        for part in *parts {
            assert!(text.contains(part), "missing `{part}`\n{text}");
        }
        assert!(!text.contains("/* asm"), "{text}");
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

/// A scalar move into a double keeps the bits above the new lane.
///
/// A register-to-register `movss` of a double is that merge, not the call
/// `movss(...)`, which hid bits 63:32. The same move of a value that may
/// still be 128 bits stays the call. `cvtss2si` rounds the low single.
#[test]
fn a_scalar_lane_move_and_round_keeps_the_bits() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &[&str], &[&str])] = &[
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x10, 0x0a, // ASM: movss xmm1,[rdx]
                0xf3, 0x0f, 0x10, 0xc1, // ASM: movss xmm0,xmm1
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["0xffffffff00000000", "*(float*)a2"],
            &["movss("],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x10, 0x0a, // ASM: movss xmm1,[rdx]
                0xc5, 0xfa, 0x10, 0xc1, // ASM: vmovss xmm0,xmm0,xmm1
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["0xffffffff00000000", "*(float*)a2"],
            &["vmovss("],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x09, // ASM: movsd xmm1,[rcx]
                0xf3, 0x0f, 0x10, 0x12, // ASM: movss xmm2,[rdx]
                0xc5, 0xf2, 0x10, 0xc2, // ASM: vmovss xmm0,xmm1,xmm2
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["0xffffffff00000000", "*(float*)a2"],
            &["vmovss("],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf2, 0x0f, 0x10, 0x0a, // ASM: movsd xmm1,[rdx]
                0xf2, 0x0f, 0x10, 0xc1, // ASM: movsd xmm0,xmm1
                0xf2, 0x41, 0x0f, 0x11, 0x00, // ASM: movsd [r8],xmm0
                0xc3, // ASM: ret
            ],
            &["*(double*)a3 = *(double*)a2;"],
            &["movsd("],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x2d, 0xc0, // ASM: cvtss2si eax,xmm0
                0xc3, // ASM: ret
            ],
            &["(int32_t)rint((float)((*(double*)a1) & 0xffffffff))"],
            &["cvtss2si(", "0xffffffff00000000"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xf3, 0x0f, 0x58, 0x02, // ASM: addss xmm0,[rdx]
                0xf3, 0x0f, 0x2d, 0xc0, // ASM: cvtss2si eax,xmm0
                0xc3, // ASM: ret
            ],
            &["rint(", "*(float*)a2"],
            &["cvtss2si(", "0xffffffff00000000"],
        ),
        (
            &[
                0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
                0xc5, 0xfa, 0x2d, 0xc0, // ASM: vcvtss2si eax,xmm0
                0xc3, // ASM: ret
            ],
            &["(int32_t)rint((float)((*(double*)a1) & 0xffffffff))"],
            &["vcvtss2si(", "cvtss2si("],
        ),
    ];
    for (code, want, absent) in cases {
        let p = program64(code);
        let text = decompiled(&p, 0x1_4000_1000);
        for needle in *want {
            assert!(text.contains(needle), "missing `{needle}`\n{text}");
        }
        for needle in *absent {
            assert!(!text.contains(needle), "still has `{needle}`\n{text}");
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
