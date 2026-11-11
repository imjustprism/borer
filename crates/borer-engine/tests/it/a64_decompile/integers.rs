//! Integer routines, atomics, system registers and vector lanes.

use super::*;

/// arm64 code decompiles under the arm64 procedure call standard.
///
/// Parameters are in `x0` and up, a call passes what its callee takes and
/// assigns `x0`, a tail call returns what its callee hands back, and a
/// function whose callers drop `x0` returns nothing.
#[test]
fn arm64_functions_decompile_with_their_arguments_and_results() {
    let p = image();
    assert!(p.refuses(Feature::Decompile).is_none());
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = |off: u64| decompile(&p, &a, &o, BASE + off).expect("decompiles");
    let f = text(0);
    assert!(
        f.contains("// signature: uint64_t f(uint64_t a1, uint64_t a2)"),
        "{f}"
    );
    assert!(f.contains("g(a1 + 1, a2)"), "{f}");
    assert!(f.contains("+ 2;"), "{f}");
    let g = text(0x20);
    assert!(g.contains("return a1 + a2;"), "{g}");
    let h = text(0x28);
    assert!(h.contains("// signature: void h(uint32_t *a1)"), "{h}");
    assert!(
        h.contains("*a1 = 0;") || h.contains("*(uint32_t*)a1 = 0;"),
        "{h}"
    );
    assert!(!h.contains("return a1"), "{h}");
    let k = text(0x30);
    assert!(k.contains("h(a1);"), "{k}");
    assert!(k.contains("return 5;"), "{k}");
    let m = text(0x48);
    assert!(m.contains("return g(a1, 3);"), "{m}");
    assert!(m.contains("return 1;"), "{m}");
}

/// The text of every routine agrees with the arm64 machine on every state
/// the check tries, and the check compares blocks of each.
#[test]
fn arm64_text_agrees_with_the_machine() {
    let p = image();
    let a = Analysis::compute(&p);
    for off in [0, 0x20, 0x28, 0x30, 0x48] {
        let r = replay_function(&p, &a, BASE + off, 1);
        assert!(r.checked > 0, "+{off:#x}: {}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "+{off:#x}: {}", replay_tsv(&r));
    }
}

/// Switches, pair stores and register tests decompile as the machine runs
/// them.
///
/// A `br` through a jump table the analysis resolved is a `switch` on the
/// index the table is loaded at, each case its arm; a pair store whose
/// first half writes out the address register stores its second half
/// beside it; a `cbnz` tests the value its block's load left, though no
/// successor reads the register; and every routine's text agrees with the
/// arm64 machine.
#[test]
fn arm64_switches_pair_stores_and_register_tests_decompile() {
    let p = image2();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = |off: u64| decompile(&p, &a, &o, BASE2 + off).expect("decompiles");
    let sw = text(0);
    assert!(sw.contains("switch (a1"), "{sw}");
    assert!(sw.contains("case 1:"), "{sw}");
    assert!(sw.contains("return 20;"), "{sw}");
    let pair = text(0x40);
    assert!(pair.contains("(var1 + 4) = a3"), "{pair}");
    let scan = text(0x50);
    assert!(scan.contains("} while (*(uint8_t*)var1 != 0);"), "{scan}");
    for off in [0, 0x40, 0x50] {
        let r = replay_function(&p, &a, BASE2 + off, 1);
        assert!(r.checked > 0, "+{off:#x}: {}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "+{off:#x}: {}", replay_tsv(&r));
    }
}

/// arm64's division idioms read as the operators they compute.
///
/// The high word of `smull`'s whole product is the quotient's magic
/// multiply, the dividend added back for a magic stored negative, and the
/// sign added after the shift makes the quotient; the dividend less the
/// quotient times the divisor, by a constant or a register, is the
/// remainder; a `tbz` of the sign bit is the sign. Every text agrees with
/// the arm64 machine.
#[test]
fn arm64_division_idioms_read_as_their_operators() {
    let code: Vec<u8> = ROUTINES4.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE4, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm64, 0, Some(BASE4), vec![text]);
    p.symbols = vec![
        local("rem", BASE4),
        local("vrem", BASE4 + 0x24),
        local("sign", BASE4 + 0x30),
    ];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let rem = decompile(&p, &a, &o, BASE4).expect("decompiles");
    assert!(rem.contains("% 127"), "{rem}");
    assert!(!rem.contains("smulhi"), "{rem}");
    let vrem = decompile(&p, &a, &o, BASE4 + 0x24).expect("decompiles");
    assert!(vrem.contains(" % "), "{vrem}");
    let sign = decompile(&p, &a, &o, BASE4 + 0x30).expect("decompiles");
    assert!(sign.contains(" >= 0") || sign.contains(" < 0"), "{sign}");
    assert!(!sign.contains("0x8000000000000000"), "{sign}");
    for off in [0, 0x24, 0x30] {
        let r = replay_function(&p, &a, BASE4 + off, 1);
        assert!(r.checked > 0, "+{off:#x}: {}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "+{off:#x}: {}", replay_tsv(&r));
    }
}

/// A stack canary whose guard is a global leaves the arm64 text, and the
/// statements it left still agree with the machine.
#[test]
fn an_arm64_stack_canary_folds_out_of_the_text() {
    let mut bytes: Vec<u8> = ROUTINES5.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(bytes.len()).expect("a small image");
    bytes.extend_from_slice(&0x5a5a_5a5a_1234_5678u64.to_le_bytes());
    let text = Section::mapped(".text", BASE5, 0, len, false, true);
    let data = Section::mapped(".data", BASE5 + 0x1000, len, 8, true, false);
    let mut p = Program::raw(bytes, Arch::Arm64, 0, Some(BASE5), vec![text, data]);
    p.symbols = vec![local("f", BASE5), local("__stack_chk_fail", BASE5 + 0x40)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let f = decompile(&p, &a, &o, BASE5).expect("decompiles");
    assert!(f.contains("// folded: stack canary"), "{f}");
    assert!(!f.contains("__stack_chk_fail("), "{f}");
    assert!(f.contains("return a1 + 1;"), "{f}");
    let r = replay_function(&p, &a, BASE5, 1);
    assert!(r.checked > 0, "{}", replay_tsv(&r));
    assert!(r.wrong().is_empty(), "{}", replay_tsv(&r));
}

/// A `w` write leaves no mask where every reader takes 32 bits, and a whole
/// read of the register is cut to the 32 bits the machine kept.
///
/// The `x` register a `w` write sets holds the value uncut until a 64-bit
/// read needs its upper half zero, as the x86 lifter's 32-bit writes do;
/// a compare, a return and another `w` operation read the low half only.
#[test]
fn arm64_w_writes_mask_only_where_a_whole_read_needs_it() {
    let code: Vec<u8> = ROUTINES3.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE3, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm64, 0, Some(BASE3), vec![text]);
    p.symbols = vec![local("wsum", BASE3), local("widx", BASE3 + 0x1c)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let wsum = decompile(&p, &a, &o, BASE3).expect("decompiles");
    assert!(!wsum.contains("0xffffffff"), "{wsum}");
    let widx = decompile(&p, &a, &o, BASE3 + 0x1c).expect("decompiles");
    assert!(
        widx.contains("0xffffffff") || widx.contains("(uint32_t)"),
        "{widx}"
    );
    for off in [0, 0x1c] {
        let r = replay_function(&p, &a, BASE3 + off, 1);
        assert!(r.checked > 0, "+{off:#x}: {}", replay_tsv(&r));
        assert!(r.disagreements.is_empty(), "+{off:#x}: {}", replay_tsv(&r));
    }
}

/// An exclusive store is the store and a status of zero, not an `/* asm */`
/// line.
///
/// The words are the `MNEMONICS` encodings of `stxr`, `stlxrh` and `stxp`,
/// and the emulate case `exclusive`. Nothing reads that status, so the
/// listing drops it. `msub`, the `MNEMONICS` word that reads `w3`, returns
/// `-(a2 * a3)`: the status was the constant 0 the machine writes, and a
/// subtract of that constant is a negation.
#[test]
fn exclusive_stores_are_a_store_and_a_zero_status() {
    for words in [&EXCLUSIVE_WORDS[..], &EXCLUSIVE_CASE[..], &STATUS_READ[..]] {
        let (p, a, text) = decompiled_words(words);
        assert!(!text.contains("/* asm: stxr"), "{text}");
        assert!(!text.contains("/* asm: stxp"), "{text}");
        assert!(!text.contains("stlxr"), "{text}");
        let entry = p.entry.expect("entry");
        let v = verify(&p, &a, &[entry], 1);
        assert!(v.checked > 0, "{}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "{text}\n{}", verify_tsv(&v));
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
    let (_, _, words) = decompiled_words(&EXCLUSIVE_WORDS);
    assert!(words.contains("*(uint64_t*)a3 = a2;"), "{words}");
    assert!(words.contains("*(uint16_t*)a3 = a2;"), "{words}");
    assert!(words.contains("*(uint64_t*)a3 = a1;"), "{words}");
    let (_, _, status) = decompiled_words(&STATUS_READ);
    assert!(status.contains("*(uint64_t*)a3 = a2;"), "{status}");
    assert!(
        status.contains("return -(a2 * a3);"),
        "status should be the constant 0\n{status}"
    );
}

/// `mrs` and `msr` of `TPIDR_EL0` and `NZCV` are moves, not an `/* asm */`
/// line. `svc #0` is the exit test and the `write` count. Another
/// immediate stays `/* asm */`.
///
/// The system-register words are the emulate case `system`. A check starts
/// with the thread pointer and the flags clear, so the read of `TPIDR_EL0`
/// is zero and the read of `NZCV` is zero.
#[test]
fn system_registers_are_the_thread_pointer_and_the_flags() {
    let (p, a, text) = decompiled_words(&SYSTEM_WORDS);
    assert!(!text.contains("/* asm"), "{text}");
    assert!(!text.contains("mrs"), "{text}");
    assert!(!text.contains("msr"), "{text}");
    let entry = p.entry.expect("entry");
    let v = verify(&p, &a, &[entry], 1);
    assert!(v.checked > 0, "{}", verify_tsv(&v));
    assert!(v.mismatches.is_empty(), "{text}\n{}", verify_tsv(&v));
    let r = replay_function(&p, &a, entry, 1);
    assert!(r.checked > 0, "{}", replay_tsv(&r));
    assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    let (sp, sa, svc) = decompiled_words(&[
        // ASM: svc #0
        0xd400_0001,
        // ASM: ret
        0xd65f_03c0,
    ]);
    assert!(!svc.contains("/* asm"), "{svc}");
    assert!(svc.contains("== 93 ||"), "{svc}");
    assert!(svc.contains("== 64 ?"), "{svc}");
    let sentry = sp.entry.expect("entry");
    let sv = verify(&sp, &sa, &[sentry], 1);
    assert!(sv.checked > 0, "{}", verify_tsv(&sv));
    assert!(sv.mismatches.is_empty(), "{svc}\n{}", verify_tsv(&sv));
    let sr = replay_function(&sp, &sa, sentry, 1);
    assert!(sr.checked > 0, "{}", replay_tsv(&sr));
    assert!(sr.wrong().is_empty(), "{svc}\n{}", replay_tsv(&sr));
    let (_, _, other) = decompiled_words(&[
        // ASM: svc #0x80
        0xd400_1001,
        // ASM: ret
        0xd65f_03c0,
    ]);
    assert!(other.contains("/* asm: svc"), "{other}");
}

/// `msr TPIDR_EL0` keeps the value it captured when a later `mrs` writes
/// that register.
///
/// `x0` is an incoming parameter, so the value `msr` reads there is that
/// parameter and a later write of `x0` does not rebind it. `x16` is not a
/// parameter: the captured expression is `x16`'s text variable. `cmp`
/// makes `mrs x16, NZCV` a word large enough to be written out at once,
/// which rebinds `x16`. The reload into `x0` must still be the pointer
/// `msr` captured, not that word. The same three moves on `x0` itself,
/// with no compare between them, stay the captured parameter.
#[test]
fn msr_tpidr_keeps_the_value_it_captured() {
    const CAPTURED: [u32; 5] = [
        // ASM: msr TPIDR_EL0, x16
        0xd51b_d050,
        // ASM: cmp x1, x2
        0xeb02_003f,
        // ASM: mrs x16, NZCV
        0xd53b_4210,
        // ASM: mrs x0, TPIDR_EL0
        0xd53b_d040,
        // ASM: ret
        0xd65f_03c0,
    ];
    const RELOADS_X0: [u32; 4] = [
        // ASM: msr TPIDR_EL0, x0
        0xd51b_d040,
        // ASM: mrs x0, NZCV
        0xd53b_4200,
        // ASM: mrs x0, TPIDR_EL0
        0xd53b_d040,
        // ASM: ret
        0xd65f_03c0,
    ];
    for words in [&CAPTURED[..], &RELOADS_X0[..]] {
        let (p, a, text) = decompiled_words(words);
        assert!(!text.contains("/* asm"), "{text}");
        let entry = p.entry.expect("entry");
        let v = verify(&p, &a, &[entry], 1);
        assert!(v.checked > 0, "{}", verify_tsv(&v));
        assert_eq!(v.unreadable, 0, "{text}\n{}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "{text}\n{}", verify_tsv(&v));
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{}", replay_tsv(&r));
        assert!(
            r.compared.get(&Claim::Return).copied().unwrap_or(0) > 0,
            "{text}\n{}",
            replay_tsv(&r)
        );
        assert!(r.unreadable.is_empty(), "{text}\n{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// An atomic is the load, the modification and the store, and `cas` is the
/// conditional store, not an `/* asm */` line.
///
/// The words are the `MNEMONICS` encodings from `ldadd` through `casb`, the
/// `ldsmin` and `ldumax` words beside them, and the emulate case `atomics`.
#[test]
fn atomics_are_a_load_a_modification_and_a_store() {
    for words in [&ATOMIC_WORDS[..], &ATOMIC_CASE[..]] {
        let (p, a, text) = decompiled_words(words);
        assert!(!text.contains("/* asm"), "{text}");
        assert!(text.contains("if ("), "{text}");
        let entry = p.entry.expect("entry");
        let v = verify(&p, &a, &[entry], 1);
        assert!(v.checked > 0, "{}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "{text}\n{}", verify_tsv(&v));
        let r = replay_function(&p, &a, entry, 1);
        assert!(r.checked > 0, "{}", replay_tsv(&r));
        assert!(r.wrong().is_empty(), "{text}\n{}", replay_tsv(&r));
    }
}

/// `rbit` prints as `rbit`, not `__rbit`. The 32-bit form reverses the low
/// half only: `a2` is declared `int32_t`, so the cast is not printed, and
/// the return is `uint32_t` with no second mask.
#[test]
fn a_bit_reversal_is_rbit() {
    let cases: &[(&[u32], &str)] = &[
        (&[0xdac0_0020, 0xd65f_03c0], "uint64_t a2"),
        (&[0x5ac0_0020, 0xd65f_03c0], "int32_t a2"),
    ];
    for (words, param) in cases {
        let (p, a, text) = decompiled_words(words);
        assert!(text.contains("return rbit(a2);"), "{text}");
        assert!(text.contains(param), "{text}");
        assert!(!text.contains("__rbit"), "{text}");
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

/// `rev32` prints as `rev32`, not `__rev32`. It is the 64-bit instruction:
/// each word's bytes swap, and the whole register is not one `bswap`.
#[test]
fn bytes_in_each_word_are_rev32() {
    let (p, a, text) = decompiled_words(&[0xdac0_0820, 0xd65f_03c0]);
    assert!(text.contains("return rev32(a2);"), "{text}");
    assert!(text.contains("uint64_t a2"), "{text}");
    assert!(!text.contains("__rev32"), "{text}");
    assert!(!text.contains("bswap"), "{text}");
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

/// `rev16` prints as `rev16`, not `__rev16`. The 32-bit form swaps each
/// halfword of the low half only, and that result is not masked again.
#[test]
fn bytes_in_each_halfword_are_rev16() {
    let cases: &[(&[u32], &str)] = &[
        (&[0xdac0_0420, 0xd65f_03c0], "uint64_t a2"),
        (&[0x5ac0_0420, 0xd65f_03c0], "int32_t a2"),
    ];
    for (words, param) in cases {
        let (p, a, text) = decompiled_words(words);
        assert!(text.contains("return rev16(a2);"), "{text}");
        assert!(text.contains(param), "{text}");
        assert!(!text.contains("__rev16"), "{text}");
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

/// `cls` prints as `cls`, not `__cls`. The 32-bit form counts the low half
/// only, and the count is not masked.
#[test]
fn leading_sign_bits_are_cls() {
    let cases: &[(&[u32], &str)] = &[
        (&[0xdac0_1420, 0xd65f_03c0], "uint64_t a2"),
        (&[0x5ac0_1420, 0xd65f_03c0], "int32_t a2"),
    ];
    for (words, param) in cases {
        let (p, a, text) = decompiled_words(words);
        assert!(text.contains("return cls(a2);"), "{text}");
        assert!(text.contains(param), "{text}");
        assert!(!text.contains("__cls"), "{text}");
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

/// Lane operations with no scalar form are C over vector types, each read
/// from the fields its word encodes; none is left as assembly or as a call
/// to its mnemonic.
///
/// The routine compares two 16-byte blocks at `x0`, widens and sums the
/// comparison's lanes, moves lanes in from general registers and out to
/// them, stores three more lane results and returns the lane sum.
#[test]
fn arm64_lane_operations_are_c_over_vector_types() {
    let words: [u32; 25] = [
        0x3dc0_0000, // ASM: ldr q0, [x0]
        0x3dc0_0401, // ASM: ldr q1, [x0, #0x10]
        0x6e21_8c00, // ASM: cmeq v0.16b, v0.16b, v1.16b
        0x4ea0_9825, // ASM: cmeq v5.4s, v1.4s, #0
        0x2f08_a402, // ASM: ushll v2.8h, v0.8b, #0x0
        0x6f08_a403, // ASM: ushll2 v3.8h, v0.16b, #0x0
        0x0f12_a426, // ASM: sshll v6.4s, v1.4h, #0x2
        0x4e63_8442, // ASM: add v2.8h, v2.8h, v3.8h
        0x6e02_4044, // ASM: ext v4.16b, v2.16b, v2.16b, #0x8
        0x4e64_8442, // ASM: add v2.8h, v2.8h, v4.8h
        0x4e04_0c27, // ASM: dup v7.4s, w1
        0x4f00_0430, // ASM: movi v16.4s, #0x1
        0x4e0c_1c42, // ASM: mov v2.s[1], w2
        0x6e18_04e2, // ASM: mov v2.d[1], v7.d[0]
        0x0e16_3c43, // ASM: umov w3, v2.h[5]
        0x4e18_3c44, // ASM: mov x4, v2.d[1]
        0x6ee5_3431, // ASM: cmhi v17.2d, v1.2d, v5.2d
        0x3d80_0811, // ASM: str q17, [x0, #0x20]
        0x3d80_0c06, // ASM: str q6, [x0, #0x30]
        0x3d80_1010, // ASM: str q16, [x0, #0x40]
        0x4e71_b840, // ASM: addv h0, v2.8h
        0x1e26_0000, // ASM: fmov w0, s0
        0x0b03_0000, // ASM: add w0, w0, w3
        0x8b04_0000, // ASM: add x0, x0, x4
        0xd65f_03c0, // ASM: ret
    ];
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE_SIMD, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm64, 0, Some(BASE_SIMD), vec![text]);
    p.symbols = vec![local("lanes", BASE_SIMD)];
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), BASE_SIMD).expect("decompiles");
    assert!(!out.contains("/* asm"), "{out}");
    for name in [
        "__cmeq", "__cmhi", "__ushll", "__sshll", "__ext", "__dup", "__ins", "__umov", "__addv",
        "__add_",
    ] {
        assert!(!out.contains(name), "{name}: {out}");
    }
    for spelled in [
        "typedef uint16_t u16x8 __attribute__((vector_size(16), aligned(1)));",
        "*(u8x16*)a1 == *(u8x16*)(a1 + 16)",
        "__builtin_convertvector(",
        "(u32x4){0} + (uint32_t)a3",
        "(u64x2){0} + (uint64_t)0x100000001",
        ")[5]",
        "(uint16_t)(",
    ] {
        assert!(out.contains(spelled), "{spelled}: {out}");
    }
}

/// Structure loads and stores, selects, narrowings and tables are C.
///
/// The bitwise selects, narrowing shifts, table lookups, the vector bit
/// reversal and population count and the conversions read from `v`
/// registers are C over vector types, none left as assembly or as a call
/// to its mnemonic. The routine loads interleaved, replicated and single-lane structures
/// from `x0`, selects, narrows, looks up and reverses their lanes, stores
/// them interleaved, as a lane and whole, and returns a negated product
/// of a fixed-point conversion.
#[test]
fn arm64_structures_selects_and_tables_are_c_over_vector_types() {
    let words: [u32; 20] = [
        0x4c40_8800, // ASM: ld2 {v0.4s, v1.4s}, [x0]
        0x4d60_e002, // ASM: ld4r {v2.16b, v3.16b, v4.16b, v5.16b}, [x0]
        0x4d40_8006, // ASM: ld1 {v6.s}[2], [x0]
        0x6e62_1c20, // ASM: bsl v0.16b, v1.16b, v2.16b
        0x0f0c_8427, // ASM: shrn v7.8b, v1.8h, #4
        0x6f0e_9c07, // ASM: uqrshrn2 v7.16b, v0.8h, #2
        0x0f1d_9408, // ASM: sqshrn v8.4h, v0.4s, #3
        0x4e03_2009, // ASM: tbl v9.16b, {v0.16b, v1.16b}, v3.16b
        0x4e05_1086, // ASM: tbx v6.16b, {v4.16b}, v5.16b
        0x6e60_592a, // ASM: rbit v10.16b, v9.16b
        0x4e20_594a, // ASM: cnt v10.16b, v10.16b
        0x4f38_e40b, // ASM: scvtf v11.4s, v0.4s, #8
        0x4c00_4826, // ASM: st3 {v6.4s, v7.4s, v8.4s}, [x1]
        0x4c00_8049, // ASM: st2 {v9.16b, v10.16b}, [x2]
        0x4d9f_846a, // ASM: st1 {v10.d}[1], [x3], #8
        0x3d80_006b, // ASM: str q11, [x3]
        0x9e67_008d, // ASM: fmov d13, x4
        0x7f7d_e5ac, // ASM: ucvtf d12, d13, #3
        0x1e6c_8980, // ASM: fnmul d0, d12, d12
        0xd65f_03c0, // ASM: ret
    ];
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE_STRUCT, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm64, 0, Some(BASE_STRUCT), vec![text]);
    p.symbols = vec![local("structures", BASE_STRUCT)];
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), BASE_STRUCT).expect("decompiles");
    assert!(!out.contains("/* asm"), "{out}");
    for name in [
        "__ld2",
        "__ld4",
        "__st2",
        "__st3",
        "__bsl",
        "__shrn",
        "__uqrshrn",
        "__sqshrn",
        "__tbl",
        "__tbx",
        "__rbit",
        "__cnt",
        "__scvtf",
        "__dup",
        "__ins",
    ] {
        assert!(!out.contains(name), "{name}: {out}");
    }
    for spelled in [
        "__builtin_shufflevector(*(u32x4*)a1, *(u32x4*)(a1 + 16), 0, 2, 4, 6)",
        "__builtin_convertvector(",
        "__builtin_elementwise_min(",
        "__builtin_elementwise_max(",
        "__builtin_elementwise_bitreverse(",
        "__builtin_elementwise_popcount(",
        " < 16 ? (",
        " < 32 ? (",
        "/ 256.0f",
        "/ 8.0",
        "-(",
    ] {
        assert!(out.contains(spelled), "{spelled}: {out}");
    }
}
