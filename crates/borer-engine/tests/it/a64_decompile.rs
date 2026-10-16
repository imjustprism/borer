//! arm64 functions decompiled under the arm64 procedure call standard,
//! and their text replayed against the arm64 machine.
//!
//! The routines are assembled by LLVM (`clang --target=aarch64-linux-gnu`)
//! and checked against `llvm-objdump`; each word's comment is its
//! instruction.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::decompile::replay::{Claim, replay_function, replay_tsv};
use borer_engine::analysis::decompile::verify_a64::{verify, verify_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Feature, Program, Section, Symbol, SymbolKind};

/// Where every routine is placed.
const BASE: u64 = 0x1_0000;

/// Calls, a tail call, a function that returns nothing and one that
/// returns a constant, at [`BASE`]:
///
/// ```text
/// f(a, b) = g(a + 1, b) + 2        at +0x00
/// g(a, b) = a + b                  at +0x20
/// h(p)    : *p = 0                 at +0x28
/// k(p)    : h(p); return 5         at +0x30
/// m(a)    : a == 0 ? 1 : g(a, 3)   at +0x48
/// ```
const ROUTINES: [u32; 23] = [
    0xa9bf_7bfd, // ASM: stp x29, x30, [sp, #-0x10]!
    0x9100_03fd, // ASM: mov x29, sp
    0x9100_0400, // ASM: add x0, x0, #0x1
    0x9400_0005, // ASM: bl g
    0x9100_0800, // ASM: add x0, x0, #0x2
    0xa8c1_7bfd, // ASM: ldp x29, x30, [sp], #0x10
    0xd65f_03c0, // ASM: ret
    0xd503_201f, // ASM: nop
    0x8b01_0000, // ASM: add x0, x0, x1 (g)
    0xd65f_03c0, // ASM: ret
    0xb900_001f, // ASM: str wzr, [x0] (h)
    0xd65f_03c0, // ASM: ret
    0xa9bf_7bfd, // ASM: stp x29, x30, [sp, #-0x10]! (k)
    0x9100_03fd, // ASM: mov x29, sp
    0x97ff_fffc, // ASM: bl h
    0x5280_00a0, // ASM: mov w0, #0x5
    0xa8c1_7bfd, // ASM: ldp x29, x30, [sp], #0x10
    0xd65f_03c0, // ASM: ret
    0xb400_0060, // ASM: cbz x0, m+0xc (m)
    0xd280_0061, // ASM: mov x1, #0x3
    0x17ff_fff4, // ASM: b g
    0x5280_0020, // ASM: mov w0, #0x1
    0xd65f_03c0, // ASM: ret
];

/// A local symbol naming a function.
///
/// # Arguments
///
/// * `name` - The name.
/// * `addr` - Its entry.
fn local(name: &str, addr: u64) -> Symbol {
    Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Local,
    }
}

/// [`ROUTINES`] as a raw arm64 image, every routine named.
fn image() -> Program {
    let code: Vec<u8> = ROUTINES.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm64, 0, Some(BASE), vec![text]);
    p.symbols = [("f", 0), ("g", 0x20), ("h", 0x28), ("k", 0x30), ("m", 0x48)]
        .iter()
        .map(|&(n, off)| local(n, BASE + off))
        .collect();
    p
}

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

/// Where the second set of routines is placed.
const BASE2: u64 = 0x2_0000;
/// Where their jump table is placed, a page above [`BASE2`].
const TABLE2: u64 = BASE2 + 0x1000;

/// A switch through a byte jump table, a pair store to an address that
/// reads memory and the register it overwrites, and a loop a `cbnz` closes
/// on a value a pre-indexed load leaves, at [`BASE2`]:
///
/// ```text
/// sw(a)          : a == 0 ? 10 : a == 1 ? 20 : a == 2 ? 30 : 0   at +0x00
/// pair(p, x, y, i): q = p->arr + i * 8; q[0] = x; q[1] = y        at +0x40
/// scan(s)        : do { q = s; c = *--s; } while (c); return q    at +0x50
/// ```
const ROUTINES2: [u32; 26] = [
    0x7100_081f, // ASM: cmp w0, #0x2 (sw)
    0x5400_01a8, // ASM: b.hi sw+0x38
    0xb000_0009, // ASM: adrp x9, TABLE2
    0x9100_0129, // ASM: add x9, x9, #0x0
    0x3860_492a, // ASM: ldrb w10, [x9, w0, uxtw]
    0x1000_006b, // ASM: adr x11, sw+0x20
    0x8b0a_096b, // ASM: add x11, x11, x10, lsl #2
    0xd61f_0160, // ASM: br x11
    0x5280_0140, // ASM: mov w0, #0xa
    0xd65f_03c0, // ASM: ret
    0x5280_0280, // ASM: mov w0, #0x14
    0xd65f_03c0, // ASM: ret
    0x5280_03c0, // ASM: mov w0, #0x1e
    0xd65f_03c0, // ASM: ret
    0x2a1f_03e0, // ASM: mov w0, wzr
    0xd65f_03c0, // ASM: ret
    0xf940_040a, // ASM: ldr x10, [x0, #0x8] (pair)
    0x8b03_0d43, // ASM: add x3, x10, x3, lsl #3
    0x2900_0861, // ASM: stp w1, w2, [x3]
    0xd65f_03c0, // ASM: ret
    0xb400_00a0, // ASM: cbz x0, scan+0x14 (scan)
    0xaa00_03e1, // ASM: mov x1, x0
    0x385f_fc08, // ASM: ldrb w8, [x0, #-0x1]!
    0x35ff_ffc8, // ASM: cbnz w8, scan+0x4
    0xaa01_03e0, // ASM: mov x0, x1
    0xd65f_03c0, // ASM: ret
];

/// The case offsets of `sw`'s table, in words from its first case.
const TABLE: [u8; 4] = [0, 2, 4, 0];

/// [`ROUTINES2`] and [`TABLE`] as a raw arm64 image, every routine named.
fn image2() -> Program {
    let mut bytes: Vec<u8> = ROUTINES2.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(bytes.len()).expect("a small image");
    bytes.extend_from_slice(&TABLE);
    let text = Section::mapped(".text", BASE2, 0, len, false, true);
    let rodata = Section::mapped(".rodata", TABLE2, len, 4, false, false);
    let mut p = Program::raw(bytes, Arch::Arm64, 0, Some(BASE2), vec![text, rodata]);
    p.symbols = [("sw", 0), ("pair", 0x40), ("scan", 0x50)]
        .iter()
        .map(|&(n, off)| local(n, BASE2 + off))
        .collect();
    p
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

/// Where the third set of routines is placed.
const BASE3: u64 = 0x3_0000;

/// 32-bit arithmetic read back at 32 bits, and a 32-bit value read whole
/// as an index, at [`BASE3`]:
///
/// ```text
/// wsum(a, b): t = a + 1; t == b ? t : t - b    (all uint32_t)   at +0x00
/// widx(a, p): return p[(uint32_t)(a + 1)]                        at +0x1c
/// ```
const ROUTINES3: [u32; 10] = [
    0x1100_0408, // ASM: add w8, w0, #0x1 (wsum)
    0x6b01_011f, // ASM: cmp w8, w1
    0x5400_0061, // ASM: b.ne wsum+0x14
    0x2a08_03e0, // ASM: mov w0, w8
    0xd65f_03c0, // ASM: ret
    0x4b01_0100, // ASM: sub w0, w8, w1
    0xd65f_03c0, // ASM: ret
    0x1100_0408, // ASM: add w8, w0, #0x1 (widx)
    0xf868_7820, // ASM: ldr x0, [x1, x8, lsl #3]
    0xd65f_03c0, // ASM: ret
];

/// Where the fourth set of routines is placed.
const BASE4: u64 = 0x4_0000;

/// A signed remainder by a constant through `smull` and a negative magic, a
/// remainder by a register through `sdiv; msub`, and a branch on the sign
/// bit, at [`BASE4`]:
///
/// ```text
/// rem(a)    : (int32_t)a % 127                 at +0x00
/// vrem(a, b): (int32_t)a % (int32_t)b          at +0x24
/// sign(a)   : (int64_t)a >= 0 ? 2 : 1          at +0x30
/// ```
const ROUTINES4: [u32; 17] = [
    0x5280_8128, // ASM: mov w8, #0x409 (rem)
    0x72b0_2048, // ASM: movk w8, #0x8102, lsl #16
    0x9b28_7c08, // ASM: smull x8, w0, w8
    0x8b48_8008, // ASM: add x8, x0, x8, lsr #32
    0x1306_7d09, // ASM: asr w9, w8, #6
    0x0b48_7d28, // ASM: add w8, w9, w8, lsr #31
    0x4b08_1d08, // ASM: sub w8, w8, w8, lsl #7
    0x0b08_0000, // ASM: add w0, w0, w8
    0xd65f_03c0, // ASM: ret
    0x1ac1_0c08, // ASM: sdiv w8, w0, w1 (vrem)
    0x1b01_8100, // ASM: msub w0, w8, w1, w0
    0xd65f_03c0, // ASM: ret
    0xb6f8_0060, // ASM: tbz x0, #63, sign+0xc (sign)
    0x5280_0020, // ASM: mov w0, #0x1
    0xd65f_03c0, // ASM: ret
    0x5280_0040, // ASM: mov w0, #0x2
    0xd65f_03c0, // ASM: ret
];

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

/// Where the fifth set of routines is placed, its guard a page above.
const BASE5: u64 = 0x5_0000;

/// A function under a stack protector whose guard is a global, at
/// [`BASE5`]: `f(a) = a + 1`, the guard copied into `[sp, #8]` and
/// compared before the return, `__stack_chk_fail` at `+0x40`.
const ROUTINES5: [u32; 17] = [
    0xd100_83ff, // ASM: sub sp, sp, #0x20
    0xa901_7bfd, // ASM: stp x29, x30, [sp, #0x10]
    0x9100_43fd, // ASM: add x29, sp, #0x10
    0xb000_0008, // ASM: adrp x8, BASE5 + 0x1000
    0xf940_0108, // ASM: ldr x8, [x8]
    0xf900_07e8, // ASM: str x8, [sp, #0x8]
    0x1100_0400, // ASM: add w0, w0, #0x1
    0xb000_0008, // ASM: adrp x8, BASE5 + 0x1000
    0xf940_0108, // ASM: ldr x8, [x8]
    0xf940_07e9, // ASM: ldr x9, [sp, #0x8]
    0xeb09_011f, // ASM: cmp x8, x9
    0x5400_0081, // ASM: b.ne f+0x3c
    0xa941_7bfd, // ASM: ldp x29, x30, [sp, #0x10]
    0x9100_83ff, // ASM: add sp, sp, #0x20
    0xd65f_03c0, // ASM: ret
    0x9400_0001, // ASM: bl __stack_chk_fail
    0x1400_0000, // ASM: b . (__stack_chk_fail)
];

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

/// The words `MNEMONICS` already assembles for an exclusive store, then
/// `ret` from the emulate case `exclusive`.
const EXCLUSIVE_WORDS: [u32; 4] = [
    // ASM: stxr w3, x1, [x2]
    0xc803_7c41,
    // ASM: stlxrh w3, w1, [x2]
    0x4803_fc41,
    // ASM: stxp w3, x0, x1, [x2]
    0xc823_0440,
    // ASM: ret
    0xd65f_03c0,
];

/// `stxr` then `msub`, both words `MNEMONICS` already assembles, so the
/// status the store writes is what the function returns.
const STATUS_READ: [u32; 3] = [
    // ASM: stxr w3, x1, [x2]
    0xc803_7c41,
    // ASM: msub w0, w1, w2, w3
    0x1b02_8c20,
    // ASM: ret
    0xd65f_03c0,
];

/// The emulate case `exclusive`, the words that case already runs.
const EXCLUSIVE_CASE: [u32; 10] = [
    // ASM: ldxr x0, [x1]
    0xc85f_7c20,
    // ASM: add x0, x0, #0x1
    0x9100_0400,
    // ASM: stxr w2, x0, [x1]
    0xc802_7c20,
    // ASM: ldaxr w3, [x1]
    0x885f_fc23,
    // ASM: stlxr w4, w3, [x5]
    0x8804_fca3,
    // ASM: ldar x6, [x1]
    0xc8df_fc26,
    // ASM: stlr x6, [x5]
    0xc89f_fca6,
    // ASM: ldxp x7, x8, [x1]
    0xc87f_2027,
    // ASM: stxp w9, x7, x8, [x5]
    0xc829_20a7,
    // ASM: ret
    0xd65f_03c0,
];

/// Decompiles `words` at the arm64 image helper's entry.
///
/// # Arguments
///
/// * `words` - The routine.
fn decompiled_words(words: &[u32]) -> (Program, Analysis, String) {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let p = crate::raw::image(Arch::Arm64, &code, &[]);
    let a = Analysis::compute(&p);
    let entry = p.entry.expect("the image is entered at its code");
    let text = decompile(&p, &a, &Overlay::default(), entry).unwrap_or_default();
    (p, a, text)
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

/// The `MNEMONICS` atomic and `cas` words, plus `ldsmin` and `ldumax`, then
/// `ret`.
const ATOMIC_WORDS: [u32; 16] = [
    // ASM: ldadd x0, x1, [x2]
    0xf820_0041,
    // ASM: ldaddal w0, w1, [x2]
    0xb8e0_0041,
    // ASM: ldclr x0, x1, [x2]
    0xf820_1041,
    // ASM: ldeor w0, w1, [x2]
    0xb820_2041,
    // ASM: ldset x0, x1, [x2]
    0xf820_3041,
    // ASM: ldsmax w0, w1, [x2]
    0xb820_4041,
    // ASM: ldsmin w0, w10, [x11]
    0xb820_516a,
    // ASM: ldumin x0, x1, [x2]
    0xf820_7041,
    // ASM: ldumax w13, w14, [x11]
    0xb82d_616e,
    // ASM: swp x0, x1, [x2]
    0xf820_8041,
    // ASM: swpalb w0, w1, [x2]
    0x38e0_8041,
    // ASM: ldaddh w0, w1, [x2]
    0x7820_0041,
    // ASM: cas x0, x1, [x2]
    0xc8a0_7c41,
    // ASM: casal w0, w1, [x2]
    0x88e0_fc41,
    // ASM: casb w0, w1, [x2]
    0x08a0_7c41,
    // ASM: ret
    0xd65f_03c0,
];

/// The emulate case `atomics`, including `ldsmin` and `ldumax`.
const ATOMIC_CASE: [u32; 15] = [
    // ASM: ldadd x0, x1, [x2]
    0xf820_0041,
    // ASM: ldaddal x0, x3, [x2]
    0xf8e0_0043,
    // ASM: ldclr x7, x5, [x4]
    0xf827_1085,
    // ASM: ldset x7, x6, [x4]
    0xf827_3086,
    // ASM: ldeor x7, x8, [x4]
    0xf827_2088,
    // ASM: swp x0, x9, [x4]
    0xf820_8089,
    // ASM: ldsmin w0, w10, [x11]
    0xb820_516a,
    // ASM: ldsmax w0, w10, [x11]
    0xb820_416a,
    // ASM: ldumax w13, w14, [x11]
    0xb82d_616e,
    // ASM: ldumin w13, w14, [x11]
    0xb82d_716e,
    // ASM: ldaddb w0, w15, [x2]
    0x3820_004f,
    // ASM: cas x16, x17, [x4]
    0xc8b0_7c91,
    // ASM: casal x19, x20, [x4]
    0xc8f3_fc94,
    // ASM: casb w21, w22, [x2]
    0x08b5_7c56,
    // ASM: ret
    0xd65f_03c0,
];

/// The emulate case `system`: `mrs` and `msr` of `TPIDR_EL0` and `NZCV`,
/// then `ret`.
const SYSTEM_WORDS: [u32; 6] = [
    // ASM: mrs x0, TPIDR_EL0
    0xd53b_d040,
    // ASM: msr TPIDR_EL0, x16
    0xd51b_d050,
    // ASM: mrs x1, TPIDR_EL0
    0xd53b_d041,
    // ASM: mrs x2, NZCV
    0xd53b_4202,
    // ASM: msr NZCV, x3
    0xd51b_4203,
    // ASM: ret
    0xd65f_03c0,
];

/// `mrs` and `msr` of `TPIDR_EL0` and `NZCV` are moves, not an `/* asm */`
/// line. `svc #0` stays one: the word is the `MNEMONICS` encoding.
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
    let (_, _, svc) = decompiled_words(&[
        // ASM: svc #0
        0xd400_0001,
        // ASM: ret
        0xd65f_03c0,
    ]);
    assert!(svc.contains("/* asm: svc"), "{svc}");
}

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
