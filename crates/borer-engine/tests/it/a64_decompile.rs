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

/// `scvtf` and `ucvtf` print as a cast of the integer's own signedness.
///
/// A signed source keeps the sign extension, so a negative value is not
/// an unsigned bit pattern. A fixed-point form divides in a double and
/// narrows after, which is the conversion's one rounding.
#[test]
fn an_integer_to_float_is_a_cast() {
    // The value is stored. A float left only in `d0` is not the integer
    // return, so the listing would drop it.
    // A 32-bit parameter declared at that width drops the redundant
    // integer cast. The store line is what carries the conversion; the
    // signature's `int32_t` is not one.
    let cases: &[(&[u32], &[&str], &[&str])] = &[
        // ASM: scvtf d0, x0 / str d0, [x1] / ret
        (
            &[0x9e62_0000, 0xfd00_0020, 0xd65f_03c0],
            &["(double)(int64_t)"],
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
            &["(double)(int64_t)", "16.0"],
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
            &["(float)(int64_t)"],
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
            &["(float)", "(double)(int64_t)", "16.0"],
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
            &["*(uint32_t*)", "((double)(int64_t)a1)", "0xffffffff"],
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
            &[
                "(float)(((double)(int64_t)a1) & 0xffffffff)",
                "0.0",
                "(int64_t)",
            ],
            &["(double)(int64_t)a1 <", "(double)(int64_t)a1 >"],
        ),
        // ASM: scvtf d0, x0 / fadd s0, s0, s0 / str d0, [x1] / ret
        (
            &[0x9e62_0000, 0x1e20_2800, 0xfd00_0020, 0xd65f_03c0],
            &[
                "*(uint64_t*)",
                "(float)(((double)(int64_t)a1) & 0xffffffff)",
                "(int64_t)",
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
        // The select is written out. `fneg` still flips bit 63 of that name.
        (
            &[
                0x1e22_0000,
                0x1e61_2000,
                0x1e61_4c00,
                0x1e61_4000,
                0xfd00_0020,
                0xd65f_03c0,
            ],
            &["*(uint64_t*)", "0x8000000000000000", "(double)(((float)"],
            &["*(double*)", "*(float*)", "/* asm"],
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
                "(int64_t)",
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
            &["isgreaterequal", "||", "isunordered", "float a"],
            &["/* asm", "&&"],
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
            &["isgreaterequal", "||", "isunordered", "float a"],
            &["/* asm", "&&"],
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
            &["isgreaterequal", "||", "isunordered", "float a"],
            &["/* asm", "&&"],
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
            &["isgreaterequal", "||", "isunordered", "*(uint64_t*)"],
            &["/* asm", "*(double*)", "&&"],
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
            &["isgreaterequal", "||", "isunordered", "*(uint64_t*)"],
            &["/* asm", "*(double*)", "&&"],
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
            &["isgreaterequal", "||", "isunordered"],
            &["/* asm", "&&"],
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
            let want = "isgreaterequal(a1, a2) || isunordered(a1, a2)";
            if !text.contains(want) {
                failures.push_str(&format!("{label} prints\n{text}\n"));
            }
        }
        if label == "fcmp d b.lo" || label == "fcmp d b.mi" {
            let want = "!isgreaterequal(a1, a2) && !isunordered(a1, a2)";
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

/// Eight seeds of one routine against the arm64 machine.
///
/// Verify compares the lifted values. Replay compares the printed
/// statements. Both have to move something, and neither may disagree.
///
/// # Arguments
///
/// * `words` - The routine, `ret` included.
fn agrees(words: &[u32]) {
    let (p, a, text) = decompiled_words(words);
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
        assert!(r.checked > 0, "seed {seed}: {text}\n{}", replay_tsv(&r));
        assert!(
            r.wrong().is_empty(),
            "seed {seed}: {text}\n{}",
            replay_tsv(&r)
        );
    }
}

/// The same check for a scalar `fmov` immediate.
///
/// That operand is not one the replay enters. A replay that does enter
/// must not disagree, and the block verify is the machine check.
///
/// # Arguments
///
/// * `words` - The routine, `ret` included.
fn agrees_immediate(words: &[u32]) {
    let (p, a, text) = decompiled_words(words);
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
        assert!(
            r.unreadable.is_empty(),
            "seed {seed}: {text}\n{}",
            replay_tsv(&r)
        );
        assert!(
            r.wrong().is_empty(),
            "seed {seed}: {text}\n{}",
            replay_tsv(&r)
        );
    }
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
