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
use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
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
    assert!(pair.contains("(x3 + 4) = a3"), "{pair}");
    let scan = text(0x50);
    assert!(scan.contains("if (*(uint8_t*)x0 != 0) continue;"), "{scan}");
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
