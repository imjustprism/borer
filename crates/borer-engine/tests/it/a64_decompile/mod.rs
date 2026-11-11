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

mod conversions;
mod floats;
mod integers;

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

/// Where the lane-operation routine is placed.
const BASE_SIMD: u64 = 0x5_0000;

/// Where the structure and table routine is placed.
const BASE_STRUCT: u64 = 0x6_0000;

/// Where the second structure routine is placed.
const BASE_STRUCT2: u64 = 0x7_0000;

/// `h_hornerf` at `-O0`: `float r = 0; for (...) r = r * x + c[i];`.
///
/// The accumulator's slot is first written by `str wzr`, an integer zero,
/// and only then read and written as a single. Typed by that first access,
/// it was declared `uint32_t`, and every `local_14 = local_14 * a3 + ...`
/// converted the float's value to an integer: 1.5 came back as 1.
const HORNERF_O0: [u32; 27] = [
    0xd100_83ff, // ASM: sub sp, sp, #0x20
    0xf900_0fe0, // ASM: str x0, [sp, #0x18]
    0xb900_17e1, // ASM: str w1, [sp, #0x14]
    0xbd00_13e0, // ASM: str s0, [sp, #0x10]
    0xb900_0fff, // ASM: str wzr, [sp, #0xc]
    0xb940_17e8, // ASM: ldr w8, [sp, #0x14]
    0x7100_0508, // ASM: subs w8, w8, #0x1
    0xb900_0be8, // ASM: str w8, [sp, #0x8]
    0x1400_0001, // ASM: b +0x4
    0xb940_0be8, // ASM: ldr w8, [sp, #0x8]
    0x37f8_01c8, // ASM: tbnz w8, #0x1f, +0x38
    0x1400_0001, // ASM: b +0x4
    0xbd40_0fe0, // ASM: ldr s0, [sp, #0xc]
    0xbd40_13e1, // ASM: ldr s1, [sp, #0x10]
    0xf940_0fe8, // ASM: ldr x8, [sp, #0x18]
    0xb980_0be9, // ASM: ldrsw x9, [sp, #0x8]
    0xbc69_7902, // ASM: ldr s2, [x8, x9, lsl #2]
    0x1f01_0800, // ASM: fmadd s0, s0, s1, s2
    0xbd00_0fe0, // ASM: str s0, [sp, #0xc]
    0x1400_0001, // ASM: b +0x4
    0xb940_0be8, // ASM: ldr w8, [sp, #0x8]
    0x7100_0508, // ASM: subs w8, w8, #0x1
    0xb900_0be8, // ASM: str w8, [sp, #0x8]
    0x17ff_fff2, // ASM: b -0x38
    0xbd40_0fe0, // ASM: ldr s0, [sp, #0xc]
    0x9100_83ff, // ASM: add sp, sp, #0x20
    0xd65f_03c0, // ASM: ret
];
