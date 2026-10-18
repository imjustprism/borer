//! The arm64 lifter, checked against the arm64 machine block by block.
//!
//! Each routine is a few blocks of one form the lifter maps (the carry a
//! compare or an addition leaves, conditional compare chains, the
//! conditional selects, the bitfield moves, pair loads that write their
//! base back, `w` writes that clear the upper half, the scalar float
//! arithmetic, compares and conversions, the vector bitwise logic, a frame
//! built and torn down under pointer authentication), assembled by LLVM
//! (`clang --target=aarch64-linux-gnu -march=armv8.5-a`) and checked
//! against `llvm-objdump` — the float and vector ones hand-encoded from
//! the Arm ARM and checked against the decoder. Every block is lifted and
//! run from the same seeded states, and every register, `v` register,
//! slot, store and branch must agree on every seed.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::verify::{Fact, Verified};
use borer_engine::analysis::decompile::verify_a64::{verify, verify_tsv};
use borer_engine::program::{Arch, Program, Section};

/// Where every routine is placed.
const BASE: u64 = 0x1_0000;

/// Seeds each routine is checked from.
const SEEDS: u64 = 24;

/// A raw arm64 image whose only section, at [`BASE`], holds `words`.
///
/// # Arguments
///
/// * `words` - The code, in order.
fn image(words: &[u32]) -> Program {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    Program::raw(code, Arch::Arm64, 0, Some(BASE), vec![text])
}

/// Checks the function at [`BASE`] from every seed and requires every
/// fact to agree.
///
/// # Arguments
///
/// * `words` - The routine.
/// * `checked` - How many of its blocks are compared on each seed.
///
/// # Returns
///
/// What each seed found.
fn agrees(words: &[u32], checked: usize) -> Vec<Verified> {
    let p = image(words);
    let a = Analysis::compute(&p);
    (1..=SEEDS)
        .map(|seed| {
            let v = verify(&p, &a, &[BASE], seed);
            assert_eq!(v.checked, checked, "seed {seed}: {}", verify_tsv(&v));
            assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
            assert_eq!(v.unreadable, 0, "seed {seed}: {}", verify_tsv(&v));
            v
        })
        .collect()
}

/// How many facts of a kind one seed compared.
///
/// # Arguments
///
/// * `v` - What the seed found.
/// * `fact` - The kind.
fn compared(v: &Verified, fact: Fact) -> usize {
    v.facts.get(&fact).map_or(0, |t| t.compared)
}

/// The carry reads by what set it.
///
/// A compare's carry is set when nothing borrows and an addition's is its
/// carry out, so `hs` after `cmp` and after `cmn` are opposite x86
/// conditions; a test leaves it clear; and an add or subtract with carry
/// reads it through the compare before it.
#[test]
fn carry_polarity_agrees_with_the_emulator() {
    let words = [
        // ASM: cmp x0, #0x5
        0xf100_141f,
        // ASM: b.hs 0x40
        0x5400_01e2,
        // ASM: cmn x1, #0x3
        0xb100_0c3f,
        // ASM: b.hs 0x40
        0x5400_01a2,
        // ASM: adds x2, x3, x4
        0xab04_0062,
        // ASM: b.lo 0x40
        0x5400_0163,
        // ASM: subs w5, w6, w7
        0x6b07_00c5,
        // ASM: b.hi 0x40
        0x5400_0128,
        // ASM: adds w8, w9, w10
        0x2b0a_0128,
        // ASM: b.ls 0x40
        0x5400_00e9,
        // ASM: cmp x14, x15
        0xeb0f_01df,
        // ASM: adc x11, x12, x13
        0x9a0d_018b,
        // ASM: sbc w16, w17, w18
        0x5a12_0230,
        // ASM: tst x19, #0x8000000000000000
        0xf241_027f,
        // ASM: b.lo 0x40
        0x5400_0043,
        // ASM: nop
        0xd503_201f,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 7) {
        assert_eq!(compared(&v, Fact::Branch), 6, "{}", verify_tsv(&v));
    }
}

/// A conditional compare leaves the truth of the condition its reader
/// asks, chained through a second conditional compare and read by a
/// `cset` and by the branch on the inverse condition.
#[test]
fn ccmp_chains_agree_with_the_emulator() {
    let words = [
        // ASM: cmp x0, #0x1
        0xf100_041f,
        // ASM: ccmp x1, #0x2, #0x0, eq
        0xfa42_0820,
        // ASM: b.eq 0x30
        0x5400_0140,
        // ASM: cmp x2, #0x3
        0xf100_0c5f,
        // ASM: ccmp x3, #0x4, #0x4, ne
        0xfa44_1864,
        // ASM: ccmp x4, x5, #0x8, eq
        0xfa45_0088,
        // ASM: b.ne 0x30
        0x5400_00c1,
        // ASM: cmp w6, #0xa
        0x7100_28df,
        // ASM: ccmn w7, #0x5, #0x2, lo
        0x3a45_38e2,
        // ASM: cset w8, hi
        0x1a9f_97e8,
        // ASM: b.ls 0x30
        0x5400_0049,
        // ASM: nop
        0xd503_201f,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 4) {
        assert_eq!(compared(&v, Fact::Branch), 3, "{}", verify_tsv(&v));
    }
}

/// The conditional selects, and their `cset`, `csetm` and `cinc` aliases,
/// are ternaries over the compare's flags.
#[test]
fn csel_agrees_with_the_emulator() {
    let words = [
        // ASM: cmp x0, x1
        0xeb01_001f,
        // ASM: csel x2, x3, x4, lt
        0x9a84_b062,
        // ASM: csinc w5, w6, w7, ge
        0x1a87_a4c5,
        // ASM: csinv x8, x9, x10, hi
        0xda8a_8128,
        // ASM: csneg w11, w12, w13, eq
        0x5a8d_058b,
        // ASM: cset x14, ne
        0x9a9f_07ee,
        // ASM: csetm w15, lo
        0x5a9f_23ef,
        // ASM: cinc x16, x17, mi
        0x9a91_5630,
        // ASM: b.gt 0x28
        0x5400_004c,
        // ASM: nop
        0xd503_201f,
        // ASM: ret
        0xd65f_03c0,
    ];
    agrees(&words, 2);
}

/// The bitfield moves and their aliases extract, insert and extend at
/// both widths, as do `extr` and `ror`.
#[test]
fn ubfx_agrees_with_the_emulator() {
    let words = [
        // ASM: ubfx x0, x1, #4, #8
        0xd344_2c20,
        // ASM: lsr w2, w3, #28
        0x531c_7c62,
        // ASM: asr x4, x5, #60
        0x937c_fca4,
        // ASM: ubfiz w6, w7, #3, #5
        0x531d_10e6,
        // ASM: bfi x8, x9, #16, #8
        0xb370_1d28,
        // ASM: bfxil w10, w11, #2, #6
        0x3302_1d6a,
        // ASM: lsr w12, w13, #7
        0x5307_7dac,
        // ASM: asr w14, w15, #3
        0x1303_7dee,
        // ASM: lsl x16, x17, #13
        0xd373_ca30,
        // ASM: sxtw x18, w19
        0x9340_7e72,
        // ASM: uxtb w20, w21
        0x5300_1eb4,
        // ASM: extr x22, x23, x24, #0xc
        0x93d8_32f6,
        // ASM: ror w25, w26, #0x5
        0x139a_1759,
        // ASM: sbfiz x27, x28, #40, #10
        0x9358_279b,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert!(compared(&v, Fact::Register) >= 32, "{}", verify_tsv(&v));
    }
}

/// Pair loads and stores write their base back after the access.
///
/// Pre- and post-indexed off the stack pointer and off a pointer; the
/// narrow, signed and register-indexed forms load and store what the
/// machine does.
#[test]
fn ldp_writeback_agrees_with_the_emulator() {
    let words = [
        // ASM: stp x0, x1, [sp, #-0x20]!
        0xa9be_07e0,
        // ASM: stp x2, x3, [sp, #0x10]
        0xa901_0fe2,
        // ASM: ldp x4, x5, [sp], #0x10
        0xa8c1_17e4,
        // ASM: ldp x6, x7, [x8, #0x8]!
        0xa9c0_9d06,
        // ASM: ldp w9, w10, [x11], #-0x8
        0x28ff_2969,
        // ASM: ldpsw x12, x13, [x14, #0x4]
        0x6940_b5cc,
        // ASM: str x15, [x16, #0x8]!
        0xf800_8e0f,
        // ASM: ldr x17, [x16], #-0x8
        0xf85f_8611,
        // ASM: ldrsb w18, [x19, #0x3]
        0x39c0_0e72,
        // ASM: ldrh w20, [x21, x22, lsl #1]
        0x7876_7ab4,
        // ASM: strb w23, [x24, w25, sxtw]
        0x3839_cb17,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Slot), 4, "{}", verify_tsv(&v));
        assert_eq!(compared(&v, Fact::Store), 2, "{}", verify_tsv(&v));
    }
}

/// A `w` write zero-extends into its `x` register whatever the operation,
/// and every register compares at all 64 bits.
#[test]
fn w_zero_extension_agrees_with_the_emulator() {
    let words = [
        // ASM: add w0, w1, w2
        0x0b02_0020,
        // ASM: mov w3, w4
        0x2a04_03e3,
        // ASM: ldr w5, [x6]
        0xb940_00c5,
        // ASM: neg w7, w8
        0x4b08_03e7,
        // ASM: mvn w9, w10
        0x2a2a_03e9,
        // ASM: mul w11, w12, w13
        0x1b0d_7d8b,
        // ASM: lsl w14, w15, w16
        0x1ad0_21ee,
        // ASM: udiv w17, w18, w19
        0x1ad3_0a51,
        // ASM: sdiv w20, w21, w22
        0x1ad6_0eb4,
        // ASM: orr w23, wzr, #0xff00
        0x3218_1ff7,
        // ASM: mov w24, #-0x4
        0x1280_0078,
        // ASM: movk w25, #0x1234, lsl #16
        0x72a2_4699,
        // ASM: add w26, w27, w28, uxtb #2
        0x0b3c_0b7a,
        // ASM: sub w29, w0, w1, lsr #3
        0x4b41_0c1d,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Register), 32, "{}", verify_tsv(&v));
    }
}

/// A narrow store to a slot reads back as the bytes it wrote, zero- or
/// sign-extended by the load, not as the whole register it stored.
#[test]
fn narrow_slots_agree_with_the_emulator() {
    let words = [
        // ASM: sub sp, sp, #0x10
        0xd100_43ff,
        // ASM: strb w0, [sp, #0xf]
        0x3900_3fe0,
        // ASM: ldrb w8, [sp, #0xf]
        0x3940_3fe8,
        // ASM: strh w1, [sp, #0xc]
        0x7900_1be1,
        // ASM: ldrsh x9, [sp, #0xc]
        0x7980_1be9,
        // ASM: str w2, [sp, #0x8]
        0xb900_0be2,
        // ASM: ldrsw x10, [sp, #0x8]
        0xb980_0bea,
        // ASM: add sp, sp, #0x10
        0x9100_43ff,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Slot), 3, "{}", verify_tsv(&v));
        assert_eq!(compared(&v, Fact::Register), 32, "{}", verify_tsv(&v));
    }
}

/// A block that is only a `cbz` or a `tbnz` is checked for its branch: a
/// register against zero, and one bit of a `w` register.
#[test]
fn cbz_and_tbnz_alone_agree_with_the_emulator() {
    let words = [
        // ASM: cbz x0, 0x8
        0xb400_0040,
        // ASM: nop
        0xd503_201f,
        // ASM: tbnz w1, #0x1f, 0x10
        0x37f8_0041,
        // ASM: nop
        0xd503_201f,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 4) {
        assert_eq!(compared(&v, Fact::Branch), 2, "{}", verify_tsv(&v));
    }
}

/// Scalar float arithmetic over values a memory load typed: the sum,
/// difference, product, quotient, root, absolute value and negation, with
/// the two results stored back.
#[test]
fn float_arithmetic_agrees_with_the_emulator() {
    let words = [
        // ASM: ldr d0, [x0]
        0xfd40_0000,
        // ASM: ldr d1, [x0, #0x8]
        0xfd40_0401,
        // ASM: fadd d2, d0, d1
        0x1e61_2802,
        // ASM: fsub d3, d0, d1
        0x1e61_3803,
        // ASM: fmul d4, d0, d1
        0x1e61_0804,
        // ASM: fdiv d5, d0, d1
        0x1e61_1805,
        // ASM: fsqrt d6, d2
        0x1e61_c046,
        // ASM: fabs d7, d6
        0x1e60_c0c7,
        // ASM: fneg d8, d7
        0x1e61_40e8,
        // ASM: str d5, [x1]
        0xfd00_0025,
        // ASM: str d8, [x1, #0x8]
        0xfd00_0428,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Vector), 32, "{}", verify_tsv(&v));
        assert_eq!(compared(&v, Fact::Store), 2, "{}", verify_tsv(&v));
    }
}

/// The fused multiply-adds agree with the machine over loaded values.
///
/// `fmadd`, `fmsub`, `fnmadd` and `fnmsub` of the same three sources, the
/// four results stored back. The machine rounds once; the product and sum the
/// text spells agree with it on every seed.
#[test]
fn fused_multiply_add_agrees_with_the_emulator() {
    let words = [
        // ASM: ldr d0, [x0]
        0xfd40_0000,
        // ASM: ldr d1, [x0, #0x8]
        0xfd40_0401,
        // ASM: ldr d3, [x0, #0x10]
        0xfd40_0803,
        // ASM: fmadd d2, d0, d1, d3
        0x1f41_0c02,
        // ASM: fmsub d4, d0, d1, d3
        0x1f41_8c04,
        // ASM: fnmadd d5, d0, d1, d3
        0x1f61_0c05,
        // ASM: fnmsub d6, d0, d1, d3
        0x1f61_8c06,
        // ASM: str d2, [x1]
        0xfd00_0022,
        // ASM: str d4, [x1, #0x8]
        0xfd00_0424,
        // ASM: str d5, [x1, #0x10]
        0xfd00_0825,
        // ASM: str d6, [x1, #0x18]
        0xfd00_0c26,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Store), 4, "{}", verify_tsv(&v));
    }
}

/// A float compare sets the flags its conditions read.
///
/// The block's `mi` branch goes where the machine's goes from every state,
/// and the two conditional selects on the same flags — `mi` both ways —
/// pick the sources the machine picks.
#[test]
fn fcmp_and_fcsel_agree_with_the_emulator() {
    let words = [
        // ASM: ldr s0, [x0]
        0xbd40_0000,
        // ASM: ldr s1, [x0, #0x4]
        0xbd40_0401,
        // ASM: fcmp s0, s1
        0x1e21_2000,
        // ASM: fcsel s2, s0, s1, mi
        0x1e21_4c02,
        // ASM: fcsel s3, s0, s1, ge
        0x1e21_ac03,
        // ASM: str s2, [x1]
        0xbd00_0022,
        // ASM: str s3, [x1, #0x4]
        0xbd00_0423,
        // ASM: b.mi 0x28
        0x5400_0064,
        // ASM: str s0, [x1]
        0xbd00_0020,
        // ASM: ret
        0xd65f_03c0,
        // ASM: str s1, [x1]
        0xbd00_0021,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 3) {
        assert_eq!(compared(&v, Fact::Branch), 1, "{}", verify_tsv(&v));
    }
}

/// A conditional float compare chains through the compare before it: the
/// branch reads the condition the immediate flags or the second compare
/// left, whichever the machine's flags say.
#[test]
fn fccmp_chains_agree_with_the_emulator() {
    let words = [
        // ASM: ldr s0, [x0]
        0xbd40_0000,
        // ASM: ldr s1, [x0, #0x4]
        0xbd40_0401,
        // ASM: ldr s2, [x0, #0x8]
        0xbd40_0802,
        // ASM: ldr s3, [x0, #0xc]
        0xbd40_0c03,
        // ASM: fcmp s0, s1
        0x1e21_2000,
        // ASM: fccmp s2, s3, #0xf, gt
        0x1e23_c44f,
        // ASM: b.mi 0x24
        0x5400_0064,
        // ASM: str s0, [x1]
        0xbd00_0020,
        // ASM: ret
        0xd65f_03c0,
        // ASM: str s1, [x1]
        0xbd00_0021,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 3) {
        assert_eq!(compared(&v, Fact::Branch), 1, "{}", verify_tsv(&v));
    }
}

/// The conversions between widths agree wherever the tree can hold the
/// value.
///
/// `fcvtzs`, `fcvtzu`, `scvtf` and `ucvtf` are compared, including the
/// fixed-point scale.
#[test]
fn float_conversions_agree_with_the_emulator() {
    let words = [
        // ASM: ldr d0, [x0]
        0xfd40_0000,
        // ASM: fcvt s1, d0
        0x1e62_4001,
        // ASM: fcvt d2, s1
        0x1e22_c022,
        // ASM: scvtf d3, x2
        0x9e62_0043,
        // ASM: ucvtf d4, w2
        0x1e63_0044,
        // ASM: fcvtzs x5, d0
        0x9e78_0005,
        // ASM: fcvtzu w6, s1
        0x1e39_0026,
        // ASM: scvtf s7, w2, #0x4
        0x1e02_f047,
        // ASM: str d3, [x1]
        0xfd00_0023,
        // ASM: str s7, [x1, #0x8]
        0xbd00_0827,
        // ASM: ret
        0xd65f_03c0,
    ];
    let p = image(&words);
    let a = Analysis::compute(&p);
    for seed in 1..=SEEDS {
        let v = verify(&p, &a, &[BASE], seed);
        let tsv = verify_tsv(&v);
        assert_eq!(v.checked, 1, "seed {seed}: {tsv}");
        assert!(v.mismatches.is_empty(), "seed {seed}: {tsv}");
        assert_eq!(compared(&v, Fact::Store), 2, "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Vector].unreadable, 0, "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Register].unreadable, 0, "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Store].unreadable, 0, "seed {seed}: {tsv}");
    }
}

/// The vector bitwise operations and `dup` agree over whole registers,
/// both through memory and through the registers a general one replicated.
#[test]
fn neon_bitwise_agrees_with_the_emulator() {
    let words = [
        // ASM: ldr d0, [x0]
        0xfd40_0000,
        // ASM: ldr d1, [x0, #0x8]
        0xfd40_0401,
        // ASM: and v2.16b, v0.16b, v1.16b
        0x4e21_1c02,
        // ASM: orr v3.16b, v0.16b, v1.16b
        0x4ea1_1c03,
        // ASM: eor v4.16b, v0.16b, v1.16b
        0x6e21_1c04,
        // ASM: bic v5.16b, v0.16b, v1.16b
        0x4e61_1c05,
        // ASM: dup v6.2d, x2
        0x4e08_0c46,
        // ASM: mov v8.4s, v0.s[1]
        0x4e0c_0408,
        // ASM: str d2, [x1]
        0xfd00_0022,
        // ASM: str d3, [x1, #0x8]
        0xfd00_0423,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Vector), 32, "{}", verify_tsv(&v));
        assert_eq!(compared(&v, Fact::Store), 2, "{}", verify_tsv(&v));
    }
}

/// Packed float arithmetic over registers memory loaded.
///
/// The packed operations lift as the intrinsics that name them, whose
/// values the checker cannot read, while the sign operations, bit masks
/// over the registers, lift as expressions over them; the checker counts
/// what it cannot read instead of comparing it, and nothing else may
/// disagree.
#[test]
fn packed_float_agrees_with_the_emulator() {
    let words = [
        // ASM: ldr q0, [x0]
        0x3dc0_0000,
        // ASM: ldr q1, [x0, #0x10]
        0x3dc0_0401,
        // ASM: fadd v2.4s, v0.4s, v1.4s
        0x4e21_d402,
        // ASM: fabs v3.4s, v2.4s
        0x4ea0_f843,
        // ASM: fmul v4.2d, v0.2d, v1.2d
        0x6e61_dc04,
        // ASM: fneg v5.2s, v2.2s
        0x2ea0_f845,
        // ASM: str q2, [x1]
        0x3d80_0022,
        // ASM: ret
        0xd65f_03c0,
    ];
    let p = image(&words);
    let a = Analysis::compute(&p);
    for seed in 1..=SEEDS {
        let v = verify(&p, &a, &[BASE], seed);
        let tsv = verify_tsv(&v);
        assert_eq!(v.checked, 1, "seed {seed}: {tsv}");
        assert!(v.mismatches.is_empty(), "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Vector].unreadable, 6, "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Store].unreadable, 1, "seed {seed}: {tsv}");
        assert_eq!(v.unreadable, 7, "seed {seed}: {tsv}");
    }
}

/// The NEON integer operations lift as the intrinsics that name them, over
/// registers memory loaded; as the packed float ones above, what the
/// checker cannot read is counted, and everything else agrees.
#[test]
fn neon_integer_agrees_with_the_emulator() {
    let words = [
        // ASM: ldr q0, [x0]
        0x3dc0_0000,
        // ASM: ldr q1, [x0, #0x10]
        0x3dc0_0401,
        // ASM: add v6.4s, v0.4s, v1.4s
        0x4ea1_8406,
        // ASM: sub v7.8h, v0.8h, v1.8h
        0x6e61_8407,
        // ASM: neg v8.16b, v0.16b
        0x6e20_b808,
        // ASM: abs v9.2d, v1.2d
        0x4ee0_b829,
        // ASM: str q6, [x1]
        0x3d80_0026,
        // ASM: ret
        0xd65f_03c0,
    ];
    let p = image(&words);
    let a = Analysis::compute(&p);
    for seed in 1..=SEEDS {
        let v = verify(&p, &a, &[BASE], seed);
        let tsv = verify_tsv(&v);
        assert_eq!(v.checked, 1, "seed {seed}: {tsv}");
        assert!(v.mismatches.is_empty(), "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Vector].unreadable, 6, "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Store].unreadable, 1, "seed {seed}: {tsv}");
    }
}

/// The `ld1` and `st1` block moves agree: the registers hold loads the
/// checker cannot read, while the base a post-indexed `ld1` advances is a
/// general register and compares.
#[test]
fn ld1_and_st1_agree_with_the_emulator() {
    let words = [
        // ASM: ld1 {v0.16b}, [x0], #16
        0x4cdf_7000,
        // ASM: ld1 {v1.16b, v2.16b}, [x0]
        0x4c40_a001,
        // ASM: st1 {v0.16b}, [x1]
        0x4c00_7020,
        // ASM: st1 {v1.16b, v2.16b}, [x1]
        0x4c00_a021,
        // ASM: ret
        0xd65f_03c0,
    ];
    let p = image(&words);
    let a = Analysis::compute(&p);
    for seed in 1..=SEEDS {
        let v = verify(&p, &a, &[BASE], seed);
        let tsv = verify_tsv(&v);
        assert_eq!(v.checked, 1, "seed {seed}: {tsv}");
        assert!(v.mismatches.is_empty(), "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Vector].unreadable, 3, "seed {seed}: {tsv}");
        assert_eq!(v.facts[&Fact::Store].unreadable, 3, "seed {seed}: {tsv}");
        assert_eq!(compared(&v, Fact::Register), 32, "seed {seed}: {tsv}");
    }
}

/// The vector `fmov` immediates are the constants their bits expand to,
/// compared at every register and through the two stores of them.
#[test]
fn fmov_vector_immediates_agree_with_the_emulator() {
    let words = [
        // ASM: fmov v0.2s, #1.00000000
        0x0f03_f600,
        // ASM: fmov v1.2d, #0.12500000
        0x6f02_f401,
        // ASM: fmov v2.4s, #-2.50000000
        0x4f04_f482,
        // ASM: str d0, [x1]
        0xfd00_0020,
        // ASM: str d1, [x1, #0x8]
        0xfd00_0421,
        // ASM: ret
        0xd65f_03c0,
    ];
    for v in agrees(&words, 1) {
        assert_eq!(compared(&v, Fact::Vector), 32, "{}", verify_tsv(&v));
        assert_eq!(compared(&v, Fact::Store), 2, "{}", verify_tsv(&v));
    }
}

/// Pointer authentication and branch targets change no value.
///
/// A frame built under `paciasp` and torn down under `autiasp`, around a
/// call to a function that opens with `bti c` and returns with `retaa`:
/// the frame record and the saved register land in their slots, and the
/// restores read them back.
#[test]
fn pac_prologue_and_epilogue_agree_with_the_emulator() {
    let words = [
        // ASM: paciasp
        0xd503_233f,
        // ASM: stp x29, x30, [sp, #-0x20]!
        0xa9be_7bfd,
        // ASM: mov x29, sp
        0x9100_03fd,
        // ASM: str x19, [sp, #0x10]
        0xf900_0bf3,
        // ASM: mov x19, x0
        0xaa00_03f3,
        // ASM: bl 0x2c
        0x9400_0006,
        // ASM: add x0, x0, x19
        0x8b13_0000,
        // ASM: ldr x19, [sp, #0x10]
        0xf940_0bf3,
        // ASM: ldp x29, x30, [sp], #0x20
        0xa8c2_7bfd,
        // ASM: autiasp
        0xd503_23bf,
        // ASM: ret
        0xd65f_03c0,
        // ASM: bti c
        0xd503_245f,
        // ASM: add x0, x0, #0x1
        0x9100_0400,
        // ASM: retaa
        0xd65f_0bff,
    ];
    for v in agrees(&words, 2) {
        assert_eq!(compared(&v, Fact::Slot), 3, "{}", verify_tsv(&v));
    }
    let p = image(&words);
    let a = Analysis::compute(&p);
    let callee = BASE + 0x2c;
    assert!(
        a.function(callee).is_some(),
        "the call's target is a function"
    );
    let v = verify(&p, &a, &[callee], 1);
    assert_eq!(v.checked, 1, "{}", verify_tsv(&v));
    assert!(v.mismatches.is_empty(), "{}", verify_tsv(&v));
}

/// The scalar `dup` (`mov s0, v1.s[1]`) is one lane, the bits above it
/// clear, in the lifter as in the emulator; both once replicated the lane
/// as the vector form does.
#[test]
fn scalar_dup_agrees_with_the_emulator() {
    let words = [
        // ASM: mov s0, v1.s[1]
        0x5e0c_0420,
        // ASM: mov h2, v3.h[2]
        0x5e0a_0462,
        // ASM: fmov x0, d0
        0x9e66_0000,
        // ASM: fmov x1, d2
        0x9e66_0041,
        // ASM: add x0, x0, x1
        0x8b01_0000,
        // ASM: ret
        0xd65f_03c0,
    ];
    agrees(&words, 1);
    let p = image(&words);
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::decompile::decompile(
        &p,
        &a,
        &borer_engine::analysis::Overlay::default(),
        BASE,
    )
    .unwrap_or_default();
    assert!(
        text.contains("return ((uint64_t)v1 >> 32) + (((uint64_t)v3 >> 0x20) & 0xffff);"),
        "{text}"
    );
}
