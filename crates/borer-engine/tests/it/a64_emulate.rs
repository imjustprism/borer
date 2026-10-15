//! The arm64 emulator.
//!
//! Words assembled by LLVM (`clang --target=aarch64-linux-gnu`, linked by
//! `ld.lld` where an address matters) and checked against
//! `llvm-objdump` — the scalar float and vector ones hand-encoded from the
//! Arm ARM and checked against the decoder —
//! run in [`Machine`] from a raw arm64 image: a table of short routines
//! with the registers set before and the registers, memory and vector
//! registers expected after; the flag truth tables of the adds, subtracts
//! and conditional compares; every way a run stops; an XOR decryption loop
//! end to end, alone and through the `emulate` and `run` surfaces; and
//! random words, which run to a stop without a panic.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::emulate::a64::Machine;
use borer_engine::emulate::{Stop, fill_byte};
use borer_engine::program::{Arch, Program, Section};

/// Where every routine is placed and run from.
const BASE: u64 = 0x1_0000;

/// Where [`DATA`] is planted before each routine runs.
const DATA_AT: u64 = 0x3_0000;

/// The bytes the loads read: a doubleword, a doubleword whose bytes have
/// their top bits set, and eight rising bytes; zeros follow.
const DATA: [u8; 24] = [
    0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe, 0xff, 0xff, 0xff,
    0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
];

/// Bytes planted at [`DATA_AT`]: [`DATA`], then zeros a store can be read
/// back from.
const PLANTED: usize = 64;

/// The stack pointer a run starts with.
const SP: u64 = 0x7fff_0000_0000;

/// What the link register holds when a run starts.
const RETURN_TO: u64 = 0x7fff_ffff_f000;

/// The return every short routine ends with.
// ASM: ret
const RET: u32 = 0xd65f_03c0;

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

/// A machine over `p` with [`DATA`] planted.
///
/// # Arguments
///
/// * `p` - The image.
fn machine(p: &Program) -> Machine<'_> {
    let mut m = Machine::new(p, 10_000).expect("an arm64 machine");
    for (at, k) in (DATA_AT..).zip(0..PLANTED) {
        m.poke(at, DATA.get(k).copied().unwrap_or(0));
    }
    m
}

/// One routine of the table: its words, the registers set before it runs,
/// and what it leaves.
struct Case {
    /// The routine's name, for a failure message.
    name: &'static str,
    /// The routine, run from [`BASE`]; it returns.
    words: &'static [u32],
    /// Registers set before the run, by name.
    set: &'static [(&'static str, u64)],
    /// Registers expected after it, by name.
    want: &'static [(&'static str, u64)],
    /// Bytes expected in memory after it, by address.
    mem: &'static [(u64, &'static [u8])],
    /// `v` registers expected after it, by number.
    vregs: &'static [(usize, u128)],
}

/// The routines, each one area of the instruction set.
const CASES: &[Case] = &[
    Case {
        name: "movk",
        words: &[
            // ASM: mov x0, #0x1234000000000000
            0xd2e2_4680,
            // ASM: movk x0, #0x5678, lsl #32
            0xf2ca_cf00,
            // ASM: movk x0, #0x9abc, lsl #16
            0xf2b3_5780,
            // ASM: movk x0, #0xdef0
            0xf29b_de00,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[],
        want: &[("x0", 0x1234_5678_9abc_def0)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "wide_w",
        words: &[
            // ASM: mov w1, #-0x1
            0x1280_0001,
            // ASM: mov x2, #-0x1
            0x9280_0002,
            // ASM: movk w3, #0x1, lsl #16
            0x72a0_0023,
            // ASM: mov w4, #-0x10000
            0x52bf_ffe4,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x3", 0xffff_ffff_0000_ffff)],
        want: &[
            ("x1", 0xffff_ffff),
            ("x2", 0xffff_ffff_ffff_ffff),
            ("x3", 0x1_ffff),
            ("x4", 0xffff_0000),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "wzero",
        words: &[
            // ASM: add w0, w0, #0x1
            0x1100_0400,
            // ASM: sub w4, w5, #0x1
            0x5100_04a4,
            // ASM: orr w6, wzr, #0x80000000
            0x3201_03e6,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x0", 0xffff_ffff_ffff_ffff), ("x5", 0x0)],
        want: &[("x0", 0x0), ("x4", 0xffff_ffff), ("x6", 0x8000_0000)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "extend",
        words: &[
            // ASM: add x0, x1, w2, sxtw #2
            0x8b22_c820,
            // ASM: add x4, x1, w3, uxtw
            0x8b23_4024,
            // ASM: add x5, sp, #0x10
            0x9100_43e5,
            // ASM: sub x6, x1, w7, sxtb
            0xcb27_8026,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x1000),
            ("x2", 0xffff_ffff_ffff_fffe),
            ("x3", 0xffff_ffff_0000_0010),
            ("x7", 0x80),
        ],
        want: &[
            ("x0", 0xff8),
            ("x4", 0x1010),
            ("x5", 0x7fff_0000_0010),
            ("x6", 0x1080),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "shifted",
        words: &[
            // ASM: eor x0, x1, x2, ror #8
            0xcac2_2020,
            // ASM: and w3, w4, w5, lsr #4
            0xa45_1083,
            // ASM: bic x6, x7, x8, asr #63
            0x8aa8_fce6,
            // ASM: add w9, w4, w5, lsl #20
            0xb05_5089,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x1122_3344_5566_7788),
            ("x2", 0xff),
            ("x4", 0xf0f0_f0f0),
            ("x5", 0xff00),
            ("x7", 0xffff_ffff_ffff_ffff),
            ("x8", 0x8000_0000_0000_0000),
        ],
        want: &[
            ("x0", 0xee22_3344_5566_7788),
            ("x3", 0xf0),
            ("x6", 0x0),
            ("x9", 0xe0f0_f0f0),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "logimm",
        words: &[
            // ASM: and x0, x1, #0xff00ff00ff00ff00
            0x9208_9c20,
            // ASM: orr w2, wzr, #0x1
            0x3200_03e2,
            // ASM: eor x3, x4, #0x5555555555555555
            0xd200_f083,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x1", 0x1234_5678_9abc_def0), ("x2", 0x99), ("x4", 0x0)],
        want: &[
            ("x0", 0x1200_5600_9a00_de00),
            ("x2", 0x1),
            ("x3", 0x5555_5555_5555_5555),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "ands",
        words: &[
            // ASM: ands w0, w1, w2
            0x6a02_0020,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x8000_0000),
            ("x2", 0xffff_ffff),
            ("nzcv", 0x3000_0000),
        ],
        want: &[("x0", 0x8000_0000), ("nzcv", 0x8000_0000)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "bics",
        words: &[
            // ASM: bics x0, x1, x2
            0xea22_0020,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0x7),
            ("x1", 0xff),
            ("x2", 0xff),
            ("nzcv", 0x2000_0000),
        ],
        want: &[("x0", 0x0), ("nzcv", 0x4000_0000)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "bitfield",
        words: &[
            // ASM: lsl x0, x1, #3
            0xd37d_f020,
            // ASM: lsr w2, w3, #4
            0x5304_7c62,
            // ASM: asr x4, x5, #60
            0x937c_fca4,
            // ASM: ubfx x6, x7, #8, #12
            0xd348_4ce6,
            // ASM: sbfx w8, w9, #4, #8
            0x1304_2d28,
            // ASM: bfi x10, x11, #16, #8
            0xb370_1d6a,
            // ASM: bfxil w12, w13, #8, #8
            0x3308_3dac,
            // ASM: sxtb x14, w15
            0x9340_1dee,
            // ASM: uxth w16, w17
            0x5300_3e30,
            // ASM: sbfiz x18, x15, #4, #8
            0x937c_1df2,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x123_4567_89ab_cdef),
            ("x3", 0xf000_0000),
            ("x5", 0x8000_0000_0000_0000),
            ("x7", 0x1234_5678),
            ("x9", 0xab0),
            ("x10", 0xffff_ffff_ffff_ffff),
            ("x11", 0x5a),
            ("x12", 0xffff_ffff),
            ("x13", 0x1234),
            ("x15", 0x80),
            ("x17", 0xffff_8001),
        ],
        want: &[
            ("x0", 0x91a_2b3c_4d5e_6f78),
            ("x2", 0xf00_0000),
            ("x4", 0xffff_ffff_ffff_fff8),
            ("x6", 0x456),
            ("x8", 0xffff_ffab),
            ("x10", 0xffff_ffff_ff5a_ffff),
            ("x12", 0xffff_ff12),
            ("x14", 0xffff_ffff_ffff_ff80),
            ("x16", 0x8001),
            ("x18", 0xffff_ffff_ffff_f800),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "extr",
        words: &[
            // ASM: extr x0, x1, x2, #0x10
            0x93c2_4020,
            // ASM: ror w3, w4, #0x8
            0x1384_2083,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x1122_3344_5566_7788),
            ("x2", 0x99aa_bbcc_ddee_ff00),
            ("x4", 0x1234_5678),
        ],
        want: &[("x0", 0x7788_99aa_bbcc_ddee), ("x3", 0x7812_3456)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "varshift",
        words: &[
            // ASM: lsl x0, x1, x2
            0x9ac2_2020,
            // ASM: lsr w3, w4, w5
            0x1ac5_2483,
            // ASM: asr x6, x7, x8
            0x9ac8_28e6,
            // ASM: ror w9, w10, w11
            0x1acb_2d49,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x1),
            ("x2", 0x41),
            ("x4", 0x8000_0000),
            ("x5", 0x21),
            ("x7", 0x8000_0000_0000_0000),
            ("x8", 0x4),
            ("x10", 0x1234_5678),
            ("x11", 0x24),
        ],
        want: &[
            ("x0", 0x2),
            ("x3", 0x4000_0000),
            ("x6", 0xf800_0000_0000_0000),
            ("x9", 0x8123_4567),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "mul",
        words: &[
            // ASM: mul x0, x1, x2
            0x9b02_7c20,
            // ASM: madd w3, w4, w5, w6
            0x1b05_1883,
            // ASM: msub x7, x8, x9, x10
            0x9b09_a907,
            // ASM: smull x11, w12, w13
            0x9b2d_7d8b,
            // ASM: umull x14, w15, w16
            0x9bb0_7dee,
            // ASM: smulh x17, x19, x20
            0x9b54_7e71,
            // ASM: umulh x21, x22, x23
            0x9bd7_7ed5,
            // ASM: smnegl x24, w13, w16
            0x9b30_fdb8,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x1_0000_0001),
            ("x2", 0x10),
            ("x4", 0x7),
            ("x5", 0x6),
            ("x6", 0x64),
            ("x8", 0x3),
            ("x9", 0x4),
            ("x10", 0x32),
            ("x12", 0xffff_fffd),
            ("x13", 0x7),
            ("x15", 0xffff_ffff),
            ("x16", 0x2),
            ("x19", 0x8000_0000_0000_0000),
            ("x20", 0x2),
            ("x22", 0xffff_ffff_ffff_ffff),
            ("x23", 0xffff_ffff_ffff_ffff),
        ],
        want: &[
            ("x0", 0x10_0000_0010),
            ("x3", 0x8e),
            ("x7", 0x26),
            ("x11", 0xffff_ffff_ffff_ffeb),
            ("x14", 0x1_ffff_fffe),
            ("x17", 0xffff_ffff_ffff_ffff),
            ("x21", 0xffff_ffff_ffff_fffe),
            ("x24", 0xffff_ffff_ffff_fff2),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "div",
        words: &[
            // ASM: udiv x0, x1, x2
            0x9ac2_0820,
            // ASM: sdiv w3, w4, w5
            0x1ac5_0c83,
            // ASM: sdiv x6, x7, x8
            0x9ac8_0ce6,
            // ASM: sdiv w9, w10, w11
            0x1acb_0d49,
            // ASM: udiv w12, w13, w14
            0x1ace_09ac,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0x55),
            ("x1", 0x64),
            ("x2", 0x0),
            ("x3", 0x55),
            ("x4", 0xffff_fff9),
            ("x5", 0x0),
            ("x7", 0x8000_0000_0000_0000),
            ("x8", 0xffff_ffff_ffff_ffff),
            ("x10", 0xffff_fff9),
            ("x11", 0x2),
            ("x13", 0x7),
            ("x14", 0x2),
        ],
        want: &[
            ("x0", 0x0),
            ("x3", 0x0),
            ("x6", 0x8000_0000_0000_0000),
            ("x9", 0xffff_fffd),
            ("x12", 0x3),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "bits",
        words: &[
            // ASM: clz x0, x1
            0xdac0_1020,
            // ASM: clz w2, w3
            0x5ac0_1062,
            // ASM: cls x4, x5
            0xdac0_14a4,
            // ASM: cls w6, w7
            0x5ac0_14e6,
            // ASM: rbit w8, w9
            0x5ac0_0128,
            // ASM: rev x10, x11
            0xdac0_0d6a,
            // ASM: rev16 w12, w13
            0x5ac0_05ac,
            // ASM: rev32 x14, x15
            0xdac0_09ee,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0x55),
            ("x1", 0x1),
            ("x3", 0x0),
            ("x5", 0x0),
            ("x7", 0xffff_0000),
            ("x9", 0x1),
            ("x11", 0x102_0304_0506_0708),
            ("x13", 0x1122_3344),
            ("x15", 0x102_0304_0506_0708),
        ],
        want: &[
            ("x0", 0x3f),
            ("x2", 0x20),
            ("x4", 0x3f),
            ("x6", 0xf),
            ("x8", 0x8000_0000),
            ("x10", 0x807_0605_0403_0201),
            ("x12", 0x2211_4433),
            ("x14", 0x403_0201_0807_0605),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "csel",
        words: &[
            // ASM: csel x0, x1, x2, eq
            0x9a82_0020,
            // ASM: csinc w3, w4, w5, ne
            0x1a85_1483,
            // ASM: cset x6, hs
            0x9a9f_37e6,
            // ASM: csetm w7, lt
            0x5a9f_a3e7,
            // ASM: cneg x8, x9, mi
            0xda89_5528,
            // ASM: csinv x10, x11, x12, gt
            0xda8c_c16a,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("nzcv", 0x6000_0000),
            ("x1", 0x1),
            ("x2", 0x2),
            ("x4", 0x4),
            ("x5", 0x5),
            ("x6", 0x66),
            ("x7", 0x77),
            ("x9", 0x9),
            ("x11", 0xb),
            ("x12", 0xc),
        ],
        want: &[
            ("x0", 0x1),
            ("x3", 0x6),
            ("x6", 0x1),
            ("x7", 0x0),
            ("x8", 0x9),
            ("x10", 0xffff_ffff_ffff_fff3),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "adr",
        words: &[
            // ASM: adr x0, .+0x8
            0x1000_0040,
            // ASM: ret
            0xd65f_03c0,
            // ASM: .word 0x00000000 (data)
            0x0,
        ],
        set: &[],
        want: &[("x0", 0x1_0008)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "loads",
        words: &[
            // ASM: ldr x0, [x1]
            0xf940_0020,
            // ASM: ldr w2, [x1, #0x4]
            0xb940_0422,
            // ASM: ldrsb x3, [x1, #0x8]
            0x3980_2023,
            // ASM: ldrsb w4, [x1, #0x8]
            0x39c0_2024,
            // ASM: ldrsh w5, [x1, #0xa]
            0x79c0_1425,
            // ASM: ldrsw x6, [x1, #0xc]
            0xb980_0c26,
            // ASM: ldrh w8, [x1, x7, lsl #1]
            0x7867_7828,
            // ASM: ldr x11, [x10, w9, sxtw #3]
            0xf869_d94b,
            // ASM: ldrb w12, [x1, #0x10]
            0x3940_402c,
            // ASM: ldur w13, [x10, #-0x4]
            0xb85f_c14d,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x3_0000),
            ("x7", 0x2),
            ("x9", 0xffff_ffff),
            ("x10", 0x3_0008),
        ],
        want: &[
            ("x0", 0x1122_3344_5566_7788),
            ("x2", 0x1122_3344),
            ("x3", 0xffff_ffff_ffff_ff80),
            ("x4", 0xffff_ff80),
            ("x5", 0xffff_8001),
            ("x6", 0xffff_ffff_ffff_fffe),
            ("x8", 0x3344),
            ("x11", 0x1122_3344_5566_7788),
            ("x12", 0x10),
            ("x13", 0x1122_3344),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "stores",
        words: &[
            // ASM: str x2, [x1]
            0xf900_0022,
            // ASM: strb w3, [x1, #0x8]
            0x3900_2023,
            // ASM: strh w2, [x1, #0xa]
            0x7900_1422,
            // ASM: stur w2, [x1, #0xc]
            0xb800_c022,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x3_0020),
            ("x2", 0x1122_3344_5566_7788),
            ("x3", 0xa5),
        ],
        want: &[],
        mem: &[(
            0x3_0020,
            &[
                0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0xa5, 0x00, 0x88, 0x77, 0x88, 0x77,
                0x66, 0x55,
            ],
        )],
        vregs: &[],
    },
    Case {
        name: "pre_post",
        words: &[
            // ASM: ldr x0, [x1, #0x8]!
            0xf840_8c20,
            // ASM: ldr x2, [x1], #0x8
            0xf840_8422,
            // ASM: str w4, [x3, #0x4]!
            0xb800_4c64,
            // ASM: str w4, [x3], #-0x4
            0xb81f_c464,
            // ASM: ldrb w5, [x1], #0x1
            0x3840_1425,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x1", 0x3_0000), ("x3", 0x3_0020), ("x4", 0xdead_beef)],
        want: &[
            ("x0", 0xffff_fffe_8001_ff80),
            ("x1", 0x3_0011),
            ("x2", 0xffff_fffe_8001_ff80),
            ("x3", 0x3_0020),
            ("x5", 0x10),
        ],
        mem: &[(0x3_0024, &[0xef, 0xbe, 0xad, 0xde])],
        vregs: &[],
    },
    Case {
        name: "pairs",
        words: &[
            // ASM: stp x2, x3, [sp, #-0x10]!
            0xa9bf_0fe2,
            // ASM: ldp x4, x5, [sp], #0x10
            0xa8c1_17e4,
            // ASM: ldp w6, w7, [x8]
            0x2940_1d06,
            // ASM: ldpsw x9, x10, [x8, #0x8]
            0x6941_2909,
            // ASM: stp w2, w3, [x8, #0x20]
            0x2904_0d02,
            // ASM: ldnp x11, x12, [x8]
            0xa840_310b,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x2", 0x2222), ("x3", 0x3333), ("x8", 0x3_0000)],
        want: &[
            ("sp", 0x7fff_0000_0000),
            ("x4", 0x2222),
            ("x5", 0x3333),
            ("x6", 0x5566_7788),
            ("x7", 0x1122_3344),
            ("x9", 0xffff_ffff_8001_ff80),
            ("x10", 0xffff_ffff_ffff_fffe),
            ("x11", 0x1122_3344_5566_7788),
            ("x12", 0xffff_fffe_8001_ff80),
        ],
        mem: &[
            (0x3_0020, &[0x22, 0x22, 0x00, 0x00, 0x33, 0x33, 0x00, 0x00]),
            (
                0x7ffe_ffff_fff0,
                &[
                    0x22, 0x22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33, 0x33, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00,
                ],
            ),
        ],
        vregs: &[],
    },
    Case {
        name: "literal",
        words: &[
            // ASM: ldr x0, .+0x10
            0x5800_0080,
            // ASM: ldrsw x1, .+0x14
            0x9800_00a1,
            // ASM: ldr w2, .+0x8
            0x1800_0042,
            // ASM: ret
            0xd65f_03c0,
            // ASM: .word 0x55667788 (data)
            0x5566_7788,
            // ASM: .word 0x11223344 (data)
            0x1122_3344,
            // ASM: .word 0x80000000 (data)
            0x8000_0000,
        ],
        set: &[],
        want: &[
            ("x0", 0x1122_3344_5566_7788),
            ("x1", 0xffff_ffff_8000_0000),
            ("x2", 0x5566_7788),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "exclusive",
        words: &[
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
        ],
        set: &[
            ("x1", 0x3_0000),
            ("x2", 0x5),
            ("x4", 0x5),
            ("x5", 0x3_0020),
            ("x9", 0x5),
        ],
        want: &[
            ("x0", 0x1122_3344_5566_7789),
            ("x2", 0x0),
            ("x3", 0x5566_7789),
            ("x4", 0x0),
            ("x6", 0x1122_3344_5566_7789),
            ("x7", 0x1122_3344_5566_7789),
            ("x8", 0xffff_fffe_8001_ff80),
            ("x9", 0x0),
        ],
        mem: &[
            (0x3_0000, &[0x89, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]),
            (
                0x3_0020,
                &[
                    0x89, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe,
                    0xff, 0xff, 0xff,
                ],
            ),
        ],
        vregs: &[],
    },
    Case {
        name: "atomics",
        words: &[
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
            // ASM: ldsmax w0, w10, [x11]
            0xb820_416a,
            // ASM: ldumin w13, w14, [x11]
            0xb82d_716e,
            // ASM: ldaddb w0, w15, [x2]
            0x3820_004f,
            // ASM: cas x16, x17, [x4]
            0xc8b0_7c91,
            // ASM: casal x19, x20, [x4]
            0xc8f3_fc94,
            // ASM: casb w21, w22, [x2]
            0x8b5_7c56,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0x1),
            ("x2", 0x3_0000),
            ("x4", 0x3_0010),
            ("x7", 0xff),
            ("x11", 0x3_0008),
            ("x13", 0x0),
            ("x16", 0x1),
            ("x17", 0x77),
            ("x19", 0x5),
            ("x20", 0x99),
            ("x21", 0x8b),
            ("x22", 0x42),
        ],
        want: &[
            ("x1", 0x1122_3344_5566_7788),
            ("x3", 0x1122_3344_5566_7789),
            ("x5", 0x8070_6050_4030_2010),
            ("x6", 0x8070_6050_4030_2000),
            ("x8", 0x8070_6050_4030_20ff),
            ("x9", 0x8070_6050_4030_2000),
            ("x10", 0x8001_ff80),
            ("x14", 0x1),
            ("x15", 0x8a),
            ("x16", 0x1),
            ("x19", 0x77),
            ("x21", 0x8b),
        ],
        mem: &[(
            0x3_0000,
            &[
                0x42, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00, 0x00, 0x00, 0x00, 0xfe, 0xff,
                0xff, 0xff, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            ],
        )],
        vregs: &[],
    },
    Case {
        name: "vector",
        words: &[
            // ASM: fmov d0, x1
            0x9e67_0020,
            // ASM: fmov x2, d0
            0x9e66_0002,
            // ASM: fmov s1, w3
            0x1e27_0061,
            // ASM: fmov w4, s1
            0x1e26_0024,
            // ASM: fmov d2, #1.00000000
            0x1e6e_1002,
            // ASM: fmov s3, #-2.50000000
            0x1e30_9003,
            // ASM: movi v4.16b, #0xff
            0x4f07_e7e4,
            // ASM: movi d5, #0xff00ff00ff00ff00
            0x2f05_e545,
            // ASM: movi v6.4s, #0x1, lsl #8
            0x4f00_2426,
            // ASM: mvni v7.2s, #0x1
            0x2f00_0427,
            // ASM: ldr q8, [x5]
            0x3dc0_00a8,
            // ASM: str q8, [x6]
            0x3d80_00c8,
            // ASM: ldp d9, d10, [x5]
            0x6d40_28a9,
            // ASM: ldr s11, [x5, #0x4]
            0xbd40_04ab,
            // ASM: movi v12.16b, #0xff
            0x4f07_e7ec,
            // ASM: fmov d12, x2
            0x9e67_004c,
            // ASM: movi v13.16b, #0xff
            0x4f07_e7ed,
            // ASM: ldr d13, [x5]
            0xfd40_00ad,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x1", 0x3ff0_0000_0000_0000),
            ("x3", 0x4049_0fdb),
            ("x5", 0x3_0000),
            ("x6", 0x3_0020),
        ],
        want: &[("x2", 0x3ff0_0000_0000_0000), ("x4", 0x4049_0fdb)],
        mem: &[(
            0x3_0020,
            &[
                0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe, 0xff,
                0xff, 0xff,
            ],
        )],
        vregs: &[
            (0, 0x3ff0_0000_0000_0000),
            (1, 0x4049_0fdb),
            (2, 0x3ff0_0000_0000_0000),
            (3, 0xc020_0000),
            (4, 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff),
            (5, 0xff00_ff00_ff00_ff00),
            (6, 0x100_0000_0100_0000_0100_0000_0100),
            (7, 0xffff_fffe_ffff_fffe),
            (8, 0xffff_fffe_8001_ff80_1122_3344_5566_7788),
            (9, 0x1122_3344_5566_7788),
            (10, 0xffff_fffe_8001_ff80),
            (11, 0x1122_3344),
            (12, 0x3ff0_0000_0000_0000),
            (13, 0x1122_3344_5566_7788),
        ],
    },
    Case {
        name: "float",
        words: &[
            // ASM: fmov d0, x0
            0x9e67_0000,
            // ASM: scvtf d1, x1
            0x9e62_0021,
            // ASM: scvtf s2, w2
            0x1e22_0042,
            // ASM: ucvtf d3, x1
            0x9e63_0023,
            // ASM: fadd d4, d0, d1
            0x1e61_2804,
            // ASM: fmul d5, d0, d0
            0x1e60_0805,
            // ASM: fdiv d6, d0, d0
            0x1e60_1806,
            // ASM: fsub d7, d1, d0
            0x1e60_3827,
            // ASM: fmul d9, d0, d0
            0x1e60_0809,
            // ASM: fsqrt d9, d9
            0x1e61_c129,
            // ASM: fneg d10, d0
            0x1e61_400a,
            // ASM: fabs d11, d10
            0x1e60_c14b,
            // ASM: fabs s12, s2
            0x1e20_c04c,
            // ASM: fneg s13, s2
            0x1e21_404d,
            // ASM: fcvt s14, d0
            0x1e62_400e,
            // ASM: fcvt d15, s14
            0x1e22_c1cf,
            // ASM: fcvt h20, d0
            0x1e63_c014,
            // ASM: fcvt s24, h20
            0x1ee2_4298,
            // ASM: fcvt d25, h20
            0x1ee2_c299,
            // ASM: fcvt h28, d7
            0x1e63_c0fc,
            // ASM: fcvtzs w16, d0
            0x1e78_0010,
            // ASM: fcvtzs x17, d10
            0x9e78_0151,
            // ASM: fcvtzu w18, s2
            0x1e39_0052,
            // ASM: scvtf d19, w1, #0x4
            0x1e42_f033,
            // ASM: scvtf d21, wzr
            0x1e62_03f5,
            // ASM: fdiv d22, d0, d21
            0x1e75_1816,
            // ASM: fdiv d23, d21, d21
            0x1e75_1ab7,
            // ASM: fcvtzs w19, d22
            0x1e78_02d3,
            // ASM: fcvtzs w20, d23
            0x1e78_02f4,
            // ASM: fadd s30, s2, s2
            0x1e22_285e,
            // ASM: fdiv s29, s2, s2
            0x1e22_185d,
            // ASM: fcmp d0, d1
            0x1e61_2000,
            // ASM: mrs x9, NZCV
            0xd53b_4209,
            // ASM: fcmp d1, d0
            0x1e60_2020,
            // ASM: mrs x10, NZCV
            0xd53b_420a,
            // ASM: fcmp d0, #0.0
            0x1e60_2008,
            // ASM: mrs x11, NZCV
            0xd53b_420b,
            // ASM: fcmpe d1, d0
            0x1e60_2030,
            // ASM: mrs x12, NZCV
            0xd53b_420c,
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
            // ASM: fcmp d0, d1
            0x1e61_2000,
            // ASM: fcsel d26, d0, d1, gt
            0x1e61_cc1a,
            // ASM: fcsel d27, d0, d1, mi
            0x1e61_4c1b,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0x4004_0000_0000_0000),
            ("x1", 0xffff_ffff_ffff_fff9),
            ("x2", 0x3),
        ],
        want: &[
            ("x9", 0x2000_0000),
            ("x10", 0x8000_0000),
            ("x11", 0x2000_0000),
            ("x12", 0x8000_0000),
            ("x13", 0x8000_0000),
            ("x14", 0xf000_0000),
            ("x16", 0x2),
            ("x17", 0xffff_ffff_ffff_fffe),
            ("x18", 0x3),
            ("x19", 0x7fff_ffff),
            ("x20", 0x0),
        ],
        mem: &[],
        vregs: &[
            (0, 0x4004_0000_0000_0000),
            (1, 0xc01c_0000_0000_0000),
            (2, 0x4040_0000),
            (3, 0x43f0_0000_0000_0000),
            (4, 0xc012_0000_0000_0000),
            (5, 0x4019_0000_0000_0000),
            (6, 0x3ff0_0000_0000_0000),
            (7, 0xc023_0000_0000_0000),
            (9, 0x4004_0000_0000_0000),
            (10, 0xc004_0000_0000_0000),
            (11, 0x4004_0000_0000_0000),
            (12, 0x4040_0000),
            (13, 0xc040_0000),
            (14, 0x4020_0000),
            (15, 0x4004_0000_0000_0000),
            (20, 0x4100),
            (24, 0x4020_0000),
            (25, 0x4004_0000_0000_0000),
            (28, 0xc8c0),
            (19, 0xbfdc_0000_0000_0000),
            (21, 0x0),
            (22, 0x7ff0_0000_0000_0000),
            (26, 0x4004_0000_0000_0000),
            (27, 0xc01c_0000_0000_0000),
            (29, 0x3f80_0000),
            (30, 0x40c0_0000),
        ],
    },
    Case {
        name: "neon",
        words: &[
            // ASM: fmov d0, x0
            0x9e67_0000,
            // ASM: fmov d1, x1
            0x9e67_0021,
            // ASM: and v2.16b, v0.16b, v1.16b
            0x4e21_1c02,
            // ASM: orr v3.16b, v0.16b, v1.16b
            0x4ea1_1c03,
            // ASM: eor v4.16b, v0.16b, v1.16b
            0x6e21_1c04,
            // ASM: bic v5.16b, v0.16b, v1.16b
            0x4e61_1c05,
            // ASM: dup v6.2d, x4
            0x4e08_0c86,
            // ASM: orr v6.4s, v6.4s, #0x1
            0x4f00_1426,
            // ASM: dup v7.2d, x4
            0x4e08_0c87,
            // ASM: bic v7.4s, v7.4s, #0x2
            0x6f00_1447,
            // ASM: dup v8.2d, x2
            0x4e08_0c48,
            // ASM: dup v9.4s, w2
            0x4e04_0c49,
            // ASM: dup v10.16b, w3
            0x4e01_0c6a,
            // ASM: mov v11.2d, v8.d[1]
            0x4e18_050b,
            // ASM: mov v12.4s, v9.s[3]
            0x4e1c_052c,
            // ASM: mov v8.4s, v0.s[1]
            0x4e0c_0408,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0xff00_ff00_ff00_ff00),
            ("x1", 0x0f0f_0f0f_0f0f_0f0f),
            ("x2", 0x8899_aabb_ccdd_eeff),
            ("x3", 0xab),
            ("x4", 0x2222_2222_2222_2222),
        ],
        want: &[],
        mem: &[],
        vregs: &[
            (0, 0xff00_ff00_ff00_ff00),
            (1, 0x0f0f_0f0f_0f0f_0f0f),
            (2, 0x0f00_0f00_0f00_0f00),
            (3, 0xff0f_ff0f_ff0f_ff0f),
            (4, 0xf00f_f00f_f00f_f00f),
            (5, 0xf000_f000_f000_f000),
            (6, 0x2222_2223_2222_2223_2222_2223_2222_2223),
            (7, 0x2222_2220_2222_2220_2222_2220_2222_2220),
            (8, 0xff00_ff00_ff00_ff00_ff00_ff00_ff00_ff00),
            (9, 0xccdd_eeff_ccdd_eeff_ccdd_eeff_ccdd_eeff),
            (10, 0xabab_abab_abab_abab_abab_abab_abab_abab),
            (11, 0x8899_aabb_ccdd_eeff_8899_aabb_ccdd_eeff),
            (12, 0xccdd_eeff_ccdd_eeff_ccdd_eeff_ccdd_eeff),
        ],
    },
    Case {
        name: "system",
        words: &[
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
        ],
        set: &[
            ("tpidr_el0", 0x7000),
            ("nzcv", 0x9000_0000),
            ("x16", 0x8888),
            ("x3", 0x6000_0000),
        ],
        want: &[
            ("x0", 0x7000),
            ("x1", 0x8888),
            ("x2", 0x9000_0000),
            ("nzcv", 0x6000_0000),
            ("tpidr_el0", 0x8888),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "pac",
        words: &[
            // ASM: paciasp
            0xd503_233f,
            // ASM: pacia x0, x1
            0xdac1_0020,
            // ASM: autia x0, x1
            0xdac1_1020,
            // ASM: xpaci x0
            0xdac1_43e0,
            // ASM: bti c
            0xd503_245f,
            // ASM: nop
            0xd503_201f,
            // ASM: dmb ish
            0xd503_3bbf,
            // ASM: isb
            0xd503_3fdf,
            // ASM: prfm pldl1keep, [x3]
            0xf980_0060,
            // ASM: ldraa x2, [x3, #0x8]!
            0xf820_1c62,
            // ASM: autiasp
            0xd503_23bf,
            // ASM: retaa
            0xd65f_0bff,
        ],
        set: &[("x0", 0x1234), ("x3", 0x3_0000)],
        want: &[
            ("x0", 0x1234),
            ("x2", 0xffff_fffe_8001_ff80),
            ("x3", 0x3_0008),
        ],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "branches",
        words: &[
            // ASM: cbz x0, .+0x8
            0xb400_0040,
            // ASM: mov x9, #0x1
            0xd280_0029,
            // ASM: cbnz x0, .+0xc
            0xb500_0060,
            // ASM: tbz w2, #0x4, .+0x8
            0x3620_0042,
            // ASM: tbnz w2, #0x4, .+0x8
            0x3720_0042,
            // ASM: mov x9, #0x2
            0xd280_0049,
            // ASM: subs x1, x1, #0x1
            0xf100_0421,
            // ASM: b.ne .-0x4
            0x54ff_ffe1,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x0", 0x0), ("x1", 0x5), ("x2", 0x10), ("x9", 0x0)],
        want: &[("x1", 0x0), ("x9", 0x0), ("nzcv", 0x6000_0000)],
        mem: &[],
        vregs: &[],
    },
    Case {
        name: "calls",
        words: &[
            // ASM: stp x29, x30, [sp, #-0x10]!
            0xa9bf_7bfd,
            // ASM: mov x29, sp
            0x9100_03fd,
            // ASM: bl .+0x14
            0x9400_0005,
            // ASM: adr x13, .+0x10
            0x1000_008d,
            // ASM: blr x13
            0xd63f_01a0,
            // ASM: ldp x29, x30, [sp], #0x10
            0xa8c1_7bfd,
            // ASM: ret
            0xd65f_03c0,
            // ASM: add x10, x10, #0x1
            0x9100_054a,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x10", 0x0)],
        want: &[
            ("x10", 0x2),
            ("x13", 0x1_001c),
            ("sp", 0x7fff_0000_0000),
            ("x29", 0x0),
            ("x30", 0x7fff_ffff_f000),
        ],
        mem: &[],
        vregs: &[],
    },
];

/// Every routine of the table returns and leaves the registers, memory and
/// vector registers the architecture says it does.
#[test]
fn routines_compute_what_the_architecture_says() {
    for c in CASES {
        let p = image(c.words);
        let mut m = machine(&p);
        for &(name, v) in c.set {
            assert!(m.set_register(name, v), "{}: {name} sets nothing", c.name);
        }
        let run = m.run(BASE);
        assert_eq!(run.stop, Stop::Returned, "{}: {run:?}", c.name);
        for &(name, v) in c.want {
            assert_eq!(m.register(name), Some(v), "{}: {name}", c.name);
        }
        for &(at, bytes) in c.mem {
            let got: Vec<Option<u8>> = (at..).take(bytes.len()).map(|a| m.byte_at(a)).collect();
            let want: Vec<Option<u8>> = bytes.iter().copied().map(Some).collect();
            assert_eq!(got, want, "{}: memory at {at:#x}", c.name);
        }
        for &(n, v) in c.vregs {
            assert_eq!(m.vregs().get(n).copied(), Some(v), "{}: v{n}", c.name);
        }
    }
}

/// `adds w0, w1, w2`.
// ASM: adds w0, w1, w2
const ADDS_W: u32 = 0x2b02_0020;
/// `adds x0, x1, x2`.
// ASM: adds x0, x1, x2
const ADDS_X: u32 = 0xab02_0020;
/// `subs w0, w1, w2`.
// ASM: subs w0, w1, w2
const SUBS_W: u32 = 0x6b02_0020;
/// `subs x0, x1, x2`.
// ASM: subs x0, x1, x2
const SUBS_X: u32 = 0xeb02_0020;
/// `adcs w0, w1, w2`.
// ASM: adcs w0, w1, w2
const ADCS_W: u32 = 0x3a02_0020;
/// `sbcs w0, w1, w2`.
// ASM: sbcs w0, w1, w2
const SBCS_W: u32 = 0x7a02_0020;
/// `ccmp x1, x2, #0x4, ne`: the compare's flags when Z is clear, else Z.
// ASM: ccmp x1, x2, #0x4, ne
const CCMP: u32 = 0xfa42_1024;
/// `ccmn w1, #0x3, #0x9, hs`: the add's flags when C is set, else N and V.
// ASM: ccmn w1, #0x3, #0x9, hs
const CCMN: u32 = 0x3a43_2829;

/// One flag case: the word, `x1`, `x2`, the flags before, `x0` after (or
/// `None` when the instruction writes no register) and the flags after.
type FlagRow = (u32, u64, u64, u64, Option<u64>, u64);

/// The negative flag, as `NZCV` holds it.
const N: u64 = 1 << 31;
/// The zero flag.
const Z: u64 = 1 << 30;
/// The carry flag.
const C: u64 = 1 << 29;
/// The overflow flag.
const V: u64 = 1 << 28;

/// The adds and subtracts set exactly the flags of `AddWithCarry`.
///
/// An add's carry is its carry out, a subtract's carry is not-borrow,
/// overflow is signed, and the carry in feeds `adcs` and `sbcs`; a
/// conditional compare takes the compare's flags when its condition holds
/// and its immediate flags when it does not.
#[test]
fn flags_follow_add_with_carry() {
    const M32: u64 = 0xffff_ffff;
    const M64: u64 = u64::MAX;
    const MIN64: u64 = 1 << 63;
    let rows: &[FlagRow] = &[
        (ADDS_W, 1, 2, 0, Some(3), 0),
        (ADDS_W, 0x7fff_ffff, 1, 0, Some(0x8000_0000), N | V),
        (ADDS_W, M32, 1, 0, Some(0), Z | C),
        (ADDS_W, 0x8000_0000, 0x8000_0000, 0, Some(0), Z | C | V),
        (ADDS_W, M32, M32, 0, Some(0xffff_fffe), N | C),
        (ADDS_X, MIN64 - 1, 1, 0, Some(MIN64), N | V),
        (ADDS_X, M64, 1, 0, Some(0), Z | C),
        (ADDS_X, MIN64, M64, 0, Some(MIN64 - 1), C | V),
        (SUBS_W, 5, 3, 0, Some(2), C),
        (SUBS_W, 3, 5, 0, Some(0xffff_fffe), N),
        (SUBS_W, 5, 5, 0, Some(0), Z | C),
        (SUBS_W, 0x8000_0000, 1, 0, Some(0x7fff_ffff), C | V),
        (SUBS_W, 0x7fff_ffff, M32, 0, Some(0x8000_0000), N | V),
        (SUBS_W, 0, 0, N | V, Some(0), Z | C),
        (SUBS_X, 0, 1, 0, Some(M64), N),
        (SUBS_X, MIN64, 1, 0, Some(MIN64 - 1), C | V),
        (ADCS_W, M32, 0, C, Some(0), Z | C),
        (ADCS_W, 1, 1, 0, Some(2), 0),
        (ADCS_W, 0x7fff_ffff, 0, C, Some(0x8000_0000), N | V),
        (SBCS_W, 5, 3, C, Some(2), C),
        (SBCS_W, 5, 3, 0, Some(1), C),
        (SBCS_W, 3, 3, 0, Some(M32), N),
        (SBCS_W, 0, 0, C, Some(0), Z | C),
        (CCMP, 5, 5, 0, None, Z | C),
        (CCMP, 3, 5, 0, None, N),
        (CCMP, 3, 5, Z, None, Z),
        (CCMN, 0xffff_fffd, 0, C, None, Z | C),
        (CCMN, 0x7fff_fffd, 0, C, None, N | V),
        (CCMN, 0xffff_fffd, 0, 0, None, N | V),
    ];
    for &(word, x1, x2, flags, x0, want) in rows {
        let p = image(&[word, RET]);
        let mut m = machine(&p);
        assert!(m.set_register("x0", 0x5a5a) && m.set_register("x1", x1));
        assert!(m.set_register("x2", x2) && m.set_register("nzcv", flags));
        let run = m.run(BASE);
        assert_eq!(run.stop, Stop::Returned, "{word:#010x}");
        let case = format!(
            "{word:#010x} on {x1:#x}, {x2:#x} with nzcv {:#x}",
            flags >> 28
        );
        assert_eq!(m.register("nzcv"), Some(want), "{case}");
        assert_eq!(m.register("x0"), Some(x0.unwrap_or(0x5a5a)), "{case}");
    }
}

/// Every way a run stops is named.
///
/// A run ends at the step budget, at a fault on a load or a fetch, on code
/// on the stack, on an instruction the machine does not model, at an exit
/// call, and at a requested stop.
#[test]
fn every_stop_is_named() {
    /// Steps the budget case is given.
    const BUDGET: usize = 100;
    /// A jump to itself.
    // ASM: b .
    const SPIN: u32 = 0x1400_0000;
    /// A load through `x1`.
    // ASM: ldr x0, [x1]
    const LOAD: u32 = 0xf940_0020;
    /// A jump through `x1`.
    // ASM: br x1
    const JUMP: u32 = 0xd61f_0020;
    /// The call number of `exit`.
    // ASM: mov x8, #93
    const EXIT: u32 = 0xd280_0ba8;
    /// The call number of `exit_group`.
    // ASM: mov x8, #94
    const EXIT_GROUP: u32 = 0xd280_0bc8;
    /// The call number of `write`.
    // ASM: mov x8, #64
    const WRITE: u32 = 0xd280_0808;
    /// A Linux system call.
    // ASM: svc #0
    const SVC: u32 = 0xd400_0001;
    let stop = |words: &[u32], set: &[(&str, u64)], budget: usize| {
        let p = image(words);
        let mut m = machine(&p);
        m.set_budget(budget);
        for &(name, v) in set {
            assert!(m.set_register(name, v), "{name}");
        }
        let run = m.run(BASE);
        (run.stop, run.steps, m.last_ip())
    };
    assert_eq!(stop(&[SPIN], &[], BUDGET), (Stop::Budget, BUDGET, BASE));
    assert_eq!(
        stop(&[LOAD, RET], &[("x1", 0x10)], BUDGET).0,
        Stop::Fault(0x10)
    );
    let far = 0x5000_0000;
    assert_eq!(
        stop(&[JUMP], &[("x1", far)], BUDGET),
        (Stop::Fault(far), 1, BASE)
    );
    assert_eq!(
        stop(&[JUMP], &[("x1", BASE + 2)], BUDGET).0,
        Stop::Fault(BASE + 2)
    );
    assert_eq!(
        stop(&[JUMP], &[("x1", SP - 0x100)], BUDGET).0,
        Stop::Derailed(SP - 0x100)
    );
    let cases: [(&[u32], &str); 5] = [
        // ASM: fadd v0.4s, v1.4s, v2.4s (the vector form; the scalar one runs)
        (&[0x4e22_d420], "fadd v0.4s"),
        // ASM: ld1 { v0.16b }, [x0]
        (&[0x4c40_7000], "ld1"),
        // ASM: brk #0x3e8
        (&[0xd420_7d00], "brk"),
        // ASM: svc #0x80
        (&[0xd400_1001], "svc #0x80"),
        // ASM: movz w0, #0x1, lsl #32 (unallocated: a 32-bit form shifted by 32), hand-encoded
        (&[0x52c0_0020], "mov w0, #0x0"),
    ];
    for (words, text) in cases {
        match stop(words, &[], BUDGET).0 {
            Stop::Unmodeled(what) => assert!(what.contains(text), "{what} for {text}"),
            other => panic!("{text}: {other:?}"),
        }
    }
    assert_eq!(stop(&[EXIT, SVC], &[], BUDGET), (Stop::Exited, 2, BASE + 4));
    assert_eq!(stop(&[EXIT_GROUP, SVC], &[], BUDGET).0, Stop::Exited);
    // A non-exit syscall is serviced and the run continues: write is
    // recorded by name, returns its count (x2), and the `ret` after it ends
    // the run.
    {
        let p = image(&[WRITE, SVC, RET]);
        let mut m = machine(&p);
        m.set_budget(BUDGET);
        assert!(m.set_register("x2", 7));
        let run = m.run(BASE);
        assert_eq!(run.stop, Stop::Returned, "{run:?}");
        assert_eq!(m.api_names(), ["write"]);
        assert_eq!(m.register("x0"), Some(7));
    }
    // ASM: an unallocated branch-register word
    match stop(&[0xd600_0000], &[], BUDGET).0 {
        Stop::Unmodeled(what) => assert_eq!(what, format!("bad opcode at {BASE:#x}")),
        other => panic!("bad opcode: {other:?}"),
    }
    let p = image(&[SPIN]);
    let mut m = machine(&p);
    m.stop_at(Some(BASE));
    assert_eq!(m.run(BASE).stop, Stop::Stopped(BASE));
}

/// An XOR decryption routine, linked at [`BASE`]: it finds its blob with
/// `adrp` and `add`, then decrypts it into the buffer `x0` points at under
/// a key that steps by seven, `x1` bytes long.
const XOR_DECRYPT: [u32; 17] = [
    // ASM: stp x29, x30, [sp, #-0x10]!
    0xa9bf_7bfd,
    // ASM: mov x29, sp
    0x9100_03fd,
    // ASM: adrp x9, 0x10000
    0x9000_0009,
    // ASM: add x9, x9, #0x34
    0x9100_d129,
    // ASM: mov w10, #0x5a
    0x5280_0b4a,
    // ASM: ldrb w11, [x9], #0x1
    0x3840_152b,
    // ASM: eor w11, w11, w10
    0x4a0a_016b,
    // ASM: strb w11, [x0], #0x1
    0x3800_140b,
    // ASM: add w10, w10, #0x7
    0x1100_1d4a,
    // ASM: subs x1, x1, #0x1
    0xf100_0421,
    // ASM: b.ne 0x10014
    0x54ff_ff61,
    // ASM: ldp x29, x30, [sp], #0x10
    0xa8c1_7bfd,
    // ASM: ret
    0xd65f_03c0,
    // ASM: .word 0x0a1a0e38 (the blob)
    0x0a1a_0e38,
    // ASM: .word 0xfef65d04
    0xfef6_5d04,
    // ASM: .word 0xc680eafc
    0xc680_eafc,
    // ASM: .word 0xf78ad8dc
    0xf78a_d8dc,
];

/// What [`XOR_DECRYPT`] writes.
const PLAINTEXT: &[u8; 16] = b"borer runs arm64";

/// Where the decrypted text goes.
const OUT_AT: u64 = 0x4_0000;

/// Steps [`XOR_DECRYPT`] takes over sixteen bytes: five to set up, six per
/// byte, two to return.
const XOR_STEPS: usize = 5 + 6 * 16 + 2;

/// The XOR loop decrypts its blob into the buffer and returns, writing its
/// frame record and the plaintext, with a trace of its last instructions.
#[test]
fn an_xor_loop_decrypts_its_blob() {
    let p = image(&XOR_DECRYPT);
    let mut m = Machine::new(&p, 10_000).expect("an arm64 machine");
    m.set_arg(0, OUT_AT);
    m.set_arg(1, 16);
    m.set_trace(3);
    let run = m.run(BASE);
    assert_eq!((run.stop, run.steps), (Stop::Returned, XOR_STEPS));
    let out: Vec<Option<u8>> = (OUT_AT..).take(16).map(|a| m.byte_at(a)).collect();
    let want: Vec<Option<u8>> = PLAINTEXT.iter().copied().map(Some).collect();
    assert_eq!(out, want);
    assert_eq!(run.written, 16 + 16, "the frame record and the text");
    assert_eq!(run.history.len(), 16 + 16);
    assert_eq!(
        (m.register("sp"), m.register("x30")),
        (Some(SP), Some(RETURN_TO))
    );
    let trace = m.trace();
    assert_eq!(trace.len(), 3, "{trace:?}");
    assert!(trace[0].starts_with("0x10028  b.ne 0x10014"), "{trace:?}");
    assert!(trace[1].contains("x29=0x0 sp=0x7fff00000000"), "{trace:?}");
    assert!(trace[2].ends_with("stopped: returned"), "{trace:?}");
}

/// A load through a pointer nothing backs faults, unless a fill is set:
/// then it reads the fill's hash of each address, while a jump there
/// still faults, since a fill answers loads and never fetches.
#[test]
fn a_fill_answers_a_load_nothing_backs() {
    /// An address no image, stack or planted byte takes.
    const NOWHERE: u64 = 0x5000_0000;
    /// The fill's seed.
    const SEED: u64 = 7;
    let load = image(&[
        // ASM: ldr x0, [x1]
        0xf940_0020,
        RET,
    ]);
    let mut m = machine(&load);
    assert!(m.set_register("x1", NOWHERE));
    assert_eq!(m.run(BASE).stop, Stop::Fault(NOWHERE));
    let mut m = machine(&load);
    m.set_fill(Some(SEED));
    assert!(m.set_register("x1", NOWHERE));
    assert_eq!(m.run(BASE).stop, Stop::Returned);
    let want = (0..8)
        .rev()
        .fold(0, |v, k| (v << 8) | u64::from(fill_byte(SEED, NOWHERE + k)));
    assert_eq!(m.register("x0"), Some(want));
    let jump = image(&[
        // ASM: br x1
        0xd61f_0020,
    ]);
    let mut m = machine(&jump);
    m.set_fill(Some(SEED));
    assert!(m.set_register("x1", NOWHERE));
    assert_eq!(m.run(BASE).stop, Stop::Fault(NOWHERE));
}

/// The experiment and typed-run surfaces run arm64 code.
///
/// `emulate` reports the stop, the registers and the text the routine
/// wrote, and `run` tabulates the call on its inputs, unchecked (the
/// decompile answer checks an arm64 text block by block instead); the
/// surfaces built on the x86 machine refuse it.
#[test]
fn emulate_and_run_answer_for_arm64() {
    let p = image(&XOR_DECRYPT);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = render::emulate_tsv(&p, &a, &o, &format!("{BASE:#x},x0={OUT_AT:#x},a2=16"))
        .expect("an arm64 routine runs");
    assert!(
        out.starts_with(&format!(
            "# ran sub_10000 from 0x10000 with x0={OUT_AT:#x} a2=0x10: returned after {XOR_STEPS} steps, 32 bytes written\n# registers: x0={:#x} x1=0x0 ",
            OUT_AT + 16
        )),
        "{out}"
    );
    assert!(out.contains("\"borer runs arm64\""), "{out}");
    let traced = render::emulate_tsv(&p, &a, &o, "0x10000,x0=0x40000,x1=2,trace=2,dump=0x40000:2")
        .expect("a traced run");
    assert!(
        traced.contains("# trace: address, instruction, registers it changed\n0x1002c  ldp"),
        "{traced}"
    );
    assert!(traced.contains("# dump 0x40000..0x40002\n"), "{traced}");
    let refused = render::emulate_tsv(&p, &a, &o, "0x10000,rax=1").expect_err("an x86 name");
    assert!(refused.contains("use x0..x30"), "{refused}");
    let refused = render::emulate_tsv(&p, &a, &o, "0x10000,profile=4").expect_err("x86 only");
    assert!(refused.contains("x86 run only"), "{refused}");
    let table = render::run_tsv(&p, &a, &o, "0x10000/out:16,16").expect("a typed run");
    assert!(
        table.contains("returned\t103\ta1=\"borer runs arm64\"") && table.contains("\tunchecked\n"),
        "{table}"
    );
    assert!(
        table.contains("an arm64 text is checked block by block against the arm64 machine")
            && table.contains("(no signature: an arm64 run passes its inputs untyped)")
            && !table.contains("does not decompile"),
        "{table}"
    );
    for refused in [
        render::oracle_tsv(&p, &a, &o, "0x10000"),
        render::solve_tsv(&p, &a, &o, "0x10000"),
        render::unpack_tsv(&p, &a, &o, "0x10000"),
        render::devirtualize_tsv(&p, &a, &o, "0x10000"),
    ] {
        let why = refused.expect_err("x86 only");
        assert!(
            why.contains("runs x86 and x86-64 code only for now"),
            "{why}"
        );
    }
    assert!(render::hidden_strings_tsv(&p, &a, &o, "").contains("only for now"));
}

/// Random words, with every register pointing into them, run to a stop
/// without a panic from any instruction the decoder hands the machine,
/// and the same words run the same way twice.
#[test]
fn random_words_run_to_a_stop_the_same_way_twice() {
    /// Words in each image.
    const WORDS: usize = 512;
    /// Images run.
    const IMAGES: u64 = 48;
    /// Steps each run is given.
    const STEPS: usize = 2_000;
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for _ in 0..IMAGES {
        let words: Vec<u32> = (0..WORDS)
            .map(|_| u32::try_from(next() >> 32).expect("32 bits"))
            .collect();
        let p = image(&words);
        let span = u64::try_from(WORDS * 4).expect("a small image");
        let regs: Vec<u64> = (0..31).map(|_| BASE + next() % span).collect();
        let start = BASE + (next() % span) / 4 * 4;
        let run = |p: &Program| {
            let mut m = machine(p);
            m.set_budget(STEPS);
            for (n, v) in regs.iter().enumerate() {
                assert!(m.set_register(&format!("x{n}"), *v));
            }
            let run = m.run(start);
            (run.stop, run.steps, m.registers(), m.vregs())
        };
        assert_eq!(run(&p), run(&p), "from {start:#x}");
    }
}
