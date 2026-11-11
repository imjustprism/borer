//! The table of routines the arm64 machine runs, with what each must leave.

use super::*;

/// The routines, each one area of the instruction set.
pub(super) const CASES: &[Case] = &[
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
        name: "packed_float",
        words: &[
            // ASM: dup v0.4s, w0
            0x4e04_0c00,
            // ASM: dup v1.4s, w1
            0x4e04_0c21,
            // ASM: fadd v2.4s, v0.4s, v1.4s
            0x4e21_d402,
            // ASM: fsub v3.4s, v0.4s, v1.4s
            0x4ea1_d403,
            // ASM: fmul v4.4s, v0.4s, v1.4s
            0x6e21_dc04,
            // ASM: fdiv v5.4s, v0.4s, v1.4s
            0x6e21_fc05,
            // ASM: fmax v6.4s, v0.4s, v1.4s
            0x4e21_f406,
            // ASM: fmin v7.4s, v0.4s, v1.4s
            0x4ea1_f407,
            // ASM: fabs v8.4s, v3.4s
            0x4ea0_f868,
            // ASM: fneg v9.4s, v2.4s
            0x6ea0_f849,
            // ASM: fsqrt v10.4s, v1.4s
            0x6ea1_f82a,
            // ASM: dup v11.2d, x2
            0x4e08_0c4b,
            // ASM: dup v12.2d, x3
            0x4e08_0c6c,
            // ASM: fadd v13.2d, v11.2d, v12.2d
            0x4e6c_d56d,
            // ASM: fmul v14.2d, v11.2d, v12.2d
            0x6e6c_dd6e,
            // ASM: fdiv v15.2d, v11.2d, v12.2d
            0x6e6c_fd6f,
            // ASM: fmin v16.2d, v11.2d, v12.2d
            0x4eec_f570,
            // ASM: fmax v17.2d, v11.2d, v12.2d
            0x4e6c_f571,
            // ASM: fsub v18.2d, v11.2d, v12.2d
            0x4eec_d572,
            // ASM: fabs v19.2d, v18.2d
            0x4ee0_fa53,
            // ASM: fneg v20.2d, v13.2d
            0x6ee0_f9b4,
            // ASM: fsqrt v21.2d, v14.2d
            0x6ee1_f9d5,
            // ASM: fmov v22.2s, #1.00000000
            0x0f03_f616,
            // ASM: fmov v23.2d, #0.12500000
            0x6f02_f417,
            // ASM: fmov v24.4s, #1.00000000
            0x4f03_f618,
            // ASM: fmov v25.4s, #-2.50000000
            0x4f04_f499,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0x4040_0000),
            ("x1", 0x4080_0000),
            ("x2", 0x4004_0000_0000_0000),
            ("x3", 0x4008_0000_0000_0000),
        ],
        want: &[],
        mem: &[],
        vregs: &[
            (0, rep(0x4040_0000, 4)),
            (1, rep(0x4080_0000, 4)),
            (2, rep(0x40e0_0000, 4)),
            (3, rep(0xbf80_0000, 4)),
            (4, rep(0x4140_0000, 4)),
            (5, rep(0x3f40_0000, 4)),
            (6, rep(0x4080_0000, 4)),
            (7, rep(0x4040_0000, 4)),
            (8, rep(0x3f80_0000, 4)),
            (9, rep(0xc0e0_0000, 4)),
            (10, rep(0x4000_0000, 4)),
            (11, rep(0x4004_0000_0000_0000, 2)),
            (12, rep(0x4008_0000_0000_0000, 2)),
            (13, rep(0x4016_0000_0000_0000, 2)),
            (14, rep(0x401e_0000_0000_0000, 2)),
            (15, rep(0x3fea_aaaa_aaaa_aaab, 2)),
            (16, rep(0x4004_0000_0000_0000, 2)),
            (17, rep(0x4008_0000_0000_0000, 2)),
            (18, rep(0xbfe0_0000_0000_0000, 2)),
            (19, rep(0x3fe0_0000_0000_0000, 2)),
            (20, rep(0xc016_0000_0000_0000, 2)),
            (21, rep(0x4005_e8ad_d236_a58f, 2)),
            (22, 0x3f80_0000_3f80_0000),
            (23, rep(0x3fc0_0000_0000_0000, 2)),
            (24, rep(0x3f80_0000, 4)),
            (25, rep(0xc020_0000, 4)),
        ],
    },
    Case {
        name: "neon_int",
        words: &[
            // ASM: dup v0.4s, w0
            0x4e04_0c00,
            // ASM: dup v1.4s, w1
            0x4e04_0c21,
            // ASM: add v2.4s, v0.4s, v1.4s
            0x4ea1_8402,
            // ASM: sub v3.4s, v0.4s, v1.4s
            0x6ea1_8403,
            // ASM: mul v4.4s, v0.4s, v1.4s
            0x4ea1_9c04,
            // ASM: neg v5.4s, v0.4s
            0x6ea0_b805,
            // ASM: abs v6.4s, v3.4s
            0x4ea0_b866,
            // ASM: dup v8.8h, w6
            0x4e02_0cc8,
            // ASM: dup v9.8h, w7
            0x4e02_0ce9,
            // ASM: sub v10.8h, v8.8h, v9.8h
            0x6e69_850a,
            // ASM: dup v11.16b, w8
            0x4e01_0d0b,
            // ASM: neg v12.16b, v11.16b
            0x6e20_b96c,
            // ASM: abs v13.16b, v12.16b
            0x4e20_b98d,
            // ASM: dup v14.2d, x9
            0x4e08_0d2e,
            // ASM: add v15.2d, v14.2d, v14.2d
            0x4eee_85cf,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x0", 0xffff_fff0),
            ("x1", 0x101),
            ("x6", 0x5),
            ("x7", 0x7),
            ("x8", 0x80),
            ("x9", 0xffff_ffff_ffff_ffff),
        ],
        want: &[],
        mem: &[],
        vregs: &[
            (0, rep(0xffff_fff0, 4)),
            (1, rep(0x101, 4)),
            (2, rep(0xf1, 4)),
            (3, rep(0xffff_feef, 4)),
            (4, rep(0xffff_eff0, 4)),
            (5, rep(0x10, 4)),
            (6, rep(0x111, 4)),
            (8, rep(0x0005, 8)),
            (9, rep(0x0007, 8)),
            (10, rep(0xfffe, 8)),
            (11, rep(0x80, 16)),
            (12, rep(0x80, 16)),
            (13, rep(0x80, 16)),
            (14, rep(0xffff_ffff_ffff_ffff, 2)),
            (15, rep(0xffff_ffff_ffff_fffe, 2)),
        ],
    },
    Case {
        name: "neon_mem",
        words: &[
            // ASM: ldp q1, q2, [x5]
            0xad40_08a1,
            // ASM: stp q1, q2, [x6]
            0xad00_08c1,
            // ASM: ld1 {v3.16b}, [x5]
            0x4c40_70a3,
            // ASM: ld1 {v6.16b, v7.16b, v8.16b, v9.16b}, [x5]
            0x4c40_20a6,
            // ASM: ld1 {v4.16b, v5.16b}, [x5], #32
            0x4cdf_a0a4,
            // ASM: st1 {v3.16b}, [x6]
            0x4c00_70c3,
            // ASM: st1 {v4.16b}, [x6], #16
            0x4c9f_70c4,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[("x5", 0x3_0000), ("x6", 0x3_0020)],
        want: &[("x5", 0x3_0020), ("x6", 0x3_0030)],
        mem: &[(
            0x3_0020,
            &[
                0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe, 0xff,
                0xff, 0xff, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
        )],
        vregs: &[
            (1, QWORDS),
            (2, RISING),
            (3, QWORDS),
            (4, QWORDS),
            (5, RISING),
            (6, QWORDS),
            (7, RISING),
            (8, QWORDS),
            (9, RISING),
        ],
    },
    Case {
        name: "neon_structures",
        words: &[
            // ASM: ld2 {v0.4s, v1.4s}, [x5]
            0x4c40_88a0,
            // ASM: ld3 {v2.8h, v3.8h, v4.8h}, [x5]
            0x4c40_44a2,
            // ASM: ld2 {v16.8b, v17.8b}, [x7], #16
            0x0cdf_80f0,
            // ASM: ld1 {v5.s}[1], [x5]
            0x0d40_90a5,
            // ASM: ld2 {v0.s, v1.s}[3], [x8]
            0x4d60_9100,
            // ASM: ld1r {v6.4s}, [x5]
            0x4d40_c8a6,
            // ASM: ld3r {v7.8b, v8.8b, v9.8b}, [x5]
            0x0d40_e0a7,
            // ASM: ld4 {v20.2d, v21.2d, v22.2d, v23.2d}, [x5]
            0x4c40_0cb4,
            // ASM: st2 {v0.4s, v1.4s}, [x6]
            0x4c00_88c0,
            // ASM: st3 {v7.8b, v8.8b, v9.8b}, [x10]
            0x0c00_4147,
            // ASM: st2 {v16.b, v17.b}[2], [x11], x12
            0x0dac_0970,
            // ASM: st4 {v2.4h, v3.4h, v4.4h, v5.4h}, [x13], #32
            0x0c9f_05a2,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x5", 0x3_0000),
            ("x6", 0x3_0100),
            ("x7", 0x3_0000),
            ("x8", 0x3_0010),
            ("x10", 0x3_0200),
            ("x11", 0x3_0300),
            ("x12", 5),
            ("x13", 0x3_0400),
        ],
        want: &[("x7", 0x3_0010), ("x11", 0x3_0305), ("x13", 0x3_0420)],
        mem: &[
            (
                0x3_0100,
                &[
                    0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe,
                    0xff, 0xff, 0xff, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x10, 0x20,
                    0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
                ],
            ),
            (
                0x3_0200,
                &[
                    0x88, 0x77, 0x66, 0x88, 0x77, 0x66, 0x88, 0x77, 0x66, 0x88, 0x77, 0x66, 0x88,
                    0x77, 0x66, 0x88, 0x77, 0x66, 0x88, 0x77, 0x66, 0x88, 0x77, 0x66,
                ],
            ),
            (0x3_0300, &[0x44, 0x33]),
            (
                0x3_0400,
                &[
                    0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x00, 0x00, 0x22, 0x11, 0x80, 0xff, 0x01,
                    0x80, 0x00, 0x00, 0xfe, 0xff, 0xff, 0xff, 0x10, 0x20, 0x88, 0x77, 0x30, 0x40,
                    0x50, 0x60, 0x70, 0x80, 0x66, 0x55,
                ],
            ),
        ],
        vregs: &[
            (0, 0x4030_2010_4030_2010_8001_ff80_5566_7788),
            (1, 0x8070_6050_8070_6050_ffff_fffe_1122_3344),
            (2, 0x4030_fffe_1122_7788),
            (3, 0x6050_ffff_ff80_5566),
            (4, 0x8070_2010_8001_3344),
            (5, 0x5566_7788_0000_0000),
            (6, rep(0x5566_7788, 4)),
            (7, 0x8888_8888_8888_8888),
            (8, 0x7777_7777_7777_7777),
            (9, 0x6666_6666_6666_6666),
            (16, 0xfffe_0180_2244_6688),
            (17, 0xffff_80ff_1133_5577),
            (20, 0x1122_3344_5566_7788),
            (21, 0xffff_fffe_8001_ff80),
            (22, 0x8070_6050_4030_2010),
            (23, 0),
        ],
    },
    Case {
        name: "neon_lanes",
        words: &[
            // ASM: ldp q0, q1, [x5]
            0xad40_04a0,
            // ASM: movi v2.2d, #0xff00ff00ff00ff00
            0x6f05_e542,
            // ASM: mov v3.16b, v2.16b
            0x4ea2_1c43,
            // ASM: bsl v3.16b, v0.16b, v1.16b
            0x6e61_1c03,
            // ASM: mov v4.16b, v0.16b
            0x4ea0_1c04,
            // ASM: bit v4.16b, v1.16b, v2.16b
            0x6ea2_1c24,
            // ASM: mov v5.16b, v0.16b
            0x4ea0_1c05,
            // ASM: bif v5.16b, v1.16b, v2.16b
            0x6ee2_1c25,
            // ASM: mov v6.16b, v0.16b
            0x4ea0_1c06,
            // ASM: bif v6.8b, v1.8b, v2.8b
            0x2ee2_1c26,
            // ASM: shrn v7.8b, v0.8h, #4
            0x0f0c_8407,
            // ASM: shrn2 v7.16b, v1.8h, #8
            0x4f08_8427,
            // ASM: rshrn v8.4h, v0.4s, #16
            0x0f10_8c08,
            // ASM: sqshrn v9.8b, v0.8h, #4
            0x0f0c_9409,
            // ASM: sqshrn2 v9.16b, v0.8h, #1
            0x4f0f_9409,
            // ASM: uqshrn v10.4h, v0.4s, #8
            0x2f18_940a,
            // ASM: sqrshrn v11.2s, v0.2d, #31
            0x0f21_9c0b,
            // ASM: uqrshrn v12.8b, v0.8h, #3
            0x2f0d_9c0c,
            // ASM: dup v15.2d, x0
            0x4e08_0c0f,
            // ASM: tbl v13.16b, {v0.16b}, v15.16b
            0x4e0f_000d,
            // ASM: tbl v16.8b, {v0.16b, v1.16b}, v15.8b
            0x0e0f_2010,
            // ASM: mov v17.16b, v2.16b
            0x4ea2_1c51,
            // ASM: tbx v17.16b, {v0.16b, v1.16b}, v15.16b
            0x4e0f_3011,
            // ASM: rbit v18.16b, v0.16b
            0x6e60_5812,
            // ASM: rbit v19.8b, v1.8b
            0x2e60_5833,
            // ASM: fmov s20, #1.5
            0x1e2f_1014,
            // ASM: fmov s21, #-2.0
            0x1e30_1015,
            // ASM: fnmul s22, s20, s21
            0x1e35_8a96,
            // ASM: fmov d23, #0.5
            0x1e6c_1017,
            // ASM: fnmul d24, d23, d23
            0x1e77_8af8,
            // ASM: fmov s26, w1
            0x1e27_003a,
            // ASM: scvtf s25, s26
            0x5e21_db59,
            // ASM: fmov d28, x2
            0x9e67_005c,
            // ASM: ucvtf d27, d28
            0x7e61_db9b,
            // ASM: scvtf s29, s26, #1
            0x5f3f_e75d,
            // ASM: ucvtf v30.2d, v28.2d, #2
            0x6f7e_e79e,
            // ASM: scvtf v31.4s, v26.4s
            0x4e21_db5f,
            // ASM: cnt v14.16b, v0.16b
            0x4e20_580e,
            // ASM: ret
            0xd65f_03c0,
        ],
        set: &[
            ("x5", 0x3_0000),
            ("x0", 0x0001_1f05_0010_ff02),
            ("x1", 0xffff_ffff_ffff_fff9),
            ("x2", 10),
        ],
        want: &[],
        mem: &[],
        vregs: &[
            (3, 0xff00_ff00_8000_ff00_1170_3350_5530_7710),
            (4, 0x00ff_00fe_0001_0080_8022_6044_4066_2088),
            (5, 0xff00_ff00_8000_ff00_1170_3350_5530_7710),
            (6, 0x1170_3350_5530_7710),
            (7, 0x8060_4020_ffff_00f8_1234_5678),
            (8, 0x8002_1122_5566),
            (9, 0xffff_80c0_7f7f_7f7f_ffff_80f8_7f7f_7f7f),
            (10, 0xffff_ffff_ffff_ffff),
            (11, 0xffff_fffd_2244_6689),
            (12, 0xffff_ffff_ffff_ffff),
            (13, 0x8877_0033_8800_0066_8877_0033_8800_0066),
            (14, 0x0808_0807_0101_0801_0202_0402_0404_0602),
            (16, 0x8877_0033_8810_0066),
            (17, 0x8877_0033_8810_ff66_8877_0033_8810_ff66),
            (18, 0xffff_ff7f_0180_ff01_8844_cc22_aa66_ee11),
            (19, 0x010e_060a_020c_0408),
            (22, 0x4040_0000),
            (24, 0xbfd0_0000_0000_0000),
            (25, 0xc0e0_0000),
            (27, 0x4024_0000_0000_0000),
            (29, 0xc060_0000),
            (30, 0x4004_0000_0000_0000),
            (31, 0xc0e0_0000),
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
