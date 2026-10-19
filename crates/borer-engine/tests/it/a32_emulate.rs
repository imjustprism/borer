//! The ARM32 machine.
//!
//! Routines assembled by LLVM (`clang --target=armv7a-linux-gnueabihf
//! -mcpu=cortex-a15 -mfpu=vfpv4`, linked by `ld.lld` at the addresses the
//! table places them) and checked against `llvm-objdump` run in
//! [`Machine`] from a raw ARM32 image: a table of short A32 and T32
//! routines, each one area of the instruction sets (the data processing
//! with its shifter and flags, the multiplies and divides, the loads and
//! stores in every addressing mode and the block transfers, the calls and
//! the change of instruction set, `cbz`, `tbb` and `tbh`, the `IT`
//! blocks and the conditions, `movw` and `movt`, the bit operations, the
//! extends and saturations, and the scalar VFP arithmetic, conversions,
//! moves and compares through `vmrs`) with the registers set before and
//! the registers and memory the Arm ARM says each leaves; an Advanced SIMD
//! word, which stops the run; and random words, which run to a stop
//! without a panic.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::emulate::Stop;
use borer_engine::emulate::a32::Machine;
use borer_engine::isa::a32::{Mode, Modes};
use borer_engine::program::{Arch, Program, Section};

/// Where [`DATA`] is planted before each routine runs.
const DATA_AT: u64 = 0x3_0000;

/// The bytes the loads read: two words, a word whose bytes have their top
/// bits set and a negative word, and eight rising bytes; zeros follow.
const DATA: [u8; 24] = [
    0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe, 0xff, 0xff, 0xff,
    0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
];

/// Bytes planted at [`DATA_AT`]: [`DATA`], then zeros a store can be read
/// back from.
const PLANTED: usize = 64;

/// Most instructions a routine runs.
const BUDGET: usize = 10_000;

/// A routine's code in the instruction set it starts in.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Code<'a> {
    /// A32 words.
    Arm(&'a [u32]),
    /// T32 halfwords.
    Thumb(&'a [u16]),
    /// A32 words that end in T32 code they call, as words of halfword
    /// pairs.
    Mixed {
        /// The words.
        words: &'a [u32],
        /// How many bytes from the start the T32 code begins.
        thumb_from: u64,
    },
}

/// One routine of the table: its code, where it runs, the registers set
/// before it, and what it leaves.
pub(crate) struct Case {
    /// What the routine checks, for a failure message.
    pub(crate) name: &'static str,
    /// The address it is placed and run at, the one it was linked at.
    pub(crate) at: u64,
    /// The routine; it returns.
    pub(crate) code: Code<'static>,
    /// Registers set before the run, by name.
    set: &'static [(&'static str, u64)],
    /// Registers expected after it, by name.
    want: &'static [(&'static str, u64)],
    /// Bytes expected in memory after it, by address.
    mem: &'static [(u64, &'static [u8])],
}

/// The routine `a_shifts`, in A32.
const A_SHIFTS: &[u32] = &[
    // ASM: add r0, r1, r2, lsl #4
    0xe081_0202,
    // ASM: lsr r3, r1, r2
    0xe1a0_3231,
    // ASM: asr r4, r5, r2
    0xe1a0_4255,
    // ASM: ror r6, r5, r2
    0xe1a0_6275,
    // ASM: rsb r7, r1, #100
    0xe261_7064,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_shift_by_reg_past_32`, in A32.
const A_SHIFT_BY_REG_PAST_32: &[u32] = &[
    // ASM: lsl r0, r1, r2
    0xe1a0_0211,
    // ASM: lsr r3, r1, r2
    0xe1a0_3231,
    // ASM: asr r4, r1, r2
    0xe1a0_4251,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_add_flags`, in A32.
const A_ADD_FLAGS: &[u32] = &[
    // ASM: adds r0, r1, r2
    0xe091_0002,
    // ASM: movhs r3, #1
    0x23a0_3001,
    // ASM: movvs r4, #1
    0x63a0_4001,
    // ASM: moveq r5, #1
    0x03a0_5001,
    // ASM: movmi r6, #1
    0x43a0_6001,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_sub_borrow`, in A32.
const A_SUB_BORROW: &[u32] = &[
    // ASM: subs r0, r1, r2
    0xe051_0002,
    // ASM: movlo r3, #1
    0x33a0_3001,
    // ASM: movhi r4, #1
    0x83a0_4001,
    // ASM: movlt r5, #1
    0xb3a0_5001,
    // ASM: movge r6, #1
    0xa3a0_6001,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_carry_chain`, in A32.
const A_CARRY_CHAIN: &[u32] = &[
    // ASM: adds r0, r0, r2
    0xe090_0002,
    // ASM: adc r1, r1, r3
    0xe0a1_1003,
    // ASM: subs r4, r5, r6
    0xe055_4006,
    // ASM: sbc r7, r8, r9
    0xe0c8_7009,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_logic_flags`, in A32.
const A_LOGIC_FLAGS: &[u32] = &[
    // ASM: ands r0, r1, r2
    0xe011_0002,
    // ASM: moveq r3, #1
    0x03a0_3001,
    // ASM: lsls r4, r1, #1
    0xe1b0_4081,
    // ASM: movhs r5, #1
    0x23a0_5001,
    // ASM: bics r6, r1, #-2147483648
    0xe3d1_6102,
    // ASM: mvn r7, r2
    0xe1e0_7002,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_multiply`, in A32.
const A_MULTIPLY: &[u32] = &[
    // ASM: umull r0, r1, r2, r3
    0xe081_0392,
    // ASM: smull r4, r5, r2, r3
    0xe0c5_4392,
    // ASM: mla r6, r2, r3, r2
    0xe026_2392,
    // ASM: mls r7, r3, r3, r8
    0xe067_8393,
    // ASM: smmul r9, r2, r10
    0xe759_fa12,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_accumulate_long`, in A32.
const A_ACCUMULATE_LONG: &[u32] = &[
    // ASM: umlal r0, r1, r2, r3
    0xe0a1_0392,
    // ASM: smlal r4, r5, r2, r3
    0xe0e5_4392,
    // ASM: smulbb r6, r2, r3
    0xe166_0382,
    // ASM: smlatt r7, r2, r3, r8
    0xe107_83e2,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_divide`, in A32.
const A_DIVIDE: &[u32] = &[
    // ASM: sdiv r0, r1, r2
    0xe710_f211,
    // ASM: udiv r3, r1, r2
    0xe733_f211,
    // ASM: udiv r4, r1, r5
    0xe734_f511,
    // ASM: sdiv r6, r7, r8
    0xe716_f817,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_loads`, in A32.
const A_LOADS: &[u32] = &[
    // ASM: ldr r0, [r1, #0x4]
    0xe591_0004,
    // ASM: ldrb r2, [r1, #0x1]!
    0xe5f1_2001,
    // ASM: ldrsh r3, [r1], #2
    0xe0d1_30f2,
    // ASM: ldrsb r4, [r1, #6]
    0xe1d1_40d6,
    // ASM: ldrh r5, [r1, r6]
    0xe191_50b6,
    // ASM: ldr r7, [r1, r6, lsl #2]
    0xe791_7106,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_stores`, in A32.
const A_STORES: &[u32] = &[
    // ASM: str r2, [r1, #-0x4]!
    0xe521_2004,
    // ASM: strb r3, [r1, #0x8]
    0xe5c1_3008,
    // ASM: strh r4, [r1], #12
    0xe0c1_40bc,
    // ASM: strd r6, r7, [r1]
    0xe1c1_60f0,
    // ASM: ldrd r8, r9, [r1]
    0xe1c1_80d0,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_block_transfer`, in A32.
const A_BLOCK_TRANSFER: &[u32] = &[
    // ASM: push {r4, r5, lr}
    0xe92d_4030,
    // ASM: stmdb r1!, {r2, r3}
    0xe921_000c,
    // ASM: ldm r1, {r6, r7}
    0xe891_00c0,
    // ASM: ldm r1!, {r8}
    0xe8b1_0100,
    // ASM: pop {r4, r5, lr}
    0xe8bd_4030,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_exclusive`, in A32.
const A_EXCLUSIVE: &[u32] = &[
    // ASM: ldrex r0, [r1]
    0xe191_0f9f,
    // ASM: add r0, r0, #1
    0xe280_0001,
    // ASM: strex r2, r0, [r1]
    0xe181_2f90,
    // ASM: ldr r3, [r1]
    0xe591_3000,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_wide_constants`, in A32.
const A_WIDE_CONSTANTS: &[u32] = &[
    // ASM: movw r0, #0x1234
    0xe301_0234,
    // ASM: movt r0, #0x5678
    0xe345_0678,
    // ASM: movw r1, #0xffff
    0xe30f_1fff,
    // ASM: mvn r2, #0
    0xe3e0_2000,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_bit_counts`, in A32.
const A_BIT_COUNTS: &[u32] = &[
    // ASM: clz r0, r1
    0xe16f_0f11,
    // ASM: rbit r2, r1
    0xe6ff_2f31,
    // ASM: rev r3, r1
    0xe6bf_3f31,
    // ASM: rev16 r4, r1
    0xe6bf_4fb1,
    // ASM: revsh r5, r1
    0xe6ff_5fb1,
    // ASM: clz r6, r7
    0xe16f_6f17,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_bit_fields`, in A32.
const A_BIT_FIELDS: &[u32] = &[
    // ASM: ubfx r0, r1, #0x4, #0x8
    0xe7e7_0251,
    // ASM: sbfx r2, r1, #0x18, #0x8
    0xe7a7_2c51,
    // ASM: bfi r3, r1, #8, #4
    0xe7cb_3411,
    // ASM: bfc r4, #0, #16
    0xe7cf_401f,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_extends`, in A32.
const A_EXTENDS: &[u32] = &[
    // ASM: uxtb r0, r1
    0xe6ef_0071,
    // ASM: sxtb r2, r1
    0xe6af_2071,
    // ASM: uxth r3, r1, ror #8
    0xe6ff_3471,
    // ASM: sxth r4, r1
    0xe6bf_4071,
    // ASM: uxtab r5, r6, r1
    0xe6e6_5071,
    // ASM: sxtah r7, r6, r1
    0xe6b6_7071,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_saturate`, in A32.
const A_SATURATE: &[u32] = &[
    // ASM: usat r0, #0x8, r1
    0xe6e8_0011,
    // ASM: usat r2, #0x8, r3
    0xe6e8_2013,
    // ASM: ssat r4, #0x8, r1
    0xe6a7_4011,
    // ASM: ssat r5, #0x10, r3, asr #4
    0xe6af_5253,
    // ASM: usat r6, #0x8, r7
    0xe6e8_6017,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_conditions`, in A32.
const A_CONDITIONS: &[u32] = &[
    // ASM: cmp r0, r1
    0xe150_0001,
    // ASM: movgt r2, #1
    0xc3a0_2001,
    // ASM: movle r2, #2
    0xd3a0_2002,
    // ASM: movhi r3, #1
    0x83a0_3001,
    // ASM: movls r3, #2
    0x93a0_3002,
    // ASM: cmn r0, r1
    0xe170_0001,
    // ASM: movne r4, #1
    0x13a0_4001,
    // ASM: tst r0, #1
    0xe310_0001,
    // ASM: moveq r5, #1
    0x03a0_5001,
    // ASM: teq r0, r0
    0xe130_0000,
    // ASM: moveq r6, #1
    0x03a0_6001,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_call_and_return`, in A32.
const A_CALL_AND_RETURN: &[u32] = &[
    // ASM: push {r4, lr}
    0xe92d_4010,
    // ASM: mov r4, r0
    0xe1a0_4000,
    // ASM: bl 0x101e4
    0xeb00_0001,
    // ASM: add r0, r0, r4
    0xe080_0004,
    // ASM: pop {r4, pc}
    0xe8bd_8010,
    // ASM: add r0, r0, #1
    0xe280_0001,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_interworking`, in A32.
const A_INTERWORKING: &[u32] = &[
    // ASM: push {r4, lr}
    0xe92d_4010,
    // ASM: add r4, pc, #12
    0xe28f_400c,
    // ASM: orr r4, r4, #1
    0xe384_4001,
    // ASM: blx r4
    0xe12f_ff34,
    // ASM: blx 0x10204
    0xfa00_0000,
    // ASM: pop {r4, pc}
    0xe8bd_8010,
    // ASM: lsls r0, r0, #0x1; bx lr (T32)
    0x4770_0040,
];

/// The routine `a_float_single`, in A32.
const A_FLOAT_SINGLE: &[u32] = &[
    // ASM: vmov s0, r1
    0xee00_1a10,
    // ASM: vcvt.f32.s32 s0, s0
    0xeeb8_0ac0,
    // ASM: vadd.f32 s0, s0, s0
    0xee30_0a00,
    // ASM: vmul.f32 s1, s0, s0
    0xee60_0a00,
    // ASM: vsub.f32 s2, s1, s0
    0xee30_1ac0,
    // ASM: vdiv.f32 s3, s2, s0
    0xeec1_1a00,
    // ASM: vcvt.s32.f32 s4, s3
    0xeebd_2ae1,
    // ASM: vmov r0, s4
    0xee12_0a10,
    // ASM: vneg.f32 s5, s3
    0xeef1_2a61,
    // ASM: vmov r2, s5
    0xee12_2a90,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_float_double`, in A32.
const A_FLOAT_DOUBLE: &[u32] = &[
    // ASM: vmov d0, r0, r1
    0xec41_0b10,
    // ASM: vsqrt.f64 d1, d0
    0xeeb1_1bc0,
    // ASM: vabs.f64 d2, d1
    0xeeb0_2bc1,
    // ASM: vneg.f64 d2, d2
    0xeeb1_2b42,
    // ASM: vmov.f64 d3, #5.000000e-01
    0xeeb6_3b00,
    // ASM: vfma.f64 d3, d1, d1
    0xeea1_3b01,
    // ASM: vcvt.f32.f64 s8, d3
    0xeeb7_4bc3,
    // ASM: vcvt.f64.f32 d5, s8
    0xeeb7_5ac4,
    // ASM: vmov r2, r3, d2
    0xec53_2b12,
    // ASM: vmov r4, r5, d3
    0xec55_4b13,
    // ASM: vcvt.u32.f64 s12, d1
    0xeebc_6bc1,
    // ASM: vmov r6, s12
    0xee16_6a10,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_float_compare`, in A32.
const A_FLOAT_COMPARE: &[u32] = &[
    // ASM: vmov d0, r0, r1
    0xec41_0b10,
    // ASM: vmov d1, r2, r3
    0xec43_2b11,
    // ASM: vcmp.f64 d0, d1
    0xeeb4_0b41,
    // ASM: vmrs APSR_nzcv, fpscr
    0xeef1_fa10,
    // ASM: movgt r4, #1
    0xc3a0_4001,
    // ASM: movmi r5, #1
    0x43a0_5001,
    // ASM: moveq r6, #1
    0x03a0_6001,
    // ASM: movvs r7, #1
    0x63a0_7001,
    // ASM: vcmpe.f64 d0, #0
    0xeeb5_0bc0,
    // ASM: vmrs APSR_nzcv, fpscr
    0xeef1_fa10,
    // ASM: movgt r8, #1
    0xc3a0_8001,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `a_float_memory`, in A32.
const A_FLOAT_MEMORY: &[u32] = &[
    // ASM: vldr d0, [r1]
    0xed91_0b00,
    // ASM: vstr d0, [r1, #16]
    0xed81_0b04,
    // ASM: vldr s2, [r1, #4]
    0xed91_1a01,
    // ASM: vpush {d0, d1}
    0xed2d_0b04,
    // ASM: vpop {d2, d3}
    0xecbd_2b04,
    // ASM: vmov r0, r2, d2
    0xec52_0b12,
    // ASM: vmov r3, s6
    0xee13_3a10,
    // ASM: vldmia r1!, {s8, s9}
    0xecb1_4a02,
    // ASM: vmov r4, r5, d4
    0xec55_4b14,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// The routine `t_narrow`, in T32.
const T_NARROW: &[u16] = &[
    // ASM: adds r0, r1, r2
    0x1888, // ASM: subs r3, r1, #0x1
    0x1e4b, // ASM: lsls r4, r1, #0x3
    0x00cc, // ASM: lsrs r5, r1, #0x1
    0x084d, // ASM: muls r6, r1, r6
    0x434e, // ASM: mvns r7, r1
    0x43cf, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00,
];

/// The routine `t_wide`, in T32.
const T_WIDE: &[u16] = &[
    // ASM: add.w r0, r1, r2, lsl #2
    0xeb01, 0x0082, // ASM: orr r3, r1, #0xff00ff00
    0xf041, 0x23ff, // ASM: orn r4, r1, r2
    0xea61, 0x0402, // ASM: bic r5, r1, #0xf0
    0xf021, 0x05f0, // ASM: adds.w r6, r1, #0x100000
    0xf511, 0x1680, // ASM: rsb.w r7, r1, #0x0
    0xf1c1, 0x0700, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00,
];

/// The routine `t_shift_flags`, in T32.
const T_SHIFT_FLAGS: &[u16] = &[
    // ASM: cmp r1, r1
    0x4289, // ASM: lsls.w r0, r1, r2
    0xfa11, 0xf002, // ASM: movs r3, #0x0
    0x2300, // ASM: adc r3, r3, #0x0
    0xf143, 0x0300, // ASM: lsrs.w r4, r1, r5
    0xfa31, 0xf405, // ASM: movs r6, #0x0
    0x2600, // ASM: adc r6, r6, #0x0
    0xf146, 0x0600, // ASM: bx lr
    0x4770,
];

/// The routine `t_it_block`, in T32.
const T_IT_BLOCK: &[u16] = &[
    // ASM: cmp r0, #0x5
    0x2805, // ASM: ite gt
    0xbfcc, // ASM: movgt r1, #0x1
    0x2101, // ASM: movle r1, #0x2
    0x2102, // ASM: itttt eq
    0xbf01, // ASM: addeq r2, r2, #0x1
    0x1c52, // ASM: addeq r2, r2, #0x2
    0x1c92, // ASM: addeq r2, r2, #0x4
    0x1d12, // ASM: addeq r2, #0x8
    0x3208, // ASM: bx lr
    0x4770,
];

/// The routine `t_compare_branch`, in T32.
const T_COMPARE_BRANCH: &[u16] = &[
    // ASM: cbz r0, 0x1031c
    0xb100, // ASM: movs r1, #0x1
    0x2101, // ASM: cbnz r2, 0x10320
    0xb902, // ASM: movs r3, #0x1
    0x2301, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00,
];

/// The routine `t_table_byte`, in T32.
const T_TABLE_BYTE: &[u16] = &[
    // ASM: tbb [pc, r0]
    0xe8df, 0xf000, // ASM: .byte 2, 4, 6, 6
    0x0402, 0x0606, // ASM: movs r1, #0xa
    0x210a, // ASM: bx lr
    0x4770, // ASM: movs r1, #0xb
    0x210b, // ASM: bx lr
    0x4770, // ASM: movs r1, #0xc
    0x210c, // ASM: bx lr
    0x4770,
];

/// The routine `t_table_half`, in T32.
const T_TABLE_HALF: &[u16] = &[
    // ASM: tbh [pc, r0, lsl #1]
    0xe8df, 0xf010, // ASM: .hword 2, 4
    0x0002, 0x0004, // ASM: movs r1, #0x14
    0x2114, // ASM: bx lr
    0x4770, // ASM: movs r1, #0x15
    0x2115, // ASM: bx lr
    0x4770,
];

/// The routine `t_loop`, in T32.
const T_LOOP: &[u16] = &[
    // ASM: movs r1, #0x0
    0x2100, // ASM: ldrb r2, [r0], #1
    0xf810, 0x2b01, // ASM: cbz r2, 0x10354
    0xb10a, // ASM: add r1, r2
    0x4411, // ASM: b 0x1034a
    0xe7fa, // ASM: mov r0, r1
    0x4608, // ASM: bx lr
    0x4770,
];

/// The routine `t_memory`, in T32.
const T_MEMORY: &[u16] = &[
    // ASM: ldr r2, [r1, #0x4]
    0x684a, // ASM: ldrd r4, r5, [r1, #8]
    0xe9d1, 0x4502, // ASM: str r2, [r1, #16]!
    0xf841, 0x2f10, // ASM: ldrh r6, [r1, #-16]
    0xf831, 0x6c10, // ASM: push {r4, r5, r6, r7}
    0xb4f0, // ASM: pop {r0, r3, r6, r7}
    0xbcc9, // ASM: ldm r1!, {r6}
    0xc940, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00,
];

/// The routine `t_bits`, in T32.
const T_BITS: &[u16] = &[
    // ASM: clz r0, r1
    0xfab1, 0xf081, // ASM: rbit r2, r1
    0xfa91, 0xf2a1, // ASM: ubfx r3, r1, #0x8, #0x8
    0xf3c1, 0x2307, // ASM: sbfx r4, r1, #0x1c, #0x4
    0xf341, 0x7403, // ASM: bfi r5, r1, #4, #4
    0xf361, 0x1507, // ASM: sxtb r6, r1
    0xb24e, // ASM: usat r7, #0x4, r1
    0xf381, 0x0704, // ASM: bx lr
    0x4770,
];

/// The routine `t_divide_and_multiply`, in T32.
const T_DIVIDE_AND_MULTIPLY: &[u16] = &[
    // ASM: sdiv r0, r1, r2
    0xfb91, 0xf0f2, // ASM: udiv r3, r1, r2
    0xfbb1, 0xf3f2, // ASM: mla r4, r1, r2, r3
    0xfb01, 0x3402, // ASM: smull r5, r6, r1, r2
    0xfb81, 0x5602, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00,
];

/// The routine `t_float`, in T32.
const T_FLOAT: &[u16] = &[
    // ASM: vmov s0, r0
    0xee00, 0x0a10, // ASM: vmov s1, r1
    0xee00, 0x1a90, // ASM: vcmp.f32 s0, s1
    0xeeb4, 0x0a60, // ASM: vmrs APSR_nzcv, fpscr
    0xeef1, 0xfa10, // ASM: ite lt
    0xbfb4, // ASM: vmovlt.f32 s2, s0
    0xeeb0, 0x1a40, // ASM: vmovge.f32 s2, s1
    0xeeb0, 0x1a60, // ASM: vmov r2, s2
    0xee11, 0x2a10, // ASM: vcvt.s32.f32 s3, s2
    0xeefd, 0x1ac1, // ASM: vmov r3, s3
    0xee11, 0x3a90, // ASM: bx lr
    0x4770,
];

/// The routines, each one area of the instruction sets, with what the
/// Arm ARM says each leaves.
pub(crate) const CASES: &[Case] = &[
    Case {
        name: "shifts by an immediate and by a register",
        at: 0x1_0000,
        code: Code::Arm(A_SHIFTS),
        set: &[("r1", 0x8000_0001), ("r2", 4), ("r5", 0xf000_0000)],
        want: &[
            ("r0", 0x8000_0041),
            ("r3", 0x0800_0000),
            ("r4", 0xff00_0000),
            ("r6", 0x0f00_0000),
            ("r7", 0x8000_0063),
        ],
        mem: &[],
    },
    Case {
        name: "a shift by a register's low byte past 32",
        at: 0x1_0018,
        code: Code::Arm(A_SHIFT_BY_REG_PAST_32),
        set: &[("r1", 0x8000_0001), ("r2", 0x121)],
        want: &[("r0", 0), ("r3", 0), ("r4", 0xffff_ffff)],
        mem: &[],
    },
    Case {
        name: "the flags of an add that overflows",
        at: 0x1_0028,
        code: Code::Arm(A_ADD_FLAGS),
        set: &[("r1", 0x7fff_ffff), ("r2", 1)],
        want: &[
            ("r0", 0x8000_0000),
            ("r3", 0),
            ("r4", 1),
            ("r5", 0),
            ("r6", 1),
        ],
        mem: &[],
    },
    Case {
        name: "the flags of a subtract that borrows",
        at: 0x1_0040,
        code: Code::Arm(A_SUB_BORROW),
        set: &[("r1", 1), ("r2", 2)],
        want: &[
            ("r0", 0xffff_ffff),
            ("r3", 1),
            ("r4", 0),
            ("r5", 1),
            ("r6", 0),
        ],
        mem: &[],
    },
    Case {
        name: "a carry carried into adc and sbc",
        at: 0x1_0058,
        code: Code::Arm(A_CARRY_CHAIN),
        set: &[
            ("r0", 0xffff_ffff),
            ("r1", 1),
            ("r2", 1),
            ("r3", 2),
            ("r5", 0),
            ("r6", 1),
            ("r8", 5),
            ("r9", 1),
        ],
        want: &[("r0", 0), ("r1", 4), ("r4", 0xffff_ffff), ("r7", 3)],
        mem: &[],
    },
    Case {
        name: "the flags of a logical operation and the shifter's carry",
        at: 0x1_006c,
        code: Code::Arm(A_LOGIC_FLAGS),
        set: &[("r1", 0x8000_0000), ("r2", 0x7fff_ffff)],
        want: &[
            ("r0", 0),
            ("r3", 1),
            ("r4", 0),
            ("r5", 1),
            ("r6", 0),
            ("r7", 0x8000_0000),
        ],
        mem: &[],
    },
    Case {
        name: "the multiplies",
        at: 0x1_0088,
        code: Code::Arm(A_MULTIPLY),
        set: &[
            ("r2", 0xffff_ffff),
            ("r3", 2),
            ("r8", 10),
            ("r10", 0x4000_0000),
        ],
        want: &[
            ("r0", 0xffff_fffe),
            ("r1", 1),
            ("r4", 0xffff_fffe),
            ("r5", 0xffff_ffff),
            ("r6", 0xffff_fffd),
            ("r7", 6),
            ("r9", 0xffff_ffff),
        ],
        mem: &[],
    },
    Case {
        name: "the accumulating and halfword multiplies",
        at: 0x1_00a0,
        code: Code::Arm(A_ACCUMULATE_LONG),
        set: &[
            ("r0", 1),
            ("r2", 0xffff_ffff),
            ("r3", 2),
            ("r4", 5),
            ("r8", 100),
        ],
        want: &[
            ("r0", 0xffff_ffff),
            ("r1", 1),
            ("r4", 3),
            ("r5", 0),
            ("r6", 0xffff_fffe),
            ("r7", 100),
        ],
        mem: &[],
    },
    Case {
        name: "the divides, by zero and of the least integer by -1",
        at: 0x1_00b4,
        code: Code::Arm(A_DIVIDE),
        set: &[
            ("r1", 0xffff_fff9),
            ("r2", 2),
            ("r7", 0x8000_0000),
            ("r8", 0xffff_ffff),
        ],
        want: &[
            ("r0", 0xffff_fffd),
            ("r3", 0x7fff_fffc),
            ("r4", 0),
            ("r6", 0x8000_0000),
        ],
        mem: &[],
    },
    Case {
        name: "loads in every addressing mode",
        at: 0x1_00c8,
        code: Code::Arm(A_LOADS),
        set: &[("r1", DATA_AT), ("r6", 2)],
        want: &[
            ("r0", 0x1122_3344),
            ("r1", DATA_AT + 3),
            ("r2", 0x77),
            ("r3", 0x6677),
            ("r4", 0xffff_ffff),
            ("r5", 0x2233),
            ("r7", 0xffff_fe80),
        ],
        mem: &[],
    },
    Case {
        name: "stores that write their base back, and the pair",
        at: 0x1_00e4,
        code: Code::Arm(A_STORES),
        set: &[
            ("r1", DATA_AT + 0x20),
            ("r2", 0xaabb_ccdd),
            ("r3", 0x11),
            ("r4", 0x2233),
            ("r6", 0x0102_0304),
            ("r7", 0x0506_0708),
        ],
        want: &[
            ("r1", DATA_AT + 0x28),
            ("r8", 0x0102_0304),
            ("r9", 0x0506_0708),
        ],
        mem: &[
            (DATA_AT + 0x1c, &[0x33, 0x22, 0xbb, 0xaa]),
            (DATA_AT + 0x24, &[0x11]),
            (DATA_AT + 0x28, &[4, 3, 2, 1, 8, 7, 6, 5]),
        ],
    },
    Case {
        name: "the block transfers, push and pop",
        at: 0x1_00fc,
        code: Code::Arm(A_BLOCK_TRANSFER),
        set: &[
            ("r1", DATA_AT + 0x30),
            ("r2", 0x22),
            ("r3", 0x33),
            ("r4", 0x44),
            ("r5", 0x55),
        ],
        want: &[
            ("r1", DATA_AT + 0x2c),
            ("r4", 0x44),
            ("r5", 0x55),
            ("r6", 0x22),
            ("r7", 0x33),
            ("r8", 0x22),
        ],
        mem: &[(DATA_AT + 0x28, &[0x22, 0, 0, 0, 0x33, 0, 0, 0])],
    },
    Case {
        name: "an exclusive load and store",
        at: 0x1_0114,
        code: Code::Arm(A_EXCLUSIVE),
        set: &[("r1", DATA_AT), ("r2", 7)],
        want: &[("r0", 0x5566_7789), ("r2", 0), ("r3", 0x5566_7789)],
        mem: &[(DATA_AT, &[0x89, 0x77, 0x66, 0x55])],
    },
    Case {
        name: "movw, movt and mvn",
        at: 0x1_0128,
        code: Code::Arm(A_WIDE_CONSTANTS),
        set: &[],
        want: &[("r0", 0x5678_1234), ("r1", 0xffff), ("r2", 0xffff_ffff)],
        mem: &[],
    },
    Case {
        name: "clz, rbit and the byte reversals",
        at: 0x1_013c,
        code: Code::Arm(A_BIT_COUNTS),
        set: &[("r1", 0x00f0_0001)],
        want: &[
            ("r0", 8),
            ("r2", 0x8000_0f00),
            ("r3", 0x0100_f000),
            ("r4", 0xf000_0100),
            ("r5", 0x100),
            ("r6", 32),
        ],
        mem: &[],
    },
    Case {
        name: "the bit field extracts, insert and clear",
        at: 0x1_0158,
        code: Code::Arm(A_BIT_FIELDS),
        set: &[
            ("r1", 0x8765_4321),
            ("r3", 0xffff_ffff),
            ("r4", 0x1234_5678),
        ],
        want: &[
            ("r0", 0x32),
            ("r2", 0xffff_ff87),
            ("r3", 0xffff_f1ff),
            ("r4", 0x1234_0000),
        ],
        mem: &[],
    },
    Case {
        name: "the extends, rotated and accumulating",
        at: 0x1_016c,
        code: Code::Arm(A_EXTENDS),
        set: &[("r1", 0x1234_8085), ("r6", 0x100)],
        want: &[
            ("r0", 0x85),
            ("r2", 0xffff_ff85),
            ("r3", 0x3480),
            ("r4", 0xffff_8085),
            ("r5", 0x185),
            ("r7", 0xffff_8185),
        ],
        mem: &[],
    },
    Case {
        name: "the saturations",
        at: 0x1_0188,
        code: Code::Arm(A_SATURATE),
        set: &[("r1", 300), ("r3", 0xffff_f000), ("r7", 0xffff_ffff)],
        want: &[
            ("r0", 255),
            ("r2", 0),
            ("r4", 127),
            ("r5", 0xffff_ff00),
            ("r6", 0),
        ],
        mem: &[],
    },
    Case {
        name: "instructions under every kind of condition",
        at: 0x1_01a0,
        code: Code::Arm(A_CONDITIONS),
        set: &[("r0", 0xffff_fffe), ("r1", 1)],
        want: &[("r2", 2), ("r3", 1), ("r4", 1), ("r5", 1), ("r6", 1)],
        mem: &[],
    },
    Case {
        name: "a call and a return through the stack",
        at: 0x1_01d0,
        code: Code::Arm(A_CALL_AND_RETURN),
        set: &[("r0", 5), ("r4", 0x99)],
        want: &[("r0", 11), ("r4", 0x99)],
        mem: &[],
    },
    Case {
        name: "calls from A32 into T32 and back",
        at: 0x1_01ec,
        code: Code::Mixed {
            words: A_INTERWORKING,
            thumb_from: 0x18,
        },
        set: &[("r0", 3), ("r4", 0x99)],
        want: &[("r0", 12), ("r4", 0x99)],
        mem: &[],
    },
    Case {
        name: "single-precision arithmetic and conversions",
        at: 0x1_0208,
        code: Code::Arm(A_FLOAT_SINGLE),
        set: &[("r1", 3)],
        want: &[("r0", 5), ("r2", 0xc0a0_0000)],
        mem: &[],
    },
    Case {
        name: "double-precision arithmetic, a fused multiply-add and conversions",
        at: 0x1_0234,
        code: Code::Arm(A_FLOAT_DOUBLE),
        set: &[("r0", 0), ("r1", 0x4030_0000)],
        want: &[
            ("r2", 0),
            ("r3", 0xc010_0000),
            ("r4", 0),
            ("r5", 0x4030_8000),
            ("r6", 4),
        ],
        mem: &[],
    },
    Case {
        name: "vcmp and vmrs of ordered doubles",
        at: 0x1_0268,
        code: Code::Arm(A_FLOAT_COMPARE),
        set: &[("r1", 0x4000_0000), ("r3", 0x3ff0_0000)],
        want: &[("r4", 1), ("r5", 0), ("r6", 0), ("r7", 0), ("r8", 1)],
        mem: &[],
    },
    Case {
        name: "vcmp and vmrs of a NaN",
        at: 0x1_0268,
        code: Code::Arm(A_FLOAT_COMPARE),
        set: &[("r1", 0x7ff8_0000), ("r3", 0x3ff0_0000)],
        want: &[("r4", 0), ("r5", 0), ("r6", 0), ("r7", 1), ("r8", 0)],
        mem: &[],
    },
    Case {
        name: "the VFP loads, stores and block transfers",
        at: 0x1_0298,
        code: Code::Arm(A_FLOAT_MEMORY),
        set: &[("r1", DATA_AT)],
        want: &[
            ("r0", 0x5566_7788),
            ("r1", DATA_AT + 8),
            ("r2", 0x1122_3344),
            ("r3", 0x1122_3344),
            ("r4", 0x5566_7788),
            ("r5", 0x1122_3344),
        ],
        mem: &[(
            DATA_AT + 0x10,
            &[0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11],
        )],
    },
    Case {
        name: "the 16-bit T32 data processing",
        at: 0x1_02c0,
        code: Code::Thumb(T_NARROW),
        set: &[("r1", 5), ("r2", 7), ("r6", 3)],
        want: &[
            ("r0", 12),
            ("r3", 4),
            ("r4", 40),
            ("r5", 2),
            ("r6", 15),
            ("r7", 0xffff_fffa),
        ],
        mem: &[],
    },
    Case {
        name: "the 32-bit T32 data processing and its modified immediates",
        at: 0x1_02d0,
        code: Code::Thumb(T_WIDE),
        set: &[("r1", 0x10), ("r2", 1)],
        want: &[
            ("r0", 0x14),
            ("r3", 0xff00_ff10),
            ("r4", 0xffff_fffe),
            ("r5", 0),
            ("r6", 0x10_0010),
            ("r7", 0xffff_fff0),
        ],
        mem: &[],
    },
    Case {
        name: "the carry of a shift by a register",
        at: 0x1_02ec,
        code: Code::Thumb(T_SHIFT_FLAGS),
        set: &[("r1", 0x8000_0001), ("r2", 1), ("r5", 1)],
        want: &[("r0", 2), ("r3", 1), ("r4", 0x4000_0000), ("r6", 1)],
        mem: &[],
    },
    Case {
        name: "the carry of a shift by zero and by 32",
        at: 0x1_02ec,
        code: Code::Thumb(T_SHIFT_FLAGS),
        set: &[("r1", 0x7fff_fffe), ("r2", 0), ("r5", 32)],
        want: &[("r0", 0x7fff_fffe), ("r3", 1), ("r4", 0), ("r6", 0)],
        mem: &[],
    },
    Case {
        name: "an IT block whose condition holds",
        at: 0x1_0304,
        code: Code::Thumb(T_IT_BLOCK),
        set: &[("r0", 5)],
        want: &[("r1", 2), ("r2", 15)],
        mem: &[],
    },
    Case {
        name: "an IT block whose condition fails",
        at: 0x1_0304,
        code: Code::Thumb(T_IT_BLOCK),
        set: &[("r0", 7)],
        want: &[("r1", 1), ("r2", 0)],
        mem: &[],
    },
    Case {
        name: "cbz taken and cbnz not",
        at: 0x1_0318,
        code: Code::Thumb(T_COMPARE_BRANCH),
        set: &[("r0", 0), ("r2", 0)],
        want: &[("r1", 0), ("r3", 1)],
        mem: &[],
    },
    Case {
        name: "cbz not taken and cbnz taken",
        at: 0x1_0318,
        code: Code::Thumb(T_COMPARE_BRANCH),
        set: &[("r0", 1), ("r2", 9)],
        want: &[("r1", 1), ("r3", 0)],
        mem: &[],
    },
    Case {
        name: "tbb to its first case",
        at: 0x1_0324,
        code: Code::Thumb(T_TABLE_BYTE),
        set: &[("r0", 0)],
        want: &[("r1", 10)],
        mem: &[],
    },
    Case {
        name: "tbb to a case two entries share",
        at: 0x1_0324,
        code: Code::Thumb(T_TABLE_BYTE),
        set: &[("r0", 3)],
        want: &[("r1", 12)],
        mem: &[],
    },
    Case {
        name: "tbh to its second case",
        at: 0x1_0338,
        code: Code::Thumb(T_TABLE_HALF),
        set: &[("r0", 1)],
        want: &[("r1", 21)],
        mem: &[],
    },
    Case {
        name: "a loop over bytes up to a zero",
        at: 0x1_0348,
        code: Code::Thumb(T_LOOP),
        set: &[("r0", DATA_AT + 16)],
        want: &[("r0", 0x240)],
        mem: &[],
    },
    Case {
        name: "T32 loads, stores, push and pop",
        at: 0x1_0358,
        code: Code::Thumb(T_MEMORY),
        set: &[("r1", DATA_AT), ("r7", 7)],
        want: &[
            ("r0", 0x8001_ff80),
            ("r1", DATA_AT + 0x14),
            ("r2", 0x1122_3344),
            ("r3", 0xffff_fffe),
            ("r6", 0x1122_3344),
            ("r7", 7),
        ],
        mem: &[(DATA_AT + 0x10, &[0x44, 0x33, 0x22, 0x11])],
    },
    Case {
        name: "the T32 bit operations",
        at: 0x1_0370,
        code: Code::Thumb(T_BITS),
        set: &[("r1", 0xf000_1234)],
        want: &[
            ("r0", 0),
            ("r2", 0x2c48_000f),
            ("r3", 0x12),
            ("r4", 0xffff_ffff),
            ("r5", 0x40),
            ("r6", 0x34),
            ("r7", 0),
        ],
        mem: &[],
    },
    Case {
        name: "the T32 divides and multiplies",
        at: 0x1_038c,
        code: Code::Thumb(T_DIVIDE_AND_MULTIPLY),
        set: &[("r1", 100), ("r2", 0xffff_fff9)],
        want: &[
            ("r0", 0xffff_fff2),
            ("r3", 0),
            ("r4", 0xffff_fd44),
            ("r5", 0xffff_fd44),
            ("r6", 0xffff_ffff),
        ],
        mem: &[],
    },
    Case {
        name: "a float compare choosing the smaller under IT",
        at: 0x1_03a0,
        code: Code::Thumb(T_FLOAT),
        set: &[("r0", 0x3fc0_0000), ("r1", 0x4020_0000)],
        want: &[("r2", 0x3fc0_0000), ("r3", 1)],
        mem: &[],
    },
    Case {
        name: "a float compare choosing the second under IT",
        at: 0x1_03a0,
        code: Code::Thumb(T_FLOAT),
        set: &[("r0", 0xc070_0000), ("r1", 0xc080_0000)],
        want: &[("r2", 0xc080_0000), ("r3", 0xffff_fffc)],
        mem: &[],
    },
];

/// A raw ARM32 image whose only section, at `at`, holds `code`, its
/// instruction sets marked.
///
/// # Arguments
///
/// * `at` - Where the code is placed.
/// * `code` - The code.
pub(crate) fn image(at: u64, code: Code<'_>) -> Program {
    let (bytes, marks): (Vec<u8>, Vec<(u64, Mode)>) = match code {
        Code::Arm(words) => (
            words.iter().flat_map(|w| w.to_le_bytes()).collect(),
            vec![(at, Mode::Arm)],
        ),
        Code::Thumb(halves) => (
            halves.iter().flat_map(|h| h.to_le_bytes()).collect(),
            vec![(at, Mode::Thumb)],
        ),
        Code::Mixed { words, thumb_from } => (
            words.iter().flat_map(|w| w.to_le_bytes()).collect(),
            vec![(at, Mode::Arm), (at + thumb_from, Mode::Thumb)],
        ),
    };
    let len = u64::try_from(bytes.len()).expect("a small image");
    let text = Section::mapped(".text", at, 0, len, false, true);
    let mut p = Program::raw(bytes, Arch::Arm, 0, Some(at), vec![text]);
    p.modes = Modes::from_marks(marks);
    p
}

/// A machine over `p` with [`DATA`] planted.
///
/// # Arguments
///
/// * `p` - The image.
fn machine(p: &Program) -> Machine<'_> {
    let mut m = Machine::new(p, BUDGET).expect("an ARM32 machine");
    for (at, k) in (DATA_AT..).zip(0..PLANTED) {
        m.poke(at, DATA.get(k).copied().unwrap_or(0));
    }
    m
}

/// Every routine returns, leaving the registers and memory it should.
#[test]
fn every_routine_leaves_what_the_architecture_says() {
    for c in CASES {
        let p = image(c.at, c.code);
        let mut m = machine(&p);
        for (reg, v) in c.set {
            assert!(m.set_register(reg, *v), "{}: set {reg}", c.name);
        }
        let run = m.run(c.at);
        assert_eq!(run.stop, Stop::Returned, "{}: {:?}", c.name, run.stop);
        for (reg, v) in c.want {
            assert_eq!(
                m.register(reg),
                Some(*v),
                "{}: {reg} is {:#x?}, not {v:#x}",
                c.name,
                m.register(reg)
            );
        }
        for (at, bytes) in c.mem {
            let got: Vec<Option<u8>> = (*at..).take(bytes.len()).map(|a| m.byte_at(a)).collect();
            let want: Vec<Option<u8>> = bytes.iter().map(|b| Some(*b)).collect();
            assert_eq!(got, want, "{}: memory at {at:#x}", c.name);
        }
    }
}

/// An Advanced SIMD instruction stops the run and names itself.
#[test]
fn an_advanced_simd_word_stops_the_run() {
    // ASM: vadd.i32 q8, q9, q8
    let p = image(0x1_0000, Code::Thumb(&[0xef62, 0x08e0, 0x4770]));
    let mut m = machine(&p);
    let run = m.run(0x1_0000);
    assert!(
        matches!(&run.stop, Stop::Unmodeled(what) if what.contains("neon")),
        "{:?}",
        run.stop
    );
}

/// Random A32 words and T32 halfwords run to a stop without a panic.
#[test]
fn random_words_run_to_a_stop() {
    let mut x: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for round in 0..64 {
        let words: Vec<u32> = (0..32)
            .map(|_| u32::try_from(next() >> 32).expect("32 bits"))
            .collect();
        for code in [
            Code::Arm(&words),
            Code::Mixed {
                words: &words,
                thumb_from: 0,
            },
        ] {
            let p = image(0x1_0000, code);
            let mut m = machine(&p);
            let run = m.run(0x1_0000);
            assert!(run.steps <= BUDGET, "round {round}: {:?}", run.stop);
        }
    }
}
