//! A compare ladder that enters a chain of joins at every step, read
//! without a copy of the rest of the chain at each step.
//!
//! The routine is `int f(int n)` summing eight loops `for (int i = 0; i <
//! n + k; i++) s += i * (3001 + k)`, assembled by LLVM (`clang
//! --target=aarch64-linux-gnu -O2`) and checked against `llvm-objdump`;
//! each word's comment is its instruction. The compiler turns every loop
//! into a closed form and a negative `n` into a ladder of compares, each
//! jumping into the middle of the chain of closed forms.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
use borer_engine::analysis::decompile::traces::{Structure, check_structure};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Arch;

/// The eight-loop routine.
const LADDER: [u32; 87] = [
    0x7100_0408, // ASM: subs w8, w0, #0x1
    0x5400_010b, // ASM: b.lt +0x20
    0x5100_0809, // ASM: sub w9, w0, #0x2
    0x5281_772a, // ASM: mov w10, #0xbb9
    0x1281_770b, // ASM: mov w11, #-0xbb9
    0x9ba9_7d09, // ASM: umull x9, w8, w9
    0x8b49_0409, // ASM: add x9, x0, x9, lsr #1
    0x1b0a_2d29, // ASM: madd w9, w9, w10, w11
    0x1400_0003, // ASM: b +0xc
    0x37f8_0700, // ASM: tbnz w0, #0x1f, +0xe0
    0x2a1f_03e9, // ASM: mov w9, wzr
    0x1b08_7c08, // ASM: mul w8, w0, w8
    0x5281_774a, // ASM: mov w10, #0xbba
    0x1b0a_2409, // ASM: madd w9, w0, w10, w9
    0x5301_7d08, // ASM: lsr w8, w8, #1
    0x1b0a_2508, // ASM: madd w8, w8, w10, w9
    0x1100_0409, // ASM: add w9, w0, #0x1
    0x5281_776a, // ASM: mov w10, #0xbbb
    0x9ba9_7c09, // ASM: umull x9, w0, w9
    0x1b0a_2008, // ASM: madd w8, w0, w10, w8
    0xd341_fd29, // ASM: lsr x9, x9, #1
    0x1b0a_2128, // ASM: madd w8, w9, w10, w8
    0x112e_ed08, // ASM: add w8, w8, #0xbbb
    0x1100_0809, // ASM: add w9, w0, #0x2
    0x5281_778b, // ASM: mov w11, #0xbbc
    0x0aa9_7d29, // ASM: bic w9, w9, w9, asr #31
    0x5100_052a, // ASM: sub w10, w9, #0x1
    0x1b0b_2128, // ASM: madd w8, w9, w11, w8
    0x1b0a_7d2a, // ASM: mul w10, w9, w10
    0x5301_7d4a, // ASM: lsr w10, w10, #1
    0x1b0b_2148, // ASM: madd w8, w10, w11, w8
    0x1100_0c09, // ASM: add w9, w0, #0x3
    0x5281_77ab, // ASM: mov w11, #0xbbd
    0x0aa9_7d29, // ASM: bic w9, w9, w9, asr #31
    0x5100_052a, // ASM: sub w10, w9, #0x1
    0x1b0b_2128, // ASM: madd w8, w9, w11, w8
    0x9baa_7d2a, // ASM: umull x10, w9, w10
    0xd341_fd4a, // ASM: lsr x10, x10, #1
    0x1b0b_2148, // ASM: madd w8, w10, w11, w8
    0x1100_1009, // ASM: add w9, w0, #0x4
    0x5281_77cb, // ASM: mov w11, #0xbbe
    0x0aa9_7d29, // ASM: bic w9, w9, w9, asr #31
    0x5100_052a, // ASM: sub w10, w9, #0x1
    0x1b0b_2128, // ASM: madd w8, w9, w11, w8
    0x1b0a_7d2a, // ASM: mul w10, w9, w10
    0x5301_7d4a, // ASM: lsr w10, w10, #1
    0x1b0b_2148, // ASM: madd w8, w10, w11, w8
    0x1100_1409, // ASM: add w9, w0, #0x5
    0x5281_77eb, // ASM: mov w11, #0xbbf
    0x0aa9_7d29, // ASM: bic w9, w9, w9, asr #31
    0x5100_052a, // ASM: sub w10, w9, #0x1
    0x1b0b_2128, // ASM: madd w8, w9, w11, w8
    0x9baa_7d2a, // ASM: umull x10, w9, w10
    0xd341_fd4a, // ASM: lsr x10, x10, #1
    0x1b0b_2149, // ASM: madd w9, w10, w11, w8
    0x1100_1808, // ASM: add w8, w0, #0x6
    0x5281_780b, // ASM: mov w11, #0xbc0
    0x0aa8_7d08, // ASM: bic w8, w8, w8, asr #31
    0x5100_050a, // ASM: sub w10, w8, #0x1
    0x1b0a_7d0a, // ASM: mul w10, w8, w10
    0x1b0b_2508, // ASM: madd w8, w8, w11, w9
    0x5301_7d4a, // ASM: lsr w10, w10, #1
    0x1b0b_2148, // ASM: madd w8, w10, w11, w8
    0x2a08_03e0, // ASM: mov w0, w8
    0xd65f_03c0, // ASM: ret
    0x3100_081f, // ASM: cmn w0, #0x2
    0x2a1f_03e8, // ASM: mov w8, wzr
    0x54ff_fa80, // ASM: b.eq -0xb0
    0x3100_041f, // ASM: cmn w0, #0x1
    0x54ff_f960, // ASM: b.eq -0xd4
    0x3100_0c1f, // ASM: cmn w0, #0x3
    0x5400_0063, // ASM: b.lo +0xc
    0x2a1f_03e8, // ASM: mov w8, wzr
    0x17ff_ffd6, // ASM: b -0xa8
    0x3100_101f, // ASM: cmn w0, #0x4
    0x5400_0061, // ASM: b.ne +0xc
    0x2a1f_03e8, // ASM: mov w8, wzr
    0x17ff_ffda, // ASM: b -0x98
    0x3100_141f, // ASM: cmn w0, #0x5
    0x5400_0063, // ASM: b.lo +0xc
    0x2a1f_03e8, // ASM: mov w8, wzr
    0x17ff_ffde, // ASM: b -0x88
    0x2a1f_03e9, // ASM: mov w9, wzr
    0x3100_181f, // ASM: cmn w0, #0x6
    0x2a1f_03e8, // ASM: mov w8, wzr
    0x54ff_fc40, // ASM: b.eq -0x78
    0x17ff_ffe9, // ASM: b -0x5c
];

/// A ladder's arms copy a bounded tail of the chain they enter.
///
/// They jump to the rest, so the text grows with the loops rather than
/// with their square: the last loop's multiplier, `0xbc0`, is written a fixed
/// number of times, not once more for every step of the ladder. Each block
/// still agrees with the machine, and every path through the text with
/// the block graph, so no arm skips a join or jumps to the wrong one.
#[test]
fn a_ladder_into_a_chain_of_joins_copies_a_bounded_tail() {
    let code: Vec<u8> = LADDER.iter().flat_map(|w| w.to_le_bytes()).collect();
    let p = crate::raw::image(Arch::Arm64, &code, &[]);
    let a = Analysis::compute(&p);
    let entry = p.entry.expect("the image is entered at its code");
    let text = decompile(&p, &a, &Overlay::default(), entry).expect("decompiles");
    assert!(text.matches("0xbc0").count() <= 10, "{text}");
    assert!(text.lines().count() <= 75, "{text}");
    let r = replay_function(&p, &a, entry, 1);
    assert!(r.checked > 0, "{}", replay_tsv(&r));
    assert!(r.wrong().is_empty(), "{}", replay_tsv(&r));
    let structure = check_structure(&p, &a, &Overlay::default(), entry, &text);
    assert_eq!(structure, Structure::Agrees, "{text}");
}
