//! How an arm64 function opens and closes, read off its instruction words.
//!
//! A compiler opens an arm64 function in few ways: it signs the return
//! address (`paciasp`, `pacibsp`), lands an indirect call (`bti c`), pushes
//! a register pair or one register onto the stack with a pre-indexed store
//! (`stp x29, x30, [sp, #-16]!`), or takes its frame in one subtraction
//! (`sub sp, sp, #0x40`). The middle of a function does none of these, so
//! a gap no function covers is guessed to be a function only where it
//! opens with one ([`opens`]), and a call followed by a pre-indexed push
//! is a call that never returns ([`opens_surely`]). A function closes by
//! popping what it pushed, which is how a jump right after is known to be
//! a tail call ([`tears_down`]).
//!
//! The words are matched by their fixed bits, so `bti j`, the landing pad
//! of a jump table's case, is told from `bti c`, which the decoder's
//! [`crate::isa::a64::Op::Bti`] does not separate.

/// `paciasp`: signs the return address with key A.
const PACIASP: u32 = 0xd503_233f;
/// `pacibsp`: signs the return address with key B, as Windows does.
const PACIBSP: u32 = 0xd503_237f;
/// `bti c`: the landing pad of an indirect call.
const BTI_C: u32 = 0xd503_245f;
/// `bti jc`: the landing pad of an indirect call or jump.
const BTI_JC: u32 = 0xd503_24df;
/// `autiasp`: authenticates the return address with key A before a return.
const AUTIASP: u32 = 0xd503_23bf;
/// `autibsp`: authenticates the return address with key B.
const AUTIBSP: u32 = 0xd503_23ff;
/// `nop`: what an assembler aligns code with.
const NOP: u32 = 0xd503_201f;
/// The fixed bits, then their value, of `stp <Xt1>, <Xt2>, [sp, #-imm]!`:
/// a 64-bit register pair stored pre-indexed below `sp`, the offset's
/// sign bit set.
const STP_PUSH: (u32, u32) = (0xffe0_03e0, 0xa9a0_03e0);
/// The fixed bits, then their value, of `str <Xt>, [sp, #-imm]!`: one
/// 64-bit register stored pre-indexed below `sp`, the offset's sign bit
/// set.
const STR_PUSH: (u32, u32) = (0xfff0_0fe0, 0xf810_0fe0);
/// The fixed bits, then their value, of `sub sp, sp, #imm{, lsl #12}`.
const SUB_SP: (u32, u32) = (0xff80_03ff, 0xd100_03ff);
/// The fixed bits, then their value, of `ldp <Xt1>, <Xt2>, [sp], #imm`: a
/// 64-bit register pair loaded post-indexed from `sp`.
const LDP_POP: (u32, u32) = (0xffc0_03e0, 0xa8c0_03e0);
/// The fixed bits, then their value, of `ldr <Xt>, [sp], #imm`: one 64-bit
/// register loaded post-indexed from `sp`.
const LDR_POP: (u32, u32) = (0xffe0_0fe0, 0xf840_07e0);
/// The fixed bits, then their value, of `add sp, sp, #imm{, lsl #12}`.
const ADD_SP: (u32, u32) = (0xff80_03ff, 0x9100_03ff);

/// Tells whether a word matches an encoding's fixed bits.
///
/// # Arguments
///
/// * `word` - The instruction word.
/// * `pattern` - The fixed bits, then their value.
fn fits(word: u32, pattern: (u32, u32)) -> bool {
    word & pattern.0 == pattern.1
}

/// Tells whether a word is one only a function's first instructions are:
/// a return address signed, an indirect call landed, a register pair or
/// a register pushed.
///
/// SPEC: Arm ARM (DDI 0487) C6.2: `PACIASP`, `PACIBSP` and `BTI` are
/// `HINT` #25, #27 and #34/#38; `STP` and `STR` (immediate, pre-index)
/// with `Rn` = 31 address `sp`.
///
/// # Arguments
///
/// * `word` - The instruction word.
pub(super) fn opens_surely(word: u32) -> bool {
    matches!(word, PACIASP | PACIBSP | BTI_C | BTI_JC)
        || fits(word, STP_PUSH)
        || fits(word, STR_PUSH)
}

/// Tells whether a word opens a function the way compilers open one:
/// [`opens_surely`], or the whole frame taken at once by a subtraction
/// from `sp`.
///
/// # Arguments
///
/// * `word` - The instruction word.
pub(super) fn opens(word: u32) -> bool {
    opens_surely(word) || fits(word, SUB_SP)
}

/// Tells whether a word undoes a frame: a register pair or a register
/// popped off `sp`, the frame released by an addition to `sp`, or the
/// return address authenticated.
///
/// SPEC: Arm ARM (DDI 0487) C6.2: `LDP` and `LDR` (immediate,
/// post-index) and `ADD` (immediate) with `Rn` = 31; `AUTIASP` and
/// `AUTIBSP` are `HINT` #29 and #31.
///
/// # Arguments
///
/// * `word` - The instruction word.
pub(super) fn tears_down(word: u32) -> bool {
    matches!(word, AUTIASP | AUTIBSP)
        || fits(word, LDP_POP)
        || fits(word, LDR_POP)
        || fits(word, ADD_SP)
}

/// Tells whether a word is padding between functions: zero, which decodes
/// as `udf #0`, or `nop`.
///
/// # Arguments
///
/// * `word` - The instruction word.
pub(super) fn is_padding(word: u32) -> bool {
    matches!(word, 0 | NOP)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{is_padding, opens, opens_surely, tears_down};

    /// The openings, closings and padding match the words LLVM assembles
    /// for them, and their neighbours do not.
    #[test]
    fn words_open_close_and_pad_as_assembled() {
        // ASM: paciasp; pacibsp; bti c; bti jc
        for w in [0xd503_233f, 0xd503_237f, 0xd503_245f, 0xd503_24df] {
            assert!(opens_surely(w), "{w:#010x}");
        }
        // ASM: stp x29, x30, [sp, #-16]!; stp x20, x19, [sp, #-32]!; str x19, [sp, #-16]!
        for w in [0xa9bf_7bfd, 0xa9be_4ff4, 0xf81f_0ff3] {
            assert!(opens_surely(w), "{w:#010x}");
        }
        // ASM: sub sp, sp, #0x20
        assert!(opens(0xd100_83ff) && !opens_surely(0xd100_83ff));
        // ASM: bti j; stp x29, x30, [sp, #16]; stp x29, x30, [sp, #16]!; str x19, [x0, #-16]!; sub sp, sp, x15
        for w in [
            0xd503_249f,
            0xa901_7bfd,
            0xa981_7bfd,
            0xf81f_0c13,
            0xcb2f_63ff,
        ] {
            assert!(!opens(w), "{w:#010x}");
        }
        // ASM: ldp x29, x30, [sp], #16; ldr x30, [sp], #16; add sp, sp, #0x20; autiasp
        for w in [0xa8c1_7bfd, 0xf841_07fe, 0x9100_83ff, 0xd503_23bf] {
            assert!(tears_down(w), "{w:#010x}");
        }
        // ASM: ldp x29, x30, [sp, #16]; add x0, sp, #0x20
        for w in [0xa941_7bfd, 0x9100_83e0] {
            assert!(!tears_down(w), "{w:#010x}");
        }
        assert!(is_padding(0) && is_padding(0xd503_201f) && !is_padding(0xd503_233f));
    }
}
