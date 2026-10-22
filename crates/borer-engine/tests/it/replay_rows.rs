//! Statements whose text once disagreed with the machine on a block of a
//! system library, each cut down to the instructions that disagreed.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use crate::decompiled::{decompiled, program64, replays_clean};

/// Decompiles the function at the start of `p` and requires its text to
/// agree with the machine on every block.
///
/// # Arguments
///
/// * `p` - The program, its function at 0x140001000.
///
/// # Returns
///
/// The text, for the caller's own assertions.
fn replayed(p: &Program) -> String {
    let text = decompiled(p, 0x1_4000_1000);
    let a = Analysis::compute(p);
    replays_clean(p, &a, &[0x1_4000_1000]);
    text
}

/// A `movq` between vector registers keeps the low qword and clears the
/// rest, so packed work over the copy sees zero upper lanes.
///
/// `movdqu xmm7,[rcx]; movq xmm3,xmm7; paddd xmm3,xmm3; movdqu
/// [rdx],xmm3; ret`, the copy of a loop's constant vector a system
/// library's allocator makes, once copied all sixteen bytes; and the
/// truncated copy widened back into the vector is zero-extended, not
/// sign-extended through `int64_t`.
#[test]
fn a_qword_move_between_vector_registers_clears_the_upper_lanes() {
    let code = [
        0xf3, 0x0f, 0x6f, 0x39, // ASM: movdqu xmm7,[rcx]
        0xf3, 0x0f, 0x7e, 0xdf, // ASM: movq xmm3,xmm7
        0x66, 0x0f, 0xfe, 0xdb, // ASM: paddd xmm3,xmm3
        0xf3, 0x0f, 0x7f, 0x1a, // ASM: movdqu [rdx],xmm3
        0xc3, // ASM: ret
    ];
    let text = replayed(&program64(&code));
    assert!(
        text.contains("(uint128_t)(uint64_t)*(uint128_t*)a1"),
        "{text}"
    );
}
