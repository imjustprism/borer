//! Assembly text for one A64 instruction.

use std::fmt::Write as _;

use yaxpeax_arch::{Decoder as _, U8Reader};
use yaxpeax_arm::armv8::a64::{InstDecoder, Operand};

use super::{Insn, Op, Opnd};

/// What a listing shows for a word that decodes to no instruction, as the
/// x86 listing does.
const BAD: &str = "(bad)";

/// Renders one instruction as assembly text.
///
/// The decoder's own syntax and aliases (`mov x0, #0x10`, `ldr x1, [sp,
/// #0x8]`, `cmp w0, #0x3`), with two changes: a PC-relative operand is
/// printed as the absolute address it resolves to (`bl 0x100003f40`,
/// `adrp x8, 0x100004000`) rather than as an offset from the instruction,
/// and the `bti` hints are named.
///
/// # Arguments
///
/// * `insn` - The decoded instruction.
///
/// # Returns
///
/// The text; `.inst 0x........ ; sve` (or `; sme`) for a word in an
/// encoding space the decoder does not model, and `(bad)` for a word that
/// decodes to no instruction.
#[must_use]
pub fn text(insn: &Insn) -> String {
    match insn.op {
        Op::Sve => return format!(".inst {:#010x} ; sve", insn.word),
        Op::Sme => return format!(".inst {:#010x} ; sme", insn.word),
        Op::Invalid => return BAD.to_owned(),
        Op::Bti => {
            // SPEC: Arm ARM (DDI 0487), BTI is HINT #(32 | targets << 1), numbered in CRm:op2 (bits 5..11).
            return match (insn.word >> 5) & 0x7f {
                0x22 => "bti c",
                0x24 => "bti j",
                0x26 => "bti jc",
                _ => "bti",
            }
            .to_owned();
        }
        Op::B
        | Op::BCond(_)
        | Op::Cbz
        | Op::Cbnz
        | Op::Tbz
        | Op::Tbnz
        | Op::Bl
        | Op::Br
        | Op::Blr
        | Op::Ret
        | Op::Eret
        | Op::Trap
        | Op::Syscall
        | Op::Adr
        | Op::Adrp
        | Op::Nop
        | Op::Pac
        | Op::Other => {}
    }
    let bytes = insn.word.to_le_bytes();
    let Ok(inst) = InstDecoder::default().decode(&mut U8Reader::new(&bytes)) else {
        return BAD.to_owned();
    };
    let mut out = String::new();
    if write!(out, "{inst}").is_err() {
        return BAD.to_owned();
    }
    for (theirs, ours) in inst.operands.iter().zip(&insn.operands) {
        if let (Operand::PCOffset(off), Opnd::PcRel(at)) = (theirs, ours) {
            let relative = if *off < 0 {
                format!("$-{:#x}", off.unsigned_abs())
            } else {
                format!("$+{off:#x}")
            };
            out = out.replacen(&relative, &format!("{at:#x}"), 1);
        }
    }
    out
}
