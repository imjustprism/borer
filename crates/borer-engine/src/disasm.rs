//! Linear disassembly: x86/x86-64 through iced-x86, AArch64 through
//! [`crate::isa::a64`].
//!
//! [`disassemble_isa`] picks the decoder an instruction set needs;
//! [`disassemble`] is the x86 sweep the x86-only passes call directly.

use crate::isa::Isa;
use crate::isa::a64;
use crate::isa::x86::{Code, Decoder, DecoderOptions, Formatter, Instruction, NasmFormatter};

/// One decoded instruction as text.
#[derive(Debug, Clone)]
pub struct DisasmLine {
    /// Virtual address of the first byte.
    pub va: u64,
    /// The encoded bytes (empty when the decoder ran past the buffer).
    pub bytes: Vec<u8>,
    /// NASM-syntax text for x86, the decoder's syntax for AArch64, or
    /// `(bad)` for undecodable bytes.
    pub text: String,
    /// Where a direct branch or call goes, for AArch64; `None` for every
    /// other instruction and for all x86, whose listings read the target
    /// out of the text.
    pub target: Option<u64>,
}

/// Returns a memory operand's displacement as a signed offset.
///
/// iced sign-extends a displacement only to the address width, so in 32-bit
/// code `[ebp-4]` reads back as `0xFFFF_FFFC`: four billion as a 64-bit
/// offset, not minus four. The 32-bit form is reinterpreted as the signed
/// number it encodes, which is exact.
///
/// # Arguments
///
/// * `instr` - An instruction with a memory operand.
/// * `bitness` - Decoder bitness (32 or 64).
///
/// # Returns
///
/// The displacement as a signed 64-bit offset.
pub fn displacement(instr: &Instruction, bitness: u32) -> i64 {
    if bitness == 32 {
        i64::from(instr.memory_displacement32().cast_signed())
    } else {
        instr.memory_displacement64().cast_signed()
    }
}

/// Tells whether a memory operand is addressed with 16-bit registers: an
/// address-size prefix in 32-bit code (`67 8b 45 ff` is `mov eax,
/// [di-1]`).
///
/// SPEC: Intel SDM Vol. 1, 3.7.5: a 16-bit effective address is the sum of
/// 16-bit registers and a displacement, computed modulo 2^16. iced holds the
/// displacement as the 16-bit value, zero-extended (`0xffff` for `-1`), and
/// names `di`, `bx`, `bp` or `si`; a 16-bit displacement alone is the
/// absolute form.
///
/// # Arguments
///
/// * `instr` - An instruction with a memory operand.
pub fn addresses_16_bit(instr: &Instruction) -> bool {
    instr.memory_base().size() == 2
        || instr.memory_index().size() == 2
        || instr.memory_displ_size() == 2
}

/// Disassembles up to `max_instrs` instructions from `code`.
///
/// Undecodable bytes render as `(bad)` instead of stopping the sweep, so an
/// agent can page through garbage or data without the tool giving up.
///
/// # Arguments
///
/// * `code` - The bytes to decode; decoding stops at the end of the slice.
/// * `va` - Virtual address of `code[0]`, used for instruction addresses.
/// * `bitness` - `32` or `64`.
/// * `max_instrs` - Hard cap on the number of instructions returned.
///
/// # Returns
///
/// The decoded lines in address order.
pub fn disassemble(code: &[u8], va: u64, bitness: u32, max_instrs: usize) -> Vec<DisasmLine> {
    let mut decoder = Decoder::with_ip(bitness, code, va, DecoderOptions::NONE);
    let mut fmt = NasmFormatter::new();
    let mut out = Vec::with_capacity(max_instrs.min(code.len() / 4 + 1));
    let mut text = String::new();
    while out.len() < max_instrs && decoder.can_decode() {
        let mut instr = Instruction::default();
        // The decoder's position is the instruction's offset into `code`.
        let start = decoder.position();
        decoder.decode_out(&mut instr);
        let end = decoder.position();
        let line_text = if instr.code() == Code::INVALID {
            "(bad)".to_owned()
        } else {
            text.clear();
            fmt.format(&instr, &mut text);
            text.clone()
        };
        out.push(DisasmLine {
            va: instr.ip(),
            bytes: code.get(start..end).map(<[u8]>::to_vec).unwrap_or_default(),
            text: line_text,
            target: None,
        });
    }
    out
}

/// Disassembles up to `max_instrs` instructions from `code` in the
/// instruction set given.
///
/// AArch64 decodes one four-byte word per line; trailing bytes too few for
/// a word are one `(bad)` line holding them, so a listing never drops
/// bytes it was handed, as an x86 instruction cut off by the end of the
/// buffer is.
///
/// # Arguments
///
/// * `code` - The bytes to decode; decoding stops at the end of the slice.
/// * `va` - Virtual address of `code[0]`.
/// * `isa` - The instruction set the bytes are written in.
/// * `max_instrs` - Hard cap on the number of instructions returned.
///
/// # Returns
///
/// The decoded lines in address order.
pub fn disassemble_isa(code: &[u8], va: u64, isa: Isa, max_instrs: usize) -> Vec<DisasmLine> {
    match isa {
        Isa::X86 { bits } => disassemble(code, va, bits, max_instrs),
        Isa::A64 => {
            let step = crate::num::from_usize(a64::INSN_LEN);
            let mut at = va;
            let mut out = Vec::with_capacity(max_instrs.min(code.len() / a64::INSN_LEN + 1));
            for chunk in code.chunks(a64::INSN_LEN).take(max_instrs) {
                out.push(match <[u8; a64::INSN_LEN]>::try_from(chunk) {
                    Ok(word) => {
                        let insn = a64::decode(u32::from_le_bytes(word), at);
                        DisasmLine {
                            va: at,
                            bytes: chunk.to_vec(),
                            text: a64::text(&insn),
                            target: insn.target(),
                        }
                    }
                    Err(_) => DisasmLine {
                        va: at,
                        bytes: chunk.to_vec(),
                        text: "(bad)".to_owned(),
                        target: None,
                    },
                });
                at = at.wrapping_add(step);
            }
            out
        }
    }
}

/// Renders disassembly lines as `va  text` rows.
///
/// The bytes column costs an agent more tokens than it is usually worth;
/// [`crate::hexdump::hexdump`] and [`crate::memory::read_values`] exist for
/// raw bytes.
///
/// # Arguments
///
/// * `lines` - The decoded instructions to render.
/// * `with_bytes` - Adds a `bytes` column between the address and the text.
///
/// # Returns
///
/// One row per line, each terminated by a newline.
pub fn render(lines: &[DisasmLine], with_bytes: bool) -> String {
    let mut s = String::new();
    for l in lines {
        if with_bytes {
            let mut hexb = String::new();
            for b in &l.bytes {
                hexb.push_str(&format!("{b:02x} "));
            }
            s.push_str(&format!(
                "{:#x}  {:<24} {}\n",
                l.va,
                hexb.trim_end(),
                l.text
            ));
        } else {
            s.push_str(&format!("{:#x}  {}\n", l.va, l.text));
        }
    }
    s
}
