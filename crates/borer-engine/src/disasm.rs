//! Linear disassembly of x86/x86-64 code (iced-x86).
//!
//! iced stays the fast x86 path (and the future encoder for patching); a
//! multi-architecture lifter would sit beside it rather than replace it.

use crate::isa::{Code, Decoder, DecoderOptions, Formatter, Instruction, NasmFormatter};

/// One decoded instruction as text.
#[derive(Debug, Clone)]
pub struct DisasmLine {
    /// Virtual address of the first byte.
    pub va: u64,
    /// The encoded bytes (empty when the decoder ran past the buffer).
    pub bytes: Vec<u8>,
    /// NASM-syntax text, or `(bad)` for undecodable bytes.
    pub text: String,
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
        });
    }
    out
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
