//! Linear disassembly: x86/x86-64 through iced-x86, AArch64 through
//! [`crate::isa::a64`], ARM32 through [`crate::isa::a32`], RISC-V through
//! [`crate::isa::rv`].
//!
//! [`disassemble_isa`] picks the decoder an instruction set needs;
//! [`disassemble`] is the x86 sweep the x86-only passes call directly.

use crate::isa::Isa;
use crate::isa::x86::{
    Code, Decoder, DecoderOptions, Formatter, FormatterOutput, FormatterTextKind, Instruction,
    Mnemonic, NasmFormatter, NumberKind, OpKind, PrefixKind, Register,
};
use crate::isa::{a32, a64, rv};
use crate::program::Program;
use crate::view::{Kind, Ref, Sink};

/// One decoded instruction as text.
#[derive(Debug, Clone)]
pub struct DisasmLine {
    /// Virtual address of the first byte.
    pub va: u64,
    /// The encoded bytes (empty when the decoder ran past the buffer).
    pub bytes: Vec<u8>,
    /// NASM-syntax text for x86, the decoder's syntax for AArch64, ARM32 and
    /// RISC-V, or `(bad)` for undecodable bytes.
    pub text: String,
    /// Direct branch or call target reported by the AArch64, ARM32 or RISC-V
    /// decoder; `None` for other instructions and on x86, whose function
    /// listings decode through [`decode_x86`].
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

/// Returns the operand size of a stack instruction in bits.
///
/// Gives how wide each value a `push`, `pop`, `pushf`, `popf`, `pusha`, `popa`
/// or `leave` moves is, and so how far it moves the stack pointer per value.
///
/// SPEC: Intel SDM Vol. 2, PUSH, POP, PUSHA, POPA, PUSHF, POPF and LEAVE:
/// the operand size, not the mode's word, sets the move, so a 66h prefix
/// makes it a word (`66 6a 07` in 64-bit code pushes two bytes). iced
/// counts a push or a pop's whole move
/// ([`Instruction::stack_pointer_increment`]), eight values for `pusha`,
/// and nothing for `leave`, whose size its code names.
///
/// # Arguments
///
/// * `instr` - The instruction.
///
/// # Returns
///
/// 16, 32 or 64, or `None` for any other instruction: iced counts the
/// moves of `ret 4` and `enter 8, 0` too, which are no value's size.
#[must_use]
pub(crate) fn stack_operand_bits(instr: &Instruction) -> Option<u8> {
    match instr.code() {
        Code::Leavew | Code::Pushaw | Code::Popaw => Some(16),
        Code::Leaved | Code::Pushad | Code::Popad => Some(32),
        Code::Leaveq => Some(64),
        _ if matches!(
            instr.mnemonic(),
            Mnemonic::Push
                | Mnemonic::Pop
                | Mnemonic::Pushf
                | Mnemonic::Pushfd
                | Mnemonic::Pushfq
                | Mnemonic::Popf
                | Mnemonic::Popfd
                | Mnemonic::Popfq
        ) =>
        {
            let bytes = instr.stack_pointer_increment().unsigned_abs();
            bytes.checked_mul(8).and_then(|b| u8::try_from(b).ok())
        }
        _ => None,
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

/// Tells whether a memory operand of 64-bit code is addressed with 32-bit
/// registers: an address-size prefix (`67 48 8d 41 08` is `lea rax,
/// [ecx+8]`).
///
/// SPEC: Intel SDM Vol. 1, 3.3.7: with a 32-bit address size in 64-bit
/// mode the effective address is computed modulo 2^32 and zero-extended.
/// iced names the 32-bit registers and reports a full displacement of that
/// address size as four bytes wide.
///
/// # Arguments
///
/// * `instr` - An instruction with a memory operand.
/// * `bitness` - Decoder bitness (32 or 64).
pub fn wraps_at_32(instr: &Instruction, bitness: u32) -> bool {
    bitness == 64
        && (instr.memory_base().size() == 4
            || instr.memory_index().size() == 4
            || instr.memory_displ_size() == 4)
}

/// Returns how many bits a memory operand's effective address keeps.
///
/// 16 under a 16-bit address ([`addresses_16_bit`]), 32 in 32-bit code
/// and under a 32-bit address of 64-bit code ([`wraps_at_32`]), else 64.
///
/// # Arguments
///
/// * `instr` - An instruction with a memory operand.
/// * `bitness` - Decoder bitness (32 or 64).
#[must_use]
pub fn address_bits(instr: &Instruction, bitness: u32) -> u8 {
    if addresses_16_bit(instr) {
        16
    } else if bitness == 32 || wraps_at_32(instr, bitness) {
        32
    } else {
        64
    }
}

/// Returns the mask of the bits a memory operand's effective address
/// keeps ([`address_bits`]).
///
/// # Arguments
///
/// * `instr` - An instruction with a memory operand.
/// * `bitness` - Decoder bitness (32 or 64).
#[must_use]
pub(crate) fn address_mask(instr: &Instruction, bitness: u32) -> u64 {
    u64::MAX >> (64 - u32::from(address_bits(instr, bitness)))
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
    let mut fmt = NasmFormatter::new();
    let mut out = Vec::with_capacity(max_instrs.min(code.len() / 4 + 1));
    let mut text = String::new();
    decode_x86(code, va, bitness, max_instrs, |d| {
        let line_text = if d.instr.code() == Code::INVALID {
            "(bad)".to_owned()
        } else {
            text.clear();
            fmt.format(&d.instr, &mut text);
            text.clone()
        };
        out.push(DisasmLine {
            va: d.va,
            bytes: d.bytes.to_vec(),
            text: line_text,
            target: None,
        });
    });
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
        Isa::A32 => disassemble_a32(code, va, &a32::Modes::default(), max_instrs),
        Isa::Rv(xlen) => sweep(code, va, max_instrs, |rest, at| {
            rv::decode(rest, at, xlen).map(|i| (usize::from(i.len), rv::text(&i), i.target()))
        }),
    }
}

/// Disassembles up to `max_instrs` instructions from `code` in the
/// program's instruction set: [`disassemble_isa`], with ARM32 code decoded
/// in the instruction set the program says each address is in.
///
/// # Arguments
///
/// * `program` - The image the bytes come from.
/// * `code` - The bytes to decode.
/// * `va` - Virtual address of `code[0]`.
/// * `isa` - The program's instruction set.
/// * `max_instrs` - Hard cap on the number of instructions returned.
///
/// # Returns
///
/// The decoded lines in address order.
pub fn disassemble_program(
    program: &Program,
    code: &[u8],
    va: u64,
    isa: Isa,
    max_instrs: usize,
) -> Vec<DisasmLine> {
    match isa {
        Isa::A32 => disassemble_a32(code, va, &program.modes, max_instrs),
        Isa::X86 { .. } | Isa::A64 | Isa::Rv(_) => disassemble_isa(code, va, isa, max_instrs),
    }
}

/// Disassembles ARM32 code in the instruction sets `modes` names.
///
/// Each instruction is read in the instruction set `modes` names for its
/// address, an `IT` block's conditions carried along ([`sweep`]).
///
/// # Arguments
///
/// * `code` - The bytes.
/// * `va` - Virtual address of `code[0]`.
/// * `modes` - Which instruction set each address is in.
/// * `max_instrs` - Hard cap on the number of instructions returned.
fn disassemble_a32(code: &[u8], va: u64, modes: &a32::Modes, max_instrs: usize) -> Vec<DisasmLine> {
    let mut it = a32::ItState::default();
    sweep(code, va, max_instrs, |rest, at| {
        a32::decode(rest, at, modes.at(at), &mut it)
            .map(|i| (usize::from(i.len), a32::text(&i), i.target()))
    })
}

/// Decodes a run of two- and four-byte instructions one at a time.
///
/// Bytes that do not make an instruction are one `(bad)` line of two
/// bytes, so a listing never drops bytes it was handed.
///
/// # Arguments
///
/// * `code` - The bytes.
/// * `va` - Virtual address of `code[0]`.
/// * `max_instrs` - Hard cap on the number of instructions returned.
/// * `decode` - Decodes the instruction at the start of the bytes at an
///   address into its length, text and branch target, or `None`.
fn sweep(
    code: &[u8],
    va: u64,
    max_instrs: usize,
    mut decode: impl FnMut(&[u8], u64) -> Option<(usize, String, Option<u64>)>,
) -> Vec<DisasmLine> {
    let mut out = Vec::new();
    let mut off = 0usize;
    while out.len() < max_instrs && off < code.len() {
        let at = va.wrapping_add(crate::num::from_usize(off));
        let rest = code.get(off..).unwrap_or_default();
        let (len, text, target) =
            decode(rest, at).unwrap_or_else(|| (rest.len().min(2), "(bad)".to_owned(), None));
        out.push(DisasmLine {
            va: at,
            bytes: rest.get(..len).map(<[u8]>::to_vec).unwrap_or_default(),
            text,
            target,
        });
        off += len;
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

/// One decoded x86 instruction and the slice it occupied.
pub(crate) struct X86Decoded<'c> {
    /// Virtual address of the first byte.
    pub(crate) va: u64,
    /// The encoded bytes.
    pub(crate) bytes: &'c [u8],
    /// The decoded instruction.
    instr: Instruction,
}

/// Targets the x86 formatter saw on one instruction, read from the decoder
/// and operand stream rather than parsed back from text.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct X86Targets {
    /// Direct `call` or `jmp` target when the first operand is the
    /// unprefixed, unsized target number.
    pub(crate) branch: Option<u64>,
    /// Bare `[rel addr]` or `[addr]` memory operand's target address, for
    /// import-slot lookup.
    pub(crate) memory: Option<u64>,
}

/// Decodes up to `max_instrs` x86 instructions from `code`, handing each to
/// `visit` without formatting into an intermediate string.
///
/// # Arguments
///
/// * `code` - The bytes to decode.
/// * `va` - Virtual address of `code[0]`.
/// * `bitness` - `32` or `64`.
/// * `max_instrs` - Hard cap on instructions decoded.
/// * `visit` - Called once per decoded instruction in address order.
///
/// # Returns
///
/// How many instructions were decoded.
pub(crate) fn decode_x86<'c>(
    code: &'c [u8],
    va: u64,
    bitness: u32,
    max_instrs: usize,
    mut visit: impl FnMut(X86Decoded<'c>),
) -> usize {
    let mut decoder = Decoder::with_ip(bitness, code, va, DecoderOptions::NONE);
    let mut count = 0usize;
    while count < max_instrs && decoder.can_decode() {
        let mut instr = Instruction::default();
        let start = decoder.position();
        decoder.decode_out(&mut instr);
        let end = decoder.position();
        visit(X86Decoded {
            va: instr.ip(),
            bytes: code.get(start..end).unwrap_or_default(),
            instr,
        });
        count += 1;
    }
    count
}

/// Formats decoded x86 instructions directly into a [`Sink`], keeping one
/// [`NasmFormatter`] across a function's blocks.
pub(crate) struct X86Format {
    /// The NASM formatter.
    fmt: NasmFormatter,
}

impl X86Format {
    /// Creates a reusable x86 instruction formatter.
    pub(crate) fn new() -> Self {
        Self {
            fmt: NasmFormatter::new(),
        }
    }

    /// Formats `decoded` into `out` and returns the targets its operands
    /// named.
    ///
    /// # Arguments
    ///
    /// * `decoded` - The decoded instruction.
    /// * `out` - Where each token is written.
    /// * `is_fn` - Tells whether a branch target starts a discovered function.
    ///
    /// # Returns
    ///
    /// The branch and bare-memory targets the instruction named.
    pub(crate) fn write<S: Sink>(
        &mut self,
        decoded: &X86Decoded<'_>,
        out: &mut S,
        is_fn: impl Fn(u64) -> bool,
    ) -> X86Targets {
        if decoded.instr.code() == Code::INVALID {
            out.put("(bad)", Kind::Text, None);
            return X86Targets::default();
        }
        let mut adapter = X86Adapter {
            out,
            is_fn,
            prefixed: false,
            branch_kw: false,
            saw_operand_tok: false,
            bracket: Bracket::Before,
        };
        self.fmt.format(&decoded.instr, &mut adapter);
        adapter.targets(&decoded.instr)
    }
}

/// How far through the first `[...]` memory operand formatting has walked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bracket {
    /// No `[` seen yet.
    Before,
    /// Inside the first `[...]`, with only whitespace or `rel` so far.
    Open,
    /// Inside the first `[...]`, after one hex address number.
    Addr(u64),
    /// Inside the first `[...]`, with a register, operator or size keyword.
    Complex,
    /// Past the first `]`, holding the bare address if that was all it held.
    Closed(Option<u64>),
}

/// Maps iced's [`FormatterTextKind`] to [`Kind`].
///
/// # Arguments
///
/// * `text` - The piece's text, used to separate whitespace from words.
/// * `kind` - The formatter's classification.
fn map_kind(text: &str, kind: FormatterTextKind) -> Kind {
    match kind {
        FormatterTextKind::Text if text.bytes().all(|b| b.is_ascii_whitespace()) => Kind::Space,
        FormatterTextKind::Mnemonic => Kind::Mnemonic,
        FormatterTextKind::Prefix
        | FormatterTextKind::Keyword
        | FormatterTextKind::Directive
        | FormatterTextKind::Decorator => Kind::Keyword,
        FormatterTextKind::Register => Kind::Register,
        FormatterTextKind::Number | FormatterTextKind::SelectorValue => Kind::Number,
        FormatterTextKind::FunctionAddress | FormatterTextKind::LabelAddress => Kind::Address,
        FormatterTextKind::Function => Kind::Function,
        FormatterTextKind::Label => Kind::Label,
        FormatterTextKind::Data => Kind::Global,
        FormatterTextKind::Operator | FormatterTextKind::Punctuation => Kind::Punct,
        _ => Kind::Text,
    }
}

/// Streams [`NasmFormatter`] pieces into a [`Sink`] while noting branch and
/// bare-memory operand targets from the instruction.
struct X86Adapter<'s, S, F> {
    /// Destination sink.
    out: &'s mut S,
    /// Tells whether a target address starts a function.
    is_fn: F,
    /// Whether `write_prefix` ran before the mnemonic.
    prefixed: bool,
    /// Whether a keyword (`short`, `near`, `word`, `dword`) preceded the first operand.
    branch_kw: bool,
    /// Whether an operand token has started.
    saw_operand_tok: bool,
    /// State of the first `[...]` memory operand.
    bracket: Bracket,
}

impl<S, F> X86Adapter<'_, S, F> {
    /// Builds [`X86Targets`] after formatting `instr`.
    ///
    /// # Arguments
    ///
    /// * `instr` - The formatted instruction.
    fn targets(&self, instr: &Instruction) -> X86Targets {
        let is_near = matches!(
            instr.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        );
        let branch = (matches!(instr.mnemonic(), Mnemonic::Call | Mnemonic::Jmp)
            && is_near
            && !self.prefixed
            && !self.branch_kw)
            .then(|| instr.near_branch_target());
        let memory = match self.bracket {
            Bracket::Closed(addr) => addr,
            Bracket::Before | Bracket::Open | Bracket::Addr(_) | Bracket::Complex => None,
        };
        X86Targets { branch, memory }
    }
}

impl<S: Sink, F: Fn(u64) -> bool> FormatterOutput for X86Adapter<'_, S, F> {
    fn write(&mut self, text: &str, kind: FormatterTextKind) {
        if kind == FormatterTextKind::Keyword && !self.saw_operand_tok {
            self.branch_kw = true;
        }
        if matches!(
            kind,
            FormatterTextKind::Register
                | FormatterTextKind::Number
                | FormatterTextKind::FunctionAddress
                | FormatterTextKind::LabelAddress
                | FormatterTextKind::SelectorValue
        ) || (kind == FormatterTextKind::Punctuation && matches!(text, "[" | ","))
        {
            self.saw_operand_tok = true;
        }
        match (self.bracket, kind, text) {
            (Bracket::Before, FormatterTextKind::Punctuation, "[") => {
                self.bracket = Bracket::Open;
            }
            (Bracket::Open, FormatterTextKind::Punctuation, "]") => {
                self.bracket = Bracket::Closed(None);
            }
            (Bracket::Addr(a), FormatterTextKind::Punctuation, "]") => {
                self.bracket = Bracket::Closed(Some(a));
            }
            (Bracket::Open | Bracket::Addr(_), FormatterTextKind::Text, t)
                if t.bytes().all(|b| b.is_ascii_whitespace()) => {}
            (Bracket::Open, FormatterTextKind::Keyword, "rel") => {}
            (Bracket::Open | Bracket::Addr(_), _, _) => {
                self.bracket = Bracket::Complex;
            }
            (Bracket::Before | Bracket::Complex | Bracket::Closed(_), _, _) => {}
        }
        self.out.put(text, map_kind(text, kind), None);
    }

    fn write_prefix(&mut self, _instruction: &Instruction, text: &str, _prefix: PrefixKind) {
        self.prefixed = true;
        self.out.put(text, Kind::Keyword, None);
    }

    fn write_number(
        &mut self,
        instruction: &Instruction,
        _operand: u32,
        instruction_operand: Option<u32>,
        text: &str,
        value: u64,
        _number_kind: NumberKind,
        kind: FormatterTextKind,
    ) {
        self.saw_operand_tok = true;
        let is_near = matches!(
            instruction.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        );
        let ip_rel_mem = instruction.is_ip_rel_memory_operand()
            && !matches!(instruction.segment_prefix(), Register::FS | Register::GS)
            && instruction_operand.is_some_and(|op| instruction.op_kind(op) == OpKind::Memory);
        let (mapped, link) = match kind {
            FormatterTextKind::FunctionAddress | FormatterTextKind::LabelAddress if is_near => {
                let r = if (self.is_fn)(value) {
                    Ref::Function(value)
                } else {
                    Ref::Address(value)
                };
                (Kind::Address, Some(r))
            }
            FormatterTextKind::Number if ip_rel_mem => (
                Kind::Number,
                Some(Ref::Address(instruction.ip_rel_memory_address())),
            ),
            _ => (map_kind(text, kind), None),
        };
        if matches!(self.bracket, Bracket::Open | Bracket::Addr(_)) {
            self.bracket = if self.bracket == Bracket::Open
                && kind == FormatterTextKind::Number
                && text.ends_with('h')
            {
                let addr = if ip_rel_mem {
                    instruction.ip_rel_memory_address()
                } else {
                    value
                };
                Bracket::Addr(addr)
            } else {
                Bracket::Complex
            };
        }
        self.out.put(text, mapped, link);
    }
}

#[cfg(test)]
mod tests {
    use super::stack_operand_bits;
    use crate::isa::x86::{Decoder, DecoderOptions};

    /// Only value-moving stack instructions report a stack operand size.
    ///
    /// A stack instruction's operand size is its own, a word under a 66h
    /// prefix, and an instruction that moves no value has none: in 32-bit
    /// code iced counts the eight bytes `ret 4` moves the stack and the
    /// twelve of `enter 8, 0`, which once read as widths of 64 and 96 bits.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn only_a_stack_instruction_has_a_stack_operand_size() {
        let bits = |code: &[u8]| {
            stack_operand_bits(&Decoder::with_ip(32, code, 0, DecoderOptions::NONE).decode())
        };
        assert_eq!(bits(&[0x50]), Some(32));
        assert_eq!(bits(&[0x66, 0x50]), Some(16));
        assert_eq!(bits(&[0x66, 0x9c]), Some(16));
        assert_eq!(bits(&[0x66, 0xc9]), Some(16));
        assert_eq!(bits(&[0xc2, 0x04, 0x00]), None);
        assert_eq!(bits(&[0xc8, 0x08, 0x00, 0x00]), None);
    }
}
