//! Byte signatures and YARA rules: patterns that find the same code again in
//! another build or another sample.
//!
//! A signature is a function's leading bytes with every byte that moves
//! between builds wildcarded, the displacement of a RIP-relative operand,
//! an absolute address, a branch's offset, grown one instruction at a time
//! until the pattern matches the image exactly once. A YARA rule carries the
//! signatures of chosen functions and the strings they reference, with a
//! condition on the file's magic.

use super::summary::referenced_literal;
use super::{Analysis, Function, Overlay, name_of};
use crate::emulate::{CANARY_FS, CANARY_GS};
use crate::isa::x86::{
    Decoder, DecoderOptions, FlowControl, Instruction, Mnemonic, OpKind, Register, xmm_slot,
};
use crate::program::{Arch, BinaryFormat, Program};
use crate::search;
use std::fmt::Write as _;

/// Longest signature tried, in bytes.
const SIGNATURE_MAX: usize = 96;

/// Fixed bytes a signature holds at least before it is tested, so a short
/// common prologue is not reported as unique by chance.
const FIXED_MIN: usize = 6;

/// Non-idiom fixed bytes a YARA code string holds before it is tested.
const OWN_MIN: usize = 12;

/// Extra leading bytes decoded past [`SIGNATURE_MAX`] so a prologue does not
/// shorten a YARA code string.
const PROLOGUE_ROOM: usize = 160;

/// Letters outside `printf` directives a YARA text string holds at least.
const STRING_MIN: usize = 6;

/// A function's byte signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    /// The bytes, `None` where a byte moves between builds.
    pub pattern: Vec<Option<u8>>,
    /// How many places in the image it matches.
    pub matches: usize,
}

impl Signature {
    /// The pattern as `search` and most tools write it: `48 8B ?? ??`.
    #[must_use]
    pub fn spaced(&self) -> String {
        self.pattern
            .iter()
            .map(|b| b.map_or_else(|| "??".to_owned(), |b| format!("{b:02X}")))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The pattern as a C string and mask, as code-scanning libraries take
    /// it: `\x48\x8B\x00` and `xx?`.
    #[must_use]
    pub fn code_and_mask(&self) -> (String, String) {
        let mut code = String::new();
        let mut mask = String::new();
        for b in &self.pattern {
            let _ = write!(code, "\\x{:02X}", b.unwrap_or(0));
            mask.push(if b.is_some() { 'x' } else { '?' });
        }
        (code, mask)
    }
}

/// Whether a value is an address inside the image, so the bytes that hold
/// it move when the image is rebuilt or rebased.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `value` - The operand's value.
fn in_image(p: &Program, value: u64) -> bool {
    p.section_at(value).is_some()
}

/// Returns the x86 decoder bitness (`32` or `64`) for a program's architecture.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// `64` for `x86-64` or `32` for `x86`.
///
/// # Errors
///
/// When `p` is neither `x86` nor `x86-64`.
fn x86_bitness(p: &Program) -> Result<u32, String> {
    match p.arch {
        Arch::X86_64 => Ok(64),
        Arch::X86 => Ok(32),
        other => Err(format!(
            "byte signatures read x86 and x86-64 code; this image is {}",
            other.name()
        )),
    }
}

/// Masks the bytes of one decoded instruction that move when the image is rebuilt.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `decoder` - Decoder positioned right after `instr`.
/// * `instr` - The decoded instruction.
/// * `code` - Raw bytes of `instr`.
///
/// # Returns
///
/// One entry per byte of `code`, `None` where an operand moves between builds.
fn masked_instr(
    p: &Program,
    decoder: &mut Decoder<'_>,
    instr: &Instruction,
    code: &[u8],
) -> Vec<Option<u8>> {
    let offsets = decoder.get_constant_offsets(instr);
    let mut moving = vec![false; instr.len()];
    let mut mark = |at: usize, size: usize| {
        for m in moving.iter_mut().skip(at).take(size) {
            *m = true;
        }
    };
    if offsets.has_displacement()
        && (instr.is_ip_rel_memory_operand()
            || (offsets.displacement_size() >= 4 && in_image(p, instr.memory_displacement64())))
    {
        mark(offsets.displacement_offset(), offsets.displacement_size());
    }
    let branch = matches!(
        instr.flow_control(),
        FlowControl::Call | FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch
    ) && instr.near_branch_target() != 0;
    let address = crate::analysis::sigs::immediate_operand(instr)
        .is_some_and(|op| offsets.immediate_size() >= 4 && in_image(p, instr.immediate(op)));
    if offsets.has_immediate() && (branch || address) {
        mark(offsets.immediate_offset(), offsets.immediate_size());
    }
    code.iter()
        .zip(&moving)
        .map(|(&b, &m)| if m { None } else { Some(b) })
        .collect()
}

/// Trims leading and trailing wildcards from a byte pattern slice.
///
/// # Arguments
///
/// * `pattern` - Candidate byte pattern with `None` wildcards.
///
/// # Returns
///
/// Subslice bounded by the first and last fixed bytes, or empty if all wildcards.
fn trim_wildcards(mut pattern: &[Option<u8>]) -> &[Option<u8>] {
    while let Some((None, rest)) = pattern.split_first() {
        pattern = rest;
    }
    while let Some((None, rest)) = pattern.split_last() {
        pattern = rest;
    }
    pattern
}

/// Decodes instructions from `bytes` at `va` and masks build-moving bytes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `bitness` - Decoder bitness (`32` or `64`).
/// * `va` - Virtual address of `bytes[0]`.
/// * `bytes` - Machine bytes to decode, stopping at the first invalid opcode.
///
/// # Returns
///
/// Decoded instructions paired with their per-byte wildcard masks.
fn decode_masked(
    p: &Program,
    bitness: u32,
    va: u64,
    bytes: &[u8],
) -> Vec<(Instruction, Vec<Option<u8>>)> {
    let mut decoder = Decoder::with_ip(bitness, bytes, va, DecoderOptions::NONE);
    let mut out = Vec::new();
    while decoder.can_decode() {
        let instr = decoder.decode();
        if instr.is_invalid() {
            break;
        }
        let start = crate::num::saturating_usize(instr.ip().saturating_sub(va));
        let end_off = start.saturating_add(instr.len());
        let code = bytes.get(start..end_off).unwrap_or_default();
        out.push((instr, masked_instr(p, &mut decoder, &instr, code)));
    }
    out
}

/// Builds the shortest byte signature for code at an address that matches
/// the image once.
///
/// It reads no further than `end`: a function's signature is its own
/// bytes, never the code that happens to follow it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `va` - Where the code starts: a function's entry or any instruction.
/// * `end` - Where the code stops: the function's end, or `None` to read
///   up to the longest signature tried.
///
/// # Returns
///
/// The shortest unique [`Signature`], or the full bounded prefix when not unique.
///
/// # Errors
///
/// When the image is not x86 or x86-64 code, or nothing is mapped at `va`.
pub fn signature(p: &Program, va: u64, end: Option<u64>) -> Result<Signature, String> {
    let bitness = x86_bitness(p)?;
    let room = end.map_or(SIGNATURE_MAX, |e| {
        crate::num::saturating_usize(e.saturating_sub(va)).min(SIGNATURE_MAX)
    });
    let bytes = p
        .read_va_upto(va, room)
        .filter(|b| !b.is_empty())
        .ok_or_else(|| format!("nothing is mapped at {va:#x}"))?;
    let mut pattern: Vec<Option<u8>> = Vec::new();
    let mut best = Signature {
        pattern: Vec::new(),
        matches: 0,
    };
    for (_, masked) in decode_masked(p, bitness, va, bytes) {
        pattern.extend(masked);
        if pattern.iter().flatten().count() < FIXED_MIN {
            continue;
        }
        let mut trimmed = pattern.clone();
        while trimmed.last().is_some_and(Option::is_none) {
            trimmed.pop();
        }
        let matches = search::find_bytes(p, &trimmed, 0).total;
        best = Signature {
            pattern: trimmed,
            matches,
        };
        if matches <= 1 {
            break;
        }
    }
    if best.pattern.is_empty() {
        while pattern.last().is_some_and(Option::is_none) {
            pattern.pop();
        }
        if pattern.is_empty() {
            return Err(format!("no instruction decodes at {va:#x}"));
        }
        let matches = search::find_bytes(p, &pattern, 0).total;
        return Ok(Signature { pattern, matches });
    }
    Ok(best)
}

/// Renders a function's signature in the forms tools take, and whether it
/// is unique.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results, for the name.
/// * `o` - User names.
/// * `va` - The function's entry, or any code address.
///
/// # Errors
///
/// As [`signature`].
pub fn signature_tsv(p: &Program, a: &Analysis, o: &Overlay, va: u64) -> Result<String, String> {
    let end = a.function_at(va).map(|f| f.end);
    let sig = signature(p, va, end)?;
    let (code, mask) = sig.code_and_mask();
    let named = a.function_at(va).map_or_else(
        || format!("{va:#x}"),
        |f| format!("{}{}", name_of(a, o, f.entry), f.offset_of(va)),
    );
    let verdict = match sig.matches {
        1 => "unique in the image".to_owned(),
        0 => "matches nothing: the bytes were read past mapped code".to_owned(),
        n => format!(
            "still matches {n} places at the end of the code read: the function's body is duplicated; sign a caller instead"
        ),
    };
    Ok(format!(
        "# signature of {named} at {va:#x}: {} bytes, {} wildcarded, {verdict}\npattern  {}\ncode     {code}\nmask     {mask}\n# search with: borer search <binary> \"{}\"\n",
        sig.pattern.len(),
        sig.pattern.iter().filter(|b| b.is_none()).count(),
        sig.spaced(),
        sig.spaced()
    ))
}

/// Tells whether a decoded instruction is alignment or trap padding.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
///
/// # Returns
///
/// `true` for `nop`, `int3`, or a zero-displacement `lea r, [r]` filler.
fn is_padding(instr: &Instruction) -> bool {
    matches!(instr.mnemonic(), Mnemonic::Nop | Mnemonic::Int3)
        || (instr.mnemonic() == Mnemonic::Lea
            && instr.op0_kind() == OpKind::Register
            && instr.memory_base() == instr.op0_register()
            && instr.memory_index() == Register::None
            && instr.memory_displacement64() == 0)
}

/// Tells whether `reg` is a callee-saved general-purpose register on x86 or x86-64.
///
/// # Arguments
///
/// * `reg` - Any register operand.
///
/// # Returns
///
/// `true` when `reg`'s full register is `rbx`, `rbp`, `rsi`, `rdi`, or `r12`..`r15`.
fn is_callee_saved(reg: Register) -> bool {
    matches!(
        reg.full_register(),
        Register::RBX
            | Register::RBP
            | Register::RSI
            | Register::RDI
            | Register::R12
            | Register::R13
            | Register::R14
            | Register::R15
    )
}

/// Tells whether `reg` carries an incoming register argument under `p`'s convention.
///
/// # Arguments
///
/// * `p` - The loaded image, for architecture and binary format.
/// * `reg` - The source register of a prologue store.
///
/// # Returns
///
/// `true` when `reg` is an integer or vector parameter register for `p`.
fn is_arg_reg(p: &Program, reg: Register) -> bool {
    match p.arch {
        Arch::X86_64 if p.format == BinaryFormat::Pe => {
            matches!(
                reg.full_register(),
                Register::RCX | Register::RDX | Register::R8 | Register::R9
            ) || xmm_slot(reg).is_some_and(|s| s < 4)
        }
        Arch::X86_64 => {
            matches!(
                reg.full_register(),
                Register::RDI
                    | Register::RSI
                    | Register::RDX
                    | Register::RCX
                    | Register::R8
                    | Register::R9
            ) || xmm_slot(reg).is_some_and(|s| s < 8)
        }
        Arch::X86 => matches!(reg.full_register(), Register::RCX | Register::RDX),
        _ => false,
    }
}

/// Tells whether `instr` mixes `cookie` with the stack or frame pointer (`xor rax, rsp`).
///
/// # Arguments
///
/// * `instr` - Candidate `xor` instruction.
/// * `cookie` - Full register holding the loaded stack cookie.
///
/// # Returns
///
/// `true` when `instr` `xor`s `cookie` with `rsp`, `rbp`, `esp`, or `ebp`.
fn is_cookie_xor(instr: &Instruction, cookie: Register) -> bool {
    instr.mnemonic() == Mnemonic::Xor
        && instr.op0_kind() == OpKind::Register
        && instr.op0_register().full_register() == cookie
        && instr.op1_kind() == OpKind::Register
        && matches!(
            instr.op1_register(),
            Register::RSP | Register::RBP | Register::ESP | Register::EBP
        )
}

/// Tells whether `instr` clears `reg` with a self-`xor` (`xor eax, eax`).
///
/// # Arguments
///
/// * `instr` - Candidate `xor` instruction.
/// * `reg` - Full register expected to be scrubbed.
///
/// # Returns
///
/// `true` when `instr` `xor`s `reg` (or its 32-bit subregister) with itself.
fn is_zero_scrub(instr: &Instruction, reg: Register) -> bool {
    instr.mnemonic() == Mnemonic::Xor
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Register
        && instr.op0_register() == instr.op1_register()
        && instr.op0_register().full_register() == reg
}

/// Tells whether `instr`'s memory operand addresses a stack-frame slot.
///
/// # Arguments
///
/// * `instr` - Instruction with a memory operand.
/// * `sp_alias` - Optional full register aliasing the entry stack pointer.
///
/// # Returns
///
/// `true` when the base is `rsp`, `rbp`, `esp`, `ebp` or `sp_alias`, with no
/// index register and no `fs` or `gs` segment.
fn on_frame(instr: &Instruction, sp_alias: Option<Register>) -> bool {
    let base = instr.memory_base();
    !matches!(instr.memory_segment(), Register::FS | Register::GS)
        && instr.memory_index() == Register::None
        && (matches!(
            base,
            Register::RSP | Register::RBP | Register::ESP | Register::EBP
        ) || sp_alias.is_some_and(|a| base.full_register() == a))
}

/// Tells whether `instr` stores `cookie` into a stack-frame slot.
///
/// # Arguments
///
/// * `instr` - Candidate `mov` store instruction.
/// * `cookie` - Full register holding the loaded stack cookie.
/// * `sp_alias` - Optional full register aliasing the entry stack pointer.
///
/// # Returns
///
/// `true` when `instr` writes `cookie` to a frame-addressed memory operand.
fn is_cookie_frame_store(
    instr: &Instruction,
    cookie: Register,
    sp_alias: Option<Register>,
) -> bool {
    instr.mnemonic() == Mnemonic::Mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && on_frame(instr, sp_alias)
        && instr.op1_register().full_register() == cookie
}

/// Tells whether `instr` adjusts `rsp` or `esp` downward with an immediate.
///
/// # Arguments
///
/// * `instr` - Candidate stack-pointer adjustment instruction.
///
/// # Returns
///
/// `true` for `sub` or `and` on `rsp`/`esp`, or `add` with a negative immediate.
fn is_sp_adjust(instr: &Instruction) -> bool {
    if instr.op0_kind() != OpKind::Register || !crate::analysis::is_imm(instr.op1_kind()) {
        return false;
    }
    match (instr.op0_register(), instr.mnemonic()) {
        (Register::RSP | Register::ESP, Mnemonic::Sub | Mnemonic::And) => true,
        (Register::RSP, Mnemonic::Add) => instr.immediate(1).cast_signed() < 0,
        (Register::ESP, Mnemonic::Add) => crate::num::lo32(instr.immediate(1)).cast_signed() < 0,
        _ => false,
    }
}

/// Tells whether `instr` loads a stack cookie from the thread block or image.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `instr` - Candidate load instruction.
/// * `after` - Following decoded instructions, checked for `/GS` or canary store+scrub.
/// * `sp_alias` - Optional full register aliasing the entry stack pointer.
///
/// # Returns
///
/// `true` for a thread-block canary load or a global canary load followed by
/// pointer mixing or a frame store plus register zero-scrub.
fn is_cookie_load(
    p: &Program,
    instr: &Instruction,
    after: &[(Instruction, Vec<Option<u8>>)],
    sp_alias: Option<Register>,
) -> bool {
    if instr.mnemonic() != Mnemonic::Mov
        || instr.op0_kind() != OpKind::Register
        || instr.op1_kind() != OpKind::Memory
    {
        return false;
    }
    let tls = instr.memory_base() == Register::None
        && instr.memory_index() == Register::None
        && matches!(
            (instr.memory_segment(), instr.memory_displacement64()),
            (Register::FS, CANARY_FS) | (Register::GS, CANARY_GS)
        );
    if tls {
        return true;
    }
    let global = instr.is_ip_rel_memory_operand()
        || (instr.memory_base() == Register::None
            && instr.memory_index() == Register::None
            && in_image(p, instr.memory_displacement64()));
    let dst = instr.op0_register().full_register();
    let look = after.iter().take(4);
    let mixed = look.clone().any(|(n, _)| is_cookie_xor(n, dst));
    let stored_and_scrubbed = look
        .clone()
        .any(|(n, _)| is_cookie_frame_store(n, dst, sp_alias))
        && look.clone().any(|(n, _)| is_zero_scrub(n, dst));
    global && (mixed || stored_and_scrubbed)
}

/// State of stack-cookie setup while walking a prologue.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
enum Cookie {
    /// No stack cookie has been loaded.
    #[default]
    None,
    /// Cookie loaded or mixed into this full register.
    InReg(Register),
    /// Cookie written into its frame slot from this full register.
    Stored(Register),
}

/// Registers tracked across a function's leading prologue idiom.
#[derive(Debug, Default)]
struct Prologue {
    /// Full register holding a copy of the entry stack pointer (`rax` or `r11`).
    sp_alias: Option<Register>,
    /// Stack-cookie setup state.
    cookie: Cookie,
}

impl Prologue {
    /// Tells whether `instr` saves a prologue register into the stack frame.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image, for its calling convention.
    /// * `instr` - The decoded instruction.
    ///
    /// # Returns
    ///
    /// `true` when `instr` homes an argument, saves a callee-saved register, or
    /// stores the loaded stack cookie into a frame slot.
    fn is_frame_store(&mut self, p: &Program, instr: &Instruction) -> bool {
        let store = matches!(
            instr.mnemonic(),
            Mnemonic::Mov
                | Mnemonic::Movaps
                | Mnemonic::Movups
                | Mnemonic::Movapd
                | Mnemonic::Movupd
                | Mnemonic::Movdqa
                | Mnemonic::Movdqu
                | Mnemonic::Movsd
                | Mnemonic::Movss
                | Mnemonic::Movq
                | Mnemonic::Movd
                | Mnemonic::Vmovaps
                | Mnemonic::Vmovups
                | Mnemonic::Vmovapd
                | Mnemonic::Vmovupd
                | Mnemonic::Vmovdqa
                | Mnemonic::Vmovdqu
                | Mnemonic::Vmovsd
                | Mnemonic::Vmovss
                | Mnemonic::Vmovq
                | Mnemonic::Vmovd
        );
        if !store
            || instr.op0_kind() != OpKind::Memory
            || instr.op1_kind() != OpKind::Register
            || !on_frame(instr, self.sp_alias)
        {
            return false;
        }
        let src = instr.op1_register();
        if self.cookie == Cookie::InReg(src.full_register()) {
            self.cookie = Cookie::Stored(src.full_register());
            return true;
        }
        is_callee_saved(src) || xmm_slot(src).is_some_and(|s| s >= 6) || is_arg_reg(p, src)
    }

    /// Advances prologue recognition across one decoded instruction.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image.
    /// * `instr` - The current instruction.
    /// * `after` - Following decoded instructions, for stack-cookie lookahead.
    ///
    /// # Returns
    ///
    /// `true` when `instr` belongs to the leading prologue or padding idiom.
    fn step(
        &mut self,
        p: &Program,
        instr: &Instruction,
        after: &[(Instruction, Vec<Option<u8>>)],
    ) -> bool {
        if matches!(instr.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) || is_padding(instr) {
            return true;
        }
        if instr.mnemonic() == Mnemonic::Push
            && instr.op0_kind() == OpKind::Register
            && is_callee_saved(instr.op0_register())
        {
            return true;
        }
        if instr.mnemonic() == Mnemonic::Mov
            && instr.op0_kind() == OpKind::Register
            && instr.op1_kind() == OpKind::Register
            && matches!(instr.op1_register(), Register::RSP | Register::ESP)
        {
            if matches!(instr.op0_register(), Register::RBP | Register::EBP) {
                return true;
            }
            if matches!(instr.op0_register(), Register::RAX | Register::R11) {
                self.sp_alias = Some(instr.op0_register().full_register());
                return true;
            }
        }
        if instr.mnemonic() == Mnemonic::Lea
            && instr.op0_kind() == OpKind::Register
            && matches!(instr.op0_register(), Register::RBP | Register::EBP)
            && matches!(instr.memory_base(), Register::RSP | Register::ESP)
            && instr.memory_index() == Register::None
        {
            return true;
        }
        if is_sp_adjust(instr) {
            return true;
        }
        if is_cookie_load(p, instr, after, self.sp_alias) {
            self.cookie = Cookie::InReg(instr.op0_register().full_register());
            return true;
        }
        if let Cookie::InReg(c) = self.cookie {
            let deref = instr.mnemonic() == Mnemonic::Mov
                && instr.op0_kind() == OpKind::Register
                && instr.op0_register().full_register() == c
                && instr.op1_kind() == OpKind::Memory
                && !matches!(instr.memory_segment(), Register::FS | Register::GS)
                && instr.memory_base().full_register() == c
                && instr.memory_index() == Register::None
                && instr.memory_displacement64() == 0;
            if is_cookie_xor(instr, c) || deref {
                return true;
            }
        }
        if let Cookie::Stored(c) = self.cookie
            && is_zero_scrub(instr, c)
        {
            self.cookie = Cookie::None;
            return true;
        }
        self.is_frame_store(p, instr)
    }
}

/// Returns the end of the contiguous code run starting at `f.entry`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The discovered function.
/// * `bitness` - Decoder bitness (`32` or `64`).
///
/// # Returns
///
/// Exclusive virtual address ending `f`'s contiguous entry blocks, capped once
/// enough bytes are covered for [`yara_signature`].
fn contiguous_end(p: &Program, f: &Function, bitness: u32) -> u64 {
    /// Largest alignment gap bridged between adjacent blocks of one function.
    const GAP_MAX: u64 = 16;
    let enough = crate::num::from_usize(SIGNATURE_MAX.saturating_add(PROLOGUE_ROOM));
    let mut spans: Vec<(u64, u64)> = f
        .blocks
        .iter()
        .filter(|b| b.end > f.entry)
        .map(|b| (b.start, b.end))
        .collect();
    spans.sort_unstable();
    let mut end = f.entry;
    for (start, stop) in spans {
        if end.saturating_sub(f.entry) >= enough {
            break;
        }
        if start > end {
            let gap = start.saturating_sub(end);
            let gap_len = crate::num::saturating_usize(gap);
            let Some(pad) = (gap <= GAP_MAX)
                .then(|| p.read_va_upto(end, gap_len))
                .flatten()
                .filter(|s| s.len() == gap_len)
            else {
                break;
            };
            let mut dec = Decoder::with_ip(bitness, pad, end, DecoderOptions::NONE);
            let mut all_pad = true;
            while dec.can_decode() {
                let instr = dec.decode();
                if instr.is_invalid() || !is_padding(&instr) {
                    all_pad = false;
                    break;
                }
            }
            if !all_pad {
                break;
            }
        }
        end = end.max(stop);
    }
    if end > f.entry { end } else { f.end }
}

/// Builds a YARA hex pattern for `f` from its own post-prologue bytes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The discovered function to sign.
///
/// # Returns
///
/// Spaced hex pattern holding at least [`OWN_MIN`] non-idiom fixed bytes and
/// matching `p` once.
///
/// # Errors
///
/// Reason `f` yields no YARA code string: unsupported architecture, unmapped or
/// undecodable bytes, fewer than [`OWN_MIN`] non-idiom fixed bytes, or a pattern
/// that still matches multiple places.
fn yara_signature(p: &Program, f: &Function) -> Result<String, String> {
    let bitness = x86_bitness(p)?;
    let end = contiguous_end(p, f, bitness);
    let cap = SIGNATURE_MAX.saturating_add(PROLOGUE_ROOM);
    let room = crate::num::saturating_usize(end.saturating_sub(f.entry)).min(cap);
    let bytes = p
        .read_va_upto(f.entry, room)
        .filter(|b| !b.is_empty())
        .ok_or_else(|| format!("nothing is mapped at {:#x}", f.entry))?;
    let decoded = decode_masked(p, bitness, f.entry, bytes);
    if decoded.is_empty() {
        return Err(format!("no instruction decodes at {:#x}", f.entry));
    }
    let mut prologue = Prologue::default();
    let mut in_prologue = true;
    let mut pattern = Vec::new();
    let mut own_fixed = 0usize;
    let mut last_matches = None;
    for (idx, (instr, masked)) in decoded.iter().enumerate() {
        let after = decoded.get(idx.saturating_add(1)..).unwrap_or_default();
        let idiom = if in_prologue && prologue.step(p, instr, after) {
            true
        } else {
            in_prologue = false;
            is_padding(instr)
        };
        if pattern.is_empty() && idiom {
            continue;
        }
        if pattern.len().saturating_add(masked.len()) > SIGNATURE_MAX {
            break;
        }
        pattern.extend_from_slice(masked);
        if !idiom {
            own_fixed = own_fixed.saturating_add(masked.iter().flatten().count());
        }
        if own_fixed < OWN_MIN {
            continue;
        }
        let trimmed = trim_wildcards(&pattern);
        if trimmed.is_empty() {
            continue;
        }
        let matches = search::find_bytes(p, trimmed, 0).total;
        last_matches = Some(matches);
        if matches == 1 {
            let sig = Signature {
                pattern: trimmed.to_vec(),
                matches: 1,
            };
            return Ok(sig.spaced());
        }
        if matches == 0 {
            break;
        }
    }
    match last_matches {
        Some(n) => Err(format!("its signature matches {n} places, left out")),
        None if own_fixed == 0 => Err(format!(
            "only prologue and padding bytes (needs {OWN_MIN} fixed body bytes), left out"
        )),
        None => Err(format!(
            "only {own_fixed} fixed bytes past its prologue (needs {OWN_MIN}), left out"
        )),
    }
}

/// A string's text as a YARA text string: quoted, with `\\`, `"` and
/// bytes outside printable ASCII escaped.
///
/// # Arguments
///
/// * `text` - The string as stored.
fn yara_quoted(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            ' '..='~' => out.push(c),
            c => {
                let mut buf = [0u8; 4];
                for b in c.encode_utf8(&mut buf).bytes() {
                    let _ = write!(out, "\\x{b:02x}");
                }
            }
        }
    }
    out.push('"');
    out
}

/// Advances past a `printf`-family directive starting immediately after `%`.
///
/// # Arguments
///
/// * `chars` - The string's characters.
/// * `at` - Index immediately following `%`.
///
/// # Returns
///
/// Index past the conversion specifier, or `None` when `%` does not open a
/// recognized directive.
fn skip_format_spec(chars: &[char], mut at: usize) -> Option<usize> {
    if chars.get(at) == Some(&'%') {
        return Some(at + 1);
    }
    let pos_start = at;
    while chars.get(at).is_some_and(char::is_ascii_digit) {
        at += 1;
    }
    if at > pos_start && chars.get(at) == Some(&'$') {
        at += 1;
    } else {
        at = pos_start;
    }
    while chars
        .get(at)
        .is_some_and(|c| matches!(c, '-' | '+' | ' ' | '#' | '0' | '\''))
    {
        at += 1;
    }
    if chars.get(at) == Some(&'*') {
        at += 1;
    } else {
        while chars.get(at).is_some_and(char::is_ascii_digit) {
            at += 1;
        }
    }
    if chars.get(at) == Some(&'.') {
        at += 1;
        if chars.get(at) == Some(&'*') {
            at += 1;
        } else {
            while chars.get(at).is_some_and(char::is_ascii_digit) {
                at += 1;
            }
        }
    }
    let rest = chars.get(at..).unwrap_or_default();
    if rest.starts_with(&['I', '6', '4']) || rest.starts_with(&['I', '3', '2']) {
        at += 3;
    } else if rest.starts_with(&['l', 'l']) || rest.starts_with(&['h', 'h']) {
        at += 2;
    } else if rest
        .first()
        .is_some_and(|c| matches!(c, 'h' | 'l' | 'L' | 'z' | 'j' | 't' | 'I' | 'w' | 'q'))
    {
        at += 1;
    }
    chars
        .get(at)
        .is_some_and(|c| {
            matches!(
                c,
                'd' | 'i'
                    | 'u'
                    | 'o'
                    | 'x'
                    | 'X'
                    | 'f'
                    | 'F'
                    | 'e'
                    | 'E'
                    | 'g'
                    | 'G'
                    | 'a'
                    | 'A'
                    | 'c'
                    | 'C'
                    | 's'
                    | 'S'
                    | 'p'
                    | 'n'
                    | 'm'
                    | 'Z'
            )
        })
        .then_some(at + 1)
}

/// Tells whether a referenced string is specific enough for a YARA rule.
///
/// Format directives, digits and punctuation alone never identify a program,
/// and short words such as `"Error"` match unrelated binaries.
///
/// # Arguments
///
/// * `text` - The unquoted string text.
///
/// # Returns
///
/// `true` when `text` holds at least [`STRING_MIN`] letters outside `printf`
/// directives.
fn identifying_text(text: &str) -> bool {
    let chars: Vec<char> = text.chars().collect();
    let mut letters = 0;
    let mut i = 0;
    while let Some(&c) = chars.get(i) {
        if c == '%'
            && let Some(next) = skip_format_spec(&chars, i + 1)
        {
            i = next;
            continue;
        }
        if c.is_alphabetic() {
            letters += 1;
        }
        i += 1;
    }
    letters >= STRING_MIN
}

/// The string a function references at an address, as YARA writes it,
/// read from the image's bytes rather than a rendered literal.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results.
/// * `target` - The address the function refers to.
///
/// # Returns
///
/// The quoted text and whether it is UTF-16, or `None` when no identifying
/// string ([`identifying_text`]) is there.
fn yara_string(p: &Program, a: &Analysis, target: u64) -> Option<(String, bool)> {
    /// Longest string a rule matches whole; a longer one is matched by
    /// this much of its start.
    const CAP: usize = 120;
    let (start, lit) = referenced_literal(p, a, target, CAP)?;
    let wide = lit.starts_with('L');
    let (len, text) = if wide {
        crate::strings::wstr_text_at(p, start, 4, CAP)?
    } else {
        crate::strings::cstr_text_at(p, start, 4, CAP)?
    };
    let shown = if len > CAP {
        text.strip_suffix("...").unwrap_or(&text)
    } else {
        &text
    };
    identifying_text(shown).then(|| (yara_quoted(shown), wide))
}

/// The YARA condition a file of this format meets by its first bytes.
///
/// That is a PE's `MZ`, an ELF's magic, a thin Mach-O's 32- or 64-bit magic
/// or a universal one's `CAFEBABE` (read big-endian, as the header stores
/// it).
///
/// # Arguments
///
/// * `format` - The file's format.
fn yara_magic(format: BinaryFormat) -> &'static str {
    match format {
        BinaryFormat::Pe => "uint16(0) == 0x5A4D",
        BinaryFormat::Elf => "uint32(0) == 0x464C457F",
        BinaryFormat::MachO => {
            "(uint32(0) == 0xFEEDFACF or uint32(0) == 0xFEEDFACE or uint32be(0) == 0xCAFEBABE)"
        }
        _ => "true",
    }
}

/// A YARA identifier from a file name: `borer_` and its letters, digits
/// and underscores, so no name is a keyword (`rule`, `global`) or starts
/// with a digit.
///
/// # Arguments
///
/// * `stem` - The file's name without its extension.
fn rule_name(stem: &str) -> String {
    let body: String = stem
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    format!("borer_{body}")
}

/// Writes a YARA rule that finds the given functions again from their own body
/// bytes and identifying strings.
///
/// Each code string starts past the prologue idiom and holds at least
/// [`OWN_MIN`] non-idiom fixed bytes that match the image once; functions that
/// fall short are noted in `//` comments above the rule. The condition asks for
/// every code string, or at least two of the identifying strings (half when
/// five or more, all when one).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Discovery results.
/// * `o` - User names.
/// * `entries` - The functions the rule describes.
///
/// # Returns
///
/// Complete YARA rule text preceded by any `//` omission notes.
///
/// # Errors
///
/// When no entry is a function, or none yields a code signature or an
/// identifying string.
pub fn yara_rule(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entries: &[u64],
) -> Result<String, String> {
    /// Strings the rule carries at most.
    const STRINGS_MAX: usize = 12;
    let mut sigs: Vec<(String, String)> = Vec::new();
    let mut texts: Vec<(String, bool)> = Vec::new();
    let mut notes: Vec<String> = Vec::new();
    for &entry in entries {
        let f = a
            .function_at(entry)
            .ok_or_else(|| format!("no function at {entry:#x}"))?;
        let name = crate::text::one_line(&name_of(a, o, f.entry));
        match yara_signature(p, f) {
            Ok(pattern) => sigs.push((name, pattern)),
            Err(why) => notes.push(format!("{name}: {why}")),
        }
        for (target, _) in a.refs_from(f.entry) {
            if texts.len() >= STRINGS_MAX {
                break;
            }
            if let Some(t) = yara_string(p, a, target)
                && !texts.contains(&t)
            {
                texts.push(t);
            }
        }
    }
    if sigs.is_empty() && texts.is_empty() {
        return Err(format!(
            "nothing to match on: {}",
            if notes.is_empty() {
                "the functions reference no strings".to_owned()
            } else {
                notes.join("; ")
            }
        ));
    }
    let stem = p
        .path
        .file_stem()
        .map_or_else(|| "sample".to_owned(), |s| s.to_string_lossy().into_owned());
    let magic = yara_magic(p.format);
    let mut out = String::new();
    for n in &notes {
        let _ = writeln!(out, "// {n}");
    }
    let _ = writeln!(out, "rule {} {{", rule_name(&stem));
    let _ = writeln!(out, "    meta:");
    let described = format!(
        "code and strings of {}",
        entries
            .iter()
            .filter_map(|&e| a
                .function_at(e)
                .map(|f| crate::text::one_line(&name_of(a, o, f.entry))))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let _ = writeln!(out, "        description = {}", yara_quoted(&described));
    let _ = writeln!(out, "        generator = \"borer\"");
    let _ = writeln!(out, "    strings:");
    for (i, (name, pattern)) in sigs.iter().enumerate() {
        let _ = writeln!(out, "        $c{i} = {{ {pattern} }} // {name}");
    }
    for (i, (text, wide)) in texts.iter().enumerate() {
        let _ = writeln!(
            out,
            "        $s{i} = {text}{}",
            if *wide { " wide" } else { " ascii" }
        );
    }
    let code = (!sigs.is_empty()).then_some("all of ($c*)");
    let strs = match texts.len() {
        0 => None,
        1 => Some("all of ($s*)".to_owned()),
        n => Some(format!("{} of ($s*)", n.div_ceil(2).max(2))),
    };
    let either = match (code, strs) {
        (Some(c), Some(s)) => format!("({c} or {s})"),
        (Some(c), None) => c.to_owned(),
        (None, Some(s)) => s,
        (None, None) => "false".to_owned(),
    };
    let _ = writeln!(out, "    condition:");
    let _ = writeln!(out, "        {magic} and {either}");
    out.push_str("}\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{rule_name, signature, yara_magic, yara_quoted};
    use crate::program::BinaryFormat;

    /// Each format's rule opens on the bytes its files start with, a
    /// universal Mach-O's included.
    ///
    /// # Panics
    ///
    /// When a format's magic is missing.
    #[test]
    fn every_format_is_matched_by_its_magic() {
        assert_eq!(yara_magic(BinaryFormat::Pe), "uint16(0) == 0x5A4D");
        assert!(yara_magic(BinaryFormat::MachO).contains("uint32be(0) == 0xCAFEBABE"));
        assert!(yara_magic(BinaryFormat::MachO).contains("0xFEEDFACF"));
        assert_eq!(yara_magic(BinaryFormat::Raw), "true");
    }
    use crate::program::{Arch, Program, Section};

    /// An absolute address in an immediate operand that is not the first
    /// operand, `mov eax, <address>`, is wildcarded too.
    ///
    /// # Panics
    ///
    /// When the address bytes stay fixed.
    #[test]
    fn an_address_in_a_later_operand_is_wildcarded() {
        let mut code = vec![0xcc_u8; 0x1000];
        code[..10].copy_from_slice(&[0x55, 0x89, 0xe5, 0x53, 0x56, 0x57, 0xb8, 0x00, 0x18, 0x40]);
        code[10..12].copy_from_slice(&[0x00, 0xc3]);
        let text = Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true);
        let p = Program::raw(code, Arch::X86, 0x40_0000, Some(0x40_1000), vec![text]);
        let sig = signature(&p, 0x40_1000, None).expect("a signature");
        assert!(
            sig.spaced().starts_with("55 89 E5 53 56 57"),
            "{}",
            sig.spaced()
        );
        assert!(!sig.spaced().contains("00 18 40 00"), "{}", sig.spaced());
    }

    /// A function whose whole body is duplicated gets no signature borrowed
    /// from the bytes after it: it reports the places it matches.
    ///
    /// # Panics
    ///
    /// When the signature is called unique.
    #[test]
    fn a_duplicated_body_borrows_no_bytes_past_its_end() {
        let body = [0x55, 0x48, 0x89, 0xe5, 0x31, 0xc0, 0x5d, 0xc3];
        let mut code = vec![0xcc_u8; 0x1000];
        code[..8].copy_from_slice(&body);
        code[8] = 0x90;
        code[0x100..0x108].copy_from_slice(&body);
        code[0x108] = 0x91;
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let sig = signature(&p, 0x1000, Some(0x1008)).expect("a signature");
        assert_eq!(sig.matches, 2, "{}", sig.spaced());
        assert_eq!(sig.pattern.len(), 8);
    }

    /// A signature grows past a prefix found twice, wildcarding the
    /// RIP-relative displacement it crosses, and stops once it is unique.
    ///
    /// # Panics
    ///
    /// When the pattern or its match count reads otherwise.
    #[test]
    fn a_signature_wildcards_what_moves_and_stops_when_unique() {
        let prefix = [0x55, 0x48, 0x89, 0xe5, 0x48, 0x8b, 0x05];
        let mut code = vec![0xcc_u8; 0x1000];
        code[..7].copy_from_slice(&prefix);
        code[7..11].copy_from_slice(&[0x10, 0x00, 0x00, 0x00]);
        code[11..16].copy_from_slice(&[0xe8, 0x00, 0x01, 0x00, 0x00]);
        code[16] = 0xc3;
        code[0x800..0x807].copy_from_slice(&prefix);
        code[0x807..0x80b].copy_from_slice(&[0x20, 0x00, 0x00, 0x00]);
        code[0x80b] = 0xc3;
        let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let sig = signature(&p, 0x1000, None).expect("a signature");
        assert_eq!(sig.spaced(), "55 48 89 E5 48 8B 05 ?? ?? ?? ?? E8");
        assert_eq!(sig.matches, 1);
    }

    /// Backslashes, quotes and bytes past ASCII are escaped as YARA reads
    /// them; a Windows path keeps its backslashes as backslashes.
    ///
    /// # Panics
    ///
    /// When the quoting reads otherwise.
    #[test]
    fn text_is_quoted_as_yara_reads_it() {
        assert_eq!(
            yara_quoted("shell\\notepad\\np.cpp"),
            "\"shell\\\\notepad\\\\np.cpp\""
        );
        assert_eq!(
            yara_quoted("say \"hi\"\u{e9}"),
            "\"say \\\"hi\\\"\\xc3\\xa9\""
        );
    }

    /// Rule names are identifiers.
    ///
    /// # Panics
    ///
    /// When one is not.
    #[test]
    fn rule_names_are_identifiers() {
        assert_eq!(rule_name("notepad"), "borer_notepad");
        assert_eq!(rule_name("rule"), "borer_rule");
        assert_eq!(rule_name("7z-setup.x64"), "borer_7z_setup_x64");
    }

    /// Builds a minimal x86-64 ELF image with code at `0x40_1000` and optional
    /// read-only data at `0x40_2000`.
    ///
    /// # Arguments
    ///
    /// * `code` - Machine bytes mapped executable at `0x40_1000`.
    /// * `rodata` - Read-only data bytes mapped at `0x40_2000`, if non-empty.
    ///
    /// # Returns
    ///
    /// Parsed [`Program`] with `BinaryFormat::Elf` and entry `0x40_1000`.
    ///
    /// # Panics
    ///
    /// When `code` exceeds `0x100` bytes while `rodata` is present, or ELF
    /// parsing fails.
    fn elf_x64(code: &[u8], rodata: &[u8]) -> Program {
        let phnum: u16 = if rodata.is_empty() { 1 } else { 2 };
        let end = if rodata.is_empty() {
            0x100_usize + code.len()
        } else {
            assert!(code.len() <= 0x100, "code overlaps rodata");
            0x200_usize + rodata.len()
        };
        let mut bytes = vec![0_u8; end];
        bytes[..8].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0]);
        bytes[0x10..0x12].copy_from_slice(&2_u16.to_le_bytes());
        bytes[0x12..0x14].copy_from_slice(&62_u16.to_le_bytes());
        bytes[0x14..0x18].copy_from_slice(&1_u32.to_le_bytes());
        bytes[0x18..0x20].copy_from_slice(&0x40_1000_u64.to_le_bytes());
        bytes[0x20..0x28].copy_from_slice(&0x40_u64.to_le_bytes());
        bytes[0x34..0x36].copy_from_slice(&64_u16.to_le_bytes());
        bytes[0x36..0x38].copy_from_slice(&56_u16.to_le_bytes());
        bytes[0x38..0x3a].copy_from_slice(&phnum.to_le_bytes());
        let put_phdr = |buf: &mut [u8], at: usize, flags: u32, off: u64, va: u64, len: usize| {
            let sz = u64::try_from(len).expect("fits");
            buf[at..at + 4].copy_from_slice(&1_u32.to_le_bytes());
            buf[at + 4..at + 8].copy_from_slice(&flags.to_le_bytes());
            buf[at + 8..at + 16].copy_from_slice(&off.to_le_bytes());
            buf[at + 16..at + 24].copy_from_slice(&va.to_le_bytes());
            buf[at + 24..at + 32].copy_from_slice(&va.to_le_bytes());
            buf[at + 32..at + 40].copy_from_slice(&sz.to_le_bytes());
            buf[at + 40..at + 48].copy_from_slice(&sz.to_le_bytes());
            buf[at + 48..at + 56].copy_from_slice(&0x1000_u64.to_le_bytes());
        };
        put_phdr(&mut bytes, 0x40, 5, 0x100, 0x40_1000, code.len());
        bytes[0x100..0x100 + code.len()].copy_from_slice(code);
        if !rodata.is_empty() {
            put_phdr(&mut bytes, 0x78, 4, 0x200, 0x40_2000, rodata.len());
            bytes[0x200..0x200 + rodata.len()].copy_from_slice(rodata);
        }
        Program::from_bytes(std::path::PathBuf::from("sample.elf"), bytes).expect("valid ELF64")
    }

    /// Appends a `lea r64, [rip + disp32]` instruction targeting `target_va`.
    ///
    /// # Arguments
    ///
    /// * `code` - Code buffer starting at virtual address `0x40_1000`.
    /// * `modrm` - ModR/M byte (`0x3d` for `rdi`, `0x35` for `rsi`).
    /// * `target_va` - Target virtual address above the instruction's end.
    ///
    /// # Panics
    ///
    /// When the displacement does not fit in a forward `u32`.
    fn push_lea_rip(code: &mut Vec<u8>, modrm: u8, target_va: u64) {
        let next_ip = 0x40_1000_u64 + u64::try_from(code.len() + 7).expect("fits");
        let disp = u32::try_from(target_va - next_ip).expect("forward target");
        code.extend_from_slice(&[0x48, 0x8d, modrm]); // ASM: lea r64, [rip + disp32]
        code.extend_from_slice(&disp.to_le_bytes());
    }

    /// Parses every `$cN = { ... }` hex pattern from a rendered YARA rule.
    ///
    /// # Arguments
    ///
    /// * `rule` - Rendered YARA rule text.
    ///
    /// # Returns
    ///
    /// Decoded wildcard patterns in `$cN` order.
    ///
    /// # Panics
    ///
    /// When a `$c` line in `rule` has malformed hex bytes.
    fn rule_code_patterns(rule: &str) -> Vec<Vec<Option<u8>>> {
        rule.lines()
            .filter_map(|line| {
                let trimmed = line.trim_start();
                if !trimmed.starts_with("$c") {
                    return None;
                }
                let (_, rest) = trimmed.split_once('{')?;
                let (hex, _) = rest.split_once('}')?;
                Some(crate::search::parse_pattern(hex).expect("valid YARA hex pattern"))
            })
            .collect()
    }

    /// Two x86-64 ELF images sharing a stock `-O0` prologue and differing in
    /// their bodies share no YARA code string.
    ///
    /// # Panics
    ///
    /// When a code string from `A`'s rule matches `B`, or a body long enough
    /// past the shared prologue fails to match `C` alone.
    #[test]
    fn shared_prologue_functions_produce_no_cross_matching_yara_code() {
        use super::{Analysis, Overlay, yara_rule};

        let a_code: &[u8] = &[
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xec, 0x40, // ASM: sub rsp, 0x40
            0x89, 0x7d, 0xfc, // ASM: mov [rbp - 4], edi
            0x8b, 0x45, 0xfc, // ASM: mov eax, [rbp - 4]
            0x0f, 0xaf, 0xc0, // ASM: imul eax, eax
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ];
        let b_code: &[u8] = &[
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xec, 0x40, // ASM: sub rsp, 0x40
            0x89, 0x7d, 0xfc, // ASM: mov [rbp - 4], edi
            0x8b, 0x45, 0xfc, // ASM: mov eax, [rbp - 4]
            0x83, 0xc0, 0x07, // ASM: add eax, 7
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ];
        let a_prog = elf_x64(a_code, &[]);
        let b_prog = elf_x64(b_code, &[]);
        let a_ana = Analysis::compute(&a_prog);
        let sig = signature(&a_prog, 0x40_1000, Some(0x40_1013)).expect("in-image signature");
        assert_eq!(sig.spaced(), "55 48 89 E5 48 83 EC 40");
        match yara_rule(&a_prog, &a_ana, &Overlay::default(), &[0x40_1000]) {
            Ok(rule) => {
                let patterns = rule_code_patterns(&rule);
                assert!(!patterns.is_empty(), "{rule}");
                for pat in &patterns {
                    assert_eq!(
                        crate::search::find_bytes(&b_prog, pat, 0).total,
                        0,
                        "{rule}"
                    );
                }
            }
            Err(why) => assert!(why.contains("prologue"), "{why}"),
        }

        let c_code: &[u8] = &[
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xec, 0x40, // ASM: sub rsp, 0x40
            0x89, 0x7d, 0xfc, // ASM: mov [rbp - 4], edi
            0x8b, 0x45, 0xfc, // ASM: mov eax, [rbp - 4]
            0x69, 0xc0, 0x67, 0x45, 0x23, 0x01, // ASM: imul eax, eax, 0x01234567
            0x83, 0xc0, 0x42, // ASM: add eax, 0x42
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ];
        let c_prog = elf_x64(c_code, &[]);
        let c_ana = Analysis::compute(&c_prog);
        let c_rule = yara_rule(&c_prog, &c_ana, &Overlay::default(), &[0x40_1000])
            .expect("rule with >= 12 own fixed bytes");
        let c_patterns = rule_code_patterns(&c_rule);
        assert_eq!(c_patterns.len(), 1, "{c_rule}");
        assert_eq!(
            crate::search::find_bytes(&c_prog, &c_patterns[0], 0).total,
            1
        );
        assert_eq!(
            crate::search::find_bytes(&b_prog, &c_patterns[0], 0).total,
            0,
            "{c_rule}"
        );
    }

    /// A function whose only unique prefix is its prologue emits no `$c0`
    /// string and explains why in a rule comment line.
    ///
    /// # Panics
    ///
    /// When `$c0` is emitted or the omission comment is missing.
    #[test]
    fn a_prologue_only_function_omits_its_code_string_and_comments_why() {
        use super::{Analysis, Overlay, yara_rule};

        let mut code = vec![
            0xf3, 0x0f, 0x1e, 0xfa, // ASM: endbr64
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xec, 0x40, // ASM: sub rsp, 0x40
        ];
        push_lea_rip(&mut code, 0x3d, 0x40_2000);
        code.extend_from_slice(&[
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ]);
        code.resize(0x40, 0xcc); // ASM: int3 padding
        code.extend_from_slice(&[
            0xf3, 0x0f, 0x1e, 0xfa, // ASM: endbr64
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ]);
        let prog = elf_x64(&code, b"borer_unique_marker\0");
        let ana = Analysis::compute(&prog);
        let rule =
            yara_rule(&prog, &ana, &Overlay::default(), &[0x40_1000]).expect("rule on string");
        assert!(!rule.contains("$c0"), "{rule}");
        assert!(
            rule.lines()
                .any(|l| l.starts_with("// ") && l.contains("prologue") && l.contains("left out")),
            "{rule}"
        );
        assert!(
            rule.contains("$s0 = \"borer_unique_marker\" ascii"),
            "{rule}"
        );
        assert!(rule.contains("all of ($s*)"), "{rule}");
    }

    /// Short words and `printf` directive templates such as `"%s: "` and
    /// `"Error"` never build a strings arm.
    ///
    /// # Panics
    ///
    /// When `"%s: "` or `"Error"` appears as `$sN`, or two identifying strings
    /// fail to require `2 of ($s*)`.
    #[test]
    fn non_identifying_strings_give_no_strings_arm() {
        use super::{Analysis, Overlay, yara_rule};

        let mut code = vec![
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        ];
        push_lea_rip(&mut code, 0x3d, 0x40_2000);
        push_lea_rip(&mut code, 0x35, 0x40_2005);
        code.extend_from_slice(&[
            0x69, 0xc7, 0x67, 0x45, 0x23, 0x01, // ASM: imul eax, edi, 0x01234567
            0x83, 0xc0, 0x42, // ASM: add eax, 0x42
            0x31, 0xd2, // ASM: xor edx, edx
            0x5d, // ASM: pop rbp
            0xc3, // ASM: ret
        ]);
        let prog = elf_x64(&code, b"%s: \0Error\0");
        let ana = Analysis::compute(&prog);
        let rule = yara_rule(&prog, &ana, &Overlay::default(), &[0x40_1000]).expect("rule on code");
        assert!(rule.contains("$c0"), "{rule}");
        assert!(!rule.contains("$s0"), "{rule}");
        assert!(!rule.contains("($s*)"), "{rule}");

        let mut two_code = vec![
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        ];
        push_lea_rip(&mut two_code, 0x3d, 0x40_2000);
        push_lea_rip(&mut two_code, 0x35, 0x40_2013);
        two_code.extend_from_slice(&[
            0x5d, // ASM: pop rbp
            0xc3, // ASM: ret
        ]);
        let two_prog = elf_x64(&two_code, b"borer_alpha_marker\0borer_beta_marker\0");
        let two_ana = Analysis::compute(&two_prog);
        let two_rule = yara_rule(&two_prog, &two_ana, &Overlay::default(), &[0x40_1000])
            .expect("rule on two identifying strings");
        assert!(two_rule.contains("2 of ($s*)"), "{two_rule}");
    }

    /// Out-of-order block discovery still spans contiguous fallthrough blocks.
    ///
    /// # Panics
    ///
    /// When reversing block discovery order drops `$c0`.
    #[test]
    fn contiguous_blocks_sign_regardless_of_discovery_order() {
        use super::{Analysis, Overlay, yara_rule};

        let code: &[u8] = &[
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x85, 0xff, // ASM: test edi, edi
            0x74, 0x09, // ASM: jz +9
            0x69, 0xc7, 0x67, 0x45, 0x23, 0x01, // ASM: imul eax, edi, 0x01234567
            0x83, 0xc0, 0x42, // ASM: add eax, 0x42
            0x31, 0xd2, // ASM: xor edx, edx
            0x81, 0xc2, 0x78, 0x56, 0x34, 0x12, // ASM: add edx, 0x12345678
            0x5d, // ASM: pop rbp
            0xc3, // ASM: ret
        ];
        let prog = elf_x64(code, &[]);
        let mut ana = Analysis::compute(&prog);
        ana.functions[0].blocks.reverse();
        let rule = yara_rule(&prog, &ana, &Overlay::default(), &[0x40_1000])
            .expect("rule across contiguous blocks");
        assert!(rule.contains("$c0"), "{rule}");
    }

    /// Negative `add rsp, -imm` frame allocation and indirect global canary
    /// loads are stripped as prologue idioms rather than signed as body code.
    ///
    /// # Panics
    ///
    /// When `add rsp, -0x80` leaks into `$c0` or a global canary setup counts
    /// toward [`super::OWN_MIN`].
    #[test]
    fn negative_sp_add_and_global_canary_prologues_emit_no_yara_code() {
        use super::{Analysis, Overlay, yara_rule};

        let sp_code: &[u8] = &[
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xc4, 0x80, // ASM: add rsp, -0x80
            0x69, 0xc7, 0x67, 0x45, 0x23, 0x01, // ASM: imul eax, edi, 0x01234567
            0x83, 0xc0, 0x42, // ASM: add eax, 0x42
            0x31, 0xd2, // ASM: xor edx, edx
            0x5d, // ASM: pop rbp
            0xc3, // ASM: ret
        ];
        let sp_prog = elf_x64(sp_code, &[]);
        let sp_ana = Analysis::compute(&sp_prog);
        let sp_rule = yara_rule(&sp_prog, &sp_ana, &Overlay::default(), &[0x40_1000])
            .expect("rule past negative add rsp");
        assert!(!sp_rule.contains("48 83 C4 80"), "{sp_rule}");
        assert!(sp_rule.contains("$c0 = { 69 C7 67 45 23 01"), "{sp_rule}");

        let mut canary_code = vec![
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
            0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
        ];
        let next_ip = 0x40_1000_u64 + u64::try_from(canary_code.len() + 7).expect("fits");
        let guard_disp = u32::try_from(0x40_2018_u64 - next_ip).expect("forward guard");
        canary_code.extend_from_slice(&[0x48, 0x8b, 0x05]); // ASM: mov rax, [rip + disp32]
        canary_code.extend_from_slice(&guard_disp.to_le_bytes());
        canary_code.extend_from_slice(&[
            0x48, 0x8b, 0x00, // ASM: mov rax, [rax]
            0x48, 0x89, 0x45, 0xf8, // ASM: mov [rbp - 8], rax
            0x31, 0xc0, // ASM: xor eax, eax
        ]);
        push_lea_rip(&mut canary_code, 0x3d, 0x40_2000);
        canary_code.extend_from_slice(&[
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ]);
        let mut rodata = b"borer_canary_marker\0".to_vec();
        rodata.resize(0x20, 0);
        let canary_prog = elf_x64(&canary_code, &rodata);
        let canary_ana = Analysis::compute(&canary_prog);
        let canary_rule = yara_rule(&canary_prog, &canary_ana, &Overlay::default(), &[0x40_1000])
            .expect("rule on string when canary prologue is stripped");
        assert!(!canary_rule.contains("$c0"), "{canary_rule}");
    }
}
