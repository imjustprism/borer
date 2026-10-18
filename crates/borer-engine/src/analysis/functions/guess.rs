//! The shape tests a guessed seed must pass before its walk is kept:
//! padding, prologues, odd instructions and thunk slots.

use super::frame::moves_rsp_by_imm;
use super::helpers::frame_helper_name;
use super::sets::AddrSet;
use super::{Cursors, decode_at, near_target, seh_scope_roots, string_at};
use crate::isa::x86::{Code, FlowControl, Instruction, Mnemonic, OpKind, Register};
use crate::program::Program;

/// Tells whether the code at `va` is padding a call never returns into.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `va` - The address after a call.
///
/// # Returns
///
/// `true` when `va` does not decode, or decodes as `int3` or `ud2`.
pub(super) fn is_padding(cursors: &mut Cursors<'_>, va: u64) -> bool {
    cursors.decode(va).is_none_or(|i| {
        i.code() == Code::INVALID || matches!(i.mnemonic(), Mnemonic::Int3 | Mnemonic::Ud2)
    })
}

/// Tells whether `va` opens the way a function opens.
///
/// A jump to such an address is a tail call. On x64 the frame is taken
/// once, at the entry: an argument homed to its slot, a callee-saved push,
/// a `sub rsp, N` never appear in the middle of a function, so any of them
/// at a jump target says the target is another function. 32-bit code pushes
/// in its middle to pass arguments, so only the shapes no argument push
/// makes are believed there: `push ebp; mov ebp, esp`, the hotpatch
/// `mov edi, edi`, `sub esp, N` then a register saved or the cookie
/// loaded, an `endbr32`, or a thunk's `jmp [slot]`.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `va` - The jump target.
pub(super) fn opens_a_function(cursors: &mut Cursors<'_>, va: u64) -> bool {
    let Some(first) = cursors.decode(va) else {
        return false;
    };
    if first.code() == Code::INVALID {
        return false;
    }
    if cursors.bitness == 64 {
        return prologue_like(&first);
    }
    let is = |i: &Instruction, r: Register| {
        i.op0_kind() == OpKind::Register && i.op0_register().full_register() == r
    };
    match first.mnemonic() {
        Mnemonic::Push if is(&first, Register::RBP) => {
            cursors.decode(first.next_ip()).is_some_and(|second| {
                second.mnemonic() == Mnemonic::Mov
                    && is(&second, Register::RBP)
                    && second.op1_kind() == OpKind::Register
                    && second.op1_register().full_register() == Register::RSP
            })
        }
        Mnemonic::Push
            if matches!(
                first.op0_kind(),
                OpKind::Immediate8to32 | OpKind::Immediate32
            ) =>
        {
            let program = cursors.program;
            let bitness = cursors.bitness;
            let Some(second) = cursors.decode(first.next_ip()) else {
                return false;
            };
            if second.mnemonic() != Mnemonic::Push
                || second.op0_kind() != OpKind::Immediate32
                || seh_scope_roots(program, u64::from(second.immediate32()), va).is_empty()
            {
                return false;
            }
            cursors.decode(second.next_ip()).is_some_and(|third| {
                third.flow_control() == FlowControl::Call
                    && near_target(&third)
                        .is_some_and(|t| frame_helper_name(program, bitness, t).is_some())
            })
        }
        Mnemonic::Mov => {
            first.op0_kind() == OpKind::Register
                && first.op1_kind() == OpKind::Register
                && first.op0_register() == first.op1_register()
        }
        Mnemonic::Sub => {
            is(&first, Register::RSP)
                && first.op1_kind() != OpKind::Register
                && cursors.decode(first.next_ip()).is_some_and(|second| {
                    let saves = second.mnemonic() == Mnemonic::Push
                        && second.op0_kind() == OpKind::Register
                        && matches!(
                            second.op0_register().full_register(),
                            Register::RBX | Register::RSI | Register::RDI | Register::RBP
                        );
                    let cookie = second.mnemonic() == Mnemonic::Mov
                        && second.op1_kind() == OpKind::Memory
                        && second.memory_base() == Register::None
                        && second.memory_index() == Register::None;
                    saves || cookie
                })
        }
        Mnemonic::Endbr32 => true,
        Mnemonic::Jmp => first.op0_kind() == OpKind::Memory,
        _ => false,
    }
}

/// Tells whether `instr` is one a function opens with.
///
/// A callee-saved register pushed, an argument register homed to its stack
/// slot, the frame taken with `sub rsp, N`, `mov rax, rsp` before a big
/// frame, the hotpatch `mov edi, edi`, an `endbr`, or the `jmp` of a
/// thunk. A leaf that opens with its work (`xor eax, eax; ret`) is not
/// recognized here, and is found by the call or the pointer that names it.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
pub(super) fn prologue_like(instr: &Instruction) -> bool {
    let op0_reg = instr.op0_kind() == OpKind::Register;
    let op1_reg = instr.op1_kind() == OpKind::Register;
    match instr.mnemonic() {
        Mnemonic::Push => {
            op0_reg
                && matches!(
                    instr.op0_register().full_register(),
                    Register::RBX
                        | Register::RBP
                        | Register::RSI
                        | Register::RDI
                        | Register::RCX
                        | Register::R12
                        | Register::R13
                        | Register::R14
                        | Register::R15
                )
        }
        Mnemonic::Mov => {
            let homing = instr.op0_kind() == OpKind::Memory
                && instr.memory_base().full_register() == Register::RSP
                && instr.memory_index() == Register::None
                && matches!(instr.memory_displacement64(), 0x8 | 0x10 | 0x18 | 0x20)
                && op1_reg
                && matches!(
                    instr.op1_register().full_register(),
                    Register::RCX
                        | Register::RDX
                        | Register::R8
                        | Register::R9
                        | Register::RBX
                        | Register::RBP
                        | Register::RSI
                        | Register::RDI
                        | Register::R12
                        | Register::R13
                        | Register::R14
                        | Register::R15
                );
            let frame_copy =
                op0_reg && op1_reg && instr.op1_register().full_register() == Register::RSP;
            let hotpatch = op0_reg && op1_reg && instr.op0_register() == instr.op1_register();
            homing || frame_copy || hotpatch
        }
        Mnemonic::Sub => moves_rsp_by_imm(instr),
        Mnemonic::Endbr64 | Mnemonic::Endbr32 | Mnemonic::Jmp => true,
        _ => false,
    }
}

/// Names a mnemonic for the seed trace, as `decoded <mnemonic>`.
///
/// A handful of names cover what the trace has ever shown; the rest share
/// one line rather than allocate for a diagnostic.
///
/// # Arguments
///
/// * `m` - The mnemonic.
pub(super) fn mnemonic_name(m: Mnemonic) -> &'static str {
    match m {
        Mnemonic::In => "decoded in",
        Mnemonic::Out => "decoded out",
        Mnemonic::Hlt => "decoded hlt",
        Mnemonic::Cli | Mnemonic::Sti => "decoded cli/sti",
        Mnemonic::Int => "decoded int N",
        Mnemonic::Xlatb => "decoded xlatb",
        Mnemonic::Ud0 | Mnemonic::Ud1 => "decoded ud0/ud1",
        Mnemonic::Add => "decoded add [..], r8 (zero bytes)",
        Mnemonic::Jmp | Mnemonic::Call => "decoded a far transfer",
        _ => {
            "decoded an instruction no compiler emits (a segment override, a BCD adjust, a descriptor load)"
        }
    }
}

/// Tells whether a relocation site lies inside `instr` anywhere but at its
/// displacement or an immediate, where the address the loader patches sits.
///
/// # Arguments
///
/// * `cursors` - The decoders, one of which decoded `instr` last.
/// * `sites` - The relocation sites.
/// * `instr` - The instruction.
pub(super) fn misplaced_site(cursors: &Cursors<'_>, sites: &AddrSet, instr: &Instruction) -> bool {
    let start = instr.ip();
    let inside = || (start + 1..instr.next_ip()).filter(|va| sites.contains(*va));
    if inside().next().is_none() {
        return false;
    }
    let Some(offsets) = cursors.constant_offsets(instr) else {
        return true;
    };
    let patched = |va: u64| {
        let off = usize::try_from(va - start).unwrap_or(usize::MAX);
        (offsets.has_displacement()
            && off == offsets.displacement_offset()
            && offsets.displacement_size() >= 4)
            || (offsets.has_immediate()
                && off == offsets.immediate_offset()
                && offsets.immediate_size() >= 4)
            || (offsets.has_immediate2()
                && off == offsets.immediate_offset2()
                && offsets.immediate_size2() >= 4)
    };
    inside().any(|va| !patched(va))
}

/// Tells whether `instr` adds a byte register into memory other than the
/// way two zero bytes do, `add [eax], al`: rare in code, but written.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
pub(super) fn byte_add(instr: &Instruction) -> bool {
    instr.code() == Code::Add_rm8_r8
        && !(instr.op0_kind() == OpKind::Memory
            && instr.memory_base().full_register() == Register::RAX
            && instr.memory_index() == Register::None
            && instr.memory_displacement64() == 0
            && instr.op1_register() == Register::AL)
}

/// Tells whether `instr` is one no compiler emits into a program.
///
/// Data read as code decodes into these: `add [..], r8`, the opcode zero
/// that a run of zero bytes makes, port and descriptor-table instructions,
/// the BCD adjusts, far transfers, and interrupts other than the ones
/// Windows and Linux use. One of them in a walk from a guessed seed is the
/// clearest sign the seed was data; the same rule is what the disassemblers
/// with the best measured precision apply to their pattern hits.
///
/// A `nop` is left out even with a `cs` prefix, because that is exactly how
/// an aligning `nop` inside a function is written.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
/// * `bitness` - Decoder bitness; segment overrides mean nothing in 64-bit
///   code and no compiler writes them there.
/// * `pe` - The program is a PE, whose interrupts are Windows' and not
///   Linux's.
pub(super) fn odd_instruction(instr: &Instruction, bitness: u32, pe: bool) -> bool {
    use crate::isa::x86::Mnemonic as M;
    if instr.code() == Code::Add_rm8_r8 {
        return true;
    }
    if matches!(
        instr.mnemonic(),
        M::In
            | M::Out
            | M::Insb
            | M::Insw
            | M::Insd
            | M::Outsb
            | M::Outsw
            | M::Outsd
            | M::Hlt
            | M::Cli
            | M::Sti
            | M::Clts
            | M::Lgdt
            | M::Lidt
            | M::Lldt
            | M::Ltr
            | M::Sgdt
            | M::Sidt
            | M::Aaa
            | M::Aad
            | M::Aam
            | M::Aas
            | M::Daa
            | M::Das
            | M::Arpl
            | M::Bound
            | M::Lds
            | M::Les
            | M::Into
            | M::Iret
            | M::Iretd
            | M::Iretq
            | M::Retf
            | M::Lss
            | M::Lfs
            | M::Lgs
            | M::Lar
            | M::Lsl
            | M::Rsm
            | M::Int1
            | M::Xlatb
            | M::Rdmsr
            | M::Wrmsr
            | M::Ud0
            | M::Ud1
    ) {
        return true;
    }
    if matches!(instr.mnemonic(), M::Push | M::Pop)
        && instr.op0_kind() == OpKind::Register
        && matches!(
            instr.op0_register(),
            Register::ES | Register::CS | Register::SS | Register::DS
        )
    {
        return true;
    }
    if instr.mnemonic() == M::Int {
        let n = instr.immediate8();
        return if pe {
            !matches!(n, 3 | 0x29 | 0x2c | 0x2d | 0x2e)
        } else {
            !matches!(n, 3 | 0x80)
        };
    }
    if instr.mnemonic() == M::Ret && instr.op_count() == 1 {
        let n = instr.immediate16();
        if !n.is_multiple_of(4) || n > 0x1000 {
            return true;
        }
    }
    if matches!(
        instr.code(),
        Code::Jmp_ptr1616 | Code::Jmp_ptr1632 | Code::Call_ptr1616 | Code::Call_ptr1632
    ) {
        return true;
    }
    bitness == 64
        && instr.mnemonic() != M::Nop
        && matches!(
            instr.segment_prefix(),
            Register::CS | Register::DS | Register::ES | Register::SS
        )
}

/// Returns where the run of `int3` bytes starting at `va` ends.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - Where the run may start.
/// * `hi` - One past the last byte to consider.
///
/// # Returns
///
/// The first address past the run; `va` itself when no `int3` is there.
pub(super) fn int3_end(program: &Program, va: u64, hi: u64) -> u64 {
    let mut cur = va;
    while cur < hi && program.read_va(cur, 1) == Some(&[0xcc][..]) {
        cur += 1;
    }
    cur
}

/// Returns the import slot a thunk at `va` jumps through.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `va` - A call target.
///
/// # Returns
///
/// The slot address when the first instruction (after an optional `endbr64`)
/// is `jmp [slot]` with a rip-relative or absolute operand, else `None`.
pub(super) fn thunk_slot(cursors: &mut Cursors<'_>, va: u64) -> Option<u64> {
    let mut instr = cursors.decode(va)?;
    if matches!(instr.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) {
        instr = cursors.decode(instr.next_ip())?;
    }
    slot_jump(&instr)
}

/// The slot `instr` jumps through when it is `jmp [slot]` with a
/// rip-relative or absolute operand.
///
/// # Arguments
///
/// * `instr` - The instruction.
pub(super) fn slot_jump(instr: &Instruction) -> Option<u64> {
    if instr.mnemonic() != Mnemonic::Jmp || instr.op0_kind() != OpKind::Memory {
        return None;
    }
    if !matches!(instr.memory_base(), Register::None | Register::RIP)
        || instr.memory_index() != Register::None
    {
        return None;
    }
    Some(instr.memory_displacement64())
}

/// Tells whether a heuristic seed can start a function.
///
/// Pointer and padding seeds are guesses; one that lands on an `int3`, on
/// bytes that do not decode, inside a procedure linkage table (the GOT's
/// lazy-binding pointers aim at the `push` after each stub's jump), or
/// inside a function an x64 exception table declares ([`declared_interior`]:
/// a catch funclet returns its continuation there, `lea rax, [label]`) is
/// not a function.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The candidate entry.
pub(super) fn plausible_entry(program: &Program, bitness: u32, va: u64) -> bool {
    if program
        .section_at(va)
        .is_none_or(|s| s.name.starts_with(".plt"))
        || string_at(program, va)
        || declared_interior(program, va)
    {
        return false;
    }
    decode_at(program, bitness, va)
        .is_some_and(|i| i.code() != Code::INVALID && i.mnemonic() != Mnemonic::Int3)
}

/// Whether `va` follows `int3` padding, so a jump there is a tail call.
///
/// MSVC pads with `int3` only between functions; inside one, an aligned
/// loop head follows `nop`s. On x64 the exception table has the last word:
/// a target inside a function it declares is the function's own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The jump target.
pub(super) fn after_padding(program: &Program, bitness: u32, va: u64) -> bool {
    if program.format != crate::program::BinaryFormat::Pe
        || va < 2
        || program.read_va(va - 2, 2) != Some(&[0xcc, 0xcc][..])
    {
        return false;
    }
    if bitness == 64 {
        !program.function_ranges.is_empty() && !declared_interior(program, va)
    } else {
        true
    }
}

/// Whether an x64 exception table puts `va` inside a function it declares,
/// past its start, or in one of a function's separated chunks.
///
/// No function starts there, so a jump there is the function's own: the
/// shapes that otherwise read as a tail call - a jump after the frame's
/// release, to code that opens like a function, over padding - are only
/// guesses the table overrules. MSVC threads jumps through shared `jmp`
/// blocks and stores to stack slots (`mov [rsp+0x30], eax`), and both read
/// as a function's opening.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The jump target.
pub(super) fn declared_interior(program: &Program, va: u64) -> bool {
    /// Whether `va` lies in one of `ranges` (sorted by start), past its start
    /// unless `at_start`.
    fn inside(ranges: &[(u64, u64)], va: u64, at_start: bool) -> bool {
        let k = ranges.partition_point(|r| r.0 <= va);
        k > 0 && {
            let (lo, hi) = ranges[k - 1];
            va < hi && (at_start || va > lo)
        }
    }
    program.format == crate::program::BinaryFormat::Pe
        && program.is_64
        && (inside(&program.function_ranges, va, false)
            || inside(&program.headers.chained_chunks, va, true))
}

/// Whether the instruction at `va` addresses memory through the frame
/// pointer, which on a function's entry still holds its caller's frame.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The address.
pub(super) fn opens_on_frame(program: &Program, bitness: u32, va: u64) -> bool {
    decode_at(program, bitness, va).is_some_and(|i| {
        (0..i.op_count()).any(|k| i.op_kind(k) == OpKind::Memory)
            && i.memory_base().full_register() == Register::RBP
    })
}
