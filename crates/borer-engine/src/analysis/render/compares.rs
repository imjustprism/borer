//! Which immediates a function compares against, as opposed to the
//! constants it mixes into a hash.

use super::*;
use crate::analysis::decompile::abi::Conv;

/// Most instructions [`flags_decide`] visits for one flag write.
const FLAG_SCAN_MAX: usize = 4096;

/// Where a compared value comes from, so a hint does not call every one
/// the function's first argument.
pub(super) enum Compared {
    /// Argument `n` (counting from 1) still in the register the convention
    /// passed it in.
    Argument(u8),
    /// A register copied from a call's return register.
    CallResult,
    /// Anything else: a local, a memory operand, a later argument the scan
    /// cannot place, or a value the scan cannot show is an argument.
    Other,
}

/// The immediate `instrs[at]` compares, when it does.
///
/// A `cmp` or `test` always does. A `sub`, `xor` or `and` does when a
/// later instruction reads the flags it wrote before anything overwrites
/// them. The scan follows a direct jump, so a block that only sits between
/// the two in address order cannot hide the check. Copying the result does
/// not hide it either: `sub ecx, imm; mov edx, ecx; sete al` still
/// compares, and `sub edx, imm; xor esi, edx` does not, because the `xor`
/// overwrites the flags.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `at` - The instruction to read.
///
/// # Returns
///
/// The immediate, or `None` when the instruction does not compare one.
pub(super) fn compare_immediate(instrs: &[Instruction], at: usize) -> Option<u64> {
    let i = instrs.get(at)?;
    let plain = matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test);
    let arith = matches!(i.mnemonic(), Mnemonic::Sub | Mnemonic::Xor | Mnemonic::And);
    if !plain && !arith {
        return None;
    }
    let value = immediate_of(i)?;
    if plain || flags_decide(instrs, at) {
        Some(value)
    } else {
        None
    }
}

/// Immediates of `sub`, `xor` and `and` that no later flag read decides.
///
/// A call, a return or another flag write leaves them undecided. The
/// decompiled text can still print one as `==`, and a hint skips it.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
///
/// # Returns
///
/// Those immediates, each once.
pub(super) fn undecided_immediates(instrs: &[Instruction]) -> BTreeSet<u64> {
    instrs
        .iter()
        .enumerate()
        .filter(|(at, i)| {
            matches!(i.mnemonic(), Mnemonic::Sub | Mnemonic::Xor | Mnemonic::And)
                && compare_immediate(instrs, *at).is_none()
        })
        .filter_map(|(_, i)| immediate_of(i))
        .collect()
}

/// Whether a later instruction reads a flag `instrs[at]` wrote that no
/// instruction in between has overwritten.
///
/// A direct jump is followed. A conditional branch counts only when it
/// reads one of those flags: `sub` then `inc` then `jz` does not, because
/// `inc` replaced the zero flag. A write of one flag leaves the others:
/// `clc` clears carry and a following `sete` still reads the compare's
/// zero flag. A call leaves the flags undefined, so the scan stops there.
/// Each instruction is visited once, and at most
/// [`FLAG_SCAN_MAX`] of them, so the scan stops at a loop.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `at` - The instruction that wrote the flags.
fn flags_decide(instrs: &[Instruction], at: usize) -> bool {
    let mut live = instrs.get(at).map_or(0, Instruction::rflags_modified);
    if live == 0 {
        return false;
    }
    let mut cursor = at.saturating_add(1);
    let mut seen = BTreeSet::new();
    while seen.len() < FLAG_SCAN_MAX && seen.insert(cursor) {
        if cursor >= instrs.len() {
            return false;
        }
        let n = &instrs[cursor];
        if n.rflags_read() & live != 0 {
            return true;
        }
        live &= !n.rflags_modified();
        if live == 0 {
            return false;
        }
        if n.flow_control() == FlowControl::UnconditionalBranch {
            let target = n.near_branch_target();
            let Ok(pos) = instrs.binary_search_by_key(&target, Instruction::ip) else {
                return false;
            };
            cursor = pos;
            continue;
        }
        if matches!(
            n.flow_control(),
            FlowControl::Return
                | FlowControl::Call
                | FlowControl::IndirectCall
                | FlowControl::IndirectBranch
                | FlowControl::Interrupt
                | FlowControl::Exception
        ) {
            return false;
        }
        cursor += 1;
    }
    false
}

/// Says whether the value compared at `at` is an argument or a call's
/// result.
///
/// The scan walks back to the entry. A copy of every compared byte
/// (`mov ecx, eax`) follows the source register. A copy of fewer bytes
/// (`mov dl, cl` under `cmp edx, imm`) does not. A call defines the return
/// register and ends the trace of every register it may clobber, so
/// `call; cmp ecx, imm` is not an argument on either x64 convention. A
/// register that still holds an argument is that argument's number in
/// `conv`. A convention with no register arguments never claims one.
///
/// A branch that jumps over a copy and still reaches the compare leaves
/// the source unnamed.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `at` - The comparing instruction.
/// * `conv` - The function's calling convention.
pub(super) fn compared_source(instrs: &[Instruction], at: usize, conv: &Conv) -> Compared {
    let Some(i) = instrs.get(at) else {
        return Compared::Other;
    };
    if i.op0_kind() != OpKind::Register {
        return Compared::Other;
    }
    let compared = i.op0_register();
    let need = compared.size();
    let mut reg = compared.full_register();
    for n in instrs[..at].iter().rev() {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            if reg == Register::RAX {
                return Compared::CallResult;
            }
            if conv.volatile.contains(&reg) {
                return Compared::Other;
            }
            continue;
        }
        if let Some(src) = copied_from(n, reg, need) {
            if branch_skips(instrs, n.ip(), i.ip()) {
                return Compared::Other;
            }
            reg = src;
            continue;
        }
        if reg_touch(&mut InstructionInfoFactory::new(), n, reg).1 {
            return Compared::Other;
        }
    }
    let Some(pos) = conv.args.iter().position(|r| *r == reg) else {
        return Compared::Other;
    };
    let Some(n) = pos.checked_add(1).and_then(|n| u8::try_from(n).ok()) else {
        return Compared::Other;
    };
    Compared::Argument(n)
}

/// The first immediate operand of `i`.
fn immediate_of(i: &Instruction) -> Option<u64> {
    (0..i.op_count()).find_map(|n| match i.op_kind(n) {
        OpKind::Immediate8 => Some(u64::from(i.immediate8())),
        OpKind::Immediate8to16
        | OpKind::Immediate8to32
        | OpKind::Immediate8to64
        | OpKind::Immediate16
        | OpKind::Immediate32
        | OpKind::Immediate32to64
        | OpKind::Immediate64 => Some(i.immediate(n)),
        _ => None,
    })
}

/// Whether `n` reads and writes `reg`, by its full register.
fn reg_touch(factory: &mut InstructionInfoFactory, n: &Instruction, reg: Register) -> (bool, bool) {
    let mut read = false;
    let mut write = false;
    for ur in factory.info(n).used_registers() {
        if ur.register().full_register() != reg {
            continue;
        }
        read |= matches!(
            ur.access(),
            OpAccess::Read | OpAccess::ReadWrite | OpAccess::CondRead | OpAccess::ReadCondWrite
        );
        write |= matches!(
            ur.access(),
            OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite | OpAccess::ReadCondWrite
        );
    }
    (read, write)
}

/// Whether a branch before `from` lands in `(from, to]`.
///
/// That branch reaches `to` without running the instruction at `from`.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `from` - The instruction a path can jump over.
/// * `to` - The instruction that path still reaches.
fn branch_skips(instrs: &[Instruction], from: u64, to: u64) -> bool {
    instrs.iter().any(|n| {
        if n.ip() >= from
            || !matches!(
                n.flow_control(),
                FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch
            )
        {
            return false;
        }
        let target = n.near_branch_target();
        target > from && target <= to
    })
}

/// The register a full-width `mov` into `dest` copies.
///
/// A write narrower than `need` bytes, other than a 32-bit write that
/// zero-extends, does not define the compared value.
///
/// # Arguments
///
/// * `n` - The instruction that may be the copy.
/// * `dest` - The full register the compare reads.
/// * `need` - How many bytes of `dest` the compare reads.
fn copied_from(n: &Instruction, dest: Register, need: usize) -> Option<Register> {
    if n.mnemonic() != Mnemonic::Mov
        || n.op_count() != 2
        || n.op0_kind() != OpKind::Register
        || n.op1_kind() != OpKind::Register
        || n.op0_register().full_register() != dest
    {
        return None;
    }
    let written = n.op0_register();
    let source = n.op1_register();
    if !covers(written, need) || !covers(source, need) {
        return None;
    }
    Some(source.full_register())
}

/// Whether a write of `reg` defines at least `need` bytes.
///
/// A 32-bit write zero-extends, so it defines the whole register.
fn covers(reg: Register, need: usize) -> bool {
    reg.size() >= need || reg.size() == 4 && need <= 8
}
