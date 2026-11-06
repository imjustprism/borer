//! Which immediates a function compares against, as opposed to the
//! constants it mixes into a hash.

use super::*;
use crate::analysis::decompile::abi::Conv;
use crate::isa::x86::ConditionCode;

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
/// overwrites the flags. A later `test` of the result against itself is
/// that compare when something reads the flags the `test` wrote.
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
    if plain || flags_decide(instrs, at) || result_checked(instrs, at) {
        Some(value)
    } else {
        None
    }
}

/// Immediates of `sub`, `xor` and `and` that no later flag read decides.
///
/// A call, a return, or a flag write that is not a test of the result
/// leaves them undecided. The decompiled text can still print one as
/// `==`, and a hint skips it.
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
/// `inc` replaced the zero flag. `adc` reads the carry to continue the
/// sum, so it is not that check. A write of one flag leaves the others:
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
        let reads = n.rflags_read() & live != 0;
        let decides = n.flow_control() == FlowControl::ConditionalBranch
            || n.condition_code() != ConditionCode::None;
        if reads && decides {
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

/// Whether a later instruction tests the result of `instrs[at]` against
/// zero and something reads the flags that test wrote.
///
/// `test` of the register against itself, or `cmp` of it with zero,
/// replaces the flags the arithmetic wrote. A full-width copy of the
/// result is still that result. A write of every copy, a call, or a return
/// ends the scan.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `at` - The arithmetic instruction.
fn result_checked(instrs: &[Instruction], at: usize) -> bool {
    let Some(wrote) = instrs.get(at).and_then(arith_reg) else {
        return false;
    };
    let mut held = [Register::None; 4];
    held[0] = wrote.full_register();
    let need = wrote.size();
    let mut factory = InstructionInfoFactory::new();
    let mut cursor = at.saturating_add(1);
    let mut seen = BTreeSet::new();
    while seen.len() < FLAG_SCAN_MAX && seen.insert(cursor) {
        if cursor >= instrs.len() {
            return false;
        }
        let n = &instrs[cursor];
        if zero_checks(n, &held, need) && flags_decide(instrs, cursor) {
            return true;
        }
        if let Some(dest) = copied_into(n, &held, need) {
            if !held.contains(&dest)
                && let Some(slot) = held.iter_mut().find(|r| **r == Register::None)
            {
                *slot = dest;
            }
        } else {
            for reg in &mut held {
                if *reg != Register::None && reg_touch(&mut factory, n, *reg).1 {
                    *reg = Register::None;
                }
            }
        }
        if held.iter().all(|r| *r == Register::None) {
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

/// The register a `sub`, `xor` or `and` writes, when it writes one.
fn arith_reg(i: &Instruction) -> Option<Register> {
    if !matches!(i.mnemonic(), Mnemonic::Sub | Mnemonic::Xor | Mnemonic::And) {
        return None;
    }
    if i.op0_kind() != OpKind::Register {
        return None;
    }
    Some(i.op0_register())
}

/// Whether `n` compares a held register with zero.
///
/// The tested width is the width that was written, or the full register
/// after a 32-bit write, which zero-extends.
fn zero_checks(n: &Instruction, held: &[Register; 4], need: usize) -> bool {
    if n.op0_kind() != OpKind::Register {
        return false;
    }
    let reg = n.op0_register();
    let width = reg.size() == need || reg.size() == 8 && need == 4;
    if !width || !held.contains(&reg.full_register()) {
        return false;
    }
    match n.mnemonic() {
        Mnemonic::Test => {
            n.op_count() == 2
                && n.op1_kind() == OpKind::Register
                && n.op1_register().full_register() == reg.full_register()
                && n.op1_register().size() == reg.size()
        }
        Mnemonic::Cmp => immediate_of(n) == Some(0),
        _ => false,
    }
}

/// The register a full-width `mov` copies a held result into.
///
/// A 32-bit destination zero-extends, so it can hold a 64-bit result. The
/// source has to cover `need` itself: `mov ebx, eax` keeps only the low
/// half of `rax`.
fn copied_into(n: &Instruction, held: &[Register; 4], need: usize) -> Option<Register> {
    if n.mnemonic() != Mnemonic::Mov
        || n.op_count() != 2
        || n.op0_kind() != OpKind::Register
        || n.op1_kind() != OpKind::Register
    {
        return None;
    }
    let dest = n.op0_register();
    let source = n.op1_register();
    if !held.contains(&source.full_register()) || !covers(dest, need) || source.size() < need {
        return None;
    }
    Some(dest.full_register())
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
/// the source unnamed, and so does a later block that writes a traced
/// register and jumps back.
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
    let mut traced = vec![reg];
    let found = 'walk: {
        for n in instrs[..at].iter().rev() {
            if matches!(
                n.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                if reg == Register::RAX {
                    break 'walk Compared::CallResult;
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
                traced.push(src);
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
    };
    if rejoined(instrs, at, &traced, conv) {
        return Compared::Other;
    }
    found
}

/// Whether code after the compare at `at` may jump back to or before it
/// after writing a register the trace read.
///
/// The trace walks back in address order, which is execution order only
/// when no later block jumps back. A later block that writes `rcx` and
/// jumps to the compare defines it on a path the trace never saw. An
/// indirect jump may land anywhere, and a call clobbers its volatile
/// registers.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `at` - The comparing instruction.
/// * `traced` - The full registers the trace followed back from the compare.
/// * `conv` - The function's calling convention.
fn rejoined(instrs: &[Instruction], at: usize, traced: &[Register], conv: &Conv) -> bool {
    let Some((cmp, later)) = instrs.get(at..).and_then(<[_]>::split_first) else {
        return false;
    };
    let back = later.iter().any(|n| match n.flow_control() {
        FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch => {
            n.near_branch_target() <= cmp.ip()
        }
        FlowControl::IndirectBranch => true,
        _ => false,
    });
    let mut factory = InstructionInfoFactory::new();
    back && later.iter().any(|n| {
        traced.iter().any(|&r| {
            reg_touch(&mut factory, n, r).1
                || (matches!(
                    n.flow_control(),
                    FlowControl::Call | FlowControl::IndirectCall
                ) && (r == Register::RAX || conv.volatile.contains(&r)))
        })
    })
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
pub(crate) fn reg_touch(
    factory: &mut InstructionInfoFactory,
    n: &Instruction,
    reg: Register,
) -> (bool, bool) {
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
/// A 32-bit write zero-extends, so it defines a 64-bit destination. The
/// source has to be at least `need` bytes. `mov ecx, eax` does not carry
/// the high half of `rax` into a compare of `rcx`.
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
    if !covers(written, need) || source.size() < need {
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
