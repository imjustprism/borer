//! Which immediates a function compares against, as opposed to the
//! constants it mixes into a hash.

use super::*;

/// Where a compared value comes from, so a hint does not call every one
/// the function's first argument.
pub(super) enum Compared {
    /// The architecture's first integer argument, never written before the
    /// compare.
    Argument,
    /// A register copied from a call's return register.
    CallResult,
    /// Anything else: a local, a memory operand, or a value the scan cannot
    /// show is the argument.
    Other,
}

/// The immediate `instrs[at]` compares, when it does.
///
/// A `cmp` or `test` always does. A `sub`, `xor` or `and` does only when a
/// later instruction reads the flags it wrote and nothing reads the result
/// first: `sub ecx, imm; jz` is a compare, and `sub edx, imm; xor esi, edx`
/// is arithmetic whose flags the `xor` overwrites.
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
    if plain {
        return Some(value);
    }
    if i.op0_kind() != OpKind::Register {
        return None;
    }
    let dest = i.op0_register().full_register();
    let mut factory = InstructionInfoFactory::new();
    let mut read = false;
    for n in instrs.iter().skip(at + 1).take(8) {
        let (reads, writes) = reg_touch(&mut factory, n, dest);
        read |= reads && !writes;
        if reads_flags(n) {
            return (!read).then_some(value);
        }
        if n.rflags_modified() != 0 {
            return None;
        }
        if writes && !reads {
            read = false;
        }
    }
    None
}

/// Says whether the value compared at `at` is the first argument or a
/// call's result.
///
/// The scan walks back to the entry. A copy (`mov ecx, eax`) follows the
/// source register. A call defines the return register and nothing else
/// this scan tracks, so `call; mov ecx, eax; cmp ecx, imm` is a call
/// result and a `cmp ecx, imm` with `ecx` still intact is the argument.
/// On a 32-bit target the first argument arrives on the stack, so a
/// register compare is never claimed as one.
///
/// # Arguments
///
/// * `instrs` - The function's instructions, in address order.
/// * `at` - The comparing instruction.
/// * `bits` - The decoder bitness.
pub(super) fn compared_source(instrs: &[Instruction], at: usize, bits: u32) -> Compared {
    let Some(i) = instrs.get(at) else {
        return Compared::Other;
    };
    if i.op0_kind() != OpKind::Register || bits != 64 {
        return Compared::Other;
    }
    let mut reg = i.op0_register().full_register();
    for n in instrs[..at].iter().rev() {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            if reg == Register::RAX {
                return Compared::CallResult;
            }
            continue;
        }
        if let Some(src) = copied_from(n, reg) {
            reg = src;
            continue;
        }
        if reg_touch(&mut InstructionInfoFactory::new(), n, reg).1 {
            return Compared::Other;
        }
    }
    if reg == Register::RCX {
        Compared::Argument
    } else {
        Compared::Other
    }
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

/// Whether `n` reads the flags a compare writes.
fn reads_flags(n: &Instruction) -> bool {
    n.flow_control() == FlowControl::ConditionalBranch || n.rflags_read() != 0
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

/// The register a `mov` into `dest` copies, when that is all the
/// instruction does.
fn copied_from(n: &Instruction, dest: Register) -> Option<Register> {
    if n.mnemonic() != Mnemonic::Mov
        || n.op_count() != 2
        || n.op0_kind() != OpKind::Register
        || n.op1_kind() != OpKind::Register
        || n.op0_register().full_register() != dest
    {
        return None;
    }
    Some(n.op1_register().full_register())
}
