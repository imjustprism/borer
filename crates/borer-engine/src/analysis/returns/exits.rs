//! What one block on a path to a `ret` leaves in a result register, read
//! backwards from the block's end, and the compiler idioms that say a path
//! leaves no result at all.

use super::*;

/// What a block's instructions, read back from its end, say about the
/// result register a path hands back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Scan {
    /// The last write of the register, and whether some instruction after
    /// it on the path reads the value back (a compare, a store, a copy).
    Wrote(Writer, bool),
    /// A compiler idiom says the path hands back no result ([`scan`]).
    Idle,
    /// Nothing in the block writes the register; whether something in it
    /// reads it.
    Open(bool),
}

/// Reads a block backwards from its end for the last write of a result
/// register.
///
/// A call writes rax with its callee's result, except a call to a callee
/// that hands it back untouched, which is looked past. Three idioms of
/// rax say the path holds no result, as a value-returning function's code
/// never does: a one-byte `nop` met before any write and followed by the
/// epilogue's unwinding of the frame (or by another such `nop`), which
/// unoptimized GCC code puts at a `void` function's closing brace; a stack-cookie check run in rax (`sub rax, fs:[0x28]`), which
/// a compiler places in the result register only when it holds nothing;
/// and `xor eax, eax` within a run that also clears two or more of `ecx`,
/// `esi`, `edi` and `r8d`-`r11d`, which no ABI returns in, each one read
/// by nothing before the exit: the epilogue of code built to zero the
/// registers it used (`-fzero-call-used-regs`), which leaves rax alone
/// when it holds the result. A cleared register the exit path then reads
/// (`xor ecx, ecx; mov [rdx], ecx`) is a value, not an epilogue.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `instrs` - The block's instructions, after any skipped at its start.
/// * `whole` - The block's instructions, for a copy's source precision
///   ([`copied_bits`]).
/// * `reg` - The result register followed.
/// * `preserves` - Whether the direct callee at an entry hands the
///   register back untouched.
pub(super) fn scan(
    factory: &mut InstructionInfoFactory,
    instrs: &[Instruction],
    whole: &[Instruction],
    reg: ResultReg,
    preserves: &dyn Fn(u64) -> bool,
) -> Scan {
    let rax = reg == ResultReg::Rax;
    let mut read = false;
    let (mut cleared, mut used) = (0u8, 0u8);
    let mut after: Option<&Instruction> = None;
    for i in instrs.iter().rev() {
        let next = after.replace(i);
        if !is_call(i) {
            let wrote = match reg {
                ResultReg::Rax => rax_write(factory, i).map(|_| Writer::Own(None)),
                ResultReg::Rdx => None,
                ResultReg::Xmm0 => writes_xmm0(factory, i)
                    .then(|| Writer::Own(float_bits(i).or_else(|| copied_bits(whole, i)))),
            };
            if rax && closing_nop(i) && next.is_some_and(|n| closing_nop(n) || unwinds(n)) {
                return Scan::Idle;
            }
            if let Some(w) = wrote {
                let idle = rax
                    && (cookie_check(i)
                        || (cleared.count_ones() >= 2 && self_xor(i, Register::RAX)));
                return if idle {
                    Scan::Idle
                } else {
                    Scan::Wrote(w, read)
                };
            }
            if rax {
                for (bit, &r) in SCRATCH.iter().enumerate() {
                    if self_xor(i, r) && used & (1 << bit) == 0 {
                        cleared |= 1 << bit;
                    }
                }
                used |= scratch_reads(factory, i);
            }
            read |= rax && reads_rax(factory, i);
            continue;
        }
        let direct = matches!(
            i.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        );
        return match i.near_branch_target() {
            t if direct && preserves(t) => continue,
            t if direct => Scan::Wrote(Writer::Call(t), read),
            _ => Scan::Wrote(Writer::Indirect, read),
        };
    }
    Scan::Open(read)
}

/// Tells whether an instruction is the one-byte `nop` (`0x90`).
///
/// # Arguments
///
/// * `i` - The instruction.
fn closing_nop(i: &Instruction) -> bool {
    i.mnemonic() == Mnemonic::Nop && i.len() == 1
}

/// Tells whether an instruction unwinds a stack frame on the way out:
/// `leave`, a `pop`, or a move, add or `lea` into the stack pointer.
///
/// # Arguments
///
/// * `i` - The instruction.
fn unwinds(i: &Instruction) -> bool {
    match i.mnemonic() {
        Mnemonic::Leave | Mnemonic::Pop => true,
        Mnemonic::Mov
            if i.op0_kind() == OpKind::Register
                && i.op1_kind() == OpKind::Memory
                && matches!(i.memory_base(), Register::RBP | Register::EBP)
                && matches!(
                    i.op0_register().full_register(),
                    Register::RBX | Register::R12 | Register::R13 | Register::R14 | Register::R15
                ) =>
        {
            true
        }
        Mnemonic::Mov | Mnemonic::Add | Mnemonic::Lea => {
            i.op0_kind() == OpKind::Register && i.op0_register().full_register() == Register::RSP
        }
        _ => false,
    }
}

/// The scratch registers no calling convention returns a value in, which
/// a register-clearing epilogue zeroes beside rax.
const SCRATCH: [Register; 7] = [
    Register::RCX,
    Register::RSI,
    Register::RDI,
    Register::R8,
    Register::R9,
    Register::R10,
    Register::R11,
];

/// Tells whether an instruction is `xor r, r` (or `sub r, r`) on some
/// width of `full`.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `full` - The 64-bit register.
fn self_xor(i: &Instruction, full: Register) -> bool {
    matches!(i.mnemonic(), Mnemonic::Xor | Mnemonic::Sub)
        && i.op0_kind() == OpKind::Register
        && i.op1_kind() == OpKind::Register
        && i.op0_register() == i.op1_register()
        && i.op0_register().full_register() == full
}

/// Tells whether an instruction checks a stack cookie in the thread block.
///
/// That is `sub` or `xor` with the cookie's own slot, `fs:[0x28]` or
/// `gs:[0x14]`. Any other thread-local operand is a value the function may
/// be computing its result from.
///
/// # Arguments
///
/// * `i` - The instruction.
fn cookie_check(i: &Instruction) -> bool {
    matches!(i.mnemonic(), Mnemonic::Sub | Mnemonic::Xor)
        && i.op1_kind() == OpKind::Memory
        && i.memory_base() == Register::None
        && i.memory_index() == Register::None
        && matches!(
            (i.memory_segment(), i.memory_displacement64()),
            (Register::FS, COOKIE_FS) | (Register::GS, COOKIE_GS)
        )
}

/// Where glibc keeps the stack cookie on x86-64, in the thread block `fs`
/// points at.
const COOKIE_FS: u64 = 0x28;

/// Where glibc keeps it on i386, under `gs`.
const COOKIE_GS: u64 = 0x14;

/// The [`SCRATCH`] registers an instruction reads, one bit each in their
/// order.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn scratch_reads(factory: &mut InstructionInfoFactory, i: &Instruction) -> u8 {
    let mut mask = 0;
    for ur in factory.info(i).used_registers() {
        let reads = matches!(
            ur.access(),
            OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite
        );
        if let Some(bit) = SCRATCH
            .iter()
            .position(|&r| r == ur.register().full_register())
            && reads
        {
            mask |= 1 << bit;
        }
    }
    mask
}

/// Tells whether an instruction reads rax at any width.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn reads_rax(factory: &mut InstructionInfoFactory, i: &Instruction) -> bool {
    factory.info(i).used_registers().iter().any(|ur| {
        ur.register().full_register() == Register::RAX
            && matches!(
                ur.access(),
                OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite
            )
    })
}
