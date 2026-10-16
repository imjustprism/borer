//! Syscall sites: where a Linux program enters the kernel by number.
//!
//! A static or stripped Linux binary imports nothing, so what it can do
//! shows only where it calls the kernel itself: `syscall` on x86-64 with
//! the number in `rax`, `int 0x80` with it in `eax` (the i386 entry, which
//! 64-bit code can use too), and `svc #0` on arm64 with it in `x8`.
//! [`syscall_sites`] finds each such instruction inside a discovered
//! function of an ELF and reads the number its block sets before it
//! (`mov eax, N`, `xor eax, eax`, `push N; pop rax`, `movz w8, #N`); a
//! number set in another block, or computed, is unresolved rather than
//! guessed. The names come from the Linux table of the entry used. The
//! capability map, a function's summary and its listing read the sites
//! the way they read imported calls.

use std::sync::Arc;

use super::{Analysis, BasicBlock};
use crate::isa::Isa;
use crate::isa::x86::{
    Decoder, DecoderOptions, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind,
    Register,
};
use crate::program::{BinaryFormat, Program};

/// Most syscall sites read from one program.
const SITES_MAX: usize = 4096;

/// How a program enters the kernel, which says where the number is and
/// which table names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Gate {
    /// x86-64 `syscall`: the number in `rax`, the x86-64 table.
    Syscall,
    /// `int 0x80`: the number in `eax`, the i386 table.
    Int80,
    /// arm64 `svc #0`: the number in `x8`, the generic table.
    Svc,
}

impl Gate {
    /// Names a number by this entry's table.
    ///
    /// # Arguments
    ///
    /// * `nr` - The syscall number.
    ///
    /// # Returns
    ///
    /// The name, or `None` for a number the table does not list.
    fn name(self, nr: u64) -> Option<&'static str> {
        match self {
            Gate::Syscall => crate::emulate::linux_syscall_name(nr),
            Gate::Int80 => i386_syscall_name(nr),
            Gate::Svc => crate::emulate::a64::a64_syscall_name(nr),
        }
    }
}

/// One place a program enters the Linux kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyscallSite {
    /// The `syscall`, `int 0x80` or `svc #0` instruction's address.
    pub at: u64,
    /// The entry of the function it is in.
    pub function: u64,
    /// How it enters the kernel.
    pub gate: Gate,
    /// The number its block sets, `None` when the block does not set one.
    pub nr: Option<u64>,
    /// The number's name, `None` when there is no number or the table does
    /// not list it.
    pub name: Option<&'static str>,
}

impl SyscallSite {
    /// The site as listings tag it: `syscall socket`, `syscall 999` for a
    /// number the table does not list, `syscall ?` for one its block does
    /// not set.
    #[must_use]
    pub fn label(&self) -> String {
        match (self.name, self.nr) {
            (Some(name), _) => format!("syscall {name}"),
            (None, Some(nr)) => format!("syscall {nr}"),
            (None, None) => String::from("syscall ?"),
        }
    }
}

/// Returns the i386 Linux name of an `int 0x80` syscall number.
///
/// The table holds the calls a static i386 binary reaches for: files and
/// descriptors, processes, memory, identity and the sockets, both the
/// multiplexed `socketcall` and the direct calls Linux 4.3 added.
///
/// # Arguments
///
/// * `nr` - The number in `eax` at the `int 0x80`.
///
/// # Returns
///
/// The name, or `None` for a number this table does not list.
#[must_use]
pub fn i386_syscall_name(nr: u64) -> Option<&'static str> {
    Some(match nr {
        1 => "exit",
        2 => "fork",
        3 => "read",
        4 => "write",
        5 => "open",
        6 => "close",
        7 => "waitpid",
        8 => "creat",
        10 => "unlink",
        11 => "execve",
        12 => "chdir",
        15 => "chmod",
        19 => "lseek",
        20 => "getpid",
        26 => "ptrace",
        33 => "access",
        37 => "kill",
        38 => "rename",
        39 => "mkdir",
        41 => "dup",
        42 => "pipe",
        45 => "brk",
        54 => "ioctl",
        55 => "fcntl",
        63 => "dup2",
        64 => "getppid",
        90 => "mmap",
        91 => "munmap",
        102 => "socketcall",
        114 => "wait4",
        120 => "clone",
        122 => "uname",
        125 => "mprotect",
        162 => "nanosleep",
        172 => "prctl",
        190 => "vfork",
        192 => "mmap2",
        224 => "gettid",
        240 => "futex",
        252 => "exit_group",
        295 => "openat",
        355 => "getrandom",
        356 => "memfd_create",
        358 => "execveat",
        359 => "socket",
        361 => "bind",
        362 => "connect",
        363 => "listen",
        364 => "accept4",
        369 => "sendto",
        371 => "recvfrom",
        _ => return None,
    })
}

/// Finds an ELF's syscall sites, in address order, at most [`SITES_MAX`].
///
/// The executable sections are searched for the entries' encodings, and
/// an encoding counts only where it is an instruction of a discovered
/// function's block; the number is read from that block alone. Any other
/// format has none: a PE's `syscall` numbers are Windows', which change
/// with every build.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its functions.
///
/// # Returns
///
/// The sites, kept with the analysis once found.
pub fn syscall_sites(p: &Program, a: &Analysis) -> Arc<Vec<SyscallSite>> {
    a.derived.get_or_build("syscall_sites", (), || scan(p, a))
}

/// Searches the executable sections for syscall sites ([`syscall_sites`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its functions.
fn scan(p: &Program, a: &Analysis) -> Vec<SyscallSite> {
    /// `svc #0`, little-endian.
    const SVC0: [u8; 4] = [0x01, 0x00, 0x00, 0xd4];
    let mut out = Vec::new();
    let Some(isa) = p.arch.isa().filter(|_| p.format == BinaryFormat::Elf) else {
        return out;
    };
    'sections: for s in p.sections.iter().filter(|s| s.executable) {
        let Some(bytes) = p.section_bytes(s) else {
            continue;
        };
        let mut found = |site: Option<SyscallSite>| {
            out.extend(site);
            out.len() < SITES_MAX
        };
        match isa {
            Isa::A64 => {
                for (k, word) in bytes.chunks_exact(4).enumerate() {
                    if word == SVC0 {
                        let va = s.va.0.saturating_add(crate::num::from_usize(k * 4));
                        if !found(svc_site(p, a, va)) {
                            break 'sections;
                        }
                    }
                }
            }
            Isa::X86 { bits } => {
                for (k, pair) in bytes.windows(2).enumerate() {
                    let gate = match pair {
                        [0x0f, 0x05] if bits == 64 => Gate::Syscall,
                        [0xcd, 0x80] => Gate::Int80,
                        _ => continue,
                    };
                    let va = s.va.0.saturating_add(crate::num::from_usize(k));
                    if !found(x86_site(p, a, va, gate, bits)) {
                        break 'sections;
                    }
                }
            }
        }
    }
    out.sort_by_key(|s| s.at);
    out.dedup_by_key(|s| s.at);
    out.truncate(SITES_MAX);
    out
}

/// The function and the block an address is inside.
///
/// # Arguments
///
/// * `a` - The functions.
/// * `va` - The address.
fn block_of(a: &Analysis, va: u64) -> Option<(u64, &BasicBlock)> {
    let f = a.function_at(va)?;
    let b = f.blocks.iter().find(|b| b.start <= va && va < b.end)?;
    Some((f.entry, b))
}

/// Reads an x86 syscall site: the instruction at `va` when it is the
/// entry `gate` names and starts an instruction of its block, with the
/// number its block leaves in `eax`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its functions.
/// * `va` - Where the encoding is.
/// * `gate` - Which entry the encoding is.
/// * `bits` - Decoder bitness.
fn x86_site(p: &Program, a: &Analysis, va: u64, gate: Gate, bits: u32) -> Option<SyscallSite> {
    let (function, b) = block_of(a, va)?;
    let len = usize::try_from(va.checked_sub(b.start)?)
        .ok()?
        .checked_add(2)?;
    let code = p.read_va_upto(b.start, len)?;
    let mut factory = InstructionInfoFactory::new();
    let (mut value, mut pushed) = (None, None);
    for i in &mut Decoder::with_ip(bits, code, b.start, DecoderOptions::NONE) {
        if i.ip() == va {
            let is_gate = match gate {
                Gate::Syscall => i.mnemonic() == Mnemonic::Syscall,
                Gate::Int80 => {
                    i.mnemonic() == Mnemonic::Int && i.try_immediate(0).ok() == Some(0x80)
                }
                Gate::Svc => false,
            };
            return is_gate.then(|| SyscallSite {
                at: va,
                function,
                gate,
                nr: value,
                name: value.and_then(|nr| gate.name(nr)),
            });
        }
        if i.ip() > va {
            return None;
        }
        (value, pushed) = eax_after(&i, value, pushed, &mut factory);
    }
    None
}

/// The constant `eax` holds after an instruction, and the immediate the
/// instruction pushed, for a `pop rax` after it.
///
/// A syscall leaves its result in `eax`, so the next one's number is
/// whatever is set after it.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `value` - What `eax` held before it.
/// * `pushed` - The immediate the instruction before it pushed.
/// * `factory` - Reads which registers it writes.
fn eax_after(
    i: &Instruction,
    value: Option<u64>,
    pushed: Option<u64>,
    factory: &mut InstructionInfoFactory,
) -> (Option<u64>, Option<u64>) {
    if matches!(i.mnemonic(), Mnemonic::Syscall | Mnemonic::Int) {
        return (None, None);
    }
    let push = (i.mnemonic() == Mnemonic::Push)
        .then(|| i.try_immediate(0).ok())
        .flatten();
    let writes = factory.info(i).used_registers().iter().any(|u| {
        u.register().full_register() == Register::RAX
            && matches!(
                u.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            )
    });
    if !writes {
        return (value, push);
    }
    let into_eax = i.op0_kind() == OpKind::Register
        && matches!(i.op0_register(), Register::EAX | Register::RAX);
    let set = match i.mnemonic() {
        Mnemonic::Mov if into_eax => i.try_immediate(1).ok(),
        Mnemonic::Xor
            if into_eax
                && i.op1_kind() == OpKind::Register
                && i.op1_register() == i.op0_register() =>
        {
            Some(0)
        }
        Mnemonic::Pop if into_eax => pushed,
        _ => None,
    };
    (set, push)
}

/// Reads an arm64 syscall site: the `svc #0` at `va` in a discovered
/// block, with the number its block leaves in `x8`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - Its functions.
/// * `va` - The `svc`'s address.
fn svc_site(p: &Program, a: &Analysis, va: u64) -> Option<SyscallSite> {
    let (function, b) = block_of(a, va)?;
    let mut insns = Vec::new();
    let mut at = b.start;
    while at < va {
        let word = p.read_va(at, 4)?;
        insns.push(crate::isa::a64::decode(
            u32::from_le_bytes(word.try_into().ok()?),
            at,
        ));
        at = at.checked_add(4)?;
    }
    let nr = super::a64::constant_in(&insns, 8);
    Some(SyscallSite {
        at: va,
        function,
        gate: Gate::Svc,
        nr,
        name: nr.and_then(|nr| Gate::Svc.name(nr)),
    })
}
