//! Anti-analysis tells that a mnemonic alone cannot name.
//!
//! A bare `cpuid` is a feature probe, a bare `rdtsc` is one read, and a
//! bare `in` is a port read. The labels here say otherwise only when the
//! surrounding instructions show a hypervisor leaf, a subtracted pair of
//! reads, or the `VMware` backdoor. The same pass reports the patterns a
//! single instruction does not hold: a PEB read, a debug-register check,
//! a debugger window, a debug spawn, a scan or patch of `0xCC`, and an
//! illegal opcode after an exception filter.

use super::*;

/// Debugger window titles and classes the known checks look up.
const DEBUGGER_WINDOWS: [&str; 2] = ["OLLYDBG", "WinDbgFrameClass"];

/// The tells in one function, instruction sites first.
///
/// An `int3` that follows a call, a branch, a return or another `int3`
/// (nops aside) is the compiler's trap and is left out.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for calls and imports.
/// * `f` - The function.
/// * `bits` - Decoder bitness.
///
/// # Returns
///
/// Each tell's label and the instruction address that shows it.
pub(super) fn sites(
    p: &Program,
    a: &Analysis,
    f: &Function,
    bits: u32,
) -> Vec<(&'static str, u64)> {
    let instrs = decoded(p, f, bits);
    let mut out = Vec::new();
    let mut after = FlowControl::Next;
    for (at, i) in instrs.iter().enumerate() {
        let trap = i.mnemonic() == Mnemonic::Int3 && after != FlowControl::Next;
        if !trap && let Some(tag) = instruction_tag(&instrs, at) {
            out.push((tag, i.ip()));
        }
        if i.mnemonic() != Mnemonic::Nop {
            after = i.flow_control();
        }
    }
    out.extend(patterns(p, a, f, &instrs, bits));
    out
}

/// The label of one instruction, using the instructions around it.
fn instruction_tag(instrs: &[Instruction], at: usize) -> Option<&'static str> {
    let i = instrs.get(at)?;
    Some(match i.mnemonic() {
        Mnemonic::Rdtsc | Mnemonic::Rdtscp => {
            if rdtsc_timing(instrs) {
                "rdtsc (timing)"
            } else {
                "rdtsc (read)"
            }
        }
        Mnemonic::Cpuid => {
            if cpuid_hypervisor(instrs, at) {
                "cpuid (hypervisor probe)"
            } else {
                "cpuid (feature probe)"
            }
        }
        Mnemonic::Int3 => "int3 (debugger trap)",
        Mnemonic::Int1 => "icebp (debugger trap)",
        Mnemonic::Int if i.immediate8() == 0x2d => "int 2dh (debugger trap)",
        Mnemonic::Sidt | Mnemonic::Sgdt | Mnemonic::Sldt | Mnemonic::Str => {
            "descriptor-table read (VM red pill)"
        }
        Mnemonic::In | Mnemonic::Insb | Mnemonic::Insw | Mnemonic::Insd => {
            if vmware_backdoor(instrs, at) {
                "in (VMware backdoor port)"
            } else {
                "in (port read)"
            }
        }
        _ if debug_register(i) => "hardware breakpoint (debug register)",
        _ => return None,
    })
}

/// Whether two `rdtsc` reads are subtracted and a branch reads that difference.
fn rdtsc_timing(instrs: &[Instruction]) -> bool {
    let mut seen = 0u32;
    let mut second = None;
    for (at, i) in instrs.iter().enumerate() {
        if matches!(i.mnemonic(), Mnemonic::Rdtsc | Mnemonic::Rdtscp) {
            seen += 1;
            if seen == 2 {
                second = Some(at);
            }
        }
    }
    let Some(at) = second else {
        return false;
    };
    let Some(sub) = instrs.iter().skip(at + 1).take(8).position(subtracts_rax) else {
        return false;
    };
    instrs.iter().skip(at + 1 + sub).take(6).any(|n| {
        n.mnemonic() == Mnemonic::Cmp || n.flow_control() == FlowControl::ConditionalBranch
    })
}

/// Whether `n` subtracts from `rax`, where `rdtsc` left its low half.
fn subtracts_rax(n: &Instruction) -> bool {
    n.mnemonic() == Mnemonic::Sub
        && n.op0_kind() == OpKind::Register
        && n.op0_register().full_register() == Register::RAX
}

/// Whether `cpuid` at `at` follows a hypervisor vendor leaf or is followed
/// by a test of the hypervisor bit.
fn cpuid_hypervisor(instrs: &[Instruction], at: usize) -> bool {
    let leaf = instrs[..at]
        .iter()
        .rev()
        .take(6)
        .any(|n| moved_immediate(n, Register::RAX, 0x4000_0000));
    let bit =
        instrs.iter().skip(at + 1).take(8).any(|n| {
            moved_immediate(n, Register::RCX, 0x8000_0000) || tests_immediate(n, 0x8000_0000)
        });
    leaf || bit
}

/// Whether the `in` at `at` is aimed at the `VMware` backdoor.
///
/// The backdoor is port `0x5658`, and the call sets `eax` to `VMXh`
/// (`0x564d5868`) first. A bare `in` has neither.
fn vmware_backdoor(instrs: &[Instruction], at: usize) -> bool {
    instrs[..at].iter().rev().take(6).any(|n| {
        moved_immediate(n, Register::RAX, 0x564d_5868) || moved_immediate(n, Register::RDX, 0x5658)
    })
}

/// Whether `i` moves a debug register.
fn debug_register(i: &Instruction) -> bool {
    let dr = |r: Register| {
        matches!(
            r.full_register(),
            Register::DR0
                | Register::DR1
                | Register::DR2
                | Register::DR3
                | Register::DR6
                | Register::DR7
        )
    };
    (i.op_count() > 0 && i.op0_kind() == OpKind::Register && dr(i.op0_register()))
        || (i.op_count() > 1 && i.op1_kind() == OpKind::Register && dr(i.op1_register()))
}

/// The tells that take more than one instruction.
fn patterns(
    p: &Program,
    a: &Analysis,
    f: &Function,
    instrs: &[Instruction],
    bits: u32,
) -> Vec<(&'static str, u64)> {
    let mut out = Vec::new();
    let Some(ip) = instrs.first().map(Instruction::ip) else {
        return out;
    };
    if let Some(at) = peb_read(instrs) {
        out.push(("peb read (BeingDebugged)", at));
    }
    let called = called_imports(p, a, f.entry);
    let has = |frag: &str| called.iter().any(|n| n.contains(frag));
    if has("getthreadcontext")
        && instrs
            .iter()
            .any(|i| has_immediate(i, 0x1_0010) || has_immediate(i, 0x10_0010))
    {
        out.push(("hardware breakpoint (GetThreadContext)", ip));
    }
    if has("findwindow")
        && (has("postquitmessage") || has("exitprocess") || has("terminateprocess"))
        && debugger_string(p, instrs)
    {
        out.push(("debugger window (FindWindow)", ip));
    }
    if has("createprocess") && (has("waitfordebugevent") || has("continuedebugevent")) {
        out.push(("debug block (DEBUG_PROCESS)", ip));
    }
    let exits = has("exitprocess") || has("terminateprocess");
    let cc = instrs
        .iter()
        .any(|i| compares_byte(i, 0xcc) || compares_byte(i, 0x90));
    let loops = f
        .blocks
        .iter()
        .any(|b| b.successors.iter().any(|s| *s <= b.start));
    if exits && cc && loops {
        out.push(("breakpoint scan", ip));
    } else if cc && writes_executable(p, instrs) {
        out.push(("breakpoint patch", ip));
    }
    if has("setunhandledexceptionfilter")
        && executable_handler(p, instrs)
        && continued_past_bad(p, f, instrs, bits)
    {
        out.push(("illegal opcode (exception filter)", ip));
    }
    out
}

/// Whether the filter argument is an address in executable memory.
///
/// On x86 the argument is pushed. On x64 it is moved into `ecx`. A call
/// that passes something else is not this tell.
fn executable_handler(p: &Program, instrs: &[Instruction]) -> bool {
    instrs.iter().any(|i| {
        let Some(imm) = immediate_any(i) else {
            return false;
        };
        if !p.section_at(imm).is_some_and(|s| s.executable) {
            return false;
        }
        i.mnemonic() == Mnemonic::Push
            || (i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && i.op0_register().full_register() == Register::RCX)
    })
}

/// Whether the function keeps going after an instruction that does not decode.
///
/// The bytes sit between two instructions the walk kept. A filter call that
/// returns, with nothing undecodable after it, does not.
fn continued_past_bad(p: &Program, f: &Function, instrs: &[Instruction], bits: u32) -> bool {
    let starts: BTreeSet<u64> = f.blocks.iter().map(|b| b.start).collect();
    instrs.iter().any(|i| {
        let gap = i.next_ip();
        gap != i.ip()
            && !starts.contains(&gap)
            && f.blocks.iter().any(|b| b.start > gap)
            && decodes_invalid(p, bits, gap)
    })
}

/// Reports whether the bytes at `at` are not an instruction.
fn decodes_invalid(p: &Program, bits: u32, at: u64) -> bool {
    let Some(code) = p.read_va(at, 16) else {
        return false;
    };
    let mut decoder = Decoder::with_ip(bits, code, at, DecoderOptions::NONE);
    decoder.can_decode() && decoder.decode().is_invalid()
}

/// The address of a PEB read, when the instructions perform one.
///
/// `fs:[0x30]` and `gs:[0x60]` are the PEB. `fs:[0x18]` and `gs:[0x30]` are
/// the TEB's self pointer, and count only when a following use indexes the
/// PEB (`0x30` or `0x60`). A read of the stack base at `+4` or `+8` does not.
fn peb_read(instrs: &[Instruction]) -> Option<u64> {
    for (at, i) in instrs.iter().enumerate() {
        let Some((seg, disp, base)) = memory(i) else {
            continue;
        };
        let direct = (seg == Register::FS && disp == 0x30) || (seg == Register::GS && disp == 0x60);
        let teb = (seg == Register::FS && disp == 0x18) || (seg == Register::GS && disp == 0x30);
        if direct {
            return Some(i.ip());
        }
        if teb && base == Register::None {
            let indexed = instrs.iter().skip(at + 1).take(4).any(|n| {
                memory(n).is_some_and(|(_, d, b)| b != Register::None && matches!(d, 0x30 | 0x60))
            });
            if indexed {
                return Some(i.ip());
            }
        }
    }
    None
}

/// The bare import names this function calls, in lower case.
fn called_imports(p: &Program, a: &Analysis, entry: u64) -> Vec<String> {
    let mut names = Vec::new();
    for (target, _) in a.refs_from(entry) {
        let slot = a.function(target).and_then(|g| g.thunk).unwrap_or(target);
        let Some(sym) = p
            .symbols
            .iter()
            .find(|s| s.addr == slot && matches!(s.kind, SymbolKind::Import))
        else {
            continue;
        };
        names.push(bare_name(&sym.name).to_lowercase());
    }
    names
}

/// Whether a pushed or moved immediate names a known debugger window.
fn debugger_string(p: &Program, instrs: &[Instruction]) -> bool {
    instrs.iter().any(|i| {
        immediate_any(i).is_some_and(|imm| {
            imm != 0
                && cstr_at(p, imm, 4, 64)
                    .is_some_and(|(_, s)| DEBUGGER_WINDOWS.iter().any(|w| s.contains(w)))
        })
    })
}

/// Whether a compare of `0xCC` is followed by a store into executable memory.
fn writes_executable(p: &Program, instrs: &[Instruction]) -> bool {
    let Some(at) = instrs.iter().position(|i| compares_byte(i, 0xcc)) else {
        return false;
    };
    instrs.iter().skip(at + 1).any(|i| {
        i.mnemonic() == Mnemonic::Mov
            && i.op0_kind() == OpKind::Memory
            && p.section_at(i.memory_displacement64())
                .is_some_and(|s| s.executable)
    })
}

/// The instructions of `f`, in address order.
fn decoded(p: &Program, f: &Function, bits: u32) -> Vec<Instruction> {
    let mut instrs = Vec::new();
    for b in &f.blocks {
        let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
        let Some(code) = p.read_va(b.start, len) else {
            continue;
        };
        let mut d = Decoder::with_ip(bits, code, b.start, DecoderOptions::NONE);
        while d.can_decode() {
            let i = d.decode();
            if i.is_invalid() || i.ip() >= b.end {
                break;
            }
            instrs.push(i);
        }
    }
    instrs
}

/// The segment, displacement and base of `i`'s memory operand.
fn memory(i: &Instruction) -> Option<(Register, u64, Register)> {
    let mem = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory);
    mem.then_some((
        i.segment_prefix(),
        i.memory_displacement64(),
        i.memory_base(),
    ))
}

/// Whether `i` moves `imm` into `reg`.
fn moved_immediate(i: &Instruction, reg: Register, imm: u64) -> bool {
    i.mnemonic() == Mnemonic::Mov
        && i.op0_kind() == OpKind::Register
        && i.op0_register().full_register() == reg
        && has_immediate(i, imm)
}

/// Whether `i` tests or compares against `imm`.
fn tests_immediate(i: &Instruction, imm: u64) -> bool {
    matches!(i.mnemonic(), Mnemonic::Test | Mnemonic::Cmp | Mnemonic::Bt) && has_immediate(i, imm)
}

/// Whether `i` compares a byte with `imm`.
fn compares_byte(i: &Instruction, imm: u64) -> bool {
    matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test) && has_immediate(i, imm)
}

/// Whether one of `i`'s immediates is `imm`.
fn has_immediate(i: &Instruction, imm: u64) -> bool {
    immediate_any(i).is_some_and(|v| v == imm)
}

/// The first immediate operand of `i`.
fn immediate_any(i: &Instruction) -> Option<u64> {
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
