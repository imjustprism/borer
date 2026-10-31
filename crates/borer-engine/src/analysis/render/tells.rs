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
    let timing = rdtsc_timing(&instrs);
    let mut out = Vec::new();
    let mut after = FlowControl::Next;
    for (at, i) in instrs.iter().enumerate() {
        let trap = i.mnemonic() == Mnemonic::Int3 && after != FlowControl::Next;
        if !trap && let Some(tag) = instruction_tag(&instrs, at, timing) {
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
///
/// # Arguments
///
/// * `instrs` - The function's instructions.
/// * `at` - The instruction's index.
/// * `timing` - Two timestamp reads are subtracted and a check reads that.
fn instruction_tag(instrs: &[Instruction], at: usize, timing: bool) -> Option<&'static str> {
    let i = instrs.get(at)?;
    Some(match i.mnemonic() {
        Mnemonic::Rdtsc | Mnemonic::Rdtscp => {
            if timing {
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

/// Consecutive timestamp pairs one function is searched for.
const TIMESTAMP_PAIRS: usize = 8;

/// Whether two timestamp reads are subtracted and a later check reads that
/// difference.
///
/// The subtraction has to use the earlier read, or a register it was copied
/// into. A write of that register after the second read and before the
/// subtraction drops it. `sub eax, eax` clears the register, and a compare
/// of some other register is not that check. An earlier read that nothing
/// saves does not hide a later pair. At most [`TIMESTAMP_PAIRS`] pairs are
/// checked.
fn rdtsc_timing(instrs: &[Instruction]) -> bool {
    let mut reads = [0usize; TIMESTAMP_PAIRS + 1];
    let mut count = 0usize;
    for (at, i) in instrs.iter().enumerate() {
        if !matches!(i.mnemonic(), Mnemonic::Rdtsc | Mnemonic::Rdtscp) {
            continue;
        }
        if count == reads.len() {
            break;
        }
        reads[count] = at;
        count += 1;
    }
    reads[..count].windows(2).any(|pair| {
        let (earlier, later) = (pair[0], pair[1]);
        let mut saved = saved_timestamp(&instrs[earlier + 1..later], instrs[later].mnemonic());
        let mut live = saved.iter().take_while(|r| **r != Register::None).count();
        let mut gap = None;
        for (offset, n) in instrs.iter().skip(later + 1).take(8).enumerate() {
            if timestamp_difference(n, &saved) {
                gap = Some(offset);
                break;
            }
            drop_timestamp(n, &mut saved, &mut live);
        }
        let Some(gap) = gap else {
            return false;
        };
        difference_checked(instrs, later + 1 + gap)
    })
}

/// Registers still holding the first timestamp when the second read runs.
///
/// The second read replaces `rax` and `rdx`. `rdtscp` also replaces `rcx`.
///
/// # Arguments
///
/// * `between` - Instructions after the first read and before the second.
/// * `second` - The second read's mnemonic.
fn saved_timestamp(between: &[Instruction], second: Mnemonic) -> [Register; 6] {
    let mut held = [Register::None; 6];
    held[0] = Register::RAX;
    held[1] = Register::RDX;
    let mut count = 2usize;
    for n in between {
        if let Some(dest) = copied_timestamp(n, &held[..count]) {
            if count < held.len() && !held[..count].contains(&dest) {
                held[count] = dest;
                count += 1;
            }
            continue;
        }
        drop_timestamp(n, &mut held, &mut count);
    }
    drop_one(&mut held, &mut count, Register::RAX);
    drop_one(&mut held, &mut count, Register::RDX);
    if second == Mnemonic::Rdtscp {
        drop_one(&mut held, &mut count, Register::RCX);
    }
    held
}

/// The full register a full-width `mov` copies out of `held`.
fn copied_timestamp(n: &Instruction, held: &[Register]) -> Option<Register> {
    if n.mnemonic() != Mnemonic::Mov
        || n.op_count() != 2
        || n.op0_kind() != OpKind::Register
        || n.op1_kind() != OpKind::Register
        || n.op0_register().size() < 4
        || !held.contains(&n.op1_register().full_register())
    {
        return None;
    }
    Some(n.op0_register().full_register())
}

/// Drops a timestamp register `n` writes, other than a compare.
fn drop_timestamp(n: &Instruction, held: &mut [Register], count: &mut usize) {
    if n.op0_kind() != OpKind::Register || matches!(n.mnemonic(), Mnemonic::Cmp | Mnemonic::Test) {
        return;
    }
    drop_one(held, count, n.op0_register().full_register());
}

/// Removes `reg` from the live prefix of `held`.
fn drop_one(held: &mut [Register], count: &mut usize, reg: Register) {
    let Some(at) = held[..*count].iter().position(|r| *r == reg) else {
        return;
    };
    held[at] = held[*count - 1];
    held[*count - 1] = Register::None;
    *count -= 1;
}

/// Whether `n` subtracts a saved timestamp from the new `rax` read, or the
/// new read from a saved one. `sub eax, eax` does neither.
fn timestamp_difference(n: &Instruction, saved: &[Register]) -> bool {
    if n.mnemonic() != Mnemonic::Sub
        || n.op0_kind() != OpKind::Register
        || n.op1_kind() != OpKind::Register
    {
        return false;
    }
    let dest = n.op0_register().full_register();
    let src = n.op1_register().full_register();
    if src == dest {
        return false;
    }
    let live = |r: Register| r != Register::None && saved.contains(&r);
    (dest == Register::RAX && live(src)) || (src == Register::RAX && live(dest))
}

/// Whether a later compare reads the difference, or a branch reads the
/// flags the subtraction wrote.
///
/// A full-width copy of the difference is still that value. A later write
/// drops only the register it writes.
fn difference_checked(instrs: &[Instruction], at: usize) -> bool {
    let Some(sub) = instrs.get(at) else {
        return false;
    };
    let mut held = [Register::None; 4];
    held[0] = sub.op0_register().full_register();
    let mut count = 1usize;
    let mut flags = sub.rflags_modified();
    for n in instrs.iter().skip(at + 1).take(6) {
        let reads = (0..n.op_count()).any(|k| {
            n.op_kind(k) == OpKind::Register
                && held[..count].contains(&n.op_register(k).full_register())
        });
        if matches!(n.mnemonic(), Mnemonic::Cmp | Mnemonic::Test) && reads {
            return true;
        }
        if n.flow_control() == FlowControl::ConditionalBranch && n.rflags_read() & flags != 0 {
            return true;
        }
        flags &= !n.rflags_modified();
        if let Some(dest) = copied_timestamp(n, &held[..count]) {
            if count < held.len() && !held[..count].contains(&dest) {
                held[count] = dest;
                count += 1;
            }
            continue;
        }
        drop_timestamp(n, &mut held, &mut count);
    }
    false
}

/// Whether `cpuid` at `at` runs the hypervisor vendor leaf or is followed
/// by a test of the hypervisor bit in `ecx`.
///
/// The leaf is the last write of `rax` before the instruction. A constant
/// an earlier `mov` left, and that a later `mov` replaced, is not the leaf.
/// A test of some other register is not the hypervisor bit. A write of
/// `ecx` before the test, or a call, replaces that bit.
fn cpuid_hypervisor(instrs: &[Instruction], at: usize) -> bool {
    hypervisor_leaf(instrs, at) || hypervisor_bit(instrs, at)
}

/// Whether the last write of `rax` before `instrs[at]` is the vendor leaf.
fn hypervisor_leaf(instrs: &[Instruction], at: usize) -> bool {
    instrs[..at]
        .iter()
        .rev()
        .take(6)
        .find(|n| writes_register(n, Register::RAX))
        .is_some_and(|n| moved_immediate(n, Register::RAX, 0x4000_0000))
}

/// Whether a later instruction tests the hypervisor bit in `ecx`.
///
/// A write of `ecx`, or a call, replaces the `cpuid` result. A test after
/// that reads the new value.
fn hypervisor_bit(instrs: &[Instruction], at: usize) -> bool {
    for n in instrs.iter().skip(at + 1).take(8) {
        if tests_register(n, Register::RCX, 0x8000_0000) {
            return true;
        }
        if writes_register(n, Register::RCX)
            || matches!(
                n.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            )
        {
            return false;
        }
    }
    false
}

/// Whether `i` writes `reg`, other than a compare that only reads it.
fn writes_register(i: &Instruction, reg: Register) -> bool {
    i.op0_kind() == OpKind::Register
        && i.op0_register().full_register() == reg
        && !matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Bt)
}

/// Whether `i` tests or compares `reg` against `imm`.
fn tests_register(i: &Instruction, reg: Register, imm: u64) -> bool {
    tests_immediate(i, imm)
        && (0..i.op_count())
            .any(|k| i.op_kind(k) == OpKind::Register && i.op_register(k).full_register() == reg)
}

/// Whether the `in` at `at` is aimed at the `VMware` backdoor.
///
/// The backdoor is port `0x5658`, or the call sets `eax` to `VMXh`
/// (`0x564d5868`). A later write of that register replaces the value.
/// A bare `in` has neither.
fn vmware_backdoor(instrs: &[Instruction], at: usize) -> bool {
    let mut magic = false;
    let mut port = false;
    let mut saw_rax = false;
    let mut saw_rdx = false;
    for n in instrs[..at].iter().rev().take(6) {
        if !saw_rax && writes_register(n, Register::RAX) {
            saw_rax = true;
            magic = moved_immediate(n, Register::RAX, 0x564d_5868);
        }
        if !saw_rdx && writes_register(n, Register::RDX) {
            saw_rdx = true;
            port = moved_immediate(n, Register::RDX, 0x5658);
        }
    }
    magic || port
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
    if !matches!(p.format, BinaryFormat::Elf | BinaryFormat::MachO)
        && let Some((at, label)) = peb_read(instrs)
    {
        out.push((label, at));
    }
    let called = called_imports(p, a, f.entry);
    let has = |frag: &str| called.iter().any(|n| n.contains(frag));
    if context_debug(p, a, f.entry, instrs, bits) {
        out.push(("hardware breakpoint (GetThreadContext)", ip));
    }
    if has("findwindow")
        && (has("postquitmessage") || has("exitprocess") || has("terminateprocess"))
        && debugger_string(p, instrs)
    {
        out.push(("debugger window (FindWindow)", ip));
    }
    if (has("waitfordebugevent") || has("continuedebugevent"))
        && debug_spawn(p, a, f.entry, instrs, bits)
    {
        out.push(("debug block (DEBUG_PROCESS)", ip));
    }
    if has("ntqueryinformationprocess") && debug_port(p, a, f.entry, instrs, bits) {
        out.push(("debug port (NtQueryInformationProcess)", ip));
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
    if illegal_filter(p, a, f, instrs, bits) {
        out.push(("illegal opcode (exception filter)", ip));
    }
    out
}

/// Whether a `CreateProcess` call passes a debug creation flag.
///
/// The flags are the sixth argument. `DEBUG_PROCESS` and
/// `DEBUG_ONLY_THIS_PROCESS` are the low two bits. An ordinary helper,
/// or `CREATE_SUSPENDED` alone, is not this tell.
fn debug_spawn(p: &Program, a: &Analysis, entry: u64, instrs: &[Instruction], bits: u32) -> bool {
    for (target, site) in a.refs_from(entry) {
        if site.kind != RefKind::Call {
            continue;
        }
        let slot = a.function(target).and_then(|g| g.thunk).unwrap_or(target);
        let Some(sym) = a
            .symbol_at(p, slot)
            .filter(|s| s.kind == SymbolKind::Import)
        else {
            continue;
        };
        let name = bare_name(&sym.name).to_ascii_lowercase();
        if !matches!(
            name.as_str(),
            "createprocess" | "createprocessa" | "createprocessw"
        ) {
            continue;
        }
        let Some(at) = instrs.iter().position(|i| i.ip() == site.va) else {
            continue;
        };
        if creation_flags(&instrs[..at], bits) {
            return true;
        }
    }
    false
}

/// Whether the sixth argument passed before this call is a debug flag.
fn creation_flags(before: &[Instruction], bits: u32) -> bool {
    let disp = if bits == 32 { 0x14 } else { 0x28 };
    if bits == 32 && pushed_immediate(before, 6).is_some_and(debug_creation) {
        return true;
    }
    for n in before.iter().rev().take(16) {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            return false;
        }
        if stack_immediate(n, disp, bits).is_some_and(debug_creation) {
            return true;
        }
    }
    false
}

/// Whether `imm` includes `DEBUG_PROCESS` or `DEBUG_ONLY_THIS_PROCESS`.
fn debug_creation(imm: u64) -> bool {
    (imm & 3) != 0
}

/// The `nth` immediate `push` before the call, counting from the call.
fn pushed_immediate(before: &[Instruction], nth: u32) -> Option<u64> {
    let mut seen = 0u32;
    for i in before.iter().rev().take(24) {
        if matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            return None;
        }
        if i.mnemonic() != Mnemonic::Push {
            continue;
        }
        seen += 1;
        if seen == nth {
            return immediate_any(i);
        }
    }
    None
}

/// The immediate stored at `[rsp+disp]` or `[esp+disp]`.
fn stack_immediate(n: &Instruction, disp: u64, bits: u32) -> Option<u64> {
    if n.mnemonic() != Mnemonic::Mov || n.op0_kind() != OpKind::Memory {
        return None;
    }
    let width = if bits == 32 { 4 } else { 8 };
    if n.memory_base().full_register() != Register::RSP
        || n.memory_base().size() != width
        || n.memory_index() != Register::None
        || n.memory_displacement64() != disp
        || !matches!(n.segment_prefix(), Register::None | Register::SS)
    {
        return None;
    }
    immediate_any(n)
}

/// Whether the `NtQueryInformationProcess` call passes `ProcessDebugPort`.
///
/// On x64 the class is `edx`. On x86 it is the second push. The `7` has to
/// belong to that call. The same immediate passed to another call is not
/// this tell, and neither is `ProcessBasicInformation` (`0`).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the call's target.
/// * `entry` - The function the calls sit in.
/// * `instrs` - The function, in address order.
/// * `bits` - Decoder bitness, which picks the class operand.
fn debug_port(p: &Program, a: &Analysis, entry: u64, instrs: &[Instruction], bits: u32) -> bool {
    let sites = import_sites(p, a, entry, "ntqueryinformationprocess");
    if sites.is_empty() {
        return false;
    }
    instrs.iter().enumerate().any(|(at, i)| {
        matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) && sites.contains(&i.ip())
            && class_is_debug_port(&instrs[..at], bits)
    })
}

/// Instruction addresses that call an import whose name contains `stem`.
fn import_sites(p: &Program, a: &Analysis, entry: u64, stem: &str) -> Vec<u64> {
    let mut sites = Vec::new();
    for (target, site) in a.refs_from(entry) {
        if site.kind != RefKind::Call {
            continue;
        }
        let slot = a.function(target).and_then(|g| g.thunk).unwrap_or(target);
        let Some(sym) = a
            .symbol_at(p, slot)
            .filter(|s| s.kind == SymbolKind::Import)
        else {
            continue;
        };
        if bare_name(&sym.name).to_lowercase().contains(stem) {
            sites.push(site.va);
        }
    }
    sites
}

/// Whether the call `before` leads to passes `ProcessDebugPort`.
fn class_is_debug_port(before: &[Instruction], bits: u32) -> bool {
    if bits == 32 {
        pushed_class(before) == Some(7)
    } else {
        edx_class(before) == Some(7)
    }
}

/// The information class in `edx`, when moves of immediates set it.
///
/// A compare does not write the register. A later write of `dl` or `dh`
/// replaces only that byte, so `mov edx, 0x100; mov dl, 7` is `0x107`,
/// not `7`.
fn edx_class(before: &[Instruction]) -> Option<u64> {
    let mut part: Option<(u64, u64)> = None;
    for n in before.iter().rev().take(8) {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            return None;
        }
        if !writes_register(n, Register::RDX) {
            continue;
        }
        if n.mnemonic() != Mnemonic::Mov {
            return None;
        }
        let imm = immediate_any(n)?;
        let (mask, shift) = rdx_field(n.op0_register())?;
        if mask >= 0xffff_ffff {
            let full = imm & 0xffff_ffff;
            let class = match part {
                Some((value, keep)) => (full & !keep) | value,
                None => full,
            };
            return Some(class);
        }
        let bits = (imm << shift) & mask;
        part = Some(match part {
            Some((value, keep)) => (value | (bits & !keep), keep | mask),
            None => (bits, mask),
        });
    }
    None
}

/// The bits of `edx` that `reg` writes, and the shift of that immediate.
fn rdx_field(reg: Register) -> Option<(u64, u32)> {
    match reg {
        Register::DL => Some((0xff, 0)),
        Register::DH => Some((0xff00, 8)),
        Register::DX => Some((0xffff, 0)),
        Register::EDX | Register::RDX => Some((0xffff_ffff, 0)),
        _ => None,
    }
}

/// The second `push` before the call, which is the class on x86.
fn pushed_class(before: &[Instruction]) -> Option<u64> {
    let mut seen = 0u32;
    for i in before.iter().rev().take(12) {
        if matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            break;
        }
        if i.mnemonic() != Mnemonic::Push {
            continue;
        }
        seen += 1;
        if seen == 2 {
            return immediate_any(i);
        }
    }
    None
}

/// Whether `SetUnhandledExceptionFilter` is given code and then runs into
/// bytes that do not decode.
///
/// The code address has to be that call's argument. Undecodable bytes
/// before the call, or a code address passed to another call, are not
/// this tell.
fn illegal_filter(
    p: &Program,
    a: &Analysis,
    f: &Function,
    instrs: &[Instruction],
    bits: u32,
) -> bool {
    import_sites(p, a, f.entry, "setunhandledexceptionfilter")
        .iter()
        .any(|site| {
            let Some(at) = instrs.iter().position(|i| i.ip() == *site) else {
                return false;
            };
            executable_handler(p, &instrs[..at], bits)
                && continued_past_bad(p, f, &instrs[at..], bits)
        })
}

/// Whether the filter argument is an address in executable memory.
///
/// On x86 the argument is pushed. On x64 it is moved into `ecx`. A call
/// that passes something else is not this tell.
fn executable_handler(p: &Program, before: &[Instruction], bits: u32) -> bool {
    let imm = if bits == 32 {
        pushed_handler(before)
    } else {
        rcx_handler(before)
    };
    imm.is_some_and(|addr| p.section_at(addr).is_some_and(|s| s.executable))
}

/// The immediate in `ecx`, when the last write of it is a `mov`.
fn rcx_handler(before: &[Instruction]) -> Option<u64> {
    for n in before.iter().rev().take(8) {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            return None;
        }
        if n.op0_kind() != OpKind::Register || n.op0_register().full_register() != Register::RCX {
            continue;
        }
        if n.mnemonic() == Mnemonic::Mov {
            return immediate_any(n);
        }
        return None;
    }
    None
}

/// The immediate pushed as the filter, when that push is the argument.
fn pushed_handler(before: &[Instruction]) -> Option<u64> {
    for n in before.iter().rev().take(8) {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            return None;
        }
        if n.mnemonic() == Mnemonic::Push {
            return immediate_any(n);
        }
    }
    None
}

/// Whether the instructions keep going after bytes that do not decode.
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

/// The address and label of a PEB read, when the instructions perform one.
///
/// `fs:[0x30]` and `gs:[0x60]` are the PEB. `fs:[0x18]` and `gs:[0x30]` are
/// the TEB's self pointer, and count only when a following use indexes the
/// PEB (`0x30` or `0x60`). A read of the stack base at `+4` or `+8` does not.
/// The label names the field a later read shows.
fn peb_read(instrs: &[Instruction]) -> Option<(u64, &'static str)> {
    for (at, i) in instrs.iter().enumerate() {
        let Some((seg, disp, base)) = memory(i) else {
            continue;
        };
        let direct = (seg == Register::FS && disp == 0x30) || (seg == Register::GS && disp == 0x60);
        let teb = (seg == Register::FS && disp == 0x18) || (seg == Register::GS && disp == 0x30);
        if direct {
            return Some((i.ip(), peb_field(&instrs[at + 1..], pointer_dest(i))));
        }
        if teb && base == Register::None {
            let indexed = instrs.iter().skip(at + 1).take(4).any(|n| {
                memory(n).is_some_and(|(_, d, b)| b != Register::None && matches!(d, 0x30 | 0x60))
            });
            if indexed {
                return Some((i.ip(), peb_field(&instrs[at + 1..], pointer_dest(i))));
            }
        }
    }
    None
}

/// Names the PEB field a later read uses.
///
/// A byte at displacement 2 is `BeingDebugged`. A read at `0x68` or `0xBC`
/// is `NtGlobalFlag`. The base has to be `origin` or a copy of it. A store
/// and an `Ldr` walk stay a plain PEB read.
fn peb_field(rest: &[Instruction], origin: Register) -> &'static str {
    let mut held = [Register::None; 4];
    let mut count = 0usize;
    if origin != Register::None {
        held[0] = origin;
        count = 1;
    }
    for n in rest.iter().take(4) {
        if let Some(label) = peb_field_read(n, &held[..count]) {
            return label;
        }
        if let Some(dest) = copied_timestamp(n, &held[..count]) {
            if count < held.len() && !held[..count].contains(&dest) {
                held[count] = dest;
                count += 1;
            }
            continue;
        }
        if let Some(dest) = peb_pointer(n, &held[..count]) {
            if count < held.len() && !held[..count].contains(&dest) {
                held[count] = dest;
                count += 1;
            }
            continue;
        }
        drop_timestamp(n, &mut held, &mut count);
    }
    "peb read"
}

/// The register a PEB or TEB read writes.
fn pointer_dest(i: &Instruction) -> Register {
    if i.op0_kind() == OpKind::Register {
        i.op0_register().full_register()
    } else {
        Register::None
    }
}

/// The field `n` reads through one of `held`.
///
/// A store writes that slot instead of reading it, so it is not a field.
fn peb_field_read(n: &Instruction, held: &[Register]) -> Option<&'static str> {
    if held.is_empty()
        || n.mnemonic() == Mnemonic::Lea
        || (n.mnemonic() == Mnemonic::Mov && n.op0_kind() == OpKind::Memory)
    {
        return None;
    }
    let (_, disp, base) = memory(n)?;
    let base = base.full_register();
    if base == Register::None || !held.contains(&base) {
        return None;
    }
    if disp == 2 && n.memory_size().size() == 1 {
        return Some("peb read (BeingDebugged)");
    }
    if matches!(disp, 0x68 | 0xbc) {
        return Some("peb read (NtGlobalFlag)");
    }
    None
}

/// The register a load of the PEB pointer from the TEB writes.
fn peb_pointer(n: &Instruction, held: &[Register]) -> Option<Register> {
    if n.op0_kind() != OpKind::Register || held.is_empty() {
        return None;
    }
    let (_, disp, base) = memory(n)?;
    if !matches!(disp, 0x30 | 0x60) || !held.contains(&base.full_register()) {
        return None;
    }
    Some(n.op0_register().full_register())
}

/// The bare import names this function calls, in lower case.
///
/// A load or an `lea` of the import's address is not a call.
fn called_imports(p: &Program, a: &Analysis, entry: u64) -> Vec<String> {
    let mut names = Vec::new();
    for (target, site) in a.refs_from(entry) {
        if site.kind != RefKind::Call {
            continue;
        }
        let slot = a.function(target).and_then(|g| g.thunk).unwrap_or(target);
        let Some(sym) = a
            .symbol_at(p, slot)
            .filter(|s| s.kind == SymbolKind::Import)
        else {
            continue;
        };
        names.push(bare_name(&sym.name).to_lowercase());
    }
    names
}

/// Whether a pushed, moved, or RIP-relative address names a debugger window.
///
/// `FindWindowA` passes ASCII. `FindWindowW` passes UTF-16. The address
/// may be an immediate or `lea reg, [rip+name]`. A one-character narrow
/// reading of a wide string does not count.
fn debugger_string(p: &Program, instrs: &[Instruction]) -> bool {
    instrs
        .iter()
        .any(|i| string_address(i).is_some_and(|va| va != 0 && debugger_name(p, va)))
}

/// An immediate, or the target of a RIP-relative `lea`, that may name a window.
fn string_address(i: &Instruction) -> Option<u64> {
    if let Some(imm) = immediate_any(i) {
        return Some(imm);
    }
    (i.mnemonic() == Mnemonic::Lea && i.is_ip_rel_memory_operand())
        .then_some(i.ip_rel_memory_address())
}

/// Whether the ASCII or UTF-16 run at `va` is a known debugger window.
fn debugger_name(p: &Program, va: u64) -> bool {
    let named = |text: &str| DEBUGGER_WINDOWS.iter().any(|w| text.contains(w));
    cstr_at(p, va, 4, 64).is_some_and(|(_, text)| named(&text))
        || wstr_at(p, va, 4, 64).is_some_and(|(_, text)| named(&text))
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
///
/// A wider compare, such as `cmp eax, 0x90`, is a counter. It is not a
/// scan for an `int3` or a `nop`.
fn compares_byte(i: &Instruction, imm: u64) -> bool {
    if !matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test) || !has_immediate(i, imm) {
        return false;
    }
    match i.op0_kind() {
        OpKind::Register => i.op0_register().size() == 1,
        OpKind::Memory => i.memory_size().size() == 1,
        _ => false,
    }
}

/// Whether one of `i`'s immediates is `imm`.
fn has_immediate(i: &Instruction, imm: u64) -> bool {
    immediate_any(i).is_some_and(|v| v == imm)
}

/// Whether a context call asks for the debug registers or reads them back
/// from the buffer it was given.
///
/// `CONTEXT_ALL` includes `CONTEXT_DEBUG_REGISTERS`. `CONTEXT_CONTROL` and
/// `CONTEXT_INTEGER` do not. A later load of `Dr0` through `Dr7` counts
/// when its base is the pointer passed to that call, or the stack slot that
/// pointer was loaded from. A load through another register is not the
/// buffer, and neither is a buffer passed to a different call. The call may
/// be direct or indirect.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis, for the call's target.
/// * `entry` - The function the calls sit in.
/// * `instrs` - The function, in address order.
/// * `bits` - Decoder bitness, which picks the `CONTEXT` offsets.
fn context_debug(p: &Program, a: &Analysis, entry: u64, instrs: &[Instruction], bits: u32) -> bool {
    let mut sites = import_sites(p, a, entry, "getthreadcontext");
    for site in import_sites(p, a, entry, "getcontextthread") {
        if !sites.contains(&site) {
            sites.push(site);
        }
    }
    if sites.is_empty() {
        return false;
    }
    instrs.iter().enumerate().any(|(at, i)| {
        matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) && sites.contains(&i.ip())
            && (context_flags(&instrs[..at])
                || reads_context_dr(&instrs[..at], &instrs[at + 1..], bits))
    })
}

/// Whether the instructions before a context call ask for the debug registers.
///
/// The word has to be moved. A compare that happens to hold it is not a
/// request, and the same flags passed to an earlier call do not count.
fn context_flags(before: &[Instruction]) -> bool {
    for n in before.iter().rev().take(8) {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            return false;
        }
        if n.mnemonic() == Mnemonic::Mov && immediate_any(n).is_some_and(debug_context_flags) {
            return true;
        }
    }
    false
}

/// Whether a load after the call reads a debug-register slot of the
/// context pointer set up before it.
///
/// # Arguments
///
/// * `before` - Instructions before the call.
/// * `after` - Instructions after the call.
/// * `bits` - Decoder bitness, which picks the `CONTEXT` offsets.
fn reads_context_dr(before: &[Instruction], after: &[Instruction], bits: u32) -> bool {
    let ptr = context_ptr(before, bits);
    after.iter().take(8).any(|n| dr_from_ptr(n, bits, ptr))
}

/// The callee-saved register holding the context pointer, and the frame
/// slot it was loaded from.
///
/// On x64 the pointer is `rdx`. On x86 it is the second push. A register
/// the call clobbers is not returned: the load has to use a copy that
/// survives, or the frame slot itself.
///
/// # Arguments
///
/// * `before` - Instructions before the call.
/// * `bits` - Decoder bitness.
///
/// # Returns
///
/// The surviving register (`Register::None` when there is none) and the
/// frame slot, when the pointer was addressed that way.
fn context_ptr(before: &[Instruction], bits: u32) -> (Register, Option<(Register, u64)>) {
    if bits == 32 {
        return (pushed_context(before), None);
    }
    let mut reg = Register::None;
    let mut slot = None;
    for n in before.iter().rev().take(8) {
        if n.op0_kind() != OpKind::Register || n.op0_register().full_register() != Register::RDX {
            continue;
        }
        if n.mnemonic() == Mnemonic::Lea {
            slot = frame_slot(n);
        } else if n.mnemonic() == Mnemonic::Mov && n.op1_kind() == OpKind::Register {
            let src = n.op1_register().full_register();
            if kept(src) {
                reg = src;
            }
            if let Some(lea) = lea_of(before, src) {
                slot = frame_slot(lea);
            }
        }
        break;
    }
    (reg, slot)
}

/// The register pushed as the context pointer, when the call keeps it.
fn pushed_context(before: &[Instruction]) -> Register {
    let mut seen = 0u32;
    for n in before.iter().rev().take(8) {
        if matches!(
            n.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            break;
        }
        if n.mnemonic() != Mnemonic::Push {
            continue;
        }
        seen += 1;
        if seen == 2 {
            if n.op0_kind() == OpKind::Register {
                let src = n.op0_register().full_register();
                if kept(src) {
                    return src;
                }
            }
            break;
        }
    }
    Register::None
}

/// The last `lea` that writes `reg`.
fn lea_of(instrs: &[Instruction], reg: Register) -> Option<&Instruction> {
    instrs.iter().rev().find(|n| {
        n.mnemonic() == Mnemonic::Lea
            && n.op0_kind() == OpKind::Register
            && n.op0_register().full_register() == reg
    })
}

/// The frame register and displacement of an `lea` of a stack slot.
fn frame_slot(n: &Instruction) -> Option<(Register, u64)> {
    let (seg, disp, base) = memory(n)?;
    if seg != Register::None && seg != Register::DS {
        return None;
    }
    let frame = base.full_register();
    matches!(frame, Register::RSP | Register::RBP).then_some((frame, disp))
}

/// Whether `reg` still holds its value after a call.
fn kept(reg: Register) -> bool {
    matches!(
        reg,
        Register::RBX
            | Register::RSI
            | Register::RDI
            | Register::R12
            | Register::R13
            | Register::R14
            | Register::R15
    )
}

/// Whether `imm` is an architecture context-flags word that includes the
/// debug registers.
fn debug_context_flags(imm: u64) -> bool {
    let feature = 0x3f;
    let debug = 0x10;
    let arch = |bit: u64| {
        let rest = imm & !bit;
        imm & bit == bit && rest & !feature == 0 && rest & debug == debug
    };
    arch(0x1_0000) || arch(0x10_0000)
}

/// Whether `i` loads a debug-register slot of `ptr`.
///
/// `ptr` is the surviving register and the frame slot from
/// [`context_ptr`]. A store does not count. A stack base counts only when
/// it is that slot.
///
/// # Arguments
///
/// * `i` - One instruction after the context call.
/// * `bits` - `32` uses the x86 `Dr` offsets; anything else the x64 ones.
/// * `ptr` - The context pointer the call was given.
fn dr_from_ptr(i: &Instruction, bits: u32, ptr: (Register, Option<(Register, u64)>)) -> bool {
    if i.mnemonic() == Mnemonic::Lea
        || (i.mnemonic() == Mnemonic::Mov && i.op0_kind() == OpKind::Memory)
    {
        return false;
    }
    let Some((_, disp, base)) = memory(i) else {
        return false;
    };
    let base = base.full_register();
    if base == Register::None {
        return false;
    }
    let size = i.memory_size().size();
    let field = |d: u64| {
        if bits == 32 {
            size == 4 && matches!(d, 4 | 8 | 0xc | 0x10 | 0x14 | 0x18)
        } else {
            size == 8 && matches!(d, 0x48 | 0x50 | 0x58 | 0x60 | 0x68 | 0x70)
        }
    };
    let (reg, slot) = ptr;
    if reg != Register::None && base == reg && field(disp) {
        return true;
    }
    slot.is_some_and(|(frame, at)| base == frame && field(disp.wrapping_sub(at)))
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
