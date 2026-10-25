//! Recognizers for the runtime's own helpers by their bytes and calls: the
//! frame, epilog, cookie-check, refcount, assert-banner and panic helpers,
//! and the names of functions that never return.

use super::guess::{slot_jump, thunk_slot};
use super::walk::Via;
use super::{Cursors, Recorded, decode_at, near_target, straight_line_before};
use crate::analysis::{Analysis, Function, bare_name, is_imm};
use crate::fxmap::FxHashSet;
use crate::isa::x86::{
    ConditionCode, FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind,
    Register,
};
use crate::num::lo32;
use crate::program::{BinaryFormat, Program, SymbolKind};

/// Most instructions in an MSVC epilogue helper: the unlink, the pops, the
/// frame's release and the return.
pub(super) const EPILOG_INSTRS_MAX: usize = 12;
/// Most instructions in the `/GS` cookie check: the compare, the two
/// tests of the x64 form, the rotates back and the jump to the report.
pub(super) const COOKIE_CHECK_INSTRS_MAX: usize = 10;
/// Most instructions in a Rust panic entry: the frame, the arguments it
/// lays out for the message and the call that never returns.
pub(super) const PANIC_INSTRS_MAX: usize = 24;

/// The messages Rust's panic entries format, each with the entry's name;
/// an entry loads its message's address, often a format template whose
/// first byte is the literal's length.
const PANIC_MESSAGES: [(&str, &str); 15] = [
    ("index out of bounds: the len is ", "panic_bounds_check"),
    ("attempt to add with overflow", "panic_const_add_overflow"),
    (
        "attempt to subtract with overflow",
        "panic_const_sub_overflow",
    ),
    (
        "attempt to multiply with overflow",
        "panic_const_mul_overflow",
    ),
    (
        "attempt to divide with overflow",
        "panic_const_div_overflow",
    ),
    (
        "attempt to calculate the remainder with overflow",
        "panic_const_rem_overflow",
    ),
    (
        "attempt to negate with overflow",
        "panic_const_neg_overflow",
    ),
    (
        "attempt to shift left with overflow",
        "panic_const_shl_overflow",
    ),
    (
        "attempt to shift right with overflow",
        "panic_const_shr_overflow",
    ),
    ("attempt to divide by zero", "panic_const_div_by_zero"),
    (
        "attempt to calculate the remainder with a divisor of zero",
        "panic_const_rem_by_zero",
    ),
    (
        "misaligned pointer dereference: address must be a multiple of ",
        "panic_misaligned_pointer_dereference",
    ),
    (
        "called `Option::unwrap()` on a `None` value",
        "option_unwrap_failed",
    ),
    ("range start index ", "slice_start_index_len_fail"),
    ("range end index ", "slice_end_index_len_fail"),
];

/// The 32-bit stack probe's opening, `push ecx; lea ecx,[esp+4]; sub
/// ecx,eax`: MSVC's `_chkstk` and `_alloca_probe` are that in every
/// runtime version.
pub(super) const CHKSTK_X86: [u8; 7] = [0x51, 0x8d, 0x4c, 0x24, 0x04, 0x2b, 0xc8];

/// Bare names of functions that never return to their caller (C runtime,
/// C++ ABI, Windows API and MSVC runtime, Rust runtime, the kernel's bug
/// check, and the Go runtime's ways of not coming back).
const NORETURN_NAMES: &[&str] = &[
    "abort",
    "exit",
    "_exit",
    "_Exit",
    "quick_exit",
    "__assert_fail",
    "__stack_chk_fail",
    "longjmp",
    "_longjmp",
    "siglongjmp",
    "__longjmp_chk",
    "err",
    "errx",
    "verr",
    "verrx",
    "_Unwind_Resume",
    "__cxa_throw",
    "__cxa_rethrow",
    "__cxa_bad_cast",
    "__cxa_bad_typeid",
    "__cxa_call_unexpected",
    "__cxa_pure_virtual",
    "std::terminate",
    "std::unexpected",
    "ExitProcess",
    "ExitThread",
    "FreeLibraryAndExitThread",
    "RtlRaiseException",
    "_CxxThrowException",
    "__report_gsfailure",
    "__report_rangecheckfailure",
    "__report_securityfailure",
    "_invalid_parameter_noinfo_noreturn",
    "_invoke_watson",
    "__std_terminate",
    "_purecall",
    "_amsg_exit",
    "terminate",
    "rust_panic",
    "alloc::alloc::handle_alloc_error",
    "alloc::raw_vec::capacity_overflow",
    "std::process::abort",
    "std::process::exit",
    "KeBugCheck",
    "KeBugCheckEx",
    "runtime.gopanic",
    "runtime.throw",
    "runtime.fatal",
    "runtime.fatalthrow",
    "runtime.fatalpanic",
    "runtime.abort",
    "runtime.goexit1",
    "runtime.morestack",
];

/// Tells whether a (bare, demangled) function name denotes a function that never returns.
///
/// # Arguments
///
/// * `name` - The name as [`crate::search::demangled_name`] renders it, without a `dll!` prefix.
pub(crate) fn is_noreturn_name(name: &str) -> bool {
    NORETURN_NAMES.contains(&name)
        || name.starts_with("core::panicking::")
        || name.starts_with("std::panicking::begin_panic")
        || name.starts_with("std::__throw_")
        || name.ends_with("::unwrap_failed")
}

/// Bare names of functions that never return when their first argument is
/// nonzero: glibc's `error` and `error_at_line` call `exit(status)` then.
const EXIT_ON_STATUS_NAMES: [&str; 2] = ["error", "error_at_line"];

/// Tells whether a (bare, demangled) name is a function that never returns
/// when its first argument is nonzero ([`EXIT_ON_STATUS_NAMES`]).
///
/// # Arguments
///
/// * `name` - The name, without a `dll!` prefix.
pub(super) fn exits_on_status_name(name: &str) -> bool {
    EXIT_ON_STATUS_NAMES.contains(&name)
}

/// Returns the import slots of glibc's `error` and `error_at_line`.
///
/// Only the imports are glibc's: a function the program defines under
/// either name is its own reporter, which may well return, so a call to it
/// stays a call (a statically linked glibc's is missed, not guessed at).
///
/// # Arguments
///
/// * `program` - The loaded image.
///
/// # Returns
///
/// The slots, empty for an image other than ELF, where the names are not
/// glibc's.
pub(crate) fn status_exits(program: &Program) -> FxHashSet<u64> {
    if program.format != BinaryFormat::Elf {
        return FxHashSet::default();
    }
    program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .filter(|s| exits_on_status_name(bare_name(&crate::search::demangled_name(&s.name))))
        .map(|s| s.addr)
        .collect()
}

/// Returns the slot a `call [slot]` reads its target from, with an absolute
/// or rip-relative operand.
///
/// # Arguments
///
/// * `call` - The call.
pub(super) fn call_slot(call: &Instruction) -> Option<u64> {
    (call.op0_kind() == OpKind::Memory
        && matches!(call.memory_base(), Register::None | Register::RIP)
        && call.memory_index() == Register::None)
        .then(|| call.memory_displacement64())
}

/// Tells whether the instructions before a call set its first argument
/// register to a definite nonzero constant.
///
/// The last instruction that writes the register decides: a `mov` of an
/// immediate whose low 32 bits, the `int` status, are not zero. Any other
/// write, a way in between that write and the call, or no write at all
/// says no, so an unknown status stays a call that returns.
///
/// # Arguments
///
/// * `program` - The loaded image, for the calling convention.
/// * `bitness` - 32 or 64.
/// * `before` - The straight-line run before the call, in order.
/// * `entered` - Whether control can come in at an address other than
///   by falling through from the instruction before it; asked of each
///   address from the call back to the write that decides, in that order.
pub(super) fn sets_nonzero_status(
    program: &Program,
    bitness: u32,
    before: &[Instruction],
    mut entered: impl FnMut(u64) -> bool,
) -> bool {
    let Some(&first) = crate::analysis::decompile::abi::conv(program, bitness)
        .args
        .first()
    else {
        return false;
    };
    let mut info = InstructionInfoFactory::new();
    for i in before.iter().rev() {
        if entered(i.next_ip()) {
            return false;
        }
        let writes = info.info(i).used_registers().iter().any(|u| {
            u.register().full_register() == first
                && matches!(
                    u.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                )
        });
        if writes {
            return i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && is_imm(i.op1_kind())
                && lo32(i.immediate(1)) != 0;
        }
    }
    false
}

/// Tells whether a call the walk decodes never returns for its status.
///
/// That is a call to glibc's `error` or `error_at_line` with a nonzero
/// status ([`sets_nonzero_status`]) over the run the walk recorded before
/// it, where a branch decoded to an address inside the run is a way in.
/// The callee is the import a thunk it reaches jumps through, or the
/// import slot it calls through, never a function the program defines.
/// The answer is tentative: the call waits in [`Recorded::status_ends`]
/// until the walk has every branch of the function, and
/// [`Recorded::reopen`] takes it back if one enters the run.
///
/// # Arguments
///
/// * `cursors` - The walk's decoders.
/// * `status_exits` - The addresses [`status_exits`] lists.
/// * `call` - The call.
/// * `recorded` - What the walk decoded so far.
pub(super) fn exits_with_status(
    cursors: &mut Cursors<'_>,
    status_exits: &FxHashSet<u64>,
    call: &Instruction,
    recorded: &mut Recorded,
) -> bool {
    if status_exits.is_empty() {
        return false;
    }
    let hit = |a: u64| status_exits.contains(&a);
    let reaches = match near_target(call) {
        Some(t) => thunk_slot(cursors, t).is_some_and(hit),
        None => call_slot(call).is_some_and(hit),
    };
    if !reaches {
        return false;
    }
    let (program, bitness) = (cursors.program, cursors.bitness);
    let before = straight_line_before(program, bitness, call.ip(), recorded);
    let mut ways = Vec::new();
    let ends = sets_nonzero_status(program, bitness, &before, |va| {
        ways.push(va);
        recorded.last_branch_to.contains_key(&va)
    });
    if ends {
        recorded.status_ends.push((call.ip(), call.next_ip(), ways));
    }
    ends
}

impl Recorded {
    /// Takes back the first call ended for its status that a branch decoded
    /// since now enters, between the status and the call.
    ///
    /// The walk asks each time its queue runs dry, so the calls still ended
    /// when it finishes were checked against every branch of the function;
    /// each call is taken back at most once, so the asking ends.
    ///
    /// # Arguments
    ///
    /// * `ended` - The call sites the walk ended paths at; the call taken
    ///   back leaves it.
    ///
    /// # Returns
    ///
    /// The address after the call taken back, for the walk to follow, or
    /// `None` when every such call still holds.
    pub(super) fn reopen(&mut self, ended: &mut Vec<u64>) -> Option<(u64, Via)> {
        let at = self.status_ends.iter().position(|(_, _, ways)| {
            ways.iter().any(|w| {
                self.last_branch_to.contains_key(w)
                    || self.by_next.get(w).is_some_and(|f| f.count > 1)
            })
        })?;
        let (call, next, _) = self.status_ends.remove(at);
        ended.retain(|&e| e != call);
        Some((next, Via::Fall))
    }
}

/// Tells whether a call reaches a function a name test accepts.
///
/// The callee is a direct one or an import ([`calls_import`]).
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the callee's name.
/// * `bitness` - 32 or 64.
/// * `call` - The call.
/// * `test` - The test, on a bare, demangled name.
pub(super) fn calls_named(
    program: &Program,
    analysis: &Analysis,
    bitness: u32,
    call: &Instruction,
    test: fn(&str) -> bool,
) -> bool {
    near_target(call)
        .and_then(|t| analysis.function(t).filter(|g| g.entry == t))
        .and_then(|g| g.name.as_deref())
        .is_some_and(|name| test(bare_name(&crate::search::demangled_name(name))))
        || calls_import(program, bitness, call, test)
}

/// Tells whether a call reaches an import a name test accepts.
///
/// That is through the import slot it calls through, or the one a thunk it
/// reaches jumps through (past the `endbr64` a CET stub opens with).
///
/// # Arguments
///
/// * `program` - The image.
/// * `bitness` - 32 or 64.
/// * `call` - The call.
/// * `test` - The test, on a bare, demangled name.
pub(super) fn calls_import(
    program: &Program,
    bitness: u32,
    call: &Instruction,
    test: fn(&str) -> bool,
) -> bool {
    let import = |slot: u64| {
        program.symbols.iter().any(|s| {
            s.kind == SymbolKind::Import
                && s.addr == slot
                && test(bare_name(&crate::search::demangled_name(&s.name)))
        })
    };
    if let Some(slot) = call_slot(call) {
        return import(slot);
    }
    near_target(call)
        .and_then(|t| decode_at(program, bitness, t))
        .and_then(|i| {
            if matches!(i.mnemonic(), Mnemonic::Endbr64 | Mnemonic::Endbr32) {
                decode_at(program, bitness, i.next_ip())
            } else {
                Some(i)
            }
        })
        .and_then(|i| slot_jump(&i))
        .is_some_and(import)
}

/// Names the reference-counting helper a function is, when it is one.
///
/// An intrusive smart pointer's release is the same handful of instructions
/// in every instantiation: load the object, atomically take one off its
/// reference count, destroy it through its vtable when that count reaches
/// zero, and clear the pointer. A template writes one copy per type, so a C++
/// program carries hundreds of them, all unnamed.
///
/// The assignment operator opens with that same release and then stores the
/// new object and adds a reference to it, so the two are told apart by the
/// atomic increment: a release only ever takes one away.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `f` - The candidate function.
///
/// # Returns
///
/// `refcounted_release`, `refcounted_assign`, or `None` when the shape is
/// neither: an exchange-add paired with an indirect call is what marks them.
pub(super) fn refcount_helper_name(
    program: &Program,
    bitness: u32,
    f: &Function,
) -> Option<&'static str> {
    let mut takes_one = false;
    let mut adds_one = false;
    let mut destroys = false;
    for b in &f.blocks {
        let mut va = b.start;
        while va < b.end {
            let Some(i) = decode_at(program, bitness, va) else {
                break;
            };
            if i.has_lock_prefix() {
                match i.mnemonic() {
                    Mnemonic::Xadd => takes_one = true,
                    Mnemonic::Inc => adds_one = true,
                    Mnemonic::Add if i.try_immediate(1).is_ok_and(|v| v == 1) => adds_one = true,
                    _ => {}
                }
            }
            destroys |= i.flow_control() == FlowControl::IndirectCall;
            va = i.next_ip();
        }
    }
    if !(takes_one && destroys) {
        return None;
    }
    Some(if adds_one {
        "refcounted_assign"
    } else {
        "refcounted_release"
    })
}

/// Whether a function prints an assertion banner of its own.
///
/// The reporter behind `assert` names itself in the text it prints, for
/// example `Assertion failed`. Reading the literals a function references
/// is what tells it from the thousands of
/// functions that merely call it.
///
/// # Arguments
///
/// * `program` - The loaded image, read for the literals.
/// * `bitness` - Decoder bitness.
/// * `f` - The candidate function.
pub(super) fn prints_assert_banner(program: &Program, bitness: u32, f: &Function) -> bool {
    /// Longest banner read.
    const CAP: usize = 64;
    /// Shortest run accepted, so a stray byte pair is not a banner.
    const MIN: usize = 6;
    for b in &f.blocks {
        let mut va = b.start;
        while va < b.end {
            let Some(i) = decode_at(program, bitness, va) else {
                break;
            };
            let refs = [i.memory_displacement64(), i.immediate64()];
            if refs.iter().any(|addr| {
                *addr != 0
                    && crate::strings::cstr_at(program, *addr, MIN, CAP)
                        .is_some_and(|(_, t)| t.to_ascii_lowercase().contains("assert"))
            }) {
                return true;
            }
            va = i.next_ip();
        }
    }
    false
}

/// Names the MSVC prologue helper at `va` by its first two instructions.
///
/// `__SEH_prolog4` opens with `push -1; push eax`, or, as later CRTs build
/// it, with `push __except_handler4; push dword [fs:0]`, and `__EH_prolog3`
/// with `push eax; push dword [fs:0]`: each pushes the caller's exception
/// registration, points `ebp` one word below the entry stack pointer and
/// returns with the stack lower than it found it, which is why a caller's
/// `[ebp+8]` is its first argument only when the helper's effect is known.
/// The names are the CRT's own; the `_GS` and `_catch` variants share the
/// opening and the frame effect and are not told apart.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The callee's entry.
///
/// # Returns
///
/// The helper's name, or `None` when the code at `va` does not open like one.
pub(crate) fn frame_helper_name(program: &Program, bitness: u32, va: u64) -> Option<&'static str> {
    let first = decode_at(program, bitness, va)?;
    let second = decode_at(program, bitness, first.next_ip())?;
    let pushes_reg = |i: &Instruction, r: Register| {
        i.mnemonic() == Mnemonic::Push
            && i.op0_kind() == OpKind::Register
            && i.op0_register().full_register() == r
    };
    let pushes_minus_one = first.mnemonic() == Mnemonic::Push
        && matches!(
            first.op0_kind(),
            OpKind::Immediate8to32 | OpKind::Immediate32
        )
        && first.immediate(0) & 0xffff_ffff == 0xffff_ffff;
    let pushes_fs0 = second.mnemonic() == Mnemonic::Push
        && second.op0_kind() == OpKind::Memory
        && second.segment_prefix() == Register::FS
        && second.memory_base() == Register::None
        && second.memory_displacement64() == 0;
    let pushes_handler =
        first.mnemonic() == Mnemonic::Push && first.op0_kind() == OpKind::Immediate32;
    if (pushes_minus_one && pushes_reg(&second, Register::RAX)) || (pushes_handler && pushes_fs0) {
        Some("__SEH_prolog4")
    } else if pushes_reg(&first, Register::RAX) && pushes_fs0 {
        Some("__EH_prolog3")
    } else {
        None
    }
}

/// Names the MSVC epilogue helper at `va` by its first two instructions.
///
/// `__SEH_epilog4` opens with `mov ecx, [ebp-0x10]; mov fs:[0], ecx` and
/// `__EH_epilog3` with `mov ecx, [ebp-0xc]; mov fs:[0], ecx`: each unlinks
/// the caller's exception registration, restores the registers the
/// prologue helper saved, tears the frame down and returns to the
/// caller's return address, which it pops and pushes back around the
/// work. The names are the CRT's own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The callee's entry.
///
/// # Returns
///
/// The helper's name, or `None` when the code at `va` does not open like one.
pub(crate) fn epilog_helper_name(program: &Program, bitness: u32, va: u64) -> Option<&'static str> {
    let first = decode_at(program, bitness, va)?;
    let second = decode_at(program, bitness, first.next_ip())?;
    let loads_link = first.mnemonic() == Mnemonic::Mov
        && first.op0_kind() == OpKind::Register
        && first.op0_register().full_register() == Register::RCX
        && first.op1_kind() == OpKind::Memory
        && first.memory_base().full_register() == Register::RBP
        && first.memory_index() == Register::None;
    let unlinks = second.mnemonic() == Mnemonic::Mov
        && second.op0_kind() == OpKind::Memory
        && second.segment_prefix() == Register::FS
        && second.memory_base() == Register::None
        && second.memory_displacement64() == 0
        && second.op1_kind() == OpKind::Register
        && second.op1_register().full_register() == Register::RCX;
    if !(loads_link && unlinks) {
        return None;
    }
    match crate::disasm::displacement(&first, bitness) {
        -0x10 => Some("__SEH_epilog4"),
        -0xc => Some("__EH_epilog3"),
        _ => None,
    }
}

/// Names the `/GS` cookie check at `va` by its first three instructions.
///
/// `__security_check_cookie` compares its argument with the cookie
/// global and jumps to the failure report when they differ: on x64 `cmp
/// rcx, [cookie]; jne fail; rol rcx, 16` (its second test checks the top
/// word is clear), on x86 `cmp ecx, [cookie]; jne fail; ret`. A function of
/// that shape returns its argument register and every other one as it
/// found them, which the decompiler reads it by. The name is the CRT's
/// own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The function's entry.
///
/// # Returns
///
/// The checker's name, or `None` when the code at `va` does not open like
/// one.
pub(crate) fn cookie_check_name(program: &Program, bitness: u32, va: u64) -> Option<&'static str> {
    let first = decode_at(program, bitness, va)?;
    let second = decode_at(program, bitness, first.next_ip())?;
    let third = decode_at(program, bitness, second.next_ip())?;
    let arg = if bitness == 64 {
        Register::RCX
    } else {
        Register::ECX
    };
    let compares = first.mnemonic() == Mnemonic::Cmp
        && first.op0_kind() == OpKind::Register
        && first.op0_register() == arg
        && first.op1_kind() == OpKind::Memory
        && matches!(
            first.memory_base(),
            Register::None | Register::RIP | Register::EIP
        )
        && first.memory_index() == Register::None
        && first.segment_prefix() == Register::None;
    let differs = second.flow_control() == FlowControl::ConditionalBranch
        && second.condition_code() == ConditionCode::ne;
    let then = if bitness == 64 {
        third.mnemonic() == Mnemonic::Rol
            && third.op0_kind() == OpKind::Register
            && third.op0_register() == Register::RCX
    } else {
        third.flow_control() == FlowControl::Return
    };
    (compares && differs && then).then_some("__security_check_cookie")
}

/// Names a Rust panic entry at `va` by the message it formats.
///
/// A panic entry (`core::panicking::panic_bounds_check`, the
/// `panic_const_*` family, `core::option::unwrap_failed`, the slice
/// index failures) is a few instructions that load the address of its
/// message, or of a format template whose first byte is the literal's
/// length, and call on into the panic machinery without returning. A
/// small function of that shape whose one message is one of
/// [`PANIC_MESSAGES`] is that entry; the names are the standard
/// library's own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The function's entry.
/// * `count` - Its instruction count.
///
/// # Returns
///
/// The entry's name, or `None` when the function returns, loads no
/// message, or more than one.
pub(crate) fn panic_helper_name(
    program: &Program,
    bitness: u32,
    va: u64,
    count: usize,
) -> Option<&'static str> {
    /// Bytes read at a loaded address, enough for the longest message.
    const READ: usize = 72;
    let mut at = va;
    let mut found = None;
    for _ in 0..count {
        let i = decode_at(program, bitness, at)?;
        if i.flow_control() == FlowControl::Return {
            return None;
        }
        if i.mnemonic() == Mnemonic::Lea
            && i.op1_kind() == OpKind::Memory
            && i.memory_base() == Register::RIP
            && let Some(bytes) = program.read_va_upto(i.memory_displacement64(), READ)
        {
            let says = |m: &str| {
                bytes.starts_with(m.as_bytes())
                    || bytes.get(1..).is_some_and(|b| b.starts_with(m.as_bytes()))
            };
            if let Some((_, name)) = PANIC_MESSAGES.iter().find(|(m, _)| says(m)) {
                if found.is_some_and(|f| f != *name) {
                    return None;
                }
                found = Some(*name);
            }
        }
        at = i.next_ip();
    }
    found
}
