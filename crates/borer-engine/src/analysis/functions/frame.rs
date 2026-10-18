//! What a function's instructions do to its stack frame, read step by
//! step.

use std::collections::BTreeSet;

use crate::analysis::is_imm;
use crate::fxmap::FxHashMap;
use crate::isa::x86::{FlowControl, Instruction, Mnemonic, OpKind, Register};

/// Prologue and stack-access facts gathered during the walk, enough to say
/// how many stack-passed arguments the function reads.
#[derive(Default)]
pub(super) struct FrameFacts {
    /// `(address, immediate)` of the first `sub rsp, imm`.
    pub(super) sub_rsp: Option<(u64, u64)>,
    /// Addresses of `push` instructions.
    pub(super) pushes: Vec<u64>,
    /// Addresses of `pop` instructions.
    pub(super) pops: Vec<u64>,
    /// `(address, bytes)` of every `add rsp, imm`, the caller's cleanup
    /// after a call.
    pub(super) adds: Vec<(u64, i64)>,
    /// `(address, offset)`: rsp-relative offset held by rbp after `mov rbp, rsp` / `lea rbp, [rsp+K]`.
    pub(super) rbp_off: Option<(u64, i64)>,
    /// The register holding a copy of the stack pointer and the address of
    /// the `mov` that made it: `mov rax, rsp` stores the callee-saved
    /// registers home through `rax` and sets the frame pointer from it, and
    /// `push ebx; mov ebx, esp; and esp, -16` reads the arguments through
    /// `ebx` once the stack is aligned.
    pub(super) rax_alias: Option<(Register, u64)>,
    /// `(base register, displacement, address)` of every rsp/rbp-based
    /// memory operand.
    pub(super) refs: Vec<(Register, i64, u64)>,
    /// `(address, next address)` of every instruction an epilogue is made
    /// of: a pop, an `add rsp, imm`, a `mov rsp, reg` or a `leave`.
    pub(super) links: Vec<(u64, u64)>,
    /// Addresses of `ret` and of unconditional and indirect jumps: where
    /// an epilogue ends.
    pub(super) exits: Vec<u64>,
    /// A `sub rsp, <register>` was seen: the frame is sized at runtime
    /// (`__chkstk`, `alloca`), so its size is unknown here.
    pub(super) dynamic_frame: bool,
    /// The frame pointer was set by a prologue helper to one word below the
    /// entry stack pointer, the place `push ebp; mov ebp, esp` puts it.
    pub(super) helper_frame: bool,
}

impl FrameFacts {
    /// Records what one instruction tells about the frame.
    ///
    /// # Arguments
    ///
    /// * `instr` - The decoded instruction.
    /// * `addr` - Its address; prologue facts keep the earliest occurrence.
    /// * `bitness` - Decoder bitness, which decides how a displacement's
    ///   sign is read.
    pub(super) fn observe(&mut self, instr: &Instruction, addr: u64, bitness: u32) {
        let earlier = |seen: Option<(u64, i64)>| seen.is_none_or(|(a, _)| addr < a);
        if matches!(
            instr.flow_control(),
            FlowControl::Return | FlowControl::UnconditionalBranch | FlowControl::IndirectBranch
        ) {
            self.exits.push(addr);
        }
        let restores_rsp = instr.op_count() == 2
            && instr.op0_kind() == OpKind::Register
            && instr.op0_register().full_register() == Register::RSP
            && instr.op1_kind() == OpKind::Register;
        if matches!(instr.mnemonic(), Mnemonic::Pop | Mnemonic::Leave)
            || (instr.mnemonic() == Mnemonic::Mov && restores_rsp)
        {
            self.links.push((addr, instr.next_ip()));
        }
        match instr.mnemonic() {
            Mnemonic::Push => self.pushes.push(addr),
            Mnemonic::Pop => self.pops.push(addr),
            Mnemonic::Add if moves_rsp_by_imm(instr) => {
                self.adds.push((addr, instr.immediate(1).cast_signed()));
                self.links.push((addr, instr.next_ip()));
            }
            Mnemonic::Sub
                if moves_rsp_by_imm(instr) && self.sub_rsp.is_none_or(|(a, _)| addr < a) =>
            {
                self.sub_rsp = Some((addr, instr.immediate(1)));
            }
            Mnemonic::Sub
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RSP
                    && instr.op1_kind() == OpKind::Register =>
            {
                self.dynamic_frame = true;
            }
            Mnemonic::Mov
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RBP
                    && instr.op1_kind() == OpKind::Register
                    && instr.op1_register().full_register() == Register::RSP
                    && earlier(self.rbp_off) =>
            {
                self.rbp_off = Some((addr, 0));
            }
            Mnemonic::Lea
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RBP
                    && instr.memory_base().full_register() == Register::RSP
                    && instr.memory_index() == Register::None
                    && earlier(self.rbp_off) =>
            {
                self.rbp_off = Some((addr, crate::disasm::displacement(instr, bitness)));
            }
            Mnemonic::Lea
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register().full_register() == Register::RBP
                    && instr.memory_index() == Register::None
                    && earlier(self.rbp_off)
                    && let Some((alias, at)) = self.rax_alias
                    && instr.memory_base().full_register() == alias =>
            {
                self.rbp_off = Some((at, crate::disasm::displacement(instr, bitness)));
            }
            _ => {}
        }
        let rax_alias = self.rax_alias;
        for op in 0..instr.op_count() {
            if instr.op_kind(op) == OpKind::Memory {
                let base = instr.memory_base().full_register();
                let disp = crate::disasm::displacement(instr, bitness);
                if base == Register::RSP || base == Register::RBP {
                    self.refs.push((base, disp, addr));
                } else if let Some((alias, at)) = rax_alias
                    && base == alias
                {
                    self.refs.push((Register::RSP, disp, at));
                }
            }
        }
        let written = (instr.op0_kind() == OpKind::Register)
            .then(|| instr.op0_register().full_register())
            .filter(|_| !matches!(instr.mnemonic(), Mnemonic::Cmp | Mnemonic::Test));
        let copies_rsp = instr.mnemonic() == Mnemonic::Mov
            && instr.op1_kind() == OpKind::Register
            && instr.op1_register().full_register() == Register::RSP
            && written.is_some_and(|r| r.is_gpr() && r != Register::RSP && r != Register::RBP);
        if copies_rsp {
            self.rax_alias = written.map(|r| (r, addr));
        } else if written.is_some() && written == self.rax_alias.map(|(r, _)| r) {
            self.rax_alias = None;
        }
    }

    /// Computes how many stack-passed arguments the function reads.
    ///
    /// # Arguments
    ///
    /// * `shadow` - Bytes of callee-owned home space above the return address
    ///   (32 for the Microsoft x64 convention, 0 for SysV and 32-bit code).
    /// * `word` - Stack word size in bytes: what a push moves the stack
    ///   pointer by, the width of the return address, and the distance
    ///   between two arguments.
    ///
    /// # Returns
    ///
    /// The highest argument index read, counting from the first slot above
    /// the return address and shadow space; capped at 32. Zero when the frame
    /// is sized at runtime and its size is unknown, since a local read cannot
    /// then be told from an argument.
    ///
    /// Each read is placed against the stack pointer as it stood at that
    /// instruction: the pushes, pops and cleanups before it, and the frame
    /// allocation once made. A frame-pointer read is placed against where
    /// the pointer was set, so the pushes the body makes for its own calls
    /// move nothing. The pops and cleanups of an epilogue, the run of them
    /// right before a `ret` or a tail jump, tear the frame down on that
    /// path alone and move nothing for the code after them in the image
    /// ([`FrameFacts::epilogues`]).
    pub(super) fn stack_args(&self, shadow: i64, word: i64) -> u32 {
        if self.dynamic_frame && self.sub_rsp.is_none() {
            return 0;
        }
        let epilogue = self.epilogues();
        let below_at = |addr: u64| -> i64 {
            let pushes = count_i64(self.pushes.iter().filter(|a| **a < addr).count());
            let pops = count_i64(
                self.pops
                    .iter()
                    .filter(|a| **a < addr && !epilogue.contains(a))
                    .count(),
            );
            let sub = self
                .sub_rsp
                .filter(|(a, _)| *a < addr)
                .map_or(0, |(_, imm)| imm.cast_signed());
            let adds: i64 = self
                .adds
                .iter()
                .filter(|(a, _)| *a < addr && !epilogue.contains(a))
                .map(|(_, k)| *k)
                .sum();
            sub + (pushes - pops) * word - adds
        };
        let frame_pointer = if self.helper_frame {
            Some(word)
        } else {
            self.rbp_off.map(|(at, k)| below_at(at) - k)
        };
        self.refs
            .iter()
            .filter_map(|(base, disp, addr)| {
                let below = if *base == Register::RSP {
                    below_at(*addr)
                } else {
                    frame_pointer?
                };
                let entry_rel = disp - below;
                let first = word + shadow;
                (entry_rel >= first)
                    .then(|| ((entry_rel - first) / word + 1).min(32))
                    .and_then(|n| u32::try_from(n).ok())
            })
            .max()
            .unwrap_or(0)
    }
}

/// A count of instructions as a signed stack-slot multiplier.
///
/// # Arguments
///
/// * `n` - The count; a function holds far fewer pushes than `i64::MAX`.
fn count_i64(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}

impl FrameFacts {
    /// Collects the addresses of the epilogues' instructions: from each
    /// exit, the pops, cleanups and frame restores that lead into it
    /// without a gap, walking back while each one's next address is the
    /// one reached so far.
    ///
    /// A map from each link's next address to its own, built once with the
    /// first link encountered winning as a scan's first match would, answers
    /// each step of that walk in constant time.
    pub(super) fn epilogues(&self) -> BTreeSet<u64> {
        let mut leads = FxHashMap::with_capacity_and_hasher(self.links.len(), Default::default());
        for &(addr, next) in &self.links {
            leads.entry(next).or_insert(addr);
        }
        let mut out = BTreeSet::new();
        for &exit in &self.exits {
            let mut at = exit;
            while let Some(&addr) = leads.get(&at) {
                if !out.insert(addr) {
                    break;
                }
                at = addr;
            }
        }
        out
    }
}

/// What an instruction does to a function's frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FrameStep {
    /// A callee-saved `push` or `sub rsp, N`: the frame is being set up.
    Opens,
    /// The matching `pop`, `add rsp, N` or `leave`: the frame is torn down.
    Closes,
}

/// Tells whether `instr` adds an immediate to the stack pointer or takes
/// one from it: `sub rsp, N` and `add rsp, N` in any width.
///
/// Every reader of the frame goes through here, so they agree on the
/// widths: the decoder gives `sub esp, 8` an [`OpKind::Immediate8to32`],
/// and that is as much a frame as the [`OpKind::Immediate8to64`] it gives
/// `sub rsp, 8`.
///
/// # Arguments
///
/// * `instr` - The decoded instruction, a `sub` or an `add`.
pub(super) fn moves_rsp_by_imm(instr: &Instruction) -> bool {
    instr.op0_kind() == OpKind::Register
        && instr.op0_register().full_register() == Register::RSP
        && is_imm(instr.op1_kind())
}

/// Tells whether `instr` opens or closes a frame.
///
/// # Arguments
///
/// * `instr` - The decoded instruction.
///
/// # Returns
///
/// [`FrameStep::Opens`] for a callee-saved push or `sub rsp, N`;
/// [`FrameStep::Closes`] for the matching pop, `add rsp, N` or `leave`;
/// `None` for anything else. An `add rsp` right after a call cleans
/// arguments in 32-bit code, but by then the frame has long been opened,
/// so it cannot be told apart from teardown here and need not be.
pub(super) fn frame_step(instr: &Instruction) -> Option<FrameStep> {
    let saved = |r: Register| {
        matches!(
            r.full_register(),
            Register::RBX
                | Register::RBP
                | Register::RSI
                | Register::RDI
                | Register::R12
                | Register::R13
                | Register::R14
                | Register::R15
        )
    };
    let on_rsp = moves_rsp_by_imm(instr);
    match instr.mnemonic() {
        Mnemonic::Push if instr.op0_kind() == OpKind::Register && saved(instr.op0_register()) => {
            Some(FrameStep::Opens)
        }
        Mnemonic::Sub if on_rsp => Some(FrameStep::Opens),
        Mnemonic::Pop if instr.op0_kind() == OpKind::Register && saved(instr.op0_register()) => {
            Some(FrameStep::Closes)
        }
        Mnemonic::Add if on_rsp => Some(FrameStep::Closes),
        Mnemonic::Leave => Some(FrameStep::Closes),
        _ => None,
    }
}
