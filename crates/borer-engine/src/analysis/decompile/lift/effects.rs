//! Register effects and liveness: what an instruction reads and writes, and
//! which values a block needs.

use super::*;
use crate::analysis::returns::Sse;
use crate::analysis::x87;

/// Width in bits a read or write of `r` covers in its canonical register.
///
/// Byte and word registers cover their own lane (a high byte counts as the
/// word holding it), anything wider the whole register (a 32-bit access
/// counts as whole; documented roughness).
///
/// # Arguments
///
/// * `r` - Any register.
pub(super) fn lane_bits(r: Register) -> u8 {
    match r.size() {
        1 if is_high_byte(r) => 16,
        1 => 8,
        2 => 16,
        _ => 64,
    }
}

/// Canonical registers with the lane width (in bits) accessed.
pub(in crate::analysis::decompile) type Lanes = Vec<(Key, u8)>;
/// One instruction's register reads and writes for liveness.
pub(in crate::analysis::decompile) type Effects = (Lanes, Lanes);

/// Per instruction, how many later instructions of the block read each
/// register it writes before the register is written again.
///
/// A backward pass: a write takes the reads pending for its register and
/// clears them, a read adds one for the definition before it; an
/// instruction naming a register in two operands reads it once.
///
/// # Arguments
///
/// * `ctx` - Convention and block starts.
/// * `factory` - Register-access facts.
/// * `instrs` - The block's instructions.
pub(super) fn read_counts(
    ctx: &Ctx<'_>,
    factory: &mut InstructionInfoFactory,
    instrs: &[Instruction],
) -> Vec<FxHashMap<Key, u32>> {
    let mut pending: FxHashMap<Key, u32> = FxHashMap::default();
    let mut out: Vec<FxHashMap<Key, u32>> = vec![FxHashMap::default(); instrs.len()];
    for (idx, instr) in instrs.iter().enumerate().rev() {
        let (reads, writes) = reg_effects(ctx, factory, instr);
        if let Some(counts) = out.get_mut(idx) {
            for (k, _) in &writes {
                counts.insert(*k, pending.remove(k).unwrap_or(0));
            }
        }
        let distinct: BTreeSet<Key> = reads.iter().map(|(k, _)| *k).collect();
        for k in distinct {
            *pending.entry(k).or_default() += 1;
        }
    }
    out
}

/// The import symbols by address and by demangled name.
///
/// Built once per analysis ([`import_names`]): [`import_prototype`] runs
/// for every call the lifter executes in every dataflow pass, and
/// demangling every import for each one cost ten milliseconds a call on a
/// mutant whose symbol table was corrupt, seconds for a function of thirty
/// blocks.
pub(super) struct ImportNames {
    /// The raw symbol name of the first import at each address.
    by_addr: BTreeMap<u64, String>,
    /// The raw symbol name of the first import carrying each demangled name.
    by_name: BTreeMap<String, String>,
}

/// Returns the import name tables of the program, built the first time.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis, whose memo holds the tables.
pub(super) fn import_names(ctx: &Ctx<'_>) -> std::sync::Arc<ImportNames> {
    ctx.analysis.derived.get_or_build("import_names", (), || {
        let mut by_addr = BTreeMap::new();
        let mut by_name = BTreeMap::new();
        for s in ctx
            .program
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        {
            by_addr.entry(s.addr).or_insert_with(|| s.name.clone());
            by_name
                .entry(crate::search::demangled_name(&s.name))
                .or_insert_with(|| s.name.clone());
        }
        ImportNames { by_addr, by_name }
    })
}

/// Returns the prototype of the import a call or jump reaches.
///
/// The import's raw symbol name is what carries it: an MSVC-mangled name
/// states the parameters and the calling convention outright, and a C
/// name is looked up in the SDK table ([`crate::analysis::prototypes::declared`]),
/// which says how the target's convention passes it, then in the type
/// library ([`library_prototype`]), which covers POSIX. A thunk names its
/// import by the demangled form, so the raw symbol behind it is found by
/// that.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `target` - The callee's entry when the call is direct, or the import
///   slot it calls through.
///
/// # Returns
///
/// The prototype, or `None` when the target is not an import with one.
pub(in crate::analysis::decompile) fn import_prototype(
    ctx: &Ctx<'_>,
    target: Option<u64>,
) -> Option<crate::analysis::prototypes::Prototype> {
    use crate::analysis::prototypes::{declared, msvc_prototype};
    let names = import_names(ctx);
    let name = bare(import_raw(ctx, &names, target?)?);
    msvc_prototype(name)
        .or_else(|| declared(name, ctx.bitness))
        .or_else(|| {
            crate::analysis::typelib::declared(name, ctx.program.format)
                .map(|d| library_prototype(d, ctx.bitness, ctx.program.format))
        })
}

/// Tells whether a call or jump reaches an import of a C runtime, whose
/// exports leave their arguments for the caller to pop (`__cdecl`).
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `target` - The callee's entry when the call is direct, or the import
///   slot it calls through.
pub(in crate::analysis::decompile) fn runtime_import(ctx: &Ctx<'_>, target: Option<u64>) -> bool {
    let names = import_names(ctx);
    target
        .and_then(|t| import_raw(ctx, &names, t))
        .is_some_and(|raw| {
            crate::analysis::prototypes::is_c_runtime(raw.split_once('!').map_or("", |(d, _)| d))
        })
}

/// Returns the bytes of arguments a callee is known to pop on return.
///
/// A function states it with its own `ret imm16`, an import with its
/// prototype, and a C runtime import pops nothing. On a 32-bit target a
/// function with no `ret` of its own (one that ends in a jump to
/// another, `jmp [edx+0x50]` passing its own argument on) states
/// nothing, nor does an import of another library without a prototype
/// or a callee the call does not name. A 64-bit callee pops what its
/// `ret` says, nothing when it has none.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the target.
/// * `target` - The callee's entry, when the call names it.
/// * `reached` - The callee's entry or the import slot the call goes
///   through.
///
/// # Returns
///
/// The bytes, or `None` when nothing states them.
pub(in crate::analysis::decompile) fn stated_pop(
    ctx: &Ctx<'_>,
    target: Option<u64>,
    reached: Option<u64>,
) -> Option<u32> {
    let bits32 = ctx.bitness == 32;
    if let Some(f) = target.and_then(|t| ctx.analysis.function(t)) {
        if !bits32 {
            return Some(f.stack_pop);
        }
        if let Some(pop) = function_pop(ctx, f, TAIL_DEPTH) {
            return Some(pop);
        }
    }
    let word = u32::try_from(ctx.conv.word).unwrap_or(0);
    match import_prototype(ctx, reached) {
        Some(p) if p.callee_pops && bits32 => Some(u32::from(p.stack_params()) * word),
        Some(_) => Some(0),
        None if !bits32 || runtime_import(ctx, reached) => Some(0),
        None => None,
    }
}

/// Most tail jumps followed to the `ret` that pops for a function
/// ([`function_pop`]).
pub(in crate::analysis::decompile) const TAIL_DEPTH: u8 = 4;

/// Returns the bytes a function pops on return, as its own `ret imm16`
/// says, or as the functions it ends in a jump to say alike.
///
/// `pop ebp; jmp sub_x` hands the caller's arguments to `sub_x`, whose
/// `ret` then pops for both; a jump through a register or a table names
/// no function, and functions that disagree state nothing.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `f` - The function.
/// * `depth` - How many more tail jumps may be followed.
///
/// # Returns
///
/// The bytes, or `None` when no `ret` is reached.
pub(in crate::analysis::decompile) fn function_pop(
    ctx: &Ctx<'_>,
    f: &crate::analysis::Function,
    depth: u8,
) -> Option<u32> {
    use crate::analysis::BlockTerm;
    if f.blocks.iter().any(|b| b.term == BlockTerm::Ret) {
        return Some(f.stack_pop);
    }
    let depth = depth.checked_sub(1)?;
    let mut pop = None;
    for s in f
        .blocks
        .iter()
        .filter(|b| b.term == BlockTerm::Jmp)
        .flat_map(|b| &b.successors)
        .filter(|s| f.blocks.binary_search_by_key(*s, |b| b.start).is_err())
    {
        let tail = function_pop(ctx, ctx.analysis.function(*s)?, depth)?;
        if pop.is_some_and(|p| p != tail) {
            return None;
        }
        pop = Some(tail);
    }
    pop
}

/// Returns the raw symbol name of the import at `t`: the address table
/// slot's own, or for a thunk the import its name demangles to.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `names` - The import name tables ([`import_names`]).
/// * `t` - The slot or the thunk's entry.
pub(super) fn import_raw<'n>(ctx: &Ctx<'_>, names: &'n ImportNames, t: u64) -> Option<&'n str> {
    match names.by_addr.get(&t) {
        Some(name) => Some(name),
        None => {
            let named = ctx.analysis.function(t)?.name.as_deref()?;
            names.by_name.get(named).map(String::as_str)
        }
    }
}

/// Finds the argument registers a function reads before writing them, and
/// who it passes the rest on to.
///
/// The blocks are decoded in address order up to the first call or 64
/// instructions. A push of an argument register that the first call
/// consumes as one of its arguments reads it; a push beyond the callee's
/// arity only makes room. A function of one instruction is a thunk: it
/// reads nothing, and it counts as a forward to the function it jumps to
/// when that jump is direct and lands in a function; an import thunk
/// jumps through a table and stays unknown.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the decoder.
/// * `info` - Register-access facts.
/// * `conv` - The convention whose argument registers are looked for.
/// * `t` - The function's entry address.
///
/// # Returns
///
/// The registers read, and, when the scan stopped at a direct call that no
/// write to an argument register preceded, that call's target; `None` for
/// an unknown function or an import thunk.
pub(in crate::analysis::decompile) fn leading_reads(
    ctx: &Ctx<'_>,
    info: &mut InstructionInfoFactory,
    conv: &Conv,
    t: u64,
) -> Option<Leading> {
    /// Longest prologue examined.
    const INSTRS_MAX: usize = 64;
    let f = ctx.analysis.function(t)?;
    if f.instr_count <= 1 {
        let i = ctx.decode(f.entry)?;
        let onward = (i.flow_control() == FlowControl::UnconditionalBranch)
            .then(|| i.near_branch_target())
            .filter(|&n| n != 0 && n != t && ctx.analysis.function(n).is_some())?;
        return Some(Leading {
            read: BTreeSet::new(),
            written: BTreeSet::new(),
            forward: Some(onward),
            fixed: None,
        });
    }
    let mut read: BTreeSet<Register> = BTreeSet::new();
    let mut written: BTreeSet<Register> = BTreeSet::new();
    let mut pushed: Vec<Option<(Register, bool)>> = Vec::new();
    let mut seen = 0usize;
    let mut forward = None;
    let mut homes = Homes::new(ctx.bitness, conv);
    'blocks: for b in &f.blocks {
        let mut va = b.start;
        while va < b.end && seen < INSTRS_MAX {
            let Some(i) = ctx.decode(va) else {
                break 'blocks;
            };
            seen += 1;
            match homes.step(&i, ctx.bitness) {
                Some(Home::Spill) => {
                    va = i.next_ip();
                    continue;
                }
                Some(Home::Load(r)) => {
                    if conv.slot(r).is_some() && !written.contains(&r) {
                        read.insert(r);
                    }
                }
                Some(Home::VaStart) | None => {}
            }
            // INVARIANT: a frame helper builds the callee's frame and
            // returns; it reads no argument register, so the scan goes on
            // past it to the reads that follow, with `eax` written since
            // the helper leaves the return address it juggled there.
            if crate::analysis::render::frame_helper(ctx.analysis, ctx.overlay, &i) {
                written.insert(Register::EAX);
                va = i.next_ip();
                continue;
            }
            if matches!(
                i.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                let arity =
                    crate::analysis::decompile::call_stack_arity(ctx, &i).unwrap_or(pushed.len());
                for (r, was_written) in pushed.iter().rev().take(arity).flatten() {
                    if !was_written {
                        read.insert(*r);
                    }
                }
                if i.flow_control() == FlowControl::Call {
                    forward = Some(i.near_branch_target()).filter(|&n| n != 0 && n != t);
                }
                break 'blocks;
            }
            // INVARIANT: a jump to another function's entry hands the
            // arguments on, the registers this function set excepted; a
            // jump within the function is flow.
            if i.flow_control() == FlowControl::UnconditionalBranch
                && matches!(
                    i.op0_kind(),
                    OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
                )
                && let n = i.near_branch_target()
                && n != t
                && ctx.analysis.function(n).is_some_and(|g| g.entry == n)
            {
                forward = Some(n);
                break 'blocks;
            }
            if i.mnemonic() == Mnemonic::Push {
                let reg = (i.op0_kind() == OpKind::Register)
                    .then(|| canon(i.op0_register(), ctx.bitness))
                    .filter(|r| conv.slot(*r).is_some())
                    .map(|r| (r, written.contains(&r)));
                pushed.push(reg);
                va = i.next_ip();
                continue;
            }
            let facts = info.info(&i);
            let set_only = sets_without_reading(&i).then(|| canon(i.op0_register(), ctx.bitness));
            let mut writes: Vec<Register> = Vec::new();
            for ur in facts.used_registers() {
                let r = canon(ur.register(), ctx.bitness);
                if conv.slot(r).is_none() {
                    continue;
                }
                let reads = set_only != Some(r)
                    && matches!(
                        ur.access(),
                        OpAccess::Read
                            | OpAccess::CondRead
                            | OpAccess::ReadWrite
                            | OpAccess::ReadCondWrite
                    );
                if reads && !written.contains(&r) {
                    read.insert(r);
                }
                if matches!(
                    ur.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                ) {
                    writes.push(r);
                }
            }
            written.extend(writes);
            va = i.next_ip();
        }
    }
    let fixed = homes.fixed();
    if let Some(k) = fixed {
        read.retain(|r| conv.slot(*r).is_some_and(|s| s < k));
    }
    Some(Leading {
        read,
        written,
        forward,
        fixed,
    })
}

/// What [`leading_reads`] found at the head of a function.
pub(in crate::analysis::decompile) struct Leading {
    /// Argument registers read before being written.
    pub(in crate::analysis::decompile) read: BTreeSet<Register>,
    /// Argument registers written before the hand-off: what the function
    /// it forwards to reads of these is the wrapper's own value.
    pub(in crate::analysis::decompile) written: BTreeSet<Register>,
    /// The function a wrapper hands its arguments on to.
    pub(in crate::analysis::decompile) forward: Option<u64>,
    /// The fixed argument count of a variadic function: it homed its
    /// argument registers through `r9` for `va_start`, and the registers
    /// from this slot up are the variable ones.
    pub(in crate::analysis::decompile) fixed: Option<usize>,
}

/// What one instruction does with the home slots of the argument registers.
pub(super) enum Home {
    /// Stores an argument register into its own home slot.
    Spill,
    /// Loads an argument's home slot back into a register.
    Load(Register),
    /// Takes the address of a home slot: `va_start`.
    VaStart,
}

/// Tracks the Microsoft x64 home slots through a prologue.
///
/// It follows where the stack pointer stands and which registers alias
/// it, so a store to `[rsp+8+8k]`, to `[rax+8+8k]` after `mov rax, rsp`
/// or to `[rbp+K]` after `mov rbp, rsp` is seen as the home of argument
/// `k`.
///
/// A variadic function homes every argument register from the first
/// variable one through `r9` and takes the address of the first variable
/// slot for `va_start`; a function that homes its arguments for their
/// addresses stops short of `r9` unless it has four.
pub(super) struct Homes {
    /// Whether the convention has home slots at all.
    pub(super) active: bool,
    /// Bytes the stack pointer stands below its entry value.
    pub(super) below: i64,
    /// Bytes below the entry stack pointer that `rax` stands for.
    pub(super) rax: Option<i64>,
    /// Bytes below the entry stack pointer that `rbp` stands for.
    pub(super) rbp: Option<i64>,
    /// Argument registers by slot.
    pub(super) args: Vec<Register>,
    /// The register last stored into each home slot: the slot's own
    /// argument register for `va_start`, or any other, `xmm0` for a float
    /// argument parked to be read back as bits.
    pub(super) stored: BTreeMap<usize, Register>,
    /// The lowest slot whose address was taken.
    pub(super) va_start: Option<usize>,
}

impl Homes {
    /// Starts tracking at a function's entry.
    ///
    /// # Arguments
    ///
    /// * `bitness` - 32 or 64.
    /// * `conv` - The callee's convention.
    pub(super) fn new(bitness: u32, conv: &Conv) -> Homes {
        Homes {
            active: bitness == 64 && conv.shadow > 0,
            below: 0,
            rax: None,
            rbp: None,
            args: conv.args.to_vec(),
            stored: BTreeMap::new(),
            va_start: None,
        }
    }

    /// Follows one instruction.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `bitness` - 32 or 64.
    ///
    /// # Returns
    ///
    /// What it did with a home slot, if anything.
    pub(super) fn step(&mut self, i: &Instruction, bitness: u32) -> Option<Home> {
        if !self.active {
            return None;
        }
        let word = 8i64;
        let base_below = |h: &Homes, r: Register| -> Option<i64> {
            match r.full_register() {
                Register::RSP => Some(h.below),
                Register::RAX => h.rax,
                Register::RBP => h.rbp,
                _ => None,
            }
        };
        // INVARIANT: slot `k` of the arguments, counting the home slots
        // first; one past them is the first stack argument, whose address
        // `va_start` takes when every register argument is fixed.
        let arg_slot = |h: &Homes, i: &Instruction| -> Option<usize> {
            if i.memory_index() != Register::None {
                return None;
            }
            let entry_rel =
                crate::disasm::displacement(i, bitness) - base_below(h, i.memory_base())?;
            let k = (entry_rel - word) / word;
            (entry_rel >= word && (entry_rel - word) % word == 0 && k >= 0)
                .then(|| usize::try_from(k).ok())
                .flatten()
                .filter(|k| *k <= h.args.len())
        };
        let slot_of = |h: &Homes, i: &Instruction| arg_slot(h, i).filter(|k| *k < h.args.len());
        let mut out = None;
        let is_mov = i.mnemonic() == Mnemonic::Mov;
        let is_store = matches!(
            i.mnemonic(),
            Mnemonic::Mov | Mnemonic::Movss | Mnemonic::Movsd | Mnemonic::Movd | Mnemonic::Movq
        );
        if is_store && i.op0_kind() == OpKind::Memory && i.op1_kind() == OpKind::Register {
            if let Some(k) = slot_of(self, i) {
                let r = i.op1_register().full_register();
                self.stored.insert(k, r);
                if r == self.args[k] {
                    out = Some(Home::Spill);
                }
            }
        } else if is_mov && i.op0_kind() == OpKind::Register && i.op1_kind() == OpKind::Memory {
            if let Some(k) = slot_of(self, i) {
                out = Some(Home::Load(
                    self.stored.get(&k).copied().unwrap_or(self.args[k]),
                ));
            }
        } else if i.mnemonic() == Mnemonic::Lea
            && i.op0_kind() == OpKind::Register
            && let Some(k) = arg_slot(self, i)
        {
            self.va_start = Some(self.va_start.map_or(k, |v| v.min(k)));
            out = Some(Home::VaStart);
        }
        // A 32-bit immediate is signed at its width: `add esp, -0x2d0`
        // carries 0xfffffd30, which is -0x2d0 to the 32-bit add.
        let signed_imm = |i: &Instruction| match i.op1_kind() {
            OpKind::Immediate32 => i64::from(i.immediate32().cast_signed()),
            OpKind::Immediate16 => i64::from(i.immediate16().cast_signed()),
            _ => i.immediate(1).cast_signed(),
        };
        match i.mnemonic() {
            Mnemonic::Push => self.below += word,
            Mnemonic::Pop => self.below -= word,
            Mnemonic::Sub
                if i.op0_register().full_register() == Register::RSP && is_imm(i.op1_kind()) =>
            {
                self.below += signed_imm(i);
            }
            Mnemonic::Add
                if i.op0_register().full_register() == Register::RSP && is_imm(i.op1_kind()) =>
            {
                self.below -= signed_imm(i);
            }
            _ => {}
        }
        let sets = |i: &Instruction, r: Register| {
            i.op0_kind() == OpKind::Register && i.op0_register().full_register() == r
        };
        let (below, rax, rbp) = (self.below, self.rax, self.rbp);
        let alias_of = |i: &Instruction| -> Option<i64> {
            match (i.mnemonic(), i.op1_kind()) {
                (Mnemonic::Mov, OpKind::Register) => {
                    base_below_of(below, rax, rbp, i.op1_register())
                }
                (Mnemonic::Lea, OpKind::Memory) if i.memory_index() == Register::None => {
                    base_below_of(below, rax, rbp, i.memory_base())
                        .map(|b| b - crate::disasm::displacement(i, bitness))
                }
                _ => None,
            }
        };
        if sets(i, Register::RAX) {
            self.rax = alias_of(i);
        }
        if sets(i, Register::RBP) {
            self.rbp = alias_of(i);
        }
        out
    }

    /// The fixed argument count when the function is variadic: it took the
    /// address of the first variable argument (`va_start`) and stored
    /// every argument register from there on home, so the list continues
    /// in memory; with every register argument fixed, the address is the
    /// first stack argument's and the last register is homed beside it. A
    /// function that only parks its parameters home, for their addresses
    /// or a debug build's habit, takes no address past them and is not
    /// variadic.
    pub(super) fn fixed(&self) -> Option<usize> {
        let first = self.va_start?;
        let own = |k: usize| self.stored.get(&k) == self.args.get(k);
        let last = self.args.len().checked_sub(1)?;
        ((first..self.args.len()).all(own) && (first <= last || own(last))).then_some(first)
    }
}

/// Bytes below the entry stack pointer that a base register stands for.
///
/// # Arguments
///
/// * `below` - Where the stack pointer stands.
/// * `rax` - What `rax` aliases, if the stack pointer.
/// * `rbp` - What `rbp` aliases, if the stack pointer.
/// * `r` - The register asked about.
pub(super) fn base_below_of(
    below: i64,
    rax: Option<i64>,
    rbp: Option<i64>,
    r: Register,
) -> Option<i64> {
    match r.full_register() {
        Register::RSP => Some(below),
        Register::RAX => rax,
        Register::RBP => rbp,
        _ => None,
    }
}

/// Finds the argument registers a call or jump passes on untouched to
/// its target.
///
/// A wrapper that only makes room on the stack and calls, or jumps,
/// straight on hands its callee whatever argument registers the callee
/// reads: `this` reaches a method's wrapper through `ecx` the wrapper
/// never names. An import's prototype says what it reads; a function in
/// the image is scanned ([`leading_reads`]), and a chain of such wrappers
/// is followed up to four links.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the decoder.
/// * `info` - Register-access facts.
/// * `instr` - The call or jump.
///
/// # Returns
///
/// The registers the target, or a callee it passes them on to, reads
/// before writing them; none when the target is unknown or reads none.
pub(in crate::analysis::decompile) fn forwarded_reads(
    ctx: &Ctx<'_>,
    info: &mut InstructionInfoFactory,
    instr: &Instruction,
) -> Vec<Register> {
    /// Most wrappers followed to the function that reads the arguments.
    const FORWARD_MAX: usize = 4;
    let Some(t) = static_target(instr).filter(|&t| t != 0) else {
        return Vec::new();
    };
    if let Some(p) = import_prototype(ctx, Some(t)) {
        if ctx.bitness == 32 {
            return if p.this {
                vec![Register::ECX]
            } else {
                Vec::new()
            };
        }
        let floats = p.floats.checked_shl(u32::from(p.this)).unwrap_or(0);
        let count = usize::from(p.params) + usize::from(p.this);
        return (0..count.min(ctx.conv.reg_args()))
            .filter_map(|i| ctx.conv.arg_reg(i, floats))
            .collect();
    }
    let conv: &Conv = if ctx.bitness == 32 {
        &FASTCALL_X86
    } else {
        ctx.conv
    };
    let mut at = t;
    let mut seen: BTreeSet<u64> = BTreeSet::from([t]);
    let mut shadow: BTreeSet<Register> = BTreeSet::new();
    let mut out: BTreeSet<Register> = BTreeSet::new();
    // INVARIANT: a target that reads some registers itself and calls on
    // hands that callee the others untouched: `mov [rsp+28h], rcx; lea
    // rcx, [rsp+38h]; call g` reads `rcx` and passes `g` the `rdx` it
    // never wrote, so on a 64-bit target the reads of every link not
    // shadowed by a write before it are read. On a 32-bit one the first
    // link that reads decides: there `ecx` and `edx` are a cdecl callee's
    // scratch as often as a fastcall's arguments, and a read deeper down
    // would make a cdecl caller fastcall.
    let deep = ctx.bitness == 64;
    while seen.len() <= FORWARD_MAX {
        let Some(Leading {
            read,
            written,
            forward: onward,
            ..
        }) = leading_reads(ctx, info, conv, at)
        else {
            break;
        };
        out.extend(read.difference(&shadow));
        if !deep && !out.is_empty() {
            break;
        }
        shadow.extend(written);
        match onward {
            Some(n) if seen.insert(n) => at = n,
            _ => break,
        }
    }
    out.into_iter().collect()
}

/// Returns the volatile registers a direct callee leaves as it found them.
///
/// A leaf function that never writes `r8` hands the caller's `r8` back, and
/// a compiler that sees the leaf (link-time code generation) keeps using
/// it: `mov r8, rcx; xor edx, edx; call leaf; mov [r8+0C0h], dl`. A callee
/// is read whole, once per function and overlay: any call in it (but a
/// stack probe or a cookie check), any jump out of it or through a
/// register that is no jump table, any trap clobbers every volatile;
/// otherwise the volatile registers no instruction of it writes survive.
/// `rax` is left to [`crate::analysis::Function::preserves_rax`]. `xmm0`
/// also survives a callee that hands it back untouched on every path to a
/// `ret` ([`keeps_float`]): a stack-cookie check jumps out to a function
/// that never returns when the cookie is wrong, and the double the caller
/// computed is still in `xmm0` when it does return.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the decoder.
/// * `target` - The callee's entry.
///
/// # Returns
///
/// The preserved registers as canonical keys; empty for an unknown callee,
/// an import thunk or a callee that may clobber them all.
pub(in crate::analysis::decompile) fn preserved_volatiles(
    ctx: &Ctx<'_>,
    target: u64,
) -> std::sync::Arc<Vec<Key>> {
    ctx.analysis.derived.get_or_build_item(
        "preserved_volatiles",
        ctx.overlay_key,
        target,
        || {
            let Some(f) = ctx.analysis.function(target).filter(|f| f.entry == target) else {
                return Vec::new();
            };
            let xmm0 = Key::Reg(Register::XMM0);
            let float = (ctx.bitness == 64
                && ctx.conv.volatile.contains(&Register::XMM0)
                && keeps_float(ctx, target))
            .then_some(xmm0);
            let starts: BTreeSet<u64> = f.blocks.iter().map(|b| b.start).collect();
            let mut factory = InstructionInfoFactory::new();
            let mut written: BTreeSet<Key> = BTreeSet::new();
            for b in &f.blocks {
                let mut va = b.start;
                while va < b.end {
                    let Some(i) = ctx.decode(va) else {
                        return Vec::new();
                    };
                    va = i.next_ip();
                    let leaves = match i.flow_control() {
                        FlowControl::Call | FlowControl::IndirectCall => {
                            !crate::analysis::render::preserves_registers(
                                ctx.analysis,
                                ctx.overlay,
                                &i,
                            )
                        }
                        FlowControl::UnconditionalBranch => {
                            near_target(&i).is_none_or(|t| !starts.contains(&t))
                        }
                        FlowControl::IndirectBranch => {
                            !ctx.analysis.jump_tables.contains_key(&i.ip())
                        }
                        FlowControl::Interrupt
                        | FlowControl::Exception
                        | FlowControl::XbeginXabortXend => true,
                        FlowControl::Next
                        | FlowControl::ConditionalBranch
                        | FlowControl::Return => false,
                    };
                    if leaves {
                        return float.into_iter().collect();
                    }
                    for ur in factory.info(&i).used_registers() {
                        if matches!(
                            ur.access(),
                            OpAccess::Write
                                | OpAccess::ReadWrite
                                | OpAccess::CondWrite
                                | OpAccess::ReadCondWrite
                        ) {
                            written.insert(Key::Reg(canon(ur.register(), ctx.bitness)));
                        }
                    }
                }
            }
            let rax = Key::Reg(canon(Register::RAX, ctx.bitness));
            ctx.conv
                .volatile
                .iter()
                .map(|r| Key::Reg(canon(*r, ctx.bitness)))
                .filter(|k| *k != rax && (!written.contains(k) || Some(*k) == float))
                .collect()
        },
        |keys| keys.capacity() * size_of::<Key>(),
    )
}

/// What a 32-bit callee does with the vector registers ([`Sse`]).
///
/// A C runtime SSE2 helper is known by its name or its import's
/// ([`crate::analysis::returns::sse_helper`]), any other callee with a body
/// by that body, read once per callee
/// ([`crate::analysis::returns::sse_call`]). An unknown callee takes and
/// returns nothing there.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `target` - The callee's entry, or the import slot the call goes
///   through.
pub(in crate::analysis::decompile) fn sse_callee(ctx: &Ctx<'_>, target: Option<u64>) -> Sse {
    let Some(t) = target else {
        return Sse::default();
    };
    let imports = import_names(ctx);
    let name = match (ctx.overlay.names.get(&t), ctx.analysis.function(t)) {
        (Some(n), _) => Some(n.as_str()),
        (None, Some(f)) => f.name.as_deref(),
        (None, None) => import_raw(ctx, &imports, t),
    };
    if let Some(s) = name.and_then(crate::analysis::returns::sse_helper) {
        return s;
    }
    *ctx.analysis.derived.get_or_build("sse_call", t, || {
        ctx.analysis
            .function(t)
            .filter(|f| f.entry == t && f.thunk.is_none())
            .map_or_else(Sse::default, |f| {
                crate::analysis::returns::sse_call(ctx.program, ctx.analysis, f)
            })
    })
}

/// The vector registers a 32-bit callee takes arguments in, `xmm0` first
/// ([`sse_callee`]).
///
/// # Arguments
///
/// * `sse` - What the callee does with the vector registers.
pub(in crate::analysis::decompile) fn sse_args(sse: Sse) -> impl Iterator<Item = Register> {
    [
        Register::XMM0,
        Register::XMM1,
        Register::XMM2,
        Register::XMM3,
        Register::XMM4,
        Register::XMM5,
    ]
    .into_iter()
    .enumerate()
    .filter(move |(k, _)| sse.args & (1u8 << k) != 0)
    .map(|(_, r)| r)
}

/// Tells whether a direct callee hands the float result register back
/// untouched.
///
/// That is `xmm0` on a 64-bit target, read once per callee
/// ([`crate::analysis::returns::preserves_float`]), and the x87 stack on a
/// 32-bit one ([`crate::analysis::returns::x87_kept`]).
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `target` - The callee's entry.
pub(in crate::analysis::decompile) fn keeps_float(ctx: &Ctx<'_>, target: u64) -> bool {
    if ctx.bitness == 32 {
        return crate::analysis::returns::x87_kept(ctx.program, ctx.analysis).contains(&target);
    }
    *ctx.analysis
        .derived
        .get_or_build("keeps_float", target, || {
            ctx.analysis
                .function(target)
                .filter(|f| f.entry == target && f.thunk.is_none())
                .is_some_and(|f| crate::analysis::returns::preserves_float(ctx.program, f))
        })
}

/// What a call does to the x87 stack ([`x87::Call`]).
///
/// A C runtime helper is known by its name or its import's
/// ([`x87::helper`]); a direct callee that leaves the stack alone keeps it
/// ([`keeps_float`]); a direct callee whose body takes values off the
/// stack it is handed is a helper too ([`x87_body`]). Any other callee is
/// plain.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `target` - The callee's entry, or the import slot the call goes
///   through.
pub(in crate::analysis::decompile) fn x87_callee(ctx: &Ctx<'_>, target: Option<u64>) -> x87::Call {
    let Some(t) = target else {
        return x87::Call::Plain;
    };
    let imports = import_names(ctx);
    let name = match (ctx.overlay.names.get(&t), ctx.analysis.function(t)) {
        (Some(n), _) => Some(n.as_str()),
        (None, Some(f)) => f.name.as_deref(),
        (None, None) => import_raw(ctx, &imports, t),
    };
    if let Some(e) = name.and_then(x87::helper) {
        return x87::Call::Helper(e);
    }
    if keeps_float(ctx, t) {
        return x87::Call::Kept;
    }
    match x87_body(ctx, t) {
        Some(e) => x87::Call::Helper(e),
        None => x87::Call::Plain,
    }
}

/// What a direct callee's body takes off the x87 stack it is handed, and
/// leaves there, when it is a helper that calls nothing
/// ([`x87::leaf_helper`]). Read once per callee.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `target` - The callee's entry.
fn x87_body(ctx: &Ctx<'_>, target: u64) -> Option<x87::Effect> {
    *ctx.analysis.derived.get_or_build("x87_body", target, || {
        let f = ctx
            .analysis
            .function(target)
            .filter(|f| f.entry == target && f.thunk.is_none())?;
        x87::leaf_helper(
            ctx.program,
            ctx.analysis,
            &mut InstructionInfoFactory::new(),
            f,
        )
    })
}

/// Tells whether an instruction sets its first operand without reading it.
///
/// The encoding reads the operand, the idiom does not: `xor r, r` and
/// `sub r, r` clear it, `or r, -1` sets every bit, `and r, 0` clears it.
/// What the register held is not in the result, so the register is
/// written and not read.
///
/// # Arguments
///
/// * `instr` - The instruction.
pub(in crate::analysis::decompile) fn sets_without_reading(instr: &Instruction) -> bool {
    if instr.op_count() != 2 || instr.op0_kind() != OpKind::Register {
        return false;
    }
    let same_register =
        instr.op1_kind() == OpKind::Register && instr.op0_register() == instr.op1_register();
    let immediate = is_imm(instr.op1_kind());
    let mask = match instr.op0_register().size() {
        1 => 0xff,
        2 => 0xffff,
        4 => 0xffff_ffff,
        _ => u64::MAX,
    };
    match instr.mnemonic() {
        Mnemonic::Xor | Mnemonic::Sub => same_register,
        Mnemonic::Or => immediate && instr.immediate(1) & mask == mask,
        Mnemonic::And => immediate && instr.immediate(1) & mask == 0,
        _ => false,
    }
}

/// Register reads and writes of one instruction for liveness, as canonical
/// keys with the lane width read or defined.
///
/// A byte or word write defines only its lane and keeps the rest of the
/// register, so a need wider than the lane survives it; a high-byte write
/// (`ah`) keeps bits on both sides and counts as a whole-register read that
/// defines nothing. Calls read the argument registers, on 32-bit the
/// callee's rather than the caller's, and write the volatile ones, rax
/// excepted for a callee that hands it back untouched; a return reads rax;
/// a tail jump out of the function reads the argument registers.
///
/// # Arguments
///
/// * `ctx` - Convention and block starts.
/// * `factory` - Register-access facts.
/// * `instr` - The instruction.
///
/// # Returns
///
/// `(reads, writes)`.
pub(super) fn reg_effects(
    ctx: &Ctx<'_>,
    factory: &mut InstructionInfoFactory,
    instr: &Instruction,
) -> Effects {
    let mut reads: Lanes = Vec::new();
    let mut writes: Lanes = Vec::new();
    let info = factory.info(instr);
    let set_only =
        sets_without_reading(instr).then(|| Key::Reg(canon(instr.op0_register(), ctx.bitness)));
    for ur in info.used_registers() {
        let r = ur.register();
        let k = Key::Reg(canon(r, ctx.bitness));
        let lane = lane_bits(r);
        let (mut rd, wr) = match ur.access() {
            OpAccess::Read | OpAccess::CondRead => (true, false),
            OpAccess::Write => (false, true),
            OpAccess::ReadWrite | OpAccess::ReadCondWrite => (true, true),
            OpAccess::CondWrite | OpAccess::None | OpAccess::NoMemAccess => (false, false),
        };
        if set_only.as_ref() == Some(&k) {
            rd = false;
        }
        if rd {
            reads.push((k, lane));
        }
        if wr {
            if r.size() == 1 && is_high_byte(r) {
                reads.push((k, 64));
            } else {
                writes.push((k, lane));
            }
        }
    }
    // INVARIANT: a call or a jump out may pass any argument register, a
    // float one in its vector register as well (`xmm1` for a callee that
    // takes a `float` second), so a value pending in one is kept for it.
    let args = || {
        ctx.conv
            .args
            .iter()
            .chain(ctx.conv.float_args)
            .map(|r| (Key::Reg(*r), 64u8))
    };
    match instr.flow_control() {
        // A stack probe or a cookie check reads and writes nothing the
        // function sees.
        FlowControl::Call
            if crate::analysis::render::preserves_registers(ctx.analysis, ctx.overlay, instr) => {}
        FlowControl::Call | FlowControl::IndirectCall => {
            reads.extend(args());
            // INVARIANT: a 32-bit callee's convention is its own, `thiscall`
            // reading ecx and `fastcall` ecx and edx whatever the caller's
            // is, so a call reads both unless the callee is known to read
            // fewer; a copy into one of them before the call is then live.
            if ctx.bitness == 32 {
                let sse = sse_callee(ctx, x87::named_target(instr));
                reads.extend(sse_args(sse).map(|r| (Key::Reg(r), 64u8)));
                let n = near_target(instr)
                    .and_then(|t| ctx.callee_arity.get(&t))
                    .map_or(2, |(n, _, _)| *n);
                reads.extend(
                    [Register::RCX, Register::RDX]
                        .into_iter()
                        .take(n)
                        .map(|r| (Key::Reg(canon(r, 32)), 64u8)),
                );
            }
            let rax = canon(Register::RAX, ctx.bitness);
            let keeps_rax = instr.flow_control() == FlowControl::Call
                && ctx
                    .analysis
                    .function(instr.near_branch_target())
                    .is_some_and(|f| f.preserves_rax);
            let kept = near_target(instr).map(|t| preserved_volatiles(ctx, t));
            writes.extend(
                ctx.conv
                    .volatile
                    .iter()
                    .filter(|r| !(keeps_rax && canon(**r, ctx.bitness) == rax))
                    .map(|r| Key::Reg(canon(*r, ctx.bitness)))
                    .filter(|k| kept.as_ref().is_none_or(|kept| !kept.contains(k)))
                    .map(|k| (k, 64u8)),
            );
        }
        FlowControl::Return if !ctx.unused_result => {
            let back = match (ctx.ret_float, ctx.bitness) {
                (true, 32) if !ctx.ret_sse => Register::ST0,
                (true, _) => Register::XMM0,
                (false, _) => canon(Register::RAX, ctx.bitness),
            };
            reads.push((Key::Reg(back), ctx.ret_lane));
        }
        FlowControl::Return => {}
        FlowControl::UnconditionalBranch => {
            if let Some(t) = near_target(instr)
                && !ctx.block_starts.contains(&t)
            {
                reads.extend(args());
            }
        }
        FlowControl::Next
        | FlowControl::ConditionalBranch
        | FlowControl::IndirectBranch
        | FlowControl::Interrupt
        | FlowControl::Exception
        | FlowControl::XbeginXabortXend => {}
    }
    (reads, writes)
}

/// Width in bits a declared return type fills of the return register.
///
/// # Arguments
///
/// * `declared` - The signature's return type.
///
/// # Returns
///
/// 8 for `bool` and the byte types, 16 for the 16-bit integer and character
/// types, 64 for anything else.
pub(in crate::analysis::decompile) fn declared_bits(declared: &str) -> u8 {
    match declared {
        "bool" | "char" | "unsigned char" | "signed char" | "int8_t" | "uint8_t" => 8,
        "short" | "unsigned short" | "int16_t" | "uint16_t" | "wchar_t" | "char16_t" => 16,
        _ => 64,
    }
}

/// Width in bits of the value a function's `ret` hands back through rax.
///
/// A declared `bool`, `char` or 16-bit return type fixes it. Otherwise the
/// last write of rax reaching each `ret` decides: when every returning path
/// ends its rax writes with a byte (or word) write, the function returns
/// that lane and a caller sees nothing wider, so the bits such a write keeps
/// are dead; when every one ends with a write of `eax` or narrower, the
/// value is 32 bits wide. A returning block without a rax write asks its
/// predecessors, up to [`RET_LANE_DEPTH`] blocks back (`mov al, 0; jmp
/// done` shares its `ret`). Anything else, a call as the last rax writer
/// included, is the whole register. A jump out of the function hands back
/// what the function it enters returns, so a 32-bit lane holds only when
/// that is no wider: the lane its signature or its own exits give it
/// ([`Function::ret_width`](crate::analysis::Function::ret_width)), nothing
/// when it returns nothing, and the whole register when that is not known.
///
/// # Arguments
///
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `declared` - The signature's return type when one is known.
/// * `analysis` - The functions a jump out of the function may enter.
pub(in crate::analysis::decompile) fn ret_lane(
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
    declared: Option<&str>,
    analysis: &crate::analysis::Analysis,
) -> u8 {
    if let Some(d) = declared {
        return declared_bits(d);
    }
    let n = code.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, ss) in succs.iter().enumerate() {
        for &s in ss {
            if s < n {
                preds[s].push(b);
            }
        }
    }
    let mut factory = InstructionInfoFactory::new();
    let written: Vec<Option<u8>> = code
        .iter()
        .map(|instrs| last_rax_write(&mut factory, instrs).map(|(written, _)| written))
        .collect();
    let mut known = |b: usize, from: Option<usize>| match from {
        None => written.get(b).copied().flatten(),
        Some(_) => None,
    };
    let mut lane = 0u8;
    let mut tail = 0u8;
    for (b, instrs) in code.iter().enumerate() {
        let leaves = succs.get(b).is_none_or(Vec::is_empty);
        match instrs.last().map(Instruction::flow_control) {
            Some(FlowControl::Return) => {
                lane = lane.max(lane_before(b, &mut known, &preds, RET_LANE_DEPTH));
            }
            Some(FlowControl::UnconditionalBranch | FlowControl::IndirectBranch) if leaves => {
                let entered = instrs
                    .last()
                    .and_then(near_target)
                    .and_then(|t| analysis.function(t));
                let handed = match entered.map(|g| (g.signature.as_ref(), g)) {
                    Some((Some(sig), _)) if sig.ret == "void" => 0,
                    Some((Some(sig), _)) => declared_bits(&sig.ret),
                    Some((None, g)) if g.returns_value == Some(false) => 0,
                    Some((None, g)) => g.ret_width.unwrap_or(64),
                    None => 64,
                };
                tail = tail.max(handed);
            }
            _ => {}
        }
    }
    match lane {
        0 => 64,
        32 if tail > 32 => 64,
        lane => lane,
    }
}

/// Moves a need map backwards over one instruction: a write at least as wide
/// as the need ends it, then every read adds its lane.
///
/// # Arguments
///
/// * `need` - Registers needed after the instruction, with the widest lane
///   read; updated to the registers needed before it.
/// * `reads` - The instruction's register reads.
/// * `writes` - The instruction's register writes.
pub(super) fn transfer(need: &mut FxHashMap<Key, u8>, reads: &[(Key, u8)], writes: &[(Key, u8)]) {
    for (k, w) in writes {
        if need.get(k).is_some_and(|n| n <= w) {
            need.remove(k);
        }
    }
    for (k, w) in reads {
        let e = need.entry(*k).or_insert(0);
        *e = (*e).max(*w);
    }
}

/// Joins the needs of a successor into `into`: the widest lane wins.
///
/// # Arguments
///
/// * `into` - The accumulated needs.
/// * `from` - A successor's needs at entry.
pub(in crate::analysis::decompile) fn join_need(
    into: &mut FxHashMap<Key, u8>,
    from: &FxHashMap<Key, u8>,
) {
    for (k, w) in from {
        let e = into.entry(*k).or_insert(0);
        *e = (*e).max(*w);
    }
}

/// Computes syntactic register liveness per block (canonical registers only).
///
/// Liveness carries the widest lane read: a register whose low byte alone is
/// read before the next write needs 8 bits, so a byte write fully defines it
/// and the value before the write is dead ([`reg_effects`]).
///
/// # Arguments
///
/// * `ctx` - Convention and block starts.
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
///
/// # Returns
///
/// For every block, the registers live at its entry with the lane width needed.
pub(in crate::analysis::decompile) fn live_in(
    ctx: &Ctx<'_>,
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
) -> Vec<FxHashMap<Key, u8>> {
    let mut factory = InstructionInfoFactory::new();
    let effects: Vec<Vec<Effects>> = code
        .iter()
        .map(|instrs| {
            instrs
                .iter()
                .map(|i| reg_effects(ctx, &mut factory, i))
                .collect()
        })
        .collect();
    live_from(&effects, succs)
}

/// Computes register liveness per block from each instruction's reads and
/// writes, whatever instruction set they were read from ([`live_in`]).
///
/// # Arguments
///
/// * `effects` - Per block and instruction, the register reads and writes.
/// * `succs` - Successor block indices per block.
///
/// # Returns
///
/// For every block, the registers live at its entry with the lane width needed.
pub(in crate::analysis::decompile) fn live_from(
    effects: &[Vec<Effects>],
    succs: &[Vec<usize>],
) -> Vec<FxHashMap<Key, u8>> {
    let n = effects.len();
    let mut live: Vec<FxHashMap<Key, u8>> = vec![FxHashMap::default(); n];
    loop {
        let mut changed = false;
        for b in (0..n).rev() {
            let mut need = FxHashMap::default();
            for &s in &succs[b] {
                join_need(&mut need, &live[s]);
            }
            for (reads, writes) in effects[b].iter().rev() {
                transfer(&mut need, reads, writes);
            }
            if need != live[b] {
                live[b] = need;
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// Computes, for every instruction of a block, the registers some later
/// instruction reads (with the lane width) once it has executed.
///
/// # Arguments
///
/// * `ctx` - Convention and block starts.
/// * `instrs` - The block's instructions.
/// * `out` - Registers live at the block's exit (its successors' entries joined).
///
/// # Returns
///
/// One need map per instruction, indexed like `instrs`.
pub(in crate::analysis::decompile) fn need_after(
    ctx: &Ctx<'_>,
    instrs: &[Instruction],
    out: &FxHashMap<Key, u8>,
) -> Vec<FxHashMap<Key, u8>> {
    let mut factory = InstructionInfoFactory::new();
    let mut need = out.clone();
    let mut after = vec![FxHashMap::default(); instrs.len()];
    for (idx, instr) in instrs.iter().enumerate().rev() {
        after[idx] = need.clone();
        let (reads, writes) = reg_effects(ctx, &mut factory, instr);
        transfer(&mut need, &reads, &writes);
    }
    after
}

/// Computes, for every instruction of a block, the registers some later
/// instruction reads once it has executed.
///
/// It reads each instruction's reads and writes, whatever instruction set
/// they were read from ([`need_after`]).
///
/// # Arguments
///
/// * `effects` - The block's instructions' register reads and writes.
/// * `out` - Registers live at the block's exit.
///
/// # Returns
///
/// One need map per instruction, indexed like `effects`.
pub(in crate::analysis::decompile) fn need_from(
    effects: &[Effects],
    out: &FxHashMap<Key, u8>,
) -> Vec<FxHashMap<Key, u8>> {
    let mut need = out.clone();
    let mut after = vec![FxHashMap::default(); effects.len()];
    for (idx, (reads, writes)) in effects.iter().enumerate().rev() {
        after[idx] = need.clone();
        transfer(&mut need, reads, writes);
    }
    after
}

/// Returns the near-branch target when operand 0 is a near branch.
///
/// # Arguments
///
/// * `instr` - Any decoded instruction.
pub(in crate::analysis::decompile) fn near_target(instr: &Instruction) -> Option<u64> {
    match instr.op0_kind() {
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            Some(instr.near_branch_target())
        }
        _ => None,
    }
}

/// Returns the address a call or jump names outright: a near branch, or
/// an absolute or rip-relative memory operand (`call [0x...]`, `jmp qword
/// [rel slot]` through an import slot).
///
/// # Arguments
///
/// * `instr` - The call or jump.
pub(in crate::analysis::decompile) fn static_target(instr: &Instruction) -> Option<u64> {
    match instr.op0_kind() {
        OpKind::Memory
            if matches!(instr.memory_base(), Register::None | Register::RIP)
                && instr.memory_index() == Register::None =>
        {
            Some(instr.memory_displacement64())
        }
        _ => near_target(instr),
    }
}
