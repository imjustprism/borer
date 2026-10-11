//! Parameters and the frame: which registers and stack slots a function reads
//! as arguments, and its prologue.

use super::*;

/// Infers which parameters are pointers, from the function dereferencing
/// them, and which stack parameters are floating point, from the function
/// reading them as such.
///
/// A parameter rendered `uint64_t` that the function dereferences is not a
/// number, and saying so is the difference between a signature a reader can
/// use and one that is merely not wrong about the width. The evidence is the
/// code's own: a memory access based on the register, or a `lea` taking the
/// address of a field through it.
///
/// A stack parameter the function loads as a `float` or a `double` (`fld`,
/// `movss`, `movsd`, or any instruction reading its slot at one of those
/// widths) is that, not a word that merely holds its bits: a 32-bit
/// function returning `double` in `st0` that does `fld dword [ebp+0xc]`
/// returns its second argument widened from a `float`. One width read
/// names the type; reads at both widths name none, and a parameter the
/// function also dereferences stays a pointer.
///
/// A parameter reaches a register in its argument register, or loaded from
/// its stack slot: `mov eax, [ebp+8]` then `[eax+0x10]` is a field of the
/// first stack argument. The slot is placed against the stack pointer as
/// [`block_depths`] follows it, directly or through a register holding a
/// copy of it (`mov ebp, esp`).
///
/// The pointee is named only when the accesses agree: one width at offset
/// zero is a pointer to that, and anything else is a `void *` whose shape
/// `borer://layout` can propose. A register is only believed while it still
/// holds the argument, so an access after the function reuses it says
/// nothing.
///
/// # Arguments
///
/// * `ctx` - The rendering context, for the bitness and the parameter list.
/// * `code` - The function's instructions, by block.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
///
/// # Returns
///
/// The inferred C type per parameter position, for the parameters that are
/// pointers or floating point: a register parameter's convention slot, a
/// stack parameter's slot counted on past the argument registers. A
/// `double` on a 32-bit stack takes its slot and the next.
pub(super) fn param_types(
    ctx: &Ctx<'_>,
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
    entry: usize,
) -> BTreeMap<usize, String> {
    /// Accesses through one parameter: the widths and offsets seen.
    #[derive(Default)]
    struct Seen {
        /// Access widths, in bytes.
        widths: BTreeSet<usize>,
        /// Displacements from the pointer.
        offsets: BTreeSet<i64>,
        /// The register was used as an address at all.
        addressed: bool,
    }
    let word = ctx.conv.word;
    let first = word + ctx.conv.shadow;
    // INVARIANT: a stack argument's position follows the register ones,
    // as the signature lists it.
    let position_of = |o: i64| {
        (o >= first && (o - first) % word == 0)
            .then(|| usize::try_from((o - first) / word).ok())
            .flatten()
            .map(|n| ctx.conv.args.len() + n)
    };
    // Register to the parameter position it carries and its offset from
    // it, because a function copies an argument into a preserved register
    // before using it: `mov rsi,rcx` then `[rsi+0x18]` is a field of the
    // first argument, and watching only `rcx` would see nothing at all.
    let mut holds: BTreeMap<Register, (usize, i64)> = BTreeMap::new();
    for r in &ctx.params {
        if let Some(p) = ctx.conv.param_pos(*r, &ctx.params) {
            holds.insert(*r, (p, 0));
        }
    }
    let depths = block_depths(ctx, code, succs, entry);
    let mut seen: BTreeMap<usize, Seen> = BTreeMap::new();
    let mut floats: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut factory = InstructionInfoFactory::new();
    // Registers holding a stack address, as its offset from the stack
    // pointer at the entry: the frame pointer `mov ebp, esp` sets.
    let mut frame: BTreeMap<Register, i64> = BTreeMap::new();
    for (instrs, depth) in code.iter().zip(&depths) {
        let mut sp = *depth;
        for instr in instrs {
            let moved = sp_move(ctx, &mut factory, instr);
            let base = lift::canon(instr.memory_base(), ctx.bitness);
            let stack_at = |r: Register| {
                if r.full_register() == Register::RSP {
                    sp
                } else {
                    frame.get(&r).copied()
                }
            };
            if instr.memory_base() != Register::None
                && let Some((param, at)) = holds.get(&base).copied()
            {
                let slot = seen.entry(param).or_default();
                // `lea` computes an address without reading through it, and
                // computes plain sums as often (`lea eax, [ecx-0x30]` is
                // `c - '0'`): only a read or a write through the register
                // shows it is a pointer.
                if instr.mnemonic() != Mnemonic::Lea {
                    slot.addressed = true;
                    slot.widths.insert(instr.memory_size().size());
                    slot.offsets
                        .insert(at.saturating_add(crate::disasm::displacement(instr, ctx.bitness)));
                }
            }
            let dst = (instr.op0_kind() == OpKind::Register)
                .then(|| lift::canon(instr.op0_register(), ctx.bitness));
            let direct = instr.memory_index() == Register::None;
            let address =
                || stack_at(base).map(|a| a + crate::disasm::displacement(instr, ctx.bitness));
            // A stack address copied or offset into a register, and a stack
            // argument loaded into one.
            let (to_frame, loaded) = match (instr.mnemonic(), dst) {
                (Mnemonic::Mov, Some(_)) if instr.op1_kind() == OpKind::Register => (
                    stack_at(lift::canon(instr.op1_register(), ctx.bitness)),
                    None,
                ),
                (Mnemonic::Lea, Some(_)) if direct => (address(), None),
                (Mnemonic::Mov, Some(_))
                    if direct
                        && instr.op1_kind() == OpKind::Memory
                        && usize::try_from(ctx.conv.word)
                            .is_ok_and(|w| w == instr.memory_size().size()) =>
                {
                    (None, address().and_then(position_of))
                }
                _ => (None, None),
            };
            // A `lea` through a carrier moves the offset along; a plain move
            // carries it unchanged.
            let carried = if instr.mnemonic() == Mnemonic::Lea {
                holds.get(&base).copied().map(|(p, at)| {
                    (
                        p,
                        at.saturating_add(crate::disasm::displacement(instr, ctx.bitness)),
                    )
                })
            } else if instr.mnemonic() == Mnemonic::Mov && instr.op1_kind() == OpKind::Register {
                holds
                    .get(&lift::canon(instr.op1_register(), ctx.bitness))
                    .copied()
            } else {
                None
            };
            let info = factory.info(instr);
            let float_bytes = match instr.memory_size() {
                crate::isa::MemorySize::Float32 => Some(4),
                crate::isa::MemorySize::Float64 => Some(8),
                _ => None,
            };
            if let Some(bytes) = float_bytes
                && direct
                && info
                    .used_memory()
                    .iter()
                    .any(|m| matches!(m.access(), OpAccess::Read | OpAccess::CondRead))
                && let Some(p) = address().and_then(position_of)
            {
                floats.entry(p).or_default().insert(bytes);
            }
            for ur in info.used_registers() {
                if matches!(
                    ur.access(),
                    OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
                ) {
                    let r = lift::canon(ur.register(), ctx.bitness);
                    holds.remove(&r);
                    frame.remove(&r);
                }
            }
            if let Some(d) = dst {
                if let Some(moved) = carried.or(loaded.map(|p| (p, 0))) {
                    holds.insert(d, moved);
                }
                if let Some(a) = to_frame {
                    frame.insert(d, a);
                }
            }
            sp = sp.zip(moved).map(|(s, m)| s + m);
        }
    }
    let mut types: BTreeMap<usize, String> = seen
        .into_iter()
        .filter(|(_, s)| s.addressed)
        .map(|(p, s)| (p, pointee_type(&s.widths, &s.offsets).to_owned()))
        .collect();
    for (p, widths) in floats {
        let ty = match widths.into_iter().collect::<Vec<_>>().as_slice() {
            [4] => "float",
            [8] => "double",
            _ => continue,
        };
        types.entry(p).or_insert_with(|| ty.to_owned());
    }
    types
}

/// Names what a pointer points at, from the accesses made through it.
///
/// One width at offset zero is a pointer to a value of that width. Several
/// widths, several offsets, or one offset away from the start is a
/// structure, and `void *` says so without inventing a layout;
/// `borer://layout` proposes one from the same evidence. A `uint32_t *`
/// read only at 0x14 would make the text's `*(uint32_t*)(a2 + 0x14)` read,
/// in C, the element at byte 0x50.
///
/// # Arguments
///
/// * `widths` - Access widths in bytes.
/// * `offsets` - Offsets from the pointer.
///
/// # Returns
///
/// The pointee type as C source.
pub(super) fn pointee_type(widths: &BTreeSet<usize>, offsets: &BTreeSet<i64>) -> &'static str {
    let one = widths.iter().copied().next().filter(|_| widths.len() == 1);
    match (one, offsets.len() == 1 && offsets.contains(&0)) {
        (Some(1), true) => "uint8_t *",
        (Some(2), true) => "uint16_t *",
        (Some(4), true) => "uint32_t *",
        (Some(8), true) => "uint64_t *",
        _ => "void *",
    }
}

/// Returns the state at the function's entry.
///
/// The parameters sit in their registers; a funclet also has `ebp` at its
/// parent's frame, the word below the parent's return address, so the
/// parent's locals read under the parent's names.
///
/// # Arguments
///
/// * `ctx` - The convention, the parameters and the funclet, if any.
pub(super) fn entry_env(ctx: &Ctx<'_>) -> Env {
    let mut env = Env::entry_with_params(ctx.conv, &ctx.params);
    for &(reg, value) in &ctx.assume {
        env.vals.insert(Key::Reg(reg), Expr::Const(value));
    }
    if ctx.funclet.is_some() && ctx.bitness == 32 {
        env.vals
            .insert(Key::Reg(Register::EBP), Expr::Sp(-ctx.conv.word));
    }
    env
}

/// What a function takes: the one reading of its parameters that its own
/// signature and every call to it print, so the two never disagree.
#[derive(Debug, Clone)]
pub(super) struct Shape {
    /// The convention it is called with: on a 32-bit target the one its
    /// register reads show (`ecx` and `edx` fastcall, `ecx` thiscall).
    pub(super) conv: &'static Conv,
    /// The argument registers it reads as parameters, in convention order.
    pub(super) params: Vec<Register>,
    /// It takes `...` past its fixed parameters.
    pub(super) variadic: bool,
    /// Its first parameter is `this`.
    pub(super) this_param: bool,
    /// Index of the hidden pointer a class returned by value comes back
    /// through, right after `this` when there is one.
    pub(super) result_param: Option<u8>,
    /// Positions the signature lists, `this` and the result included,
    /// `...` not.
    pub(super) count: usize,
    /// Stack words its parameters past the register ones take.
    pub(super) stack: u32,
}

impl Shape {
    /// Counts the argument registers a call to the function fills.
    pub(super) fn regs(&self) -> usize {
        self.count.min(self.conv.reg_args())
    }

    /// The argument positions the function reads in their floating-point
    /// register and not their integer one: a bit per position.
    pub(super) fn floats(&self) -> u8 {
        if self.conv.float_seq {
            // INVARIANT: the floating parameters list past the integer ones
            // the body reads, and every float argument below the highest
            // one read fills the positions between: the second float
            // argument arrives in `xmm1` whether the callee reads `xmm0`
            // or not, so the mask runs from `base` to that highest
            // position, saturated where the byte runs out.
            let base = self.conv.float_base(&self.params);
            let last = self
                .params
                .iter()
                .filter(|r| self.conv.float_args.contains(r))
                .filter_map(|r| self.conv.slot(*r))
                .max();
            let upto = |n: usize| {
                if n >= 8 { u8::MAX } else { (1u8 << n) - 1 }
            };
            return match last {
                Some(s) => upto(base + s - self.conv.args.len() + 1) & !upto(base),
                None => 0,
            };
        }
        (0..self.conv.args.len().min(8))
            .filter(|&i| {
                self.conv
                    .float_args
                    .get(i)
                    .is_some_and(|r| self.params.contains(r))
                    && !self
                        .conv
                        .args
                        .get(i)
                        .is_some_and(|r| self.params.contains(r))
            })
            .fold(0u8, |m, i| m | (1 << i))
    }
}

/// Reads what a function takes from its code, its declared signature and
/// its debug information ([`Shape`]).
///
/// The registers are those [`detect_params`] finds, cut at the fixed ones
/// of a variadic function. The stack words are the most the frame scan
/// found, the body reads through the stack pointer followed from the
/// entry ([`stack_params_read`]), or a tail jump hands on to a callee that
/// takes them ([`forwarded_stack`]). A declaration ([`declared_arity`])
/// lists `this`, the hidden result and its parameters: the SDK's prototype
/// for the function's own name fixes the count, an attributed signature
/// sets its least. On a 32-bit target the convention is chosen first, from
/// the registers read under fastcall's, and a declared method is a
/// thiscall whether or not its body reads `ecx`.
///
/// # Arguments
///
/// * `ctx` - The function's context; its convention is set to the one
///   chosen.
/// * `f` - The function.
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
pub(super) fn shape_of(
    ctx: &mut Ctx<'_>,
    f: &Function,
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
    entry: usize,
) -> Shape {
    if ctx.bitness == 32 {
        ctx.conv = &lift::FASTCALL_X86;
        let regs = detect_params(ctx, code, succs, entry);
        ctx.conv = if regs.contains(&Register::EDX) {
            &lift::FASTCALL_X86
        } else if regs.contains(&Register::ECX) {
            &lift::THISCALL_X86
        } else {
            &lift::CDECL_X86
        };
    }
    let mut params = detect_params(ctx, code, succs, entry);
    let fixed = variadic_fixed(ctx, f.entry);
    if let Some(fixed) = fixed {
        params.retain(|r| ctx.conv.slot(*r).is_some_and(|s| s < fixed));
    }
    let used = params
        .iter()
        .filter_map(|r| ctx.conv.param_pos(*r, &params))
        .max()
        .map_or(0, |p| p + 1);
    let stack = f
        .stack_args
        .max(forwarded_stack(ctx, code))
        .max(stack_params_read(ctx, code, succs, entry));
    // INVARIANT: the positions are counted under the convention as it
    // stands when they are counted: a method read as a thiscall below has
    // `this` in `ecx` ahead of its stack words.
    let positions_of = |conv: &Conv, stack: u32| {
        usize::try_from(stack)
            .ok()
            .filter(|n| *n > 0)
            .map_or(0, |n| conv.args.len() + n)
    };
    let hidden = usize::from(f.signature.as_ref().is_some_and(|s| s.by_pointer));
    // INVARIANT: a method's positions are `this`, the hidden result and
    // the declared parameters; the registers read show the first four,
    // and a stack argument the frame scan found shows the rest, so a
    // method with three declared parameters and a hidden result has
    // `this` though only four registers are read. An assert that says
    // `this->` says the same outright.
    let positions = used.max(positions_of(ctx.conv, stack));
    let mut this_param = match &f.signature {
        Some(s) => {
            s.is_const
                || (classes::class_of(&s.name).is_some()
                    && (positions > s.params.len() + hidden
                        || classes::asserts_a_member(ctx.program, ctx.analysis, f.entry)))
        }
        None => {
            let full = name_of(ctx.analysis, ctx.overlay, f.entry);
            let own = classes::class_of(expr::bare(&full));
            own.is_some() && own == f.param_hints.get(&0).map(String::as_str)
        }
    };
    if ctx.bitness == 32 && this_param && std::ptr::eq(ctx.conv, &lift::CDECL_X86) {
        ctx.conv = &lift::THISCALL_X86;
    }
    if std::ptr::eq(ctx.conv, &lift::THISCALL_X86) {
        this_param = true;
    }
    let result_param = (hidden == 1).then_some(u8::from(this_param));
    let lead = usize::from(this_param) + hidden;
    let regs = ctx.conv.args.len();
    let (count, stack, variadic) = match declared_arity(ctx, f, lead) {
        Some((count, floats, variadic, source)) => {
            // INVARIANT: a declared parameter sits in its register at the
            // entry whether or not the body reads it. The SDK's prototype
            // for the function's own name states the arity outright, so a
            // register the body reads past it is no parameter; a signature
            // attributed from a `__FUNCSIG__` text sets the least arity,
            // and a body that reads past it shows the attribution is off,
            // so what it reads stays a parameter and no register reads
            // undefined.
            let count = match source {
                Declaration::Prototype => {
                    params.retain(|r| ctx.conv.slot(*r).is_some_and(|s| s < count));
                    count
                }
                Declaration::Attributed => count
                    .max(used)
                    .max(positions_of(ctx.conv, stack))
                    .max(ctx.debug_params.len()),
            };
            params.extend(
                (0..count.min(ctx.conv.reg_args())).filter_map(|i| ctx.conv.arg_reg(i, floats)),
            );
            params.sort_by_key(|r| (ctx.conv.slot(*r), ctx.conv.args.iter().all(|a| a != r)));
            params.dedup_by_key(|r| ctx.conv.slot(*r));
            (
                count,
                u32::try_from(count.saturating_sub(regs)).unwrap_or(0),
                variadic,
            )
        }
        None if fixed.is_some() => (used.max(lead), 0, true),
        None => (
            used.max(lead)
                .max(positions_of(ctx.conv, stack))
                .max(ctx.debug_params.len()),
            stack,
            false,
        ),
    };
    Shape {
        conv: ctx.conv,
        params,
        variadic,
        this_param,
        result_param,
        count,
        stack,
    }
}

/// Where the arity a function is declared with comes from
/// ([`declared_arity`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Declaration {
    /// The SDK's prototype for the function's own name: exact.
    Prototype,
    /// A `__FUNCSIG__` text attributed to the function by the strings it
    /// references: the least arity, which a wrong attribution understates.
    Attributed,
}

/// Returns the arity a declaration states for a function, when one does.
///
/// The declaration is the function's signature (a `__FUNCSIG__` text
/// attributed to it), else the SDK's prototype for its own name: an export
/// such as kernel32's `SetLastError` is the API it is named after, whatever
/// its one jump shows.
///
/// # Arguments
///
/// * `ctx` - The function's context, for the names and the target.
/// * `f` - The function.
/// * `lead` - Positions before the declared parameters: `this` and the
///   hidden result.
///
/// # Returns
///
/// The positions the declaration lists with the lead, a bit per position
/// passed in a vector register, whether a variable list follows, and where
/// the declaration comes from; on a 32-bit target an SDK prototype counts
/// stack words.
fn declared_arity(
    ctx: &Ctx<'_>,
    f: &Function,
    lead: usize,
) -> Option<(usize, u8, bool, Declaration)> {
    let shifted = |floats: u8| floats.checked_shl(u32::try_from(lead).ok()?);
    match &f.signature {
        Some(s) => {
            let floats = s
                .params
                .iter()
                .take(8)
                .enumerate()
                .filter(|(_, t)| matches!(t.trim(), "float" | "double"))
                .fold(0u8, |m, (j, _)| m | (1 << j));
            Some((
                s.params.len() + lead,
                shifted(floats).unwrap_or(0),
                false,
                Declaration::Attributed,
            ))
        }
        None => {
            let name = name_of(ctx.analysis, ctx.overlay, f.entry);
            let p = crate::analysis::prototypes::declared(expr::bare(&name), ctx.bitness)?;
            Some((
                usize::from(p.params) + lead,
                shifted(p.floats).unwrap_or(0),
                p.variadic,
                Declaration::Prototype,
            ))
        }
    }
}

/// Returns the fixed argument count of a variadic function.
///
/// A variadic function stores every argument register from the first
/// variable one home, which reads them; the fixed ones are its parameters
/// and the rest is `...`. A wrapper that sets no argument register before
/// handing on to a variadic function (`atexit`'s, a logging shim) is as
/// variadic as it, up to four links; one that set any of them hands
/// nothing of its caller's on.
///
/// # Arguments
///
/// * `ctx` - The function's context.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The count, or `None` when the function is not variadic.
fn variadic_fixed(ctx: &Ctx<'_>, entry: u64) -> Option<usize> {
    /// Most wrappers followed to the variadic function.
    const FORWARD_MAX: usize = 4;
    let mut info = InstructionInfoFactory::new();
    let mut at = entry;
    for _ in 0..FORWARD_MAX {
        let l = lift::leading_reads(ctx, &mut info, ctx.conv, at)?;
        if l.fixed.is_some() || !l.written.is_empty() {
            return l.fixed;
        }
        at = l.forward.filter(|n| *n != entry)?;
    }
    None
}

/// Counts the stack words a function hands on to a callee through a tail
/// jump.
///
/// They are the caller's own arguments, above the return address the jump
/// leaves in place, which the callee reads as its parameters: `jmp
/// [__imp_MultiByteToWideChar]` hands on two of its six, so does `if (a1
/// != 0) return f(a1, a2, a3, a4, a5, a6);`.
///
/// # Arguments
///
/// * `ctx` - The function's context, for its block starts and the imports.
/// * `code` - Decoded instructions per block.
///
/// # Returns
///
/// The most words any tail jump's target takes: an import's by its
/// prototype, a function's by its frame scan; zero when none jumps out.
pub(super) fn forwarded_stack(ctx: &Ctx<'_>, code: &[Vec<Instruction>]) -> u32 {
    code.iter()
        .filter_map(|b| b.last())
        .filter(|i| {
            matches!(
                i.flow_control(),
                FlowControl::UnconditionalBranch | FlowControl::IndirectBranch
            )
        })
        .filter_map(lift::static_target)
        .filter(|t| !ctx.block_starts.contains(t))
        .filter_map(|t| match lift::import_prototype(ctx, Some(t)) {
            Some(p) if ctx.bitness == 32 => Some(u32::from(p.stack_params())),
            Some(p) => {
                let total = usize::from(p.params) + usize::from(p.this);
                u32::try_from(total.saturating_sub(ctx.conv.args.len())).ok()
            }
            None => ctx
                .analysis
                .function(t)
                .filter(|g| g.instr_count > 1)
                .map(|g| g.stack_args),
        })
        .max()
        .unwrap_or(0)
}

/// Most stack-passed arguments a body is credited with: the cap discovery's
/// frame scan applies, so the two counts agree.
///
/// A read far above the frame is a corrupt displacement or a table indexed
/// off the stack, not the hundred-thousandth argument; left uncapped, one
/// such read made the signature list every slot up to it (a mutant read
/// one at six hundred thousand words, and the parameter list alone was
/// gigabytes).
pub(super) const STACK_PARAMS_MAX: u32 = 32;

/// Follows the stack pointer from the entry to the start of every block.
///
/// Every move of it is followed while it is known: a push or a pop, an
/// `add`, `sub` or `lea` of a constant, a call whose callee states what it
/// pops ([`lift::stated_pop`]). A block reached at two depths, or after a
/// move nothing states (`and esp, -16`, `mov esp, ebp`, a call through a
/// pointer on a 32-bit target), has no depth.
///
/// # Arguments
///
/// * `ctx` - The function's context, for the convention and the callees.
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
///
/// # Returns
///
/// Per block, how many bytes the stack pointer stands from where it stood
/// at the entry when the block starts, or `None` where that is not known.
pub(super) fn block_depths(
    ctx: &Ctx<'_>,
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
    entry: usize,
) -> Vec<Option<i64>> {
    /// Where the stack pointer stands at a block's start.
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Depth {
        /// No path from the entry reached the block yet.
        Unreached,
        /// This many bytes from where it stood at the entry.
        At(i64),
        /// Paths disagree, or a move nothing states came first.
        Unknown,
    }
    let mut factory = InstructionInfoFactory::new();
    let mut depth = vec![Depth::Unreached; code.len()];
    if let Some(start) = depth.get_mut(entry) {
        *start = Depth::At(0);
    }
    let mut work = vec![entry];
    while let Some(b) = work.pop() {
        let mut sp = match depth.get(b) {
            Some(Depth::At(sp)) => Some(*sp),
            _ => None,
        };
        for i in code.get(b).into_iter().flatten() {
            sp = sp.and_then(|sp| Some(sp + sp_move(ctx, &mut factory, i)?));
        }
        for &s in succs.get(b).into_iter().flatten() {
            let Some(d) = depth.get_mut(s) else { continue };
            *d = match (*d, sp) {
                (Depth::Unreached, Some(sp)) => Depth::At(sp),
                (Depth::At(at), Some(sp)) if at == sp => continue,
                (Depth::Unknown, _) => continue,
                _ => Depth::Unknown,
            };
            work.push(s);
        }
    }
    depth
        .into_iter()
        .map(|d| match d {
            Depth::At(sp) => Some(sp),
            Depth::Unreached | Depth::Unknown => None,
        })
        .collect()
}

/// Counts the stack-passed arguments the body reads through the stack
/// pointer, followed from the entry.
///
/// The frame scan at discovery places each read against the pushes and
/// pops before it in the image, and misses an argument read after a
/// callee popped what was pushed for it. Here the stack pointer is
/// followed through the blocks while every move of it is known
/// ([`block_depths`]), and a block where it is not reads nothing. A slot
/// read above the return address and the shadow space before its
/// block writes it is an argument; the highest one within
/// [`STACK_PARAMS_MAX`] sets the count, and a read beyond that is no
/// argument.
///
/// # Arguments
///
/// * `ctx` - The function's context, for the convention and the callees.
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
///
/// # Returns
///
/// The number of stack arguments read, zero when none is.
pub(super) fn stack_params_read(
    ctx: &Ctx<'_>,
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
    entry: usize,
) -> u32 {
    let mut factory = InstructionInfoFactory::new();
    let depths = block_depths(ctx, code, succs, entry);
    let word = ctx.conv.word;
    let first = word + ctx.conv.shadow;
    let mut most = 0u32;
    for (block, at) in code.iter().zip(&depths) {
        let Some(mut sp) = *at else {
            continue;
        };
        let mut written: BTreeSet<i64> = BTreeSet::new();
        for i in block {
            let operand = (0..i.op_count()).find(|k| i.op_kind(*k) == OpKind::Memory);
            if let Some(k) = operand
                && i.memory_base().full_register() == Register::RSP
                && i.memory_index() == Register::None
            {
                let o = sp + crate::disasm::displacement(i, ctx.bitness);
                match factory.info(i).op_access(k) {
                    OpAccess::Write | OpAccess::CondWrite => {
                        written.insert(o);
                    }
                    OpAccess::Read
                    | OpAccess::CondRead
                    | OpAccess::ReadWrite
                    | OpAccess::ReadCondWrite
                        if o >= first && (o - first) % word == 0 && !written.contains(&o) =>
                    {
                        let n = u32::try_from((o - first) / word + 1).unwrap_or(u32::MAX);
                        if n <= STACK_PARAMS_MAX {
                            most = most.max(n);
                        }
                    }
                    _ => {}
                }
            }
            let Some(moved) = sp_move(ctx, &mut factory, i) else {
                break;
            };
            sp += moved;
        }
    }
    most
}

/// Returns how far an instruction moves the stack pointer, when that is
/// known.
///
/// A push or a pop moves it a word, an `add`, `sub` or `lea` of a
/// constant by the constant, a call by what its callee pops
/// ([`lift::stated_pop`]), and an instruction that leaves it alone not at
/// all.
///
/// # Arguments
///
/// * `ctx` - The function's context, for the callees.
/// * `factory` - Reused instruction-info factory.
/// * `i` - The instruction.
///
/// # Returns
///
/// The bytes added to the stack pointer, or `None` when nothing says.
fn sp_move(ctx: &Ctx<'_>, factory: &mut InstructionInfoFactory, i: &Instruction) -> Option<i64> {
    /// Largest constant an `add` or `sub` is believed to move it by.
    const ADJUST_MAX: i64 = 0x10_0000;
    match i.flow_control() {
        FlowControl::Call | FlowControl::IndirectCall => {
            let target = lift::near_target(i);
            let reached = target.or_else(|| lift::static_target(i));
            return lift::stated_pop(ctx, target, reached).map(i64::from);
        }
        FlowControl::Return => return Some(0),
        _ => {}
    }
    if matches!(i.mnemonic(), Mnemonic::Enter | Mnemonic::Leave) {
        return None;
    }
    if i.is_stack_instruction() {
        return Some(i64::from(i.stack_pointer_increment()));
    }
    let writes_sp = factory.info(i).used_registers().iter().any(|u| {
        u.register().full_register() == Register::RSP
            && matches!(
                u.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            )
    });
    if !writes_sp {
        return Some(0);
    }
    let constant = || {
        i.try_immediate(1)
            .ok()
            .and_then(|v| i64::try_from(v).ok())
            .filter(|v| *v < ADJUST_MAX)
    };
    match i.mnemonic() {
        Mnemonic::Add => constant(),
        Mnemonic::Sub => constant().map(|v| -v),
        Mnemonic::Lea
            if i.memory_base().full_register() == Register::RSP
                && i.memory_index() == Register::None =>
        {
            Some(crate::disasm::displacement(i, ctx.bitness))
        }
        _ => None,
    }
}

/// Returns what a call's callee takes ([`Shape`]), read once per function
/// and overlay through [`Analysis::derived`].
///
/// # Arguments
///
/// * `ctx` - The calling function's context, for the program, the
///   analysis and the overlay.
/// * `target` - The callee's entry.
///
/// # Returns
///
/// The shape, or `None` when no function starts there, the function is an
/// import thunk, whose import's prototype says what it takes, or its whole
/// body is one instruction that hands nothing on to another function (a
/// bare `ret`, a `jmp $`): a body that reads nothing says nothing of what
/// its callers pass.
pub(super) fn callee_shape(ctx: &Ctx<'_>, target: u64) -> Option<std::sync::Arc<Shape>> {
    let forwards = |i: Instruction| {
        lift::near_target(&i)
            .is_some_and(|n| n != target && ctx.analysis.function(n).is_some_and(|g| g.entry == n))
    };
    let f = ctx.analysis.function(target).filter(|f| {
        f.entry == target
            && f.thunk.is_none()
            && (f.instr_count > 1 || ctx.decode(target).is_some_and(forwards))
    })?;
    Some(ctx.analysis.derived.get_or_build_item(
        "shape",
        ctx.overlay_key,
        target,
        || shape_built(ctx.program, ctx.analysis, ctx.overlay, f, ctx.bitness),
        |shape| shape.params.capacity() * size_of::<Register>(),
    ))
}

/// Reads a function's [`Shape`] afresh: its blocks decoded, its context
/// built as its own decompilation builds it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names.
/// * `f` - The function.
/// * `bitness` - Decoder bitness.
pub(super) fn shape_built(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
    bitness: u32,
) -> Shape {
    let idx: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let succs: Vec<Vec<usize>> = f
        .blocks
        .iter()
        .map(|b| {
            b.successors
                .iter()
                .filter_map(|s| idx.get(s).copied())
                .collect()
        })
        .collect();
    let mut ctx = new_ctx(
        program,
        analysis,
        overlay,
        f,
        bitness,
        idx.keys().copied().collect(),
        &[],
    );
    let code = decode_blocks(&ctx, f);
    let entry = idx.get(&f.entry).copied().unwrap_or(0);
    shape_of(&mut ctx, f, &code, &succs, entry)
}

/// Decodes every block of a function, in block order.
///
/// # Arguments
///
/// * `ctx` - The function's context, for the decoder.
/// * `f` - The function.
pub(super) fn decode_blocks(ctx: &Ctx<'_>, f: &Function) -> Vec<Vec<Instruction>> {
    f.blocks
        .iter()
        .map(|b| {
            let mut v = Vec::new();
            let mut va = b.start;
            while va < b.end {
                let Some(i) = ctx.decode(va) else { break };
                va = i.next_ip();
                v.push(i);
            }
            v
        })
        .collect()
}

/// Counts the stack arguments a call's callee reads, when known.
///
/// An import's prototype says; a function in the image says through the
/// slots its body reads; a callee the call reaches through a register or
/// an unknown thunk says nothing.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `instr` - The call.
pub(super) fn call_stack_arity(ctx: &Ctx<'_>, instr: &Instruction) -> Option<usize> {
    let target = lift::static_target(instr)?;
    if let Some(p) = lift::import_prototype(ctx, Some(target)) {
        return Some(usize::from(p.stack_params()));
    }
    let f = ctx.analysis.function(target)?;
    (f.instr_count > 1).then(|| usize::try_from(f.stack_args).unwrap_or(0))
}

/// Detects the function's parameters.
///
/// Calling-convention registers read before being written on some path
/// from the entry that no call precedes (a call clobbers them), whatever
/// the order of the blocks in the image. A slot's
/// argument travels in one register or the other, so where both are read
/// the integer one is taken and the floating-point read is a leftover. A
/// register passed on untouched to a callee or a jump's target that reads
/// it is read by proxy ([`lift::forwarded_reads`]): `this` reaches a
/// method's wrapper through `ecx` the wrapper never names. A push of a
/// register that the next call consumes as one of its arguments reads it
/// too, while a push beyond the callee's arity only makes room.
///
/// # Arguments
///
/// * `ctx` - Convention and bitness.
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
///
/// # Returns
///
/// The registers in convention order.
pub(super) fn detect_params(
    ctx: &Ctx<'_>,
    code: &[Vec<Instruction>],
    succs: &[Vec<usize>],
    entry: usize,
) -> Vec<Register> {
    let mut found: Vec<Register> = Vec::new();
    let mut factory = InstructionInfoFactory::new();
    // INVARIANT: writes are tracked only for the convention's own argument
    // registers, so a register the convention does not pass is not read by
    // proxy either: the first scan, under the widest convention, decides
    // which convention holds, and the second sees only what it passes.
    let forward = |found: &mut Vec<Register>, written: &BTreeSet<Register>, regs: Vec<Register>| {
        for r in regs {
            if ctx.conv.slot(r).is_some() && !written.contains(&r) && !found.contains(&r) {
                found.push(r);
            }
        }
    };
    // INVARIANT: a read counts on any path from the entry that no call
    // precedes, so a register read in a block placed after a call in the
    // image is a parameter when its own path is call-free; each path
    // carries its writes and its pushes, and a block reached again with
    // the same writes is done.
    type Path = (usize, BTreeSet<Register>, Vec<Option<(Register, bool)>>);
    let mut seen: BTreeSet<(usize, BTreeSet<Register>)> = BTreeSet::new();
    let mut work: Vec<Path> = vec![(entry, BTreeSet::new(), Vec::new())];
    while let Some((b, mut written, mut pushed)) = work.pop() {
        if !seen.insert((b, written.clone())) {
            continue;
        }
        let Some(instrs) = code.get(b) else {
            continue;
        };
        let mut stopped = false;
        for instr in instrs {
            // INVARIANT: a push reads its register only when the next call
            // takes the slot as an argument; MSVC reserves a local's slot
            // with `push ecx`, which would otherwise make every such
            // function a method, and a call's arity tells the two apart.
            // The registers a pushed memory operand's address is made of
            // are read whatever the callee takes: `push dword ptr
            // [ecx+38h]` reads `ecx`.
            if instr.mnemonic() == Mnemonic::Push {
                if instr.op0_kind() == OpKind::Memory {
                    for r in [instr.memory_base(), instr.memory_index()] {
                        let r = lift::canon(r, ctx.bitness);
                        if ctx.conv.slot(r).is_some()
                            && !written.contains(&r)
                            && !found.contains(&r)
                        {
                            found.push(r);
                        }
                    }
                }
                let reg = (instr.op0_kind() == OpKind::Register)
                    .then(|| lift::canon(instr.op0_register(), ctx.bitness))
                    .filter(|r| ctx.conv.slot(*r).is_some())
                    .map(|r| (r, written.contains(&r)));
                pushed.push(reg);
                continue;
            }
            if matches!(
                instr.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                let arity = call_stack_arity(ctx, instr).unwrap_or(pushed.len());
                let args: Vec<Register> = pushed
                    .iter()
                    .rev()
                    .take(arity)
                    .filter_map(|p| p.filter(|(_, written)| !written).map(|(r, _)| r))
                    .collect();
                pushed.clear();
                forward(&mut found, &written, args);
                // A stack probe is a call that clobbers nothing, and a
                // compiler emits one in the prologue of any function with a
                // large frame, before the arguments are read. Stopping at it
                // loses every parameter of exactly the functions worth
                // reading.
                if crate::analysis::render::preserves_registers(ctx.analysis, ctx.overlay, instr)
                    || crate::analysis::render::frame_helper(ctx.analysis, ctx.overlay, instr)
                {
                    continue;
                }
                forward(
                    &mut found,
                    &written,
                    lift::forwarded_reads(ctx, &mut factory, instr),
                );
                stopped = true;
                break;
            }
            if matches!(
                instr.flow_control(),
                FlowControl::UnconditionalBranch | FlowControl::IndirectBranch
            ) {
                forward(
                    &mut found,
                    &written,
                    lift::forwarded_reads(ctx, &mut factory, instr),
                );
                continue;
            }
            let info = factory.info(instr);
            let set_only = lift::sets_without_reading(instr)
                .then(|| lift::canon(instr.op0_register(), ctx.bitness));
            let mut writes: Vec<Register> = Vec::new();
            for ur in info.used_registers() {
                let r = lift::canon(ur.register(), ctx.bitness);
                if ctx.conv.slot(r).is_none() {
                    continue;
                }
                match ur.access() {
                    OpAccess::Read | OpAccess::CondRead if set_only == Some(r) => {}
                    OpAccess::ReadWrite | OpAccess::ReadCondWrite if set_only == Some(r) => {
                        writes.push(r);
                    }
                    OpAccess::Read
                    | OpAccess::CondRead
                    | OpAccess::ReadWrite
                    | OpAccess::ReadCondWrite => {
                        if !written.contains(&r) && !found.contains(&r) {
                            found.push(r);
                        }
                        if matches!(ur.access(), OpAccess::ReadWrite) {
                            writes.push(r);
                        }
                    }
                    OpAccess::Write => writes.push(r),
                    OpAccess::CondWrite | OpAccess::None | OpAccess::NoMemAccess => {}
                }
            }
            written.extend(writes);
        }
        if !stopped {
            for &next in succs.get(b).into_iter().flatten() {
                work.push((next, written.clone(), pushed.clone()));
            }
        }
    }
    found.sort_by_key(|r| (ctx.conv.slot(*r), ctx.conv.args.iter().all(|a| a != r)));
    found.dedup_by_key(|r| ctx.conv.slot(*r));
    found
}

/// Tells whether block `b` is where the prologue's register saves happen.
///
/// That is the entry block, and the block right after it when the entry
/// block ends in a call to a frame helper: the compiler saves the callee-saved
/// registers after `__SEH_prolog4` returns, and a call ends a block. The
/// entry block need not be the lowest one.
///
/// # Arguments
///
/// * `ctx` - The analysis and overlay, to name the call's target.
/// * `code` - Decoded instructions per block.
/// * `b` - The block index.
pub(super) fn prologue_block(ctx: &Ctx<'_>, code: &[Vec<Instruction>], b: usize) -> bool {
    let entry = ctx.entry_block;
    b == entry
        || (b == entry + 1
            && code.get(entry).and_then(|c| c.last()).is_some_and(|i| {
                crate::analysis::render::frame_helper(ctx.analysis, ctx.overlay, i)
            }))
}

/// The unsigned integer type of the machine word: what a parameter or a
/// result is when nothing narrower or more specific is known.
///
/// # Arguments
///
/// * `bitness` - Decoder bitness (32 or 64).
pub(super) fn word_type(bitness: u32) -> &'static str {
    if bitness == 32 {
        "uint32_t"
    } else {
        "uint64_t"
    }
}

/// Tells whether the function runs under a structured exception handler.
///
/// A frame helper (`__SEH_prolog4`) does the registration in the callee;
/// an inline prologue stores `esp`, or a frame address, to `fs:[0]`
/// itself. A fragment that discovery split off its function has no
/// prologue, but the unlink it runs before returning, `fs:[0]` restored
/// from the frame, is the same evidence; in a function with a frame of its
/// own, that store alone restores a head the function read.
///
/// # Arguments
///
/// * `ctx` - Names, for the frame helper.
/// * `code` - Decoded instructions per block.
pub(super) fn seh_frame(ctx: &Ctx<'_>, code: &[Vec<Instruction>]) -> bool {
    let registers = |i: &Instruction| {
        lift::is_seh_link(i)
            && i.op1_kind() == OpKind::Register
            && i.op1_register() == Register::ESP
    };
    // INVARIANT: a function that sets up its own frame and links nothing
    // in its entry registers no handler; a later store to `fs:[0]` puts
    // back a head it read (an unwinder calling `RtlUnwind`), the evidence
    // only for a fragment, which has no frame of its own.
    let framed = code.first().is_some_and(|entry| {
        entry.iter().any(|i| {
            i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && i.op0_register() == Register::EBP
                && i.op1_kind() == OpKind::Register
                && i.op1_register() == Register::ESP
        })
    });
    code.first().is_some_and(|entry| {
        entry
            .last()
            .is_some_and(|i| crate::analysis::render::frame_helper(ctx.analysis, ctx.overlay, i))
            || entry.iter().any(registers)
            || (framed && entry.iter().any(lift::is_seh_link))
    }) || (!framed
        && code
            .iter()
            .flatten()
            .any(|i| lift::is_seh_link(i) && !registers(i)))
}

/// Tells whether any non-call instruction writes the return register.
///
/// # Arguments
///
/// * `ctx` - Bitness.
/// * `code` - Decoded instructions per block.
pub(super) fn writes_rax(ctx: &Ctx<'_>, code: &[Vec<Instruction>]) -> bool {
    let rax = lift::canon(Register::RAX, ctx.bitness);
    let mut factory = InstructionInfoFactory::new();
    code.iter().any(|instrs| {
        for instr in instrs {
            if matches!(
                instr.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                continue;
            }
            if factory.info(instr).used_registers().iter().any(|ur| {
                lift::canon(ur.register(), ctx.bitness) == rax
                    && matches!(
                        ur.access(),
                        OpAccess::Write
                            | OpAccess::ReadWrite
                            | OpAccess::CondWrite
                            | OpAccess::ReadCondWrite
                    )
            }) {
                return true;
            }
        }
        false
    })
}
