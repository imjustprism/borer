//! How an unresolved call or jump forms its target, and why discovery
//! left it unresolved, read from the site's own block.

use super::*;
use crate::isa::{Isa, a32, a64, rv};

/// What a register held at a site, as its block shows it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// Nothing the block shows: loaded elsewhere, computed, or passed in.
    Register,
    /// A word loaded from `[R+k]`, with `R` itself loaded earlier in the
    /// block from `[X+0]`, `X` a register that is no stack or frame pointer
    /// and that the block does not set to a fixed address: an object's
    /// first word, its table. `k` is the byte offset.
    Slot(i64),
    /// A word loaded from `[R+k]`, `R` not loaded so in the block.
    Field(i64),
    /// A word loaded from a fixed address.
    Global(u64),
    /// A word loaded through a stack or frame pointer, an index or a
    /// register the block moves: memory, but no object's table and no
    /// fixed slot.
    Memory,
}

/// One blind block's branch sites, each a range of its function's
/// site-sorted pairs.
#[derive(Debug, Clone, Copy)]
pub(super) struct Block<'s> {
    /// Its sites' targets as discovery recorded them ([`super::targets`]).
    pub(super) targets: &'s [(u64, u64)],
    /// Where its sites land ([`super::landings`]).
    pub(super) lands: &'s [(u64, u64)],
}

/// Returns where a blind block's call or jump is, how it forms its target
/// and why discovery left it unresolved.
///
/// The site is the block's last instruction. A call into a trampoline, or
/// through a slot holding one, goes wherever the trampoline's jump reads:
/// its form is that register's at the call, or the fixed slot the
/// trampoline reads.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `b` - The block, one [`super::blind`] holds unresolved.
/// * `sites` - Its branch sites' targets and landings.
/// * `through` - The trampolines.
/// * `jumps` - What each trampoline jumps through ([`jumps`]).
///
/// # Returns
///
/// The site's address, its form and why it is unresolved; `None` when the
/// block ends in a direct call or jump, as its decoder reads it, whose own
/// target is no trampoline's entry: it names its target, which is only
/// not code or not recorded (the per-target reference cap).
pub(super) fn site(
    p: &Program,
    a: &Analysis,
    b: &BasicBlock,
    sites: Block<'_>,
    through: &BTreeSet<u64>,
    jumps: &BTreeMap<u64, Through>,
) -> Option<(u64, Form, Why)> {
    let slot = sites
        .targets
        .iter()
        .map(|&(_, t)| t)
        .find(|t| !is_code(p, a, *t));
    let tramp = sites
        .lands
        .iter()
        .map(|&(_, t)| t)
        .find(|t| through.contains(t));
    let insns = Insns::of(p, b);
    let into = sites.targets.iter().any(|(_, t)| through.contains(t));
    if insns.direct() && !into {
        return None;
    }
    let at = insns
        .last()
        .or_else(|| sites.targets.last().map(|&(s, _)| s))
        .unwrap_or(b.start);
    let why = match (tramp, slot) {
        (Some(t), _) => Why::Trampoline { through: t },
        (None, Some(s)) => Why::SlotFilledAtRunTime { slot: s },
        (None, None) if b.term == BlockTerm::Indirect => Why::NoJumpTable,
        (None, None) => Why::NoTarget,
    };
    let form = match (tramp, slot) {
        (Some(t), _) => match jumps.get(&t) {
            Some(&Through::Slot(g)) => Form::Global { slot: g },
            Some(&Through::Reg(r)) => match insns.held(r) {
                Shape::Slot(k) => slot_form(p, k),
                Shape::Field(k) => Form::Field { offset: k },
                Shape::Memory => Form::Memory,
                Shape::Register | Shape::Global(_) => Form::IntoTrampoline { entry: t },
            },
            None => Form::IntoTrampoline { entry: t },
        },
        (None, Some(s)) => Form::Global { slot: s },
        (None, None) => match insns.operand() {
            Shape::Slot(k) => slot_form(p, k),
            Shape::Field(k) => Form::Field { offset: k },
            Shape::Global(s) => Form::Global { slot: s },
            Shape::Memory => Form::Memory,
            Shape::Register if b.term == BlockTerm::Indirect => Form::Jump,
            Shape::Register => Form::Register,
        },
    };
    Some((at, form, why))
}

/// Returns the form of a load from `[R+k]` with `R` loaded from memory: a
/// vtable slot when `k` is a whole word at or past the table's start, a
/// field otherwise.
///
/// # Arguments
///
/// * `p` - The loaded image, for its word size.
/// * `k` - The byte offset.
fn slot_form(p: &Program, k: i64) -> Form {
    let word = p.arch.bitness().map_or(8, |b| i64::from(b / 8)).max(1);
    match usize::try_from(k / word) {
        Ok(slot) if k % word == 0 => Form::VtableSlot { slot },
        Ok(_) | Err(_) => Form::Field { offset: k },
    }
}

/// A register named the way its instruction set's decoder names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Reg {
    /// An x86 register, by its full width.
    X86(Register),
    /// An arm64 general register.
    A64(a64::Reg),
}

/// What a trampoline's jump reads its target from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Through {
    /// A register its block does not load from a fixed slot: `jmp rax`.
    Reg(Reg),
    /// A slot at a fixed address: `jmp [rip+g]`, or a register loaded
    /// from one in the block.
    Slot(u64),
}

/// Returns what each trampoline jumps on through: `jmp rax`, `br x16`, or
/// a fixed slot; one through other memory is left out.
///
/// Each trampoline's block is decoded once, however many sites call it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `through` - The trampolines.
pub(super) fn jumps(p: &Program, a: &Analysis, through: &BTreeSet<u64>) -> BTreeMap<u64, Through> {
    let via = |entry: u64| {
        let b = a.function(entry)?.blocks.first()?;
        let (reg, held) = match Insns::of(p, b) {
            Insns::X86(bits, list) => {
                let (i, before) = list.split_last()?;
                match i.op0_kind() {
                    OpKind::Register => {
                        let r = i.op0_register().full_register();
                        (Reg::X86(r), x86_held(bits, before, r))
                    }
                    OpKind::Memory => match x86_memory(bits, before, i) {
                        Shape::Global(g) => return Some(Through::Slot(g)),
                        Shape::Register | Shape::Slot(_) | Shape::Field(_) | Shape::Memory => {
                            return None;
                        }
                    },
                    _ => return None,
                }
            }
            Insns::A64(list) => {
                let (i, before) = list.split_last()?;
                let r = a64_reg(i.operands[0])?;
                (Reg::A64(r), a64_held(before, r))
            }
            Insns::Other { .. } => return None,
        };
        Some(match held {
            Shape::Global(g) => Through::Slot(g),
            Shape::Register | Shape::Slot(_) | Shape::Field(_) | Shape::Memory => Through::Reg(reg),
        })
    };
    through.iter().filter_map(|&e| Some((e, via(e)?))).collect()
}

/// A block's instructions, decoded by its instruction set's decoder.
enum Insns {
    /// x86 or x86-64, with the decoder bitness.
    X86(u32, Vec<Instruction>),
    /// arm64.
    A64(Vec<a64::Insn>),
    /// Any other instruction set: only its last instruction.
    Other {
        /// Where it starts.
        last: Option<u64>,
        /// Whether it calls or jumps to an address it names itself.
        direct: bool,
    },
}

impl Insns {
    /// Decodes a block.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image.
    /// * `b` - The block.
    fn of(p: &Program, b: &BasicBlock) -> Insns {
        let len = usize::try_from(b.end.saturating_sub(b.start)).unwrap_or(0);
        match p.arch.isa() {
            Some(Isa::X86 { bits }) => {
                Insns::X86(bits, crate::analysis::functions::decode_block(p, bits, b))
            }
            Some(Isa::A64) => {
                let words = p.read_va_upto(b.start, len).unwrap_or_default();
                let mut va = b.start;
                Insns::A64(
                    words
                        .chunks_exact(a64::INSN_LEN)
                        .map(|w| {
                            let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
                            let i = a64::decode(word, va);
                            va = va.wrapping_add(4);
                            i
                        })
                        .collect(),
                )
            }
            Some(isa @ (Isa::A32 | Isa::Rv(_))) => {
                let mut last = None;
                let code = p.read_va_upto(b.start, len).unwrap_or_default();
                disasm::lengths(p, code, b.start, isa, b.end, len, |at, _| {
                    last = Some(at);
                });
                let direct = last.is_some_and(|at| {
                    let bytes = p.read_va_upto(at, 4).unwrap_or_default();
                    let target = match isa {
                        Isa::Rv(xlen) => rv::decode(bytes, at, xlen).and_then(|i| i.target()),
                        Isa::A32 => {
                            let it = &mut a32::ItState::default();
                            a32::decode(bytes, at, p.modes.at(at), it).and_then(|i| i.target())
                        }
                        Isa::A64 | Isa::X86 { .. } => None,
                    };
                    target.is_some()
                });
                Insns::Other { last, direct }
            }
            None => Insns::Other {
                last: None,
                direct: false,
            },
        }
    }

    /// Returns where the block's last instruction starts.
    fn last(&self) -> Option<u64> {
        match self {
            Insns::X86(_, list) => list.last().map(Instruction::ip),
            Insns::A64(list) => list.last().map(|i| i.va),
            Insns::Other { last, .. } => *last,
        }
    }

    /// Tells whether the block's last instruction calls or jumps to an
    /// address it names itself.
    fn direct(&self) -> bool {
        match self {
            Insns::X86(_, list) => list.last().is_some_and(|i| {
                matches!(
                    i.op0_kind(),
                    OpKind::NearBranch16
                        | OpKind::NearBranch32
                        | OpKind::NearBranch64
                        | OpKind::FarBranch16
                        | OpKind::FarBranch32
                )
            }),
            Insns::A64(list) => list
                .last()
                .is_some_and(|i| matches!(i.operands[0], a64::Opnd::PcRel(_))),
            Insns::Other { direct, .. } => *direct,
        }
    }

    /// Returns the shape of the target the block's last instruction calls
    /// or jumps to.
    fn operand(&self) -> Shape {
        match self {
            Insns::X86(bits, list) => {
                list.split_last()
                    .map_or(Shape::Register, |(i, before)| match i.op0_kind() {
                        OpKind::Memory => x86_memory(*bits, before, i),
                        OpKind::Register => {
                            x86_held(*bits, before, i.op0_register().full_register())
                        }
                        _ => Shape::Register,
                    })
            }
            Insns::A64(list) => list.split_last().map_or(Shape::Register, |(i, before)| {
                a64_reg(i.operands[0]).map_or(Shape::Register, |r| a64_held(before, r))
            }),
            Insns::Other { .. } => Shape::Register,
        }
    }

    /// Returns what a register holds at the block's last instruction.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn held(&self, r: Reg) -> Shape {
        match (self, r) {
            (Insns::X86(bits, list), Reg::X86(r)) => list
                .split_last()
                .map_or(Shape::Register, |(_, before)| x86_held(*bits, before, r)),
            (Insns::A64(list), Reg::A64(r)) => list
                .split_last()
                .map_or(Shape::Register, |(_, before)| a64_held(before, r)),
            (Insns::X86(..) | Insns::A64(_) | Insns::Other { .. }, _) => Shape::Register,
        }
    }
}

/// Returns what an x86 register holds after `before`: the shape of the
/// memory its last writer loaded it from, when that writer is a load.
///
/// # Arguments
///
/// * `bits` - Decoder bitness.
/// * `before` - The instructions before the use, in order.
/// * `r` - The register, by its full width.
fn x86_held(bits: u32, before: &[Instruction], r: Register) -> Shape {
    let mut factory = InstructionInfoFactory::new();
    let Some(at) = before.iter().rposition(|i| reg_touch(&mut factory, i, r).1) else {
        return Shape::Register;
    };
    let w = &before[at];
    let loads = w.mnemonic() == Mnemonic::Mov
        && w.op0_kind() == OpKind::Register
        && w.op1_kind() == OpKind::Memory;
    if loads {
        x86_memory(bits, &before[..at], w)
    } else {
        Shape::Register
    }
}

/// Returns the shape of an x86 instruction's memory operand.
///
/// # Arguments
///
/// * `bits` - Decoder bitness.
/// * `before` - The instructions before it in its block, in order.
/// * `i` - The instruction.
fn x86_memory(bits: u32, before: &[Instruction], i: &Instruction) -> Shape {
    if i.is_ip_rel_memory_operand() {
        return Shape::Global(i.ip_rel_memory_address());
    }
    let (base, k) = (i.memory_base(), disasm::displacement(i, bits));
    match (base, i.memory_index()) {
        (Register::None, Register::None) => Shape::Global(i.memory_displacement64()),
        (_, Register::None) if !is_frame(base) => {
            if x86_loaded(before, base.full_register()) {
                Shape::Slot(k)
            } else {
                Shape::Field(k)
            }
        }
        _ => Shape::Memory,
    }
}

/// Tells whether an x86 register is a stack or frame pointer, through
/// which a word is a local, never an object's table.
///
/// # Arguments
///
/// * `r` - The register.
fn is_frame(r: Register) -> bool {
    matches!(
        r.full_register(),
        Register::RSP | Register::RBP | Register::ESP | Register::EBP
    )
}

/// Tells whether an x86 register's last writer in `before` loads it from
/// an object's first word.
///
/// That is `[X+0]`, `X` a register that is no stack or frame pointer,
/// with no index, which the block does not set to a fixed address
/// ([`x86_fixed`]).
///
/// # Arguments
///
/// * `before` - The instructions, in order.
/// * `r` - The register, by its full width.
fn x86_loaded(before: &[Instruction], r: Register) -> bool {
    let mut factory = InstructionInfoFactory::new();
    let Some(at) = before.iter().rposition(|i| reg_touch(&mut factory, i, r).1) else {
        return false;
    };
    let w = &before[at];
    w.mnemonic() == Mnemonic::Mov
        && w.op0_kind() == OpKind::Register
        && w.op1_kind() == OpKind::Memory
        && !w.is_ip_rel_memory_operand()
        && w.memory_base() != Register::None
        && w.memory_index() == Register::None
        && w.memory_displacement64() == 0
        && !is_frame(w.memory_base())
        && !x86_fixed(&before[..at], w.memory_base().full_register())
}

/// Tells whether an x86 register's last writer in `before` sets it to a
/// fixed address: `lea r, [rip+g]`, `lea r, [g]` or `mov r, imm`.
///
/// # Arguments
///
/// * `before` - The instructions, in order.
/// * `r` - The register, by its full width.
fn x86_fixed(before: &[Instruction], r: Register) -> bool {
    let mut factory = InstructionInfoFactory::new();
    before
        .iter()
        .rfind(|i| reg_touch(&mut factory, i, r).1)
        .is_some_and(|w| match w.mnemonic() {
            Mnemonic::Lea => {
                w.is_ip_rel_memory_operand()
                    || (w.memory_base() == Register::None && w.memory_index() == Register::None)
            }
            Mnemonic::Mov => crate::analysis::is_imm(w.op1_kind()),
            _ => false,
        })
}

/// Returns what an arm64 register holds after `before`, read as
/// [`x86_held`] reads an x86 one.
///
/// `ldr x8, [x0]; ldr x8, [x8, #8]` is a slot, `ldr x8, [x0, #16]; ldr
/// x8, [x8, #8]` a field, `adrp x8, page; ldr x8, [x8, #off]` a global, a
/// load through `sp`, an index or a moving base memory.
///
/// # Arguments
///
/// * `before` - The instructions before the use, in order.
/// * `r` - The register.
fn a64_held(before: &[a64::Insn], r: a64::Reg) -> Shape {
    let Some(at) = a64_writer(before, r) else {
        return Shape::Register;
    };
    let (w, earlier) = (&before[at], &before[..at]);
    let word = |i: &a64::Insn| matches!(i.mnemonic, a64::Mnemonic::Ldr(a64::Width::Reg));
    if !word(w) {
        return Shape::Register;
    }
    if let a64::Opnd::PcRel(slot) = w.operands[1] {
        return Shape::Global(slot);
    }
    let a64::Opnd::Mem(m) = w.operands[1] else {
        return Shape::Register;
    };
    if m.index.is_some() || m.mode != a64::Mode::Offset || m.base == a64::Reg::Sp {
        return Shape::Memory;
    }
    let Some(j) = a64_writer(earlier, m.base) else {
        return Shape::Field(m.disp);
    };
    let b = &earlier[j];
    if let a64::Opnd::Mem(n) = b.operands[1]
        && word(b)
        && n.base != a64::Reg::Sp
        && n.index.is_none()
        && n.mode == a64::Mode::Offset
        && n.disp == 0
        && !a64_fixed(&earlier[..j], n.base)
    {
        return Shape::Slot(m.disp);
    }
    if let a64::Opnd::PcRel(page) = b.operands[1]
        && b.op == a64::Op::Adrp
    {
        return Shape::Global(page.wrapping_add_signed(m.disp));
    }
    Shape::Field(m.disp)
}

/// Tells whether an arm64 register's last writer in `before` sets it to a
/// fixed address.
///
/// That is `adrp` or `adr`, or an `add` to a register one of those set.
///
/// # Arguments
///
/// * `before` - The instructions, in order.
/// * `r` - The register.
fn a64_fixed(before: &[a64::Insn], r: a64::Reg) -> bool {
    let page = |i: &a64::Insn| matches!(i.op, a64::Op::Adrp | a64::Op::Adr);
    let Some(at) = a64_writer(before, r) else {
        return false;
    };
    let w = &before[at];
    page(w)
        || (w.mnemonic == a64::Mnemonic::Add
            && a64_reg(w.operands[1])
                .and_then(|src| a64_writer(&before[..at], src))
                .is_some_and(|k| page(&before[k])))
}

/// Returns the general register an arm64 operand names, if it names one.
///
/// # Arguments
///
/// * `o` - The operand.
fn a64_reg(o: a64::Opnd) -> Option<a64::Reg> {
    match o {
        a64::Opnd::Reg { reg, .. } => Some(reg),
        a64::Opnd::None
        | a64::Opnd::Shifted { .. }
        | a64::Opnd::Imm(_)
        | a64::Opnd::PcRel(_)
        | a64::Opnd::Mem(_)
        | a64::Opnd::Cond(_)
        | a64::Opnd::Other => None,
    }
}

/// Returns the index of the last instruction in `before` that writes an
/// arm64 register.
///
/// # Arguments
///
/// * `before` - The instructions, in order.
/// * `r` - The register.
fn a64_writer(before: &[a64::Insn], r: a64::Reg) -> Option<usize> {
    before
        .iter()
        .rposition(|i| i.registers().writes.contains(&r))
}
