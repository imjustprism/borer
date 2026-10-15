//! The constants an arm64 function forms in its registers, and the data
//! and slots they reference.
//!
//! arm64 code names an address in two instructions: `adrp` puts the 4 KiB
//! page in a register and an `add` or a load or store adds the offset in
//! the page, often several instructions later, sometimes in another block.
//! [`Tracker`] follows the constants each register holds forward through a
//! function's blocks: `adrp` and `adr` set one ([`Val::Addr`]), an `add` of
//! an immediate carries it, a `mov` copies it, a 64-bit load from a known
//! address leaves the slot's contents ([`Val::Loaded`]), a call clobbers
//! what the procedure call standard lets a callee change (`x0` to `x18`
//! and `x30`), and every other write forgets the register. Where two paths
//! meet, a register keeps its constant only when both bring the same one.
//!
//! [`index`] reads the references off the tracked constants: an `adr`, an
//! `add` forming an address and a load or store at a known address are data
//! references ([`RefKind::Data`]), a load indexed by a register from a known
//! base names a table ([`RefKind::Index`]), a literal load names its
//! literal, and `blr` or `br` through a register loaded from a known slot
//! calls or jumps through that slot ([`RefKind::Call`], [`RefKind::Jmp`]),
//! which is how code calls an import without a stub. [`calls`] reads, at
//! each call, where its first argument registers got their values.

use std::collections::BTreeMap;

use super::discover::Text;
use crate::analysis::functions::push_site;
use crate::analysis::objc::{Arg, Call, Callee, falls_through};
use crate::analysis::{BasicBlock, Function, RefKind, RefSite, striped};
use crate::isa::a64::{self, Insn, Mem, Mnemonic, Mode, Op, Opnd, Reg, Shift, Width};
use crate::program::Program;

/// General-purpose registers tracked: `x0` to `x30`.
const REGS: usize = 31;
/// The registers a call may change, as bits by register number: `x0` to
/// `x18` (the arguments, the results, the scratch and platform registers)
/// and `x30`, the return address.
///
/// SPEC: Procedure Call Standard for the Arm 64-bit Architecture (IHI
/// 0055) 6.1.1: `r19` to `r29` are callee-saved, the rest are not.
const CALL_CLOBBERS: u32 = 0x4007_ffff;
/// Every tracked register, as bits by register number.
const ALL: u32 = 0x7fff_ffff;
/// Most passes over one function's blocks before the tracker settles for
/// what it has: real code settles in a few, and the cap keeps a hostile
/// graph from looping.
const PASSES_MAX: usize = 64;

/// What a register is known to hold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Val {
    /// An address the function formed: an `adrp` page, an `adr` address,
    /// or one of them plus constants.
    Addr(u64),
    /// The 64-bit value a load read from this address: a slot's contents,
    /// such as an import's address.
    Loaded(u64),
}

/// The constants the registers hold before one instruction, by register
/// number; `None` where nothing is known.
pub(super) type Regs = [Option<Val>; REGS];

/// The constants every block of one function starts with, once settled.
pub(super) struct Tracker<'a> {
    /// The function's instructions, in address order.
    insns: &'a [Insn],
    /// Its blocks, in address order.
    blocks: &'a [BasicBlock],
    /// The registers at the start of each block, by block index.
    entry: Vec<Regs>,
    /// The registers at the end of each block reached, by block index.
    exit: Vec<Option<Regs>>,
    /// The blocks leading to each block, by block index.
    preds: Vec<Vec<usize>>,
}

impl<'a> Tracker<'a> {
    /// Settles the constants at the start of every block.
    ///
    /// The first block and every block no block of the function leads to
    /// start knowing nothing; every other block starts with what its
    /// predecessors reached so far agree on, pass after pass until nothing
    /// changes or [`PASSES_MAX`] passes ran.
    ///
    /// # Arguments
    ///
    /// * `insns` - The function's instructions, in address order.
    /// * `blocks` - Its blocks, in address order, their successors by
    ///   start address.
    pub(super) fn new(insns: &'a [Insn], blocks: &'a [BasicBlock]) -> Self {
        let index = |va: u64| blocks.binary_search_by_key(&va, |b| b.start).ok();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); blocks.len()];
        for (k, b) in blocks.iter().enumerate() {
            for s in b.successors.iter().filter_map(|&s| index(s)) {
                if let Some(p) = preds.get_mut(s)
                    && !p.contains(&k)
                {
                    p.push(k);
                }
            }
        }
        let mut entry: Vec<Option<Regs>> = preds
            .iter()
            .enumerate()
            .map(|(k, p)| (k == 0 || p.is_empty()).then_some([None; REGS]))
            .collect();
        let mut exit: Vec<Option<Regs>> = vec![None; blocks.len()];
        for _ in 0..PASSES_MAX {
            let mut changed = false;
            for (k, b) in blocks.iter().enumerate() {
                if k > 0 && !preds[k].is_empty() {
                    let joined = preds[k]
                        .iter()
                        .filter_map(|&p| exit.get(p).copied().flatten())
                        .reduce(|a, r| join(&a, &r));
                    if joined.is_some() {
                        entry[k] = joined;
                    }
                }
                let Some(mut regs) = entry[k] else {
                    continue;
                };
                for i in block_insns(insns, b) {
                    step(&mut regs, i, &mut |_, _| {});
                }
                if exit[k] != Some(regs) {
                    exit[k] = Some(regs);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Tracker {
            insns,
            blocks,
            entry: entry
                .into_iter()
                .map(|r| r.unwrap_or([None; REGS]))
                .collect(),
            exit,
            preds,
        }
    }

    /// Returns the constants the registers hold right before `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - An instruction of the function.
    ///
    /// # Returns
    ///
    /// The registers, or `None` when no block holds `va`.
    pub(super) fn before(&self, va: u64) -> Option<Regs> {
        let k = self
            .blocks
            .partition_point(|b| b.start <= va)
            .checked_sub(1)?;
        let b = self.blocks.get(k).filter(|b| va < b.end)?;
        let mut regs = *self.entry.get(k)?;
        for i in block_insns(self.insns, b).iter().take_while(|i| i.va < va) {
            step(&mut regs, i, &mut |_, _| {});
        }
        Some(regs)
    }

    /// Calls `found` with every reference the function's instructions make
    /// through the constants: target, site and kind.
    ///
    /// A `blr` or `br` whose register the paths into its block load from
    /// different slots, as when a compiler merges the call that ends each
    /// path, calls or jumps through each of those slots.
    ///
    /// # Arguments
    ///
    /// * `found` - Called once per reference, in block then address order.
    fn refs(&self, found: &mut dyn FnMut(u64, u64, RefKind)) {
        for (k, (b, start)) in self.blocks.iter().zip(&self.entry).enumerate() {
            let mut regs = *start;
            let mut written = 0u32;
            for i in block_insns(self.insns, b) {
                if let (Op::Blr | Op::Br, Some(r)) = (i.op, any_reg(&i.operands[0]))
                    && value(&regs, Some(r)).is_none()
                    && written & (1u32 << r) == 0
                {
                    let kind = if i.op == Op::Blr {
                        RefKind::Call
                    } else {
                        RefKind::Jmp
                    };
                    for slot in self.slots_into(k, r) {
                        found(slot, i.va, kind);
                    }
                }
                step(&mut regs, i, &mut |target, kind| found(target, i.va, kind));
                written |= writes(i);
            }
        }
    }

    /// Returns the slots the paths into a block load a register from, when
    /// every path loads it from one.
    ///
    /// # Arguments
    ///
    /// * `k` - The block's index.
    /// * `r` - The register's number.
    ///
    /// # Returns
    ///
    /// The slots, sorted and distinct; empty when a path brings anything
    /// else or the block has no predecessor.
    fn slots_into(&self, k: usize, r: usize) -> Vec<u64> {
        let mut slots = Vec::new();
        for &p in self.preds.get(k).map_or(&[][..], Vec::as_slice) {
            let Some(Val::Loaded(slot)) = self
                .exit
                .get(p)
                .copied()
                .flatten()
                .and_then(|e| e.get(r).copied().flatten())
            else {
                return Vec::new();
            };
            slots.push(slot);
        }
        slots.sort_unstable();
        slots.dedup();
        slots
    }
}

/// Returns the instructions of one block.
///
/// # Arguments
///
/// * `insns` - The function's instructions, in address order.
/// * `b` - The block.
fn block_insns<'i>(insns: &'i [Insn], b: &BasicBlock) -> &'i [Insn] {
    let lo = insns.partition_point(|i| i.va < b.start);
    let hi = insns.partition_point(|i| i.va < b.end);
    insns.get(lo..hi).unwrap_or_default()
}

/// Returns what two paths agree the registers hold.
///
/// # Arguments
///
/// * `a` - The registers one path brings.
/// * `b` - The registers the other brings.
fn join(a: &Regs, b: &Regs) -> Regs {
    let mut out = *a;
    for (o, r) in out.iter_mut().zip(b) {
        if o != r {
            *o = None;
        }
    }
    out
}

/// Returns the number of a general-purpose register `x0`..`x30`.
///
/// # Arguments
///
/// * `reg` - The register.
///
/// # Returns
///
/// The number, or `None` for `sp`, the zero register and a `v` register.
pub(super) fn gpr(reg: Reg) -> Option<usize> {
    match reg {
        Reg::X(n) => Some(usize::from(n)).filter(|&n| n < REGS),
        Reg::Sp | Reg::Zr | Reg::V(_) => None,
    }
}

/// Returns the general-purpose register an operand reads whole, as 64
/// bits and unshifted.
///
/// # Arguments
///
/// * `o` - The operand.
///
/// # Returns
///
/// The register number, or `None` when the operand is anything else.
pub(super) fn x_reg(o: &Opnd) -> Option<usize> {
    match *o {
        Opnd::Reg { reg, bits: 64 }
        | Opnd::Shifted {
            reg,
            bits: 64,
            shift: Shift::Lsl,
            amount: 0,
        } => gpr(reg),
        Opnd::None
        | Opnd::Reg { .. }
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    }
}

/// Returns the general-purpose register an operand names, at any width.
///
/// # Arguments
///
/// * `o` - The operand.
///
/// # Returns
///
/// The register number, or `None` when the operand names none.
pub(super) fn any_reg(o: &Opnd) -> Option<usize> {
    match *o {
        Opnd::Reg { reg, .. } | Opnd::Shifted { reg, .. } => gpr(reg),
        Opnd::None | Opnd::Imm(_) | Opnd::PcRel(_) | Opnd::Mem(_) | Opnd::Cond(_) | Opnd::Other => {
            None
        }
    }
}

/// Returns the instruction's memory operand.
///
/// # Arguments
///
/// * `insn` - The instruction.
pub(super) fn mem(insn: &Insn) -> Option<Mem> {
    insn.operands.iter().find_map(|o| match *o {
        Opnd::Mem(m) => Some(m),
        Opnd::None
        | Opnd::Reg { .. }
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    })
}

/// Returns the address a PC-relative operand of a data instruction names.
///
/// # Arguments
///
/// * `insn` - The instruction.
fn pc_rel(insn: &Insn) -> Option<u64> {
    insn.operands.iter().find_map(|o| match *o {
        Opnd::PcRel(at) => Some(at),
        Opnd::None
        | Opnd::Reg { .. }
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    })
}

/// Returns the general-purpose registers an instruction may write, as bits
/// by register number.
///
/// A call writes what a callee may change ([`CALL_CLOBBERS`]). A store, a
/// compare, a prefetch, a barrier and a branch write nothing but a
/// written-back base; a store-exclusive writes its status, a pair load its
/// two registers, an atomic the old value; a memory instruction the engine
/// does not class is taken to write every register it names; and every
/// other instruction writes its first operand, the destination of every
/// A64 data-processing instruction. A word the decoder does not model
/// (SVE, SME) may write any register; pointer authentication leaves its
/// register's value as it is.
///
/// # Arguments
///
/// * `insn` - The instruction.
pub(super) fn writes(insn: &Insn) -> u32 {
    let bit = |k: usize| {
        insn.operands
            .get(k)
            .and_then(any_reg)
            .map_or(0, |n| 1u32 << n)
    };
    let writeback = mem(insn)
        .filter(|m| matches!(m.mode, Mode::PreIndex | Mode::PostIndex))
        .and_then(|m| gpr(m.base))
        .map_or(0, |n| 1u32 << n);
    match insn.op {
        Op::B
        | Op::BCond(_)
        | Op::Cbz
        | Op::Cbnz
        | Op::Tbz
        | Op::Tbnz
        | Op::Br
        | Op::Ret
        | Op::Eret
        | Op::Trap
        | Op::Nop
        | Op::Bti
        | Op::Pac
        | Op::Invalid => 0,
        Op::Bl | Op::Blr | Op::Syscall => CALL_CLOBBERS,
        Op::Sve | Op::Sme => ALL,
        Op::Adr | Op::Adrp => bit(0),
        Op::Other => match insn.mnemonic {
            Mnemonic::Str(_)
            | Mnemonic::Stp
            | Mnemonic::Prfm
            | Mnemonic::Barrier
            | Mnemonic::Msr
            | Mnemonic::Ccmp
            | Mnemonic::Ccmn
            // INVARIANT: the floating-point compares write the flags only.
            | Mnemonic::Fcmp
            | Mnemonic::Fcmpe
            | Mnemonic::Fccmp
            | Mnemonic::Ld1
            | Mnemonic::St1 => writeback,
            Mnemonic::Stxr(_) | Mnemonic::Stxp | Mnemonic::Cas(_) => bit(0) | writeback,
            Mnemonic::Ldp(_) => bit(0) | bit(1) | writeback,
            Mnemonic::Atomic(..) => bit(1),
            Mnemonic::Other if mem(insn).is_some() => (0..insn.operands.len())
                .map(bit)
                .fold(writeback, |acc, b| acc | b),
            Mnemonic::Svc => CALL_CLOBBERS,
            Mnemonic::Movz
            | Mnemonic::Movn
            | Mnemonic::Movk
            | Mnemonic::Add
            | Mnemonic::Adds
            | Mnemonic::Sub
            | Mnemonic::Subs
            | Mnemonic::Adc
            | Mnemonic::Adcs
            | Mnemonic::Sbc
            | Mnemonic::Sbcs
            | Mnemonic::And
            | Mnemonic::Ands
            | Mnemonic::Orr
            | Mnemonic::Orn
            | Mnemonic::Eor
            | Mnemonic::Eon
            | Mnemonic::Bic
            | Mnemonic::Bics
            | Mnemonic::Ubfm
            | Mnemonic::Sbfm
            | Mnemonic::Bfm
            | Mnemonic::Extr
            | Mnemonic::Lslv
            | Mnemonic::Lsrv
            | Mnemonic::Asrv
            | Mnemonic::Rorv
            | Mnemonic::Madd
            | Mnemonic::Msub
            | Mnemonic::Smaddl
            | Mnemonic::Smsubl
            | Mnemonic::Umaddl
            | Mnemonic::Umsubl
            | Mnemonic::Smulh
            | Mnemonic::Umulh
            | Mnemonic::Udiv
            | Mnemonic::Sdiv
            | Mnemonic::Clz
            | Mnemonic::Cls
            | Mnemonic::Rbit
            | Mnemonic::Rev
            | Mnemonic::Rev16
            | Mnemonic::Rev32
            | Mnemonic::Csel
            | Mnemonic::Csinc
            | Mnemonic::Csinv
            | Mnemonic::Csneg
            | Mnemonic::Ldr(_)
            | Mnemonic::Fmov
            | Mnemonic::Fadd
            | Mnemonic::Fsub
            | Mnemonic::Fmul
            | Mnemonic::Fdiv
            | Mnemonic::Fsqrt
            | Mnemonic::Fabs
            | Mnemonic::Fneg
            | Mnemonic::Fmax
            | Mnemonic::Fmin
            | Mnemonic::Fcsel
            | Mnemonic::Scvtf
            | Mnemonic::Ucvtf
            | Mnemonic::Fcvtzs
            | Mnemonic::Fcvtzu
            | Mnemonic::Fcvt
            | Mnemonic::Dup
            | Mnemonic::Mul
            | Mnemonic::Neg
            | Mnemonic::Abs
            | Mnemonic::Movi
            | Mnemonic::Mvni
            | Mnemonic::Mrs
            | Mnemonic::Other => bit(0) | writeback,
        },
    }
}

/// Returns the constant a register holds after a run of instructions, as
/// a `movz` into it set it: where an `svc #0` reads its number from.
///
/// # Arguments
///
/// * `insns` - The instructions, in order.
/// * `reg` - The register's number.
///
/// # Returns
///
/// The value, or `None` when no `movz` set it or an instruction after the
/// last one may have changed it.
pub(crate) fn constant_in(insns: &[Insn], reg: usize) -> Option<u64> {
    let bit = 1u32.checked_shl(u32::try_from(reg).ok()?)?;
    let mut value = None;
    for insn in insns.iter().filter(|i| writes(i) & bit != 0) {
        value = (insn.mnemonic == Mnemonic::Movz && any_reg(&insn.operands[0]) == Some(reg)).then(
            || {
                // SPEC: Arm ARM (DDI 0487) C6.2 MOVZ: imm16 is bits 5..20 and hw bits 21..22, shifting by hw * 16.
                u64::from((insn.word >> 5) & 0xffff) << (((insn.word >> 21) & 3) * 16)
            },
        );
    }
    value
}

/// Applies one instruction to the registers, reporting each reference it
/// makes through them.
///
/// # Arguments
///
/// * `regs` - The registers before the instruction; after it on return.
/// * `insn` - The instruction.
/// * `found` - Called with the target and kind of each reference.
fn step(regs: &mut Regs, insn: &Insn, found: &mut dyn FnMut(u64, RefKind)) {
    let dst = insn.operands[0];
    let set = match insn.op {
        Op::Adrp => x_reg(&dst)
            .zip(pc_rel(insn))
            .map(|(d, page)| (d, Val::Addr(page))),
        Op::Adr => pc_rel(insn).and_then(|at| {
            found(at, RefKind::Data);
            x_reg(&dst).map(|d| (d, Val::Addr(at)))
        }),
        Op::Blr | Op::Br => {
            if let Some(Val::Loaded(slot)) = value(regs, any_reg(&dst)) {
                let kind = if insn.op == Op::Blr {
                    RefKind::Call
                } else {
                    RefKind::Jmp
                };
                found(slot, kind);
            }
            None
        }
        Op::Other => data(regs, insn, found),
        Op::B
        | Op::BCond(_)
        | Op::Cbz
        | Op::Cbnz
        | Op::Tbz
        | Op::Tbnz
        | Op::Bl
        | Op::Ret
        | Op::Eret
        | Op::Trap
        | Op::Syscall
        | Op::Nop
        | Op::Bti
        | Op::Pac
        | Op::Sve
        | Op::Sme
        | Op::Invalid => None,
    };
    let mask = writes(insn);
    for (n, r) in regs.iter_mut().enumerate() {
        if mask & (1u32 << n) != 0 {
            *r = None;
        }
    }
    if let Some((d, v)) = set
        && let Some(r) = regs.get_mut(d)
    {
        *r = Some(v);
    }
}

/// Returns what a register is known to hold.
///
/// # Arguments
///
/// * `regs` - The registers.
/// * `n` - The register number, when there is one.
fn value(regs: &Regs, n: Option<usize>) -> Option<Val> {
    n.and_then(|n| regs.get(n).copied().flatten())
}

/// Applies a data-processing or memory instruction ([`Op::Other`]),
/// reporting its references.
///
/// # Arguments
///
/// * `regs` - The registers before the instruction.
/// * `insn` - The instruction.
/// * `found` - Called with the target and kind of each reference.
///
/// # Returns
///
/// The register the instruction sets to a known constant and the
/// constant, when it does.
fn data(regs: &Regs, insn: &Insn, found: &mut dyn FnMut(u64, RefKind)) -> Option<(usize, Val)> {
    let [dst, src, third, _] = insn.operands;
    let loaded = |at: u64| {
        x_reg(&dst)
            .filter(|_| insn.mnemonic == Mnemonic::Ldr(Width::Reg))
            .map(|d| (d, Val::Loaded(at)))
    };
    match insn.mnemonic {
        Mnemonic::Add => {
            let (Some(Val::Addr(v)), Opnd::Imm(imm)) = (value(regs, x_reg(&src)), third) else {
                return None;
            };
            let at = v.wrapping_add(imm);
            found(at, RefKind::Data);
            x_reg(&dst).map(|d| (d, Val::Addr(at)))
        }
        Mnemonic::Orr => {
            let (Some(d), Opnd::Reg { reg: Reg::Zr, .. }) = (x_reg(&dst), src) else {
                return None;
            };
            value(regs, x_reg(&third)).map(|v| (d, v))
        }
        Mnemonic::Ldr(_) => match pc_rel(insn) {
            Some(at) => {
                found(at, RefKind::Data);
                loaded(at)
            }
            None => access(regs, insn, found).and_then(loaded),
        },
        Mnemonic::Str(_)
        | Mnemonic::Ldp(_)
        | Mnemonic::Stp
        | Mnemonic::Stxr(_)
        | Mnemonic::Stxp
        | Mnemonic::Atomic(..)
        | Mnemonic::Cas(_)
        | Mnemonic::Ld1
        | Mnemonic::St1
        | Mnemonic::Other => {
            match pc_rel(insn) {
                Some(at) => found(at, RefKind::Data),
                None => {
                    access(regs, insn, found);
                }
            }
            None
        }
        Mnemonic::Movz
        | Mnemonic::Movn
        | Mnemonic::Movk
        | Mnemonic::Adds
        | Mnemonic::Sub
        | Mnemonic::Subs
        | Mnemonic::Adc
        | Mnemonic::Adcs
        | Mnemonic::Sbc
        | Mnemonic::Sbcs
        | Mnemonic::And
        | Mnemonic::Ands
        | Mnemonic::Orn
        | Mnemonic::Eor
        | Mnemonic::Eon
        | Mnemonic::Bic
        | Mnemonic::Bics
        | Mnemonic::Ubfm
        | Mnemonic::Sbfm
        | Mnemonic::Bfm
        | Mnemonic::Extr
        | Mnemonic::Lslv
        | Mnemonic::Lsrv
        | Mnemonic::Asrv
        | Mnemonic::Rorv
        | Mnemonic::Madd
        | Mnemonic::Msub
        | Mnemonic::Smaddl
        | Mnemonic::Smsubl
        | Mnemonic::Umaddl
        | Mnemonic::Umsubl
        | Mnemonic::Smulh
        | Mnemonic::Umulh
        | Mnemonic::Udiv
        | Mnemonic::Sdiv
        | Mnemonic::Clz
        | Mnemonic::Cls
        | Mnemonic::Rbit
        | Mnemonic::Rev
        | Mnemonic::Rev16
        | Mnemonic::Rev32
        | Mnemonic::Csel
        | Mnemonic::Csinc
        | Mnemonic::Csinv
        | Mnemonic::Csneg
        | Mnemonic::Ccmp
        | Mnemonic::Ccmn
        | Mnemonic::Prfm
        | Mnemonic::Fmov
        | Mnemonic::Fadd
        | Mnemonic::Fsub
        | Mnemonic::Fmul
        | Mnemonic::Fdiv
        | Mnemonic::Fsqrt
        | Mnemonic::Fabs
        | Mnemonic::Fneg
        | Mnemonic::Fmax
        | Mnemonic::Fmin
        | Mnemonic::Fcmp
        | Mnemonic::Fcmpe
        | Mnemonic::Fccmp
        | Mnemonic::Fcsel
        | Mnemonic::Scvtf
        | Mnemonic::Ucvtf
        | Mnemonic::Fcvtzs
        | Mnemonic::Fcvtzu
        | Mnemonic::Fcvt
        | Mnemonic::Dup
        | Mnemonic::Mul
        | Mnemonic::Neg
        | Mnemonic::Abs
        | Mnemonic::Movi
        | Mnemonic::Mvni
        | Mnemonic::Svc
        | Mnemonic::Mrs
        | Mnemonic::Msr
        | Mnemonic::Barrier => None,
    }
}

/// Reports the address a memory operand reaches through a known base.
///
/// # Arguments
///
/// * `regs` - The registers before the instruction.
/// * `insn` - The instruction.
/// * `found` - Called with the address and [`RefKind::Data`], or with the
///   base and [`RefKind::Index`] when a register indexes it.
///
/// # Returns
///
/// The address an access without an index register reaches, or `None`
/// when the base is not a known address or a register indexes it.
fn access(regs: &Regs, insn: &Insn, found: &mut dyn FnMut(u64, RefKind)) -> Option<u64> {
    let m = mem(insn)?;
    let Some(Val::Addr(base)) = value(regs, gpr(m.base)) else {
        return None;
    };
    if m.index.is_some() {
        found(base, RefKind::Index);
        return None;
    }
    let at = match m.mode {
        Mode::Offset | Mode::PreIndex => base.wrapping_add_signed(m.disp),
        Mode::PostIndex => base,
    };
    found(at, RefKind::Data);
    Some(at)
}

/// Decodes the instructions of a function's blocks.
///
/// # Arguments
///
/// * `text` - The code.
/// * `f` - The function.
///
/// # Returns
///
/// Its instructions in address order.
pub(super) fn decode_function(text: &Text<'_>, f: &Function) -> Vec<Insn> {
    let mut out = Vec::with_capacity(f.instr_count);
    for b in &f.blocks {
        let words = b.end.saturating_sub(b.start) / 4;
        out.extend((0..words).filter_map(|k| {
            let va = b.start.checked_add(k.checked_mul(4)?)?;
            Some(a64::decode(text.word(va)?, va))
        }));
    }
    out.sort_unstable_by_key(|i| i.va);
    out.dedup_by_key(|i| i.va);
    out
}

/// Reads where the first argument registers of each call a function makes
/// got their values.
///
/// A register loaded from a constant address on every path into the call
/// ([`Tracker`]) names that slot; otherwise one last written by an earlier
/// call holds that call's result (`x0`), and one not written since the
/// function's entry holds what the caller passed, each read within the
/// call's block and the blocks it is entered from only by falling through
/// ([`falls_through`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The function.
///
/// # Returns
///
/// The calls (`bl`, and `blr` through a slot) in block then address
/// order, with `x0`, `x1` and `x2`.
pub(crate) fn calls(program: &Program, f: &Function) -> Vec<Call> {
    let text = Text::new(program);
    let insns = decode_function(&text, f);
    let tracker = Tracker::new(&insns, &f.blocks);
    let mut out = Vec::new();
    let carried = falls_through(&f.blocks);
    let mut last = [Arg::Unknown; 3];
    for ((b, start), carry) in f.blocks.iter().zip(&tracker.entry).zip(carried) {
        let mut regs = *start;
        if !carry {
            last = [if b.start == f.entry {
                Arg::Entry
            } else {
                Arg::Unknown
            }; 3];
        }
        for i in block_insns(&insns, b) {
            let call = matches!(i.op, Op::Bl | Op::Blr);
            let callee = if i.op == Op::Bl {
                i.target().map(Callee::Direct)
            } else if let (true, Some(Val::Loaded(slot))) =
                (call, value(&regs, any_reg(&i.operands[0])))
            {
                Some(Callee::Slot(slot))
            } else {
                None
            };
            if let Some(callee) = callee {
                let args = std::array::from_fn(|n| match value(&regs, Some(n)) {
                    Some(Val::Loaded(slot)) => Arg::Slot(slot),
                    Some(Val::Addr(_)) | None => last.get(n).copied().unwrap_or(Arg::Unknown),
                });
                out.push(Call {
                    site: i.va,
                    callee,
                    args,
                });
            }
            let mask = writes(i);
            for (n, a) in last.iter_mut().enumerate() {
                if mask & (1u32 << n) != 0 {
                    *a = if call && n == 0 {
                        Arg::Result(i.va)
                    } else {
                        Arg::Unknown
                    };
                }
            }
            step(&mut regs, i, &mut |_, _| {});
        }
    }
    out
}

/// Indexes every reference the functions make through the constants their
/// registers hold ([`Tracker`]) that lands in one of the image's sections.
///
/// The functions are tracked across the cores and their references put
/// back in function order.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `text` - The code.
/// * `functions` - The functions, final.
/// * `xrefs` - The reference index, extended.
pub(super) fn index(
    program: &Program,
    text: &Text<'_>,
    functions: &[Function],
    xrefs: &mut BTreeMap<u64, Vec<RefSite>>,
) {
    let refs_of = |f: &Function| {
        let insns = decode_function(text, f);
        let mut sites: Vec<(u64, u64, RefKind)> = Vec::new();
        Tracker::new(&insns, &f.blocks).refs(&mut |target, va, kind| {
            if program.section_at(target).is_some() {
                sites.push((target, va, kind));
            }
        });
        sites
    };
    let found = striped(functions, refs_of);
    for (f, sites) in functions.iter().zip(found) {
        for (target, va, kind) in sites.unwrap_or_else(|| refs_of(f)) {
            push_site(xrefs, target, va, kind, Some(f.entry));
        }
    }
}
