//! What an ARM32 function takes and hands back, as the procedure call
//! standard passes it ([`super::super::abi::a32`]).
//!
//! A parameter is an argument register the function reads before writing
//! it on a path from its entry that no call precedes, or that a call or a
//! jump out on such a path hands on to a callee that takes it: `r0` to
//! `r3`, and the singles and doubles below `s16`. The integer ones come first in
//! register order, then the floating ones in the order their storage
//! takes, a double where the function reads the double and a single where
//! it reads the single. A declaration, when one states the function, fixes
//! the positions instead, its floating ones taken as doubles.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::super::abi::{self, a32 as a32_abi};
use super::super::expr::{Expr, Key};
use super::super::lift::{self, Env};
use super::super::{Ctx, Shape, declared_arity, new_ctx, pointee_type};
use super::{decode_blocks, live};
use crate::analysis::{Analysis, Function, Overlay};
use crate::isa::a32::{
    Block, Cond, DpKind, Flow, Index, Insn, Offset, Op as AOp, Operand, PC, Reg, SP,
};
use crate::program::Program;

/// Most paths the parameter walk follows from the entry.
const PATHS_MAX: usize = 4096;

/// Most stack parameter words tracked above the entry stack pointer.
const STACK_PARAMS_MAX: i64 = 8;

/// The register a call passes argument position `i` in when nothing says
/// more than a float mask: integer positions take `r0` to `r3`, floating
/// ones `d0` to `d7`.
///
/// # Arguments
///
/// * `i` - The position.
/// * `floats` - A bit per floating position.
///
/// # Returns
///
/// The register, or `None` past the registers the standard passes in.
pub(in crate::analysis::decompile) fn arg_reg(i: usize, floats: u8) -> Option<Reg> {
    let bit = |p: usize| p < 8 && (floats >> p) & 1 != 0;
    let before = (0..i).filter(|&p| bit(p)).count();
    if bit(i) {
        u8::try_from(before).ok().filter(|n| *n < 8).map(Reg::D)
    } else {
        u8::try_from(i - before)
            .ok()
            .filter(|n| *n < a32_abi::INT_ARGS)
            .map(Reg::R)
    }
}

/// The bit of an argument register in a set of them: `r0` to `r3` take
/// bits 0 to 3, `s0` to `s15` bits 4 to 19; a double takes its singles'.
///
/// # Arguments
///
/// * `r` - The register.
fn arg_bits(r: Reg) -> u32 {
    match r {
        Reg::R(n) if n < a32_abi::INT_ARGS => 1 << n,
        Reg::S(n) if n < a32_abi::FLOAT_SINGLES => 1 << (4 + u32::from(n)),
        Reg::D(n) if n < a32_abi::FLOAT_SINGLES / 2 => 3 << (4 + 2 * u32::from(n)),
        Reg::R(_) | Reg::S(_) | Reg::D(_) => 0,
    }
}

/// Walks a function's paths from its entry and finds the argument
/// registers read before being written on one that no call precedes.
///
/// A call ends a path. When `follow` is set, it reads the registers its
/// callee takes ([`forwarded`]), as a jump out of the function does; a
/// register a call goes through is read either way.
///
/// # Arguments
///
/// * `ctx` - Any function's context, for the image and the callees.
/// * `code` - Each block's instructions.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
/// * `follow` - Read what calls and jumps out hand on.
fn walk(
    ctx: &Ctx<'_>,
    code: &[Vec<Insn>],
    succs: &[Vec<usize>],
    entry: usize,
    follow: bool,
) -> BTreeSet<Reg> {
    let starts: BTreeSet<u64> = code
        .iter()
        .filter_map(|b| b.first())
        .map(|i| i.va)
        .collect();
    let r3_pad_ok = r3_align_slot_unused(code);
    let mut found = BTreeSet::new();
    let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
    let mut work = vec![(entry, 0u32)];
    let take = |found: &mut BTreeSet<Reg>, written: u32, r: Reg| {
        let bits = arg_bits(r);
        if bits != 0 && bits & !written == bits {
            found.insert(r);
        }
    };
    while let Some((b, mut written)) = work.pop() {
        if seen.len() >= PATHS_MAX || !seen.insert((b, written)) {
            continue;
        }
        let Some(instrs) = code.get(b) else { continue };
        let mut stopped = false;
        for i in instrs {
            let out = match i.flow() {
                Flow::Call => true,
                Flow::Jump => i.target().is_some_and(|t| !starts.contains(&t)),
                Flow::Next | Flow::CondJump | Flow::Return | Flow::Invalid => false,
            };
            if out && follow {
                for r in forwarded(ctx, i.target()) {
                    take(&mut found, written, r);
                }
            }
            if i.flow() == Flow::Call {
                if let AOp::BlxReg { rm } = i.op {
                    take(&mut found, written, rm);
                }
                stopped = true;
                break;
            }
            let align_r3 = r3_pad_ok
                && matches!(
                    i.op,
                    AOp::Stm {
                        rn: SP,
                        wback: true,
                        block: Block::Db,
                        regs,
                    } if regs & (1 << 3) != 0
                        && regs & 0x7 == 0
                        && regs & (1 << 14) != 0
                        && regs.count_ones() % 2 == 0
                );
            let regs = i.registers();
            for r in regs.reads {
                if align_r3 && r == Reg::R(3) {
                    continue;
                }
                take(&mut found, written, r);
            }
            for r in regs.writes {
                written |= arg_bits(r);
            }
        }
        if !stopped {
            for &s in succs.get(b).into_iter().flatten() {
                work.push((s, written));
            }
        }
    }
    found
}

/// Tells whether a prologue `push {r3, ...}` alignment slot at `[sp, #0]`
/// is never read before the epilogue `pop {..., pc}`.
fn r3_align_slot_unused(code: &[Vec<Insn>]) -> bool {
    code.iter().flatten().all(|i| match i.op {
        AOp::Dp { rn, src, .. } => rn != SP && !matches!(src, Operand::Reg { rm: SP, .. }),
        AOp::Load { addr, .. }
        | AOp::LoadEx { addr, .. }
        | AOp::LoadDual { addr, .. }
        | AOp::VLoad { addr, .. } => {
            addr.base != SP
                || (addr.index == Index::Offset && matches!(addr.offset, Offset::Imm(d) if d != 0))
        }
        AOp::Ldm {
            rn: SP,
            wback,
            block,
            regs,
        } => wback && block == Block::Ia && regs & 0x8000 != 0,
        AOp::VLdm { rn: SP, .. } => false,
        _ => true,
    })
}

/// Returns the argument registers a call or a jump out hands on to `target`.
///
/// They are the words a run-time helper takes, what a declaration says
/// the callee takes, else what its body reads before writing on a path
/// from its entry that no call precedes.
///
/// # Arguments
///
/// * `ctx` - Any function's context, for the image and the callees.
/// * `target` - The callee, when the transfer names one.
fn forwarded(ctx: &Ctx<'_>, target: Option<u64>) -> Vec<Reg> {
    let Some(t) = target else {
        return Vec::new();
    };
    let name = crate::analysis::name_of(ctx.analysis, ctx.overlay, t);
    if let Some(words) = super::call::runtime_words(&name) {
        return (0..words).map(Reg::R).collect();
    }
    let Some(f) = ctx.analysis.function(t).filter(|f| f.entry == t) else {
        return Vec::new();
    };
    let starts = f.blocks.iter().map(|b| b.start).collect();
    let fctx = new_ctx(ctx.program, ctx.analysis, ctx.overlay, f, 32, starts, &[]);
    if let Some((count, floats, _, _)) = declared_arity(&fctx, f, 0) {
        return (0..count).filter_map(|i| arg_reg(i, floats)).collect();
    }
    let (code, succs, entry) = graph(&fctx, f);
    walk(&fctx, &code, &succs, entry, false)
        .into_iter()
        .collect()
}

/// Orders the argument registers a function reads into its parameter list.
///
/// The integer ones come up to the highest read, then the floating ones
/// in storage order, a double read whole and the singles up to the
/// highest single read, so a double's unread half names no parameter.
///
/// # Arguments
///
/// * `read` - The registers read.
fn ordered(read: &BTreeSet<Reg>) -> Vec<Reg> {
    let ints = read
        .iter()
        .filter_map(|r| match r {
            Reg::R(n) => Some(*n + 1),
            Reg::S(_) | Reg::D(_) => None,
        })
        .max()
        .unwrap_or(0);
    let mut out: Vec<Reg> = (0..ints).map(Reg::R).collect();
    let top = read
        .iter()
        .filter_map(|r| match r {
            Reg::S(n) => Some(*n),
            Reg::R(_) | Reg::D(_) => None,
        })
        .max();
    let mut s = 0u8;
    while s < a32_abi::FLOAT_SINGLES {
        if s.is_multiple_of(2) && read.contains(&Reg::D(s / 2)) {
            out.push(Reg::D(s / 2));
            s += 2;
            continue;
        }
        if top.is_some_and(|t| s <= t) {
            out.push(Reg::S(s));
        }
        s += 1;
    }
    out
}

/// The parameter registers of the function at `entry`, read once per
/// function and overlay.
///
/// # Arguments
///
/// * `ctx` - Any function's context, for the image and the overlay.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The registers in position order, `None` when no function starts there.
pub(in crate::analysis::decompile) fn arg_regs(ctx: &Ctx<'_>, entry: u64) -> Option<Arc<Vec<Reg>>> {
    let f = ctx.analysis.function(entry).filter(|f| f.entry == entry)?;
    Some(ctx.analysis.derived.get_or_build_item(
        "a32 args",
        ctx.overlay.fingerprint(),
        entry,
        || {
            let starts = f.blocks.iter().map(|b| b.start).collect();
            let fctx = new_ctx(ctx.program, ctx.analysis, ctx.overlay, f, 32, starts, &[]);
            if let Some((count, floats, _, _)) = declared_arity(&fctx, f, 0) {
                return (0..count).filter_map(|i| arg_reg(i, floats)).collect();
            }
            let (code, succs, entry) = graph(&fctx, f);
            let mut read = walk(&fctx, &code, &succs, entry, true);
            if stack_params_read(&code, &succs, entry) > 0 {
                read.extend((0..a32_abi::INT_ARGS).map(Reg::R));
            }
            ordered(&read)
        },
        |v: &Vec<Reg>| v.capacity(),
    ))
}

/// Maximum exact offsets kept per register before recording an outer span.
const OFFSETS_MAX: usize = 64;

/// Maximum intra-block states before collapsing into one merged state.
const BLOCK_STATES_MAX: usize = 32;

/// Reachable stack-pointer byte offsets for a register.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct OffsetSet {
    /// Exact byte offsets from the entry stack pointer, up to [`OFFSETS_MAX`].
    offsets: BTreeSet<i64>,
    /// Outer `[lo, hi]` byte-offset bounds when merged sets exceed [`OFFSETS_MAX`].
    span: Option<(i64, i64)>,
    /// Relative byte offsets written through this register value.
    rel_written: BTreeSet<i64>,
    /// Whether the register holds a single definite offset on all merged paths.
    definite: bool,
}

impl OffsetSet {
    /// Creates a definite singleton offset set at `d`.
    fn single(d: i64) -> Self {
        Self {
            offsets: BTreeSet::from([d]),
            span: None,
            rel_written: BTreeSet::new(),
            definite: true,
        }
    }

    /// Shifts every offset in the set by `delta`.
    fn shifted(&self, delta: i64) -> Self {
        Self {
            offsets: self
                .offsets
                .iter()
                .map(|&x| x.saturating_add(delta))
                .collect(),
            span: self
                .span
                .map(|(lo, hi)| (lo.saturating_add(delta), hi.saturating_add(delta))),
            rel_written: self
                .rel_written
                .iter()
                .map(|&w| w.saturating_sub(delta))
                .collect(),
            definite: self.definite,
        }
    }

    /// Returns the single offset when this set is a definite singleton.
    fn definite_offset(&self) -> Option<i64> {
        (self.definite && self.span.is_none() && self.offsets.len() == 1)
            .then(|| *self.offsets.iter().next().unwrap_or(&0))
    }

    /// Unions two offset sets, preserving `definite` only when both are the
    /// same definite singleton and `all_have` holds.
    fn union(&self, other: &Self, all_have: bool) -> Self {
        if self.offsets == other.offsets
            && self.span == other.span
            && self.definite
            && other.definite
            && all_have
        {
            return Self {
                offsets: self.offsets.clone(),
                span: self.span,
                rel_written: self
                    .rel_written
                    .intersection(&other.rel_written)
                    .copied()
                    .collect(),
                definite: true,
            };
        }
        let mut offsets: BTreeSet<i64> = self.offsets.union(&other.offsets).copied().collect();
        let mut span = match (self.span, other.span) {
            (Some((l1, h1)), Some((l2, h2))) => Some((l1.min(l2), h1.max(h2))),
            (Some(s), None) | (None, Some(s)) => Some(s),
            (None, None) => None,
        };
        if offsets.len() > OFFSETS_MAX {
            let lo = *offsets.first().unwrap_or(&0);
            let hi = *offsets.last().unwrap_or(&0);
            span = Some(span.map_or((lo, hi), |(l, h)| (l.min(lo), h.max(hi))));
            while offsets.len() > OFFSETS_MAX {
                let first = *offsets.first().unwrap_or(&0);
                let last = *offsets.last().unwrap_or(&0);
                if first.saturating_abs() > last.saturating_abs() {
                    offsets.pop_first();
                } else {
                    offsets.pop_last();
                }
            }
        }
        Self {
            offsets,
            span,
            rel_written: BTreeSet::new(),
            definite: false,
        }
    }
}

/// Intra-block state: known condition-pair mask, true condition-pair mask,
/// written-byte mask, and register-to-SP displacements.
type BlockState = (u8, u8, u32, BTreeMap<Reg, OffsetSet>);

/// Counts stack parameter words at `[sp_entry + 4 * k]` read before being
/// written on any path from `entry`.
///
/// # Arguments
///
/// * `code` - Each block's instructions.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
fn stack_params_read(code: &[Vec<Insn>], succs: &[Vec<usize>], entry: usize) -> u8 {
    /// Block index, written-byte bitmask, and register-to-SP displacements.
    type SeenState = (usize, u32, Vec<(Reg, OffsetSet)>);
    let mut max_slot: Option<u8> = None;
    let mut seen: BTreeSet<SeenState> = BTreeSet::new();
    let mut work = vec![(entry, 0u32, BTreeMap::from([(SP, OffsetSet::single(0))]))];
    while let Some((b, written, frame)) = work.pop() {
        let key: Vec<(Reg, OffsetSet)> = frame.iter().map(|(&r, d)| (r, d.clone())).collect();
        if seen.len() >= PATHS_MAX || !seen.insert((b, written, key)) {
            continue;
        }
        let Some(instrs) = code.get(b) else { continue };
        let mut states: Vec<BlockState> = vec![(0, 0, written, frame)];
        for i in instrs {
            let resets = i.sets
                || i.flow() == Flow::Call
                || matches!(i.op, AOp::Msr { .. } | AOp::Vmrs { .. });
            let mut next = Vec::with_capacity(states.len());
            for s in states {
                step_block_state(i, s, resets, &mut max_slot, &mut next);
            }
            next.sort_unstable();
            next.dedup();
            if next.len() > BLOCK_STATES_MAX {
                collapse_states(&mut next);
            }
            states = next;
        }
        if states.len() > 8 {
            collapse_states(&mut states);
        }
        for &s in succs.get(b).into_iter().flatten() {
            for (_, _, w, f) in &states {
                work.push((s, *w, f.clone()));
            }
        }
    }
    max_slot.unwrap_or(0)
}

/// Merges multiple intra-block states into one conservative state without
/// dropping reachable register offsets.
fn collapse_states(states: &mut Vec<BlockState>) {
    if states.len() <= 1 {
        for (k, h, _, _) in states.iter_mut() {
            *k = 0;
            *h = 0;
        }
        return;
    }
    let total = states.len();
    let written = states.iter().fold(!0u32, |acc, (_, _, w, _)| acc & *w);
    let mut counts: BTreeMap<Reg, usize> = BTreeMap::new();
    let mut merged: BTreeMap<Reg, OffsetSet> = BTreeMap::new();
    for (_, _, _, f) in states.iter() {
        for (&r, offs) in f {
            *counts.entry(r).or_default() += 1;
            merged
                .entry(r)
                .and_modify(|cur| *cur = cur.union(offs, true))
                .or_insert_with(|| offs.clone());
        }
    }
    for (&r, &c) in &counts {
        if c < total
            && let Some(offs) = merged.get_mut(&r)
        {
            offs.definite = false;
        }
    }
    states.clear();
    states.push((0, 0, written, merged));
}

/// Maps a condition code to its canonical pair bit and polarity.
fn cond_bit(c: Cond) -> Option<(u8, bool)> {
    match c {
        Cond::Eq => Some((1 << 0, true)),
        Cond::Ne => Some((1 << 0, false)),
        Cond::Hs => Some((1 << 1, true)),
        Cond::Lo => Some((1 << 1, false)),
        Cond::Mi => Some((1 << 2, true)),
        Cond::Pl => Some((1 << 2, false)),
        Cond::Vs => Some((1 << 3, true)),
        Cond::Vc => Some((1 << 3, false)),
        Cond::Hi => Some((1 << 4, true)),
        Cond::Ls => Some((1 << 4, false)),
        Cond::Ge => Some((1 << 5, true)),
        Cond::Lt => Some((1 << 5, false)),
        Cond::Gt => Some((1 << 6, true)),
        Cond::Le => Some((1 << 6, false)),
        Cond::Al | Cond::Nv => None,
    }
}

/// Advances one intra-block state across an instruction, updating `max_slot`
/// and pushing resulting states into `next`.
fn step_block_state(
    i: &Insn,
    state: BlockState,
    resets: bool,
    max_slot: &mut Option<u8>,
    next: &mut Vec<BlockState>,
) {
    let (known, holds, written, frame) = state;
    let apply = |mut w: u32, mut f: BTreeMap<Reg, OffsetSet>, max_slot: &mut Option<u8>| {
        apply_mem(i, &mut f, &mut w, max_slot);
        step_frame(i, &mut f);
        (w, f)
    };
    let Some((bit, pol)) = cond_bit(i.cond) else {
        let (w, f) = apply(written, frame, max_slot);
        let (k, h) = if resets { (0, 0) } else { (known, holds) };
        next.push((k, h, w, f));
        return;
    };
    let with_pol = |h: u8, v: bool| if v { h | bit } else { h & !bit };
    if known & bit != 0 {
        if ((holds & bit) != 0) == pol {
            let (w, f) = apply(written, frame, max_slot);
            let (k, h) = if resets { (0, 0) } else { (known, holds) };
            next.push((k, h, w, f));
        } else {
            next.push((known, holds, written, frame));
        }
        return;
    }
    let (w, f) = apply(written, frame.clone(), max_slot);
    if w == written && f == frame && !resets {
        next.push((known, holds, written, frame));
        return;
    }
    next.push((known | bit, with_pol(holds, !pol), written, frame));
    let (k, h) = if resets {
        (0, 0)
    } else {
        (known | bit, with_pol(holds, pol))
    };
    next.push((k, h, w, f));
}

/// Records stack parameter loads and definite stores for one instruction.
fn apply_mem(
    i: &Insn,
    frame: &mut BTreeMap<Reg, OffsetSet>,
    written: &mut u32,
    max_slot: &mut Option<u8>,
) {
    let Some((is_load, base_reg, rel, bytes)) = mem_op(i) else {
        return;
    };
    let Some(offs) = frame.get_mut(&base_reg) else {
        return;
    };
    let mark_load = |start: i64, end: i64, written: u32, max_slot: &mut Option<u8>| {
        for b_off in start.max(0)..end.min(STACK_PARAMS_MAX * 4) {
            if written & (1u32 << b_off) == 0
                && let Ok(slot) = u8::try_from(b_off / 4)
            {
                *max_slot = Some(max_slot.map_or(slot + 1, |m| m.max(slot + 1)));
            }
        }
    };
    if is_load {
        for byte_idx in 0..bytes {
            let r_off = rel.saturating_add(byte_idx);
            if offs.rel_written.contains(&r_off) {
                continue;
            }
            for &base in &offs.offsets {
                let at = base.saturating_add(r_off);
                mark_load(at, at.saturating_add(1), *written, max_slot);
            }
            if let Some((lo, hi)) = offs.span {
                mark_load(
                    lo.saturating_add(r_off),
                    hi.saturating_add(r_off).saturating_add(1),
                    *written,
                    max_slot,
                );
            }
        }
    } else {
        if let Some(base) = offs.definite_offset() {
            let at = base.saturating_add(rel);
            for b_off in at.max(0)..at.saturating_add(bytes).min(STACK_PARAMS_MAX * 4) {
                *written |= 1u32 << b_off;
            }
        }
        if offs.rel_written.len() < OFFSETS_MAX {
            for byte_idx in 0..bytes {
                offs.rel_written.insert(rel.saturating_add(byte_idx));
            }
        }
    }
}

/// Relative range `(is_load, base_reg, rel_offset, byte_len)` of a memory op.
///
/// # Arguments
///
/// * `i` - The instruction.
fn mem_op(i: &Insn) -> Option<(bool, Reg, i64, i64)> {
    let addr_rel = |addr: crate::isa::a32::Addr| -> Option<(Reg, i64)> {
        match (addr.index, addr.offset) {
            (Index::Post, _) => Some((addr.base, 0)),
            (Index::Offset | Index::Pre, Offset::Imm(d)) => Some((addr.base, i64::from(d))),
            _ => None,
        }
    };
    match i.op {
        AOp::Load { width, rt, addr } | AOp::LoadEx { width, rt, addr } if rt != PC => {
            let (b, rel) = addr_rel(addr)?;
            Some((true, b, rel, i64::from(width.bytes())))
        }
        AOp::LoadDual { rt, rt2, addr } if rt != PC && rt2 != PC => {
            let (b, rel) = addr_rel(addr)?;
            Some((true, b, rel, 8))
        }
        AOp::VLoad { vd, addr } => {
            let (b, rel) = addr_rel(addr)?;
            Some((true, b, rel, if matches!(vd, Reg::D(_)) { 8 } else { 4 }))
        }
        AOp::Store { width, addr, .. } | AOp::StoreEx { width, addr, .. } => {
            let (b, rel) = addr_rel(addr)?;
            Some((false, b, rel, i64::from(width.bytes())))
        }
        AOp::StoreDual { addr, .. } => {
            let (b, rel) = addr_rel(addr)?;
            Some((false, b, rel, 8))
        }
        AOp::VStore { vd, addr } => {
            let (b, rel) = addr_rel(addr)?;
            Some((false, b, rel, if matches!(vd, Reg::D(_)) { 8 } else { 4 }))
        }
        AOp::Ldm {
            rn, regs, block, ..
        }
        | AOp::Stm {
            rn, regs, block, ..
        } => {
            let is_load = matches!(i.op, AOp::Ldm { .. });
            if !is_load && regs & 0x8000 != 0 {
                return None;
            }
            let total = 4 * i64::from(regs.count_ones());
            let rel = match block {
                Block::Ia => 0,
                Block::Ib => 4,
                Block::Da => 4 - total,
                Block::Db => -total,
            };
            let bytes = if is_load {
                4 * i64::from((regs & 0x7fff).count_ones())
            } else {
                total
            };
            Some((is_load, rn, rel, bytes))
        }
        AOp::VLdm {
            rn,
            first,
            count,
            db,
            ..
        }
        | AOp::VStm {
            rn,
            first,
            count,
            db,
            ..
        } => {
            let step = if matches!(first, Reg::D(_)) { 8 } else { 4 };
            let bytes = step * i64::from(count);
            let rel = if db { -bytes } else { 0 };
            Some((matches!(i.op, AOp::VLdm { .. }), rn, rel, bytes))
        }
        _ => None,
    }
}

/// Updates entry-relative stack pointer offsets across one instruction.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `frame` - Known offsets from the entry stack pointer per register.
fn step_frame(i: &Insn, frame: &mut BTreeMap<Reg, OffsetSet>) {
    if i.flow() == Flow::Call {
        frame.retain(|&r, _| r == SP || a32_abi::callee_saved(r));
        return;
    }
    if step_frame_mem(i, frame) {
        return;
    }
    match i.op {
        AOp::Dp {
            kind: DpKind::Add,
            rd,
            rn,
            src: Operand::Imm { value, .. },
        } => {
            if let Some(b) = frame
                .get(&rn)
                .map(|b| b.shifted(i64::from(value.cast_signed())))
            {
                frame.insert(rd, b);
            } else {
                frame.remove(&rd);
            }
        }
        AOp::Dp {
            kind: DpKind::Sub,
            rd,
            rn,
            src: Operand::Imm { value, .. },
        } => {
            if let Some(b) = frame
                .get(&rn)
                .map(|b| b.shifted(-i64::from(value.cast_signed())))
            {
                frame.insert(rd, b);
            } else {
                frame.remove(&rd);
            }
        }
        AOp::Dp {
            kind: DpKind::Mov,
            rd,
            src: Operand::Reg { rm, amount: 0, .. },
            ..
        } => {
            if let Some(b) = frame.get(&rm).cloned() {
                frame.insert(rd, b);
            } else {
                frame.remove(&rd);
            }
        }
        _ => {
            for r in i.registers().writes {
                frame.remove(&r);
            }
        }
    }
}

/// Updates entry-relative stack pointer offsets for writeback memory ops.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `frame` - Known offsets from the entry stack pointer per register.
fn step_frame_mem(i: &Insn, frame: &mut BTreeMap<Reg, OffsetSet>) -> bool {
    let wback = match i.op {
        AOp::Load { rt, addr, .. }
        | AOp::LoadEx { rt, addr, .. }
        | AOp::VLoad { vd: rt, addr }
        | AOp::StoreEx { rd: rt, addr, .. } => Some((addr, Some(rt), None)),
        AOp::LoadDual { rt, rt2, addr } => Some((addr, Some(rt), Some(rt2))),
        AOp::Store { addr, .. } | AOp::StoreDual { addr, .. } | AOp::VStore { addr, .. } => {
            Some((addr, None, None))
        }
        _ => None,
    };
    if let Some((addr, dst1, dst2)) = wback
        && addr.index != Index::Offset
    {
        if dst1 != Some(addr.base)
            && dst2 != Some(addr.base)
            && let Offset::Imm(d) = addr.offset
            && let Some(b) = frame.get_mut(&addr.base)
        {
            *b = b.shifted(i64::from(d));
        } else {
            frame.remove(&addr.base);
        }
        for r in [dst1, dst2].into_iter().flatten() {
            frame.remove(&r);
        }
        return true;
    }
    match i.op {
        AOp::Stm {
            rn,
            regs,
            wback: true,
            block,
        }
        | AOp::Ldm {
            rn,
            regs,
            wback: true,
            block,
        } => {
            if matches!(i.op, AOp::Ldm { .. }) {
                for bit in 0..16u8 {
                    if regs & (1 << bit) != 0 {
                        frame.remove(&Reg::R(bit));
                    }
                }
            }
            let bytes = 4 * i64::from(regs.count_ones());
            let delta = match block {
                Block::Ia | Block::Ib => bytes,
                Block::Da | Block::Db => -bytes,
            };
            if let Some(d) = frame.get_mut(&rn) {
                *d = d.shifted(delta);
            }
            true
        }
        AOp::VStm {
            rn,
            first,
            count,
            wback: true,
            db,
        }
        | AOp::VLdm {
            rn,
            first,
            count,
            wback: true,
            db,
        } => {
            let step = if matches!(first, Reg::D(_)) { 8 } else { 4 };
            let bytes = step * i64::from(count);
            let delta = if db { -bytes } else { bytes };
            if let Some(d) = frame.get_mut(&rn) {
                *d = d.shifted(delta);
            }
            true
        }
        _ => false,
    }
}

/// Decodes a function's blocks and edges.
///
/// # Arguments
///
/// * `ctx` - The function's context.
/// * `f` - The function.
fn graph(ctx: &Ctx<'_>, f: &Function) -> (Vec<Vec<Insn>>, Vec<Vec<usize>>, usize) {
    let idx: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let succs = f
        .blocks
        .iter()
        .map(|b| {
            b.successors
                .iter()
                .filter_map(|s| idx.get(s).copied())
                .collect()
        })
        .collect();
    (
        decode_blocks(ctx, f),
        succs,
        idx.get(&f.entry).copied().unwrap_or(0),
    )
}

/// The float mask of a parameter list: a bit per position held in a VFP
/// register.
///
/// # Arguments
///
/// * `regs` - The registers in position order.
fn float_mask(regs: &[Reg]) -> u8 {
    regs.iter()
        .take(8)
        .enumerate()
        .filter(|(_, r)| matches!(r, Reg::S(_) | Reg::D(_)))
        .fold(0u8, |m, (i, _)| m | (1 << i))
}

/// Reads what an ARM32 function takes ([`Shape`]).
///
/// # Arguments
///
/// * `ctx` - The function's context.
/// * `f` - The function.
/// * `code` - Each block's instructions.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
pub(in crate::analysis::decompile) fn shape(
    ctx: &Ctx<'_>,
    f: &Function,
    code: &[Vec<Insn>],
    succs: &[Vec<usize>],
    entry: usize,
) -> Shape {
    let (regs, stack) = match declared_arity(ctx, f, 0) {
        Some((count, floats, _, _)) => {
            let regs: Vec<Reg> = (0..count).filter_map(|i| arg_reg(i, floats)).collect();
            let stack = u8::try_from(count.saturating_sub(regs.len())).unwrap_or(0);
            (regs, stack)
        }
        None => {
            let mut read = walk(ctx, code, succs, entry, true);
            let stack = stack_params_read(code, succs, entry);
            if stack > 0 {
                read.extend((0..a32_abi::INT_ARGS).map(Reg::R));
            }
            (ordered(&read), stack)
        }
    };
    Shape {
        conv: &abi::AAPCS32,
        params: Vec::new(),
        variadic: false,
        this_param: false,
        result_param: None,
        count: regs.len() + usize::from(stack),
        stack: u32::from(stack),
        stated_short: None,
        float_mask: Some(float_mask(&regs)),
    }
}

/// Returns what a call's ARM32 callee takes, read once per function and
/// overlay.
///
/// # Arguments
///
/// * `ctx` - The calling function's context.
/// * `target` - The callee's entry.
///
/// # Returns
///
/// The shape, or `None` when no function of its own starts there.
pub(in crate::analysis::decompile) fn callee_shape(
    ctx: &Ctx<'_>,
    target: u64,
) -> Option<Arc<Shape>> {
    let f = ctx
        .analysis
        .function(target)
        .filter(|f| f.entry == target && f.thunk.is_none())?;
    Some(abi::shape(
        ctx.program,
        ctx.analysis,
        ctx.overlay,
        ctx.overlay_key,
        f,
        32,
    ))
}

/// Reads a function's [`Shape`] afresh.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names.
/// * `f` - The function.
pub(in crate::analysis::decompile) fn built(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
) -> Shape {
    let starts = f.blocks.iter().map(|b| b.start).collect();
    let ctx = new_ctx(program, analysis, overlay, f, 32, starts, &[]);
    let (code, succs, entry) = graph(&ctx, f);
    shape(&ctx, f, &code, &succs, entry)
}

/// The entry of the function a context is for: the start of its entry
/// block.
///
/// # Arguments
///
/// * `ctx` - The function's context.
pub(in crate::analysis::decompile) fn entry_of(ctx: &Ctx<'_>) -> Option<u64> {
    ctx.block_starts.iter().nth(ctx.entry_block).copied()
}

/// Returns the state at a function's entry: each parameter in its
/// register.
///
/// # Arguments
///
/// * `ctx` - The function's context.
pub(in crate::analysis::decompile) fn entry_env(ctx: &Ctx<'_>) -> Env {
    let mut env = Env::entry();
    let regs = entry_of(ctx)
        .and_then(|e| arg_regs(ctx, e))
        .map(|a| a.to_vec())
        .unwrap_or_default();
    for (p, r) in regs.iter().enumerate().take(ctx.arg_count) {
        if let Ok(i) = u8::try_from(p) {
            env.vals.insert(Key::A32(*r), Expr::Var(Key::Param(i)));
        }
    }
    env
}

/// Tells whether an instruction other than a call writes the register the
/// function hands its result back in.
///
/// # Arguments
///
/// * `ctx` - The function's state.
/// * `code` - Each block's instructions.
pub(in crate::analysis::decompile) fn writes_result(ctx: &Ctx<'_>, code: &[Vec<Insn>]) -> bool {
    let back = super::call::result_key(ctx);
    code.iter()
        .flatten()
        .filter(|i| i.flow() != Flow::Call)
        .any(|i| live::effects(ctx, i).1.iter().any(|(k, _)| *k == back))
}

/// Width in bits of the value a return hands back: a declared return
/// type's, else 64 when the function writes `d0` outside a call (a
/// double comes back there), else the word.
///
/// # Arguments
///
/// * `code` - Each block's instructions.
/// * `declared` - The signature's return type when one is known.
pub(in crate::analysis::decompile) fn ret_lane(code: &[Vec<Insn>], declared: Option<&str>) -> u8 {
    if let Some(d) = declared {
        return lift::declared_bits(d);
    }
    let double = code
        .iter()
        .flatten()
        .any(|i| i.flow() != Flow::Call && i.registers().writes.contains(&Reg::D(0)));
    if double { 64 } else { 32 }
}

/// Infers the types of an ARM32 function's parameters: a pointer read or
/// written through, a float or a double.
///
/// # Arguments
///
/// * `ctx` - The function's parameters.
/// * `code` - Each block's instructions.
/// * `entry` - Index of the entry block.
///
/// # Returns
///
/// The C type per parameter position.
pub(in crate::analysis::decompile) fn param_types(
    ctx: &Ctx<'_>,
    code: &[Vec<Insn>],
    entry: usize,
) -> BTreeMap<usize, String> {
    let regs = entry_of(ctx)
        .and_then(|e| arg_regs(ctx, e))
        .map(|a| a.to_vec())
        .unwrap_or_default();
    let mut typed: BTreeMap<usize, String> = BTreeMap::new();
    let mut holds: BTreeMap<Reg, usize> = BTreeMap::new();
    for (p, r) in regs.iter().enumerate().take(ctx.arg_count) {
        match r {
            Reg::S(_) => {
                typed.insert(p, "float".to_owned());
            }
            Reg::D(_) => {
                typed.insert(p, "double".to_owned());
            }
            Reg::R(_) => {
                holds.insert(*r, p);
            }
        }
    }
    let mut widths: BTreeMap<usize, (BTreeSet<usize>, BTreeSet<i64>)> = BTreeMap::new();
    let order = code.get(entry).into_iter().chain(
        code.iter()
            .enumerate()
            .filter(|(b, _)| *b != entry)
            .map(|(_, c)| c),
    );
    for i in order.flatten() {
        let access = if let AOp::Load { width, addr, .. } | AOp::Store { width, addr, .. } = i.op {
            Some((usize::from(width.bytes()), addr, false))
        } else if let AOp::LoadDual { addr, .. } | AOp::StoreDual { addr, .. } = i.op {
            Some((4, addr, true))
        } else if let AOp::VLoad { vd, addr } | AOp::VStore { vd, addr } = i.op {
            Some((if matches!(vd, Reg::D(_)) { 8 } else { 4 }, addr, false))
        } else {
            None
        };
        if let Some((bytes, addr, dual)) = access
            && let Offset::Imm(d) = addr.offset
            && let Some(&p) = holds.get(&addr.base)
        {
            let e = widths.entry(p).or_default();
            e.0.insert(bytes);
            e.1.insert(i64::from(d));
            if dual {
                e.1.insert(i64::from(d) + 4);
            }
        }
        let copied = match i.op {
            AOp::Dp {
                kind: DpKind::Mov,
                rd,
                src: Operand::Reg { rm, amount: 0, .. },
                ..
            } if !i.sets => holds.get(&rm).copied().map(|p| (rd, p)),
            AOp::Dp {
                kind: DpKind::Add | DpKind::Sub,
                rd,
                rn,
                src: Operand::Imm { value: 0, .. },
            } if !i.sets => holds.get(&rn).copied().map(|p| (rd, p)),
            _ => None,
        };
        for (k, _) in live::effects(ctx, i).1 {
            if let Key::A32(r) = k {
                holds.remove(&r);
            }
        }
        if let Some((rd, p)) = copied {
            holds.insert(rd, p);
        }
    }
    for (p, (w, o)) in widths {
        typed.insert(p, pointee_type(&w, &o).to_owned());
    }
    typed
}
