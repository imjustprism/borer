//! What an arm64 function takes and hands back, as the arm64 procedure
//! call standard (AAPCS64) passes it.
//!
//! An integer or a pointer travels in `x0` to `x7` and a `float` or a
//! `double` in `v0` to `v7`, each sequence counted on its own, so a
//! signature lists the integer parameters a body reads in register order
//! and the floating ones after them, as a declaration interleaves them
//! when one states the positions. A function returning a structure too
//! large for registers takes the address to write it at in `x8`, an ABI
//! fact and no parameter, which the signature lists first as `result`
//! ([`abi::indirect_result_position`]). A parameter is a register of
//! these the function reads before writing it on a path from its entry
//! that no call precedes; a call or a jump out of the function reads what
//! its target takes ([`forwarded`]). A function that stores the argument
//! registers from some `x` register up to `x7` in its entry block before
//! writing them is variadic, its fixed parameters the ones below: that is
//! how it fills the save area its `va_list` walks.
//!
//! A declaration fixes the positions: the prototype an agent stated, the
//! signature the function's name came from, the SDK's prototype for its
//! name, or the type library's declaration of a C library function of the
//! same name, which a statically linked program carries its own copy of.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::super::abi;
use super::super::expr::{Expr, Key, Ty};
use super::super::lift::{self, Env};
use super::super::{Ctx, Shape, declared_arity, new_ctx, pointee_type};
use super::{decode, live};
use crate::analysis::{Analysis, Function, Overlay};
use crate::isa::a64::{self, Flow, Insn, Mnemonic, Opnd, Reg, Width};
use crate::program::Program;

/// The general registers an argument travels in, `x0` to `x7`.
pub(in crate::analysis::decompile) const INT_ARGS: u8 = 8;
/// The `v` registers a floating-point argument travels in, `v0` to `v7`.
pub(in crate::analysis::decompile) const FLOAT_ARGS: u8 = 8;
/// The register an indirect result's address travels in.
pub(in crate::analysis::decompile) const RESULT_REG: u8 = 8;
/// Most paths the parameter walk follows from the entry.
const PATHS_MAX: usize = 4096;
/// Most wrappers [`forwarded`] follows to the function that reads the
/// arguments.
const FORWARD_MAX: usize = 4;
/// Blocks followed back from a return to the last write of `x0`.
const RET_LANE_DEPTH: usize = 4;

/// The register a call passes argument position `i` in, as a float mask
/// spells the signature: integer positions take the next `x` register,
/// floating ones the next `v` register.
///
/// # Arguments
///
/// * `i` - The position.
/// * `floats` - A bit per position that is floating point.
///
/// # Returns
///
/// The register, or `None` past the registers the standard passes in.
pub(in crate::analysis::decompile) fn arg_reg(i: usize, floats: u8) -> Option<Reg> {
    let bit = |p: usize| p < 8 && (floats >> p) & 1 != 0;
    let before = (0..i).filter(|&p| bit(p)).count();
    if bit(i) {
        u8::try_from(before)
            .ok()
            .filter(|n| *n < FLOAT_ARGS)
            .map(Reg::V)
    } else {
        u8::try_from(i - before)
            .ok()
            .filter(|n| *n < INT_ARGS)
            .map(Reg::X)
    }
}

/// The bit of an argument register in a set of them: `x0` to `x8` take
/// bits 0 to 8, `v0` to `v7` bits 9 to 16.
///
/// # Arguments
///
/// * `r` - The register.
///
/// # Returns
///
/// The bit, or `None` for a register no argument travels in.
fn arg_bit(r: Reg) -> Option<u32> {
    match r {
        Reg::X(n) if n <= RESULT_REG => Some(1 << n),
        Reg::V(n) if n < FLOAT_ARGS => Some(1 << (u32::from(RESULT_REG) + 1 + u32::from(n))),
        Reg::X(_) | Reg::V(_) | Reg::Sp | Reg::Zr => None,
    }
}

/// A function's blocks and their edges, decoded for a walk of its paths.
struct Graph {
    /// Each block's instructions, in block order.
    code: Vec<Vec<Insn>>,
    /// Successor block indices per block.
    succs: Vec<Vec<usize>>,
    /// Index of the entry block.
    entry: usize,
    /// The blocks' start addresses: a jump elsewhere leaves the function.
    starts: BTreeSet<u64>,
}

impl Graph {
    /// The graph as a walk reads it.
    fn walked(&self) -> Walked<'_> {
        Walked {
            code: &self.code,
            succs: &self.succs,
            entry: self.entry,
            starts: &self.starts,
        }
    }
}

/// A function's blocks and edges as [`walk`] reads them.
#[derive(Clone, Copy)]
struct Walked<'g> {
    /// Each block's instructions, in block order.
    code: &'g [Vec<Insn>],
    /// Successor block indices per block.
    succs: &'g [Vec<usize>],
    /// Index of the entry block.
    entry: usize,
    /// The blocks' start addresses: a jump elsewhere leaves the function.
    starts: &'g BTreeSet<u64>,
}

/// Decodes a function's blocks and edges.
///
/// # Arguments
///
/// * `ctx` - Any function's context, for the image.
/// * `f` - The function.
fn graph(ctx: &Ctx<'_>, f: &Function) -> Graph {
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
    Graph {
        code: decode_blocks(ctx, f),
        succs,
        entry: idx.get(&f.entry).copied().unwrap_or(0),
        starts: idx.keys().copied().collect(),
    }
}

/// Walks a function's paths from its entry and finds the argument
/// registers read before being written on one that no call precedes.
///
/// A call ends a path. When `follow` is set, it reads the registers its
/// callee takes ([`forwarded`]), as a jump out of the function does; a
/// register read through a call's target reads it too. A vector form's
/// `v` registers, which the decoder leaves unmodeled, are no evidence.
///
/// # Arguments
///
/// * `ctx` - Any function's context, for the image and the callees.
/// * `g` - The function's blocks, their edges, its entry block and the
///   blocks' starts.
/// * `follow` - Read what calls and jumps out hand on.
///
/// # Returns
///
/// The registers read.
fn walk(ctx: &Ctx<'_>, g: Walked<'_>, follow: bool) -> BTreeSet<Reg> {
    let mut found: BTreeSet<Reg> = BTreeSet::new();
    let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
    let mut work: Vec<(usize, u32)> = vec![(g.entry, 0)];
    let take = |found: &mut BTreeSet<Reg>, written: u32, r: Reg| {
        if arg_bit(r).is_some_and(|bit| written & bit == 0) {
            found.insert(r);
        }
    };
    while let Some((b, mut written)) = work.pop() {
        if seen.len() >= PATHS_MAX || !seen.insert((b, written)) {
            continue;
        }
        let Some(instrs) = g.code.get(b) else {
            continue;
        };
        let mut stopped = false;
        for i in instrs {
            match i.flow {
                Flow::Call => {
                    if let (a64::Op::Blr, Opnd::Reg { reg, .. }) = (i.op, i.operands[0]) {
                        take(&mut found, written, reg);
                    }
                    if follow {
                        for r in forwarded(ctx, i.target()) {
                            take(&mut found, written, r);
                        }
                    }
                    stopped = true;
                    break;
                }
                Flow::Jump if i.op == a64::Op::B => {
                    if follow && i.target().is_some_and(|t| !g.starts.contains(&t)) {
                        for r in forwarded(ctx, i.target()) {
                            take(&mut found, written, r);
                        }
                    }
                    continue;
                }
                Flow::Return => continue,
                Flow::Next | Flow::CondJump | Flow::Jump | Flow::Invalid => {}
            }
            let vector = i.operands.contains(&Opnd::Other);
            let regs = i.registers();
            for (r, _) in regs.reads {
                if !(vector && matches!(r, Reg::V(_))) {
                    take(&mut found, written, r);
                }
            }
            for r in regs.writes {
                if let Some(bit) = arg_bit(r) {
                    written |= bit;
                }
            }
        }
        if !stopped {
            for &s in g.succs.get(b).into_iter().flatten() {
                work.push((s, written));
            }
        }
    }
    found
}

/// The argument registers a call or jump to `target` hands on to it.
///
/// They are what a declaration says the callee takes
/// ([`declared_callee`]), else what its body reads before writing on a path
/// from its entry that no call precedes, and, when its entry block hands
/// the registers on untouched to another function, what that one reads, up
/// to [`FORWARD_MAX`] links. A variadic callee takes its fixed registers
/// only ([`variadic_fixed`]).
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the overlay.
/// * `target` - The callee, when the call names one.
pub(in crate::analysis::decompile) fn forwarded(ctx: &Ctx<'_>, target: Option<u64>) -> Vec<Reg> {
    let Some(t) = target.filter(|t| *t != 0) else {
        return Vec::new();
    };
    let mut out: BTreeSet<Reg> = BTreeSet::new();
    let mut shadow: BTreeSet<Reg> = BTreeSet::new();
    let mut seen: BTreeSet<u64> = BTreeSet::from([t]);
    let mut at = t;
    while seen.len() <= FORWARD_MAX {
        if let Some((count, floats, _)) = declared_callee(ctx, at) {
            out.extend(
                (0..count)
                    .filter_map(|i| arg_reg(i, floats))
                    .filter(|r| !shadow.contains(r)),
            );
            break;
        }
        let Some(f) = ctx.analysis.function(at).filter(|f| f.entry == at) else {
            break;
        };
        let g = graph(ctx, f);
        let mut read = walk(ctx, g.walked(), false);
        let first = g.code.get(g.entry).map_or(&[][..], Vec::as_slice);
        if let Some(fixed) = variadic_fixed(first) {
            read.retain(|r| matches!(r, Reg::X(n) if usize::from(*n) < fixed));
        }
        out.extend(read.difference(&shadow));
        let written: BTreeSet<Reg> = first
            .iter()
            .flat_map(|i| i.registers().writes)
            .filter(|r| arg_bit(*r).is_some())
            .collect();
        let onward = first.last().and_then(|i| match i.flow {
            Flow::Call | Flow::Jump => i.target().filter(|n| !g.starts.contains(n)),
            Flow::Next | Flow::CondJump | Flow::Return | Flow::Invalid => None,
        });
        shadow.extend(written);
        match onward {
            Some(n) if seen.insert(n) && shadow.is_empty() => at = n,
            Some(_) | None => break,
        }
    }
    out.into_iter().collect()
}

/// What a declaration says a callee takes.
///
/// The declaration is the prototype stated for it, the prototype of the
/// import it reaches through a stub or a slot, or the type library's
/// declaration of the C library function it is named after, which a
/// statically linked program carries its own copy of.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the overlay.
/// * `t` - The callee's entry, or the import slot a call goes through.
///
/// # Returns
///
/// The positions, a bit per floating one, and whether a variable list
/// follows; `None` when nothing declares the callee.
pub(in crate::analysis::decompile) fn declared_callee(
    ctx: &Ctx<'_>,
    t: u64,
) -> Option<(usize, u8, bool)> {
    let f = ctx.analysis.function(t).filter(|f| f.entry == t);
    if let Some(f) = f
        && ctx.overlay.prototypes.contains_key(&t)
    {
        return declared_arity(ctx, f, 0)
            .map(|(count, floats, variadic, _)| (count, floats, variadic));
    }
    if let Some(p) = lift::import_prototype(ctx, Some(t)) {
        let floats = p.floats.checked_shl(u32::from(p.this)).unwrap_or(0);
        return Some((
            usize::from(p.params) + usize::from(p.this),
            floats,
            p.variadic,
        ));
    }
    f.and_then(|f| library_arity(ctx, f))
}

/// The arity the type library declares for the C library function a
/// function is named after.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the overlay.
/// * `f` - The function.
///
/// # Returns
///
/// The positions, a bit per floating one, and whether a variable list
/// follows; `None` when the library declares no function of its name.
fn library_arity(ctx: &Ctx<'_>, f: &Function) -> Option<(usize, u8, bool)> {
    let name = crate::analysis::name_of(ctx.analysis, ctx.overlay, f.entry);
    let d =
        crate::analysis::typelib::declared(crate::analysis::bare_name(&name), ctx.program.format)?;
    let p = lift::library_prototype(d, 64, ctx.program.format);
    Some((usize::from(p.params), p.floats, p.variadic))
}

/// Finds the argument registers a function reads before writing them on
/// some path from its entry that no call precedes, a call reading what its
/// callee takes.
///
/// # Arguments
///
/// * `ctx` - The function's context.
/// * `code` - Each block's instructions.
/// * `succs` - Successor block indices per block.
/// * `entry` - Index of the entry block.
fn detect(ctx: &Ctx<'_>, code: &[Vec<Insn>], succs: &[Vec<usize>], entry: usize) -> BTreeSet<Reg> {
    let g = Walked {
        code,
        succs,
        entry,
        starts: &ctx.block_starts,
    };
    walk(ctx, g, true)
}

/// Returns the fixed parameters of a variadic function: the entry block
/// stores the argument registers from this one up to `x7` before writing
/// any of them, which fills the save area its `va_list` walks.
///
/// # Arguments
///
/// * `entry` - The entry block's instructions.
///
/// # Returns
///
/// How many registers below the stored run are fixed parameters; `None`
/// when the function is not variadic that way.
fn variadic_fixed(entry: &[Insn]) -> Option<usize> {
    let mut stored: BTreeSet<u8> = BTreeSet::new();
    let mut written: u32 = 0;
    for i in entry {
        if i.flow != Flow::Next {
            break;
        }
        if matches!(i.mnemonic, Mnemonic::Str(Width::Reg) | Mnemonic::Stp) {
            for o in i.operands.iter().take(2) {
                if let Opnd::Reg { reg: Reg::X(n), .. } = *o
                    && n < INT_ARGS
                    && arg_bit(Reg::X(n)).is_some_and(|b| written & b == 0)
                {
                    stored.insert(n);
                }
            }
        }
        for r in i.registers().writes {
            if let Some(bit) = arg_bit(r) {
                written |= bit;
            }
        }
    }
    let last = INT_ARGS - 1;
    if !stored.contains(&last) || !stored.contains(&(last - 1)) {
        return None;
    }
    let low = (0..=last).rev().take_while(|n| stored.contains(n)).last()?;
    Some(usize::from(low))
}

/// Reads what an arm64 function takes ([`Shape`]) from its code and the
/// declarations that state it.
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
    let read = detect(ctx, code, succs, entry);
    let ints = read
        .iter()
        .filter_map(|r| match r {
            Reg::X(n) if *n < INT_ARGS => Some(usize::from(*n) + 1),
            Reg::X(_) | Reg::V(_) | Reg::Sp | Reg::Zr => None,
        })
        .max()
        .unwrap_or(0);
    let floats_read = read
        .iter()
        .filter_map(|r| match r {
            Reg::V(n) => Some(usize::from(*n) + 1),
            Reg::X(_) | Reg::Sp | Reg::Zr => None,
        })
        .max()
        .unwrap_or(0);
    let declared = declared_arity(ctx, f, 0)
        .map(|(count, floats, variadic, _)| (count, floats, variadic))
        .or_else(|| library_arity(ctx, f));
    let (count, floats, variadic) = match declared {
        Some(d) => d,
        None => match code.get(entry).and_then(|c| variadic_fixed(c)) {
            Some(fixed) => (fixed, 0, true),
            None => {
                let mask = (ints..ints + floats_read)
                    .filter(|p| *p < 8)
                    .fold(0u8, |m, p| m | (1 << p));
                (ints + floats_read, mask, false)
            }
        },
    };
    let result = read.contains(&Reg::X(RESULT_REG));
    let result_param = result.then(|| u8::try_from(count).ok()).flatten();
    Shape {
        conv: &abi::AAPCS64,
        params: Vec::new(),
        variadic,
        this_param: false,
        result_param,
        count: count + usize::from(result_param.is_some()),
        stack: 0,
        stated_short: None,
        float_mask: Some(floats),
    }
}

/// Returns what a call's arm64 callee takes, read once per function and
/// overlay through [`Analysis::derived`].
///
/// # Arguments
///
/// * `ctx` - The calling function's context.
/// * `target` - The callee's entry.
///
/// # Returns
///
/// The shape, or `None` when no function starts there, it is an import's
/// stub, or its one instruction hands nothing on.
pub(in crate::analysis::decompile) fn callee_shape(
    ctx: &Ctx<'_>,
    target: u64,
) -> Option<Arc<Shape>> {
    let forwards = |i: Insn| {
        i.op == a64::Op::B
            && i.target().is_some_and(|n| {
                n != target && ctx.analysis.function(n).is_some_and(|g| g.entry == n)
            })
    };
    let f = ctx.analysis.function(target).filter(|f| {
        f.entry == target
            && f.thunk.is_none()
            && (f.instr_count > 1 || decode(ctx.program, target).is_some_and(forwards))
    })?;
    Some(abi::shape(ctx.program, ctx.analysis, ctx.overlay, f, 64))
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
pub(in crate::analysis::decompile) fn built(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
) -> Shape {
    let starts = f.blocks.iter().map(|b| b.start).collect();
    let ctx = new_ctx(program, analysis, overlay, f, 64, starts, &[]);
    let g = graph(&ctx, f);
    shape(&ctx, f, &g.code, &g.succs, g.entry)
}

/// Decodes every block of a function, in block order.
///
/// # Arguments
///
/// * `ctx` - The function's context, for the image.
/// * `f` - The function.
pub(in crate::analysis::decompile) fn decode_blocks(ctx: &Ctx<'_>, f: &Function) -> Vec<Vec<Insn>> {
    f.blocks
        .iter()
        .map(|b| {
            let mut v = Vec::new();
            let mut va = b.start;
            while va < b.end {
                let Some(i) = decode(ctx.program, va) else {
                    break;
                };
                va = va.wrapping_add(crate::num::from_usize(a64::INSN_LEN));
                v.push(i);
            }
            v
        })
        .collect()
}

/// Returns the state at an arm64 function's entry: each parameter in its
/// register, an indirect result's address in `x8`.
///
/// # Arguments
///
/// * `ctx` - The function's parameters.
pub(in crate::analysis::decompile) fn entry_env(ctx: &Ctx<'_>) -> Env {
    let mut env = Env::entry();
    let declared = ctx.arg_count - usize::from(ctx.result_param.is_some());
    for p in 0..declared {
        if let (Some(r), Ok(i)) = (arg_reg(p, ctx.arg_floats), u8::try_from(p)) {
            env.vals.insert(Key::A64(r), Expr::Var(Key::Param(i)));
        }
    }
    if let Some(i) = ctx.result_param {
        env.vals
            .insert(Key::A64(Reg::X(RESULT_REG)), Expr::Var(Key::Param(i)));
    }
    env
}

/// Tells whether an instruction other than a call writes the register the
/// function hands its result back in: `x0`, or `v0` for a float.
///
/// # Arguments
///
/// * `ctx` - The function's state.
/// * `code` - Each block's instructions.
pub(in crate::analysis::decompile) fn writes_result(ctx: &Ctx<'_>, code: &[Vec<Insn>]) -> bool {
    let back = Key::A64(if ctx.ret_float { Reg::V(0) } else { Reg::X(0) });
    code.iter()
        .flatten()
        .filter(|i| i.flow != Flow::Call)
        .any(|i| live::effects(ctx, i).1.iter().any(|(k, _)| *k == back))
}

/// The width of the last write of `x0` in a block, when it has one.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
///
/// # Returns
///
/// 32 for a `w0` write, 64 for any other write of `x0`, a call's included.
fn last_x0_write(instrs: &[Insn]) -> Option<u8> {
    instrs.iter().rev().find_map(|i| {
        if i.flow == Flow::Call {
            return Some(64);
        }
        match i.operands[0] {
            Opnd::Reg {
                reg: Reg::X(0),
                bits,
            } if !matches!(
                i.mnemonic,
                Mnemonic::Str(_)
                    | Mnemonic::Stp
                    | Mnemonic::Ccmp
                    | Mnemonic::Ccmn
                    | Mnemonic::Atomic(..)
                    | Mnemonic::Prfm
            ) && !matches!(
                i.op,
                a64::Op::Cbz | a64::Op::Cbnz | a64::Op::Tbz | a64::Op::Tbnz
            ) =>
            {
                Some(if bits == 32 { 32 } else { 64 })
            }
            Opnd::Reg { .. }
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => None,
        }
    })
}

/// Width in bits of the value an arm64 function's `ret` hands back in
/// `x0`: a declared return type's, else 32 when the last write of `x0`
/// before every `ret` writes `w0`, else the whole register.
///
/// # Arguments
///
/// * `code` - Each block's instructions.
/// * `succs` - Successor block indices per block.
/// * `declared` - The signature's return type when one is known.
pub(in crate::analysis::decompile) fn ret_lane(
    code: &[Vec<Insn>],
    succs: &[Vec<usize>],
    declared: Option<&str>,
) -> u8 {
    if let Some(d) = declared {
        return lift::declared_bits(d);
    }
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); code.len()];
    for (b, ss) in succs.iter().enumerate() {
        for &s in ss {
            if let Some(p) = preds.get_mut(s) {
                p.push(b);
            }
        }
    }
    let mut lane = 0u8;
    for (b, instrs) in code.iter().enumerate() {
        if instrs.last().is_none_or(|i| i.flow != Flow::Return) {
            continue;
        }
        let mut at = b;
        let mut width = None;
        for _ in 0..RET_LANE_DEPTH {
            width = code.get(at).and_then(|c| last_x0_write(c));
            match (width, preds.get(at).map(Vec::as_slice)) {
                (None, Some([p])) => at = *p,
                _ => break,
            }
        }
        lane = lane.max(width.unwrap_or(64));
    }
    if lane == 0 { 64 } else { lane }
}

/// The width in bytes a load or store moves through its memory operand,
/// for each register it moves.
///
/// # Arguments
///
/// * `i` - The instruction.
fn access_bytes(i: &Insn) -> Option<usize> {
    let width = if let Mnemonic::Ldr(w) | Mnemonic::Str(w) | Mnemonic::Ldp(w) = i.mnemonic {
        w
    } else if i.mnemonic == Mnemonic::Stp {
        Width::Reg
    } else {
        return None;
    };
    match width {
        Width::Reg => match i.operands[0] {
            Opnd::Reg { bits, .. } => Some(usize::from(bits / 8)),
            Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => None,
        },
        Width::Byte | Width::SByte => Some(1),
        Width::Half | Width::SHalf => Some(2),
        Width::SWord => Some(4),
    }
}

/// The copy of a parameter an instruction makes: `mov xd, xs` carries it,
/// `add xd, xs, #k` carries it `k` bytes on.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `holds` - The registers holding a parameter, with its position and
///   the offset from it.
///
/// # Returns
///
/// The register written and what it then holds, when it holds a copy.
fn copy_of(i: &Insn, holds: &BTreeMap<Reg, (usize, i64)>) -> Option<(Reg, (usize, i64))> {
    let (Opnd::Reg { reg: d, bits: 64 }, Opnd::Reg { reg: s, bits: 64 }) =
        (i.operands[0], i.operands[1])
    else {
        return None;
    };
    if i.mnemonic == Mnemonic::Orr
        && s == Reg::Zr
        && let Opnd::Reg {
            reg: from,
            bits: 64,
        } = i.operands[2]
    {
        return holds.get(&from).map(|h| (d, *h));
    }
    if i.mnemonic == Mnemonic::Add
        && let Opnd::Imm(k) = i.operands[2]
    {
        return holds
            .get(&s)
            .map(|&(p, at)| (d, (p, at.saturating_add(k.cast_signed()))));
    }
    None
}

/// Infers which parameters of an arm64 function are pointers, from loads
/// and stores through the register holding one, or a copy of it or an
/// offset from it.
///
/// # Arguments
///
/// * `ctx` - The function's parameters.
/// * `code` - Each block's instructions.
/// * `entry` - Index of the entry block.
///
/// # Returns
///
/// The C type per parameter position, for the parameters accessed as
/// pointers, and for a floating parameter whose register was first read
/// as a double.
pub(in crate::analysis::decompile) fn param_types(
    ctx: &Ctx<'_>,
    code: &[Vec<Insn>],
    entry: usize,
) -> BTreeMap<usize, String> {
    /// Accesses through one parameter.
    #[derive(Default)]
    struct Seen {
        /// Access widths, in bytes.
        widths: BTreeSet<usize>,
        /// Displacements from the pointer.
        offsets: BTreeSet<i64>,
    }
    let declared = ctx.arg_count - usize::from(ctx.result_param.is_some());
    let mut holds: BTreeMap<Reg, (usize, i64)> = (0..declared)
        .filter_map(|p| match arg_reg(p, ctx.arg_floats)? {
            r @ Reg::X(_) => Some((r, (p, 0))),
            Reg::V(_) | Reg::Sp | Reg::Zr => None,
        })
        .collect();
    let mut seen: BTreeMap<usize, Seen> = BTreeMap::new();
    let order = code.get(entry).into_iter().chain(
        code.iter()
            .enumerate()
            .filter(|(b, _)| *b != entry)
            .map(|(_, c)| c),
    );
    for i in order.flatten() {
        if let Some(bytes) = access_bytes(i)
            && let Some(Opnd::Mem(m)) = i.operands.iter().find(|o| matches!(o, Opnd::Mem(_)))
            && m.index.is_none()
            && let Some(&(p, at)) = holds.get(&m.base)
        {
            let s = seen.entry(p).or_default();
            s.widths.insert(bytes);
            let disp = if m.mode == a64::Mode::PostIndex {
                0
            } else {
                m.disp
            };
            s.offsets.insert(at.saturating_add(disp));
        }
        let copied = copy_of(i, &holds);
        for (k, _) in live::effects(ctx, i).1 {
            if let Key::A64(r) = k {
                holds.remove(&r);
            }
        }
        if let Some((d, h)) = copied {
            holds.insert(d, h);
        }
    }
    let mut typed: BTreeMap<usize, String> = seen
        .into_iter()
        .map(|(p, s)| (p, pointee_type(&s.widths, &s.offsets).to_owned()))
        .collect();
    for p in 0..declared {
        if typed.contains_key(&p) {
            continue;
        }
        let Some(r @ Reg::V(_)) = arg_reg(p, ctx.arg_floats) else {
            continue;
        };
        if matches!(ctx.reg_ty.get(&Key::A64(r)), Some(Ty::F64)) {
            typed.insert(p, "double".to_owned());
        }
    }
    typed
}
