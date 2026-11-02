//! What a RISC-V function takes and hands back, as the calling convention
//! passes it ([`super::super::abi::rv`]).
//!
//! A parameter is an argument register the function reads before writing
//! it on a path from its entry that no call precedes, or that a call or a
//! jump out on such a path hands on to a callee that takes it: `a0` to
//! `a7`, then `fa0` to `fa7`. The float ones come first, up to the
//! highest read, then the integer ones up to the highest read. A
//! declaration, when one states the function, fixes the positions instead,
//! those past the registers taking stack words, and says whether a
//! variable list follows. A body is not read for stack arguments.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::super::abi::{self, rv as rv_abi};
use super::super::expr::{Expr, Key};
use super::super::lift::{self, Env};
use super::super::{Ctx, Shape, declared_arity, new_ctx, pointee_type};
use super::{decode_blocks, live};
use crate::analysis::{Analysis, Function, Overlay};
use crate::isa::rv::{Alu, Flow, Fmt, Insn, Op as ROp, Reg, Xlen};
use crate::program::Program;

/// Most paths the parameter walk follows from the entry.
const PATHS_MAX: usize = 4096;
/// Most functions [`forwarded`] follows down a chain of wrappers.
const FORWARD_MAX: usize = 4;

/// Returns the register width in bits, as a shape is built at.
///
/// # Arguments
///
/// * `program` - The image.
fn bitness(program: &Program) -> u32 {
    super::xlen(program).bits()
}

/// The register a call passes argument position `i` in when nothing says
/// more than a float mask: integer positions take `a0` to `a7`, floating
/// ones `fa0` to `fa7`, each bank counting its own.
///
/// # Arguments
///
/// * `i` - The position.
/// * `floats` - A bit per floating position.
///
/// # Returns
///
/// The register, or `None` past the registers the convention passes in.
pub(in crate::analysis::decompile) fn arg_reg(i: usize, floats: u8) -> Option<Reg> {
    let bit = |p: usize| p < 8 && (floats >> p) & 1 != 0;
    let before = (0..i).filter(|&p| bit(p)).count();
    let (make, k, count): (fn(u8) -> Reg, usize, u8) = if bit(i) {
        (Reg::F, before, rv_abi::FLOAT_ARGS)
    } else {
        (Reg::X, i - before, rv_abi::INT_ARGS)
    };
    u8::try_from(k)
        .ok()
        .filter(|n| *n < count)
        .map(|n| make(rv_abi::FIRST_ARG + n))
}

/// The bit of an argument register in a set of them: `a0` to `a7` take
/// bits 0 to 7, `fa0` to `fa7` bits 8 to 15.
///
/// # Arguments
///
/// * `r` - The register.
fn arg_bits(r: Reg) -> u32 {
    let at = |n: u8, count: u8| {
        n.checked_sub(rv_abi::FIRST_ARG)
            .filter(|k| *k < count)
            .map(u32::from)
    };
    match r {
        Reg::X(n) => at(n, rv_abi::INT_ARGS).map_or(0, |k| 1 << k),
        Reg::F(n) => at(n, rv_abi::FLOAT_ARGS).map_or(0, |k| 1 << (8 + k)),
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
    let xlen = super::xlen(ctx.program);
    let mut found = BTreeSet::new();
    let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
    let mut work = vec![(entry, 0u32)];
    let take = |found: &mut BTreeSet<Reg>, written: u32, r: Reg| {
        let bits = arg_bits(r);
        if bits != 0 && bits & written == 0 {
            found.insert(r);
        }
    };
    while let Some((b, mut written)) = work.pop() {
        if seen.len() >= PATHS_MAX || !seen.insert((b, written)) {
            continue;
        }
        let Some(instrs) = code.get(b) else { continue };
        let mut stopped = false;
        let mut prev = None;
        for i in instrs {
            let target = super::transfer_target(prev, i, xlen);
            prev = Some(i);
            let out = match i.flow() {
                Flow::Call => true,
                Flow::Jump => target.is_none_or(|t| !starts.contains(&t)),
                Flow::Next | Flow::CondJump | Flow::Return | Flow::Invalid => false,
            };
            if out && follow {
                for r in forwarded(ctx, target) {
                    take(&mut found, written, r);
                }
            }
            let regs = i.registers();
            for r in regs.reads {
                take(&mut found, written, r);
            }
            if i.flow() == Flow::Call {
                stopped = true;
                break;
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

/// Returns the argument registers a call or a jump out hands on to
/// `target`.
///
/// They are what a declaration says the callee takes, else what its body
/// reads before writing on a path from its entry that no call precedes,
/// and, when its entry block hands the registers on untouched to another
/// function, what that one reads, down to [`FORWARD_MAX`] functions.
///
/// # Arguments
///
/// * `ctx` - Any function's context, for the image and the callees.
/// * `target` - The callee, when the transfer names one.
fn forwarded(ctx: &Ctx<'_>, target: Option<u64>) -> Vec<Reg> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut at = target;
    while let Some(t) = at.filter(|t| seen.len() < FORWARD_MAX && seen.insert(*t)) {
        let Some(f) = ctx.analysis.function(t).filter(|f| f.entry == t) else {
            break;
        };
        let starts: BTreeSet<u64> = f.blocks.iter().map(|b| b.start).collect();
        let bits = bitness(ctx.program);
        let fctx = new_ctx(
            ctx.program,
            ctx.analysis,
            ctx.overlay,
            f,
            bits,
            starts.clone(),
            &[],
        );
        if let Some((count, floats, _, _)) = declared_arity(&fctx, f, 0) {
            out.extend((0..count).filter_map(|i| arg_reg(i, floats)));
            break;
        }
        let (code, succs, entry) = graph(&fctx, f);
        out.extend(walk(&fctx, &code, &succs, entry, false));
        let first = code.get(entry).map_or(&[][..], Vec::as_slice);
        let untouched = first
            .iter()
            .all(|i| i.registers().writes.iter().all(|r| arg_bits(*r) == 0));
        let prev = first.len().checked_sub(2).and_then(|k| first.get(k));
        at = first
            .last()
            .filter(|i| untouched && matches!(i.flow(), Flow::Call | Flow::Jump))
            .and_then(|i| super::transfer_target(prev, i, super::xlen(ctx.program)))
            .filter(|n| !starts.contains(n));
    }
    out.into_iter().collect()
}

/// Orders the argument registers a function reads into its parameter
/// list: the float ones up to the highest read, then the integer ones up
/// to the highest read.
///
/// The float ones come first so the eight-position float mask a shape
/// carries ([`float_mask`]) holds every one of them, `fa0` to `fa7`, and
/// a declaration built from the mask places each where the body reads it.
///
/// # Arguments
///
/// * `read` - The registers read.
fn ordered(read: &BTreeSet<Reg>) -> Vec<Reg> {
    let top = |float: bool| {
        read.iter()
            .filter(|r| matches!(r, Reg::F(_)) == float)
            .map(|r| arg_bits(*r).trailing_zeros() % 8 + 1)
            .max()
            .unwrap_or(0)
    };
    let bank = |make: fn(u8) -> Reg, n: u32| {
        (0..n).filter_map(move |k| u8::try_from(k).ok().map(|k| make(rv_abi::FIRST_ARG + k)))
    };
    bank(Reg::F, top(true))
        .chain(bank(Reg::X, top(false)))
        .collect()
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
        "rv args",
        ctx.overlay.fingerprint(),
        entry,
        || {
            let starts = f.blocks.iter().map(|b| b.start).collect();
            let bits = bitness(ctx.program);
            let fctx = new_ctx(ctx.program, ctx.analysis, ctx.overlay, f, bits, starts, &[]);
            if let Some((count, floats, _, _)) = declared_arity(&fctx, f, 0) {
                return (0..count).filter_map(|i| arg_reg(i, floats)).collect();
            }
            let (code, succs, entry) = graph(&fctx, f);
            ordered(&walk(&fctx, &code, &succs, entry, true))
        },
        |v: &Vec<Reg>| v.capacity(),
    ))
}

/// Decodes a function's blocks and edges.
///
/// # Arguments
///
/// * `ctx` - The function's context.
/// * `f` - The function.
///
/// # Returns
///
/// Each block's instructions, each block's successors as block indices,
/// and the entry block's index.
fn graph(ctx: &Ctx<'_>, f: &Function) -> (Vec<Vec<Insn>>, Vec<Vec<usize>>, usize) {
    let (succs, entry) = lift::edges(f);
    (decode_blocks(ctx.program, f), succs, entry)
}

/// The float mask of a parameter list: a bit per position held in a float
/// register.
///
/// # Arguments
///
/// * `regs` - The registers in position order.
fn float_mask(regs: &[Reg]) -> u8 {
    regs.iter()
        .take(8)
        .enumerate()
        .filter(|(_, r)| matches!(r, Reg::F(_)))
        .fold(0u8, |m, (i, _)| m | (1 << i))
}

/// Reads what a RISC-V function takes ([`Shape`]).
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
    let (regs, stack, variadic) = match declared_arity(ctx, f, 0) {
        Some((count, floats, variadic, _)) => {
            let regs: Vec<Reg> = (0..count).filter_map(|i| arg_reg(i, floats)).collect();
            let stack = count.saturating_sub(regs.len());
            (regs, stack, variadic)
        }
        None => (ordered(&walk(ctx, code, succs, entry, true)), 0, false),
    };
    let conv = match super::xlen(ctx.program) {
        Xlen::X32 => &abi::RISCV_ILP32,
        Xlen::X64 => &abi::RISCV_LP64,
    };
    Shape {
        conv,
        params: Vec::new(),
        variadic,
        this_param: false,
        result_param: None,
        count: regs.len() + stack,
        stack: u32::try_from(stack).unwrap_or(0),
        stated_short: None,
        float_mask: Some(float_mask(&regs)),
    }
}

/// Returns what a call's RISC-V callee takes, read once per function and
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
        bitness(ctx.program),
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
    let ctx = new_ctx(program, analysis, overlay, f, bitness(program), starts, &[]);
    let (code, succs, entry) = graph(&ctx, f);
    shape(&ctx, f, &code, &succs, entry)
}

/// The parameter registers of the function a context is for.
///
/// # Arguments
///
/// * `ctx` - The function's context.
fn params_of(ctx: &Ctx<'_>) -> Vec<Reg> {
    ctx.block_starts
        .iter()
        .nth(ctx.entry_block)
        .and_then(|e| arg_regs(ctx, *e))
        .map(|a| a.to_vec())
        .unwrap_or_default()
}

/// Returns the state at a function's entry: each parameter in its
/// register.
///
/// # Arguments
///
/// * `ctx` - The function's context.
pub(in crate::analysis::decompile) fn entry_env(ctx: &Ctx<'_>) -> Env {
    let mut env = Env::entry();
    for (p, r) in params_of(ctx).iter().enumerate().take(ctx.arg_count) {
        if let Ok(i) = u8::try_from(p) {
            env.vals.insert(Key::Rv(*r), Expr::Var(Key::Param(i)));
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
    let back = Key::Rv(super::call::result_reg(ctx));
    code.iter()
        .flatten()
        .filter(|i| i.flow() != Flow::Call)
        .any(|i| live::effects(ctx, i).1.iter().any(|(k, _)| *k == back))
}

/// Width in bits of the value a return hands back: a declared return
/// type's, else the register width.
///
/// # Arguments
///
/// * `declared` - The signature's return type when one is known.
/// * `bitness` - The register width: 32 or 64.
pub(in crate::analysis::decompile) fn ret_lane(declared: Option<&str>, bitness: u32) -> u8 {
    declared.map_or_else(|| u8::try_from(bitness).unwrap_or(64), lift::declared_bits)
}

/// Infers the types of a RISC-V function's parameters: a pointer read or
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
    let mut typed: BTreeMap<usize, String> = BTreeMap::new();
    let mut holds: BTreeMap<Reg, usize> = BTreeMap::new();
    let mut floats: BTreeMap<Reg, usize> = BTreeMap::new();
    for (p, r) in params_of(ctx).iter().enumerate().take(ctx.arg_count) {
        match r {
            Reg::F(_) => {
                typed.insert(p, "double".to_owned());
                floats.insert(*r, p);
            }
            Reg::X(_) => {
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
        let access = match i.op {
            ROp::Load {
                width, rs1, off, ..
            }
            | ROp::Store {
                width, rs1, off, ..
            } => Some((usize::from(width.bytes()), rs1, off)),
            _ => None,
        };
        if let Some((bytes, base, off)) = access
            && let Some(&p) = holds.get(&base)
        {
            let e = widths.entry(p).or_default();
            e.0.insert(bytes);
            e.1.insert(off);
        }
        let copied = match i.op {
            ROp::Imm {
                op: Alu::Add,
                rd,
                rs1,
                imm: 0,
                word: false,
            } => holds.get(&rs1).copied().map(|p| (rd, p)),
            _ => None,
        };
        if let ROp::Float(f) = i.op {
            let read = f.reads_fmt();
            for r in i.registers().reads {
                if let (Some(p), Some(fmt)) = (floats.remove(&r), read) {
                    let name = if fmt == Fmt::S { "float" } else { "double" };
                    typed.insert(p, name.to_owned());
                }
            }
        }
        for (k, _) in live::effects(ctx, i).1 {
            if let Key::Rv(r) = k {
                holds.remove(&r);
                floats.remove(&r);
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
