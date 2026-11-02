//! Whether any caller reads an arm64 function's result after calling it.
//!
//! The arm64 counterpart of [`crate::analysis::returns`]. Each call site is
//! scanned forward from the instruction after the `bl`, down both sides of
//! every branch: a read of `x0` on any path (at any width, as an address
//! register too) means the result is used, at the width read; a write of
//! it first means it is dead there. A later call reads `x0` as its first
//! argument when its callee does (it reads `x0` before writing it in its
//! first instructions, or its import takes an argument), which hands the
//! result on as `g(f())` does; otherwise the call clobbers it. A `ret`
//! hands the result on to the caller's own callers, as a tail jump does,
//! so it is used exactly when the caller's result is. A path the scan
//! cannot follow is no evidence either way: `x0` is the next call's first
//! argument as well, so code that drops a result writes it within a few
//! instructions, and one only such paths follow is left unknown. The
//! hand-on rule runs to a fixpoint, so a chain of wrappers ending in
//! callers that discard the value returns nothing through.
//!
//! Callers that all discard the result make it nothing only when what the
//! function hands back is a callee's leftover or its own first argument:
//! one whose every return hands back a value an instruction of its own put
//! in `x0` (`mov w0, w19` before the epilogue) returns that value, read or
//! not, as an exported function's callers outside the image may, and the
//! verdict stays open ([`hands_back_own`]).
//!
//! A `float` or a `double` comes back in `v0`: read there as `s0` or `d0`
//! after the call, and nowhere as `x0`, it is the function's result at
//! that width. A function nothing calls has no call site to ask, so the
//! writes nearest its returns answer ([`float_left`]). A caller reading `x1` before writing it after the call
//! reads a second result, which a function returning a pair of words or a
//! 128-bit integer hands back there.

use crate::analysis::call_returns::{self, Facts, Own, Site};
use crate::analysis::{Analysis, BlockTerm, Function, striped};
use crate::isa::a64::{self, Flow, Insn, Reg};
use crate::program::Program;

/// Longest run of instructions scanned along one path after a call.
const SCAN_MAX: usize = 16;
/// Most paths a call site's scan follows through the caller's branches.
const PATHS_MAX: usize = 8;
/// Longest prologue read for whether a callee reads its first argument.
const LEADING_MAX: usize = 16;
/// Decodes the instruction at `va` in executable memory.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
fn decode(program: &Program, va: u64) -> Option<Insn> {
    if !crate::analysis::is_executable_va(program, va) {
        return None;
    }
    let bytes: [u8; a64::INSN_LEN] = program.read_va(va, a64::INSN_LEN)?.try_into().ok()?;
    Some(a64::decode(u32::from_le_bytes(bytes), va))
}

/// The address after an instruction.
///
/// # Arguments
///
/// * `i` - The instruction.
fn next(i: &Insn) -> u64 {
    i.va.wrapping_add(crate::num::from_usize(a64::INSN_LEN))
}

/// Tells whether a call to `target` reads `x0` as an argument: the import
/// a stub reaches takes one, or the function reads `x0` before writing it
/// in its first instructions.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `target` - The callee, when the call names one.
fn reads_first_argument(program: &Program, analysis: &Analysis, target: Option<u64>) -> bool {
    let Some(f) = target
        .and_then(|t| analysis.function(t))
        .filter(|f| Some(f.entry) == target)
    else {
        return false;
    };
    if let Some(takes) = crate::analysis::typelib::stub_takes_arguments(program, f) {
        return takes;
    }
    let mut at = f.entry;
    for _ in 0..LEADING_MAX {
        let Some(i) = decode(program, at) else {
            return false;
        };
        let regs = i.registers();
        if regs.reads.iter().any(|(r, _)| *r == Reg::X(0)) {
            return true;
        }
        if regs.writes.contains(&Reg::X(0)) || i.flow != Flow::Next {
            return false;
        }
        at = next(&i);
    }
    false
}

/// Classifies what the code after one call does with a result register.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `site` - The call's address.
/// * `from` - The calling function's entry, when known.
/// * `r` - The register: `x0`, `x1` or `v0`.
fn classify(program: &Program, analysis: &Analysis, site: u64, from: Option<u64>, r: Reg) -> Site {
    let caller = from.and_then(|e| analysis.function(e));
    let inside =
        |t: u64| caller.is_some_and(|f| f.blocks.iter().any(|b| b.start <= t && t < b.end));
    let mut paths: Vec<(u64, usize)> = vec![(site.wrapping_add(4), 0)];
    let mut found: Vec<Site> = Vec::new();
    let mut forks = 1usize;
    while let Some((mut at, mut n)) = paths.pop() {
        let outcome = loop {
            if n >= SCAN_MAX {
                break Site::Unknown;
            }
            let Some(i) = decode(program, at) else {
                break Site::Unknown;
            };
            n += 1;
            if matches!(r, Reg::V(_)) && i.operands.contains(&a64::Opnd::Other) {
                break Site::Unknown;
            }
            let regs = i.registers();
            if i.op != a64::Op::Ret
                && let Some(&(_, bits)) = regs.reads.iter().find(|(x, _)| *x == r)
            {
                break Site::Used(u8::try_from(bits).unwrap_or(u8::MAX));
            }
            match i.flow {
                Flow::Call => {
                    let passes = r == Reg::X(0)
                        && i.op == a64::Op::Bl
                        && reads_first_argument(program, analysis, i.target());
                    break if passes { Site::Used(64) } else { Site::Dead };
                }
                Flow::Return => break from.map_or(Site::Unknown, Site::Tail),
                Flow::Invalid => break Site::Dead,
                Flow::Jump => match i.target() {
                    Some(t) if inside(t) => {
                        at = t;
                        continue;
                    }
                    Some(t)
                        if r == Reg::X(0) && reads_first_argument(program, analysis, Some(t)) =>
                    {
                        break Site::Used(64);
                    }
                    Some(_) => break from.map_or(Site::Unknown, Site::Tail),
                    None => break Site::Unknown,
                },
                Flow::CondJump => {
                    if let Some(t) = i.target() {
                        if forks < PATHS_MAX {
                            forks += 1;
                            paths.push((t, n));
                        } else {
                            found.push(Site::Unknown);
                        }
                    }
                }
                Flow::Next => {}
            }
            if regs.writes.contains(&r) {
                break Site::Dead;
            }
            at = next(&i);
        };
        found.push(outcome);
    }
    Site::merge(&found)
}

/// Tells whether every return of a function hands back a value one of its
/// own instructions put in `x0` ([`call_returns::hands_back_own`]).
///
/// # Arguments
///
/// * `program` - The image.
/// * `f` - The function.
fn hands_back_own(program: &Program, f: &Function) -> bool {
    call_returns::hands_back_own(f, |b| {
        let mut insns = Vec::new();
        let mut at = b.start;
        while at < b.end {
            let i = decode(program, at)?;
            at = next(&i);
            insns.push(i);
        }
        Some(
            insns
                .iter()
                .rev()
                .find_map(|i| {
                    if i.flow == Flow::Call {
                        Some(Own::Call)
                    } else {
                        i.registers()
                            .writes
                            .contains(&Reg::X(0))
                            .then_some(Own::Written)
                    }
                })
                .unwrap_or(Own::Through),
        )
    })
}

/// Blocks walked back along a path from a `ret` for the result a function
/// nothing calls leaves ([`float_left`]).
const LEFT_DEPTH: u8 = 4;

/// The float a function nothing calls leaves in `v0`, read off the writes
/// nearest its returns.
///
/// No call site says what a caller reads, so the body answers. Walking back
/// from each `ret`, at most [`LEFT_DEPTH`] blocks along a path: a call, a
/// write of `x0` or a store of `v0` met first decides against a float, and
/// a scalar write of `v0` met first is a vote for one at that width. A
/// path that runs out of blocks first says nothing, which keeps a path the
/// code cannot take out of the answer.
///
/// # Arguments
///
/// * `program` - The image.
/// * `f` - The function.
///
/// # Returns
///
/// 32 or 64 when some return's nearest result write is a scalar `s0` or
/// `d0` and none is `x0`; `None` otherwise.
fn float_left(program: &Program, f: &Function) -> Option<u8> {
    let preds = call_returns::preds(f);
    let mut todo: Vec<(usize, u8)> = f
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| b.term == BlockTerm::Ret)
        .map(|(k, _)| (k, 1))
        .collect();
    let mut seen = vec![false; f.blocks.len()];
    let mut width: Option<u8> = None;
    while let Some((k, depth)) = todo.pop() {
        if std::mem::replace(&mut seen[k], true) {
            continue;
        }
        let b = &f.blocks[k];
        let mut insns = Vec::new();
        let mut at = b.start;
        while at < b.end {
            let i = decode(program, at)?;
            at = next(&i);
            insns.push(i);
        }
        let mut settled = false;
        for i in insns.iter().rev() {
            let regs = i.registers();
            let stored = matches!(i.mnemonic, a64::Mnemonic::Str(_) | a64::Mnemonic::Stp)
                && regs.reads.iter().any(|(r, _)| *r == Reg::V(0));
            if i.flow == Flow::Call || stored || regs.writes.contains(&Reg::X(0)) {
                return None;
            }
            if regs.writes.contains(&Reg::V(0)) {
                let bits = match i.operands[0] {
                    a64::Opnd::Reg {
                        reg: Reg::V(0),
                        bits: 32,
                    } => 32,
                    a64::Opnd::Reg {
                        reg: Reg::V(0),
                        bits: 64,
                    } => 64,
                    _ => return None,
                };
                width = Some(width.map_or(bits, |w: u8| w.max(bits)));
                settled = true;
                break;
            }
        }
        if !settled && depth < LEFT_DEPTH {
            todo.extend(preds[k].iter().map(|&p| (p, depth + 1)));
        }
    }
    width
}

/// Fills the return facts of every arm64 function from its call sites:
/// [`Function::returns_value`], [`Function::ret_width`],
/// [`Function::ret_float`] and [`Function::hands_back_rdx`] (here `x1`).
///
/// # Arguments
///
/// * `program` - The image the callers are decoded from.
/// * `analysis` - Functions and cross-references; the facts are written in
///   place.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    let shared: &Analysis = analysis;
    let regs = [Reg::X(0), Reg::V(0), Reg::X(1)];
    let facts: Vec<Facts> = striped(&shared.functions, |f| {
        call_returns::facts(shared, f, regs, |va, from, r| {
            classify(program, shared, va, from, r)
        })
    })
    .into_iter()
    .map(Option::unwrap_or_default)
    .collect();
    call_returns::settle(
        analysis,
        facts,
        |f| float_left(program, f),
        |f| hands_back_own(program, f),
    );
}
