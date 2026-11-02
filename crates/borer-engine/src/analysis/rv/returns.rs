//! Whether any caller reads a RISC-V function's result after calling it.
//!
//! The RISC-V reading of [`crate::analysis::call_returns`], as arm64 reads
//! its own. Each call site is scanned forward from the instruction after
//! the call, down both sides of every branch: a read of `a0` on any path
//! means the result is used; a write of it first means it is dead there. A
//! later call reads `a0` as its first argument when its callee does (it
//! reads `a0` before writing it in its first instructions, or its import
//! takes an argument), which hands the result on as `g(f())` does;
//! otherwise the call clobbers it. A jump out to another function reads
//! as a call to it. A return hands the result on to the caller's own
//! callers. A path the scan cannot follow is no
//! evidence either way, and neither is one that meets an instruction
//! whose registers are not modeled: an `ecall` may read any argument
//! register.
//!
//! A `float` or a `double` comes back in `fa0`: read there after the call,
//! at the width the reading instruction takes, and nowhere as `a0`, it is
//! the function's result, and so it is when a later call takes `fa0` as
//! its first float argument. A caller reading `a1` before writing it reads a
//! second result. A function nothing calls has no call site to ask and is
//! left unknown. A result is read at the register's full width: no read is
//! taken as evidence of a narrow one.

use std::collections::BTreeMap;

use super::{decode, paired, upper};
use crate::analysis::call_returns::{self, Facts, Own, Site};
use crate::analysis::{Analysis, Function, striped};
use crate::isa::rv::{FOp, Flow, Fmt, Insn, Op, Reg, Xlen};
use crate::program::Program;

/// Longest run of instructions scanned along one path after a call.
const SCAN_MAX: usize = 16;
/// Most paths a call site's scan follows through the caller's branches.
const PATHS_MAX: usize = 8;
/// Longest prologue read for whether a callee reads its first argument.
const LEADING_MAX: usize = 16;
/// The integer result register and first argument, `a0`.
const A0: Reg = Reg::X(10);
/// The second integer result register, `a1`.
const A1: Reg = Reg::X(11);
/// The float result register, `fa0`.
const FA0: Reg = Reg::F(10);

/// Returns where a transfer goes: its own target, or the address the
/// `auipc` or `lui` right before it built.
///
/// # Arguments
///
/// * `prev` - The instruction before, when one was read.
/// * `i` - The transfer.
/// * `xlen` - The register width.
fn target(prev: Option<&Insn>, i: &Insn, xlen: Xlen) -> Option<u64> {
    i.target().or_else(|| {
        let hi: BTreeMap<Reg, u64> = prev.and_then(|p| upper(p, xlen)).into_iter().collect();
        paired(&hi, i, xlen)
    })
}

/// Returns the width at which an instruction reads `r`, when it reads it:
/// a float register at the format the instruction takes it in, an integer
/// one at the register's width.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `r` - The register.
/// * `xlen` - The register width.
fn read_bits(i: &Insn, r: Reg, xlen: Xlen) -> Option<u8> {
    if !i.registers().reads.contains(&r) {
        return None;
    }
    let xbits = u8::try_from(xlen.bits()).ok();
    let (Reg::F(_), Op::Float(f)) = (r, i.op) else {
        return xbits;
    };
    let fmt = match f {
        FOp::Store { fmt, .. }
        | FOp::Arith { fmt, .. }
        | FOp::Sqrt { fmt, .. }
        | FOp::Fused { fmt, .. }
        | FOp::Cmp { fmt, .. }
        | FOp::Class { fmt, .. }
        | FOp::ToInt { fmt, .. }
        | FOp::MvToInt { fmt, .. }
        | FOp::Convert { from: fmt, .. } => fmt,
        FOp::Load { .. } | FOp::FromInt { .. } | FOp::MvFromInt { .. } => return xbits,
    };
    Some(match fmt {
        Fmt::S => 32,
        Fmt::D => 64,
    })
}

/// Tells whether an instruction may read or write registers its
/// [`Insn::registers`] does not name: an `ecall` reads any argument
/// register, and an operation the decoder leaves unknown names none.
///
/// # Arguments
///
/// * `i` - The instruction.
fn unmodeled(i: &Insn) -> bool {
    matches!(i.op, Op::Ecall | Op::System | Op::Unknown)
}

/// Returns what a call to `target` does with `r` as an argument.
///
/// The import a stub reaches reads `a0` when the library says it takes an
/// argument; whether it reads `fa0` the stub does not say, so that is
/// unknown. A function reads `r` when it does before writing it in its
/// first instructions, at that instruction's width.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `xlen` - The register width.
/// * `target` - The callee, when the call names one.
/// * `r` - The register: `a0` or `fa0`.
///
/// # Returns
///
/// [`Site::Used`] at the width read, [`Site::Dead`] when the callee writes
/// `r` first or takes no argument, [`Site::Unknown`] when the call names no
/// function or its first instructions, up to their first transfer, do not
/// say.
fn reads_first_argument(
    program: &Program,
    analysis: &Analysis,
    xlen: Xlen,
    target: Option<u64>,
    r: Reg,
) -> Site {
    let Some(f) = target
        .and_then(|t| analysis.function(t))
        .filter(|f| Some(f.entry) == target)
    else {
        return Site::Unknown;
    };
    if let Some(takes) = crate::analysis::typelib::stub_takes_arguments(program, f) {
        return match (r == A0, takes) {
            (true, true) => Site::Used(64),
            (true, false) => Site::Dead,
            (false, _) => Site::Unknown,
        };
    }
    let mut at = f.entry;
    for _ in 0..LEADING_MAX {
        let Some(i) = decode(program, at, xlen).filter(|i| !unmodeled(i)) else {
            return Site::Unknown;
        };
        if let Some(bits) = read_bits(&i, r, xlen) {
            return Site::Used(bits);
        }
        if i.registers().writes.contains(&r) {
            return Site::Dead;
        }
        if i.flow() != Flow::Next {
            return Site::Unknown;
        }
        at = i.next();
    }
    Site::Unknown
}

/// Classifies what the code after one call does with a result register.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `xlen` - The register width.
/// * `site` - The call's address.
/// * `from` - The calling function's entry, when known.
/// * `r` - The register: `a0`, `a1` or `fa0`.
fn classify(
    program: &Program,
    analysis: &Analysis,
    xlen: Xlen,
    (site, from): (u64, Option<u64>),
    r: Reg,
) -> Site {
    let caller = from.and_then(|e| analysis.function(e));
    let inside =
        |t: u64| caller.is_some_and(|f| f.blocks.iter().any(|b| b.start <= t && t < b.end));
    let Some(after) = decode(program, site, xlen).map(|i| i.next()) else {
        return Site::Unknown;
    };
    let passes = |t: Option<u64>| {
        if r == A1 {
            Site::Dead
        } else {
            reads_first_argument(program, analysis, xlen, t, r)
        }
    };
    let mut paths: Vec<(u64, usize)> = vec![(after, 0)];
    let mut found: Vec<Site> = Vec::new();
    let mut forks = 1usize;
    while let Some((mut at, mut n)) = paths.pop() {
        let mut prev: Option<Insn> = None;
        let outcome = loop {
            let Some(i) = decode(program, at, xlen).filter(|_| n < SCAN_MAX) else {
                break Site::Unknown;
            };
            n += 1;
            if let Some(bits) = read_bits(&i, r, xlen).filter(|_| i.flow() != Flow::Return) {
                break Site::Used(bits);
            }
            if unmodeled(&i) {
                break Site::Unknown;
            }
            let to = target(prev.as_ref(), &i, xlen);
            match i.flow() {
                Flow::Call => break passes(to),
                Flow::Return => break from.map_or(Site::Unknown, Site::Tail),
                Flow::Invalid => break Site::Dead,
                Flow::Jump => match to {
                    Some(t) if inside(t) => {
                        at = t;
                        prev = None;
                        continue;
                    }
                    Some(t) => break passes(Some(t)),
                    None => break Site::Unknown,
                },
                Flow::CondJump => match i.target() {
                    Some(t) if forks < PATHS_MAX => {
                        forks += 1;
                        paths.push((t, n));
                    }
                    Some(_) => found.push(Site::Unknown),
                    None => {}
                },
                Flow::Next => {}
            }
            if i.registers().writes.contains(&r) {
                break Site::Dead;
            }
            at = i.next();
            prev = Some(i);
        };
        found.push(outcome);
    }
    Site::merge(&found)
}

/// Tells whether every return of a function hands back a value one of its
/// own instructions put in `a0` ([`call_returns::hands_back_own`]).
///
/// # Arguments
///
/// * `program` - The image.
/// * `xlen` - The register width.
/// * `f` - The function.
fn hands_back_own(program: &Program, xlen: Xlen, f: &Function) -> bool {
    call_returns::hands_back_own(f, |b| {
        let mut insns = Vec::new();
        let mut at = b.start;
        while at < b.end {
            let i = decode(program, at, xlen)?;
            at = i.next();
            insns.push(i);
        }
        Some(
            insns
                .iter()
                .rev()
                .find_map(|i| {
                    if i.flow() == Flow::Call {
                        Some(Own::Call)
                    } else {
                        i.registers().writes.contains(&A0).then_some(Own::Written)
                    }
                })
                .unwrap_or(Own::Through),
        )
    })
}

/// Fills the return facts of every RISC-V function from its call sites
/// ([`call_returns::settle`]).
///
/// # Arguments
///
/// * `program` - The image the callers are decoded from.
/// * `analysis` - Functions and cross-references; the facts are written in
///   place.
/// * `xlen` - The register width.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis, xlen: Xlen) {
    let shared: &Analysis = analysis;
    let facts: Vec<Facts> = striped(&shared.functions, |f| {
        call_returns::facts(shared, f, [A0, FA0, A1], |va, from, r| {
            classify(program, shared, xlen, (va, from), r)
        })
    })
    .into_iter()
    .map(Option::unwrap_or_default)
    .collect();
    call_returns::settle(
        analysis,
        facts,
        |_| None,
        |f| hands_back_own(program, xlen, f),
    );
}
