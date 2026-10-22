//! Whether any caller reads an ARM32 function's `r0` result after calling
//! it.
//!
//! The ARM32 counterpart of [`crate::analysis::returns`] and the arm64
//! pass. Each call site is scanned forward from the instruction after the
//! call, down both sides of every branch: a read of `r0` on any path means
//! the result is used; a write of it first means it is dead there. A later
//! call reads `r0` as its first argument when its callee does, which hands
//! the result on as `g(f())` does; otherwise the call clobbers it. A
//! return or a jump out of the caller hands the result on to the caller's
//! own callers, so it is used exactly when the caller's result is, run to
//! a fixpoint over chains of wrappers.
//!
//! The body speaks too ([`exits`]): a path to a return whose last write of
//! `r0` is a call to a function that returns nothing, or that meets the
//! `nop` unoptimized GCC code puts at a `void` function's closing brace,
//! just ahead of the epilogue, before any write, hands back nothing, which
//! makes the function return nothing when no caller reads its result,
//! whether or not anything calls it. Callers that all discard the result make it nothing too, unless
//! every return hands back a value an instruction of its own put in `r0`.

use crate::analysis::{Analysis, BlockTerm, Function, RefKind, striped};
use crate::isa::a32::{Flow, Insn, ItState, Op, Reg};
use crate::program::Program;

/// Longest run of instructions scanned along one path after a call.
const SCAN_MAX: usize = 16;
/// Most paths a call site's scan follows through the caller's branches.
const PATHS_MAX: usize = 8;
/// Longest prologue read for whether a callee reads its first argument.
const LEADING_MAX: usize = 16;
/// Most rounds of each fixpoint.
const PASS_ROUNDS_MAX: usize = 64;
/// Most blocks walked back from a function's returns.
const BLOCKS_MAX: usize = 256;
/// The T32 `nop` encoding.
const NOP_T16: u32 = 0xbf00;
/// The T32 `nop.w` encoding.
const NOP_T32: u32 = 0xf3af_8000;
/// The A32 `nop` encoding, always run.
const NOP_A32: u32 = 0xe320_f000;

/// What one call site does with `r0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Site {
    /// Read before being written.
    Used,
    /// Written or clobbered before any read.
    Dead,
    /// Handed on by the caller's return or a jump out: used exactly when
    /// the caller's result is (the caller's entry).
    Tail(u64),
    /// Lost: the scan ran out or could not follow a jump.
    Unknown,
}

/// The last instruction on a path to a return that says what `r0` holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Exit {
    /// A `nop`, met before any write of `r0`.
    Nop,
    /// A call, to the callee at this entry when it names one.
    Call(Option<u64>),
    /// One of the function's own instructions writes `r0`.
    Own,
}

/// What a function's returns hand back in `r0`.
#[derive(Debug, Clone, Default)]
struct Exits {
    /// Some path meets a `nop` before any write of `r0`, followed by the
    /// epilogue's unwinding of the frame or by another `nop`.
    idle: bool,
    /// Some path's last write of `r0` is the function's own instruction.
    own: bool,
    /// Some path reaches the entry without writing `r0`, handing back the
    /// first argument.
    argument: bool,
    /// The direct callees whose result some path hands back, by a call
    /// before a return or a jump into them.
    calls: Vec<u64>,
    /// Some path hands back what an indirect call left, or ran past
    /// [`BLOCKS_MAX`] blocks.
    unknown: bool,
}

/// Tells whether a call to `target` reads `r0` as an argument: the import
/// a stub reaches takes one, or the function reads `r0` before writing it
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
    let mut it = ItState::default();
    let mut at = f.entry;
    for _ in 0..LEADING_MAX {
        let Some(i) = super::decode(program, at, &mut it) else {
            return false;
        };
        let regs = i.registers();
        if regs.reads.contains(&Reg::R(0)) {
            return true;
        }
        if regs.writes.contains(&Reg::R(0)) || i.flow() != Flow::Next {
            return false;
        }
        at = i.next();
    }
    false
}

/// Classifies what the code after one call does with `r0`.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions.
/// * `site` - The call's address.
/// * `from` - The calling function's entry, when known.
fn classify(program: &Program, analysis: &Analysis, site: u64, from: Option<u64>) -> Site {
    let caller = from.and_then(|e| analysis.function(e));
    let inside =
        |t: u64| caller.is_some_and(|f| f.blocks.iter().any(|b| b.start <= t && t < b.end));
    let mut it = ItState::default();
    let Some(call) = super::decode(program, site, &mut it) else {
        return Site::Unknown;
    };
    let mut paths: Vec<(u64, usize)> = vec![(call.next(), 0)];
    let mut found: Vec<Site> = Vec::new();
    let mut forks = 1usize;
    while let Some((mut at, mut n)) = paths.pop() {
        let mut it = ItState::default();
        let outcome = loop {
            if n >= SCAN_MAX {
                break Site::Unknown;
            }
            let Some(i) = super::decode(program, at, &mut it) else {
                break Site::Unknown;
            };
            n += 1;
            let regs = i.registers();
            if regs.reads.contains(&Reg::R(0)) {
                break Site::Used;
            }
            match i.flow() {
                Flow::Call => {
                    let passes = matches!(i.op, Op::Bl { .. } | Op::Blx { .. })
                        && reads_first_argument(program, analysis, i.target());
                    break if passes { Site::Used } else { Site::Dead };
                }
                Flow::Return => break from.map_or(Site::Unknown, Site::Tail),
                Flow::Invalid => break Site::Dead,
                Flow::Jump => match i.target() {
                    Some(t) if inside(t) => {
                        at = t;
                        it = ItState::default();
                        continue;
                    }
                    Some(t) if reads_first_argument(program, analysis, Some(t)) => {
                        break Site::Used;
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
            if regs.writes.contains(&Reg::R(0)) {
                break Site::Dead;
            }
            at = i.next();
        };
        found.push(outcome);
    }
    if found.contains(&Site::Used) {
        Site::Used
    } else if found.contains(&Site::Unknown) {
        Site::Unknown
    } else {
        found
            .iter()
            .find(|s| matches!(s, Site::Tail(_)))
            .copied()
            .unwrap_or(Site::Dead)
    }
}

/// Reads what a function's returns hand back in `r0`, walking back from
/// each return and each jump out to the last write of `r0` on each path.
///
/// A one-instruction function is a stub that says nothing.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions, for the targets of jumps out.
/// * `f` - The function.
fn exits(program: &Program, analysis: &Analysis, f: &Function) -> Exits {
    let mut out = Exits::default();
    if f.instr_count <= 1 {
        out.unknown = true;
        return out;
    }
    let index: std::collections::BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(k, b)| (b.start, k))
        .collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); f.blocks.len()];
    let mut todo: Vec<usize> = Vec::new();
    for (k, b) in f.blocks.iter().enumerate() {
        for s in &b.successors {
            match index.get(s) {
                Some(&t) => preds[t].push(k),
                None if b.term == BlockTerm::Jmp && analysis.function(*s).is_some() => {
                    out.calls.push(*s);
                }
                None => out.unknown |= b.term == BlockTerm::Jmp,
            }
        }
        out.unknown |= b.term == BlockTerm::Indirect && b.successors.is_empty();
        if b.term == BlockTerm::Ret {
            todo.push(k);
        }
    }
    let mut seen = vec![false; f.blocks.len()];
    let mut walked = 0usize;
    while let Some(k) = todo.pop() {
        if std::mem::replace(&mut seen[k], true) {
            continue;
        }
        walked += 1;
        if walked > BLOCKS_MAX {
            out.unknown = true;
            break;
        }
        let b = &f.blocks[k];
        let mut insns: Vec<Insn> = Vec::new();
        let mut it = ItState::default();
        let mut at = b.start;
        while at < b.end {
            let Some(i) = super::decode(program, at, &mut it) else {
                break;
            };
            at = i.next();
            insns.push(i);
        }
        let last = insns
            .iter()
            .enumerate()
            .rev()
            .find_map(|(n, i)| match i.op {
                _ if closing_nop(i) => insns
                    .get(n + 1)
                    .is_some_and(|next| closing_nop(next) || unwinds(next))
                    .then_some(Exit::Nop),
                Op::Bl { .. } | Op::Blx { .. } | Op::BlxReg { .. } => Some(Exit::Call(i.target())),
                _ => (super::last_write(i) == Some(super::Last::Int)).then_some(Exit::Own),
            });
        match last {
            Some(Exit::Nop) => out.idle = true,
            Some(Exit::Call(Some(t))) => out.calls.push(t),
            Some(Exit::Call(None)) => out.unknown = true,
            Some(Exit::Own) => out.own = true,
            None if b.start == f.entry || preds[k].is_empty() => out.argument = true,
            None => todo.extend(preds[k].iter().copied()),
        }
    }
    out.calls.sort_unstable();
    out.calls.dedup();
    out
}

/// Tells whether an instruction is a `nop` in its plain encoding, not a
/// hint or a barrier.
///
/// # Arguments
///
/// * `i` - The instruction.
fn closing_nop(i: &Insn) -> bool {
    matches!((i.len, i.word), (2, NOP_T16) | (4, NOP_T32 | NOP_A32))
}

/// Tells whether an instruction unwinds a stack frame on the way out: it
/// writes the stack pointer or a frame pointer (`r7`, `r11`).
///
/// # Arguments
///
/// * `i` - The instruction.
fn unwinds(i: &Insn) -> bool {
    i.registers()
        .writes
        .iter()
        .any(|r| matches!(r, Reg::R(7 | 11 | 13)))
}

/// What one function's callers and body say about its result.
#[derive(Debug, Clone, Default)]
struct Facts {
    /// What each call or tail jump into the function does with `r0`.
    sites: Vec<Site>,
    /// What its returns hand back.
    exits: Exits,
}

/// Reads one function's call sites and returns.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - The functions and their references.
/// * `f` - The function.
fn facts(program: &Program, analysis: &Analysis, f: &Function) -> Facts {
    let sites = analysis
        .xrefs_to(f.entry)
        .iter()
        .filter_map(|s| match s.kind {
            RefKind::Call => Some(classify(program, analysis, s.va, s.from_entry)),
            RefKind::Jmp => match s.from_entry {
                Some(from) if from == f.entry => None,
                Some(from) => Some(Site::Tail(from)),
                None => Some(Site::Unknown),
            },
            RefKind::Data | RefKind::Index | RefKind::Table | RefKind::Ptr => None,
        })
        .collect();
    Facts {
        sites,
        exits: exits(program, analysis, f),
    }
}

/// Fills [`Function::returns_value`] of every ARM32 function from its
/// call sites and its returns.
///
/// # Arguments
///
/// * `program` - The image the code is decoded from.
/// * `analysis` - Functions and cross-references; the verdicts are
///   written in place.
pub(super) fn infer(program: &Program, analysis: &mut Analysis) {
    let shared: &Analysis = analysis;
    let facts: Vec<Facts> = striped(&shared.functions, |f| facts(program, shared, f))
        .into_iter()
        .map(Option::unwrap_or_default)
        .collect();
    let read: Vec<bool> = facts
        .iter()
        .map(|f| f.sites.contains(&Site::Used))
        .collect();
    let mut nothing: Vec<bool> = facts
        .iter()
        .zip(&read)
        .map(|(f, &read)| !read && f.exits.idle)
        .collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, f) in facts.iter().enumerate() {
            let void = |c: &u64| shared.entry_index.get(c).is_some_and(|&j| nothing[j]);
            if !nothing[i] && !read[i] && f.exits.calls.iter().any(void) {
                nothing[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut verdicts: Vec<Option<bool>> = facts
        .iter()
        .zip(&read)
        .zip(&nothing)
        .map(|((f, &read), &nothing)| {
            let e = &f.exits;
            let own = e.own && !e.argument && e.calls.is_empty() && !e.unknown;
            if read {
                Some(true)
            } else if nothing {
                Some(false)
            } else if f
                .sites
                .iter()
                .any(|s| matches!(s, Site::Dead | Site::Tail(_)))
            {
                (!own).then_some(false)
            } else {
                None
            }
        })
        .collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, f) in facts.iter().enumerate() {
            if verdicts[i] == Some(true) || nothing[i] {
                continue;
            }
            let handed_on = f.sites.iter().any(|site| match site {
                Site::Tail(caller) => shared
                    .entry_index
                    .get(caller)
                    .is_none_or(|&c| verdicts[c] != Some(false)),
                Site::Used | Site::Dead | Site::Unknown => false,
            });
            if handed_on {
                verdicts[i] = Some(true);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (f, verdict) in analysis.functions.iter_mut().zip(verdicts) {
        f.returns_value = verdict;
    }
}
