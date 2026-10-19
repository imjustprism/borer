//! The guarded regions of the function being decompiled, laid over its
//! blocks: which blocks each `try` protects, which code each handler
//! runs, and where the lift starts that code.
//!
//! The code a handler runs inside the function (an Itanium landing pad, an
//! `__except` body, the continuation a catch returns to) is reached by no
//! edge: only the runtime enters it. The plan names those entries as roots
//! for the lift, which starts each from the frame of the blocks the
//! region protects, and as roots for the structurer, which writes their
//! code after the body; [`cir::wrap`] then moves it into the handlers.

use std::collections::{BTreeMap, BTreeSet};

use super::cir;
use crate::analysis::guards::{ClauseKind, Dialect};
use crate::analysis::{Analysis, Function, Overlay, name_of};
use crate::isa::x86::{Decoder, DecoderOptions, FlowControl, Mnemonic, OpKind, Register};
use crate::program::Program;

/// Most blocks an Itanium landing pad's selector tests are followed
/// through.
const DISPATCH_MAX: usize = 16;

/// The guarded regions of one function, in its blocks.
#[derive(Debug, Default)]
pub(super) struct Plan {
    /// Each handler entry's block and the protected blocks whose frame it
    /// starts from.
    pub(super) roots: Vec<(usize, Vec<usize>)>,
    /// The regions to wrap once the body is structured.
    pub(super) regions: Vec<cir::Region>,
}

impl Plan {
    /// Lists the blocks the plan adds as roots.
    ///
    /// # Returns
    ///
    /// Each root's block index.
    pub(super) fn root_blocks(&self) -> impl Iterator<Item = usize> + '_ {
        self.roots.iter().map(|r| r.0)
    }
}

/// Lays a function's guarded regions over its blocks.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names, for the funclets.
/// * `f` - The function.
/// * `succs` - Successor block indices per block.
/// * `entry` - The entry block's index.
///
/// # Returns
///
/// The plan; empty when nothing in the function is guarded.
pub(super) fn plan(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    f: &Function,
    succs: &[Vec<usize>],
    entry: usize,
) -> Plan {
    let guards = crate::analysis::guards::of(program, analysis, f);
    if guards.is_empty() {
        return Plan::default();
    }
    let index: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let main = reach(succs, &[entry]);
    let mut out = Plan::default();
    let x86 = match program.arch.isa() {
        Some(crate::isa::Isa::X86 { bits }) => Some(bits),
        Some(crate::isa::Isa::A64) | None => None,
    };
    for g in &guards {
        let pad = g
            .clauses
            .first()
            .filter(|c| c.selector.is_some())
            .and_then(|c| c.resume);
        let (entries, dropped_from): (Vec<Option<usize>>, Option<usize>) = match pad {
            Some(pad) => {
                let at = index.get(&pad).copied();
                let found = at
                    .zip(x86)
                    .and_then(|(i, bits)| dispatch(program, f, i, &index, bits));
                let entries: Vec<Option<usize>> = g
                    .clauses
                    .iter()
                    .map(|c| match &found {
                        Some(map) if !map.is_empty() => {
                            c.selector.and_then(|s| map.get(&s).copied())
                        }
                        Some(_) | None => at.filter(|_| g.clauses.len() == 1),
                    })
                    .collect();
                if entries.iter().all(Option::is_some) {
                    (entries, at)
                } else {
                    (vec![None; g.clauses.len()], None)
                }
            }
            None => (
                g.clauses
                    .iter()
                    .map(|c| c.resume.and_then(|r| index.get(&r).copied()))
                    .collect(),
                None,
            ),
        };
        let owned: Vec<BTreeSet<usize>> = entries
            .iter()
            .map(|e| {
                e.map_or_else(BTreeSet::new, |e| {
                    reach(succs, &[e])
                        .into_iter()
                        .filter(|b| !main.contains(b))
                        .collect()
                })
            })
            .collect();
        let handled: BTreeSet<usize> = owned.iter().flatten().copied().collect();
        let dropped: BTreeSet<usize> = dropped_from.map_or_else(BTreeSet::new, |p| {
            reach(succs, &[p])
                .into_iter()
                .filter(|b| !main.contains(b) && !handled.contains(b))
                .collect()
        });
        let first = f.blocks.iter().position(|b| g.covers(b.start, b.end));
        let resumed: Vec<usize> = entries.iter().flatten().copied().collect();
        let after = reach_avoiding(succs, &resumed, first);
        let protected: Vec<usize> = f
            .blocks
            .iter()
            .enumerate()
            .filter(|(i, b)| {
                g.covers(b.start, b.end)
                    && !handled.contains(i)
                    && !dropped.contains(i)
                    && !after.contains(i)
            })
            .map(|(i, _)| i)
            .collect();
        if protected.is_empty() {
            continue;
        }
        let feeders: Vec<usize> = protected
            .iter()
            .copied()
            .filter(|b| main.contains(b))
            .collect();
        let starts = |set: &mut dyn Iterator<Item = usize>| -> BTreeSet<u64> {
            set.filter_map(|i| f.blocks.get(i).map(|b| b.start))
                .collect()
        };
        let mut rooted: BTreeSet<usize> = BTreeSet::new();
        rooted.extend(dropped_from);
        if dropped_from.is_none() {
            rooted.extend(entries.iter().flatten().copied());
        }
        for r in rooted.into_iter().filter(|r| !main.contains(r)) {
            out.roots.push((r, feeders.clone()));
        }
        out.regions.push(cir::Region {
            seh: g.dialect == Dialect::Seh,
            protected: starts(&mut protected.iter().copied()),
            handlers: g
                .clauses
                .iter()
                .zip(&entries)
                .zip(&owned)
                .map(|((c, e), owned)| cir::RegionHandler {
                    head: head(analysis, overlay, &c.kind),
                    note: note(analysis, overlay, c, pad.filter(|_| e.is_none())),
                    entry: e
                        .filter(|_| !owned.is_empty())
                        .and_then(|i| f.blocks.get(i))
                        .map(|b| b.start),
                    owned: starts(&mut owned.iter().copied()),
                })
                .collect(),
            dropped: starts(&mut dropped.iter().copied()),
            ranges: g.ranges.clone(),
        });
    }
    out
}

/// Spells what a clause handles as a handler's head.
///
/// # Arguments
///
/// * `analysis` - Discovery results, for the filter's name.
/// * `overlay` - User names.
/// * `kind` - The clause.
///
/// # Returns
///
/// The head: a `catch` declaration, an `__except` filter or `__finally`.
fn head(analysis: &Analysis, overlay: &Overlay, kind: &ClauseKind) -> cir::Head {
    let expr = |kind| cir::Expr {
        kind,
        ty: None,
        prov: cir::Prov::ENTRY,
    };
    match kind {
        ClauseKind::Catch(decl) => cir::Head::Catch(decl.clone()),
        ClauseKind::Except(None) => cir::Head::Except(expr(cir::ExprKind::Name(cir::Name::of(
            "EXCEPTION_EXECUTE_HANDLER",
        )))),
        ClauseKind::Except(Some(filter)) => cir::Head::Except(expr(cir::ExprKind::Call(
            Box::new(expr(cir::ExprKind::Name(cir::Name::of(&name_of(
                analysis, overlay, *filter,
            ))))),
            Vec::new(),
        ))),
        ClauseKind::Finally => cir::Head::Finally,
    }
}

/// Writes the comment a handler's body opens with: the funclet the runtime
/// calls for it, or the landing pad whose selector tests were not read.
///
/// # Arguments
///
/// * `analysis` - Discovery results, for the funclet's name.
/// * `overlay` - User names.
/// * `c` - The clause.
/// * `pad` - The landing pad, when its code is not split per clause.
///
/// # Returns
///
/// The comment's text, or `None` when the clause's code is all inline.
fn note(
    analysis: &Analysis,
    overlay: &Overlay,
    c: &crate::analysis::guards::Clause,
    pad: Option<u64>,
) -> Option<String> {
    if let Some(funclet) = c.funclet {
        return Some(format!(
            "runs {} @ {funclet:#x}",
            name_of(analysis, overlay, funclet)
        ));
    }
    let pad = pad?;
    Some(match c.selector {
        Some(s) => format!("landing pad {pad:#x}, selector {s}"),
        None => format!("landing pad {pad:#x}"),
    })
}

/// Lists the blocks reachable from some roots.
///
/// # Arguments
///
/// * `succs` - Successor block indices per block.
/// * `roots` - Where to start.
///
/// # Returns
///
/// The roots and every block reachable from them.
fn reach(succs: &[Vec<usize>], roots: &[usize]) -> BTreeSet<usize> {
    let mut seen = BTreeSet::new();
    let mut work: Vec<usize> = roots.to_vec();
    while let Some(b) = work.pop() {
        if b < succs.len() && seen.insert(b) {
            work.extend(succs[b].iter().copied());
        }
    }
    seen
}

/// Lists the blocks a handler's code goes on to without entering the
/// guarded region again: the code after the `try`.
///
/// A handler ends where its `try` statement ends, so whatever its code
/// reaches lies after the region, even where the metadata's ranges run on
/// (a `FuncInfo4` state holds to the function's end). A path that comes
/// back through the region's first block is a loop around the `try` and
/// is not followed in.
///
/// # Arguments
///
/// * `succs` - Successor block indices per block.
/// * `roots` - The handler entries.
/// * `first` - The region's first block, never entered.
///
/// # Returns
///
/// The blocks reached, the entries included.
fn reach_avoiding(succs: &[Vec<usize>], roots: &[usize], first: Option<usize>) -> BTreeSet<usize> {
    let mut seen = BTreeSet::new();
    let mut work: Vec<usize> = roots.to_vec();
    while let Some(b) = work.pop() {
        if Some(b) != first && b < succs.len() && seen.insert(b) {
            work.extend(succs[b].iter().copied());
        }
    }
    seen
}

/// Follows an x86 Itanium landing pad's selector tests to the block each
/// clause begins at.
///
/// The pad receives the selector in `edx`: the type filter of the clause
/// that matched. The compiler tests it against each filter in turn, `cmp
/// edx, k` then `je` or `jne`, a copy of it in another register counting
/// as it; the equal side of each test is that clause's code, the other
/// side the next test, and the last other side the resume.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The function.
/// * `pad` - The landing pad's block index.
/// * `index` - Block index by start address.
/// * `bits` - Decoder bitness.
///
/// # Returns
///
/// Each filter's clause block; empty when the pad tests nothing (its one
/// clause begins at the pad itself). `None` when a block's bytes do not
/// decode.
fn dispatch(
    program: &Program,
    f: &Function,
    pad: usize,
    index: &BTreeMap<u64, usize>,
    bits: u32,
) -> Option<BTreeMap<i64, usize>> {
    let mut out = BTreeMap::new();
    let mut selector: BTreeSet<Register> = BTreeSet::from([Register::RDX]);
    let mut at = pad;
    for _ in 0..DISPATCH_MAX {
        let b = f.blocks.get(at)?;
        let bytes = program.read_va(b.start, usize::try_from(b.end - b.start).ok()?)?;
        let code: Vec<_> = Decoder::with_ip(bits, bytes, b.start, DecoderOptions::NONE)
            .into_iter()
            .collect();
        for i in &code {
            if i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && i.op1_kind() == OpKind::Register
            {
                let (to, from) = (
                    i.op0_register().full_register(),
                    i.op1_register().full_register(),
                );
                if selector.contains(&from) {
                    selector.insert(to);
                } else {
                    selector.remove(&to);
                }
            }
        }
        let [.., cmp, jump] = code.as_slice() else {
            break;
        };
        let equal_on_jump = match jump.mnemonic() {
            Mnemonic::Je => true,
            Mnemonic::Jne => false,
            _ => break,
        };
        if cmp.mnemonic() != Mnemonic::Cmp
            || cmp.op0_kind() != OpKind::Register
            || !selector.contains(&cmp.op0_register().full_register())
            || !matches!(
                cmp.op1_kind(),
                OpKind::Immediate8 | OpKind::Immediate8to32 | OpKind::Immediate32
            )
            || jump.flow_control() != FlowControl::ConditionalBranch
        {
            break;
        }
        let k = i64::from(cmp.immediate32().cast_signed());
        let target = index.get(&jump.near_branch_target()).copied()?;
        let fall = index.get(&b.end).copied()?;
        let (equal, other) = if equal_on_jump {
            (target, fall)
        } else {
            (fall, target)
        };
        out.insert(k, equal);
        at = other;
    }
    Some(out)
}
