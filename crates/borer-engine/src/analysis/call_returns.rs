//! What callers do with a function's result registers, for the
//! instruction sets that read it off their call sites: arm64 and RISC-V.
//!
//! Each instruction set classifies its own call sites ([`Site`]) and the
//! writes before a function's returns ([`Own`]); the verdicts are settled
//! here the same way for both. A read of the result register after any
//! call means the function returns a value; callers that all discard it
//! mean it returns nothing, unless every return hands back a value the
//! function itself put there ([`hands_back_own`]). A site that hands the
//! result on through its caller's return counts as the caller's verdict,
//! run to a fixpoint so a chain of wrappers settles from its far end.

use crate::analysis::{Analysis, BasicBlock, BlockTerm, Function, RefKind};

/// Most rounds of the hand-on rule.
const PASS_ROUNDS_MAX: usize = 64;
/// Most blocks walked back from a function's returns for the writes of
/// the result register they hand back.
const OWN_BLOCKS_MAX: usize = 32;
/// The widest a result is recorded as narrow at ([`Function::ret_width`]).
const NARROW_MAX: u8 = 16;

/// What one call site does with a result register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Site {
    /// Read before being written, at this width in bits.
    Used(u8),
    /// Written or clobbered before any read.
    Dead,
    /// Handed on by the caller's own return or tail jump: used exactly
    /// when the caller's result is (the caller's entry).
    Tail(u64),
    /// Lost: the scan ran out or could not follow a jump.
    Unknown,
}

impl Site {
    /// Returns what a call site does over all the paths scanned from it:
    /// the widest read, else unknown when any path was lost, else the first
    /// hand-on, else dead.
    ///
    /// # Arguments
    ///
    /// * `found` - What each path met first.
    pub(crate) fn merge(found: &[Self]) -> Self {
        let used = found
            .iter()
            .filter_map(|s| match s {
                Self::Used(bits) => Some(*bits),
                Self::Dead | Self::Tail(_) | Self::Unknown => None,
            })
            .max();
        match used {
            Some(bits) => Self::Used(bits),
            None if found.contains(&Self::Unknown) => Self::Unknown,
            None => found
                .iter()
                .find(|s| matches!(s, Self::Tail(_)))
                .copied()
                .unwrap_or(Self::Dead),
        }
    }
}

/// What the call sites of one function say about its results.
#[derive(Debug, Clone, Default)]
pub(crate) struct Facts {
    /// What each call or tail jump into the function does with the integer
    /// result register.
    pub(crate) sites: Vec<Site>,
    /// The widest read of the float result register at a call site, when
    /// one reads it.
    pub(crate) float: Option<u8>,
    /// Some caller reads the second integer result register before writing
    /// it after the call.
    pub(crate) second: bool,
}

/// Reads what one function's callers do with its results.
///
/// # Arguments
///
/// * `analysis` - The functions and their references.
/// * `f` - The function.
/// * `regs` - The integer result register, the float one and the second
///   integer one.
/// * `classify` - What the code after a call (its address and the calling
///   function's entry) does with a register.
pub(crate) fn facts<R: Copy>(
    analysis: &Analysis,
    f: &Function,
    [int, float, second]: [R; 3],
    classify: impl Fn(u64, Option<u64>, R) -> Site,
) -> Facts {
    let mut out = Facts::default();
    for s in analysis.xrefs_to(f.entry) {
        match s.kind {
            RefKind::Call => {
                out.sites.push(classify(s.va, s.from_entry, int));
                if let Site::Used(bits) = classify(s.va, s.from_entry, float) {
                    out.float = Some(out.float.map_or(bits, |b| b.max(bits)));
                }
                out.second |= matches!(classify(s.va, s.from_entry, second), Site::Used(_));
            }
            RefKind::Jmp => match s.from_entry {
                Some(from) if from == f.entry => {}
                Some(from) => out.sites.push(Site::Tail(from)),
                None => out.sites.push(Site::Unknown),
            },
            RefKind::Data | RefKind::Index | RefKind::Table | RefKind::Ptr => {}
        }
    }
    out
}

/// What a block's instructions, read back from its end, do last with the
/// integer result register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Own {
    /// A call comes first, whose result is the callee's.
    Call,
    /// An instruction of the block writes it.
    Written,
    /// Nothing in the block touches it.
    Through,
}

/// Returns each block's predecessors within the function, by block index.
///
/// # Arguments
///
/// * `f` - The function.
pub(crate) fn preds(f: &Function) -> Vec<Vec<usize>> {
    let index: std::collections::BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(k, b)| (b.start, k))
        .collect();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); f.blocks.len()];
    for (k, b) in f.blocks.iter().enumerate() {
        for s in &b.successors {
            if let Some(p) = index.get(s).and_then(|&t| preds.get_mut(t)) {
                p.push(k);
            }
        }
    }
    preds
}

/// Tells whether every return of a function hands back a value one of its
/// own instructions put in the result register.
///
/// Walking back from each return, every path must meet a write of the
/// register before it meets a call (whose result is a callee's) or the
/// entry (where the register is the first argument).
///
/// # Arguments
///
/// * `f` - The function.
/// * `block` - What a block does last with the register ([`Own`]); `None`
///   when it does not decode.
///
/// # Returns
///
/// `false` as well when the function has no return or the walk runs past
/// [`OWN_BLOCKS_MAX`] blocks.
pub(crate) fn hands_back_own(f: &Function, block: impl Fn(&BasicBlock) -> Option<Own>) -> bool {
    let preds = preds(f);
    let mut todo: Vec<usize> = f
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| b.term == BlockTerm::Ret)
        .map(|(k, _)| k)
        .collect();
    if todo.is_empty() {
        return false;
    }
    let mut seen = vec![false; f.blocks.len()];
    let mut walked = 0usize;
    while let Some(k) = todo.pop() {
        if seen.get_mut(k).is_none_or(|s| std::mem::replace(s, true)) {
            continue;
        }
        walked += 1;
        let Some(b) = f.blocks.get(k).filter(|_| walked <= OWN_BLOCKS_MAX) else {
            return false;
        };
        match block(b) {
            None | Some(Own::Call) => return false,
            Some(Own::Written) => continue,
            Some(Own::Through) => {}
        }
        let from = preds.get(k).map_or(&[][..], Vec::as_slice);
        if b.start == f.entry || from.is_empty() {
            return false;
        }
        todo.extend_from_slice(from);
    }
    true
}

/// Settles every function's return facts from its call sites.
///
/// It writes [`Function::returns_value`], [`Function::ret_width`],
/// [`Function::ret_float`] and [`Function::hands_back_rdx`] (here the
/// second integer result register).
///
/// # Arguments
///
/// * `analysis` - The functions, written in place.
/// * `facts` - Each function's call-site facts, in function order.
/// * `left` - The float a function nothing calls leaves, read off its body.
/// * `own` - Whether a function hands back a value of its own
///   ([`hands_back_own`]).
pub(crate) fn settle(
    analysis: &mut Analysis,
    facts: Vec<Facts>,
    left: impl Fn(&Function) -> Option<u8>,
    own: impl Fn(&Function) -> bool,
) {
    let float: Vec<Option<u8>> = facts
        .iter()
        .zip(&analysis.functions)
        .map(|(f, func)| {
            if f.sites.is_empty() {
                return left(func);
            }
            let int_read = f.sites.iter().any(|s| matches!(s, Site::Used(_)));
            f.float
                .filter(|_| !int_read)
                .map(|bits| if bits <= 32 { 32 } else { 64 })
        })
        .collect();
    let mut verdicts: Vec<Option<bool>> = facts
        .iter()
        .zip(&float)
        .zip(&analysis.functions)
        .map(|((f, float), func)| {
            if float.is_some() || f.sites.iter().any(|s| matches!(s, Site::Used(_))) {
                Some(true)
            } else if f
                .sites
                .iter()
                .any(|s| matches!(s, Site::Dead | Site::Tail(_)))
            {
                (!own(func)).then_some(false)
            } else {
                None
            }
        })
        .collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, f) in facts.iter().enumerate() {
            if verdicts.get(i) == Some(&Some(true)) {
                continue;
            }
            let handed_on = f.sites.iter().any(|site| match site {
                Site::Tail(caller) => analysis.entry_index.get(caller).is_none_or(|&c| {
                    verdicts.get(c) != Some(&Some(false))
                        && float.get(c).is_none_or(Option::is_none)
                }),
                Site::Used(_) | Site::Dead | Site::Unknown => false,
            });
            if handed_on && let Some(v) = verdicts.get_mut(i) {
                *v = Some(true);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (((f, verdict), facts), float) in analysis
        .functions
        .iter_mut()
        .zip(verdicts)
        .zip(facts)
        .zip(float)
    {
        f.returns_value = verdict;
        f.ret_width = facts
            .sites
            .iter()
            .filter_map(|s| match s {
                Site::Used(bits) => Some(*bits),
                Site::Unknown => Some(64),
                Site::Dead | Site::Tail(_) => None,
            })
            .max()
            .filter(|w| *w <= NARROW_MAX);
        f.ret_float = float;
        f.hands_back_rdx = facts.second;
    }
}
