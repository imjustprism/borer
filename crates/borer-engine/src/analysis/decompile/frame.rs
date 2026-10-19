//! The frame as objects with solved types.
//!
//! A slot's declaration used to be the type of the first access the
//! emission pass met, so an `-O0` float whose slot starts as `str wzr,
//! [sp, #0xc]` (the integer zero) was declared `uint32_t`, and every later
//! `local_c = x * y` converted the float's value into an integer. Here each
//! access the dataflow pass makes is a vote ([`Frame::note`]), and the votes
//! are solved once ([`Frame::solve`]) before the text is written: a slot
//! every access reads or writes at one width, with at least one float
//! access, no integer read and no integer store but of a constant, holds a
//! float. A constant stored there is the float with its bits
//! ([`Frame::store`]), never the integer converted. A slot whose
//! votes conflict, or that shares bytes with another, keeps the type of
//! its first access, as before: a conflict never picks a side.

use std::collections::{BTreeMap, BTreeSet};

use super::expr::{Expr, Ty};

/// How one access uses a slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Access {
    /// A load at this type.
    Load(Ty),
    /// A store of a float value, or at a float type.
    StoreFloat(Ty),
    /// A store of an integer constant at this type.
    StoreConst(Ty),
    /// A store of any other value at this type.
    StoreInt(Ty),
}

impl Access {
    /// Returns the access's width in bits.
    fn bits(self) -> u8 {
        match self {
            Self::Load(t) | Self::StoreFloat(t) | Self::StoreConst(t) | Self::StoreInt(t) => {
                t.bits()
            }
        }
    }
}

/// The votes one slot gathered.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Votes {
    /// Every width in bits an access used.
    widths: BTreeSet<u8>,
    /// Some access read or wrote a float.
    float: bool,
    /// Some access read an integer, or stored one that is no constant.
    int: bool,
}

/// The frame's slots, their votes and, once solved, their types.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct Frame {
    /// The votes, by slot offset.
    votes: BTreeMap<i64, Votes>,
    /// The solved float slots and their types, once [`Frame::solve`] ran.
    solved: Option<BTreeMap<i64, Ty>>,
}

impl Frame {
    /// Records one access, until the frame is solved.
    ///
    /// # Arguments
    ///
    /// * `k` - The slot's offset.
    /// * `access` - What the access does.
    pub(super) fn note(&mut self, k: i64, access: Access) {
        if self.solved.is_some() {
            return;
        }
        let v = self.votes.entry(k).or_default();
        v.widths.insert(access.bits());
        match access {
            Access::Load(Ty::F32 | Ty::F64) | Access::StoreFloat(_) => v.float = true,
            Access::Load(_) | Access::StoreInt(_) => v.int = true,
            Access::StoreConst(_) => {}
        }
    }

    /// Solves the slots' types from the votes recorded so far, and stops
    /// recording.
    pub(super) fn solve(&mut self) {
        let spans: Vec<(i64, i64)> = self
            .votes
            .iter()
            .map(|(k, v)| {
                let len = v.widths.last().map_or(1, |b| i64::from(b / 8).max(1));
                (*k, k.saturating_add(len))
            })
            .collect();
        let alone = |k: i64, end: i64| spans.iter().all(|&(o, e)| o == k || e <= k || end <= o);
        let solved = self
            .votes
            .iter()
            .zip(&spans)
            .filter_map(|((k, v), &(_, end))| {
                let ty = match v.widths.iter().collect::<Vec<_>>().as_slice() {
                    [32] => Ty::F32,
                    [64] => Ty::F64,
                    _ => return None,
                };
                (v.float && !v.int && alone(*k, end)).then_some((*k, ty))
            })
            .collect();
        self.solved = Some(solved);
    }

    /// Returns the solved type of a slot.
    ///
    /// # Arguments
    ///
    /// * `k` - The slot's offset.
    ///
    /// # Returns
    ///
    /// The float type the slot holds, or `None` when it holds no float or
    /// the frame is not solved yet.
    pub(super) fn ty(&self, k: i64) -> Option<Ty> {
        self.solved.as_ref()?.get(&k).copied()
    }

    /// Returns a store as the slot's solved type spells it: an integer
    /// constant stored to a float slot is the float with those bits. Zero
    /// is the same number either way and stays as it is.
    ///
    /// # Arguments
    ///
    /// * `k` - The slot's offset.
    /// * `ty` - The store's type.
    /// * `v` - The stored value.
    ///
    /// # Returns
    ///
    /// The type and value to store.
    pub(super) fn store(&self, k: i64, ty: Ty, v: Expr) -> (Ty, Expr) {
        match (self.ty(k), v) {
            (Some(f), Expr::Const(bits)) if bits != 0 && f.bits() == ty.bits() => {
                (f, Expr::FConst(bits, f))
            }
            (_, v) => (ty, v),
        }
    }
}
