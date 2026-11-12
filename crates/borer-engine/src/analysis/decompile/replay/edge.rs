//! The equality a branch hands the block it enters, checked at the branch.
//!
//! A block entered from one predecessor through an equality branch is
//! lifted, and replayed, with the compared variable fixed at the branch's
//! constant ([`Witness::assumes`](super::Witness::assumes)), in as many of
//! its low bits as the branch compared. That equality is a claim of the
//! text like any other: where the machine takes the branch into the block,
//! the variable holds the constant in those bits. Taken on faith it let a
//! block agree with the machine from a start no run reaches: a loop left
//! when its counter, counted down, reached zero, with the block after it
//! started from the 1 the loop's last test had compared; a block after a
//! compare of a register's low half, started with the upper half zero.
//!
//! The claim is made in every state a block is tried from, whenever the
//! machine goes on into such a successor ([`Function::successors`]). The
//! states seldom take an equality edge, so each block that starts under an
//! equality has its predecessor tried once more, from a state made to take
//! the edge ([`Function::borne`]): the variable holds the constant in the
//! bits the branch compares and anything above them. A block whose
//! equality no such run bears out is not checked at all ([`ASSUMED`]),
//! since every state it would be tried from rests on the equality. One
//! state tests the equality; it does not prove it.

use std::collections::BTreeSet;

use super::super::expr::{Flags, Key};
use super::super::lift::EffectKind;
use super::term::{self, Term};
use super::{Bench, Claim, End, Function, Replay, Replayed, Transfer, Trial, low, mix};
use crate::emulate::Stop;
use crate::fxmap::FxHashMap;
use crate::num::lo8;

/// What the row of an equality a run does not bear out shows as its
/// expression.
const GIVEN: &str = "the value the branch into the block gives it";

/// Why a block is not checked when no run into it bore out the equality
/// it starts under.
pub(super) const ASSUMED: &str = "an equality at its start no run into it bore out";

/// Tells whether a fact's variable is held in the state and not in memory:
/// a register, a parameter or a temporary.
///
/// # Arguments
///
/// * `k` - The variable.
pub(super) fn in_register(k: Key) -> bool {
    matches!(
        k,
        Key::Reg(_) | Key::A64(_) | Key::A32(_) | Key::Tmp(_) | Key::Param(_)
    )
}

/// The value a variable starts a block with under an equality of its low
/// bits: the constant in those bits, what it held above them.
///
/// # Arguments
///
/// * `v` - What the variable holds without the equality.
/// * `c` - The constant.
/// * `n` - How many low bits the equality fixes.
pub(super) fn under(v: u64, c: u64, n: u8) -> u64 {
    (v & !low(n)) | (c & low(n))
}

/// The term a variable starts a proof as under an equality of its low
/// bits: the constant, and above it, where the equality stops short of the
/// register width, a value no state fixes.
///
/// # Arguments
///
/// * `k` - The variable.
/// * `c` - The constant.
/// * `n` - How many low bits the equality fixes.
/// * `width` - The register width.
pub(super) fn start_term(k: Key, c: u64, n: u8, width: u8) -> Term {
    let known = Term::Const(c & low(n.min(width)));
    if n >= width {
        return known;
    }
    let above = term::mul(64, &Term::In(k, width - n), &Term::Const(1u64 << n));
    term::add(64, &known, &above)
}

impl<'p, L: Replay> Function<'_, 'p, L> {
    /// The bytes of memory an equality of a variable fixes where block `b`
    /// starts, each by its address and its index in the constant: those of
    /// a slot or a global, and none for a variable held in the state
    /// ([`in_register`]).
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `k` - The variable.
    /// * `sp0` - The stack pointer at the function's entry.
    pub(super) fn fact_bytes(&self, b: usize, k: Key, sp0: u64) -> Vec<(u64, u8)> {
        let (at, len) = match k {
            Key::Slot(o) => {
                let bits = self.w.ins.get(b).and_then(|e| e.slot_bits.get(&o));
                (
                    sp0.wrapping_add_signed(o),
                    bits.copied().unwrap_or(self.width) / 8,
                )
            }
            Key::Global(a, bits) => (a, (bits / 8).max(1)),
            Key::Reg(_) | Key::A64(_) | Key::A32(_) | Key::Rv(_) => (0, 0),
            Key::Tmp(_) | Key::Param(_) => (0, 0),
        };
        (0..len.min(8))
            .map(|i| (at.wrapping_add(u64::from(i)) & low(self.width), i))
            .collect()
    }

    /// The bytes of memory a trial of block `b` starts with fixed, each by
    /// its address: those of the equality the block starts under, and of
    /// an equality one of its successors starts under when the trial is
    /// forced to it ([`Function::borne`]).
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `forced` - Values variables start with in place of a draw.
    /// * `sp0` - The stack pointer at the function's entry.
    pub(super) fn planted(
        &self,
        b: usize,
        forced: &FxHashMap<Key, u64>,
        sp0: u64,
    ) -> Vec<(u64, u8)> {
        let fact = |s: usize| self.w.assumes.get(s).copied().flatten();
        let fed = self.succs.get(b).into_iter().flatten().filter_map(|&s| {
            let (k, ..) = fact(s)?;
            Some((k, *forced.get(&k)?))
        });
        fact(b)
            .map(|(k, c, _)| (k, c))
            .into_iter()
            .chain(fed)
            .flat_map(|(k, c)| {
                let bytes = self.fact_bytes(b, k, sp0).into_iter();
                bytes.map(move |(at, i)| (at, lo8(c >> (8 * i))))
            })
            .collect()
    }

    /// Whether the machine takes the branch ending a block, run one step
    /// from where the block stopped; `None` when the block ends in no
    /// branch or the step does not tell.
    ///
    /// # Arguments
    ///
    /// * `emu` - The machine, stopped before the branch.
    /// * `end` - How the block ends.
    pub(super) fn taken(emu: &L::Rig<'p>, end: End<L::Insn>) -> Option<bool> {
        match end.last().map(|jcc| (jcc, L::transfer(&jcc))) {
            Some((jcc, Transfer::Branch { target, next }))
                if matches!(end, End::Branch(_)) && target != next =>
            {
                let mut step = emu.clone();
                step.set_budget(1);
                step.stop_at(Some(target));
                match step.run(L::start(&jcc)).stop {
                    Stop::Stopped(_) => Some(true),
                    Stop::Budget => Some(false),
                    _ => None,
                }
            }
            Some(_) | None => None,
        }
    }

    /// Whether the machine, having taken or passed the branch ending a
    /// block, goes on into block `s`.
    ///
    /// # Arguments
    ///
    /// * `end` - How the block ends.
    /// * `taken` - Whether the machine takes its branch ([`Function::taken`]).
    /// * `s` - The successor's index.
    fn enters(&self, end: End<L::Insn>, taken: Option<bool>, s: usize) -> bool {
        let succ = self.code.get(s).and_then(|c| c.first()).map(L::start);
        let branch = end.last().map(|i| L::transfer(&i));
        branch.zip(taken).is_some_and(|(transfer, taken)| {
            matches!(
                transfer,
                Transfer::Branch { target, next }
                    if succ == Some(if taken { target } else { next })
            )
        })
    }

    /// The bits the branch ending block `p` compares, as its text states
    /// it: the width of the compare, the test or the result its flags are
    /// of, and the register width for any other condition.
    ///
    /// # Arguments
    ///
    /// * `p` - The block's index.
    fn compared(&self, p: usize) -> u8 {
        let last = self.effects.get(p).and_then(|es| es.last());
        let n = match last.map(|e| &e.kind) {
            Some(EffectKind::Branch(c)) => match &c.flags {
                Flags::Cmp(_, _, n)
                | Flags::Test(_, _, n)
                | Flags::Result(_, n)
                | Flags::Add(_, _, n) => *n,
                Flags::Float(..)
                | Flags::FCmp(..)
                | Flags::Carry(_)
                | Flags::Shift(..)
                | Flags::Truth(..)
                | Flags::Unknown => self.width,
            },
            Some(
                EffectKind::Assign(..)
                | EffectKind::Store(_)
                | EffectKind::Call(_)
                | EffectKind::Return(_)
                | EffectKind::Switch(_)
                | EffectKind::Jump(_)
                | EffectKind::Unmodeled,
            )
            | None => self.width,
        };
        n.min(self.width)
    }

    /// Tells whether the equality block `s` starts under is one a run into
    /// the block bears out, and records the run that does not.
    ///
    /// The block's one predecessor is tried from a state made to take the
    /// edge: the variable holds the constant in the bits the predecessor's
    /// branch compares ([`Function::compared`]) and a value of the trial's
    /// above them, so an equality that claims more bits than the branch
    /// compared is one this state refutes. Only the equality is kept of
    /// such a state ([`Function::successors`]); the predecessor's other
    /// claims are the ones its own states compare.
    ///
    /// # Arguments
    ///
    /// * `s` - The block's index.
    /// * `out` - Where a disagreement goes.
    ///
    /// # Returns
    ///
    /// `true` for a block that starts under no equality, and for one whose
    /// equality the machine was seen to enter the block under; `false`
    /// where the predecessor cannot be tried, the machine does not take
    /// the edge, the variable cannot be read there, or it holds another
    /// value.
    pub(super) fn borne(&self, s: usize, out: &mut Replayed) -> bool {
        let Some((k, c, _)) = self.w.assumes.get(s).copied().flatten() else {
            return true;
        };
        let blocks = self.analysis.function(self.entry).map(|f| &f.blocks);
        let Some(&[p]) = self.preds.get(s).map(Vec::as_slice) else {
            return false;
        };
        let (Some(block), Ok((code, sp))) = (blocks.and_then(|b| b.get(p)), self.admit(p)) else {
            return false;
        };
        let Ok(end) = End::of::<L>(code) else {
            return false;
        };
        let n = self.compared(p);
        let state = (mix(self.seed ^ block.start) & !low(n)) | (c & low(n));
        let forced: FxHashMap<Key, u64> = [(k, state)].into_iter().collect();
        let (mut own, mut found) = (BTreeSet::new(), Replayed::default());
        let ran = self.trial(
            p,
            block,
            code,
            sp,
            end,
            &[],
            0,
            &forced,
            &mut own,
            &mut found,
        );
        let entered = ran.is_ok_and(|(_, taken)| self.enters(end, taken, s));
        let mut held = entered && !found.unreadable.contains_key(&Claim::Branch);
        for d in found.disagreements.into_iter().filter(|d| d.expr == GIVEN) {
            held = false;
            if !told(out, &d.place) {
                out.disagreements.push(d);
            }
        }
        held
    }

    /// Checks the relation at each successor of a block
    /// ([`Function::successor`]) and, where the machine goes on into one
    /// that starts under an equality, the equality: the variable holds the
    /// constant there, in the bits the equality is of.
    ///
    /// The row of one that does not shows the constant as the text's side,
    /// since the text of the successor starts from it, and as the
    /// machine's what the run into the block leaves in the variable. A
    /// difference above bit 32 is this claim's too, and no lane's: the
    /// equality says what those bits hold.
    ///
    /// # Arguments
    ///
    /// * `t` - The state at the block's end.
    /// * `start` - The block's start.
    /// * `at` - The block's last instruction.
    /// * `end` - How the block ends.
    /// * `out` - Where the counts and disagreements go.
    pub(super) fn successors(
        &self,
        t: &mut Trial<'_, L::Rig<'p>>,
        start: u64,
        at: u64,
        end: End<L::Insn>,
        out: &mut Replayed,
    ) {
        let w = self.w;
        for &s in self.succs.get(t.b).map_or(&[][..], Vec::as_slice) {
            if !w.processed.get(s).copied().unwrap_or(false) {
                continue;
            }
            self.successor(t, start, at, s, out);
            let Some((k, c, n)) = w.assumes.get(s).copied().flatten() else {
                continue;
            };
            let succ = self.code.get(s).and_then(|c| c.first()).map_or(0, L::start);
            let name = self.regs.iter().find(|&&(_, r)| r == k);
            let place = name.map_or_else(|| format!("{k:?}"), |r| r.0.to_owned());
            let place = format!("{place} at {succ:#x}");
            if !self.enters(end, t.taken, s) || told(out, &place) {
                continue;
            }
            let (bits, now) = (n.min(self.width), t.text.var(k));
            self.compare(
                t,
                out,
                start,
                at,
                Claim::Branch,
                || place,
                now.map(|_| c & low(bits)),
                now.unwrap_or(0),
                bits,
                false,
                || GIVEN.to_owned(),
            );
            if let Some(d) = out.disagreements.last_mut().filter(|d| d.expr == GIVEN) {
                d.lane = false;
            }
        }
    }
}

/// Tells whether a replay already holds the row of an equality at a place.
///
/// # Arguments
///
/// * `out` - The replay.
/// * `place` - The variable and the block entered, as the row names them.
fn told(out: &Replayed, place: &str) -> bool {
    let given = |d: &&super::Disagreement| d.expr == GIVEN && d.place == place;
    out.disagreements.iter().any(|d| given(&d))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests;
