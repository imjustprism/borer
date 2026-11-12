//! The equality a branch hands the block it enters, checked at the branch.
//!
//! A block entered from one predecessor through an equality branch is
//! lifted, and replayed, with the compared variable fixed at the branch's
//! constant ([`Witness::assumes`](super::Witness::assumes)). That equality
//! is a claim of the text like any other: where the machine takes the
//! branch into the block, the register the block reads by that variable's
//! name holds the constant. Taken on faith it let a block agree with the
//! machine from a start no run reaches: a loop left when its counter,
//! counted down, reached zero, with the block after it started from the 1
//! the loop's last test had compared.
//!
//! The states a block is tried from seldom take such an edge, so each is
//! taken once on purpose: the predecessor is tried from a state whose
//! variable holds the constant, and where the machine then goes into the
//! block, its register is compared with the constant the block is started
//! from. One state tests the equality; it does not prove it, and a block
//! proved over every state is proved of its other claims.

use std::collections::BTreeSet;

use super::super::expr::Key;
use super::{Bench, Claim, End, Function, Replay, Replayed, Transfer, Trial, low};
use crate::analysis::BasicBlock;
use crate::fxmap::FxHashMap;

/// What the row of an equality the machine does not bear out shows as its
/// expression.
const GIVEN: &str = "the value the branch into the block gives it";

impl<'p, L: Replay> Function<'_, 'p, L> {
    /// The equality a block starts under, where it is one the machine can
    /// bear out: of a general register read from the block's start on by
    /// its own name.
    ///
    /// A variable the block's IN environment holds a pending value for, a
    /// parameter or a temporary is not assigned on the way in, so its
    /// equality is the branch's own and there is nothing to compare. A
    /// register nothing reads from there on, in the block or after it,
    /// holds whatever the machine left there, and the equality is of the
    /// variable alone (`mov ecx, eax; mov eax, [ecx+8]; test ecx, ecx`
    /// tests the variable `eax` named before the load). A block that only
    /// jumps on to the one reading the register is given the equality and
    /// checked like any other; the block behind the jump is given none,
    /// since the lift reads an equality only from the branch ending a
    /// block's one predecessor.
    ///
    /// # Arguments
    ///
    /// * `s` - The block's index.
    ///
    /// # Returns
    ///
    /// The register as the machine names it, its variable, the constant,
    /// and the bits compared: as many as the block reads of the register.
    fn given(&self, s: usize) -> Option<(&'static str, Key, u64, u8)> {
        let (k, c) = self.w.assumes.get(s).copied().flatten()?;
        let name = self.regs.iter().find(|&&(_, r)| r == k)?.0;
        let bits = *self.w.live.regs.get(s)?.get(&k)?;
        let pending = self.w.ins.get(s)?.vals.contains_key(&k);
        (!pending).then_some((name, k, c, bits.min(self.width)))
    }

    /// Tries a block from the state that takes each edge a successor reads
    /// an equality from, and records where the machine does not bear the
    /// equality out.
    ///
    /// Only that claim is kept of such a state: the block's other claims
    /// are the ones its own states compare.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `block` - The block.
    /// * `code` - Its instructions.
    /// * `sp` - The stack pointer at its start, from the function's entry.
    /// * `end` - How it ends.
    /// * `seen` - The block's disagreements so far, by claim and place.
    /// * `out` - Where the disagreements go.
    #[expect(
        clippy::too_many_arguments,
        reason = "one block's facts, threaded through"
    )]
    pub(super) fn edges(
        &self,
        b: usize,
        block: &BasicBlock,
        code: &[L::Insn],
        sp: i64,
        end: End<L::Insn>,
        seen: &mut BTreeSet<(Claim, String)>,
        out: &mut Replayed,
    ) {
        for &s in self.succs.get(b).map_or(&[][..], Vec::as_slice) {
            let Some((_, k, c, _)) = self.given(s) else {
                continue;
            };
            let forced: FxHashMap<Key, u64> = [(k, c)].into_iter().collect();
            let (mut own, mut found) = (BTreeSet::new(), Replayed::default());
            let tried = self.trial(
                b,
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
            if tried.is_err() {
                continue;
            }
            for d in found.disagreements {
                if d.expr == GIVEN && seen.insert((d.claim, d.place.clone())) {
                    out.disagreements.push(d);
                }
            }
        }
    }

    /// Checks the relation at each successor of a block
    /// ([`Function::successor`]) and, from a state chosen to take the edge
    /// into one ([`Function::edges`]), the equality that successor starts
    /// under ([`Function::given`]): where the machine goes there, its
    /// register holds the constant.
    ///
    /// The row of one that does not shows the constant as the text's side,
    /// since the text of the successor starts from it, and the register as
    /// the machine's.
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
        let branch = end.last().map(|i| L::transfer(&i));
        for &s in self.succs.get(t.b).map_or(&[][..], Vec::as_slice) {
            if !w.processed.get(s).copied().unwrap_or(false) {
                continue;
            }
            self.successor(t, start, at, s, out);
            let Some((name, k, c, bits)) = self.given(s) else {
                continue;
            };
            let succ = self.code.get(s).and_then(|c| c.first()).map(L::start);
            let entered = branch.zip(t.taken).is_some_and(|(transfer, taken)| {
                matches!(
                    transfer,
                    Transfer::Branch { target, next }
                        if succ == Some(if taken { target } else { next })
                )
            });
            let Some(machine) = t.emu.register(name) else {
                continue;
            };
            if entered && t.text.forced.get(&k) == Some(&c) {
                self.compare(
                    t,
                    out,
                    start,
                    at,
                    Claim::Branch,
                    || format!("{name} at {:#x}", succ.unwrap_or(0)),
                    Some(c & low(bits)),
                    machine,
                    bits,
                    false,
                    || GIVEN.to_owned(),
                );
            }
        }
    }
}
