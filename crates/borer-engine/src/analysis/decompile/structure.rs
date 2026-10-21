//! Structuring: guards, regions, gotos and switches recovered from the block
//! graph.

use super::*;
use crate::fxmap::FxHashMap;

/// Emission state of the structurer for one function.
pub(super) struct Emit<'e, L: Lifter> {
    /// The function's basic blocks in address order.
    pub(super) blocks: &'e [BasicBlock],
    /// Each block's start address mapped to its index, the first block at
    /// that address winning as [`Emit::index_of`] always found it.
    pub(super) starts: FxHashMap<u64, usize>,
    /// Decoded instructions per block.
    pub(super) code: &'e [Vec<L::Insn>],
    /// Owned: never-taken edges are removed before structuring.
    pub(super) succs: Vec<Vec<usize>>,
    /// Owned: structuring through a trampoline re-parents its target.
    pub(super) preds: Vec<Vec<usize>>,
    /// IN environments per block from the dataflow.
    pub(super) in_envs: &'e [Env],
    /// Liveness oracle.
    pub(super) live: &'e Live,
    /// Which blocks the dataflow processed.
    pub(super) processed: &'e [bool],
    /// Per block, the equality fact it may read under.
    pub(super) assumes: &'e [Option<(Key, u64)>],
    /// Blocks whose text has been written (or that must never be written).
    pub(super) emitted: Vec<bool>,
    /// Blocks that make the same test as an earlier block, each with that
    /// block ([`twin_tests`]): every jump to one lands on the other.
    pub(super) twins: BTreeMap<usize, usize>,
    /// Blocks nothing reaches once the folded branches lost their dead
    /// edges: marked emitted from the start, with no edges in or out.
    pub(super) dead: Vec<bool>,
    /// Blocks at or beyond this index lie after the loop being emitted and
    /// are never absorbed into a structure inside it.
    pub(super) bound: usize,
    /// Blocks inside the loop's address range that are not the loop's to
    /// emit (entered from outside it); a structure inside the loop treats
    /// them as it treats the blocks beyond the bound.
    pub(super) skipped: BTreeSet<usize>,
    /// Loop headers whose bodies are being emitted (re-entry guard).
    pub(super) loops: Vec<usize>,
    /// One-way blocks that may not be copied into an arm: a predecessor
    /// outside the structure still needs the original, so a copy would only
    /// duplicate the text and keep the goto. Set while one structure's arms
    /// are computed, then cleared.
    pub(super) no_dup: BTreeSet<usize>,
    /// Whether a copied chain may include a block ending in a call. Off by
    /// default (a copied call is a copied side effect); a branch that
    /// structures no other way turns it on for a later attempt.
    pub(super) copy_calls: bool,
    /// Goto sites a shared return tail has been cloned into so far, capped
    /// by [`TAIL_CLONE_MAX`].
    pub(super) tail_clones: usize,
    /// Whether the block that ends a region (the other arm's start) may be
    /// copied into it when it leads one way into the region's exits. Off by
    /// default (the arm would rather fall into it); a branch that structures
    /// no other way turns it on for a second attempt.
    pub(super) copy_stop: bool,
    /// Blocks each enclosing structure copies privately, innermost last; an
    /// inner structure may copy them too, since the enclosing one owns every
    /// predecessor and writes no original.
    pub(super) dup_stack: Vec<BTreeSet<usize>>,
    /// Blocks a copied block jumps to. The copy is a path [`Emit::preds`]
    /// does not list, so such a block keeps its label: no fold may take it
    /// into its one listed predecessor's test ([`call_then_test`],
    /// [`pure_condition`]).
    pub(super) copy_targets: BTreeSet<usize>,
    /// The block the function is entered at: an entry of any loop it is
    /// in, whatever its predecessors.
    pub(super) entry: usize,
    /// Blocks only the exception runtime enters ([`guarded::Plan::roots`]):
    /// written though no predecessor of theirs is.
    pub(super) eh_roots: BTreeSet<usize>,
    /// Emission orders of the structures being written, innermost last, each
    /// with the position of the block currently being emitted. Top level is
    /// address order.
    pub(super) orders: Vec<(Vec<usize>, usize)>,
}

impl<L: Lifter> Emit<'_, L> {
    /// Returns the start address of block `i` (`0` for an invalid index).
    ///
    /// # Arguments
    ///
    /// * `i` - Block index.
    pub(super) fn start(&self, i: usize) -> u64 {
        self.start_of(i).unwrap_or(0)
    }

    /// Returns the start address of block `i`, or `None` past the last
    /// block (the index a structure continues at when it ends the text).
    ///
    /// # Arguments
    ///
    /// * `i` - Block index.
    pub(super) fn start_of(&self, i: usize) -> Option<u64> {
        self.blocks.get(i).map(|b| b.start)
    }

    /// Tells whether block `b` lies outside the loop being emitted: beyond
    /// its bound, or inside its address range but not its to emit.
    ///
    /// # Arguments
    ///
    /// * `b` - Block index.
    pub(super) fn outside(&self, b: usize) -> bool {
        b >= self.bound || self.skipped.contains(&b)
    }

    /// Returns the block whose text will follow block `i`.
    ///
    /// # Arguments
    ///
    /// * `i` - The block being emitted.
    ///
    /// # Returns
    ///
    /// The next unemitted block in the innermost structure's order (a copied
    /// tail counts: it is placed where control falls into it), else the next
    /// unemitted block by address.
    pub(super) fn next_block(&self, i: usize) -> Option<usize> {
        match self.orders.last() {
            Some((order, pos)) => order
                .iter()
                .skip(pos + 1)
                .copied()
                .find(|b| !self.emitted[*b]),
            None => (i + 1..self.bound).find(|&b| !self.emitted[b] && !self.skipped.contains(&b)),
        }
    }

    /// Records the position within the innermost structure's order.
    ///
    /// # Arguments
    ///
    /// * `pos` - Index into that order.
    pub(super) fn set_pos(&mut self, pos: usize) {
        if let Some(top) = self.orders.last_mut() {
            top.1 = pos;
        }
    }

    /// Finds the block starting at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - A block start address.
    pub(super) fn index_of(&self, va: u64) -> Option<usize> {
        let i = self.starts.get(&va).copied()?;
        Some(self.twins.get(&i).copied().unwrap_or(i))
    }

    /// Returns the start addresses of the blocks that end in a call the
    /// binary never returns from, for folding the text's jumps.
    ///
    /// Such a block has no successor left, and its call ends its path
    /// ([`crate::analysis::functions::call_ends_path`]).
    ///
    /// # Arguments
    ///
    /// * `ctx` - Per-function state: the program and its functions.
    /// * `cleanup` - Whether the body is cleaned at all.
    /// * `skip` - The passes left out.
    ///
    /// # Returns
    ///
    /// The addresses, or `None` when the jumps stay as written: the body is
    /// not cleaned, or [`Pass::FoldJumps`] is left out.
    pub(super) fn ends(&self, ctx: &Ctx<'_>, cleanup: bool, skip: Passes) -> Option<BTreeSet<u64>> {
        let ends = self
            .blocks
            .iter()
            .zip(&self.succs)
            .filter(|(b, succs)| {
                succs.is_empty()
                    && crate::analysis::functions::call_ends_path(ctx.program, ctx.analysis, b)
            })
            .map(|(b, _)| b.start);
        (cleanup && skip.runs(Pass::FoldJumps)).then(|| ends.collect())
    }

    /// Tells whether no path of the text can reach block `b` any more.
    ///
    /// Every predecessor is written, so none still to come can jump to it,
    /// and the written text names no jump to its label: every way in was a
    /// copy of it (a shared `return` each arm of a switch, or of an `if`
    /// and then a switch, wrote for itself). Written anyway, the original
    /// would stand after code that never falls into it, a `return` no
    /// path runs.
    ///
    /// # Arguments
    ///
    /// * `b` - Block index.
    /// * `named` - The labels the text written so far jumps to ([`note_jumps`]).
    pub(super) fn unread(&self, b: usize, named: &BTreeSet<u64>) -> bool {
        b != self.entry
            && !self.eh_roots.contains(&b)
            && self.preds[b].iter().all(|&p| self.emitted[p])
            && !named.contains(&self.start(b))
    }
}

/// Adds the label of every `goto L_<va>;` in `text` to `named`.
///
/// # Arguments
///
/// * `text` - Text just written.
/// * `named` - The labels jumped to so far.
pub(super) fn note_jumps(text: &str, named: &mut BTreeSet<u64>) {
    const JUMP: &str = "goto L_";
    for (at, _) in text.match_indices(JUMP) {
        let hex = text[at + JUMP.len()..]
            .split(|c: char| !c.is_ascii_hexdigit())
            .next()
            .unwrap_or("");
        if let Ok(va) = u64::from_str_radix(hex, 16) {
            named.insert(va);
        }
    }
}

/// Executes block `i` for emission.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - Block index.
///
/// # Returns
///
/// Body lines plus phi assignments, with the captured branch condition and
/// switch index kept consistent with them.
pub(super) fn run_block<L: Lifter>(ctx: &mut Ctx<'_>, st: &Emit<'_, L>, i: usize) -> BlockOut {
    run_block_env(ctx, st, i).0
}

/// Executes block `i` for emission, also returning the environment after it.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - Block index.
pub(super) fn run_block_env<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &Emit<'_, L>,
    i: usize,
) -> (BlockOut, Env) {
    let mut env = st.in_envs[i].clone();
    let succs = &st.succs[i];
    let ins = st.in_envs;
    let live = st.live;
    let processed = st.processed;
    let phi = |out: &Env| phi_keys(out, succs, ins, live, processed, None);
    let live_out = |k: Key| succs.iter().any(|&s| live.is_live(s, k));
    let facts = block_facts::<L>(ctx, st.code, &st.succs, &st.live.need, st.assumes, i);
    let out = L::exec_block(
        ctx,
        &st.code[i],
        i.checked_sub(1).map(|p| st.code[p].as_slice()),
        &mut env,
        lift::Pass::Emission,
        Some((&phi, &live_out)),
        facts,
    );
    (out, env)
}

/// The side of a branch an arm is written for.
///
/// The guard renders as the branch tests it for the target side and
/// negated for the fall-through side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Side {
    /// The branch target.
    Target,
    /// The fall-through.
    Fall,
}

impl Side {
    /// The other side of the same branch.
    pub(super) fn other(self) -> Side {
        match self {
            Side::Target => Side::Fall,
            Side::Fall => Side::Target,
        }
    }
}

/// One body of a `switch` with the `case N:` labels that reach it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Arm {
    /// Index of the block the arm starts at.
    pub(super) body: usize,
    /// The `case N:` lines written in front of it, in table order.
    pub(super) labels: Vec<String>,
}

/// Groups a jump table's entries by target, in first-appearance order,
/// each with the case numbers that reach it.
///
/// # Arguments
///
/// * `targets` - The table's targets, indexed by case number.
pub(super) fn table_arms(targets: &[u64]) -> Vec<(u64, Vec<usize>)> {
    let mut arms: Vec<(u64, Vec<usize>)> = Vec::new();
    for (n, &target) in targets.iter().enumerate() {
        match arms.iter_mut().find(|(t, _)| *t == target) {
            Some((_, ns)) => ns.push(n),
            None => arms.push((target, vec![n])),
        }
    }
    arms
}

/// Renders a jump table's case numbers as `case N:` lines.
///
/// # Arguments
///
/// * `ns` - The case numbers.
pub(super) fn case_labels(ns: &[usize]) -> Vec<String> {
    ns.iter().map(|n| format!("case {n}:")).collect()
}

/// A branch condition, possibly a short-circuit chain merged from several
/// pure condition blocks (`if a goto X; if b goto X;` is `a || b`).
#[derive(Debug, Clone)]
pub(super) enum Guard {
    /// One block's condition, with the call it takes in, if any
    /// ([`call_in_cond`]).
    One(expr::Cond, Option<InCond>),
    /// Either side holds.
    Or(Box<Guard>, Box<Guard>),
    /// Both sides hold.
    And(Box<Guard>, Box<Guard>),
}

/// A call whose result only its block's branch reads, written inside the
/// branch's condition instead of on a line of its own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct InCond {
    /// The variable the result was assigned to, as the condition names it.
    pub(super) var: String,
    /// The call as its line wrote it.
    pub(super) call: String,
}

/// The integer types a condition casts its operands to: words that name
/// no variable.
const CAST_TYPES: [&str; 10] = [
    "int8_t",
    "int16_t",
    "int32_t",
    "int64_t",
    "uint8_t",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "intptr_t",
    "uintptr_t",
];

/// Finds the call a block's branch alone reads the result of.
///
/// `rax = strcmp(a, b); if (rax != 0)` is `if (strcmp(a, b) != 0)` when
/// the call is the block's last statement (its second result right after
/// it, if the text shows one), no successor reads the result (nor the
/// second one), and the condition names the result once and reads nothing
/// else but constants: an operand read after the call might be one the
/// call changes, where C leaves the order of the two open. The call is
/// evaluated where the condition is, as it was, and a guard chain that
/// holds it skips it on the paths the blocks did.
///
/// # Arguments
///
/// * `ctx` - Per-function state (names).
/// * `st` - Emission state (liveness, successors).
/// * `b` - The block.
/// * `out` - What the block wrote.
/// * `cond` - Its branch condition.
///
/// # Returns
///
/// How many of the block's lines stay, and the call the condition takes
/// in; `None` when it takes in none.
pub(super) fn call_in_cond<L: Lifter>(
    ctx: &Ctx<'_>,
    st: &Emit<'_, L>,
    b: usize,
    out: &BlockOut,
    cond: &expr::Cond,
) -> Option<(usize, InCond)> {
    let lift::EffectKind::Call(call) = &out
        .effects
        .iter()
        .rev()
        .find(|e| !matches!(e.kind, lift::EffectKind::Branch(_)))?
        .kind
    else {
        return None;
    };
    let lift::Call {
        result: Some(k),
        result2,
        noreturn: false,
        shown: lift::Shown::Statement,
        ..
    } = call.as_ref()
    else {
        return None;
    };
    let dead = |k: Key| {
        st.succs.get(b).is_some_and(|ss| {
            ss.iter().all(|&s| {
                !st.live.is_live(s, k)
                    && st.in_envs.get(s).is_some_and(|env| {
                        !env.flags.mentions(k) && env.vals.values().all(|v| !v.mentions(k))
                    })
            })
        })
    };
    if !dead(*k) || result2.is_some_and(|k2| !dead(k2)) {
        return None;
    }
    let names = ctx.names();
    let var = names.key(*k);
    let kept = out
        .lines
        .len()
        .checked_sub(1 + usize::from(result2.is_some()))?;
    let text = out
        .lines
        .get(kept)?
        .strip_prefix(&format!("{var} = "))?
        .strip_suffix(';')?;
    let open = text.strip_suffix(')').and_then(|_| {
        text.match_indices('(')
            .map(|(o, _)| o)
            .find(|&o| matching_paren(text, o) == Some(text.len() - 1))
    })?;
    let callee = text.get(..open)?;
    let operators = [
        " | ", " & ", " ^ ", " + ", " - ", " * ", " / ", " % ", " << ", " >> ", " ? ", " == ",
        " != ", " < ", " > ", " <= ", " >= ", " && ", " || ",
    ];
    if callee.is_empty() || callee.starts_with('(') || operators.iter().any(|o| callee.contains(o))
    {
        return None;
    }
    let text = text.to_owned();
    let reads_only_var = |inverted: bool| {
        let rendered = cond.render(&names, inverted);
        word_positions(&rendered, &var).len() == 1
            && tokens(&rendered).all(|w| {
                w == var || CAST_TYPES.contains(&w) || w.starts_with(|c: char| c.is_ascii_digit())
            })
    };
    (reads_only_var(false) && reads_only_var(true)).then_some((kept, InCond { var, call: text }))
}

impl Guard {
    /// Tells whether the guard calls a function: a term takes in its
    /// block's call, so the test is a statement even with nothing to guard.
    pub(super) fn calls(&self) -> bool {
        match self {
            Guard::One(_, call) => call.is_some(),
            Guard::Or(a, b) | Guard::And(a, b) => a.calls() || b.calls(),
        }
    }

    /// Returns the negated guard (De Morgan), for merging a chain whose own
    /// target is the outer guard's fall-through side.
    pub(super) fn invert(self) -> Guard {
        match self {
            Guard::One(c, call) => Guard::One(c.invert(), call),
            Guard::Or(a, b) => Guard::And(Box::new(a.invert()), Box::new(b.invert())),
            Guard::And(a, b) => Guard::Or(Box::new(a.invert()), Box::new(b.invert())),
        }
    }

    /// Returns the guard with the tests an earlier term decided absorbed
    /// (`C1 || (!C1 && C2)` is `C1 || C2`).
    ///
    /// A chain's terms are reached in evaluation order, each only after
    /// every earlier one failed, so a compound term of the other operator
    /// whose own test an earlier term decides is constant wherever the
    /// machine evaluates it and decides nothing. The redundant test goes;
    /// the term that carried it keeps its remaining operand, which the
    /// machine reached under exactly the same conditions. A test with a
    /// call in it ([`Guard::calls`]) stays, since the machine runs the
    /// call wherever the block ran and dropping the test would drop the
    /// call.
    pub(super) fn minimize(self) -> Guard {
        match self {
            one @ Guard::One(..) => one,
            compound => {
                let or = matches!(compound, Guard::Or(..));
                compound.absorb(&mut Vec::new(), or)
            }
        }
    }

    /// Walks one chain's operands in evaluation order, absorbing each
    /// compound term's decided test ([`Guard::minimize`]).
    ///
    /// A compound operand of the other operator sits behind every term in
    /// `seen`, so the operand one of them decides is constant wherever
    /// the machine evaluates it and the other operand is the whole term.
    ///
    /// # Arguments
    ///
    /// * `seen` - The one-condition terms the chain decided already,
    ///   which a later term's own test may not duplicate.
    /// * `or` - Whether the chain being walked joins by `||`.
    fn absorb(self, seen: &mut Vec<Guard>, or: bool) -> Guard {
        let out = match self {
            Guard::Or(a, b) if or => {
                Guard::Or(Box::new(a.absorb(seen, or)), Box::new(b.absorb(seen, or)))
            }
            Guard::And(a, b) if !or => {
                Guard::And(Box::new(a.absorb(seen, or)), Box::new(b.absorb(seen, or)))
            }
            Guard::Or(a, b) | Guard::And(a, b) => {
                let (a, b) = (*a, *b);
                let decided = |g: &Guard| !g.calls() && seen.iter().any(|e| g.negates(e));
                if decided(&a) {
                    b
                } else if decided(&b) {
                    a
                } else {
                    wrap(a, b, !or)
                }
            }
            one @ Guard::One(..) => one,
        };
        if matches!(out, Guard::One(..)) {
            seen.push(out.clone());
        }
        out
    }

    /// Tells whether this one condition is the negation of `other`.
    ///
    /// The flipped code over the same flags is the exact negation, a float
    /// compare's included: its predicate negates within the set
    /// ([`super::fcmp::FPred::negate`]), NaN order and all. A condition
    /// that carries a call decides nothing, which the caller checks.
    ///
    /// # Arguments
    ///
    /// * `other` - The one condition this one may negate.
    fn negates(&self, other: &Guard) -> bool {
        let (Guard::One(a, ka), Guard::One(b, kb)) = (self, other) else {
            return false;
        };
        a.cc.0 != ConditionCode::None && ka == kb && b.cc.0 == a.cc.invert().0 && b.flags == a.flags
    }

    /// Renders the guard as a C boolean expression.
    ///
    /// De Morgan keeps the inverted form readable (`!(a || b)` renders as
    /// `!a && !b`); compound operands of the other operator are
    /// parenthesized, and a chain's same-operator operands render flat in
    /// evaluation order ([`Guard::chain`]). A condition that takes in its
    /// block's call names the call where it named the result.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `side` - The side the arm is on; the fall-through side renders
    ///   the negation.
    pub(super) fn render(&self, n: &Names<'_>, side: Side) -> String {
        if let Some(members) = self.bit_set(n, side) {
            return members;
        }
        match (self, side) {
            (Guard::One(c, None), _) => c.render(n, side == Side::Fall),
            (Guard::One(c, Some(call)), _) => {
                rename_word(&c.render(n, side == Side::Fall), &call.var, &call.call)
            }
            (Guard::Or(..), Side::Fall) | (Guard::And(..), Side::Target) => {
                self.chain(n, side, " && ")
            }
            (Guard::Or(..), Side::Target) | (Guard::And(..), Side::Fall) => {
                self.chain(n, side, " || ")
            }
        }
    }

    /// Renders one short-circuit chain's operands joined by `sep`.
    ///
    /// The chain's same-operator descendants are spliced flat, in
    /// evaluation order, so a condition merged block by block reads as
    /// one list (`a && b && c`, never `a && (b && c)`); a compound of the
    /// other operator, or a single condition that renders a chain of its
    /// own, keeps its parentheses.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `side` - The side the arm is on, as for [`Guard::render`].
    /// * `sep` - The operator that joins the operands.
    fn chain(&self, n: &Names<'_>, side: Side, sep: &str) -> String {
        let or = matches!(self, Guard::Or(..));
        let mut ops: Vec<&Guard> = Vec::new();
        splice(self, &mut ops);
        let parts: Vec<String> = ops
            .iter()
            .map(|g| {
                let text = g.render(n, side);
                let flat = match g {
                    Guard::Or(..) | Guard::And(..) => matches!(g, Guard::Or(..)) == or,
                    Guard::One(..) => logical_operands(&text).is_none(),
                };
                if flat { text } else { format!("({text})") }
            })
            .collect();
        parts.join(sep)
    }

    /// Renders a range test joined to a bit test of a constant as the set
    /// of values it admits.
    ///
    /// A compiler turns `x == 5 || x == 32 || x == 59` into `x - 5 <= 54
    /// && bt(0x40000008000001, x - 5)`: the range keeps the bit index
    /// inside the constant, whose set bits are the members. The pair reads
    /// as the list it came from, `x == 5 || x == 32 || x == 59`, and its
    /// negation as `x != 5 && ...`. A range that lets everything outside
    /// it through (`x > 28 || bit set`) keeps its test in front of the
    /// list, as does one that requires the inside with the bit clear. Up
    /// to [`BIT_SET_MAX`] members; the range and the bit index must test
    /// the same value ([`same_index`]).
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `side` - The side the arm is on, as for [`Guard::render`].
    ///
    /// # Returns
    ///
    /// The comparisons, or `None` when the guard is no such pair.
    fn bit_set(&self, n: &Names<'_>, side: Side) -> Option<String> {
        let (Guard::And(a, b) | Guard::Or(a, b)) = self else {
            return None;
        };
        let (Guard::One(range, None), Guard::One(bit, None)) = (a.as_ref(), b.as_ref()) else {
            return None;
        };
        let inverted = side == Side::Fall;
        let joins_and = matches!(
            (self, side),
            (Guard::And(..), Side::Target) | (Guard::Or(..), Side::Fall)
        );
        let (x, bits, max, inside) = range_test(range, inverted)?;
        let (index, mask, set, when_set) = bit_test(bit, inverted)?;
        let (member, keep_range) = match (joins_and, inside, when_set) {
            (true, true, true) => (true, false),
            (false, false, false) => (false, false),
            (false, false, true) => (true, true),
            (true, true, false) => (false, true),
            (true, false, _) | (false, true, _) => return None,
        };
        if max > mask || !same_index(index, x, max, mask) {
            return None;
        }
        let values: Vec<u64> = (0..=max).filter(|v| (set >> v) & 1 == 1).collect();
        if values.is_empty() || values.len() > BIT_SET_MAX {
            return None;
        }
        let cc = Cc(if member {
            ConditionCode::e
        } else {
            ConditionCode::ne
        });
        let tests: Vec<String> = keep_range
            .then(|| range.render(n, inverted))
            .into_iter()
            .chain(values.iter().map(|v| {
                expr::Cond {
                    cc,
                    flags: Flags::Cmp(x.clone(), Expr::Const(*v), bits),
                }
                .render(n, false)
            }))
            .collect();
        Some(tests.join(if member { " || " } else { " && " }))
    }
}

/// Wraps two guards in the compound `or` names.
///
/// # Arguments
///
/// * `a` - One operand.
/// * `b` - The other operand.
/// * `or` - Whether the compound joins by `||`.
fn wrap(a: Guard, b: Guard, or: bool) -> Guard {
    if or {
        Guard::Or(Box::new(a), Box::new(b))
    } else {
        Guard::And(Box::new(a), Box::new(b))
    }
}

/// Splices a compound guard's same-operator operands into `ops`, in
/// evaluation order.
///
/// # Arguments
///
/// * `g` - The compound guard.
/// * `ops` - Receives the chain's operands in order; a compound of the
///   other operator goes in whole.
fn splice<'a>(g: &'a Guard, ops: &mut Vec<&'a Guard>) {
    let (a, b, or) = match g {
        Guard::Or(a, b) => (a.as_ref(), b.as_ref(), true),
        Guard::And(a, b) => (a.as_ref(), b.as_ref(), false),
        one @ Guard::One(..) => {
            ops.push(one);
            return;
        }
    };
    for c in [a, b] {
        if matches!(c, Guard::Or(..)) == or {
            splice(c, ops);
        } else {
            ops.push(c);
        }
    }
}

/// Tells whether a bit index reads the value a range test bounds.
///
/// The index may be the value itself, the value before a mask the range
/// test applies (`(x & 0xff) <= 13` against bit `x & 0x1f`: a value the
/// range admits has no bits the mask would clear), or its sign extension
/// when the range admits no value with the sign bit set.
///
/// # Arguments
///
/// * `index` - The bit index, its own mask removed.
/// * `x` - The value the range test bounds.
/// * `max` - The largest value the range admits.
/// * `mask` - The mask the bit test wraps the index with.
fn same_index(index: &Expr, x: &Expr, max: u64, mask: u64) -> bool {
    let index = match index {
        Expr::Sext(e, b) if b.checked_sub(1).is_some_and(|s| max < 1u64 << s.min(63)) => e.as_ref(),
        other => other,
    };
    index == x
        || matches!(x, Expr::Bin(expr::Op::And, inner, m)
            if inner.as_ref() == index
                && matches!(**m, Expr::Const(k) if k >= mask && k & k.wrapping_add(1) == 0))
}

/// Most members a range and bit test is listed as ([`Guard::bit_set`]).
pub(super) const BIT_SET_MAX: usize = 8;

/// Reads a condition as an unsigned bound on a value: `x <= max` holding
/// (inside) or failing (outside).
///
/// # Arguments
///
/// * `c` - The condition.
/// * `inverted` - Read its negation.
///
/// # Returns
///
/// The value, its width, the largest value inside, and whether the
/// condition holds inside; `None` for any other condition.
fn range_test(c: &expr::Cond, inverted: bool) -> Option<(&Expr, u8, u64, bool)> {
    let Flags::Cmp(x, Expr::Const(k), bits) = &c.flags else {
        return None;
    };
    let cc = if inverted { c.cc.invert() } else { c.cc };
    match cc.0 {
        ConditionCode::be => Some((x, *bits, *k, true)),
        ConditionCode::b => Some((x, *bits, k.checked_sub(1)?, true)),
        ConditionCode::a => Some((x, *bits, *k, false)),
        ConditionCode::ae => Some((x, *bits, k.checked_sub(1)?, false)),
        ConditionCode::None
        | ConditionCode::o
        | ConditionCode::no
        | ConditionCode::e
        | ConditionCode::ne
        | ConditionCode::s
        | ConditionCode::ns
        | ConditionCode::p
        | ConditionCode::np
        | ConditionCode::l
        | ConditionCode::ge
        | ConditionCode::le
        | ConditionCode::g => None,
    }
}

/// Reads a condition as a test of one bit of a constant, `bt` style: bit
/// `index & mask` of `set`.
///
/// # Arguments
///
/// * `c` - The condition.
/// * `inverted` - Read its negation.
///
/// # Returns
///
/// The index, the mask the instruction wraps it with, the constant, and
/// whether the condition holds when the bit is set; `None` for any other
/// condition.
fn bit_test(c: &expr::Cond, inverted: bool) -> Option<(&Expr, u64, u64, bool)> {
    let Flags::Carry(Expr::Bin(expr::Op::And, shifted, one)) = &c.flags else {
        return None;
    };
    let (Expr::Bin(expr::Op::Shr, set, index), Expr::Const(1)) = (shifted.as_ref(), one.as_ref())
    else {
        return None;
    };
    let (Expr::Const(set), Expr::Bin(expr::Op::And, index, mask)) = (set.as_ref(), index.as_ref())
    else {
        return None;
    };
    let Expr::Const(mask @ (31 | 63)) = mask.as_ref() else {
        return None;
    };
    let cc = if inverted { c.cc.invert() } else { c.cc };
    let when_set = match cc.0 {
        ConditionCode::b => true,
        ConditionCode::ae => false,
        ConditionCode::None
        | ConditionCode::o
        | ConditionCode::no
        | ConditionCode::e
        | ConditionCode::ne
        | ConditionCode::be
        | ConditionCode::a
        | ConditionCode::s
        | ConditionCode::ns
        | ConditionCode::p
        | ConditionCode::np
        | ConditionCode::l
        | ConditionCode::ge
        | ConditionCode::le
        | ConditionCode::g => return None,
    };
    Some((index, *mask, *set, when_set))
}

/// Splits a rendered condition at its top-level `&&` or `||`.
///
/// Brackets, string literals and character literals are skipped, so only
/// the operators that join the whole condition count. A condition joined by
/// both operators is not split, since its precedence would have to be read
/// too.
///
/// # Arguments
///
/// * `cond` - The rendered condition.
///
/// # Returns
///
/// The operator (`"&&"` or `"||"`) and the operands in order, or `None`
/// when the condition is no such chain.
pub(super) fn logical_operands(cond: &str) -> Option<(&'static str, Vec<&str>)> {
    let bytes = cond.as_bytes();
    let mut depth = 0i32;
    let mut quote: Option<u8> = None;
    let mut esc = false;
    let mut op: Option<&'static str> = None;
    let mut parts = Vec::new();
    let mut from = 0;
    let mut i = 0;
    while let Some(&c) = bytes.get(i) {
        i += 1;
        if let Some(q) = quote {
            match c {
                _ if esc => esc = false,
                b'\\' => esc = true,
                _ if c == q => quote = None,
                _ => {}
            }
            continue;
        }
        match c {
            b'"' | b'\'' => quote = Some(c),
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            b' ' if depth == 0 => {
                let found = match bytes.get(i..i + 3) {
                    Some(b"&& ") => "&&",
                    Some(b"|| ") => "||",
                    _ => continue,
                };
                if op.is_some_and(|o| o != found) {
                    return None;
                }
                op = Some(found);
                parts.push(cond.get(from..i - 1)?);
                from = i + 3;
                i += 3;
            }
            _ => {}
        }
    }
    parts.push(cond.get(from..)?);
    Some((op?, parts))
}

/// Negates a rendered `&&` or `||` chain by De Morgan's law.
///
/// `!(a != 0 && b < c)` reads as `a == 0 || b >= c`: each operand is
/// negated on its own ([`invert_condition`]) and the operator turns into
/// the other one, in the order the operands were evaluated, so a short
/// circuit still skips what it skipped. An operand that is a parenthesized
/// chain is negated the same way and keeps its parentheses. The chain stays
/// whole when an operand would only negate as `!(...)`, as a bare value
/// does.
///
/// # Arguments
///
/// * `cond` - The rendered condition.
///
/// # Returns
///
/// The negation, or `None` when the condition is no chain or an operand
/// does not negate by itself.
pub(super) fn de_morgan(cond: &str) -> Option<String> {
    let (op, parts) = logical_operands(cond)?;
    let dual = if op == "&&" { " || " } else { " && " };
    let mut out = Vec::with_capacity(parts.len());
    for p in parts {
        let inner = p
            .strip_prefix('(')
            .and_then(|r| r.strip_suffix(')'))
            .filter(|r| matching_paren(p, 0) == Some(r.len() + 1));
        let negated = match inner {
            Some(r) if logical_operands(r).is_some() => de_morgan(r)?,
            Some(r) => invert_condition(r),
            None => invert_condition(p),
        };
        if negated.starts_with("!(") {
            return None;
        }
        out.push(if logical_operands(&negated).is_some() {
            format!("({negated})")
        } else {
            negated
        });
    }
    Some(out.join(dual))
}

/// A block's decision as a term of a guard ([`pure_condition`]).
pub(super) struct Decision {
    /// The condition.
    pub(super) cond: expr::Cond,
    /// The call the condition takes in, if any.
    pub(super) call: Option<InCond>,
    /// The block the condition branches to when it holds.
    pub(super) t: usize,
    /// The block it falls through to otherwise.
    pub(super) f: usize,
    /// The block that tests, when it is not the candidate itself: the
    /// test a block ending in a call falls into ([`call_then_test`]), which
    /// the guard consumes with it.
    pub(super) test: Option<usize>,
}

/// Recognizes a block that only decides, so its condition can fold into the
/// predecessor's guard.
///
/// Lazy register and slot copies the block leaves in the environment are
/// consistent whoever prints the decision (every successor's entry state
/// came from the dataflow); only statements and frame changes are not. A
/// block whose one statement is a call its test takes in ([`call_in_cond`],
/// [`call_then_test`]) only decides too: the call moves into the guard
/// term, which the chain evaluates exactly when the block ran.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `from` - The predecessor whose guard would absorb the block.
/// * `b` - The candidate block.
///
/// # Returns
///
/// The decision, or `None` when the block is not a conditional (or a call
/// falling into one) entered only from `from`, has other statements, a
/// switch dispatch, changes the stack pointer, or has a constant condition
/// (its dead edge was pruned, so it is a plain jump, not a guard term).
pub(super) fn pure_condition<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    from: usize,
    b: usize,
) -> Option<Decision> {
    if b == from
        || st.outside(b)
        || st.emitted[b]
        || st.preds[b].as_slice() != [from]
        || st.copy_targets.contains(&b)
    {
        return None;
    }
    let (out, env) = match st.blocks[b].term {
        BlockTerm::Cond | BlockTerm::Call => run_block_env(ctx, st, b),
        BlockTerm::Fall
        | BlockTerm::Jmp
        | BlockTerm::Ret
        | BlockTerm::Indirect
        | BlockTerm::Invalid => return None,
    };
    if out.switch_idx.is_some() || env.sp != st.in_envs[b].sp {
        return None;
    }
    let (test, br, call) = match &out.branch {
        Some(br) => {
            let call = if out.lines.is_empty() {
                None
            } else {
                Some(call_in_cond(ctx, st, b, &out, &br.cond)?)
            };
            (None, br.clone(), call)
        }
        None => {
            let (s, br, call) = call_then_test(ctx, st, b, &out)?;
            (Some(s), br, Some(call))
        }
    };
    if br.cond.eval().is_some() || call.as_ref().is_some_and(|(kept, _)| *kept != 0) {
        return None;
    }
    Some(Decision {
        t: st.index_of(br.target)?,
        f: st.index_of(br.fall)?,
        cond: br.cond,
        call: call.map(|(_, c)| c),
        test,
    })
}

/// Finds the test a block ending in a call falls into, when the test
/// decides on the call's result alone ([`call_in_cond`]).
///
/// The call ends its block, so `rax = f(); if (rax != 0)` is two blocks:
/// the call's, and the test entered only from it, which writes nothing.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `p` - The block ending in the call.
/// * `out` - What `p` wrote.
///
/// # Returns
///
/// The test block, its branch, and how many of `p`'s lines stay with the
/// call the test takes in; `None` when `p` is no such block.
pub(super) fn call_then_test<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &Emit<'_, L>,
    p: usize,
    out: &BlockOut,
) -> Option<(usize, Branch, (usize, InCond))> {
    let &[s] = st.succs.get(p)?.as_slice() else {
        return None;
    };
    if st.blocks[p].term != BlockTerm::Call
        || s == p
        || st.outside(s)
        || st.emitted[s]
        || st.preds[s].as_slice() != [p]
        || st.copy_targets.contains(&s)
        || st.blocks[s].term != BlockTerm::Cond
    {
        return None;
    }
    let (test, env) = run_block_env(ctx, st, s);
    let br = test.branch?;
    if !test.lines.is_empty()
        || test.switch_idx.is_some()
        || env.sp != st.in_envs[s].sp
        || br.cond.eval().is_some()
    {
        return None;
    }
    let call = call_in_cond(ctx, st, s, out, &br.cond)?;
    Some((s, br, call))
}

/// Merges the pure condition blocks hanging off `i`'s branch into one
/// guard, then absorbs the tests an earlier term decided
/// ([`Guard::minimize`]).
///
/// Merged blocks are consumed and their successors re-parented to `i`.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - The header block.
/// * `cond` - Its own condition.
/// * `call` - The call its condition takes in, if any.
/// * `t` - Its branch target block.
/// * `f` - Its fall-through block.
///
/// # Returns
///
/// `(guard, target, fall)` after merging.
pub(super) fn merge_guard<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    i: usize,
    (cond, call): (expr::Cond, Option<InCond>),
    t: usize,
    f: usize,
) -> (Guard, usize, usize) {
    let mut journal = Journal::default();
    let (guard, t, f) = merge_chain(ctx, st, i, Guard::One(cond, call), t, f, 0, &mut journal);
    (guard.minimize(), t, f)
}

/// Deepest chain of pure condition blocks merged into one guard.
pub(super) const MAX_GUARD_DEPTH: usize = 4;

/// One entry of the structuring state as it stood before a speculative
/// merge changed it.
pub(super) enum Undo {
    /// The emitted flag of a block.
    Emitted(usize, bool),
    /// The successors of a block.
    Succs(usize, Vec<usize>),
    /// The predecessors of a block.
    Preds(usize, Vec<usize>),
}

/// The structuring state a speculative merge changes, recorded entry by
/// entry as it changes, so a failed merge can give it back.
///
/// A merge marks the journal before it starts ([`Journal::mark`]) and
/// restores to that mark when the merged block does not fit
/// ([`Journal::restore`]); a merge that fits leaves its entries, since a
/// merge enclosing it may still fail. Copying the three per-block tables
/// instead cost half a millisecond per candidate on a function of ten
/// thousand blocks, most of a second over the function.
#[derive(Default)]
pub(super) struct Journal(Vec<Undo>);

impl Journal {
    /// Returns where the journal stands, to restore to.
    pub(super) fn mark(&self) -> usize {
        self.0.len()
    }

    /// Records block `b`'s emitted flag before it changes.
    ///
    /// # Arguments
    ///
    /// * `st` - Emission state.
    /// * `b` - Block index.
    pub(super) fn emitted<L: Lifter>(&mut self, st: &Emit<'_, L>, b: usize) {
        self.0.push(Undo::Emitted(b, st.emitted[b]));
    }

    /// Records block `b`'s successors before they change.
    ///
    /// # Arguments
    ///
    /// * `st` - Emission state.
    /// * `b` - Block index.
    pub(super) fn succs<L: Lifter>(&mut self, st: &Emit<'_, L>, b: usize) {
        self.0.push(Undo::Succs(b, st.succs[b].clone()));
    }

    /// Records block `b`'s predecessors before they change.
    ///
    /// # Arguments
    ///
    /// * `st` - Emission state.
    /// * `b` - Block index.
    pub(super) fn preds<L: Lifter>(&mut self, st: &Emit<'_, L>, b: usize) {
        self.0.push(Undo::Preds(b, st.preds[b].clone()));
    }

    /// Gives back every change recorded since `mark`, newest first.
    ///
    /// # Arguments
    ///
    /// * `st` - Emission state.
    /// * `mark` - Where the journal stood ([`Journal::mark`]).
    pub(super) fn restore<L: Lifter>(&mut self, st: &mut Emit<'_, L>, mark: usize) {
        while self.0.len() > mark {
            match self.0.pop() {
                Some(Undo::Emitted(b, was)) => st.emitted[b] = was,
                Some(Undo::Succs(b, was)) => st.succs[b] = was,
                Some(Undo::Preds(b, was)) => st.preds[b] = was,
                None => break,
            }
        }
    }
}

/// Merges the chain a pure condition block may head before it joins a guard.
///
/// `if a goto X; if b goto Y; if c goto Y; else X` is `a || !(b || c)`: the
/// inner chain (`b || c`) is merged first so the block's whole decision
/// joins the outer guard. The caller undoes it when the merged block does
/// not fit after all.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `block` - The pure condition block heading the chain.
/// * `cond` - Its condition, with the call it takes in, if any.
/// * `t` - Its branch target block.
/// * `f` - Its fall-through block.
/// * `depth` - Current nesting; [`MAX_GUARD_DEPTH`] stops the recursion.
/// * `journal` - Where the merge records what it changes.
#[expect(clippy::too_many_arguments, reason = "the structurer's shape")]
pub(super) fn sub_chain<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    block: usize,
    (cond, call): (expr::Cond, Option<InCond>),
    t: usize,
    f: usize,
    depth: usize,
    journal: &mut Journal,
) -> (Guard, usize, usize) {
    if depth + 1 >= MAX_GUARD_DEPTH {
        return (Guard::One(cond, call), t, f);
    }
    merge_chain(
        ctx,
        st,
        block,
        Guard::One(cond, call),
        t,
        f,
        depth + 1,
        journal,
    )
}

/// Merges pure condition blocks into `guard` while they chain over one target.
///
/// `if a goto T; F: if b goto T2 else F2` merges when `T2 == T`
/// (`a || b`, falling to `F2`) or `F2 == T` (`a || !b`, falling to `T2`);
/// `if a goto X; X: if b goto T2 else F2` merges when `F2 == F` (`a && b`)
/// or `T2 == F` (`a && !b`). Trampolines on the way are followed. Each
/// candidate's own chain is merged first ([`sub_chain`]) and undone when
/// the candidate does not fit.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `header` - The block whose guard grows.
/// * `guard` - The guard so far.
/// * `t` - Current branch target block.
/// * `f` - Current fall-through block.
/// * `depth` - Current nesting.
/// * `journal` - Where the merge records what it changes, so a candidate
///   that does not fit is given back ([`Journal`]).
///
/// # Returns
///
/// `(guard, target, fall)` after merging.
#[expect(clippy::too_many_arguments, reason = "the structurer's shape")]
pub(super) fn merge_chain<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    header: usize,
    mut guard: Guard,
    mut t: usize,
    mut f: usize,
    depth: usize,
    journal: &mut Journal,
) -> (Guard, usize, usize) {
    let mut fuel = 8;
    while fuel > 0 {
        fuel -= 1;
        if let Some(d) = pure_condition(ctx, st, header, f) {
            let consumed = f;
            let decides = d.test.unwrap_or(consumed);
            let mark = journal.mark();
            let t2 = follow_trampoline(ctx, st, decides, d.t, journal);
            let f2 = follow_trampoline(ctx, st, decides, d.f, journal);
            let (g2, t2, f2) =
                sub_chain(ctx, st, decides, (d.cond, d.call), t2, f2, depth, journal);
            let (g, nt, nf) = if t2 == t {
                (Guard::Or(Box::new(guard), Box::new(g2)), t, f2)
            } else if f2 == t {
                (Guard::Or(Box::new(guard), Box::new(g2.invert())), t, t2)
            } else {
                journal.restore(st, mark);
                return (guard, t, f);
            };
            consume(st, header, consumed, journal);
            if let Some(test) = d.test {
                consume(st, header, test, journal);
            }
            guard = g;
            t = nt;
            f = nf;
            continue;
        }
        if let Some(d) = pure_condition(ctx, st, header, t) {
            let consumed = t;
            let decides = d.test.unwrap_or(consumed);
            let mark = journal.mark();
            let t2 = follow_trampoline(ctx, st, decides, d.t, journal);
            let f2 = follow_trampoline(ctx, st, decides, d.f, journal);
            let (g2, t2, f2) =
                sub_chain(ctx, st, decides, (d.cond, d.call), t2, f2, depth, journal);
            let (g, nt, nf) = if f2 == f {
                (Guard::And(Box::new(guard), Box::new(g2)), t2, f)
            } else if t2 == f {
                (Guard::And(Box::new(guard), Box::new(g2.invert())), f2, f)
            } else {
                journal.restore(st, mark);
                return (guard, t, f);
            };
            consume(st, header, consumed, journal);
            if let Some(test) = d.test {
                consume(st, header, test, journal);
            }
            guard = g;
            t = nt;
            f = nf;
            continue;
        }
        break;
    }
    (guard, t, f)
}

/// Folds block `b` into `header`: never emitted; whoever `b` reached is now
/// reached from the header.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `header` - The absorbing block.
/// * `b` - The block folded away.
/// * `journal` - Where the change is recorded.
pub(super) fn consume<L: Lifter>(
    st: &mut Emit<'_, L>,
    header: usize,
    b: usize,
    journal: &mut Journal,
) {
    journal.emitted(st, b);
    st.emitted[b] = true;
    let succs: Vec<usize> = st.succs[b].clone();
    journal.succs(st, header);
    for s in &succs {
        journal.preds(st, *s);
        for p in &mut st.preds[*s] {
            if *p == b {
                *p = header;
            }
        }
        if !st.succs[header].contains(s) {
            st.succs[header].push(*s);
        }
    }
    st.succs[header].retain(|s| *s != b);
}

/// A structured region.
pub(super) struct Region {
    /// Blocks in emission order (reverse post-order from the start).
    pub(super) order: Vec<usize>,
    /// Blocks the region leaves through.
    pub(super) exits: BTreeSet<usize>,
    /// Every member is entered only from the header or from inside.
    pub(super) closed: bool,
    /// Small terminal blocks (shared `return`/trap epilogues) emitted as
    /// private copies rather than jumped to.
    pub(super) dups: BTreeSet<usize>,
}

/// Largest terminal block, or chain of blocks ending in one, worth
/// duplicating into an arm, in instructions that render
/// ([`body_len`]).
pub(super) const DUP_MAX_INSTRS: usize = 8;

/// Counts the instructions of a block that render as statements.
///
/// Epilogue instructions render as nothing: `pop`, `ret`, `leave`, the
/// stack adjustment (`add`/`sub`/`lea` on `rsp`) and the reloads of
/// callee-saved registers from the frame, so a shared return block with a
/// ten-instruction epilogue is as small as its `return`.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
pub(super) fn body_len(instrs: &[Instruction]) -> usize {
    let callee_saved = |r: Register| {
        matches!(
            r.full_register(),
            Register::RBX
                | Register::RBP
                | Register::RSI
                | Register::RDI
                | Register::R12
                | Register::R13
                | Register::R14
                | Register::R15
        )
    };
    instrs
        .iter()
        .filter(|i| {
            let stack = i.op0_kind() == OpKind::Register
                && i.op0_register().full_register() == Register::RSP;
            let reload = i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && callee_saved(i.op0_register())
                && i.op1_kind() == OpKind::Memory
                && i.memory_base() == Register::RSP;
            !(matches!(
                i.mnemonic(),
                Mnemonic::Pop | Mnemonic::Ret | Mnemonic::Leave
            ) || (matches!(i.mnemonic(), Mnemonic::Add | Mnemonic::Sub | Mnemonic::Lea) && stack)
                || reload)
        })
        .count()
}

/// Most instructions a block holds for [`twin_tests`] to pair it.
pub(super) const TWIN_MAX_INSTRS: usize = 4;

/// Pairs each small test block with an earlier block making the same test.
///
/// The test is [`Lifter::same_test`]'s, and the later block's predecessors
/// then jump to the earlier block instead. A compiler that tests one value twice on two paths (`if (x & 2)` after
/// both arms of an `if`) leaves two copies of the test, each a block of its
/// own, and the two paths can only meet again by a jump; read as one block
/// they join where the source did. The same instructions sending each
/// outcome to the same blocks compute the same thing from the same state,
/// so the merge is exact. Pairs where one block's predecessor also reaches
/// the other are left alone, so no branch gains two edges to one block.
///
/// # Arguments
///
/// * `code` - Each block's instructions.
/// * `preds` - Each block's predecessors.
///
/// # Returns
///
/// The later block of each pair, mapped to the earlier.
pub(super) fn twin_tests<L: Lifter>(
    code: &[Vec<L::Insn>],
    preds: &[Vec<usize>],
) -> BTreeMap<usize, usize> {
    let mut twins = BTreeMap::new();
    for (b, instrs) in code.iter().enumerate() {
        if instrs.len() > TWIN_MAX_INSTRS || preds.get(b).is_none_or(Vec::is_empty) {
            continue;
        }
        let first = (0..b).find(|&a| {
            !twins.contains_key(&a)
                && code.get(a).is_some_and(|other| L::same_test(other, instrs))
                && preds.get(a).is_some_and(|pa| {
                    preds
                        .get(b)
                        .is_some_and(|pb| pb.iter().all(|p| *p != a && !pa.contains(p)))
                })
        });
        if let Some(a) = first {
            twins.insert(b, a);
        }
    }
    twins
}

/// Tells whether two x86 blocks make the same test.
///
/// They hold the same instructions up to a conditional branch at the end
/// of each, the branches sending each outcome to the same address (the
/// same condition and targets, or the opposite condition with the taken
/// and fall-through sides swapped).
///
/// # Arguments
///
/// * `a` - One block's instructions.
/// * `b` - The other's.
pub(super) fn same_test(a: &[Instruction], b: &[Instruction]) -> bool {
    let (Some((ja, ha)), Some((jb, hb))) = (a.split_last(), b.split_last()) else {
        return false;
    };
    if ha != hb
        || ja.flow_control() != FlowControl::ConditionalBranch
        || jb.flow_control() != FlowControl::ConditionalBranch
        || ja.condition_code() == ConditionCode::None
    {
        return false;
    }
    let (ta, fa) = (ja.near_branch_target(), ja.next_ip());
    let (tb, fb) = (jb.near_branch_target(), jb.next_ip());
    (ja.mnemonic() == jb.mnemonic() && ta == tb && fa == fb)
        || (ja.code().negate_condition_code().mnemonic() == jb.mnemonic() && ta == fb && fa == tb)
}

/// Longest chain of one-way blocks ending in a terminal block copied whole.
pub(super) const DUP_CHAIN_MAX: usize = 3;

/// Most goto sites one function clones a shared return tail into.
///
/// A tail every site copied is dead text ([`Emit::unread`] drops it), so
/// the cap bounds how much text the rule can add to one function.
pub(super) const TAIL_CLONE_MAX: usize = 4;

/// Largest shared return tail, in instructions that render.
///
/// Counts as [`body_len`] does, worth cloning to a goto site: the two
/// assignments a compiler writes in front of the shared `return`, whose
/// own epilogue renders as nothing.
pub(super) const TAIL_BODY_MAX: usize = 2;

/// Returns the statements of a shared return tail for the site of a `goto`
/// to clone in place of the jump.
///
/// The tail is a block, or a short one-way chain of blocks ending in one
/// ([`DUP_CHAIN_MAX`] long, as the region copier allows), that only
/// returns: every statement it renders is an assignment to a local or a
/// register ([`lift::EffectKind::Assign`]) except the last, the `return`.
/// No calls, stores, unmodeled instructions or stack-pointer changes, so
/// the common `rc = ERR; goto cleanup;` shape, whose cleanup tail calls,
/// stays a goto for a single-cleanup-tail pattern to claim; cloning a call
/// would clone a side effect the function runs once. The tail must be
/// shared ([`Emit::preds`] holds two sites at least): a site of its own is
/// the label-following rule's, and the goto the site writes is dropped by
/// the cleanup. The goto itself is the site block's last statement (an
/// unconditional jump), so the clone replaces the block's whole
/// continuation.
///
/// Each statement renders from the tail's own entry state, as a region's
/// copied tail does ([`copy_chain`]), so every site prints the same text.
/// With every predecessor cloned no text names the tail's label, and the
/// emission driver's [`Emit::unread`] rule drops the original.
///
/// # Arguments
///
/// * `ctx` - Per-function state (names).
/// * `st` - Emission state; the clone count grows by one on success.
/// * `va` - The jump target address.
///
/// # Returns
///
/// The tail's statements, one per line, ending in its `return`; `None`
/// when the target is no shared pure return tail, or the function has
/// cloned [`TAIL_CLONE_MAX`] sites already.
pub(super) fn return_tail<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    va: u64,
) -> Option<String> {
    let t = st.index_of(va)?;
    if st.tail_clones >= TAIL_CLONE_MAX || t == st.entry || st.emitted[t] || st.preds[t].len() < 2 {
        return None;
    }
    let mut body = 0usize;
    let mut chain: Vec<usize> = Vec::new();
    let mut lines: Vec<String> = Vec::new();
    let mut cur = t;
    loop {
        body += L::body_len(&st.code[cur]);
        let (out, env) = run_block_env(ctx, st, cur);
        if body > TAIL_BODY_MAX
            || out.branch.is_some()
            || out.switch_idx.is_some()
            || out.unmodeled > 0
            || env.sp != st.in_envs[cur].sp
        {
            return None;
        }
        let assign_only = |effects: &[lift::Effect]| {
            effects
                .iter()
                .all(|e| matches!(e.kind, lift::EffectKind::Assign(..)))
        };
        match out.effects.last().map(|e| &e.kind) {
            Some(lift::EffectKind::Return(_)) => {
                if !assign_only(&out.effects[..out.effects.len() - 1])
                    || !out.lines.last().is_some_and(|l| is_return(l))
                    || chain.len() >= DUP_CHAIN_MAX
                {
                    return None;
                }
                lines.extend(out.lines.iter().cloned());
                st.tail_clones += 1;
                return Some(lines.join("\n"));
            }
            _ if assign_only(&out.effects) => {
                let &[next] = st.succs[cur].as_slice() else {
                    return None;
                };
                if chain.len() + 1 >= DUP_CHAIN_MAX || next == t || chain.contains(&next) {
                    return None;
                }
                lines.extend(out.lines.iter().cloned());
                chain.push(cur);
                cur = next;
            }
            _ => return None,
        }
    }
}

/// Largest loop-exit region written inline in front of its `break`.
pub(super) const ABSORB_MAX_BLOCKS: usize = 8;

/// Emits a jump-table dispatch the structurer could not turn into a `switch` with arms.
///
/// The same `switch`, every case a `goto`, so control transfer stays explicit
/// and every arm keeps its label.
///
/// # Arguments
///
/// * `ctx` - Per-function state (the jump tables).
/// * `st` - Emission state.
/// * `i` - The dispatch block.
/// * `idx_expr` - The switch index expression.
/// * `out` - Receives the text.
pub(super) fn goto_switch<L: Lifter>(
    ctx: &Ctx<'_>,
    st: &Emit<'_, L>,
    i: usize,
    idx_expr: &Expr,
    out: &mut String,
) {
    let block = &st.blocks[i];
    let Some((_, targets)) = ctx
        .analysis
        .jump_tables
        .range(block.start..block.end)
        .next()
    else {
        return;
    };
    let names = ctx.names();
    let idx = match idx_expr {
        Expr::Sext(e, _) => e.as_ref(),
        other => other,
    };
    let _ = writeln!(out, "switch ({}) {{", idx.render(&names));
    for (t, ns) in table_arms(targets) {
        let _ = writeln!(out, "{} {}", case_labels(&ns).join(" "), jump_to(st, t));
    }
    out.push_str("}\n");
}

/// Computes the single-entry region hanging off `start`, entered from any
/// of `headers` (one branch's block, or a loop's blocks for the blocks it
/// exits to).
///
/// Every block reachable from `start` without passing through a header,
/// the `stop_at` block, or the emission bound, and entered only from the
/// headers or from inside the region (compilers place an arm's tail after
/// the join, so members need not be contiguous). A shared small block
/// reached from any number of members is duplicated into the region
/// instead of counted as an exit when it is terminal, heads a short
/// one-way chain into a terminal block (copied whole at every jump), or
/// leads one way into blocks that are already exits (the default arm two
/// halves of a compare ladder share before their common tail); the block
/// that ends the region (the other arm's start) is copied only in that
/// last form, never as a return the region reaches anyway, and only when
/// the branch asks for it after structuring failed without.
///
/// The arm may be nothing but a shared small block: a `return`, a short
/// chain of one-way blocks ending in one (`rax = -1;` before a shared
/// `return rax;`; a call ends the chain, since a copied call is a copied
/// side effect, unless the branch structures no other way and asks for
/// call copies), copied whole with no exit, or one that leads one way, a
/// private copy whose exits are its successors.
/// Otherwise the region is everything `start` reaches without leaving
/// through a header, the stop block, the bound or written text; blocks
/// entered from outside (and what only they reached) are shed until the rest
/// is entered only from the headers or from inside, so loops entered through
/// `start` stay whole. The order is reverse post-order from the start, so a
/// block follows its predecessors and straight-line chains need no gotos.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `start` - The region's first block.
/// * `headers` - Blocks allowed to enter the region from outside.
/// * `stop_at` - A block that ends the region.
pub(super) fn closed_run_from<L: Lifter>(
    st: &Emit<'_, L>,
    start: usize,
    headers: &BTreeSet<usize>,
    stop_at: Option<usize>,
) -> Region {
    closed_run_with(st, start, headers, stop_at, None)
}

/// What a region's start reaches before any shared tail is copied in: the
/// part of [`closed_run_from`] that depends on the graph alone.
///
/// A header's two arms are asked for by the `while` test and again by
/// every `if` attempt, between which only the copy rules change, so
/// [`emit_block`] computes each arm's base once and hands it to every ask.
pub(super) struct Base {
    /// The region's blocks, ascending.
    members: Vec<usize>,
    /// Every member is entered only from the headers or from inside.
    closed: bool,
}

/// Computes the base of the region `start` heads ([`Base`]).
///
/// Everything `start` reaches without leaving through a header, the stop
/// block, the bound or written text; blocks entered from outside (and what
/// only they reached) are shed until the rest is entered only from the
/// headers or from inside.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `start` - The region's first block.
/// * `headers` - Blocks allowed to enter the region from outside.
/// * `stop_at` - A block that ends the region.
pub(super) fn base_of<L: Lifter>(
    st: &Emit<'_, L>,
    start: usize,
    headers: &BTreeSet<usize>,
    stop_at: Option<usize>,
) -> Base {
    let n = st.blocks.len();
    let inside = |reached: &[bool], s: usize| -> bool {
        st.preds[s]
            .iter()
            .all(|p| headers.contains(p) || reached[*p])
    };
    let allowed =
        |s: usize| !headers.contains(&s) && Some(s) != stop_at && !st.outside(s) && !st.emitted[s];
    let mut reached = vec![false; n];
    let mut kept = vec![false; n];
    let mut members: Vec<usize> = Vec::new();
    let mut kept_members: Vec<usize> = Vec::new();
    let mut work: Vec<usize> = Vec::new();
    let reach = |within: &dyn Fn(usize) -> bool,
                 reached: &mut [bool],
                 members: &mut Vec<usize>,
                 work: &mut Vec<usize>| {
        reached[start] = true;
        members.push(start);
        work.push(start);
        while let Some(b) = work.pop() {
            for &s in &st.succs[b] {
                if s != start && within(s) && !reached[s] {
                    reached[s] = true;
                    members.push(s);
                    work.push(s);
                }
            }
        }
    };
    reach(&allowed, &mut reached, &mut members, &mut work);
    loop {
        let shed: Vec<usize> = members
            .iter()
            .copied()
            .filter(|&b| b != start && !inside(&reached, b))
            .collect();
        if shed.is_empty() {
            break;
        }
        for m in kept_members.drain(..) {
            kept[m] = false;
        }
        for &b in &shed {
            reached[b] = false;
        }
        std::mem::swap(&mut reached, &mut kept);
        kept_members.extend(members.iter().copied().filter(|&m| kept[m]));
        members.clear();
        reach(&|s| kept[s], &mut reached, &mut members, &mut work);
    }
    members.sort_unstable();
    let closed = members.iter().all(|&b| inside(&reached, b));
    Base { members, closed }
}

/// [`closed_run_from`] with the region's base computed already, or
/// computed here when `base` is `None`.
///
/// PERF: the region and the blocks its walk has seen are bitmaps over the
/// function's blocks: it is asked for twice per attempt at every branch,
/// and as tree sets they made a big function's structuring quadratic in
/// set operations.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `start` - The region's first block.
/// * `headers` - Blocks allowed to enter the region from outside.
/// * `stop_at` - A block that ends the region.
/// * `base` - The base of this very region ([`base_of`] with the same
///   arguments under the same graph), when the caller has it.
pub(super) fn closed_run_with<L: Lifter>(
    st: &Emit<'_, L>,
    start: usize,
    headers: &BTreeSet<usize>,
    stop_at: Option<usize>,
    base: Option<&Base>,
) -> Region {
    let small = |b: usize| L::body_len(&st.code[b]) <= DUP_MAX_INSTRS;
    let one_way = |b: usize| {
        st.succs[b].len() == 1
            && st.succs[b].first() != Some(&b)
            && small(b)
            && !st.no_dup.contains(&b)
    };
    let chain = |b: usize| -> Option<Vec<usize>> {
        let mut order = vec![b];
        let mut instrs = L::body_len(&st.code[b]);
        let mut cur = b;
        while let Some(&next) = st.succs[cur].first() {
            if !one_way(cur)
                || (!st.copy_calls && st.blocks[cur].term == BlockTerm::Call)
                || order.len() >= DUP_CHAIN_MAX
                || headers.contains(&next)
                || Some(next) == stop_at
                || order.contains(&next)
            {
                return None;
            }
            instrs += L::body_len(&st.code[next]);
            if instrs > DUP_MAX_INSTRS {
                return None;
            }
            order.push(next);
            cur = next;
        }
        (st.succs[cur].is_empty() && small(cur)).then_some(order)
    };
    let shared = st.preds[start].iter().any(|p| !headers.contains(p));
    if shared && let Some(order) = chain(start) {
        return Region {
            exits: BTreeSet::new(),
            closed: true,
            dups: order.iter().copied().collect(),
            order,
        };
    }
    if shared && one_way(start) {
        return Region {
            order: vec![start],
            exits: st.succs[start].iter().copied().collect(),
            closed: true,
            dups: [start].into_iter().collect(),
        };
    }
    let own;
    let base = match base {
        Some(b) => b,
        None => {
            own = base_of(st, start, headers, stop_at);
            &own
        }
    };
    let closed = base.closed;
    let mut in_region = vec![false; st.blocks.len()];
    let mut region: Vec<usize> = base.members.clone();
    for &b in &region {
        mark(&mut in_region, b);
    }
    let mut exits: BTreeSet<usize> = region
        .iter()
        .flat_map(|b| st.succs[*b].iter().copied())
        .filter(|&s| !is_marked(&in_region, s))
        .collect();
    let mut dups: BTreeSet<usize> = BTreeSet::new();
    loop {
        let more: Vec<Vec<usize>> = exits
            .iter()
            .copied()
            .filter(|&s| !headers.contains(&s))
            .filter_map(|s| {
                let leads_to_exits = one_way(s) && st.succs[s].iter().all(|t| exits.contains(t));
                if Some(s) == stop_at {
                    return (st.copy_stop && leads_to_exits).then(|| vec![s]);
                }
                chain(s).or_else(|| leads_to_exits.then(|| vec![s]))
            })
            .collect();
        if more.is_empty() {
            break;
        }
        for s in more.into_iter().flatten() {
            dups.insert(s);
            if mark(&mut in_region, s) {
                region.push(s);
            }
            exits.remove(&s);
        }
    }
    region.sort_unstable();
    Region {
        order: region_order(&st.succs, start, &in_region, &region),
        exits,
        closed,
        dups,
    }
}

/// Tells whether a block is set in a bitmap over the function's blocks.
///
/// # Arguments
///
/// * `set` - The bitmap.
/// * `b` - Block index.
fn is_marked(set: &[bool], b: usize) -> bool {
    set.get(b).copied().unwrap_or(false)
}

/// Sets a block in a bitmap over the function's blocks.
///
/// # Arguments
///
/// * `set` - The bitmap.
/// * `b` - Block index.
///
/// # Returns
///
/// Whether it was not set before.
fn mark(set: &mut [bool], b: usize) -> bool {
    set.get_mut(b).is_some_and(|x| !std::mem::replace(x, true))
}

/// Returns the order a region's blocks are written in: reverse postorder
/// from its start over the edges inside it, then the blocks that walk
/// never reaches, ascending.
///
/// # Arguments
///
/// * `succs` - Successor block indices per block.
/// * `start` - The region's first block.
/// * `in_region` - The region, as a bitmap over the blocks.
/// * `region` - The region's blocks, ascending.
fn region_order(
    succs: &[Vec<usize>],
    start: usize,
    in_region: &[bool],
    region: &[usize],
) -> Vec<usize> {
    let mut order: Vec<usize> = Vec::with_capacity(region.len());
    let mut seen = vec![false; in_region.len()];
    let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
    mark(&mut seen, start);
    while let Some((b, next_child)) = stack.pop() {
        let child = succs[b]
            .iter()
            .copied()
            .filter(|&s| is_marked(in_region, s))
            .nth(next_child);
        if let Some(c) = child {
            stack.push((b, next_child + 1));
            if mark(&mut seen, c) {
                stack.push((c, 0));
            }
        } else {
            order.push(b);
        }
    }
    order.reverse();
    order.extend(region.iter().copied().filter(|&b| !is_marked(&seen, b)));
    order
}

/// Renders a jump to `va` as a statement.
///
/// A label is written only for a block of the function being emitted, so a
/// target outside it (a branch into another function, into data, or past the
/// range the unwind tables give this one) becomes a computed goto, the same
/// form an unresolved indirect jump takes.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `va` - The jump target.
///
/// # Returns
///
/// `goto L_<va>;` when a block starts there, else `goto *<va>;`.
pub(super) fn jump_to<L: Lifter>(st: &Emit<'_, L>, va: u64) -> String {
    match st.index_of(va) {
        Some(i) => goto(st.start(i)),
        None => format!("goto *{va:#x};"),
    }
}

/// Deepest expression [`fold_static`] evaluates.
pub(super) const FOLD_DEPTH: u8 = 16;

/// The value an expression has when it is built only from constants and
/// reads of the image's read-only memory.
///
/// A jump-table jump with its index fixed is such an expression
/// (`*(uint32_t*)(base + 5 * 4 + rva) + base`), and its value is where the
/// jump lands. A read of writable memory, a register or anything else
/// unknown leaves the expression unfolded.
///
/// # Arguments
///
/// * `program` - The image the reads come from.
/// * `e` - The expression.
/// * `depth` - How much deeper to look.
pub(super) fn fold_static(program: &Program, e: &Expr, depth: u8) -> Option<u64> {
    let d = depth.checked_sub(1)?;
    match e {
        Expr::Const(v) => Some(*v),
        Expr::Bin(op, a, b) => {
            let (a, b) = (fold_static(program, a, d)?, fold_static(program, b, d)?);
            match op {
                expr::Op::Add => Some(a.wrapping_add(b)),
                expr::Op::Sub => Some(a.wrapping_sub(b)),
                expr::Op::Mul => Some(a.wrapping_mul(b)),
                expr::Op::Shl => a.checked_shl(u32::try_from(b).ok()?),
                expr::Op::And => Some(a & b),
                expr::Op::Or => Some(a | b),
                _ => None,
            }
        }
        Expr::Sext(inner, bits) => {
            let v = fold_static(program, inner, d)?;
            let shift = 64u32.checked_sub(u32::from(*bits)).filter(|s| *s < 64)?;
            Some((v.checked_shl(shift)?.cast_signed() >> shift).cast_unsigned())
        }
        Expr::Cast(inner, ty) if !matches!(ty, Ty::F32 | Ty::F64) => {
            let v = fold_static(program, inner, d)?;
            Some(match ty.bits() {
                8 => v & 0xff,
                16 => v & 0xffff,
                32 => v & 0xffff_ffff,
                _ => v,
            })
        }
        Expr::Deref(addr, ty) => {
            let at = fold_static(program, addr, d)?;
            let section = program
                .sections
                .iter()
                .find(|s| at >= s.va.0 && at < s.va.0.saturating_add(s.vsize))?;
            if section.writable {
                return None;
            }
            let n = usize::from(ty.bits() / 8);
            if n == 0 || n > 8 {
                return None;
            }
            let raw = program.read_va(at, n)?;
            let mut buf = [0u8; 8];
            for (dst, src) in buf.iter_mut().zip(raw) {
                *dst = *src;
            }
            Some(u64::from_le_bytes(buf))
        }
        _ => None,
    }
}

/// The value a switch index folded to, when it is a constant.
///
/// # Arguments
///
/// * `e` - The index expression.
pub(super) fn const_index(e: &Expr) -> Option<u64> {
    match e {
        Expr::Const(k) => Some(*k),
        Expr::Sext(inner, _) => const_index(inner),
        Expr::Cast(inner, _) => const_index(inner),
        _ => None,
    }
}

/// Where the jump table ending a block sends an index.
///
/// # Arguments
///
/// * `analysis` - The resolved jump tables.
/// * `block` - The block ending in the table's jump.
/// * `k` - The index.
pub(super) fn table_target(analysis: &Analysis, block: &BasicBlock, k: u64) -> Option<u64> {
    let (_, targets) = analysis.jump_tables.range(block.start..block.end).next()?;
    targets.get(usize::try_from(k).ok()?).copied()
}
