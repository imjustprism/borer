//! Structuring: guards, regions, gotos and switches recovered from the block
//! graph.

use super::*;

/// Emission state of the structurer for one function.
pub(super) struct Emit<'e, L: Lifter> {
    /// The function's basic blocks in address order.
    pub(super) blocks: &'e [BasicBlock],
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
    /// Whether the block that ends a region (the other arm's start) may be
    /// copied into it when it leads one way into the region's exits. Off by
    /// default (the arm would rather fall into it); a branch that structures
    /// no other way turns it on for a second attempt.
    pub(super) copy_stop: bool,
    /// Blocks each enclosing structure copies privately, innermost last; an
    /// inner structure may copy them too, since the enclosing one owns every
    /// predecessor and writes no original.
    pub(super) dup_stack: Vec<BTreeSet<usize>>,
    /// The block the function is entered at: an entry of any loop it is
    /// in, whatever its predecessors.
    pub(super) entry: usize,
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
        self.blocks.iter().position(|b| b.start == va)
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
pub(super) enum Guard {
    /// One block's condition.
    One(expr::Cond),
    /// Either side holds.
    Or(Box<Guard>, Box<Guard>),
    /// Both sides hold.
    And(Box<Guard>, Box<Guard>),
}

impl Guard {
    /// Returns the negated guard (De Morgan), for merging a chain whose own
    /// target is the outer guard's fall-through side.
    pub(super) fn invert(self) -> Guard {
        match self {
            Guard::One(c) => Guard::One(c.invert()),
            Guard::Or(a, b) => Guard::And(Box::new(a.invert()), Box::new(b.invert())),
            Guard::And(a, b) => Guard::Or(Box::new(a.invert()), Box::new(b.invert())),
        }
    }

    /// Renders the guard as a C boolean expression.
    ///
    /// De Morgan keeps the inverted form readable (`!(a || b)` renders as
    /// `!a && !b`); compound operands are parenthesized.
    ///
    /// # Arguments
    ///
    /// * `n` - Name resolution.
    /// * `side` - The side the arm is on; the fall-through side renders
    ///   the negation.
    pub(super) fn render(&self, n: &Names<'_>, side: Side) -> String {
        let part = |g: &Guard| -> String {
            let text = g.render(n, side);
            if matches!(g, Guard::One(_)) {
                text
            } else {
                format!("({text})")
            }
        };
        match (self, side) {
            (Guard::One(c), _) => c.render(n, side == Side::Fall),
            (Guard::Or(a, b), Side::Fall) | (Guard::And(a, b), Side::Target) => {
                format!("{} && {}", part(a), part(b))
            }
            (Guard::Or(a, b), Side::Target) | (Guard::And(a, b), Side::Fall) => {
                format!("{} || {}", part(a), part(b))
            }
        }
    }
}

/// Recognizes a block that only decides, so its condition can fold into the
/// predecessor's guard.
///
/// Lazy register and slot copies the block leaves in the environment are
/// consistent whoever prints the decision (every successor's entry state
/// came from the dataflow); only statements and frame changes are not.
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
/// The condition and its `(target, fall)` block indices, or `None` when the
/// block is not a conditional entered only from `from`, has statements, a
/// switch dispatch, changes the stack pointer, or has a constant condition
/// (its dead edge was pruned, so it is a plain jump, not a guard term).
pub(super) fn pure_condition<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    from: usize,
    b: usize,
) -> Option<(expr::Cond, usize, usize)> {
    if b == from
        || st.outside(b)
        || st.emitted[b]
        || st.preds[b].as_slice() != [from]
        || st.blocks[b].term != BlockTerm::Cond
    {
        return None;
    }
    let (out, env) = run_block_env(ctx, st, b);
    let br = out.branch?;
    if !out.lines.is_empty()
        || out.switch_idx.is_some()
        || env.sp != st.in_envs[b].sp
        || br.cond.eval().is_some()
    {
        return None;
    }
    let t = st.index_of(br.target)?;
    let f = st.index_of(br.fall)?;
    Some((br.cond, t, f))
}

/// Merges the pure condition blocks hanging off `i`'s branch into one guard.
///
/// Merged blocks are consumed and their successors re-parented to `i`.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - The header block.
/// * `cond` - Its own condition.
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
    cond: expr::Cond,
    t: usize,
    f: usize,
) -> (Guard, usize, usize) {
    let mut journal = Journal::default();
    merge_chain(ctx, st, i, Guard::One(cond), t, f, 0, &mut journal)
}

/// Deepest chain of pure condition blocks merged into one guard.
pub(super) const MAX_GUARD_DEPTH: usize = 3;

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
/// * `cond` - Its condition.
/// * `t` - Its branch target block.
/// * `f` - Its fall-through block.
/// * `depth` - Current nesting; [`MAX_GUARD_DEPTH`] stops the recursion.
/// * `journal` - Where the merge records what it changes.
#[expect(clippy::too_many_arguments, reason = "the structurer's shape")]
pub(super) fn sub_chain<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    block: usize,
    cond: expr::Cond,
    t: usize,
    f: usize,
    depth: usize,
    journal: &mut Journal,
) -> (Guard, usize, usize) {
    if depth + 1 >= MAX_GUARD_DEPTH {
        return (Guard::One(cond), t, f);
    }
    merge_chain(ctx, st, block, Guard::One(cond), t, f, depth + 1, journal)
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
        if let Some((c2, t2, f2)) = pure_condition(ctx, st, header, f) {
            let consumed = f;
            let mark = journal.mark();
            let t2 = follow_trampoline(ctx, st, consumed, t2, journal);
            let f2 = follow_trampoline(ctx, st, consumed, f2, journal);
            let (g2, t2, f2) = sub_chain(ctx, st, consumed, c2, t2, f2, depth, journal);
            let (g, nt, nf) = if t2 == t {
                (Guard::Or(Box::new(guard), Box::new(g2)), t, f2)
            } else if f2 == t {
                (Guard::Or(Box::new(guard), Box::new(g2.invert())), t, t2)
            } else {
                journal.restore(st, mark);
                return (guard, t, f);
            };
            consume(st, header, consumed, journal);
            guard = g;
            t = nt;
            f = nf;
            continue;
        }
        if let Some((c2, t2, f2)) = pure_condition(ctx, st, header, t) {
            let consumed = t;
            let mark = journal.mark();
            let t2 = follow_trampoline(ctx, st, consumed, t2, journal);
            let f2 = follow_trampoline(ctx, st, consumed, f2, journal);
            let (g2, t2, f2) = sub_chain(ctx, st, consumed, c2, t2, f2, depth, journal);
            let (g, nt, nf) = if f2 == f {
                (Guard::And(Box::new(guard), Box::new(g2)), t2, f)
            } else if t2 == f {
                (Guard::And(Box::new(guard), Box::new(g2.invert())), f2, f)
            } else {
                journal.restore(st, mark);
                return (guard, t, f);
            };
            consume(st, header, consumed, journal);
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

/// Longest chain of one-way blocks ending in a terminal block copied whole.
pub(super) const DUP_CHAIN_MAX: usize = 3;

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
    /// Per block, whether it is in the region.
    reached: Vec<bool>,
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
    let reach = |within: &dyn Fn(usize) -> bool| -> Vec<bool> {
        let mut seen = vec![false; n];
        seen[start] = true;
        let mut work = vec![start];
        while let Some(b) = work.pop() {
            for &s in &st.succs[b] {
                if s != start && within(s) && !seen[s] {
                    seen[s] = true;
                    work.push(s);
                }
            }
        }
        seen
    };
    let mut reached = reach(&allowed);
    loop {
        let shed: Vec<usize> = (0..n)
            .filter(|&b| reached[b] && b != start && !inside(&reached, b))
            .collect();
        if shed.is_empty() {
            break;
        }
        let mut kept = reached;
        for b in shed {
            kept[b] = false;
        }
        reached = reach(&|s| kept[s]);
    }
    let closed = (0..n).all(|b| !reached[b] || inside(&reached, b));
    Base { reached, closed }
}

/// [`closed_run_from`] with the region's base computed already, or
/// computed here when `base` is `None`.
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
    let mut region: BTreeSet<usize> = (0..st.blocks.len()).filter(|&b| base.reached[b]).collect();
    let mut exits: BTreeSet<usize> = region
        .iter()
        .flat_map(|b| st.succs[*b].iter().copied())
        .filter(|s| !region.contains(s))
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
            region.insert(s);
            exits.remove(&s);
        }
    }
    let mut order: Vec<usize> = Vec::with_capacity(region.len());
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
    seen.insert(start);
    while let Some((b, next_child)) = stack.pop() {
        let children: Vec<usize> = st.succs[b]
            .iter()
            .copied()
            .filter(|s| region.contains(s))
            .collect();
        if let Some(&c) = children.get(next_child) {
            stack.push((b, next_child + 1));
            if seen.insert(c) {
                stack.push((c, 0));
            }
        } else {
            order.push(b);
        }
    }
    order.reverse();
    for b in &region {
        if !seen.contains(b) {
            order.push(*b);
        }
    }
    Region {
        order,
        exits,
        closed,
        dups,
    }
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
    if st.index_of(va).is_some() {
        goto(va)
    } else {
        format!("goto *{va:#x};")
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
            let wide = i64::from_ne_bytes(v.checked_shl(shift)?.to_ne_bytes()) >> shift;
            Some(u64::from_ne_bytes(wide.to_ne_bytes()))
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
                .find(|s| at >= s.va && at < s.va.saturating_add(s.vsize))?;
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
