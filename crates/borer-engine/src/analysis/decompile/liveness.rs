//! Dataflow: liveness, phi placement at joins, and flags carried across blocks.

use super::*;

/// Tells whether two stack accesses overlap.
///
/// # Arguments
///
/// * `a` - Offset of the first access.
/// * `a_bits` - Its width in bits (at least one byte).
/// * `b` - Offset of the second access.
/// * `b_bits` - Its width in bits.
pub(super) fn overlaps(a: i64, a_bits: u8, b: i64, b_bits: u8) -> bool {
    let a_end = a + i64::from(a_bits / 8).max(1);
    let b_end = b + i64::from(b_bits / 8).max(1);
    a < b_end && b < a_end
}

/// Per-block liveness: registers syntactically, slots from the recorded
/// accesses of a first dataflow round.
pub(super) struct Live {
    /// Registers live at each block's entry, with the lane width needed.
    pub(super) regs: Vec<FxHashMap<Key, u8>>,
    /// Per block and instruction, the registers read later ([`lift::need_after`]).
    pub(super) need: Vec<Vec<FxHashMap<Key, u8>>>,
    /// Slots live at each block's entry; `None` treats every slot as live.
    pub(super) slots: Option<Vec<BTreeSet<i64>>>,
}

impl Live {
    /// Tells whether variable `k` is live at the entry of block `b`.
    ///
    /// # Arguments
    ///
    /// * `b` - Block index.
    /// * `k` - The variable; globals and temporaries are never live, and an
    ///   x87 register always is, since the next push or pop moves it.
    pub(super) fn is_live(&self, b: usize, k: Key) -> bool {
        match k {
            Key::Reg(_) => k.is_x87() || self.regs[b].contains_key(&k),
            Key::A64(_) => self.regs[b].contains_key(&k),
            Key::Slot(o) => self.slots.as_ref().is_none_or(|s| s[b].contains(&o)),
            Key::Global(..) | Key::Tmp(_) | Key::Param(_) => false,
        }
    }
}

/// Slot accesses of one block as recorded by the lifter.
#[derive(Debug, Default, Clone)]
pub(super) struct SlotRec {
    /// Slot offsets read before being written in the block.
    pub(super) uses: BTreeSet<i64>,
    /// Slot offsets written in the block.
    pub(super) defs: BTreeSet<i64>,
    /// The widest read in bits at each offset in `uses`.
    pub(super) reads: BTreeMap<i64, u8>,
    /// The widest store in bits at each offset in `defs`.
    pub(super) stores: BTreeMap<i64, u8>,
    /// Slots each call may read, with the slots written before that call:
    /// as the lifter records them, the frame bytes written; once widened
    /// ([`widen_slots`]), the slots those bytes cover whole.
    pub(super) calls: Vec<(SlotUse, BTreeSet<i64>)>,
    /// `(taken, target, fall)` when the block's branch folded to a constant.
    pub(super) branch_const: Option<(bool, u64, u64)>,
    /// The index the block's jump table is read at, when it folded to a
    /// constant.
    pub(super) switch_const: Option<u64>,
    /// Where the block's jump-table jump lands, when its target folds to
    /// an address (the index fixed, the table read from the image).
    pub(super) switch_dest: Option<u64>,
    /// The conditional branch ending the block, for edge assumptions.
    pub(super) branch: Option<Branch>,
    /// The `cmp`/`test` whose flags the block leaves to its successors.
    pub(super) flag_src: Option<Instruction>,
}

/// Returns what an equality branch establishes on the edge to `succ`.
///
/// `if (k == c)` makes `k` equal to `c` on its taken edge, `if (k != c)` on
/// its fall-through edge; `test k, k` compares with zero. Other conditions
/// establish nothing usable.
///
/// # Arguments
///
/// * `branch` - The branch ending the predecessor.
/// * `succ` - Start address of the successor being entered.
///
/// # Returns
///
/// `(variable, constant)` to assume, or `None`.
pub(super) fn assumption(branch: &Branch, succ: u64) -> Option<(Key, u64)> {
    if branch.target == branch.fall || (succ != branch.target && succ != branch.fall) {
        return None;
    }
    let on_taken = succ == branch.target;
    let equal_edge = match branch.cond.cc.0 {
        ConditionCode::e => on_taken,
        ConditionCode::ne => !on_taken,
        _ => return None,
    };
    if !equal_edge {
        return None;
    }
    let cond = branch
        .cond
        .simplify()
        .unwrap_or_else(|| branch.cond.clone());
    match &cond.flags {
        Flags::Cmp(Expr::Var(k), Expr::Const(c), _) => Some((*k, *c)),
        Flags::Test(Expr::Var(k), Expr::Var(k2), _) if k == k2 => Some((*k, 0)),
        _ => None,
    }
}

/// Computes the assumption each block may use while it executes.
///
/// A block entered from exactly one predecessor through an equality branch
/// knows the compared variable's value ([`assumption`]). The fact is applied
/// when values are read inside the block, never stored in the environment:
/// stored, it would look like a value to write out at the next join.
///
/// # Arguments
///
/// * `code` - Decoded instructions per block (the first gives the start address).
/// * `preds` - Predecessor block indices per block.
/// * `recorded` - The previous dataflow round's block records (their branches).
pub(super) fn block_assumptions<L: Lifter>(
    code: &[Vec<L::Insn>],
    preds: &[Vec<usize>],
    recorded: &[SlotRec],
) -> Vec<Option<(Key, u64)>> {
    (0..code.len())
        .map(|b| {
            let [p] = preds[b].as_slice() else {
                return None;
            };
            let start = L::start(code[b].first()?);
            assumption(recorded[*p].branch.as_ref()?, start)
        })
        .collect()
}

/// Widens each block's slot uses and definitions from offsets to the bytes
/// they span.
///
/// Slot liveness is by offset, and an access at one offset reaches what an
/// access at another left wherever their bytes overlap. A read takes in
/// every slot whose bytes it overlaps (`movzx eax, byte [rsp+0xb]` reads
/// what `mov dword [rsp+8], 0` stored): judged by its own offset alone, the
/// store would be dead, dropped at an edge, and the read would see bytes
/// the text never wrote. A store defines every slot whose bytes it covers
/// whole (`mov dword [rsp+8], edx` leaves nothing of an earlier byte at
/// `[rsp+0xb]`), and no slot it covers only in part (`mov word [rsp+8], ax`
/// leaves the dword at `[rsp+8]` half what it was); a call reads the slots
/// its window reaches into, from below its start too, but those the
/// block's stores before it cover whole. A slot spans the widest access to
/// it anywhere in the function.
///
/// # Arguments
///
/// * `recorded` - Per-block slot accesses, widened in place.
pub(super) fn widen_slots(recorded: &mut [SlotRec]) {
    let bytes = |b: u8| i64::from(b / 8).max(1);
    let mut span: BTreeMap<i64, i64> = BTreeMap::new();
    for (&o, &b) in recorded
        .iter()
        .flat_map(|r| r.reads.iter().chain(&r.stores))
    {
        let n = span.entry(o).or_default();
        *n = (*n).max(bytes(b));
    }
    let near = |o: i64, n: i64| {
        span.range(o.saturating_sub(lift::SLOT_BYTES_MAX - 1)..o.saturating_add(n))
    };
    for r in recorded.iter_mut() {
        let read: Vec<i64> = r
            .reads
            .iter()
            .flat_map(|(&u, &b)| {
                near(u, bytes(b))
                    .filter(move |&(&o, &len)| o.saturating_add(len) > u)
                    .map(|(&o, _)| o)
            })
            .collect();
        let written: Vec<i64> = r
            .stores
            .iter()
            .flat_map(|(&d, &b)| {
                let end = d.saturating_add(bytes(b));
                near(d, bytes(b))
                    .filter(move |&(&o, &len)| o >= d && o.saturating_add(len) <= end)
                    .map(|(&o, _)| o)
            })
            .collect();
        r.uses.extend(read);
        r.defs = written.into_iter().collect();
        for (seen, before) in &mut r.calls {
            let covered: BTreeSet<i64> = span
                .iter()
                .filter(|&(&o, &len)| (o..o.saturating_add(len)).all(|x| before.contains(&x)))
                .map(|(&o, _)| o)
                .collect();
            if let SlotUse::Window(lo, _) = *seen {
                r.uses.extend(
                    near(lo, 0)
                        .filter(|&(&o, &len)| o.saturating_add(len) > lo && !covered.contains(&o))
                        .map(|(&o, _)| o),
                );
            }
            *before = covered;
        }
    }
}

/// Computes backward liveness over slot offsets.
///
/// A call reads whatever a callee may see (the argument window, or
/// everything once an address escaped), minus what the block already wrote
/// before the call.
///
/// PERF: the sets are bit vectors over the offsets the blocks touch, one
/// word per 64 of them, so a sweep over a function of a thousand blocks
/// ORs words instead of merging trees; the fixpoint is the least one
/// above the uses, the same whatever order reaches it.
///
/// # Arguments
///
/// * `recorded` - Per-block slot accesses from a dataflow round.
/// * `succs` - Successor block indices per block.
///
/// # Returns
///
/// For every block, the slots live at its entry.
pub(super) fn slot_liveness(recorded: &[SlotRec], succs: &[Vec<usize>]) -> Vec<BTreeSet<i64>> {
    let universe: Vec<i64> = recorded
        .iter()
        .flat_map(|r| r.uses.iter().chain(r.defs.iter()).copied())
        .collect::<BTreeSet<i64>>()
        .into_iter()
        .collect();
    let words = universe.len().div_ceil(64);
    let bits_of = |set: &mut [u64], offs: &mut dyn Iterator<Item = i64>| {
        for o in offs {
            if let Ok(i) = universe.binary_search(&o) {
                set[i / 64] |= 1 << (i % 64);
            }
        }
    };
    let mut uses = vec![0u64; recorded.len() * words];
    let mut defs = vec![0u64; recorded.len() * words];
    for ((r, u), d) in recorded
        .iter()
        .zip(uses.chunks_mut(words.max(1)))
        .zip(defs.chunks_mut(words.max(1)))
    {
        bits_of(u, &mut r.uses.iter().copied());
        bits_of(d, &mut r.defs.iter().copied());
        for (cu, defs_before) in &r.calls {
            let seen = match cu {
                SlotUse::All => &universe[..],
                SlotUse::Window(lo, hi) => {
                    &universe
                        [universe.partition_point(|o| o < lo)..universe.partition_point(|o| o < hi)]
                }
            };
            bits_of(
                u,
                &mut seen.iter().copied().filter(|o| !defs_before.contains(o)),
            );
        }
    }
    let mut live = uses.clone();
    let mut out = vec![0u64; words];
    loop {
        let mut changed = false;
        for b in (0..recorded.len()).rev() {
            out.fill(0);
            for &s in &succs[b] {
                for (o, l) in out.iter_mut().zip(&live[s * words..(s + 1) * words]) {
                    *o |= l;
                }
            }
            for (w, o) in out.iter().enumerate() {
                let at = b * words + w;
                let inn = uses[at] | (o & !defs[at]);
                if inn != live[at] {
                    live[at] = inn;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    (0..recorded.len())
        .map(|b| {
            universe
                .iter()
                .enumerate()
                .filter(|(i, _)| live[b * words + i / 64] & (1 << (i % 64)) != 0)
                .map(|(_, o)| *o)
                .collect()
        })
        .collect()
}

/// The facts the lifter needs about block `b` before it runs it: who reads
/// its flags, what it may assume, what follows a block-ending call, and
/// where it stands in the prologue.
///
/// # Arguments
///
/// * `ctx` - Per-function state (flag readers, the frame, the rebases).
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `need` - Per block and instruction, the registers read later.
/// * `assumes` - Per block, the equality fact it may read under.
/// * `b` - The block.
pub(super) fn block_facts<'n, L: Lifter>(
    ctx: &Ctx<'_>,
    code: &[Vec<L::Insn>],
    succs: &[Vec<usize>],
    need: &'n [Vec<FxHashMap<Key, u8>>],
    assumes: &[Option<(Key, u64)>],
    b: usize,
) -> BlockFacts<'n> {
    BlockFacts {
        need: Some(&need[b]),
        flags_out: succs[b].iter().any(|&s| ctx.flag_readers[s]),
        assume: assumes.get(b).copied().flatten(),
        after: succs[b].first().and_then(|&s| L::after(code, s)),
        entry: L::prologue_block(ctx, code, b),
        unregistered: ctx.seh_frame && b == ctx.entry_block,
        rebase_flags: ctx.rebase_flags.get(b).copied().flatten(),
    }
}

/// Lists the values a block must write out at its end.
///
/// These are the entries of its OUT environment that some successor does
/// not carry (the meet lost them) and still reads. Successors not yet
/// processed by the dataflow are optimistic (they agree).
///
/// # Arguments
///
/// * `out` - The block's OUT environment.
/// * `succs` - Its successor block indices.
/// * `ins` - IN environments per block.
/// * `live` - Liveness oracle.
/// * `processed` - Which blocks the dataflow has run at least once.
/// * `current` - Overrides one successor's IN with the meet being computed.
pub(super) fn phi_keys(
    out: &Env,
    succs: &[usize],
    ins: &[Env],
    live: &Live,
    processed: &[bool],
    current: Option<(usize, &Env)>,
) -> Vec<Key> {
    out.vals
        .iter()
        .filter(|(k, v)| {
            succs.iter().any(|&s| {
                let succ_in = match current {
                    Some((b, m)) if b == s => Some(m),
                    _ if processed[s] => Some(&ins[s]),
                    _ => None,
                };
                let Some(succ_in) = succ_in else { return false };
                live.is_live(s, **k) && succ_in.vals.get(k) != Some(v)
            })
        })
        .map(|(k, _)| *k)
        .collect()
}

/// Forgets variable `k` in an environment, including flags that read it.
///
/// # Arguments
///
/// * `env` - The environment.
/// * `k` - The variable.
pub(super) fn drop_key(env: &mut Env, k: Key) {
    env.vals.remove(&k);
    if let Key::Slot(o) = k {
        env.slot_bits.remove(&o);
    }
    if env.flags.mentions(k) {
        env.flags = Flags::Unknown;
    }
}

/// Folds `v = X;` directly followed by `return v;` into `return X;` when
/// `v` is a register, temporary, local or parameter (a global keeps its
/// store).
///
/// # Arguments
///
/// * `lines` - The body lines, edited in place.
///
/// # Returns
///
/// Whether anything changed.
pub(super) fn merge_return_assignments(lines: &mut Vec<String>) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i + 1 < lines.len() {
        let (pad, rest) = lines[i].split_at(indent_of(&lines[i]));
        let merged = rest
            .strip_suffix(';')
            .and_then(|r| r.split_once(" = "))
            .filter(|(v, _)| is_plain_var(v))
            .filter(|(v, _)| {
                // The next line is exactly this assignment returned: said
                // without building the string, the comparison runs per
                // assignment line of every cleanup pass.
                let next = lines[i + 1].as_bytes();
                next.len() == pad.len() + v.len() + 8
                    && next.starts_with(pad.as_bytes())
                    && next[pad.len()..].starts_with(b"return ")
                    && next[pad.len() + 7..pad.len() + 7 + v.len()] == *v.as_bytes()
                    && next[next.len() - 1] == b';'
            })
            .map(|(_, x)| format!("{pad}return {x};"));
        if let Some(m) = merged {
            lines[i] = m;
            lines.remove(i + 1);
            changed = true;
        } else {
            i += 1;
        }
    }
    changed
}

/// Returns the class a declared parameter type points or refers to.
///
/// `Foo *`, `const Foo &` and `Foo &` give `Foo`; a value type or a pointer
/// to a pointer gives `None`.
///
/// # Arguments
///
/// * `ty` - The declared type text.
pub(in crate::analysis) fn pointee_class(ty: &str) -> Option<&str> {
    let core = ty
        .strip_suffix('*')
        .or_else(|| ty.strip_suffix('&'))?
        .trim_end();
    let core = core.strip_prefix("const ").unwrap_or(core).trim();
    if core.is_empty() || core.ends_with('*') || core.ends_with('&') {
        return None;
    }
    Some(core)
}

/// Tells whether a block reads a flag before writing it, that is, depends on
/// flags a predecessor left (`cmp; jae A; ... A: jne B`).
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
pub(super) fn reads_inherited_flags(instrs: &[Instruction]) -> bool {
    let mut written = 0u32;
    for i in instrs {
        if i.rflags_read() & !written != 0 {
            return true;
        }
        written |= i.rflags_modified();
    }
    false
}

/// Finds the condition code the first flag reader of a block tests.
///
/// # Arguments
///
/// * `instrs` - The block.
///
/// # Returns
///
/// The code of the first `jcc`, `setcc` or `cmovcc` that reads flags the
/// block inherited, the carry (`b`) for `adc`/`sbb`/`rcl`/`rcr`, or `None`
/// when the block does not read them or reads them in another way (`lahf`).
pub(super) fn join_reader_cc(instrs: &[Instruction]) -> Option<Cc> {
    let mut written = 0u32;
    for i in instrs {
        if i.rflags_read() & !written != 0 {
            let cc = match i.mnemonic() {
                Mnemonic::Adc | Mnemonic::Sbb | Mnemonic::Rcl | Mnemonic::Rcr => {
                    Cc(ConditionCode::b)
                }
                _ => Cc(i.condition_code()),
            };
            return (cc.0 != ConditionCode::None).then_some(cc);
        }
        written |= i.rflags_modified();
    }
    None
}

/// Decides how a join's predecessors can make their flags agree.
///
/// Every predecessor must leave `cmp`/`test` flags from a comparison of the
/// same mnemonic and width whose immediate operands agree, with no memory
/// operand. When all of them name the same registers the answer is
/// [`Rebase::Registers`]. Otherwise each must compare one register, and one
/// register must hold, on every edge, the value that edge compared (the
/// compared register itself, or an alias of it such as the `r15d` in
/// `mov r15d, r13d`): that is [`Rebase::Alias`], the lowest such register.
/// [`Rebase::Truth`] is the caller's fallback when neither applies.
///
/// # Arguments
///
/// * `preds` - The processed predecessors.
/// * `outs` - Their out states.
/// * `recorded` - Their block records, for the comparison instructions.
/// * `bitness` - Register width for canonicalization.
///
/// # Returns
///
/// The agreed form, or `None` when the edges cannot be reconciled.
pub(super) fn join_rebase(
    preds: &[usize],
    outs: &[Env],
    recorded: &[SlotRec],
    bitness: u32,
) -> Option<Rebase> {
    let mut common: Option<BTreeSet<Key>> = None;
    let mut shape: Option<(Mnemonic, Vec<Option<u64>>)> = None;
    let mut width = None;
    let mut reg_lists: Vec<Vec<Register>> = Vec::new();
    for &p in preds {
        let src = recorded[p].flag_src?;
        let out = &outs[p];
        let bits = match &out.flags {
            Flags::Cmp(_, _, b) | Flags::Test(_, _, b) => *b,
            _ => return None,
        };
        if *width.get_or_insert(bits) != bits {
            return None;
        }
        let mut regs: Vec<Register> = Vec::new();
        let mut imms: Vec<Option<u64>> = Vec::new();
        for i in 0..src.op_count() {
            match src.op_kind(i) {
                OpKind::Register => regs.push(lift::canon(src.op_register(i), bitness)),
                OpKind::Memory => return None,
                _ => imms.push(Some(src.try_immediate(i).ok()?)),
            }
        }
        let this_shape = (src.mnemonic(), imms);
        if *shape.get_or_insert_with(|| this_shape.clone()) != this_shape {
            return None;
        }
        let &reg = regs.first()?;
        let single = regs.iter().all(|r| *r == reg);
        reg_lists.push(regs);
        let value = out.get(Key::Reg(reg));
        let mut cands: BTreeSet<Key> = if single {
            out.vals
                .iter()
                .filter(|(k, v)| matches!(k, Key::Reg(_)) && **v == value)
                .map(|(k, _)| *k)
                .collect()
        } else {
            BTreeSet::new()
        };
        if single && value == Expr::Var(Key::Reg(reg)) {
            cands.insert(Key::Reg(reg));
        }
        common = Some(match common {
            None => cands,
            Some(c) => c.intersection(&cands).copied().collect(),
        });
    }
    if reg_lists.iter().all(|l| Some(l) == reg_lists.first()) {
        return Some(Rebase::Registers);
    }
    common?.iter().next().copied().map(Rebase::Alias)
}

/// Passes [`dataflow`] runs as plain Kleene iteration before it widens:
/// far above the five a function's p99 needs, so a converging function's
/// facts are exactly those of the fixpoint it reaches.
const WIDEN_AFTER: usize = MAX_PASSES / 4;

#[cfg(test)]
thread_local! {
    /// How many times [`dataflow`] stopped at the pass budget on this
    /// thread instead of converging: a test's evidence that it converged.
    static CAPPED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Runs the forward dataflow to a fixpoint.
///
/// Blocks are visited in address order from the entry block on, wrapping
/// round to the blocks below it, optimistically about predecessors not yet
/// processed (so loop-invariant values survive the first pass over a back
/// edge). The entry block alone starts from the entry state; a block below
/// it (a tail the entry jumps back to) is reached through its
/// predecessors like any other. `IN[b]` is the meet over processed predecessor OUTs, made
/// consistent with phi placement: a variable a predecessor
/// assigns at its end is unknown in `b` (it holds its own text value from then on) unless
/// the assigned value is a stable constant `b` carries as well, so a value
/// written out once is never written again when a later call clobbers what
/// it was copied from. The predecessor writes out before such a variable every
/// value of its own that reads it, and before those every value that reads one
/// of them; every value of `b` that reads any variable written out is unknown
/// too, and so is every value that reads one of those (`ecx = *eax` pending while
/// the `eax` it reads is written out for reading a slot written out; `edx = a2`
/// pending while `a2 = ebx` is written out for `ebx`). A block reruns only when its IN or
/// the escape floor it last ran under changed; a floor change restarts the
/// pass budget. `ran_under` holds that per block: `None` before it has run
/// and once a flag rebase it must lift under lands, `Some(None)` when it
/// last ran with the escape floor unknown, and `Some(Some(k))` when it last
/// ran under floor `k`.
///
/// The transfer is not monotone: phi placement compares a predecessor's
/// OUT with the IN it feeds, so a value a back edge disagrees with can
/// drop out of an IN, which places a phi, which changes the back edge's
/// OUT, which readmits the value, forever (`ecx = ecx - 1` before a `dec
/// ecx` loop is agreed on and refuted on alternate passes). Past
/// [`WIDEN_AFTER`] passes each new IN is therefore met with the one before
/// it (a widening on the flat lattice of each variable): a variable an IN
/// lost or changed stays unknown there, every IN only loses facts, the
/// iteration ends, and each fact kept is one every incoming edge
/// re-establishes, never the leftover of an oscillation the pass budget
/// cut short. A function that converges sooner is not touched.
///
/// PERF: `IN[b]` reads only its predecessors (their OUT, record, flag
/// rebase and whether they ran) and the IN of their other successors
/// (the phi placement), so every change to one of those is stamped with
/// a clock, and a join none of whose inputs changed since it was last
/// met keeps the IN it has instead of being met again: on a function of
/// a thousand blocks, the passes after the first meet a few joins each.
///
/// # Arguments
///
/// * `ctx` - Per-function state (the escape floor is updated as a side effect).
/// * `code` - Decoded instructions per block.
/// * `succs` - Successor block indices per block.
/// * `preds` - Predecessor block indices per block.
/// * `live` - Liveness oracle for phi placement.
/// * `assumes` - Per block, the equality fact it may read under ([`block_assumptions`]).
///
/// # Returns
///
/// `(IN environments, processed flags, slot records)` per block.
pub(super) fn dataflow<L: Lifter>(
    ctx: &mut Ctx<'_>,
    code: &[Vec<L::Insn>],
    succs: &[Vec<usize>],
    preds: &[Vec<usize>],
    live: &Live,
    assumes: &[Option<(Key, u64)>],
) -> (Vec<Env>, Vec<bool>, Vec<SlotRec>) {
    let n = code.len();
    let mut ins: Vec<Env> = vec![Env::unknown(); n];
    let mut outs: Vec<Env> = vec![Env::unknown(); n];
    let mut processed = vec![false; n];
    let mut recorded: Vec<SlotRec> = vec![SlotRec::default(); n];
    let mut ran_under: Vec<Option<Option<i64>>> = vec![None; n];
    if n == 0 {
        return (ins, processed, recorded);
    }
    let mut passes = 0usize;
    let mut escapes_seen = ctx.escape_floor;
    let mut clock = 0u64;
    let mut stamp: Vec<u64> = vec![0; n];
    let mut met: Vec<Option<u64>> = vec![None; n];
    loop {
        passes += 1;
        if passes > MAX_PASSES {
            #[cfg(test)]
            CAPPED.with(|c| c.set(c.get() + 1));
            break;
        }
        let mut changed = false;
        let entry = ctx.entry_block;
        for b in (entry..n).chain(0..entry) {
            let unchanged = b != entry
                && met[b].is_some_and(|t| {
                    preds[b].iter().all(|&p| {
                        stamp[p] <= t && succs[p].iter().all(|&s| s == b || stamp[s] <= t)
                    })
                });
            let in_changed = if unchanged {
                false
            } else {
                let mut m: Option<Env> = (b == entry).then(|| L::entry_env(&*ctx));
                for &p in &preds[b] {
                    if !processed[p] {
                        continue;
                    }
                    m = Some(match m {
                        None => outs[p].clone(),
                        Some(cur) => cur.meet(&outs[p]),
                    });
                }
                let Some(mut m) = m else { continue };
                // INVARIANT: a temporary the dataflow pass took within a
                // predecessor's run names nothing the text sets (the emission
                // numbers its own), so a value that reads one is the
                // predecessor's to write out, like any value the join lost.
                let parked: Vec<Key> = m
                    .vals
                    .iter()
                    .filter(|(_, v)| {
                        v.any_var(&|k| matches!(k, Key::Tmp(id) if id >= lift::BLOCK_TMP))
                    })
                    .map(|(k, _)| *k)
                    .collect();
                for k in parked {
                    drop_key(&mut m, k);
                }
                if met[b].is_some() && passes > WIDEN_AFTER {
                    let changed_here: Vec<Key> = m
                        .vals
                        .iter()
                        .filter(|(k, v)| ins[b].vals.get(*k) != Some(*v))
                        .map(|(k, _)| *k)
                        .collect();
                    for k in changed_here {
                        drop_key(&mut m, k);
                    }
                }
                met[b] = Some(clock);
                for &p in &preds[b] {
                    if !processed[p] {
                        continue;
                    }
                    let phis = phi_keys(&outs[p], &succs[p], &ins, live, &processed, Some((b, &m)));
                    for &k in &phis {
                        let v = outs[p].vals.get(&k);
                        let stable = v.is_some_and(|v| !v.any_var(&|_| true));
                        if !(stable && m.vals.get(&k) == v) {
                            drop_key(&mut m, k);
                        }
                    }
                    let mut written = phis;
                    // The membership mirror keeps the `written` order (the
                    // loop below walks it) while the contains test stops
                    // being a scan of every key so far.
                    let mut marked: BTreeSet<Key> = written.iter().copied().collect();
                    let mut at = 0;
                    while let Some(&k) = written.get(at) {
                        at += 1;
                        let readers: Vec<Key> = outs[p]
                            .vals
                            .iter()
                            .filter(|(x, e)| **x != k && !marked.contains(*x) && e.may_read(k))
                            .map(|(x, _)| *x)
                            .collect();
                        marked.extend(readers.iter().copied());
                        written.extend(readers);
                    }
                    while let Some(k) = written.pop() {
                        let readers: Vec<Key> = m
                            .vals
                            .iter()
                            .filter(|(x, e)| **x != k && e.may_read(k))
                            .map(|(x, _)| *x)
                            .collect();
                        for x in readers {
                            drop_key(&mut m, x);
                            written.push(x);
                        }
                    }
                }
                if m.flags == Flags::Unknown && ctx.flag_readers[b] {
                    let active: Vec<usize> =
                        preds[b].iter().copied().filter(|&p| processed[p]).collect();
                    if !active.is_empty()
                        && active.iter().any(|&p| ctx.rebase_flags[p].is_none())
                        && active.iter().all(|&p| outs[p].flags != Flags::Unknown)
                    {
                        let how = if active.len() > 1 {
                            join_rebase(&active, &outs, &recorded, ctx.bitness)
                        } else {
                            None
                        }
                        .or_else(|| {
                            let cc = L::join_reader_cc(&code[b])?;
                            ctx.tmp_count += 1;
                            Some(Rebase::Truth(cc, ctx.tmp_count))
                        });
                        if let Some(how) = how {
                            for &p in &active {
                                ctx.rebase_flags[p] = Some(how);
                                ran_under[p] = None;
                                clock += 1;
                                stamp[p] = clock;
                            }
                            changed = true;
                        }
                    }
                }
                let differs = ins[b] != m;
                if differs {
                    ins[b] = m;
                    changed = true;
                    clock += 1;
                    stamp[b] = clock;
                }
                differs
            };
            if !processed[b] {
                processed[b] = true;
                clock += 1;
                stamp[b] = clock;
            }
            let floor = ctx.escape_floor;
            if !in_changed && ran_under[b] == Some(floor) {
                continue;
            }
            ran_under[b] = Some(floor);
            let mut env = ins[b].clone();
            let facts = block_facts::<L>(ctx, code, succs, &live.need, assumes, b);
            let out = L::exec_block(
                ctx,
                &code[b],
                b.checked_sub(1).map(|p| code[p].as_slice()),
                &mut env,
                lift::Pass::Dataflow,
                None,
                facts,
            );
            if out.tmp_flags
                && ctx.rebase_flags[b].is_none()
                && let Some(cc) = succs[b]
                    .iter()
                    .find(|&&s| ctx.flag_readers[s])
                    .and_then(|&s| L::join_reader_cc(&code[s]))
            {
                ctx.tmp_count += 1;
                ctx.rebase_flags[b] = Some(Rebase::Truth(cc, ctx.tmp_count));
                ran_under[b] = None;
                changed = true;
            }
            recorded[b] = SlotRec {
                uses: out.slot_use.keys().copied().collect(),
                defs: out.slot_def.keys().copied().collect(),
                reads: out.slot_use,
                stores: out.slot_def,
                calls: out.call_uses,
                branch_const: out.branch_const,
                switch_const: out.switch_idx.as_ref().and_then(const_index),
                switch_dest: out
                    .switch_target
                    .as_ref()
                    .and_then(|t| fold_static(ctx.program, t, FOLD_DEPTH)),
                branch: out.branch,
                flag_src: out.flag_src,
            };
            if outs[b] != env {
                outs[b] = env;
                changed = true;
            }
            clock += 1;
            stamp[b] = clock;
        }
        if ctx.escape_floor != escapes_seen {
            escapes_seen = ctx.escape_floor;
            passes = 0;
            changed = true;
        }
        if !changed {
            break;
        }
    }
    (ins, processed, recorded)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::collections::BTreeSet;

    use super::{SlotRec, SlotUse, slot_liveness};

    /// Computes slot liveness the plain way, sets merged block by block
    /// until nothing changes: what [`slot_liveness`] must agree with.
    ///
    /// # Arguments
    ///
    /// * `recorded` - Per-block slot accesses.
    /// * `succs` - Successor block indices per block.
    fn reference(recorded: &[SlotRec], succs: &[Vec<usize>]) -> Vec<BTreeSet<i64>> {
        let universe: BTreeSet<i64> = recorded
            .iter()
            .flat_map(|r| r.uses.iter().chain(&r.defs).copied())
            .collect();
        let uses: Vec<BTreeSet<i64>> = recorded
            .iter()
            .map(|r| {
                let mut u = r.uses.clone();
                for (cu, before) in &r.calls {
                    let seen: Vec<i64> = match cu {
                        SlotUse::All => universe.iter().copied().collect(),
                        SlotUse::Window(lo, hi) => universe.range(*lo..*hi).copied().collect(),
                    };
                    u.extend(seen.into_iter().filter(|o| !before.contains(o)));
                }
                u
            })
            .collect();
        let mut live = uses.clone();
        loop {
            let mut changed = false;
            for b in (0..recorded.len()).rev() {
                let out: BTreeSet<i64> = succs[b].iter().flat_map(|&s| live[s].clone()).collect();
                let mut inn = uses[b].clone();
                inn.extend(out.difference(&recorded[b].defs).copied());
                if inn != live[b] {
                    live[b] = inn;
                    changed = true;
                }
            }
            if !changed {
                return live;
            }
        }
    }

    /// The bit-vector liveness agrees with the plain one over loops, calls
    /// reading a window or everything, and more slots than one word holds.
    #[test]
    fn slot_liveness_agrees_with_the_plain_fixpoint() {
        let set = |offs: &[i64]| offs.iter().copied().collect::<BTreeSet<i64>>();
        let mut recorded: Vec<SlotRec> = (0..12)
            .map(|b: i64| SlotRec {
                uses: set(&[-8 * b, -8 * b - 4, -600 + b, -1000 - 3 * b]),
                defs: set(&[-8 * (b + 1), -8 * b - 300, -600 + 2 * b]),
                ..SlotRec::default()
            })
            .collect();
        recorded[2].calls = vec![(SlotUse::Window(-40, -8), set(&[-16]))];
        recorded[5].calls = vec![(SlotUse::All, set(&[-48, -340]))];
        let succs: Vec<Vec<usize>> = (0..12)
            .map(|b| match b {
                3 => vec![4, 1],
                7 => vec![8, 4],
                10 => vec![11, 2],
                11 => vec![],
                _ => vec![b + 1],
            })
            .collect();
        assert_eq!(
            slot_liveness(&recorded, &succs),
            reference(&recorded, &succs)
        );
        let empty = vec![SlotRec::default(); 3];
        assert_eq!(
            slot_liveness(&empty, &[vec![1], vec![2], vec![0]]),
            vec![BTreeSet::new(); 3]
        );
    }

    /// The dataflow converges on a counted loop entered with the counter
    /// one less than a variable, instead of running out its pass budget.
    ///
    /// `lea eax, [ecx-1]; mov ecx, eax` before a `dec ecx; jne` loop: the
    /// loop head's `ecx = ecx - 1` agrees with the back edge only while it
    /// is not assumed, so without sticky drops every pass flips it and the
    /// text kept whichever phase the budget ended on (d3dx9's `ecx -= 2`
    /// for a loop that steps by one). The head here has no `ecx` fact, and
    /// the loop steps by one.
    ///
    /// `mov ecx,[esp+4]; mov esi,[esp+8]; test ecx,ecx; je +1; inc ecx;
    /// cmp ecx,1; jbe out; lea eax,[ecx-1]; mov ecx,eax; L: mov [esi],cl;
    /// mov al,[esi+1]; inc esi; dec ecx; mov [esi],al; jne L; out: ret`.
    #[test]
    fn a_counted_loop_converges_without_the_pass_budget() {
        use crate::analysis::{Analysis, Overlay, decompile::decompile};
        use crate::program::{Arch, Program, Section};
        let code: [u8; 34] = [
            0x8b, 0x4c, 0x24, 0x04, 0x8b, 0x74, 0x24, 0x08, 0x85, 0xc9, 0x74, 0x01, 0x41, 0x83,
            0xf9, 0x01, 0x76, 0x10, 0x8d, 0x41, 0xff, 0x8b, 0xc8, 0x88, 0x0e, 0x8a, 0x46, 0x01,
            0x46, 0x49, 0x88, 0x06, 0x75, 0xf5,
        ];
        let mut bytes = vec![0u8; 0x2000];
        bytes[..code.len()].copy_from_slice(&code);
        bytes[code.len()] = 0xc3;
        let p = Program::raw(
            bytes,
            Arch::X86,
            0x40_0000,
            Some(0x40_1000),
            vec![
                Section::mapped(".text", 0x40_1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x40_2000, 0x1000, 0x1000, false, false),
            ],
        );
        let a = Analysis::compute(&p);
        super::CAPPED.with(|c| c.set(0));
        let text = decompile(&p, &a, &Overlay::default(), 0x40_1000).unwrap_or_default();
        assert_eq!(super::CAPPED.with(std::cell::Cell::get), 0, "{text}");
        assert!(!text.contains("var1 -= 2"), "{text}");
        assert_eq!(text.matches("var1 -= 1;").count(), 2, "{text}");
    }
}
