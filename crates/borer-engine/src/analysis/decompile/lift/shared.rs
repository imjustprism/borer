//! What the arm and RISC-V lifters share with the executor beyond what
//! the x86 lifter uses: a function's edges, the registers each
//! instruction needs, a call's slot uses, and a tail call's line.

use super::*;
use crate::analysis::Function;

/// Returns a function's control-flow edges as block indices, and its entry
/// block's index.
///
/// # Arguments
///
/// * `f` - The function.
///
/// # Returns
///
/// Each block's successors that are blocks of the function, by index in
/// [`Function::blocks`], and the index of the block at the entry (0 when
/// none starts there).
pub(in crate::analysis::decompile) fn edges(f: &Function) -> (Vec<Vec<usize>>, usize) {
    let idx: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let succs = f
        .blocks
        .iter()
        .map(|b| {
            b.successors
                .iter()
                .filter_map(|s| idx.get(s).copied())
                .collect()
        })
        .collect();
    (succs, idx.get(&f.entry).copied().unwrap_or(0))
}

/// Computes, for every instruction of a block, the registers needed while
/// it is lifted: those some later instruction reads ([`need_from`]), and
/// those it reads itself, each at the wider lane.
///
/// # Arguments
///
/// * `effects` - The block's instructions' register reads and writes.
/// * `out` - Registers live at the block's exit.
///
/// # Returns
///
/// One need map per instruction, indexed like `effects`.
pub(in crate::analysis::decompile) fn need_with_reads(
    effects: &[Effects],
    out: &FxHashMap<Key, u8>,
) -> Vec<FxHashMap<Key, u8>> {
    let mut need = need_from(effects, out);
    for (n, (reads, _)) in need.iter_mut().zip(effects) {
        for &(k, lane) in reads {
            let held = n.entry(k).or_insert(lane);
            *held = (*held).max(lane);
        }
    }
    need
}

/// Fewest leading words of a table that must start functions for a jump
/// read from it to be a tail call ([`Exec::function_table`]).
const FN_TABLE_MIN: usize = 2;

/// Most entries of a function table read ([`Exec::function_table`]).
const FN_TABLE_MAX: u64 = 64;

impl Exec<'_, '_> {
    /// Records the stack slots a call's callee may read, for slot
    /// liveness: a window from the lowest escaped slot up while the stack
    /// pointer is a tracked offset, every slot when it is not.
    pub(in crate::analysis::decompile) fn note_call_slots(&mut self) {
        let written = self
            .slot_def
            .iter()
            .flat_map(|(&o, &b)| o..o.saturating_add(i64::from(b / 8).max(1)))
            .collect();
        match (self.env.sp, self.ctx.escape_floor) {
            (Some(_), Some(f)) => self.call_uses.push((SlotUse::Window(f, i64::MAX), written)),
            (Some(_), None) => {}
            (None, _) => self.call_uses.push((SlotUse::All, written)),
        }
    }

    /// The functions of the table an indirect jump's target is read from:
    /// a load from an address built on a constant whose first
    /// [`FN_TABLE_MIN`] words each start a function, and as many words after
    /// them as start one, up to [`FN_TABLE_MAX`].
    ///
    /// Such a jump leaves the function for one of them, a tail call through
    /// the table (`return ops[k](a, b);`), where a table of the function's
    /// own code addresses would be a switch. A target that is the name of a
    /// register written out early ([`Self::early_value`]), as an entry read
    /// at an index too long to read inline is, is the read it was written
    /// out as.
    ///
    /// # Arguments
    ///
    /// * `target` - The jump's target value.
    ///
    /// # Returns
    ///
    /// The table's functions, in table order; empty when the target is no
    /// read from such a table.
    pub(in crate::analysis::decompile) fn function_table(&self, target: &Expr) -> Vec<u64> {
        /// Deepest an address expression is searched for its base.
        const DEPTH_MAX: u8 = 4;
        fn bases(e: &Expr, depth: u8, out: &mut Vec<u64>) {
            match e {
                Expr::Const(c) => out.push(*c),
                Expr::Bin(_, l, r) if depth > 0 => {
                    bases(l, depth - 1, out);
                    bases(r, depth - 1, out);
                }
                _ => {}
            }
        }
        let read = match target {
            Expr::Var(k) => self.early_value(*k).unwrap_or(target),
            other => other,
        };
        let Expr::Deref(addr, _) = read else {
            return Vec::new();
        };
        let mut found = Vec::new();
        bases(addr, DEPTH_MAX, &mut found);
        let program = self.ctx.program;
        let width = if program.is_64 { 8 } else { 4 };
        let word = |base: u64, k: u64| {
            crate::analysis::read_word(program, base.wrapping_add(k * width))
                .filter(|&w| self.ctx.analysis.function(w).is_some())
        };
        found
            .into_iter()
            .map(|base| {
                (0..FN_TABLE_MAX)
                    .map_while(|k| word(base, k))
                    .collect::<Vec<u64>>()
            })
            .find(|run| run.len() >= FN_TABLE_MIN)
            .unwrap_or_default()
    }

    /// The function of a table a tail call through it takes its arguments
    /// as: the one taking the most registers, when every function's are
    /// known, its registers hold every other function's, they all return
    /// alike, and each of the registers holds a value here. Only on a 64-bit
    /// image, whose words the call's integer pointer passes one a register.
    ///
    /// # Arguments
    ///
    /// * `entries` - The table's functions ([`Self::function_table`]).
    /// * `args` - A function's argument registers and what it returns,
    ///   `None` when unknown or not a plain integer call.
    ///
    /// # Returns
    ///
    /// That function, or `None` to keep the jump a computed `goto`.
    pub(in crate::analysis::decompile) fn table_callee(
        &self,
        entries: &[u64],
        args: impl Fn(u64) -> Option<(Vec<Key>, Returns)>,
    ) -> Option<u64> {
        if !self.ctx.program.is_64 {
            return None;
        }
        let shapes: Vec<(u64, Vec<Key>, Returns)> = entries
            .iter()
            .map(|&e| args(e).map(|(r, back)| (e, r, back)))
            .collect::<Option<_>>()?;
        let (like, regs, back) = shapes.iter().max_by_key(|(_, r, _)| r.len())?;
        let alike = shapes
            .iter()
            .all(|(_, r, b)| b == back && r.iter().all(|k| regs.contains(k)));
        (alike && regs.iter().all(|k| self.env.vals.contains_key(k))).then_some(*like)
    }

    /// Emits a tail call's line: `return f(args);` when the function hands
    /// the callee's result back, else the call and a bare `return;`.
    ///
    /// # Arguments
    ///
    /// * `text` - How the call names its callee.
    /// * `args` - The arguments it passes.
    /// * `reached` - The import slot it reaches, for argument names.
    /// * `returns` - What the callee hands back.
    pub(in crate::analysis::decompile) fn emit_tail(
        &mut self,
        text: &str,
        args: &[(ArgAt, Expr)],
        reached: Option<u64>,
        returns: Returns,
    ) {
        if !self.emit {
            return;
        }
        let names = self.names();
        let mut rendered: Vec<String> = args.iter().map(|(_, e)| e.render(&names)).collect();
        self.name_arguments(reached, &mut rendered);
        let call = abi::call_text(text, &rendered);
        if !self.ctx.unused_result && returns != Returns::Nothing {
            self.lines.push(format!("return {call};"));
        } else {
            self.lines.push(format!("{call};"));
            self.lines.push("return;".to_owned());
        }
    }

    /// Returns the stack words a call passes, read where the stack
    /// pointer stands at the call; none while it is no tracked offset.
    ///
    /// # Arguments
    ///
    /// * `words` - How many words the callee takes on the stack.
    /// * `word` - A word's size in bytes, 4 or 8.
    pub(in crate::analysis::decompile) fn stack_arguments(
        &mut self,
        words: i64,
        word: i64,
    ) -> Vec<(ArgAt, Expr)> {
        let Some(sp) = self.env.sp.filter(|_| words > 0) else {
            return Vec::new();
        };
        let bits = u8::try_from(word.saturating_mul(8)).unwrap_or(64);
        (0..words)
            .map(|n| {
                let o = sp.saturating_add(word * n);
                let k = Key::Slot(o);
                if !self.slot_def.contains_key(&o) {
                    let width = self.slot_use.entry(o).or_default();
                    *width = (*width).max(bits);
                }
                let v = self
                    .env
                    .vals
                    .get(&k)
                    .cloned()
                    .unwrap_or_else(|| self.env.get(k));
                (ArgAt::Stack(word * n, bits), self.assumed(v))
            })
            .collect()
    }
}
