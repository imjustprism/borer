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
