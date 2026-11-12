//! The RISC-V lifter: executes one block of RV32 or RV64 instructions over
//! the decompiler's symbolic environment.
//!
//! The RISC-V counterpart of [`super::lift_a32`], through the same
//! executor ([`Exec`]): a register is a [`Key::Rv`] variable, `x0` reads
//! zero and a write to it vanishes, the stack pointer is the tracked
//! offset [`Expr::Sp`] while it is one, and every value is computed at the
//! register width, a `w` form at 32 bits and sign-extended. There are no
//! flags: a conditional branch compares its two registers where the block
//! ends. A call passes the arguments the calling convention puts in
//! registers and assigns its result ([`call`]), a `call` or `tail`
//! sequence's `auipc` and `jalr` naming their target as one; what a
//! function takes is read from its code ([`mod@shape`]); which registers
//! each instruction reads and writes is [`live`]'s; the float
//! instructions are [`float`]'s and the atomics [`atomic`]'s. The CSRs and
//! an `ecall` [`call`] does not name are not modeled: each stays an
//! `/* asm */` comment and forgets what it writes.

mod atomic;
mod call;
mod float;
mod live;
mod shape;
mod step;

pub(in crate::analysis::decompile) use float::ty as float_ty;
pub(in crate::analysis::decompile) use live::effects;
pub(in crate::analysis::decompile) use shape::{
    arg_reg, built as built_shape, callee_shape, entry_env, param_types, ret_lane, shape,
    writes_result,
};

use super::Ctx;
use super::expr::{Cc, Cond, Expr, Flags, Key, Op, fold};
use super::lift::{
    BlockFacts, BlockOut, Branch, Callee, EffectKind, Env, Exec, LiveFn, Pass, PhiFn,
};
use crate::analysis::Function;
use crate::fxmap::FxHashMap;
use crate::isa::rv::{self, Alu, BrCond, Flow, Insn, Op as ROp, Reg, SP, Xlen, ZERO};
use crate::isa::x86::ConditionCode;
use crate::program::Program;

/// Returns the register width of a program's RISC-V code.
///
/// # Arguments
///
/// * `program` - The image.
pub(in crate::analysis::decompile) fn xlen(program: &Program) -> Xlen {
    match program.arch.isa() {
        Some(crate::isa::Isa::Rv(x)) => x,
        Some(crate::isa::Isa::X86 { .. } | crate::isa::Isa::A64 | crate::isa::Isa::A32) | None => {
            Xlen::X64
        }
    }
}

/// Returns a width in bits as the expression folder takes it.
///
/// # Arguments
///
/// * `xlen` - The register width.
fn bits(xlen: Xlen) -> u8 {
    match xlen {
        Xlen::X32 => 32,
        Xlen::X64 => 64,
    }
}

/// Decodes every block of a function, in block order.
///
/// # Arguments
///
/// * `program` - The image.
/// * `f` - The function.
///
/// # Returns
///
/// Each block's instructions; a block stops at the first address that does
/// not decode.
pub(in crate::analysis::decompile) fn decode_blocks(
    program: &Program,
    f: &Function,
) -> Vec<Vec<Insn>> {
    let xlen = xlen(program);
    f.blocks
        .iter()
        .map(|b| {
            let mut v = Vec::new();
            let mut va = b.start;
            while va < b.end {
                let Some(i) = crate::analysis::rv::decode(program, va, xlen) else {
                    break;
                };
                va = i.next();
                v.push(i);
            }
            v
        })
        .collect()
}

/// Executes one RISC-V block from `env`, returning its lines and
/// control-flow facts, as [`super::lift_a32::exec_block_a32`] does an
/// ARM32 block.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `instrs` - The block's instructions.
/// * `env` - State at the block's entry; updated to the state at its exit.
/// * `pass` - Record text (the emission pass) or only compute state.
/// * `phi` - Values the block must write out at its end, and the liveness
///   oracle used while doing so.
/// * `facts` - The registers needed after each instruction, and whether
///   it is the entry block.
///
/// # Returns
///
/// The lines and the block's branch, jump and slot facts.
pub(in crate::analysis::decompile) fn exec_block_rv(
    ctx: &mut Ctx<'_>,
    instrs: &[Insn],
    env: &mut Env,
    pass: Pass,
    phi: Option<(&PhiFn<'_>, &LiveFn<'_>)>,
    facts: BlockFacts<'_>,
) -> BlockOut {
    let start = instrs.first().map_or(0, |i| i.va);
    let xlen = xlen(ctx.program);
    let table_load = table_load(ctx, instrs);
    let mut lift = Lift {
        ex: Exec::new(ctx, env, pass, &facts, start),
        xlen,
        table_load,
    };
    let mut out = BlockOut::default();
    let mut jcc = None;
    for (idx, i) in instrs.iter().enumerate() {
        lift.ex.at = i.va;
        if let Some(c) = lift.ex.ctx.overlay.comments.get(&i.va) {
            lift.ex.lines.push(format!("// {c}"));
        }
        match facts.need.and_then(|n| n.get(idx)) {
            Some(need) => lift.ex.regs_needed.get_or_insert_default().clone_from(need),
            None => lift.ex.regs_needed = None,
        }
        let prev = idx.checked_sub(1).and_then(|k| instrs.get(k));
        match i.flow() {
            Flow::Next => lift.step(i),
            Flow::CondJump => {
                if let ROp::Branch {
                    cond,
                    rs1,
                    rs2,
                    target,
                } = i.op
                {
                    jcc = Some(((cond, rs1, rs2), target, i.next()));
                } else {
                    lift.unmodeled(i);
                }
            }
            Flow::Jump => {
                match transfer_target(prev, i, xlen) {
                    Some(t) if lift.ex.ctx.block_starts.contains(&t) => out.goto = Some(t),
                    Some(t) => lift.tail_call(Callee::Direct(t), t),
                    None => lift.jump(i, &mut out),
                }
                if let ROp::Jal { rd, .. } | ROp::Jalr { rd, .. } = i.op {
                    lift.write(rd, Expr::Const(i.next()));
                }
            }
            Flow::Call => lift.call(i, prev),
            Flow::Return => lift.ret(i),
            Flow::Invalid => lift.unmodeled(i),
        }
    }
    lift.finish(out, jcc, phi, start)
}

/// The load of the entry a block's `jr` dispatches through, when the
/// analysis resolved its table.
///
/// The jumped-to register is followed back through the block: an `add`
/// (an entry plus its base) or a copy hands it on to its operands, and the
/// load that writes one of them is the entry's; any other write ends the
/// search.
///
/// # Arguments
///
/// * `ctx` - Per-function state: the analysis's jump tables.
/// * `instrs` - The block's instructions.
fn table_load(ctx: &Ctx<'_>, instrs: &[Insn]) -> Option<u64> {
    let jr = instrs.last()?;
    let ROp::Jalr { rs1, .. } = jr.op else {
        return None;
    };
    if !ctx.analysis.jump_tables.contains_key(&jr.va) {
        return None;
    }
    let mut wanted = vec![rs1];
    for i in instrs.iter().rev().skip(1) {
        if !crate::analysis::rv::dest(i.op).is_some_and(|rd| wanted.contains(&rd)) {
            continue;
        }
        if let ROp::Load { .. } = i.op {
            return Some(i.va);
        }
        if let ROp::Reg3 {
            op: Alu::Add,
            rs1,
            rs2,
            word: false,
            ..
        } = i.op
        {
            wanted = vec![rs1, rs2];
        } else if let ROp::Imm {
            op: Alu::Add,
            rs1,
            imm: 0,
            word: false,
            ..
        } = i.op
        {
            wanted = vec![rs1];
        } else {
            return None;
        }
    }
    None
}

/// The register an `auipc` sets and the address it holds, which a `jalr`
/// right after it reads as a `call` or `tail` sequence.
///
/// # Arguments
///
/// * `i` - The instruction.
fn auipc(i: &Insn) -> Option<(Reg, u64)> {
    if let ROp::Auipc { rd, target } = i.op {
        Some((rd, target))
    } else {
        None
    }
}

/// Returns where a `jalr` goes when an `auipc` right before it set its
/// base: the `call` and `tail` sequences.
///
/// # Arguments
///
/// * `upper` - What the instruction before set ([`auipc`]).
/// * `i` - The `jalr`.
/// * `xlen` - The register width.
fn built(upper: Option<(Reg, u64)>, i: &Insn, xlen: Xlen) -> Option<u64> {
    let (ROp::Jalr { rs1, off, .. }, Some((r, at))) = (i.op, upper) else {
        return None;
    };
    (r == rs1).then(|| xlen.addr(at.wrapping_add_signed(off)) & !1)
}

/// Returns where a direct transfer goes, or one an `auipc` right before
/// it built.
///
/// # Arguments
///
/// * `prev` - The instruction before it in its block.
/// * `i` - The transfer.
/// * `xlen` - The register width.
fn transfer_target(prev: Option<&Insn>, i: &Insn, xlen: Xlen) -> Option<u64> {
    i.target().or_else(|| built(prev.and_then(auipc), i, xlen))
}

/// Returns the registers needed while each instruction of a block is
/// lifted: those some later instruction reads, and those it reads itself.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `instrs` - The block's instructions.
/// * `out` - The registers read after the block, with their lanes.
///
/// # Returns
///
/// One map per instruction, of each needed register's lane.
pub(in crate::analysis::decompile) fn need_after(
    ctx: &Ctx<'_>,
    instrs: &[Insn],
    out: &FxHashMap<Key, u8>,
) -> Vec<FxHashMap<Key, u8>> {
    let effects: Vec<super::lift::Effects> = instrs.iter().map(|i| effects(ctx, i)).collect();
    super::lift::need_with_reads(&effects, out)
}

/// Counts the instructions of a block that render as statements.
///
/// The structurer weighs copying a block by the count: not the return,
/// the stack adjustments, nor the reloads of the registers the function
/// preserves.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
pub(in crate::analysis::decompile) fn body_len(instrs: &[Insn]) -> usize {
    let quiet = |i: &Insn| {
        let restores = matches!(i.op, ROp::Load { rd, .. } if super::abi::rv::callee_saved(rd));
        let moves_sp = matches!(i.op, ROp::Imm { rd: SP, .. });
        restores || moves_sp || i.flow() == Flow::Return
    };
    instrs.iter().filter(|i| !quiet(i)).count()
}

/// Tells whether two RISC-V blocks make the same test: the same
/// instructions up to a conditional branch at the end of each, the two
/// branches sending each outcome to the same address.
///
/// # Arguments
///
/// * `a` - One block's instructions.
/// * `b` - The other's.
pub(in crate::analysis::decompile) fn same_test(a: &[Insn], b: &[Insn]) -> bool {
    let (Some((ja, ha)), Some((jb, hb))) = (a.split_last(), b.split_last()) else {
        return false;
    };
    let same_body = ha.len() == hb.len()
        && ha
            .iter()
            .zip(hb)
            .all(|(x, y)| x.op == y.op && !matches!(x.op, ROp::Auipc { .. }));
    let (
        ROp::Branch {
            cond: ca,
            rs1: a1,
            rs2: a2,
            target: ta,
        },
        ROp::Branch {
            cond: cb,
            rs1: b1,
            rs2: b2,
            target: tb,
        },
    ) = (ja.op, jb.op)
    else {
        return false;
    };
    let (fa, fb) = (ja.next(), jb.next());
    same_body
        && (a1, a2) == (b1, b2)
        && ((ca == cb && ta == tb && fa == fb) || (ca == inverse(cb) && ta == fb && fa == tb))
}

/// Returns the comparison that holds exactly when `c` fails.
///
/// # Arguments
///
/// * `c` - The comparison.
fn inverse(c: BrCond) -> BrCond {
    match c {
        BrCond::Eq => BrCond::Ne,
        BrCond::Ne => BrCond::Eq,
        BrCond::Lt => BrCond::Ge,
        BrCond::Ge => BrCond::Lt,
        BrCond::Ltu => BrCond::Geu,
        BrCond::Geu => BrCond::Ltu,
    }
}

/// Returns the condition code a branch comparison takes on its two
/// operands.
///
/// # Arguments
///
/// * `c` - The comparison.
fn code(c: BrCond) -> ConditionCode {
    match c {
        BrCond::Eq => ConditionCode::e,
        BrCond::Ne => ConditionCode::ne,
        BrCond::Lt => ConditionCode::l,
        BrCond::Ge => ConditionCode::ge,
        BrCond::Ltu => ConditionCode::b,
        BrCond::Geu => ConditionCode::ae,
    }
}

/// A block's conditional branch: its comparison and operands, its target
/// and its fall-through.
type Jcc = ((BrCond, Reg, Reg), u64, u64);

/// One block's lifting over the shared executor.
struct Lift<'c, 'a> {
    /// The executor: the environment, the function's state and the lines.
    ex: Exec<'c, 'a>,
    /// The register width.
    xlen: Xlen,
    /// The load of the entry of a jump table the block's `jr` dispatches
    /// through, whose address names the switch's index ([`table_load`]).
    table_load: Option<u64>,
}

impl Lift<'_, '_> {
    /// Returns the register width in bits, as the folder takes it.
    fn w(&self) -> u8 {
        bits(self.xlen)
    }

    /// Reads a register: `x0` as zero, the stack pointer as its tracked
    /// offset.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn get(&self, r: Reg) -> Expr {
        match r {
            ZERO => Expr::Const(0),
            SP => self
                .ex
                .env
                .sp
                .map_or_else(|| self.ex.env.get(Key::Rv(SP)), Expr::Sp),
            Reg::X(_) | Reg::F(_) => self.ex.assumed(self.ex.env.get(Key::Rv(r)), 64),
        }
    }

    /// Writes a register, lazily: a write to `x0` vanishes, and the stack
    /// pointer is tracked as an offset while the value is one.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    /// * `v` - The value.
    fn write(&mut self, r: Reg, v: Expr) {
        match (r, v) {
            (ZERO, _) => {}
            (SP, Expr::Sp(k)) => {
                self.ex.env.sp = Some(k);
                self.ex.env.vals.remove(&Key::Rv(SP));
            }
            (SP, v) => {
                self.ex.env.sp = None;
                self.ex.assign(Key::Rv(SP), v);
            }
            (Reg::X(_) | Reg::F(_), v) => self.ex.assign(Key::Rv(r), v),
        }
    }

    /// Forgets what memory held before an instruction that may write it,
    /// its pending stack stores written out first.
    fn forget_memory(&mut self) {
        self.ex.protect_memory();
        let slots: Vec<Key> = self
            .ex
            .env
            .vals
            .keys()
            .copied()
            .filter(|k| matches!(k, Key::Slot(_)))
            .collect();
        for k in slots {
            self.ex.materialize(k, &mut Vec::new(), None);
            self.ex.clobber(k);
        }
    }

    /// Lifts an instruction without a model: keeps its assembly as a
    /// comment and forgets every register it may write and, if it may
    /// write memory, what memory held, its pending stack stores written
    /// out first.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    fn unmodeled(&mut self, i: &Insn) {
        let memory = matches!(
            i.op,
            ROp::Store { .. }
                | ROp::Sc { .. }
                | ROp::Amo { .. }
                | ROp::Ecall
                | ROp::Unknown
                | ROp::Float(rv::FOp::Store { .. })
        );
        if memory {
            if let Some(p) = &mut self.ex.ctx.probe {
                p.asm();
            }
            self.forget_memory();
        }
        let mut written = i.registers().writes;
        if i.op == ROp::Ecall {
            written.push(Reg::X(super::abi::rv::FIRST_ARG));
        }
        for r in written {
            if r == SP {
                self.ex.env.sp = None;
            }
            self.ex.clobber(Key::Rv(r));
        }
        self.ex.unmodeled += 1;
        if self.ex.emit {
            self.ex.lines.push(format!("/* asm: {} */", rv::text(i)));
            self.ex.record(EffectKind::Unmodeled);
        }
    }

    /// Returns where a `jalr` goes: its base plus its offset, bit 0
    /// cleared as the machine clears it when the address is a constant; a
    /// computed address is named as the register holds it.
    ///
    /// # Arguments
    ///
    /// * `rs1` - The base.
    /// * `off` - The offset.
    fn jalr_target(&self, rs1: Reg, off: i64) -> Expr {
        match offset(self.get(rs1), off, self.w()) {
            Expr::Const(c) => Expr::Const(c & !1),
            e => e,
        }
    }

    /// Lifts a jump through a register no `auipc` built: a switch when
    /// the analysis resolved its table and the entry's load named its index
    /// ([`table_load`]), a tail call through a table of functions, else a
    /// computed `goto`.
    ///
    /// # Arguments
    ///
    /// * `i` - The `jr`.
    /// * `out` - The block's facts, which take the switch's target.
    fn jump(&mut self, i: &Insn, out: &mut BlockOut) {
        let ROp::Jalr { rs1, off, .. } = i.op else {
            return self.unmodeled(i);
        };
        let target = self.jalr_target(rs1, off);
        if self.ex.ctx.analysis.jump_tables.contains_key(&i.va) && self.ex.switch_idx.is_some() {
            out.switch_target = Some(target);
            return;
        }
        let entries = self.ex.function_table(&target);
        if let Some(like) = self.ex.table_callee(&entries, |e| self.arg_keys(e)) {
            return self.tail_call(Callee::Through(target), like);
        }
        if self.ex.emit {
            let line = format!("goto *{};", target.render(&self.ex.names()));
            self.ex.lines.push(line);
        }
        self.ex.record(EffectKind::Jump(target));
    }

    /// Ends the block: places the phis, captures the branch, and records
    /// what the block's statements do.
    ///
    /// The branch's operands are read before the phis are written out and
    /// held through them as the flags are, each operand copied out on its
    /// own when a phi changes what it reads, so the condition names what
    /// the text holds where the block ends.
    ///
    /// # Arguments
    ///
    /// * `out` - What the instructions found so far.
    /// * `jcc` - The block's conditional branch.
    /// * `phi` - Values to write out at the end, and the liveness oracle.
    /// * `start` - The block's first address.
    fn finish(
        mut self,
        mut out: BlockOut,
        jcc: Option<Jcc>,
        phi: Option<(&PhiFn<'_>, &LiveFn<'_>)>,
        start: u64,
    ) -> BlockOut {
        self.ex.flags = match jcc {
            Some(((_, rs1, rs2), ..)) => Flags::Cmp(self.get(rs1), self.get(rs2), self.w()),
            None => Flags::Unknown,
        };
        if let Some((phi, live)) = phi {
            for k in phi(self.ex.env) {
                self.ex.materialize_phi(k, live);
            }
        }
        if let Some(((c, ..), target, fall)) = jcc {
            let cond = Cond {
                cc: Cc(code(c)),
                flags: std::mem::replace(&mut self.ex.flags, Flags::Unknown),
            };
            out.branch_const = cond.eval().map(|taken| (taken, target, fall));
            self.ex.record(EffectKind::Branch(cond.clone()));
            out.branch = Some(Branch { cond, target, fall });
        }
        let mut ex = self.ex;
        out.switch_idx = ex.switch_idx.take();
        if let Some(idx) = out.switch_idx.as_ref().filter(|_| ex.emit) {
            ex.record(EffectKind::Switch(idx.clone()));
        }
        ex.env.flags = Flags::Unknown;
        ex.close(out, Some(start))
    }
}

/// An address plus a signed offset, at a width.
///
/// # Arguments
///
/// * `base` - The address.
/// * `off` - The offset.
/// * `bits` - The width.
fn offset(base: Expr, off: i64, bits: u8) -> Expr {
    match off.cmp(&0) {
        std::cmp::Ordering::Equal => base,
        std::cmp::Ordering::Greater => fold(Op::Add, base, Expr::Const(off.unsigned_abs()), bits),
        std::cmp::Ordering::Less => fold(Op::Sub, base, Expr::Const(off.unsigned_abs()), bits),
    }
}
