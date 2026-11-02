//! Calls, tail calls and returns for the RISC-V lifter, as the calling
//! convention passes their values.
//!
//! A call passes what its callee takes: the registers its body reads as
//! parameters ([`super::shape::arg_regs`]), the positions an import's
//! declaration states, else the argument registers the caller wrote since
//! the last call. Before the call every value pending in a variable the
//! call leaves alone is written out; afterwards the registers a call may
//! change hold nothing but its result, in `a0` or `fa0`. A return hands
//! back `a0` (or `fa0` for a float) unless the function returns nothing.

use super::super::Ctx;
use super::super::abi::{self, rv as rv_abi};
use super::super::expr::{Expr, Key, Ty};
use super::super::lift::{self, ArgAt, Callee, EffectKind, Returns, Shown, stated_returns};
use super::Lift;
use super::shape::{arg_reg, arg_regs};
use crate::isa::rv::{Insn, Op as ROp, Reg};

/// The register the function at hand hands its result back in: `fa0` for
/// a float, else `a0`.
///
/// # Arguments
///
/// * `ctx` - The function's state.
pub(in crate::analysis::decompile) fn result_reg(ctx: &Ctx<'_>) -> Reg {
    if ctx.ret_float {
        Reg::F(rv_abi::FIRST_ARG)
    } else {
        Reg::X(rv_abi::FIRST_ARG)
    }
}

impl Lift<'_, '_> {
    /// The integer type a register's whole value has.
    fn word_ty(&self) -> Ty {
        if self.w() == 32 { Ty::U32 } else { Ty::U64 }
    }

    /// The variable a call's result comes back in, and its type.
    ///
    /// # Arguments
    ///
    /// * `r` - What the callee hands back.
    fn result_of(&self, r: Returns) -> Option<(Key, Ty)> {
        let back = |r: Reg| Key::Rv(r);
        match r {
            Returns::Nothing => None,
            Returns::Int(_) => Some((back(Reg::X(rv_abi::FIRST_ARG)), self.word_ty())),
            Returns::Float(32) => Some((back(Reg::F(rv_abi::FIRST_ARG)), Ty::F32)),
            Returns::Float(_) => Some((back(Reg::F(rv_abi::FIRST_ARG)), Ty::F64)),
        }
    }

    /// The argument registers a callee takes and the stack words past
    /// them, when its body or a declaration says; a variable list adds
    /// the integer registers the caller set past the fixed ones.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry, when the call names one.
    /// * `reached` - The import slot a stub reaches, when it reaches one.
    fn callee_args(&self, target: Option<u64>, reached: Option<u64>) -> Option<(Vec<Reg>, i64)> {
        let ctx = &*self.ex.ctx;
        let (mut regs, stack, variadic) =
            if let Some(p) = lift::import_prototype(ctx, reached.or(target)) {
                let count = usize::from(p.params);
                let regs: Vec<Reg> = (0..count).filter_map(|i| arg_reg(i, p.floats)).collect();
                let stack = count.saturating_sub(regs.len());
                (regs, stack, p.variadic)
            } else {
                let t = target.map(|t| abi::reached(ctx.analysis, t))?;
                let f = ctx.analysis.function(t).filter(|f| f.thunk.is_none())?;
                let s = super::shape::callee_shape(ctx, f.entry)?;
                let regs = arg_regs(ctx, f.entry)?.to_vec();
                (regs, usize::try_from(s.stack).unwrap_or(0), s.variadic)
            };
        if variadic && stack == 0 {
            let fixed: Vec<Reg> = regs.clone();
            regs.extend(
                self.written_since_call(false)
                    .into_iter()
                    .filter(|r| matches!(r, Reg::X(_)) && !fixed.contains(r)),
            );
        }
        Some((regs, i64::try_from(stack).unwrap_or(0)))
    }

    /// The argument registers the caller set since the last call: the
    /// integer ones up to the highest set, then the float ones up to the
    /// highest set.
    ///
    /// # Arguments
    ///
    /// * `tail` - The transfer is a tail jump, which hands on what the
    ///   function was passed too.
    fn written_since_call(&self, tail: bool) -> Vec<Reg> {
        let fresh = |r: Reg| {
            let k = Key::Rv(r);
            self.ex.env.fresh.contains(&k) || (tail && self.ex.env.vals.contains_key(&k))
        };
        let bank = |make: fn(u8) -> Reg, count: u8| -> Vec<Reg> {
            let regs = (0..count).map(|n| make(rv_abi::FIRST_ARG + n));
            let top = regs.clone().rposition(fresh);
            top.map_or_else(Vec::new, |t| regs.take(t + 1).collect())
        };
        let mut out = bank(Reg::X, rv_abi::INT_ARGS);
        out.extend(bank(Reg::F, rv_abi::FLOAT_ARGS));
        out
    }

    /// The value an argument register passes, declaring its variable when
    /// the register still holds what it held at entry.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn arg_value(&mut self, r: Reg) -> Expr {
        let v = self.ex.env.get(Key::Rv(r));
        let v = self.ex.assumed(v);
        if v == Expr::Var(Key::Rv(r)) {
            let ty = match r {
                Reg::F(_) => Ty::F64,
                Reg::X(_) => self.word_ty(),
            };
            self.ex.declare(Key::Rv(r), ty);
        }
        v
    }

    /// The text a call names its callee by, and the import slot it reaches.
    ///
    /// # Arguments
    ///
    /// * `callee` - What it calls.
    fn callee_named(&self, callee: &Callee) -> (String, Option<u64>) {
        match callee {
            Callee::Direct(t) => {
                let reached = self
                    .ex
                    .ctx
                    .analysis
                    .function(*t)
                    .filter(|f| f.entry == *t)
                    .and_then(|f| f.thunk);
                let name = crate::analysis::name_of(self.ex.ctx.analysis, self.ex.ctx.overlay, *t);
                (
                    super::super::expr::bare(&name).into_owned(),
                    reached.or(Some(*t)),
                )
            }
            Callee::Through(e) => (format!("(*{})", e.render(&self.ex.names())), None),
            Callee::Builtin(..) => (String::new(), None),
        }
    }

    /// What a callee hands back.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    /// * `reached` - The import slot it reaches.
    fn returns(&self, target: Option<u64>, reached: Option<u64>) -> Returns {
        let ctx = &*self.ex.ctx;
        stated_returns(ctx, target, reached).unwrap_or_else(|| {
            let f = target.and_then(|t| ctx.analysis.function(abi::reached(ctx.analysis, t)));
            match f.map(|f| (f.returns_value, f.ret_float)) {
                Some((_, Some(bits))) => Returns::Float(bits),
                Some((Some(false), None)) => Returns::Nothing,
                Some((Some(true) | None, None)) | None => Returns::Int(self.w()),
            }
        })
    }

    /// The arguments a call passes, each with its register.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    /// * `reached` - The import slot it reaches.
    /// * `tail` - The transfer is a tail jump.
    fn arguments(
        &mut self,
        target: Option<u64>,
        reached: Option<u64>,
        tail: bool,
    ) -> Vec<(ArgAt, Expr)> {
        let (regs, stack) = self
            .callee_args(target, reached)
            .unwrap_or_else(|| (self.written_since_call(tail), 0));
        let mut out: Vec<(ArgAt, Expr)> = regs
            .into_iter()
            .map(|r| (ArgAt::Rv(r), self.arg_value(r)))
            .collect();
        let word = i64::from(self.w() / 8);
        out.extend(self.ex.stack_arguments(stack, word));
        for (_, e) in &out {
            self.ex.note_escape(e);
        }
        out
    }

    /// Lifts a call: writes out every value pending outside the registers
    /// the call changes, passes the callee its arguments, assigns its
    /// result, and forgets what the call may change.
    ///
    /// # Arguments
    ///
    /// * `i` - The `jal` or `jalr` that links.
    /// * `prev` - The instruction before it in its block.
    pub(super) fn call(&mut self, i: &Insn, prev: Option<&Insn>) {
        let through = if let ROp::Jalr { rs1, off, .. } = i.op {
            Some(self.jalr_target(rs1, off))
        } else {
            None
        };
        let constant = if let Some(Expr::Const(t)) = through {
            Some(t)
        } else {
            None
        };
        let target = super::transfer_target(prev, i, self.xlen).or(constant);
        let callee = match (target, through) {
            (Some(t), _) => Callee::Direct(t),
            (None, Some(e)) => Callee::Through(e),
            (None, None) => return self.unmodeled(i),
        };
        let dying: Vec<Key> = rv_abi::clobbered().map(Key::Rv).collect();
        let outlives: Vec<Key> = self
            .ex
            .env
            .vals
            .iter()
            .filter(|(k, v)| {
                !dying.contains(k)
                    && (matches!(k, Key::Slot(_))
                        || v.mem_dependent()
                        || v.any_var(&|x| dying.contains(&x) || matches!(x, Key::Slot(_))))
            })
            .map(|(k, _)| *k)
            .collect();
        for k in outlives {
            self.ex.materialize(k, &mut Vec::new(), None);
        }
        let (text, reached) = self.callee_named(&callee);
        let returns = self.returns(target, reached);
        let args = self.arguments(target, reached, false);
        let result = self.result_of(returns);
        if self.ex.emit {
            let names = self.ex.names();
            let mut rendered: Vec<String> = args.iter().map(|(_, e)| e.render(&names)).collect();
            self.ex.name_arguments(reached.or(target), &mut rendered);
            let call = abi::call_text(&text, &rendered);
            let line = if let Some((k, ty)) = result {
                if matches!(k, Key::Rv(Reg::F(_))) {
                    self.ex.ctx.reg_ty.entry(k).or_insert(ty);
                } else {
                    self.ex.note_result_type(target, reached, &text);
                }
                self.ex.declare(k, ty);
                format!("{} = {call};", names.key(k))
            } else {
                format!("{call};")
            };
            self.ex.lines.push(line);
        }
        let result = result.map(|(k, _)| k);
        self.ex
            .record_call(callee, args, result, None, false, Shown::Statement);
        self.after_call(result);
    }

    /// Forgets what a call may change: the registers it may change but
    /// the result; the slots the callee may read are recorded for slot
    /// liveness.
    ///
    /// # Arguments
    ///
    /// * `result` - The register the call's result is assigned to.
    fn after_call(&mut self, result: Option<Key>) {
        for r in rv_abi::clobbered() {
            let k = Key::Rv(r);
            self.ex.env.vals.remove(&k);
            self.ex.env.clobbered.insert(k);
        }
        if let Some(k) = result {
            self.ex.env.clobbered.remove(&k);
            self.ex.env.touched.insert(k);
            self.ex.env.result_in_rax = k == Key::Rv(Reg::X(rv_abi::FIRST_ARG));
        }
        self.ex.env.fresh.clear();
        self.ex.note_call_slots();
    }

    /// Lifts a jump out of the function as a tail call: the callee takes
    /// its arguments as a call's, and what it hands back is the function's
    /// result.
    ///
    /// # Arguments
    ///
    /// * `target` - Where it goes.
    pub(super) fn tail_call(&mut self, target: u64) {
        let callee = Callee::Direct(target);
        let (text, reached) = self.callee_named(&callee);
        let returns = self.returns(Some(target), reached);
        let args = self.arguments(Some(target), reached, true);
        self.ex.emit_tail(&text, &args, reached, returns);
        self.ex
            .record_call(callee, args, None, None, false, Shown::Tail);
    }

    /// Lifts a return: `return a0;` (or `fa0`) when the function hands a
    /// result back; a trap return is no function's and stays unmodeled.
    ///
    /// # Arguments
    ///
    /// * `i` - The `ret`, or a `jr t0` from a millicode call.
    pub(super) fn ret(&mut self, i: &Insn) {
        if i.op == ROp::TrapRet {
            return self.unmodeled(i);
        }
        if !self.ex.emit {
            return;
        }
        let ctx = &*self.ex.ctx;
        let back = Key::Rv(result_reg(ctx));
        let hands_back = !ctx.unused_result
            && (ctx.rax_written
                || ctx.ret_float
                || self.ex.env.result_in_rax
                || ctx.returns_value == Some(true));
        let float = ctx.ret_float;
        let value = match self.ex.env.vals.get(&back).cloned() {
            _ if !hands_back => None,
            Some(v) => Some(self.ex.assumed(v)),
            None => {
                let ty = if float { Ty::F64 } else { self.word_ty() };
                self.ex.declare(back, ty);
                Some(Expr::Var(back))
            }
        };
        if value.is_some() {
            self.ex.ctx.ret_bits = self.ex.ctx.ret_bits.max(self.ex.ctx.ret_lane);
        }
        let line = match &value {
            Some(v) => format!("return {};", v.render(&self.ex.names())),
            None => "return;".to_owned(),
        };
        self.ex.lines.push(line);
        self.ex.record(EffectKind::Return(value));
    }
}
