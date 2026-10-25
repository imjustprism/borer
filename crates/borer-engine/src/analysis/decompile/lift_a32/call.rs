//! Calls, tail calls and returns for the ARM32 lifter, as the procedure
//! call standard passes their values.
//!
//! A call passes what its callee takes: the registers its body reads as
//! parameters ([`super::shape::arg_regs`]), the positions an import's
//! declaration states, else the argument registers the caller wrote since
//! the last call. Before the call every value pending in a variable the
//! call leaves alone is written out; afterwards the registers a call may
//! change hold nothing but its result, in `r0`, `s0` or `d0`. A return
//! hands back `r0` (or `s0` or `d0` for a float) unless the function
//! returns nothing; a `pop` or load into `pc` restores what it loads first.

use super::super::Ctx;
use super::super::abi::{self, a32 as a32_abi};
use super::super::expr::{Expr, Key, Op, Ty, fold, sign_extend};
use super::super::lift::{
    self, ArgAt, Callee, EffectKind, Returns, Shown, SlotUse, stated_returns,
};
use super::Lift;
use super::shape::{arg_reg, arg_regs};
use crate::isa::a32::{Insn, Op as AOp, PC, Reg};

/// The register the function at hand hands its result back in.
///
/// # Arguments
///
/// * `ctx` - The function's state.
pub(in crate::analysis::decompile) fn result_key(ctx: &Ctx<'_>) -> Key {
    Key::A32(match (ctx.ret_float, ctx.ret_lane) {
        (true, 32) => Reg::S(0),
        (true, _) => Reg::D(0),
        (false, _) => Reg::R(0),
    })
}

/// The variable a call's result comes back in, and its type.
///
/// # Arguments
///
/// * `r` - What the callee hands back.
fn result_of(r: Returns) -> Option<(Key, Ty)> {
    match r {
        Returns::Nothing => None,
        Returns::Int(_) => Some((Key::A32(Reg::R(0)), Ty::U32)),
        Returns::Float(32) => Some((Key::A32(Reg::S(0)), Ty::F32)),
        Returns::Float(_) => Some((Key::A32(Reg::D(0)), Ty::F64)),
    }
}

/// Returns the argument words a run-time helper takes in `r0` to `r3`.
///
/// The helpers of the ARM run-time ABI and of Windows on ARM take them
/// under the base standard (no VFP registers): a 32-bit division two, a
/// 64-bit one or a 64-bit shift or multiply four, a conversion from a
/// 64-bit integer two, from a float one and from a double two.
///
/// # Arguments
///
/// * `name` - The callee's name.
///
/// # Returns
///
/// The words, or `None` for a name that is no such helper.
pub(super) fn runtime_words(name: &str) -> Option<u8> {
    let name = crate::analysis::bare_name(name);
    let name = name.split('@').next().unwrap_or(name);
    Some(match name {
        "__aeabi_idiv" | "__aeabi_uidiv" | "__aeabi_idivmod" | "__aeabi_uidivmod" | "__rt_sdiv"
        | "__rt_udiv" | "__aeabi_d2iz" | "__aeabi_d2uiz" | "__aeabi_l2f" | "__aeabi_ul2f"
        | "__aeabi_l2d" | "__aeabi_ul2d" | "__aeabi_d2lz" | "__aeabi_d2ulz" => 2,
        "__aeabi_ldivmod" | "__aeabi_uldivmod" | "__aeabi_lmul" | "__rt_sdiv64" | "__rt_udiv64" => {
            4
        }
        "__aeabi_llsl" | "__aeabi_llsr" | "__aeabi_lasr" => 3,
        "__aeabi_f2lz" | "__aeabi_f2ulz" | "__aeabi_i2d" | "__aeabi_ui2d" | "__aeabi_f2d" => 1,
        _ => return None,
    })
}

/// The remainder a division helper hands back in `r1` beside its
/// quotient: `__aeabi_idivmod` and `__aeabi_uidivmod` take the dividend
/// first, `__rt_sdiv` and `__rt_udiv` the divisor.
///
/// # Arguments
///
/// * `callee` - The callee's name as the call prints it.
/// * `args` - The arguments the call passes.
/// * `dying` - The registers the call changes.
///
/// # Returns
///
/// The remainder, or `None` for another callee, or operands that read a
/// register the call changes or memory, which no longer hold what the
/// call read once it returns.
fn remainder(callee: &str, args: &[(ArgAt, Expr)], dying: &[Key]) -> Option<Expr> {
    let (op, dividend_first) = match callee {
        "__aeabi_idivmod" => (Op::SRem, true),
        "__aeabi_uidivmod" => (Op::Rem, true),
        "__rt_sdiv" => (Op::SRem, false),
        "__rt_udiv" => (Op::Rem, false),
        _ => return None,
    };
    let [(_, x), (_, y)] = args else {
        return None;
    };
    if [x, y]
        .iter()
        .any(|e| e.mem_dependent() || e.any_var(&|k| dying.contains(&k)))
    {
        return None;
    }
    let (a, b) = if dividend_first { (x, y) } else { (y, x) };
    let signed = op == Op::SRem;
    let operand = |e: &Expr| {
        if signed {
            sign_extend(e.clone(), 32)
        } else {
            e.clone()
        }
    };
    Some(fold(op, operand(a), operand(b), 32))
}

impl Lift<'_, '_> {
    /// The argument registers a callee takes, when its body or a
    /// declaration says.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry, when the call names one.
    /// * `reached` - The import slot a stub reaches, when it reaches one.
    fn callee_args(&self, target: Option<u64>, reached: Option<u64>) -> Option<Vec<Reg>> {
        let ctx = &*self.ex.ctx;
        if let Some(t) = target
            && let Some(words) =
                runtime_words(&crate::analysis::name_of(ctx.analysis, ctx.overlay, t))
        {
            return Some((0..words).map(Reg::R).collect());
        }
        if let Some(p) = lift::import_prototype(ctx, reached.or(target)) {
            let count = usize::from(p.params);
            return Some((0..count).filter_map(|i| arg_reg(i, p.floats)).collect());
        }
        let t = target.map(|t| abi::reached(ctx.analysis, t))?;
        let f = ctx.analysis.function(t).filter(|f| f.thunk.is_none())?;
        arg_regs(ctx, f.entry).map(|a| a.to_vec())
    }

    /// The argument registers the caller set since the last call: the
    /// integer ones up to the highest set, and each floating one set.
    ///
    /// # Arguments
    ///
    /// * `tail` - The transfer is a tail jump, which hands on what the
    ///   function was passed too.
    fn written_since_call(&self, tail: bool) -> Vec<Reg> {
        let fresh = |r: Reg| {
            let k = Key::A32(r);
            self.ex.env.fresh.contains(&k) || (tail && self.ex.env.vals.contains_key(&k))
        };
        let mut out: Vec<Reg> = match (0..a32_abi::INT_ARGS).rev().find(|n| fresh(Reg::R(*n))) {
            Some(top) => (0..=top).map(Reg::R).collect(),
            None => Vec::new(),
        };
        let mut s = 0;
        while s < a32_abi::FLOAT_SINGLES {
            if s % 2 == 0 && fresh(Reg::D(s / 2)) && !fresh(Reg::S(s)) {
                out.push(Reg::D(s / 2));
                s += 2;
                continue;
            }
            if fresh(Reg::S(s)) {
                out.push(Reg::S(s));
            }
            s += 1;
        }
        out
    }

    /// The value an argument register passes, declaring its variable when
    /// the register still holds what it held at entry.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn arg_value(&mut self, r: Reg) -> Expr {
        let v = self.ex.env.get(Key::A32(r));
        let v = self.ex.assumed(v);
        if v == Expr::Var(Key::A32(r)) {
            let ty = match r {
                Reg::S(_) => Ty::F32,
                Reg::D(_) => Ty::F64,
                Reg::R(_) => Ty::U32,
            };
            self.ex.declare(Key::A32(r), ty);
        }
        v
    }

    /// The text a call names its callee by, and the import slot it reaches.
    ///
    /// # Arguments
    ///
    /// * `callee` - What it calls.
    fn callee_named(&self, callee: &Callee) -> (String, Option<u64>) {
        let names = self.ex.names();
        match callee {
            Callee::Direct(t) => {
                let reached = self
                    .ex
                    .ctx
                    .analysis
                    .function(*t)
                    .filter(|f| f.entry == *t)
                    .and_then(|f| f.thunk);
                (
                    super::super::expr::bare(&crate::analysis::name_of(
                        self.ex.ctx.analysis,
                        self.ex.ctx.overlay,
                        *t,
                    ))
                    .into_owned(),
                    reached.or(Some(*t)),
                )
            }
            Callee::Through(e) => (format!("(*{})", e.render(&names)), None),
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
                Some((Some(true) | None, None)) | None => Returns::Int(32),
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
        let regs = self
            .callee_args(target, reached)
            .unwrap_or_else(|| self.written_since_call(tail));
        let mut out: Vec<(ArgAt, Expr)> = regs
            .into_iter()
            .map(|r| (ArgAt::A32(r), self.arg_value(r)))
            .collect();
        let stack_args = target
            .and_then(|t| {
                super::shape::callee_shape(self.ex.ctx, abi::reached(self.ex.ctx.analysis, t))
            })
            .map_or(0, |s| i64::from(s.stack));
        if stack_args > 0
            && let Some(sp) = self.ex.env.sp
        {
            for n in 0..stack_args {
                let o = sp.saturating_add(4 * n);
                let k = Key::Slot(o);
                if !self.ex.slot_def.contains_key(&o) {
                    let width = self.ex.slot_use.entry(o).or_default();
                    *width = (*width).max(32);
                }
                let v = self
                    .ex
                    .env
                    .vals
                    .get(&k)
                    .cloned()
                    .unwrap_or_else(|| self.ex.env.get(k));
                out.push((ArgAt::Stack(4 * n, 32), self.ex.assumed(v)));
            }
        }
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
    /// * `i` - The `bl`, `blx` or conditional call.
    pub(super) fn call(&mut self, i: &Insn) {
        let target = i.target();
        let through = if let AOp::BlxReg { rm } = i.op {
            Some(rm)
        } else {
            None
        };
        if target.is_none() && through.is_none() {
            return self.unmodeled(i);
        }
        let stack_args = target
            .and_then(|t| {
                super::shape::callee_shape(self.ex.ctx, abi::reached(self.ex.ctx.analysis, t))
            })
            .map_or(0, |s| i64::from(s.stack));
        let stack_arg_slot = |k: &Key| {
            matches!(
                (k, self.ex.env.sp),
                (Key::Slot(o), Some(sp)) if *o >= sp && *o < sp.saturating_add(4 * stack_args)
            )
        };
        let dying: Vec<Key> = a32_abi::clobbered().map(Key::A32).collect();
        let outlives: Vec<Key> = self
            .ex
            .env
            .vals
            .iter()
            .filter(|(k, v)| {
                !dying.contains(k)
                    && ((!stack_arg_slot(k) && matches!(k, Key::Slot(_)))
                        || v.mem_dependent()
                        || v.any_var(&|x| dying.contains(&x)))
            })
            .map(|(k, _)| *k)
            .collect();
        let views: Vec<Key> = outlives
            .iter()
            .copied()
            .filter(|k| self.is_view(*k, &outlives))
            .collect();
        for k in outlives.iter().filter(|k| !views.contains(k)) {
            self.ex.materialize(*k, &mut Vec::new(), None);
        }
        for k in views {
            self.view_again(k);
        }
        let callee = match (target, through) {
            (Some(t), _) => Callee::Direct(t),
            (None, Some(r)) => Callee::Through(self.get(i, r)),
            (None, None) => return self.unmodeled(i),
        };
        let (text, reached) = self.callee_named(&callee);
        let returns = self.returns(target, reached);
        let args = self.arguments(target, reached, false);
        let result = result_of(returns);
        if self.ex.emit {
            let names = self.ex.names();
            let mut rendered: Vec<String> = args.iter().map(|(_, e)| e.render(&names)).collect();
            self.ex.name_arguments(reached.or(target), &mut rendered);
            let call = abi::call_text(&text, &rendered);
            let line = if let Some((k, ty)) = result {
                if matches!(k, Key::A32(Reg::S(_) | Reg::D(_))) {
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
        let rem = remainder(&text, &args, &dying);
        self.ex
            .record_call(callee, args, result, None, false, Shown::Statement);
        self.after_call(result);
        if let Some(rem) = rem {
            self.write(Reg::R(1), rem);
        }
    }

    /// Tells whether a register outliving a call holds only the other view
    /// of one that also does: a double made of its singles while one of
    /// them outlives too, or a single cut from its double while the double
    /// outlives and is no pair of singles. Writing out the register it is
    /// a view of writes it out too ([`Lift::view_again`]).
    ///
    /// # Arguments
    ///
    /// * `k` - The register.
    /// * `outlives` - Every register the call writes out.
    fn is_view(&self, k: Key, outlives: &[Key]) -> bool {
        let paired = |n: u8| {
            matches!(self.ex.env.vals.get(&Key::A32(Reg::D(n))),
                Some(Expr::Call(name, _)) if name == "__pair")
        };
        match k {
            Key::A32(Reg::D(n)) if n < 16 => {
                paired(n)
                    && (outlives.contains(&Key::A32(Reg::S(2 * n)))
                        || outlives.contains(&Key::A32(Reg::S(2 * n + 1))))
            }
            Key::A32(Reg::S(n)) => outlives.contains(&Key::A32(Reg::D(n / 2))) && !paired(n / 2),
            Key::A32(Reg::R(_) | Reg::D(_))
            | Key::Reg(_)
            | Key::A64(_)
            | Key::Slot(_)
            | Key::Global(..)
            | Key::Tmp(_)
            | Key::Param(_) => false,
        }
    }

    /// Takes a view ([`Lift::is_view`]) again from the registers it is a
    /// view of, once they are written out.
    ///
    /// # Arguments
    ///
    /// * `k` - The view.
    fn view_again(&mut self, k: Key) {
        match k {
            Key::A32(Reg::D(n)) => {
                let lo = self.ex.env.get(Key::A32(Reg::S(2 * n)));
                let hi = self.ex.env.get(Key::A32(Reg::S(2 * n + 1)));
                self.alias(Reg::D(n), Expr::Call("__pair".to_owned(), vec![lo, hi]));
            }
            Key::A32(Reg::S(n)) => {
                let d = self.ex.env.get(Key::A32(Reg::D(n / 2)));
                let v = if n % 2 == 0 {
                    super::super::lift_a64::mem::as_integer_bits(d, 32)
                } else {
                    Expr::Call("__hi32".to_owned(), vec![d])
                };
                self.alias(Reg::S(n), v);
            }
            Key::A32(Reg::R(_))
            | Key::Reg(_)
            | Key::A64(_)
            | Key::Slot(_)
            | Key::Global(..)
            | Key::Tmp(_)
            | Key::Param(_) => {}
        }
    }

    /// Forgets what a call may change: the registers it may change but
    /// the result, and the flags; the slots the callee may read are
    /// recorded for slot liveness.
    ///
    /// # Arguments
    ///
    /// * `result` - The register the call's result is assigned to.
    fn after_call(&mut self, result: Option<Key>) {
        for r in a32_abi::clobbered() {
            let k = Key::A32(r);
            self.ex.env.vals.remove(&k);
            self.ex.env.clobbered.insert(k);
        }
        if let Some(k) = result {
            self.ex.env.clobbered.remove(&k);
            self.ex.env.touched.insert(k);
            self.ex.env.result_in_rax = k == Key::A32(Reg::R(0));
        }
        self.ex.env.fresh.clear();
        self.ex.flags = super::super::expr::Flags::Unknown;
        self.fp_flags = super::super::expr::Flags::Unknown;
        let written = self
            .ex
            .slot_def
            .iter()
            .flat_map(|(&o, &b)| o..o.saturating_add(i64::from(b / 8).max(1)))
            .collect();
        match (self.ex.env.sp, self.ex.ctx.escape_floor) {
            (Some(_), Some(f)) => self
                .ex
                .call_uses
                .push((SlotUse::Window(f, i64::MAX), written)),
            (Some(_), None) => {}
            (None, _) => self.ex.call_uses.push((SlotUse::All, written)),
        }
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
        if self.ex.emit {
            let names = self.ex.names();
            let mut rendered: Vec<String> = args.iter().map(|(_, e)| e.render(&names)).collect();
            self.ex.name_arguments(reached, &mut rendered);
            let call = abi::call_text(&text, &rendered);
            if !self.ex.ctx.unused_result && returns != Returns::Nothing {
                self.ex.lines.push(format!("return {call};"));
            } else {
                self.ex.lines.push(format!("{call};"));
                self.ex.lines.push("return;".to_owned());
            }
        }
        self.ex
            .record_call(callee, args, None, None, false, Shown::Tail);
    }

    /// Lifts a return: the loads of a `pop` or load into `pc` first, then
    /// `return r0;` (or `s0`, `d0`) when the function hands a result back.
    ///
    /// # Arguments
    ///
    /// * `i` - The `bx lr`, `pop {..., pc}`, `ldr pc, [sp], #4` or `mov
    ///   pc, lr`.
    pub(super) fn ret(&mut self, i: &Insn) {
        if let AOp::Ldm {
            rn,
            regs,
            wback,
            block,
        } = i.op
        {
            if self
                .load_multiple(i, rn, regs & 0x7fff, wback, block)
                .is_none()
            {
                return self.unmodeled(i);
            }
        } else if let AOp::Load { rt: PC, addr, .. } = i.op
            && let (_, Some((r, a))) = self.address(i, addr)
        {
            self.write(r, a);
        }
        if !self.ex.emit {
            return;
        }
        let ctx = &*self.ex.ctx;
        let back = result_key(ctx);
        let hands_back = !ctx.unused_result
            && (ctx.rax_written
                || ctx.ret_float
                || self.ex.env.result_in_rax
                || ctx.returns_value == Some(true));
        let value = match self.ex.env.vals.get(&back).cloned() {
            _ if !hands_back => None,
            Some(v) => Some(self.ex.assumed(v)),
            None => {
                let ty = if back == Key::A32(Reg::S(0)) {
                    Ty::F32
                } else if back == Key::A32(Reg::D(0)) {
                    Ty::F64
                } else {
                    Ty::U32
                };
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
