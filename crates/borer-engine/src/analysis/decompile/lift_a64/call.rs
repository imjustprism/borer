//! Calls, tail calls and returns for the arm64 lifter, as the arm64
//! procedure call standard (AAPCS64) passes their values.
//!
//! A call passes what its callee takes: the positions a declaration states
//! (a prototype stated for the callee, the prototype of the import its stub
//! or slot reaches), else the ones the callee's body reads
//! ([`shape::callee_shape`]), else the argument registers the caller wrote
//! since the last call, up to the highest. Integer positions travel in `x0`
//! to `x7`, floating ones in `v0` to `v7`, and a callee that writes its
//! result through `x8` takes that too, last. A variadic callee's variable
//! arguments are the ones the caller wrote past the fixed ones: on the
//! stack, a word each from the stack pointer up, on Apple platforms; in the
//! argument registers elsewhere. Before the call every value pending in a
//! variable the call leaves alone is written out, so the text holds what
//! the callee may read, and the arguments are read after that; the
//! registers a call may change hold nothing afterwards but the result, in
//! `x0`, or in `v0` for a float, unless the callee returns nothing.
//!
//! A return hands back `x0` (or `v0`), unless the function returns
//! nothing; a function whose callers read `x1` after calling it hands a
//! second result back there, which its text sets before each `return`.

use super::super::abi::{self, a64 as a64_abi};
use super::super::expr::{Expr, Key, Ty};
use super::super::lift::{ArgAt, Callee, EffectKind, Returns, Shown, SlotUse, stated_returns};
use super::Lift;
use super::shape::{self, FLOAT_ARGS, INT_ARGS, RESULT_REG, arg_reg};
use crate::isa::a64::{Insn, Opnd, Reg};
use crate::program::BinaryFormat;

/// What a caller knows a callee takes and hands back.
#[derive(Debug, Clone, Copy)]
struct Signature {
    /// The positions it takes and a bit per floating one, when a
    /// declaration or its body says.
    args: Option<(usize, u8)>,
    /// A variable list follows the fixed positions.
    variadic: bool,
    /// It takes the address to write its result at in `x8`.
    result_ptr: bool,
    /// What it hands back.
    returns: Returns,
}

/// The import slot a call through a register reaches, when the register
/// holds what the code loaded from one.
///
/// # Arguments
///
/// * `v` - The register's value.
fn slot_of(v: &Expr) -> Option<u64> {
    if let Expr::Var(Key::Global(a, 64)) = v {
        return Some(*a);
    }
    if let Expr::Deref(a, Ty::U64) = v
        && let Expr::Const(a) = a.as_ref()
    {
        return Some(*a);
    }
    None
}

impl Lift<'_, '_> {
    /// Reads what a callee takes and hands back.
    ///
    /// A linkage stub takes and hands back what the function its slot
    /// binds does ([`abi::reached`]).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry, when the call names one.
    /// * `reached` - The callee's entry or the import slot the call goes
    ///   through.
    fn signature(&self, target: Option<u64>, reached: Option<u64>) -> Signature {
        let ctx = &*self.ex.ctx;
        let target = target.map(|t| abi::reached(ctx.analysis, t));
        let declared = target
            .and_then(|t| shape::declared_callee(ctx, t))
            .or_else(|| {
                reached
                    .filter(|r| Some(*r) != target)
                    .and_then(|r| shape::declared_callee(ctx, r))
            });
        let body = target.and_then(|t| shape::callee_shape(ctx, t));
        let result_ptr = body.as_ref().is_some_and(|s| s.result_param.is_some());
        let args = declared
            .map(|(count, floats, _)| (count, floats))
            .or_else(|| {
                body.as_ref().map(|s| {
                    (
                        s.count - usize::from(s.result_param.is_some()),
                        s.float_mask.unwrap_or(0),
                    )
                })
            });
        let variadic =
            declared.map_or_else(|| body.as_ref().is_some_and(|s| s.variadic), |(_, _, v)| v);
        let callee = target.and_then(|t| ctx.analysis.function(t));
        let returns = stated_returns(ctx, target, reached).unwrap_or_else(|| {
            match callee.map(|f| (f.returns_value, f.ret_float)) {
                Some((_, Some(bits))) => Returns::Float(bits),
                Some((Some(false), None)) => Returns::Nothing,
                Some((Some(true) | None, None)) | None => Returns::Int(64),
            }
        });
        Signature {
            args,
            variadic,
            result_ptr,
            returns,
        }
    }

    /// The value an argument register passes: what is pending in it, else
    /// the register's own text variable, declared.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn arg_value(&mut self, r: Reg) -> Expr {
        let v = self.read(r);
        if v == Expr::Var(Key::A64(r)) {
            let ty = if matches!(r, Reg::V(_)) {
                Ty::F64
            } else {
                Ty::U64
            };
            self.ex.declare(Key::A64(r), ty);
        }
        v
    }

    /// The registers of one sequence the caller set for a call, from `from`
    /// up to the highest one set, below `limit`: written since the last
    /// call, or for a tail jump also still holding what the function was
    /// passed, which the jump hands on.
    ///
    /// # Arguments
    ///
    /// * `make` - Names the sequence's `n`th register.
    /// * `from` - The first register number looked at.
    /// * `limit` - One past the last.
    /// * `tail` - The transfer is a tail jump.
    fn written_since_call(&self, make: fn(u8) -> Reg, from: u8, limit: u8, tail: bool) -> Vec<Reg> {
        let fresh = |n: u8| {
            let k = Key::A64(make(n));
            self.ex.env.fresh.contains(&k) || (tail && self.ex.env.vals.contains_key(&k))
        };
        let Some(top) = (from..limit).rev().find(|n| fresh(*n)) else {
            return Vec::new();
        };
        (from..=top).map(make).collect()
    }

    /// The arguments a call passes, each with its register, read where the
    /// call stands.
    ///
    /// # Arguments
    ///
    /// * `sig` - What the callee takes.
    /// * `tail` - The transfer is a tail jump, which hands on what the
    ///   function was passed as well as what it set.
    ///
    /// # Returns
    ///
    /// The register arguments in position order, the indirect result's
    /// address last, and the stack words of a variadic call on an Apple
    /// platform after them, with their offsets above the stack pointer.
    fn arguments(&mut self, sig: Signature, tail: bool) -> Vec<(ArgAt, Expr)> {
        let (fixed, floats) = sig.args.unwrap_or((0, 0));
        let mut regs: Vec<Reg> = (0..fixed).filter_map(|p| arg_reg(p, floats)).collect();
        let ints = regs.iter().filter(|r| matches!(r, Reg::X(_))).count();
        let fls = regs.len() - ints;
        let apple = self.ex.ctx.program.format == BinaryFormat::MachO;
        let windows = self.ex.ctx.program.format == BinaryFormat::Pe;
        let mut stack = Vec::new();
        if sig.args.is_none() || (sig.variadic && !apple) {
            let from_x = u8::try_from(ints).unwrap_or(INT_ARGS);
            regs.extend(self.written_since_call(Reg::X, from_x, INT_ARGS, tail));
            if !(sig.variadic && windows) {
                let from_v = u8::try_from(fls).unwrap_or(FLOAT_ARGS);
                regs.extend(self.written_since_call(Reg::V, from_v, FLOAT_ARGS, tail));
            }
        } else if sig.variadic
            && let Some(sp) = self.ex.env.sp
        {
            /// Most variable arguments read off the stack.
            const STACK_VARARGS_MAX: i64 = 16;
            let word = self.ex.ctx.conv.word;
            for n in 0..STACK_VARARGS_MAX {
                let k = Key::Slot(sp + n * word);
                if !self.ex.env.fresh.contains(&k) {
                    break;
                }
                stack.push((ArgAt::Stack(n * word, 64), self.ex.env.get(k)));
            }
        }
        if sig.result_ptr {
            regs.push(Reg::X(RESULT_REG));
        }
        let mut out: Vec<(ArgAt, Expr)> = regs
            .into_iter()
            .map(|r| (ArgAt::A64(r), self.arg_value(r)))
            .collect();
        out.extend(stack);
        for (_, e) in &out {
            self.ex.note_escape(e);
        }
        out
    }

    /// The text a call names its callee by, and the import slot it
    /// reaches, if any.
    ///
    /// # Arguments
    ///
    /// * `callee` - What it calls.
    fn callee_named(&self, callee: &Callee) -> (String, Option<u64>) {
        let names = self.ex.names();
        match callee {
            Callee::Direct(t) => (
                super::super::expr::bare(&crate::analysis::name_of(
                    self.ex.ctx.analysis,
                    self.ex.ctx.overlay,
                    *t,
                ))
                .to_owned(),
                Some(*t),
            ),
            Callee::Through(e) => match slot_of(e).and_then(|s| Some((names.import_at(s)?, s))) {
                Some((name, slot)) => (name, Some(slot)),
                None => (format!("(*{})", e.render(&names)), slot_of(e)),
            },
            Callee::Builtin(..) => (String::new(), None),
        }
    }

    /// Lifts a call: writes out every value pending outside the registers
    /// the call changes, passes the callee its arguments, assigns its
    /// result, and forgets what the call may change.
    ///
    /// # Arguments
    ///
    /// * `i` - The `bl` or `blr`.
    pub(super) fn call(&mut self, i: &Insn) {
        let target = i.target();
        let through = match i.operands[0] {
            Opnd::Reg { reg, .. } if target.is_none() => Some(reg),
            Opnd::Reg { .. }
            | Opnd::None
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::PcRel(_)
            | Opnd::Mem(_)
            | Opnd::Cond(_)
            | Opnd::Other => None,
        };
        if target.is_none() && through.is_none() {
            return self.unmodeled(i);
        }
        let dying: Vec<Key> = a64_abi::clobbered().map(Key::A64).collect();
        let outlives: Vec<Key> = self
            .ex
            .env
            .vals
            .iter()
            .filter(|(k, v)| {
                !dying.contains(k)
                    && (matches!(k, Key::Slot(_))
                        || v.mem_dependent()
                        || v.any_var(&|x| dying.contains(&x)))
            })
            .map(|(k, _)| *k)
            .collect();
        for k in outlives {
            self.ex.materialize(k, &mut Vec::new(), None);
        }
        let callee = match (target, through) {
            (Some(t), _) => Callee::Direct(t),
            (None, Some(r)) => Callee::Through(self.read(r)),
            (None, None) => return self.unmodeled(i),
        };
        let (text, reached) = self.callee_named(&callee);
        let sig = self.signature(target, reached);
        let args = self.arguments(sig, false);
        let result = match sig.returns {
            Returns::Nothing => None,
            Returns::Int(_) => Some((Key::A64(Reg::X(0)), Ty::U64)),
            Returns::Float(32) => Some((Key::A64(Reg::V(0)), Ty::F32)),
            Returns::Float(_) => Some((Key::A64(Reg::V(0)), Ty::F64)),
        };
        if self.ex.emit {
            let names = self.ex.names();
            let mut rendered: Vec<String> = args.iter().map(|(_, e)| e.render(&names)).collect();
            self.ex.name_arguments(reached.or(target), &mut rendered);
            let call = format!("{text}({})", rendered.join(", "));
            let line = if let Some((k, ty)) = result {
                if matches!(k, Key::A64(Reg::V(_))) {
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

    /// Forgets what a call may change: the registers the standard lets a
    /// callee change, but the result it assigns, and the flags; nothing
    /// written before the call is set for the next one, and the slots the
    /// callee may read are recorded for slot liveness.
    ///
    /// # Arguments
    ///
    /// * `result` - The register the call's result is assigned to.
    fn after_call(&mut self, result: Option<Key>) {
        for r in a64_abi::clobbered() {
            let k = Key::A64(r);
            self.ex.env.vals.remove(&k);
            self.ex.env.narrow.remove(&k);
            self.ex.env.clobbered.insert(k);
        }
        if let Some(k) = result {
            self.ex.env.clobbered.remove(&k);
            self.ex.env.touched.insert(k);
            self.ex.env.result_in_rax = k == Key::A64(Reg::X(0));
        }
        self.ex.env.fresh.clear();
        self.ex.flags = super::super::expr::Flags::Unknown;
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
        let sig = self.signature(Some(target), reached);
        let args = self.arguments(sig, true);
        if self.ex.emit {
            let names = self.ex.names();
            let mut rendered: Vec<String> = args.iter().map(|(_, e)| e.render(&names)).collect();
            self.ex.name_arguments(reached, &mut rendered);
            let call = format!("{text}({})", rendered.join(", "));
            if !self.ex.ctx.unused_result && sig.returns != Returns::Nothing {
                self.ex.lines.push(format!("return {call};"));
            } else {
                self.ex.lines.push(format!("{call};"));
                self.ex.lines.push("return;".to_owned());
            }
        }
        self.ex
            .record_call(callee, args, None, None, false, Shown::Tail);
    }

    /// Lifts a return: `return x0;` (or `v0` for a float) when the function
    /// hands a result back, with a second result in `x1` set first when the
    /// callers read one.
    ///
    /// `x0` is also the first argument's register, so a value it still
    /// holds from the entry is a result only where something says the
    /// function hands one back: an instruction of its own writes `x0`, a
    /// call's result reaches the return, or its callers read one.
    pub(super) fn ret(&mut self) {
        if !self.ex.emit {
            return;
        }
        let ctx = &*self.ex.ctx;
        let back = Key::A64(if ctx.ret_float { Reg::V(0) } else { Reg::X(0) });
        let hands_back = !ctx.unused_result
            && (ctx.rax_written
                || ctx.ret_float
                || self.ex.env.result_in_rax
                || ctx.returns_value == Some(true));
        let value = match self.ex.env.vals.get(&back).cloned() {
            _ if !hands_back => None,
            Some(v) => Some(self.ex.assumed(v)),
            None => {
                let ty = if ctx.ret_float { Ty::F64 } else { Ty::U64 };
                self.ex.declare(back, ty);
                Some(Expr::Var(back))
            }
        };
        if value.is_some() {
            self.ex.ctx.ret_bits = self.ex.ctx.ret_bits.max(self.ex.ctx.ret_lane);
        }
        let second = Key::A64(Reg::X(1));
        let value = match self.ex.env.vals.get(&second).cloned() {
            Some(v) if self.ex.ctx.ret_rdx && v != Expr::Var(second) => {
                let value = match value {
                    Some(r) if r.mentions(second) => Some(self.ex.tmp_of(&r, Ty::U64)),
                    other => other,
                };
                self.ex.declare(second, Ty::U64);
                let names = self.ex.names();
                let line = format!("{} = {};", names.key(second), v.render(&names));
                self.ex.lines.push(line);
                self.ex.record(EffectKind::Assign(second, v, 64));
                value
            }
            Some(_) | None => value,
        };
        let line = match &value {
            Some(v) => format!("return {};", v.render(&self.ex.names())),
            None => "return;".to_owned(),
        };
        self.ex.lines.push(line);
        self.ex.record(EffectKind::Return(value));
    }
}
