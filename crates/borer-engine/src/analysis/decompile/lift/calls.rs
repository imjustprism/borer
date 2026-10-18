//! Calls: arguments, callee arity and prototypes, virtual targets, and what a
//! call leaves behind.

use super::*;
use crate::analysis::returns::Sse;
use crate::analysis::x87;

impl<'a> Exec<'_, 'a> {
    /// The argument register an indirect call or jump goes through.
    ///
    /// `call [r8]` with the vtable pointer in `r8`, or `jmp rdx`: the
    /// register is the address, not an argument, and a compiler that
    /// needed the slot for an argument would have used `rax`.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call or jump.
    pub(super) fn through_register(&self, instr: &Instruction) -> Option<Register> {
        let r = match instr.op0_kind() {
            OpKind::Register => instr.op0_register(),
            OpKind::Memory => instr.memory_base(),
            _ => return None,
        };
        if r == Register::None || r == Register::RIP {
            return None;
        }
        let r = canon(r, self.bitness());
        self.ctx.conv.slot(r).map(|_| r)
    }

    /// Renders the known argument values of a call positionally.
    ///
    /// A register never written in this function is one of our own
    /// parameters when it was detected as such; the list stops at the first
    /// unknown register so partial lists stay positionally honest.
    pub(super) fn args(&mut self) -> Vec<String> {
        self.args_for(None).0
    }

    /// Renders the register arguments of a call to `target`.
    ///
    /// A callee whose arity is known gets that many: an import's prototype
    /// says it, a declared signature or the callee's own signature when it
    /// has a body ([`Exec::callee_reg_params`]), the overrides with bodies
    /// for a virtual slot ([`Exec::family_arity`]). Each argument is the
    /// register's value, or its name when the caller wrote it out
    /// ([`Exec::names_register`]); a register a call clobbered since is no
    /// argument, and the list stops there, so a partial list stays
    /// positionally honest.
    ///
    /// A slot the callee takes whose register the environment holds no
    /// value for still gets its argument while one is known: a register
    /// the caller never wrote and no call clobbered holds the caller's own
    /// parameter of that slot, when its signature lists one, and a slot
    /// the callee's body never reads passes whatever the register holds,
    /// named by the register. Neither claims a value the lifter tracked:
    /// the register is the entry's, which its environment does not name.
    /// A slot the callee reads that nothing names still does not end the
    /// list while a later slot carries a value: the unnamed register is
    /// declared under its own name instead, because an earlier call's
    /// unknown second result must not drop the arguments set behind it.
    /// On a 32-bit target the stack words count as later slots, so a
    /// `__thiscall` callee whose `ecx` a call clobbered gets `ecx` first
    /// and its stack arguments after it, never shifted into `this`.
    ///
    /// A callee of unknown arity without a body gets only the registers
    /// written for it, in the call's own block since the last call, the
    /// object a call through a vtable is made on, and the caller's own
    /// `this` when the callee is a method of the caller's class, up to the
    /// first register that is none of these: what a register merely holds
    /// from the caller's own caller is no argument. A tail jump hands every
    /// register on as it stands, so it passes the caller's own parameters
    /// too, and a variadic callee's variable arguments are what the caller
    /// set. The count of stack arguments rendered comes back with the list,
    /// so the call can leave those slots out of what it stores before the
    /// call. A stack address in any argument register escapes regardless
    /// of the count: a local whose address the callee may hold must be
    /// reloaded after the call.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    ///
    /// # Returns
    ///
    /// The rendered arguments, how many of them are stack arguments, and,
    /// in the emission pass, each argument's value with where the callee
    /// finds it (empty in the dataflow pass).
    pub(super) fn args_for(
        &mut self,
        target: Option<u64>,
    ) -> (Vec<String>, usize, Vec<(ArgAt, Expr)>) {
        let cap = self.callee_reg_params(target);
        let variadic = self.callee_variadic(target);
        let prototype = self.callee_prototype(target);
        let stated = cap
            .or_else(|| self.callee_import_arity(target).map(usize::from))
            .or_else(|| (self.arity_floor > 0).then_some(self.arity_floor));
        let floats = self.callee_float_slots(target);
        let method = self.same_class(target);
        let stack: Vec<Expr> = self.outgoing_stack_args(target);
        let word = self.ctx.conv.word;
        let first = self
            .env
            .sp
            .map(|sp| sp + if self.forwarding { word } else { 0 } + self.ctx.conv.shadow);
        for (i, e) in (0i64..).zip(&stack) {
            let own = first.map(|f| f + i * word);
            if matches!(e, Expr::Deref(a, _) if own.is_some_and(|o| **a == Expr::Sp(o))) {
                continue;
            }
            self.note_escape(e);
        }
        let n = self.names();
        let mut out = Vec::new();
        let mut values = Vec::new();
        let emit = self.emit;
        let mut open = true;
        if self.bitness() == 32 {
            let regs32 = match prototype {
                Some(p) => usize::from(p.this),
                None => cap.unwrap_or(usize::from(target.is_none() || method)),
            };
            let known = cap.is_some() || prototype.is_some();
            let regs = FASTCALL_X86.args.get(..regs32).unwrap_or(FASTCALL_X86.args);
            for (i, r) in regs.iter().enumerate() {
                let k = Key::Reg(*r);
                let value = self.env.vals.get(&k).cloned();
                let passed = known || self.passes(k, value.as_ref(), i == 0 && method);
                let follows = !stack.is_empty()
                    || regs.iter().skip(i + 1).any(|r| {
                        let k = Key::Reg(*r);
                        self.env.vals.contains_key(&k) || self.names_register(k)
                    });
                match value {
                    Some(e) if passed => {
                        self.note_escape(&e);
                        out.push(e.render(&n));
                        if emit {
                            values.push((ArgAt::Reg(*r), e));
                        }
                    }
                    None if passed && self.names_register(k) => {
                        out.push(n.key(k));
                        if emit {
                            values.push((ArgAt::Reg(*r), Expr::Var(k)));
                        }
                    }
                    None if known && follows => {
                        self.declare(k, self.word_ty());
                        out.push(n.key(k));
                        if emit {
                            values.push((ArgAt::Reg(*r), Expr::Var(k)));
                        }
                    }
                    Some(_) | None => break,
                }
            }
        }
        let reg_slots = if self.bitness() == 32 {
            0
        } else {
            self.ctx.conv.reg_args()
        };
        for i in 0..reg_slots {
            let Some(r) = self.ctx.conv.arg_reg(i, floats) else {
                continue;
            };
            let k = Key::Reg(r);
            let value = match self.env.vals.get(&k) {
                Some(Expr::Var(Key::Slot(o)))
                    if self.env.slot_bits.get(o).is_some_and(|b| *b <= 32) =>
                {
                    Some(Expr::Var(Key::Slot(*o)))
                }
                Some(_) if r.is_gpr() && target.is_some_and(|t| reads_whole(self.ctx, t, r)) => {
                    Some(self.full_value(k))
                }
                held => held.cloned(),
            };
            if let Some(e) = &value {
                self.note_escape(e);
            }
            if self.call_through == Some(r) {
                open = false;
            }
            let takes = stated.map(|c| i < c);
            if !open || (takes == Some(false) && !variadic) {
                continue;
            }
            let bridged = stated.is_none() && self.later_set_here(i, floats);
            let takes = if bridged { Some(true) } else { takes };
            if takes != Some(true) && !self.passes(k, value.as_ref(), i == 0 && method) {
                open = false;
                continue;
            }
            match value {
                Some(e) => {
                    let e = strip_own_merge(&e, r);
                    out.push(e.render(&n));
                    if emit {
                        values.push((ArgAt::Reg(r), e));
                    }
                }
                None if takes == Some(true) && self.later_argument_binds(i, floats) => {
                    self.declare(k, self.word_ty());
                    out.push(n.key(k));
                }
                None if self.names_register(k) => {
                    out.push(n.key(k));
                    if emit {
                        values.push((ArgAt::Reg(r), Expr::Var(k)));
                    }
                }
                None if takes == Some(true) && self.holds_own_param(k, i) => {
                    out.push(n.key(Key::Param(u8::try_from(i).unwrap_or(u8::MAX))));
                }
                None if takes == Some(true) && self.callee_skips(target, r) => {
                    self.declare(k, self.word_ty());
                    out.push(n.key(k));
                }
                None => open = false,
            }
        }
        let rendered = if open { stack.len() } else { 0 };
        self.args_short = self
            .call_stack_args(target)
            .and_then(|c| usize::try_from(c).ok())
            .is_some_and(|c| rendered < c);
        if open {
            out.extend(stack.iter().map(|e| e.render(&n)));
            if emit {
                let first = if self.forwarding { word } else { 0 } + self.ctx.conv.shadow;
                let sp = self.env.sp;
                let full = u8::try_from(word * 8).unwrap_or(64);
                values.extend((0i64..).zip(stack).map(|(i, e)| {
                    let at = first + i * word;
                    let bits = sp
                        .and_then(|sp| self.env.slot_bits.get(&(sp + at)))
                        .copied()
                        .unwrap_or(full);
                    (ArgAt::Stack(at, bits), e)
                }));
            }
        }
        (out, rendered, values)
    }

    /// Tells whether the text names what an argument register holds when
    /// the environment holds no value for it: the caller wrote it out under
    /// its own name, and no call clobbered it since on any path
    /// ([`Env::clobbered`]). A register only a call left behind, or one no
    /// statement writes, holds nothing the text can name.
    ///
    /// # Arguments
    ///
    /// * `k` - The argument register.
    fn names_register(&self, k: Key) -> bool {
        self.env.fresh.contains(&k)
            || (self.env.touched.contains(&k) && !self.env.clobbered.contains(&k))
    }

    /// Tells whether an argument slot after `from` carries a value or a
    /// name, so an unnamed slot before it must not close the call's list.
    ///
    /// # Arguments
    ///
    /// * `from` - The slot the list is at.
    /// * `floats` - The callee's float slots, as [`Self::args_for`] read them.
    fn later_argument_binds(&self, from: usize, floats: u8) -> bool {
        (from + 1..self.ctx.conv.reg_args()).any(|j| {
            let Some(r) = self.ctx.conv.arg_reg(j, floats) else {
                return false;
            };
            let k = Key::Reg(r);
            self.env.vals.contains_key(&k) || self.names_register(k)
        })
    }

    /// Tells whether an argument slot after `from` holds a register the
    /// caller wrote for the call being lifted, in its block since the last
    /// call, short of the register the call goes through: a callee of
    /// unknown arity takes every slot up to it.
    ///
    /// # Arguments
    ///
    /// * `from` - The slot the list is at.
    /// * `floats` - The callee's float slots, as [`Self::args_for`] read them.
    fn later_set_here(&self, from: usize, floats: u8) -> bool {
        (from + 1..self.ctx.conv.reg_args())
            .map_while(|j| {
                self.ctx
                    .conv
                    .arg_reg(j, floats)
                    .filter(|r| self.call_through != Some(*r))
            })
            .any(|r| {
                let k = Key::Reg(r);
                self.env.fresh.contains(&k) && self.written_here.contains(&k)
            })
    }

    /// Tells whether an argument register still holds the caller's own
    /// parameter of its slot: nothing wrote it and no call clobbered it,
    /// and the caller's signature lists the slot (a parameter read at a
    /// later position, or any on the stack, lists every register slot).
    ///
    /// # Arguments
    ///
    /// * `k` - The argument register.
    /// * `slot` - Its position in the call's argument list.
    fn holds_own_param(&self, k: Key, slot: usize) -> bool {
        !self.env.touched.contains(&k)
            && !self.env.clobbered.contains(&k)
            && (self.ctx.stack_params > 0
                || self.ctx.params.iter().any(|r| {
                    self.ctx
                        .conv
                        .param_pos(*r, &self.ctx.params)
                        .is_some_and(|s| s >= slot)
                }))
    }

    /// Tells whether a callee with a body never reads an argument register:
    /// its own parameters, as its signature reads them, leave it out.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    /// * `r` - The argument register.
    fn callee_skips(&self, target: Option<u64>, r: Register) -> bool {
        target
            .and_then(|t| callee_shape(self.ctx, t))
            .is_some_and(|shape| !shape.params.contains(&r))
    }

    /// Tells whether an argument register goes to a callee whose arity
    /// nothing states: the caller wrote it for this call (in the call's
    /// block since the last call), it holds the object a call through a
    /// vtable is made on, it holds the caller's own `this` and the callee
    /// is a method of the caller's class, or a tail jump hands on the
    /// caller's own parameter in it.
    ///
    /// # Arguments
    ///
    /// * `k` - The argument register.
    /// * `value` - What the environment holds for it.
    /// * `method_this` - The register is the first argument of a call to a
    ///   method of the caller's own class.
    fn passes(&self, k: Key, value: Option<&Expr>, method_this: bool) -> bool {
        let receiver = self
            .receiver
            .as_ref()
            .is_some_and(|recv| value.map_or(*recv == Expr::Var(k), |v| v == recv));
        let own = self.forwarding && matches!(k, Key::Reg(r) if self.ctx.params.contains(&r));
        let this = method_this
            && self.ctx.this_param
            && value.is_some_and(|v| *v == Expr::Var(Key::Param(0)));
        let set_here = self.env.fresh.contains(&k) && self.written_here.contains(&k);
        set_here || receiver || own || this
    }

    /// Tells whether a callee is a method of the caller's own class: both
    /// names are qualified by the same class.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    fn same_class(&self, target: Option<u64>) -> bool {
        let Some(t) = target else {
            return false;
        };
        let own = crate::analysis::classes::class_of(&self.ctx.own_name);
        let theirs = name_of(self.ctx.analysis, self.ctx.overlay, t);
        own.is_some() && own == crate::analysis::classes::class_of(bare(&theirs))
    }

    /// Reads the outgoing stack arguments a call passes above its register slots.
    ///
    /// The arguments the callee is known to take are read, so a slot the
    /// caller happens to have written for its own use is never mistaken for
    /// one; the run stops at the first slot holding nothing, because a gap
    /// means the values after it cannot be placed with confidence. A 64-bit
    /// callee nothing states the arity of takes the outgoing slots the
    /// caller wrote for it, in the call's block since the last call
    /// ([`Env::fresh`]), up to the first it did not: the outgoing area holds
    /// nothing else. A variadic callee takes its fixed ones and those.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    ///
    /// # Returns
    ///
    /// The argument values in order, empty when the callee takes no stack
    /// arguments, when nothing says it does, or when the stack pointer is
    /// not tracked at the call.
    pub(super) fn outgoing_stack_args(&mut self, target: Option<u64>) -> Vec<Expr> {
        let stated = self.call_stack_args(target);
        let Some(sp) = self.env.sp else {
            return Vec::new();
        };
        let word = self.ctx.conv.word;
        let base = if self.forwarding { sp + word } else { sp } + self.ctx.conv.shadow;
        let slot = |i: i64| base + i * word;
        let set: i64 = if self.bitness() == 32 {
            i64::from(self.args_pushed)
        } else {
            (0..STACK_ARG_WINDOW / word)
                .take_while(|i| {
                    let o = slot(*i);
                    self.env.fresh.contains(&Key::Slot(o)) && self.slot_def.contains_key(&o)
                })
                .count()
                .try_into()
                .unwrap_or(0)
        };
        let variadic = !self.forwarding && self.callee_variadic(target);
        let count = match stated {
            Some(c) if variadic => i64::from(c).max(set),
            Some(c) => i64::from(c),
            None if self.bitness() == 64 && !self.forwarding => set,
            None => return Vec::new(),
        };
        let mut out = Vec::new();
        for i in 0..count {
            let o = slot(i);
            let k = Key::Slot(o);
            let e = match self.env.vals.get(&k).cloned() {
                Some(e) if self.is_save(&e) => break,
                Some(e) => {
                    if !self.slot_def.contains_key(&o) {
                        let word = self.word_ty().bits();
                        let widest = self.slot_use.entry(o).or_default();
                        *widest = (*widest).max(word);
                    }
                    e
                }
                None if self.forwarding
                    || stated.is_none()
                    || self.env.fresh.contains(&k)
                    || self.ctx.declared.contains_key(&k) =>
                {
                    self.slot_read(o, self.word_ty())
                }
                None => break,
            };
            out.push(e);
        }
        out
    }

    /// Returns how many stack words the call being lifted passes.
    ///
    /// What the callee is stated to read ([`Exec::callee_stack_args`]),
    /// or the words its caller cleans up after it when those are more
    /// ([`Exec::cleaned`]); for an unknown callee on a 32-bit target, what
    /// was pushed for it since the last call.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct, or the
    ///   import slot it calls through.
    ///
    /// # Returns
    ///
    /// The count, or `None` when nothing states it.
    fn call_stack_args(&self, target: Option<u64>) -> Option<u32> {
        self.callee_stack_args(target)
            .map(|c| self.cleaned.map_or(c, |n| c.max(n)))
            .or_else(|| (self.bitness() == 32 && self.bodyless(target)).then_some(self.args_pushed))
    }

    /// Returns the declared argument count of the import a call reaches.
    ///
    /// A call to an import lands on a thunk, so the scan that counts the
    /// argument registers a callee reads has no body to read and the call
    /// renders with the four register slots whatever its real arity.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct, or the
    ///   import slot it calls through.
    ///
    /// # Returns
    ///
    /// The total arity, `this` included, or `None` when the target is not a
    /// named import or nothing declares its prototype.
    pub(super) fn callee_import_arity(&self, target: Option<u64>) -> Option<u8> {
        let p = self.callee_prototype(target)?;
        let params = if self.bitness() == 32 {
            p.stack_params()
        } else {
            p.params
        };
        Some(params.saturating_add(u8::from(p.this)))
    }

    /// Returns the prototype of the import a call reaches ([`import_prototype`]).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct, or the
    ///   import slot it calls through.
    pub(super) fn callee_prototype(
        &self,
        target: Option<u64>,
    ) -> Option<crate::analysis::prototypes::Prototype> {
        import_prototype(self.ctx, target)
    }

    /// Counts the argument registers a known callee takes, as its own
    /// signature lists them ([`callee_shape`]): the registers its body
    /// reads, through the wrappers it hands its arguments on to, or the
    /// count its declaration states. Results are cached per function.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    ///
    /// # Returns
    ///
    /// The count, or `None` for an unknown callee or an import thunk.
    pub(super) fn callee_reg_params(&mut self, target: Option<u64>) -> Option<usize> {
        let t = target?;
        if let Some((n, _, _)) = self.ctx.callee_arity.get(&t) {
            return Some((*n).max(self.arity_floor));
        }
        let shape = callee_shape(self.ctx, t)?;
        let n = shape.regs();
        self.ctx
            .callee_arity
            .insert(t, (n, shape.floats(), shape.variadic));
        Some(n.max(self.arity_floor))
    }

    /// The arity of a virtual slot: what its overrides with bodies take,
    /// over the receiver's class and the classes derived from it, each as
    /// its own signature states it; when they disagree, the largest.
    ///
    /// The receiver's static class often keeps a placeholder at a slot its
    /// derived classes implement (`NetStreamBase` reports "Not implemented!"
    /// and reads only `this`), and the object is one of those: a call
    /// through the slot passes what the implementations take. An override
    /// without a body (a bare `ret`) states nothing and is left out.
    ///
    /// # Arguments
    ///
    /// * `class` - The receiver's class.
    /// * `slot` - The slot index.
    pub(super) fn family_arity(&mut self, class: &str, slot: usize) -> usize {
        /// Most distinct overrides scanned.
        const OVERRIDES_MAX: usize = 16;
        /// Most parent links followed from a class toward the receiver's.
        const DEPTH_MAX: usize = 16;
        let classes = &self.ctx.analysis.classes.by_name;
        let mut entries: BTreeSet<u64> = BTreeSet::new();
        for info in classes.values() {
            let Some(&f) = info.slots.get(slot) else {
                continue;
            };
            let mut at = Some(info.name.as_str());
            for _ in 0..DEPTH_MAX {
                let Some(c) = at else {
                    break;
                };
                if c == class {
                    entries.insert(f);
                    break;
                }
                at = classes.get(c).and_then(|i| i.parent.as_deref());
            }
            if entries.len() >= OVERRIDES_MAX {
                break;
            }
        }
        entries
            .into_iter()
            .filter_map(|e| self.callee_reg_params(Some(e)))
            .max()
            .unwrap_or(0)
    }

    /// Tells whether a known callee is variadic: an import declared so, or
    /// a function that homed its argument registers for `va_start`, so it
    /// takes whatever the caller set past its fixed arguments and nothing by
    /// name.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct, or the
    ///   import slot it calls through.
    pub(super) fn callee_variadic(&mut self, target: Option<u64>) -> bool {
        if let Some(p) = self.callee_prototype(target) {
            return p.variadic;
        }
        let _ = self.callee_reg_params(target);
        target
            .and_then(|t| self.ctx.callee_arity.get(&t))
            .is_some_and(|(_, _, v)| *v)
    }

    /// The argument slots a known callee reads as floating point.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct, or the
    ///   import slot it calls through.
    ///
    /// # Returns
    ///
    /// A bit per slot, `this` first when the callee takes one, or zero for
    /// an unknown callee, which leaves the call reading the integer
    /// registers.
    pub(super) fn callee_float_slots(&mut self, target: Option<u64>) -> u8 {
        if let Some(p) = self.callee_prototype(target) {
            return p.floats.checked_shl(u32::from(p.this)).unwrap_or(0);
        }
        let _ = self.callee_reg_params(target);
        target
            .and_then(|t| self.ctx.callee_arity.get(&t))
            .map_or(0, |(_, f, _)| *f)
    }

    /// Tells whether nothing says how many arguments the callee takes but
    /// the caller's own pushes: the callee is unknown, an import slot, or a
    /// thunk to an import without a prototype, so it has no body to read
    /// and no declaration to consult.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct, or the
    ///   import slot it calls through.
    pub(super) fn bodyless(&self, target: Option<u64>) -> bool {
        match target {
            None => true,
            Some(t) => self
                .ctx
                .analysis
                .function(t)
                .is_none_or(|f| f.thunk.is_some() || f.instr_count <= 1),
        }
    }

    /// Returns how many stack arguments the callee at `target` reads.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry, when the call is direct.
    ///
    /// # Returns
    ///
    /// The count, as an import's prototype or the callee's own signature
    /// states it ([`callee_shape`]), or `None` for an unknown callee, an
    /// import thunk without a prototype or code outside the analysis.
    pub(super) fn callee_stack_args(&self, target: Option<u64>) -> Option<u32> {
        if let Some(p) = self.callee_prototype(target) {
            if self.bitness() == 32 {
                return Some(u32::from(p.stack_params()));
            }
            let regs = u32::try_from(self.ctx.conv.args.len()).unwrap_or(0);
            return Some(u32::from(p.params.saturating_add(u8::from(p.this))).saturating_sub(regs));
        }
        callee_shape(self.ctx, target?).map(|s| s.stack)
    }

    /// Reads the code after a 32-bit call whose callee states no pop
    /// ([`stated_pop`]) for what the call takes and what it pops.
    ///
    /// `push rtti; call [edx]; mov ecx, eax; call IsDerivedFrom` pushes the
    /// second call's argument before the first runs, and `call [eax+0x10];
    /// push x; call f; add esp, 0x10` pops a `__cdecl` pointer's three
    /// arguments with the next call's one: read as popping what was pushed
    /// for it, the unknown callee popped those words a second time, and
    /// the stack pointer stood off at the next join, where every later push
    /// and pop was lost. The straight-line code after the call is followed,
    /// through direct jumps (a shared `pop ecx` several calls jump to), and
    /// the stack it moves is counted. The words a later callee's stated pop
    /// removes beyond what the code pushed itself were that callee's, not
    /// this call's arguments. Reaching the `ret`, where the stack pointer
    /// stands at the return address again, the count says exactly what the
    /// call popped; stopping at a branch instead, a `pop` of a scratch
    /// register or an `add esp` removing more than the code pushed is the
    /// caller cleaning up after a `__cdecl` call, whose arguments the
    /// callee left. A call stating no pop is read as popping nothing, which
    /// counts its pushes against the words the cleanup after it removes;
    /// past one, a `ret` says nothing exact. At any other write of the
    /// stack pointer (`leave`, `mov esp, ebp`) only the stated pops count:
    /// an `add esp` there may release the frame.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    ///
    /// # Returns
    ///
    /// `(arguments, popped)` in words: the pushed words that are the
    /// call's, and how many of them it pops.
    pub(super) fn stack_after(&mut self, instr: &Instruction) -> (u32, u32) {
        /// Most instructions followed after the call.
        const WINDOW: usize = 48;
        /// Largest `add esp`/`sub esp` read as moving arguments: a frame
        /// is allocated, not pushed.
        const ADJUST_MAX: u32 = 0x1000;
        let word = u32::try_from(self.ctx.conv.word).unwrap_or(4).max(1);
        let (mut pushed, mut stated, mut cleaned) = (0u32, 0u32, 0u32);
        let mut moved_by: i64 = 0;
        let mut guessed = false;
        let take = |n: u32, pushed: &mut u32| {
            let beyond = n.saturating_sub(*pushed);
            *pushed = pushed.saturating_sub(n);
            beyond
        };
        let mut va = instr.next_ip();
        for _ in 0..WINDOW {
            let Some(i) = self.ctx.decode(va) else { break };
            va = i.next_ip();
            let moved = i.stack_pointer_increment();
            let adjust = (i.op_count() == 2
                && i.op0_kind() == OpKind::Register
                && i.op0_register() == Register::ESP)
                .then(|| u32::try_from(i.try_immediate(1).ok()?).ok())
                .flatten()
                .filter(|n| *n < ADJUST_MAX);
            let scratch = matches!(
                i.op0_register(),
                Register::EAX | Register::ECX | Register::EDX
            );
            match (i.flow_control(), i.mnemonic(), adjust) {
                (FlowControl::Call | FlowControl::IndirectCall, _, _) => {
                    let target = near_target(&i);
                    let reached = target.or_else(|| static_target(&i));
                    match stated_pop(self.ctx, target, reached) {
                        Some(0) => {
                            let wants = self.callee_stack_args(reached).unwrap_or(0);
                            let beyond = wants.saturating_sub(pushed);
                            stated += beyond;
                            pushed += beyond;
                        }
                        Some(n) => {
                            stated += take(n / word, &mut pushed);
                            moved_by += i64::from(n);
                        }
                        None => guessed = true,
                    }
                }
                (FlowControl::UnconditionalBranch, _, _) => match near_target(&i) {
                    Some(t) => va = t,
                    None => break,
                },
                (FlowControl::Next, _, _) if moved < 0 => {
                    pushed += moved.unsigned_abs() / word;
                    moved_by += i64::from(moved);
                }
                (FlowControl::Next, Mnemonic::Pop, _) if moved > 0 => {
                    let beyond = take(moved.unsigned_abs() / word, &mut pushed);
                    if scratch {
                        cleaned += beyond;
                    }
                    moved_by += i64::from(moved);
                }
                (FlowControl::Next, Mnemonic::Add, Some(n)) => {
                    cleaned += take(n / word, &mut pushed);
                    moved_by += i64::from(n);
                }
                (FlowControl::Next, Mnemonic::Sub, Some(n)) => {
                    pushed += n / word;
                    moved_by -= i64::from(n);
                }
                (FlowControl::Next, _, _)
                    if moved == 0
                        && !self.info.info(&i).used_registers().iter().any(|u| {
                            u.register().full_register32() == Register::ESP
                                && !matches!(u.access(), OpAccess::Read | OpAccess::CondRead)
                        }) => {}
                (FlowControl::Return, _, _) => {
                    let args = self.args_pushed.saturating_sub(stated);
                    let exact = self
                        .env
                        .sp
                        .filter(|_| !guessed)
                        .and_then(|sp| u32::try_from(-(sp + moved_by)).ok())
                        .filter(|bytes| bytes % word == 0)
                        .map(|bytes| bytes / word)
                        .filter(|popped| *popped <= args);
                    return (args, exact.unwrap_or(args));
                }
                (FlowControl::ConditionalBranch | FlowControl::IndirectBranch, _, _) => break,
                _ => {
                    let args = self.args_pushed.saturating_sub(stated);
                    return (args, args);
                }
            }
        }
        let args = self.args_pushed.saturating_sub(stated);
        (args, args.saturating_sub(cleaned))
    }

    /// Returns the direct target of a call or jump.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call or jump.
    ///
    /// # Returns
    ///
    /// The near-branch target, or the constant a register operand holds.
    /// Returns the address table slot a call reaches its callee through.
    ///
    /// `call qword [rel slot]` is how a PE calls an import without a thunk,
    /// and the slot names the import even though no branch target does.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    ///
    /// # Returns
    ///
    /// The slot address, or `None` when the operand is not a bare absolute
    /// or rip-relative memory reference (a vtable call has a base register).
    pub(super) fn import_slot(instr: &Instruction) -> Option<u64> {
        (instr.op0_kind() == OpKind::Memory
            && matches!(instr.memory_base(), Register::None | Register::RIP)
            && instr.memory_index() == Register::None)
            .then(|| instr.memory_displacement64())
    }

    /// Returns the import slot a call through a register reaches: `mov
    /// esi, [__imp_SelectObject]` then `call esi` calls the import as
    /// surely as `call [__imp_SelectObject]` does.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    ///
    /// # Returns
    ///
    /// The slot, or `None` when the operand is no register or the register
    /// holds no word loaded from an import slot.
    pub(super) fn register_import(&self, instr: &Instruction) -> Option<u64> {
        if instr.op0_kind() != OpKind::Register {
            return None;
        }
        match self.reg_read(instr.op0_register()) {
            Expr::Var(Key::Global(a, _)) if self.names().import_at(a).is_some() => Some(a),
            _ => None,
        }
    }

    /// Returns the direct target of a call or jump.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call or jump.
    ///
    /// # Returns
    ///
    /// The near-branch target, or the constant a register operand holds.
    pub(super) fn direct_target(&self, instr: &Instruction) -> Option<u64> {
        match instr.op0_kind() {
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
                Some(instr.near_branch_target())
            }
            OpKind::Register => match self.reg_read(instr.op0_register()) {
                Expr::Const(a) => Some(a),
                _ => None,
            },
            _ => None,
        }
    }

    /// Materializes what a callee could observe or destroy, before the
    /// call or tail jump that reads its operands.
    ///
    /// The `__chkstk` constant is captured from rax, and the pending values
    /// of the volatile registers the transfer does not read die here.
    /// Readers of volatile registers are written out (they lose their source
    /// at the call); memory readers are written out; and every slot that is
    /// exposed, or written in this block inside the outgoing argument
    /// window, is stored so the callee sees it, except the ones the call
    /// renders as its arguments, which the reader sees there and which the
    /// callee owns from then on.
    ///
    /// The registers the transfer reads (its argument registers, its other
    /// operands, the registers its target is computed from) keep their
    /// values meanwhile: the transfer reads them first, so one that reads a
    /// variable being written out is moved onto it where it held the
    /// written value ([`Exec::rebase_arguments`]) and is written out itself
    /// before it otherwise. An operand rendered before this that reads a
    /// variable written out here is rendered again from what is left: as it
    /// stood it read the new value (`local_28 += 1; f(a1 + (local_28 <<
    /// 6));` for an index the call took before the increment).
    /// [`Exec::enter_call`] drops the operands' values once they are
    /// rendered.
    ///
    /// # Arguments
    ///
    /// * `stack_args` - How many stack arguments the callee reads, when known.
    /// * `keep_rax` - The callee preserves rax.
    /// * `rendered` - How many outgoing stack slots, counted up from the
    ///   shadow space, the call's argument list shows.
    /// * `values` - The arguments as rendered, each with where the callee
    ///   finds it.
    /// * `operands` - The registers the transfer reads beyond its
    ///   arguments.
    ///
    /// # Returns
    ///
    /// The variables written out meanwhile, in the emission pass: an
    /// operand rendered before that reads one is rendered again
    /// ([`Exec::reads_any`]).
    pub(super) fn before_call(
        &mut self,
        stack_args: Option<u32>,
        keep_rax: bool,
        rendered: usize,
        values: &[(ArgAt, Expr)],
        operands: &[Key],
    ) -> Vec<Key> {
        let volatile = self.clobbered(keep_rax);
        let mut held: Vec<Key> = if self.emit {
            values
                .iter()
                .filter_map(|(at, _)| match at {
                    ArgAt::Reg(r) => Some(Key::Reg(*r)),
                    ArgAt::Stack(..) | ArgAt::Operand | ArgAt::A64(_) => None,
                })
                .collect()
        } else {
            self.argument_registers()
        };
        held.extend_from_slice(operands);
        self.env.chkstk = match self.env.vals.get(&self.canon(self.rax())) {
            Some(Expr::Const(c)) => Some(*c),
            _ => None,
        };
        for r in volatile.iter().filter(|r| !held.contains(r)) {
            self.forget_volatile(*r);
        }
        let start = self.effects.len();
        let only_read_here: Vec<Key> = held.iter().copied().filter(|k| self.dead_reg(*k)).collect();
        let mut added: Vec<Key> = Vec::new();
        if let Some(m) = self.regs_needed.as_mut() {
            for k in &held {
                if !m.contains_key(k) {
                    m.insert(*k, 64);
                    added.push(*k);
                }
            }
        }
        let outlives = |k: &Key| !volatile.contains(k) && !only_read_here.contains(k);
        let readers: Vec<Key> = self
            .env
            .vals
            .iter()
            .filter(|(k, v)| outlives(k) && v.any_var(&|x| volatile.contains(&x)))
            .map(|(k, _)| *k)
            .collect();
        for r in readers {
            self.write_out_for_call(r, &held);
        }
        let memory: Vec<Key> = self
            .env
            .vals
            .iter()
            .filter(|(k, v)| outlives(k) && v.mem_dependent())
            .map(|(k, _)| *k)
            .collect();
        for r in memory {
            self.write_out_for_call(r, &held);
        }
        self.protect_flags(&|e: &Expr| e.mem_dependent());
        let slots: Vec<i64> = self
            .env
            .vals
            .keys()
            .filter_map(|k| match k {
                Key::Slot(o) => Some(*o),
                Key::Reg(_) | Key::Global(..) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => None,
            })
            .filter(|o| {
                !self.rendered_arg(*o, rendered)
                    && !self
                        .env
                        .vals
                        .get(&Key::Slot(*o))
                        .is_some_and(|v| self.is_save(v))
                    && (self.exposed(*o)
                        || (self.in_arg_window(*o, stack_args) && self.slot_def.contains_key(o)))
            })
            .collect();
        for o in slots {
            self.write_out_for_call(Key::Slot(o), &held);
        }
        if let Some(m) = self.regs_needed.as_mut() {
            for k in &added {
                m.remove(k);
            }
        }
        self.effects[start..]
            .iter()
            .filter_map(|e| match e.kind {
                EffectKind::Assign(k, ..) => Some(k),
                EffectKind::Store(_)
                | EffectKind::Call(_)
                | EffectKind::Return(_)
                | EffectKind::Branch(_)
                | EffectKind::Switch(_)
                | EffectKind::Jump(_)
                | EffectKind::Unmodeled => None,
            })
            .collect()
    }

    /// Tells whether any of a call's operands, as rendered, reads one of
    /// the variables written out since.
    ///
    /// # Arguments
    ///
    /// * `values` - The operands' values.
    /// * `written` - The variables written out.
    pub(super) fn reads_any(values: &[(ArgAt, Expr)], written: &[Key]) -> bool {
        values
            .iter()
            .any(|(_, e)| written.iter().any(|k| e.mentions(*k)))
    }

    /// Writes out one value [`Exec::before_call`] forces out, or forgets a
    /// register nothing reads later, keeping the call's operands right.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    /// * `held` - The registers the call reads.
    fn write_out_for_call(&mut self, k: Key, held: &[Key]) {
        if !self.env.vals.contains_key(&k) {
            return;
        }
        if self.dead_reg(k) {
            self.forget_dead(k);
            return;
        }
        let rebased = self.rebase_arguments(k, held);
        self.materialize(k, &mut Vec::new(), None);
        self.env.vals.extend(rebased);
    }

    /// Enters the call or tail jump whose operands are rendered: the
    /// volatile registers' pending values die, as do those of the operands
    /// nothing reads after it, and the slots it may read are recorded for
    /// slot liveness.
    ///
    /// # Arguments
    ///
    /// * `keep_rax` - The callee preserves rax.
    /// * `operands` - The registers the transfer reads beyond the
    ///   convention's argument registers.
    pub(super) fn enter_call(&mut self, keep_rax: bool, operands: &[Key]) {
        for r in self.clobbered(keep_rax) {
            self.forget_volatile(r);
        }
        for k in self.argument_registers().iter().chain(operands) {
            if self.dead_reg(*k) {
                self.forget_dead(*k);
            }
        }
        match self.env.sp {
            Some(_) => {
                if let Some(f) = self.ctx.escape_floor {
                    self.call_uses
                        .push((SlotUse::Window(f, i64::MAX), self.written_slots()));
                }
            }
            None => self.call_uses.push((SlotUse::All, self.written_slots())),
        }
    }

    /// The frame bytes the block's stores wrote so far, which a call made
    /// now reads as the block left them.
    pub(super) fn written_slots(&self) -> BTreeSet<i64> {
        self.slot_def
            .iter()
            .flat_map(|(&o, &b)| o..o.saturating_add(i64::from(b / 8).max(1)))
            .collect()
    }

    /// Drops the pending value of a volatile register a call clobbers; an
    /// `ecx` the call leaves holds nothing ([`Env::unset`]).
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn forget_volatile(&mut self, r: Key) {
        self.env.vals.remove(&r);
        self.env.narrow.remove(&r);
        if r == Key::Reg(Register::ECX) {
            self.env.unset.insert(r);
        }
    }

    /// The registers a call's arguments travel in: `ecx` and `edx` on a
    /// 32-bit target, where a method or `__fastcall` callee reads them,
    /// else the convention's integer and float argument registers.
    fn argument_registers(&self) -> Vec<Key> {
        if self.bitness() == 32 {
            FASTCALL_X86.args.iter().map(|r| Key::Reg(*r)).collect()
        } else {
            self.ctx
                .conv
                .args
                .iter()
                .chain(self.ctx.conv.float_args)
                .map(|r| Key::Reg(*r))
                .collect()
        }
    }

    /// The registers a call or jump computes its target from: a register
    /// operand, or a memory operand's base and index.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call or jump.
    pub(super) fn target_registers(&self, instr: &Instruction) -> Vec<Key> {
        [
            instr.op0_register(),
            instr.memory_base(),
            instr.memory_index(),
        ]
        .into_iter()
        .filter(|r| !matches!(r, Register::None | Register::RIP | Register::EIP))
        .map(|r| self.canon(r))
        .collect()
    }

    /// Tells whether a value is a callee-saved register as the caller left
    /// it ([`Env::touched`]): pushed, it is the register's save, wherever
    /// the prologue was shrink-wrapped to.
    ///
    /// # Arguments
    ///
    /// * `v` - The value a slot holds.
    pub(super) fn is_save(&self, v: &Expr) -> bool {
        matches!(v, Expr::Var(k @ Key::Reg(r))
            if self.ctx.conv.callee_saved.contains(r) && !self.env.touched.contains(k))
    }

    /// The volatile registers the call being lifted clobbers: all of them
    /// but `rax` when the callee hands it back untouched and those the
    /// callee leaves as it found them ([`Exec::preserved`]).
    ///
    /// # Arguments
    ///
    /// * `keep_rax` - The callee preserves rax.
    pub(super) fn clobbered(&self, keep_rax: bool) -> Vec<Key> {
        let rax = self.canon(self.rax());
        self.ctx
            .conv
            .volatile
            .iter()
            .map(|r| Key::Reg(*r))
            .filter(|k| !(self.preserved.contains(k) || keep_rax && *k == rax))
            .collect()
    }

    /// Tells whether slot `o` is one of the outgoing stack arguments the
    /// next call's rendering shows.
    ///
    /// # Arguments
    ///
    /// * `o` - Slot offset.
    /// * `rendered` - How many argument slots above the shadow space the
    ///   call renders; zero when the stack pointer is unknown.
    pub(super) fn rendered_arg(&self, o: i64, rendered: usize) -> bool {
        let Some(sp) = self.env.sp else {
            return false;
        };
        let lo = sp + self.ctx.conv.shadow;
        let len = i64::try_from(rendered).unwrap_or(0) * self.ctx.conv.word;
        o >= lo && o < lo + len
    }

    /// Tells whether slot `o` is an outgoing stack argument of the next call.
    ///
    /// # Arguments
    ///
    /// * `o` - Slot offset.
    /// * `stack_args` - How many the callee reads; `None` assumes the
    ///   default [`STACK_ARG_WINDOW`]. An unknown stack pointer makes every
    ///   slot a candidate.
    pub(super) fn in_arg_window(&self, o: i64, stack_args: Option<u32>) -> bool {
        match self.env.sp {
            Some(sp) => {
                let lo = sp + self.ctx.conv.shadow;
                let len =
                    stack_args.map_or(STACK_ARG_WINDOW, |n| i64::from(n) * self.ctx.conv.word);
                o >= lo && o < lo + len
            }
            None => true,
        }
    }

    /// Forgets what a call destroyed: volatile registers (rax excepted when
    /// the callee hands it back untouched), the flags, every slot at or
    /// above the escape floor, and the callee-owned home slots. The
    /// direction flag comes back clear, as the ABI requires of a callee,
    /// nothing written before the call is set for the next one, and the
    /// registers it clobbered are recorded as such ([`Env::clobbered`]).
    ///
    /// # Arguments
    ///
    /// * `keep_rax` - The callee preserves rax.
    pub(super) fn after_call(&mut self, keep_rax: bool) {
        self.env.df = Some(false);
        self.env.fresh.clear();
        self.args_short = false;
        self.stated_contradicted = false;
        for k in self.clobbered(keep_rax) {
            self.env.vals.remove(&k);
            self.env.narrow.remove(&k);
            self.env.clobbered.insert(k);
        }
        self.flags = Flags::Unknown;
        let sp = self.env.sp;
        let shadow = self.ctx.conv.shadow;
        let floor = self.ctx.escape_floor;
        let dead: Vec<i64> = self
            .env
            .slot_bits
            .keys()
            .copied()
            .filter(|o| {
                floor.is_some_and(|f| *o >= f)
                    || match sp {
                        Some(sp) => *o >= sp && *o < sp + shadow,
                        None => true,
                    }
            })
            .collect();
        for o in dead {
            self.env.vals.remove(&Key::Slot(o));
            self.env.slot_bits.remove(&o);
        }
    }

    /// Renders the callee of a call or jump operand.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call or jump.
    ///
    /// # Returns
    ///
    /// The bare name of a near target, the import or pointer form for a
    /// memory operand, the resolved form for a register operand, or `None`
    /// for an operand kind that cannot be resolved.
    pub(super) fn callee(&mut self, instr: &Instruction) -> Option<String> {
        match instr.op0_kind() {
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => Some(
                bare(&name_of(
                    self.ctx.analysis,
                    self.ctx.overlay,
                    instr.near_branch_target(),
                ))
                .to_owned(),
            ),
            OpKind::Memory => {
                let addr = self.addr(instr, 0);
                self.pointer_callee(addr, Self::mem_ty(instr))
            }
            OpKind::Register => {
                let v = self.reg_read(instr.op0_register());
                self.value_callee(v)
            }
            _ => None,
        }
    }

    /// Renders `call [addr]`: an import slot names the import; a data global
    /// is `(*name)`; anything else is a call through the loaded pointer.
    ///
    /// # Arguments
    ///
    /// * `addr` - The memory operand's address.
    /// * `ty` - Its access type.
    pub(super) fn pointer_callee(&mut self, addr: Expr, ty: Ty) -> Option<String> {
        let n = self.names();
        if let Expr::Const(a) = addr {
            if let Some(imp) = n.import_at(a) {
                return Some(imp);
            }
            if self.is_data(a) {
                if self.emit {
                    self.ctx.globals.insert((a, ty));
                }
                return Some(format!("(*{})", n.key(Key::Global(a, ty.bits()))));
            }
        }
        let v = match addr {
            Expr::Sp(k) => self.slot_read(k, ty),
            other => Expr::deref(other, ty),
        };
        Some(call_through(&v, &self.names()))
    }

    /// Applies a frame-building prologue helper's effect without rendering
    /// a call.
    ///
    /// `__SEH_prolog4` and its relatives build the caller's frame inside the
    /// callee: they push the exception registration, point `ebp` at the
    /// saved frame pointer and return with the stack four words lower, so a
    /// caller's `[ebp+8]` is its first argument only once that has happened
    /// here. The helper's instructions run through the lifter with output
    /// off, after the call's own push of the return address and up to the
    /// `ret` that pops it back; the slot that `ret` pops is dropped with it.
    /// The prologue helper leaves `eax` holding the return address it
    /// juggled, which nothing reads, so `eax` is forgotten along with the
    /// flags; the epilogue helper, `__SEH_epilog4`, tears the frame down the
    /// same way in reverse and leaves `eax` the result it is. A prologue
    /// helper that sizes the frame from the words its call pushes (`sub
    /// esp, eax` in `__SEH_prolog4`, `sub esp, [esp+0xc]` in
    /// `__EH_prolog3`) reads them from their slots: the call's block pushes
    /// them as constants before the handler is registered, when the slots
    /// keep no value, so they hold those constants while the helper runs
    /// and the stack pointer stays known.
    ///
    /// # Arguments
    ///
    /// * `target` - The helper's entry.
    /// * `call` - The address of the call to it.
    /// * `prolog` - The helper is the prologue's, which registers the
    ///   handler and clobbers `eax`.
    pub(super) fn inline_frame_helper(&mut self, target: u64, call: u64, prolog: bool) {
        let word = self.ctx.conv.word;
        let Some(block) = self
            .ctx
            .analysis
            .function(target)
            .and_then(|f| f.blocks.first())
        else {
            return;
        };
        let emit = std::mem::replace(&mut self.emit, false);
        let mut seeded: Vec<i64> = Vec::new();
        if let Some(sp) = self.env.sp
            && prolog
            && let Some(&start) = self.ctx.block_starts.range(..=call).next_back()
        {
            let mut pushed: Vec<u64> = Vec::new();
            let mut va = start;
            while va < call {
                let Some(i) = self.ctx.decode(va) else {
                    break;
                };
                va = i.next_ip();
                if i.mnemonic() == Mnemonic::Push && is_imm(i.op0_kind()) {
                    pushed.push(u64::from(crate::num::lo32(i.immediate(0))));
                }
            }
            for (k, v) in (0i64..).zip(pushed.into_iter().rev()) {
                let at = sp + k * word;
                self.env.vals.insert(Key::Slot(at), Expr::Const(v));
                self.env.slot_bits.insert(at, 32);
                seeded.push(at);
            }
        }
        if let Some(sp) = self.env.sp {
            self.env.sp = Some(sp - word);
        }
        let mut va = block.start;
        while va < block.end {
            let Some(i) = self.ctx.decode(va) else {
                break;
            };
            va = i.next_ip();
            if i.flow_control() == FlowControl::Return {
                if let Some(sp) = self.env.sp {
                    self.env.vals.remove(&Key::Slot(sp));
                    self.env.slot_bits.remove(&sp);
                    self.env.sp = Some(sp + word);
                }
                break;
            }
            self.step(&i);
        }
        for at in seeded {
            self.env.vals.remove(&Key::Slot(at));
            self.env.slot_bits.remove(&at);
        }
        self.emit = emit;
        if prolog {
            self.seh_registered = true;
            let rax = self.canon(self.rax());
            self.clobber(rax);
        }
        self.flags = Flags::Unknown;
    }

    /// Renders `call reg`: a loaded import pointer names the import; a
    /// constant that is a function is a direct target; anything else is a
    /// call through the value.
    ///
    /// # Arguments
    ///
    /// * `v` - The register's value.
    pub(super) fn value_callee(&mut self, v: Expr) -> Option<String> {
        let n = self.names();
        match v {
            Expr::Var(Key::Global(a, _)) if n.import_at(a).is_some() => n.import_at(a),
            Expr::Const(a) if self.ctx.analysis.function(a).is_some() => {
                Some(bare(&name_of(self.ctx.analysis, self.ctx.overlay, a)).to_owned())
            }
            other => Some(call_through(&other, &n)),
        }
    }

    /// The loads an unnamed 64-bit callee makes before it returns or jumps
    /// on, when that is all it does, and where it jumps.
    ///
    /// The callee is one block of at most [`IN_PLACE_MAX`] instructions,
    /// each a `mov`, `movzx`, `movsx`, `movsxd` or `lea` into a general
    /// register other than the stack pointer from a register, a constant or
    /// memory not on the stack, or a `xor` of a register with itself. The
    /// last, after at least one load, is a direct `jmp` to a named function,
    /// `mov ecx, 1; jmp Memory::Free` forwarding with its first argument
    /// fixed, or a plain `ret` after loads that all read globals,
    /// `mov rax, [g]; ret` handing back an instance. A bare `jmp` is a
    /// thunk, named as such elsewhere, and a forward to another unnamed
    /// function or a getter of a field says no more read in place.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    pub(super) fn trivial_callee(&self, target: u64) -> Option<(Vec<Instruction>, Option<u64>)> {
        if self.ctx.bitness != 64 || !self.unnamed(target) {
            return None;
        }
        let f = self.ctx.analysis.function(target)?;
        if f.blocks.len() != 1 || f.instr_count > IN_PLACE_MAX + 1 {
            return None;
        }
        let mut loads: Vec<Instruction> = Vec::new();
        let mut va = target;
        for _ in 0..=IN_PLACE_MAX {
            let i = self.ctx.decode(va)?;
            va = i.next_ip();
            match i.flow_control() {
                FlowControl::Return => {
                    let globals = loads.iter().all(|l| {
                        l.op1_kind() == OpKind::Memory && l.memory_base() == Register::RIP
                    });
                    let pops = i.op_count() > 0 && i.immediate16() != 0;
                    return (!pops && !loads.is_empty() && globals).then_some((loads, None));
                }
                FlowControl::UnconditionalBranch => {
                    if i.op0_kind() != OpKind::NearBranch64 {
                        return None;
                    }
                    let on = i.near_branch_target();
                    self.ctx.analysis.function(on)?;
                    return (on != target && !loads.is_empty() && !self.unnamed(on))
                        .then_some((loads, Some(on)));
                }
                FlowControl::Next if is_register_load(&i) => loads.push(i),
                _ => return None,
            }
        }
        None
    }

    /// Follows a call into a dispatch thunk or through a read-only pointer.
    ///
    /// Up to four hops are followed from the call's target: a direct jump,
    /// or a jump through a pointer that read-only data holds (an import
    /// slot is the import's, and ends the walk). A jump through a register
    /// ends it as a dispatch through that register; a `ret` that pops
    /// nothing ends it as a call that does nothing, but only behind a
    /// pointer: a direct call to a function that only returns is left to
    /// [`Exec::returns_at_once`], which keeps a named one.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call: a direct one, or one through a memory operand
    ///   naming the pointer outright.
    ///
    /// # Returns
    ///
    /// Where the call goes, or `None` when it is no dispatch.
    pub(super) fn dispatch(&self, instr: &Instruction) -> Option<Dispatch> {
        /// Most jumps and pointers followed from the call's target.
        const HOPS: usize = 4;
        let (mut at, behind_pointer) = match instr.op0_kind() {
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
                (instr.near_branch_target(), false)
            }
            OpKind::Memory => (self.read_only_pointer(Self::import_slot(instr)?)?, true),
            _ => return None,
        };
        for _ in 0..HOPS {
            let i = self.ctx.decode(at)?;
            match (i.flow_control(), i.op0_kind()) {
                (FlowControl::Return, _)
                    if behind_pointer && (i.op_count() == 0 || i.immediate16() == 0) =>
                {
                    return Some(Dispatch::Nothing(at));
                }
                (FlowControl::UnconditionalBranch, _) => at = near_target(&i)?,
                (FlowControl::IndirectBranch, OpKind::Register) => {
                    let r = i.op0_register();
                    return (r.full_register() != Register::RSP).then_some(Dispatch::Through(r));
                }
                (FlowControl::IndirectBranch, OpKind::Memory) => {
                    at = self.read_only_pointer(Self::import_slot(&i)?)?;
                }
                _ => return None,
            }
        }
        None
    }

    /// Reads the code address a pointer in read-only data holds.
    ///
    /// # Arguments
    ///
    /// * `slot` - The pointer's address.
    ///
    /// # Returns
    ///
    /// The address it holds, or `None` when the slot is an import's, sits in
    /// writable or executable memory, or holds no address of code.
    pub(super) fn read_only_pointer(&self, slot: u64) -> Option<u64> {
        let program = self.ctx.program;
        let section = program.section_at(slot)?;
        if section.writable || section.executable || self.names().import_at(slot).is_some() {
            return None;
        }
        let word = usize::try_from(self.ctx.conv.word).ok()?;
        let mut bytes = [0u8; 8];
        bytes
            .get_mut(..word)?
            .copy_from_slice(program.read_va(slot, word)?);
        let to = u64::from_le_bytes(bytes);
        program
            .section_at(to)
            .is_some_and(|s| s.executable)
            .then_some(to)
    }

    /// Writes out, before a call's operands render, every value the call
    /// forces out that an operand reads, so the operand reads the text the
    /// way the call line will see it.
    ///
    /// A callee-saved register whose pending value reads a volatile one,
    /// any value read from memory that is no argument, and a slot whose
    /// address escaped (the call writes it out in any case) is written out
    /// before the call; written out after the arguments rendered, `rdi =
    /// rdi + rax` would make an argument that read `rdi + rax` read it as
    /// `rdi + rax + rax`. An argument that reads such a value whole reads
    /// the variable instead ([`Exec::rebase_arguments`]); one that reads it
    /// otherwise is written out first itself, since the call reads it: the
    /// argument registers and those the call goes through count as needed
    /// while this runs. The registers the call goes through keep their
    /// values: the call reads them before it runs (`mov edi, [__imp_f]; call
    /// edi` calls `f`), and so do the x87 registers an x87 helper takes its
    /// operands from and the vector registers a 32-bit callee takes its
    /// floats in.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    /// * `keep_rax` - The callee hands `rax` back untouched.
    /// * `operands` - The x87 and vector registers the callee takes its
    ///   arguments from beyond the convention's.
    pub(super) fn protect_operands(
        &mut self,
        instr: &Instruction,
        keep_rax: bool,
        operands: &[Key],
    ) {
        let volatile = self.clobbered(keep_rax);
        let through = self.target_registers(instr);
        let mut args = self.argument_registers();
        args.extend_from_slice(operands);
        let window = self.env.sp.map(|sp| {
            let lo = sp + self.ctx.conv.shadow;
            lo..(lo + STACK_ARG_WINDOW).min(0)
        });
        let pending: Vec<Key> = self
            .env
            .vals
            .iter()
            .filter(|(k, v)| {
                !volatile.contains(k)
                    && !args.contains(k)
                    && !through.contains(k)
                    && !matches!(k, Key::Slot(o) if window.as_ref().is_some_and(|w| w.contains(o)))
                    && (v.any_var(&|x| volatile.contains(&x))
                        || v.mem_dependent()
                        || matches!(k, Key::Slot(o) if self.exposed(*o)))
            })
            .map(|(k, _)| *k)
            .collect();
        if pending.is_empty() {
            return;
        }
        let mut added: Vec<Key> = Vec::new();
        if let Some(m) = self.regs_needed.as_mut() {
            for k in args.iter().chain(&through) {
                if !m.contains_key(k) {
                    m.insert(*k, 64);
                    added.push(*k);
                }
            }
        }
        for k in pending {
            if !self.env.vals.contains_key(&k) {
                continue;
            }
            if self.dead_reg(k) {
                self.forget_dead(k);
            } else {
                let rebased = self.rebase_arguments(k, &args);
                self.materialize(k, &mut Vec::new(), None);
                self.env.vals.extend(rebased);
            }
        }
        if let Some(m) = self.regs_needed.as_mut() {
            for k in &added {
                m.remove(k);
            }
        }
    }

    /// Takes out of the environment, rewritten, the arguments that read a
    /// value about to be written out under its own name: once `rdi = rdi +
    /// rax;` is in the text, an argument `(int32_t)(rdi + rax) + a1` is
    /// `(int32_t)rdi + a1`. An argument that reads the variable outside
    /// that value, or reads another variable with a value pending (which
    /// the write-out may write out too), stays as it is, for the write-out
    /// to protect.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable about to be written out.
    /// * `args` - The registers the call reads; `k` itself among them is
    ///   written out, not rewritten.
    ///
    /// # Returns
    ///
    /// The arguments taken out with their rewritten values, to be put back
    /// once the variable is written out.
    pub(super) fn rebase_arguments(&mut self, k: Key, args: &[Key]) -> Vec<(Key, Expr)> {
        let Some(v) = self.env.vals.get(&k).cloned() else {
            return Vec::new();
        };
        let marker = Expr::Var(Key::Tmp(u32::MAX));
        let var = Expr::Var(k);
        let mut out = Vec::new();
        for a in args.iter().filter(|a| **a != k) {
            let Some(e) = self.env.vals.get(a).filter(|e| e.mentions(k)) else {
                continue;
            };
            let swapped = e.subst(&v, &marker);
            let settled = !swapped.any_var(&|x| x != k && self.env.vals.contains_key(&x));
            if swapped != *e && !swapped.mentions(k) && settled {
                out.push((*a, swapped.subst(&marker, &var)));
            }
        }
        for (a, _) in &out {
            self.env.vals.remove(a);
        }
        out
    }

    /// Tells whether a slot's function is the stub a pure virtual slot
    /// holds: one the name says reports a pure call (`_purecall`), or one
    /// that never returns and fills slots at several indexes across the
    /// classes (the CRT's handler, statically linked and unnamed).
    ///
    /// # Arguments
    ///
    /// * `entry` - The slot's function.
    pub(super) fn pure_stub(&self, entry: u64) -> bool {
        let analysis = self.ctx.analysis;
        name_of(analysis, self.ctx.overlay, entry)
            .to_ascii_lowercase()
            .contains("purecall")
            || analysis
                .derived
                .get_or_build("pure_stubs", (), || pure_stubs(analysis))
                .contains(&entry)
    }

    /// Tells whether an argument register holds a string.
    ///
    /// A call to a function that does nothing still says something with
    /// one: an assertion compiled down to a stub keeps its expression and
    /// file in the call, and a log line its message.
    pub(super) fn passes_text(&self) -> bool {
        self.ctx
            .conv
            .args
            .iter()
            .any(|r| matches!(self.env.vals.get(&self.canon(*r)), Some(Expr::Str(_))))
    }

    /// Tells whether a callee has no name of its own: none found in the
    /// binary and none the user gave. A named call says what the caller
    /// meant even when the callee does little, so only the anonymous ones
    /// are read in place or left out.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    pub(super) fn unnamed(&self, target: u64) -> bool {
        !self.ctx.overlay.names.contains_key(&target)
            && self
                .ctx
                .analysis
                .function(target)
                .is_some_and(|f| f.name.is_none())
    }

    /// Tells whether an unnamed 64-bit callee's first instruction is a
    /// `ret` that pops nothing (`ret`, `rep ret` or `ret 0`): a function
    /// that does nothing.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    pub(super) fn returns_at_once(&self, target: u64) -> bool {
        self.ctx.bitness == 64
            && self.unnamed(target)
            && matches!(
                self.ctx.program.read_va(target, 3),
                Some([0xc3, ..] | [0xf3, 0xc3, ..] | [0xc2, 0x00, 0x00])
            )
    }

    /// Lifts a call.
    ///
    /// A call through a vtable whose receiver has no known class reads
    /// `recv->vtable[N](args)`, the receiver dropped from the arguments when
    /// it is passed first, so the slot and the object stay visible without
    /// the double dereference. A call with `1` alone through the deleting
    /// destructor's slot reads `delete(recv)`, whatever class the receiver
    /// is known to have.
    ///
    /// The result is bound (`rax = f(...)`) when the next instruction reads
    /// rax or, since every call ends its block, when the successors' liveness
    /// says rax is read; without liveness (dataflow rounds) it is bound. A
    /// floating-point result is bound to `xmm0` instead when the next
    /// instruction reads `xmm0` and not rax, typed by that instruction
    /// (`movss` makes it a `float`, anything else a `double`), unless the
    /// callee hands `xmm0` back untouched. On a 32-bit target a float comes
    /// back in `st0` ([`Exec::leaves_x87_float`]): the call empties the x87
    /// stack and pushes the result it binds; an x87 helper takes its
    /// operands off the stack as its arguments instead, and a callee that
    /// runs no x87 instruction leaves the stack as it was. There only a
    /// callee known to return in `xmm0` binds it ([`sse_callee`]), and the
    /// floats it takes in vector registers are its last arguments.
    ///
    /// A callee that pops its arguments (`ret imm16`, or a `__stdcall` or
    /// `__thiscall` prototype on a 32-bit target) leaves the stack pointer
    /// higher by that many bytes; the popped slots were the callee's to
    /// write and sit above the stack pointer afterwards, so their values
    /// are forgotten with them.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    /// * `next` - The instruction that runs after the call: the block's next
    ///   one, else the successor block's first ([`BlockFacts::after`]).
    /// * `rest` - The instructions after the call in its block.
    pub(super) fn call(
        &mut self,
        instr: &Instruction,
        next: Option<&Instruction>,
        rest: &[Instruction],
    ) {
        let direct = self.direct_target(instr);
        let noreturn = next.is_none();
        if let Some(t) = direct
            && crate::analysis::render::frame_helper(self.ctx.analysis, self.ctx.overlay, instr)
        {
            self.record_call(
                Callee::Direct(t),
                Vec::new(),
                None,
                None,
                noreturn,
                Shown::Elided,
            );
            self.inline_frame_helper(t, instr.ip(), true);
            return;
        }
        if let Some(t) = direct
            && crate::analysis::render::epilog_helper(self.ctx.analysis, self.ctx.overlay, instr)
        {
            self.record_call(
                Callee::Direct(t),
                Vec::new(),
                None,
                None,
                noreturn,
                Shown::Elided,
            );
            self.inline_frame_helper(t, instr.ip(), false);
            return;
        }
        if let Some(t) = direct
            && self.returns_at_once(t)
            && !self.passes_text()
        {
            if self.emit {
                self.ctx.empty_calls.insert(t);
            }
            self.record_call(
                Callee::Direct(t),
                Vec::new(),
                None,
                None,
                noreturn,
                Shown::Elided,
            );
            return;
        }
        if let Some(t) = direct
            && !self.in_place
            && let Some((loads, on)) = self.trivial_callee(t)
        {
            if self.emit {
                self.ctx.read_in_place.insert(t);
            }
            self.record_call(
                Callee::Direct(t),
                Vec::new(),
                None,
                None,
                noreturn,
                Shown::InPlace,
            );
            for i in &loads {
                self.step(i);
            }
            self.flags = Flags::Unknown;
            if let Some(on) = on
                && let Ok(mut jump) = Instruction::with_branch(Code::Call_rel32_64, on)
            {
                jump.set_ip(instr.ip());
                jump.set_len(instr.len());
                jump.set_next_ip(instr.next_ip());
                self.in_place = true;
                self.call(&jump, next, rest);
                self.in_place = false;
            }
            return;
        }
        if let Some(t) = direct
            && crate::analysis::render::preserves_registers(
                self.ctx.analysis,
                self.ctx.overlay,
                instr,
            )
        {
            let size = match self.env.vals.get(&self.canon(self.rax())) {
                Some(Expr::Const(c)) => Some(*c),
                _ => None,
            };
            self.env.chkstk = size;
            let name = bare(&name_of(self.ctx.analysis, self.ctx.overlay, t)).to_owned();
            let arg = size.map_or(String::new(), |c| {
                crate::analysis::decompile::expr::render_const(c, true)
            });
            emit_line!(self, format!("{name}({arg});"));
            let args =
                size.map_or_else(Vec::new, |c| vec![(ArgAt::Reg(self.rax()), Expr::Const(c))]);
            self.record_call(
                Callee::Direct(t),
                args,
                None,
                None,
                noreturn,
                Shown::Statement,
            );
            return;
        }
        match self.dispatch(instr) {
            Some(Dispatch::Through(reg)) => {
                if self.emit {
                    match direct {
                        Some(t) => {
                            self.ctx.dispatches.insert(t, reg);
                        }
                        None => {
                            if let Some(t) = Self::import_slot(instr)
                                .and_then(|slot| self.read_only_pointer(slot))
                            {
                                self.ctx.pointer_dispatches.insert(t, reg);
                            }
                        }
                    }
                }
                let code = if self.bitness() == 32 {
                    Code::Call_rm32
                } else {
                    Code::Call_rm64
                };
                if let Ok(mut through) = Instruction::with1(code, reg) {
                    through.set_ip(instr.ip());
                    through.set_len(instr.len());
                    through.set_next_ip(instr.next_ip());
                    self.call(&through, next, rest);
                    return;
                }
            }
            Some(Dispatch::Nothing(t)) => {
                if self.emit {
                    self.ctx.empty_calls.insert(t);
                }
                self.record_call(
                    Callee::Direct(t),
                    Vec::new(),
                    None,
                    None,
                    noreturn,
                    Shown::Elided,
                );
                return;
            }
            None => {}
        }
        let (x87, sse) = if self.bitness() == 32 {
            let reached = direct
                .or_else(|| Self::import_slot(instr))
                .or_else(|| self.register_import(instr));
            (x87_callee(self.ctx, reached), sse_callee(self.ctx, reached))
        } else {
            (x87::Call::Kept, Sse::default())
        };
        let operands: Vec<Key> = match x87 {
            x87::Call::Helper(e) => (0..usize::from(e.takes))
                .map(|k| Key::Reg(st_register(k)))
                .collect(),
            x87::Call::Kept | x87::Call::Plain => Vec::new(),
        }
        .into_iter()
        .chain(sse_args(sse).map(Key::Reg))
        .collect();
        if x87 == x87::Call::Plain {
            self.empty_x87();
        }
        self.preserved = direct.map_or_else(Vec::new, |t| {
            preserved_volatiles(self.ctx, t).as_ref().clone()
        });
        self.protect_operands(instr, self.callee_preserves_rax(direct), &operands);
        let virt = if direct.is_none() {
            self.virtual_target(instr)
        } else {
            None
        };
        let target = direct.or(virt.as_ref().filter(|v| !v.pure).map(|v| v.entry));
        if let Some(v) = virt.as_ref().filter(|v| !v.pure)
            && self.emit
        {
            self.ctx.vcalls.insert(v.entry);
        }
        let reached = target
            .or_else(|| Self::import_slot(instr))
            .or_else(|| self.register_import(instr));
        let stated = stated_pop(self.ctx, target, reached);
        let unstated = stated.is_none().then(|| {
            let (args, popped) = self.stack_after(instr);
            self.args_pushed = args;
            popped
        });
        let cdecl = target
            .filter(|_| self.bitness() == 32 && stated == Some(0) && !self.bodyless(target))
            .and_then(|t| callee_shape(self.ctx, t))
            .is_some_and(|s| s.conv.args.is_empty());
        self.cleaned = cdecl
            .then(|| self.stack_after(instr))
            .filter(|(args, popped)| *popped == 0 && *args > 0)
            .map(|(args, _)| args);
        self.call_through = direct
            .is_none()
            .then(|| self.through_register(instr))
            .flatten();
        self.arity_floor = match &virt {
            Some(v) => self.family_arity(&v.class, v.slot),
            None => 0,
        };
        self.receiver = match &virt {
            Some(v) => Some(v.receiver.clone()),
            None if direct.is_none() => self.vtable_shape(instr).map(|(recv, _)| recv),
            None => None,
        };
        let (mut args, mut rendered, mut values) = self.args_for(reached);
        if let x87::Call::Helper(e) = x87 {
            let n = self.names();
            args = (0..usize::from(e.takes))
                .rev()
                .map(|k| self.st(k).render(&n))
                .collect();
            if self.emit {
                values = (0..usize::from(e.takes))
                    .rev()
                    .map(|k| (ArgAt::Reg(st_register(k)), self.st(k)))
                    .collect();
            }
            rendered = 0;
            for _ in 0..e.takes {
                self.pop_st();
            }
        }
        let arity = self.call_stack_args(reached);
        let preserves = self.callee_preserves_rax(target);
        let mut held = self.target_registers(instr);
        held.extend_from_slice(&operands);
        let raxk = self.canon(self.rax());
        let narrow_result = (!preserves && !self.ctx.ret_float)
            .then(|| self.callee_partial_lane(target))
            .flatten();
        let merge_pre = narrow_result
            .filter(|_| {
                self.result_read(next, rest, raxk, Key::Reg(Register::XMM0))
                    .0
            })
            .filter(|_| self.env.vals.contains_key(&raxk))
            .and_then(|_| {
                let pre = self.env.vals.get(&raxk).cloned()?;
                let stable = |k: Key| match k {
                    Key::Param(_) | Key::Global(..) | Key::Tmp(_) => true,
                    Key::Slot(o) => !self.exposed(o),
                    Key::Reg(_) | Key::A64(_) => self.env.vals.get(&k) == Some(&Expr::Var(k)),
                };
                (!pre.any_var(&|k| !stable(k))).then_some(pre)
            });
        let written = self.before_call(arity, preserves, rendered, &values, &held);
        let stale = Self::reads_any(&values, &written)
            || virt
                .as_ref()
                .is_some_and(|v| written.iter().any(|k| v.receiver.mentions(*k)));
        let virt = if stale && !matches!(x87, x87::Call::Helper(_)) {
            let virt = virt.and_then(|v| {
                self.virtual_target(instr)
                    .filter(|now| now.entry == v.entry)
            });
            self.receiver = match &virt {
                Some(v) => Some(v.receiver.clone()),
                None if direct.is_none() => self.vtable_shape(instr).map(|(recv, _)| recv),
                None => None,
            };
            (args, _, values) = self.args_for(reached);
            virt
        } else {
            virt
        };
        let n = self.names();
        args.extend(sse_args(sse).map(|r| {
            let k = Key::Reg(r);
            self.env
                .vals
                .get(&k)
                .cloned()
                .unwrap_or(Expr::Var(k))
                .render(&n)
        }));
        if self.emit {
            values.extend(sse_args(sse).map(|r| (ArgAt::Reg(r), self.env.get(Key::Reg(r)))));
            self.name_arguments(reached, &mut args);
        }
        let callee_value = self.emit.then(|| match direct {
            Some(t) => Callee::Direct(t),
            None => Callee::Through(self.call_target(instr)),
        });
        self.arity_floor = 0;
        self.call_through = None;
        self.receiver = None;
        self.type_slot_arguments(target);
        let arg0_class = self.arg_class(0);
        let callee = match virt.as_ref().filter(|v| !v.pure) {
            Some(v) => {
                let n = self.names();
                let recv = v.receiver.render(&n);
                let shown = v.shown.map_or_else(
                    || {
                        if recv.starts_with('*') {
                            format!("({recv})")
                        } else {
                            recv.clone()
                        }
                    },
                    |k| n.key(k),
                );
                let full = bare(&name_of(self.ctx.analysis, self.ctx.overlay, v.entry)).to_owned();
                let method = match crate::analysis::classes::class_of(&full) {
                    Some(c) if c == v.class => {
                        slot_method(full.get(c.len() + 2..).unwrap_or(&full))
                    }
                    _ => full.as_str(),
                };
                if args.first() == Some(&recv) {
                    args.remove(0);
                    if self.ctx.analysis.classes.dtor_slots.contains(&v.slot) && args == ["1"] {
                        args = vec![recv];
                        "delete".to_owned()
                    } else {
                        format!("{shown}->{method}")
                    }
                } else if args.is_empty() {
                    format!("{shown}->{method}")
                } else {
                    full.clone()
                }
            }
            None => match self.vtable_shape(instr) {
                Some((recv, slot)) => {
                    let n = self.names();
                    let rendered = recv.render(&n);
                    let slot = virt.as_ref().map_or(slot, |v| v.slot);
                    let shown = if matches!(recv, Expr::Var(_)) {
                        rendered.clone()
                    } else {
                        format!("({rendered})")
                    };
                    if args.first() == Some(&rendered) {
                        args.remove(0);
                    }
                    if self.ctx.analysis.classes.dtor_slots.contains(&slot) && args == ["1"] {
                        args = vec![rendered];
                        "delete".to_owned()
                    } else {
                        format!("{shown}->vtable[{slot}]")
                    }
                }
                None => self
                    .callee(instr)
                    .unwrap_or_else(|| "(*unknown)".to_owned()),
            },
        };
        self.enter_call(preserves, &held);
        let rax = self.canon(self.rax());
        let xmm0 = Key::Reg(Register::XMM0);
        let (uses_result, float_result) = self.result_read(next, rest, rax, xmm0);
        let float_result = float_result
            || (!uses_result
                && self.bitness() == 64
                && self
                    .regs_needed
                    .as_ref()
                    .is_some_and(|m| m.contains_key(&xmm0))
                && self.callee_returns_float(target));
        let st0 = match x87 {
            x87::Call::Helper(e) => (e.gives > 0).then_some(true),
            x87::Call::Plain => self.leaves_x87_float(instr, target),
            x87::Call::Kept => None,
        };
        let uses_result = uses_result && !preserves && st0.is_none();
        let float_result = float_result
            && st0.is_none()
            && !self.preserved.contains(&xmm0)
            && (self.bitness() == 64 || sse.returns);
        if let Some(t) = target.filter(|t| self.ctx.overlay.prototypes.contains_key(t))
            && callee_shape(self.ctx, t).is_some_and(|s| s.stated_short.is_some())
        {
            self.stated_contradicted = true;
        }
        let declared = stated_returns(self.ctx, target, reached).filter(|_| st0.is_none());
        let (uses_result, float_result) = match declared {
            Some(r) => {
                let (rax, float, contradicted) = r.filter(uses_result, float_result);
                self.stated_contradicted |= contradicted;
                (rax, float)
            }
            None => (uses_result, float_result),
        };
        let result = match st0 {
            Some(shown) => shown.then_some(Key::Reg(Register::ST0)),
            None if float_result => Some(xmm0),
            None => uses_result.then_some(rax),
        };
        let rdxk = self.canon(Register::RDX);
        let next_rdx = next.is_some_and(|n| self.reads_register(n, rdxk));
        let uses_rdx = if rest.is_empty() {
            match self.regs_needed.as_ref() {
                Some(m) => m.contains_key(&rdxk),
                None if next.is_some() => next_rdx,
                None => false,
            }
        } else {
            self.second_read(rest, rdxk)
        };
        let hands_back_rdx = target.is_some_and(|t| {
            self.ctx
                .analysis
                .function(t)
                .is_some_and(|f| f.hands_back_rdx)
        });
        let stated_callee = target.is_some_and(|t| self.ctx.overlay.prototypes.contains_key(&t));
        if stated_callee && hands_back_rdx && uses_rdx {
            self.stated_contradicted = true;
        }
        let word = u8::try_from(self.bitness()).unwrap_or(64);
        let declared_one =
            declared.is_some_and(|r| !matches!(r, Returns::Int(bits) if bits > word));
        let mut second = (direct.is_some()
            && virt.is_none()
            && !stated_callee
            && !declared_one
            && uses_rdx
            && hands_back_rdx)
            .then(|| {
                let n = self.names();
                format!("{} = {callee}__rdx({});", n.key(rdxk), args.join(", "))
            });
        let result2 = second.is_some().then(|| {
            self.declare(rdxk, self.word_ty());
            rdxk
        });
        let call = format!("{callee}({})", args.join(", "));
        let call = match (second.take(), result) {
            (Some(line), Some(k)) if names_variable(&args, &self.names().key(k)) => {
                let t = self.fresh_tmp(if k == xmm0 { Ty::F64 } else { self.word_ty() });
                let n = self.names();
                emit_line!(self, format!("{} = {call};", n.key(t)));
                emit_line!(self, line);
                n.key(t)
            }
            (line, _) => {
                second = line;
                call
            }
        };
        if !preserves {
            self.env.result_in_rax = uses_result && self.callee_returns_value(target);
        }
        if let Some(shown) = st0 {
            let k = Key::Reg(Register::ST0);
            self.protect_readers(k, &mut Vec::new(), None);
            self.push_st(Expr::Var(k));
            if shown {
                self.declare(k, Ty::F64);
                let n = self.names();
                emit_line!(self, format!("{} = {call};", n.key(k)));
            } else {
                emit_line!(self, format!("{call};"));
            }
        } else if float_result {
            let known = target
                .and_then(|t| self.ctx.analysis.function(t))
                .and_then(|f| f.ret_float);
            let ty = match (known, next) {
                (Some(32), _) => Ty::F32,
                (Some(_), _) => Ty::F64,
                (None, Some(n)) if is_float(n.memory_size()) => Self::mem_ty(n),
                (None, Some(n)) if format!("{:?}", n.mnemonic()).ends_with("ss") => Ty::F32,
                (None, _) => Ty::F64,
            };
            self.ctx.reg_ty.entry(xmm0).or_insert(ty);
            self.declare(xmm0, ty);
            let n = self.names();
            emit_line!(self, format!("{} = {call};", n.key(xmm0)));
        } else if uses_result {
            self.declare(rax, self.word_ty());
            if self.emit {
                self.note_result_type(target, reached, &callee);
            }
            let n = self.names();
            emit_line!(
                self,
                match (&merge_pre, narrow_result) {
                    (Some(pre), Some(bits)) => {
                        let m = if bits == 8 { "0xff" } else { "0xffff" };
                        format!(
                            "{} = ({} & ~{m}) | ({call} & {m});",
                            n.key(rax),
                            pre.render(&n)
                        )
                    }
                    _ => format!("{} = {call};", n.key(rax)),
                }
            );
            match target.and_then(|t| self.returned_class(t, arg0_class.as_deref())) {
                Some(c) => {
                    self.env.classes.insert(rax, c);
                }
                None => {
                    self.env.classes.remove(&rax);
                }
            }
        } else {
            emit_line!(self, format!("{call};"));
        }
        if let Some(line) = second {
            emit_line!(self, line);
        }
        if let Some(c) = callee_value {
            self.record_call(c, values, result, result2, noreturn, Shown::Statement);
        }
        let bits = if uses_result && !float_result {
            self.callee_return_bits(target)
        } else {
            None
        };
        self.after_call(preserves);
        if let Some(k) = result2.filter(|_| self.bitness() == 64) {
            self.env.clobbered.remove(&k);
            self.env.touched.insert(k);
        }
        self.preserved.clear();
        if let Some(b) = bits.filter(|_| merge_pre.is_none()) {
            self.env.narrow.insert(rax, b);
        }
        let popped = match (stated, unstated) {
            (Some(bytes), _) => i64::from(bytes),
            (None, Some(words)) if !cleans_stack(next) => i64::from(words) * self.ctx.conv.word,
            (None, _) => 0,
        };
        self.args_pushed = 0;
        self.cleaned = None;
        if let Some(sp) = self.env.sp.filter(|_| popped > 0) {
            let gone: Vec<i64> = self
                .env
                .slot_bits
                .keys()
                .copied()
                .filter(|o| *o >= sp && *o < sp + popped)
                .collect();
            for o in gone {
                self.env.vals.remove(&Key::Slot(o));
                self.env.slot_bits.remove(&o);
            }
            self.env.sp = Some(sp + popped);
        }
    }

    /// Empties the x87 stack, as a call made with it empty leaves it.
    ///
    /// A callee may use all eight registers and returns with the stack
    /// empty but for its result, so a value the stack held before the call
    /// is gone after it, and a register read afterwards reads its own text
    /// variable, never a stale value.
    fn empty_x87(&mut self) {
        for i in 0..8 {
            let k = Key::Reg(st_register(i));
            self.env.vals.remove(&k);
            self.env.unset.insert(k);
            self.written_here.insert(k);
        }
    }

    /// Tells whether a callee is known to return a `float` or a `double`:
    /// its stated prototype or the type library declares one, else its
    /// signature does, else every exit leaves one
    /// ([`Function::ret_float`](crate::analysis::Function::ret_float)).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when known.
    fn callee_returns_float(&self, target: Option<u64>) -> bool {
        match stated_returns(self.ctx, target, target) {
            Some(r) => matches!(r, Returns::Float(_)),
            None => target
                .and_then(|t| self.ctx.analysis.function(t))
                .is_some_and(|f| {
                    f.signature.as_ref().map_or(f.ret_float.is_some(), |s| {
                        crate::analysis::decompile::float_return(&s.ret)
                    })
                }),
        }
    }

    /// Tells whether a plain call being lifted leaves a float in `st0` on a
    /// 32-bit target, and whether the text shows it.
    ///
    /// A callee declared to return a `float` or a `double` does, as does
    /// one whose every exit leaves one there
    /// ([`Function::ret_float`](crate::analysis::Function::ret_float)), and
    /// any callee, an indirect one included, whose result the code after
    /// the call reads off the x87 stack ([`x87::after_call`]); a call whose
    /// result goes straight to the function's own `ret` leaves the float
    /// the function returns. A result the code pops unread at once is left
    /// out of the text.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    /// * `target` - The callee's entry when known.
    ///
    /// # Returns
    ///
    /// `None` when the call leaves nothing, else whether the text binds
    /// the float it leaves.
    fn leaves_x87_float(&mut self, instr: &Instruction, target: Option<u64>) -> Option<bool> {
        let declared = self.callee_returns_float(target);
        let ctx = &*self.ctx;
        let after = x87::after_call(
            &|va| ctx.decode(va),
            &mut self.info,
            instr,
            &|va| ctx.block_starts.contains(&va),
            &|i| x87_callee(ctx, x87::named_target(i)),
        );
        match after {
            x87::After::Drops => Some(false),
            x87::After::Reads => Some(true),
            x87::After::Returns if ctx.ret_float && !ctx.ret_sse => Some(true),
            x87::After::Returns | x87::After::Neither => declared.then_some(true),
        }
    }

    /// Decides whether a call's result is read and in which register.
    ///
    /// The same decision the emission of the call binds by, callable
    /// before the call clears the environment: whether the instruction
    /// after it, the rest of its block, or the successors' liveness reads
    /// `rax`, and whether the float register alone is read instead. A
    /// later call's read of the float register ([`VECTOR_ARG_LANE`]) is no
    /// read of a result here.
    ///
    /// # Arguments
    ///
    /// * `next` - The instruction that runs after the call.
    /// * `rest` - The instructions after the call in its block.
    /// * `rax` - The integer return register.
    /// * `xmm0` - The float return register.
    ///
    /// # Returns
    ///
    /// `(rax is used, the result is a float in xmm0)`.
    pub(super) fn result_read(
        &mut self,
        next: Option<&Instruction>,
        rest: &[Instruction],
        rax: Key,
        xmm0: Key,
    ) -> (bool, bool) {
        let next_float =
            next.is_some_and(|n| self.reads_register(n, xmm0) && !self.reads_register(n, rax));
        let next_rax = next.is_some_and(|n| self.reads_register(n, rax));
        if rest.is_empty() {
            match self.regs_needed.as_ref() {
                Some(_) if next_float => (false, true),
                Some(m) => {
                    let r = m.contains_key(&rax);
                    let float = m.get(&xmm0).is_some_and(|lane| *lane > VECTOR_ARG_LANE);
                    (r, float && !r)
                }
                None if next.is_some() => (next_rax, next_float),
                None => (self.rax_live_out.unwrap_or(true), false),
            }
        } else {
            self.result_use(rest, rax, xmm0)
        }
    }

    /// Decides whether the instructions after a call read its result.
    ///
    /// The block's remaining instructions are scanned in order: a read of
    /// the register before a full write of it means the result is used, a
    /// full write or another call before any read means it is not. A `ret`
    /// ends the scan: it counts as a read of rax only when the function's
    /// result is not known to be unused and no float result was found. When
    /// the block ends undecided, rax follows the successors' liveness.
    ///
    /// # Arguments
    ///
    /// * `rest` - The instructions after the call in its block.
    /// * `rax` - The integer return register.
    /// * `xmm0` - The float return register.
    ///
    /// # Returns
    ///
    /// `(rax is used, the result is a float in xmm0)`.
    pub(super) fn result_use(&mut self, rest: &[Instruction], rax: Key, xmm0: Key) -> (bool, bool) {
        let mut rax_used: Option<bool> = None;
        let mut xmm_used: Option<bool> = None;
        let mut saw_ret = false;
        for i in rest {
            if matches!(i.flow_control(), FlowControl::Return) {
                saw_ret = true;
                break;
            }
            if rax_used.is_none() {
                if self.reads_register(i, rax) {
                    rax_used = Some(true);
                } else if self.writes_register(i, rax) {
                    rax_used = Some(false);
                }
            }
            if xmm_used.is_none() {
                if self.reads_register(i, xmm0) {
                    xmm_used = Some(true);
                } else if self.writes_register(i, xmm0) {
                    xmm_used = Some(false);
                }
            }
            if matches!(
                i.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                rax_used.get_or_insert(false);
                xmm_used.get_or_insert(false);
            }
            if rax_used.is_some() && xmm_used.is_some() {
                break;
            }
        }
        let xmm = xmm_used == Some(true);
        let rax = rax_used.unwrap_or_else(|| {
            if saw_ret {
                !xmm && !self.ctx.unused_result
            } else {
                self.rax_live_out.unwrap_or(true)
            }
        });
        (rax, xmm && !rax)
    }

    /// Tells whether the instructions after a call read the register a
    /// second result comes back in.
    ///
    /// The block's remaining instructions are scanned in order: a read
    /// before a full write or another call means it is read; a `ret`
    /// hands it on only when the function itself hands a second result
    /// back ([`Ctx::ret_rdx`]); a block that ends undecided follows the
    /// liveness after the call.
    ///
    /// # Arguments
    ///
    /// * `rest` - The instructions after the call in its block.
    /// * `rdx` - The second result's register.
    fn second_read(&mut self, rest: &[Instruction], rdx: Key) -> bool {
        for i in rest {
            if matches!(i.flow_control(), FlowControl::Return) {
                return self.ctx.ret_rdx;
            }
            if self.reads_register(i, rdx) {
                return true;
            }
            if self.writes_register(i, rdx)
                || matches!(
                    i.flow_control(),
                    FlowControl::Call | FlowControl::IndirectCall
                )
            {
                return false;
            }
        }
        self.regs_needed
            .as_ref()
            .is_none_or(|m| m.contains_key(&rdx))
    }

    /// Tells whether `instr` fully writes canonical register `key` (a whole
    /// register, not a byte or word lane).
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `key` - The register.
    pub(super) fn writes_register(&mut self, instr: &Instruction, key: Key) -> bool {
        let bitness = self.bitness();
        let info = self.info.info(instr);
        info.used_registers().iter().any(|ur| {
            Key::Reg(canon(ur.register(), bitness)) == key
                && matches!(ur.access(), OpAccess::Write | OpAccess::ReadWrite)
                && lane_bits(ur.register()) == 64
        })
    }

    /// Tells whether a callee is known to return a value: its stated
    /// prototype or its signature declares a non-`void` return, or some
    /// caller reads its result.
    ///
    /// An unknown callee is not, so a function ending in `f(); ret` stays
    /// `void` until something shows `f` produces a value.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when known.
    pub(super) fn callee_returns_value(&self, target: Option<u64>) -> bool {
        if let Some(p) = target.and_then(|t| self.ctx.overlay.prototypes.get(&t)) {
            return p.ret.is_some();
        }
        let Some(f) = target.and_then(|t| self.ctx.analysis.function(t)) else {
            return false;
        };
        match &f.signature {
            Some(sig) => sig.ret != "void",
            None => f.returns_value == Some(true),
        }
    }

    /// Tells whether a direct callee hands rax back untouched
    /// ([`Function::preserves_rax`](crate::analysis::Function::preserves_rax)).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    pub(super) fn callee_preserves_rax(&self, target: Option<u64>) -> bool {
        target
            .and_then(|t| self.ctx.analysis.function(t))
            .is_some_and(|f| f.preserves_rax)
    }

    /// Width in bits of a callee's result when it is narrower than the register.
    ///
    /// The stated prototype's or the declared return type decides when
    /// there is one; otherwise the widest read any caller makes of the result
    /// ([`Function::ret_width`](crate::analysis::Function::ret_width)).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    ///
    /// # Returns
    ///
    /// 8 or 16, or `None` when the result fills the register or nothing is
    /// known about it.
    pub(super) fn callee_return_bits(&self, target: Option<u64>) -> Option<u8> {
        if target.is_some_and(|t| self.ctx.overlay.prototypes.contains_key(&t)) {
            return match stated_returns(self.ctx, target, target)? {
                Returns::Int(bits) if bits <= 16 => Some(bits),
                Returns::Int(_) | Returns::Float(_) | Returns::Nothing => None,
            };
        }
        let f = target.and_then(|t| self.ctx.analysis.function(t))?;
        let bits = match &f.signature {
            Some(sig) => declared_bits(&sig.ret),
            None => f.ret_width?,
        };
        (bits <= 16).then_some(bits)
    }

    /// Width in bits every path of a direct callee WRITES of rax, when at
    /// most a byte or a word.
    ///
    /// Unlike [`Exec::callee_return_bits`] this is the machine's fact, not
    /// a reading convenience: a value that fits a byte but writes 32 of the
    /// 64 bits (`mov eax, 0x50`) still zeroes what it does not write, so
    /// only a genuine partial write leaves the caller's bits in place.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call is direct.
    ///
    /// # Returns
    ///
    /// 8 or 16, or `None` when some path defines the register fully.
    pub(super) fn callee_partial_lane(&self, target: Option<u64>) -> Option<u8> {
        target
            .and_then(|t| self.ctx.analysis.function(t))
            .and_then(|f| f.ret_partial)
    }

    /// Types the locals whose addresses a call receives.
    ///
    /// For a callee with a declared signature, an argument that is a stack
    /// address takes the type of the object the parameter declares (`const
    /// Core::Ptr<T> &` makes the local a `Core::Ptr<T>`), and the hidden
    /// result pointer of a class returned by value makes its local that
    /// class.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when known.
    pub(super) fn type_slot_arguments(&mut self, target: Option<u64>) {
        let Some(sig) = target
            .and_then(|t| self.ctx.analysis.function(t))
            .and_then(|f| f.signature.clone())
        else {
            return;
        };
        let hidden = usize::from(sig.by_pointer);
        let reads = self.callee_reg_params(target).unwrap_or(0);
        let member = sig.is_const
            || (crate::analysis::classes::class_of(&sig.name).is_some()
                && reads > sig.params.len() + hidden);
        let lead = usize::from(member) + hidden;
        for (p, r) in self.ctx.conv.args.iter().enumerate() {
            let Some(Expr::Sp(k)) = self.env.vals.get(&Key::Reg(*r)) else {
                continue;
            };
            let k = *k;
            let ty = if sig.by_pointer && p + 1 == lead {
                Some(sig.ret.clone())
            } else {
                p.checked_sub(lead)
                    .and_then(|j| sig.params.get(j))
                    .map(|t| crate::analysis::vtables::object_type(t))
            };
            if let Some(t) = ty.filter(|t| !t.is_empty()) {
                self.env.slot_types.insert(k, t);
            }
        }
    }

    /// Returns the class of the object a call's result points at.
    ///
    /// A declared return type `Foo *` or `Foo &` gives `Foo`, a class
    /// returned by value gives that class (the result pointer); an undeclared
    /// callee gives its hinted result class, else, when its first argument is
    /// a smart pointer `X<T>`, it is taken for the accessor and gives `T`
    /// (`Core::Ptr<T>::operator->`).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    /// * `arg0_class` - The class of the first argument's object, if known.
    pub(super) fn returned_class(&self, target: u64, arg0_class: Option<&str>) -> Option<String> {
        let f = self.ctx.analysis.function(target)?;
        match f.signature.as_ref() {
            Some(sig) if sig.by_pointer => Some(sig.ret.clone()),
            Some(sig) => crate::analysis::decompile::pointee_class(&sig.ret).map(str::to_owned),
            None => f
                .ret_hint
                .clone()
                .or_else(|| smart_pointee(arg0_class?).map(str::to_owned)),
        }
    }

    /// Returns the class of the object the value in argument register `i`
    /// points at ([`Exec::class_of_expr`]).
    ///
    /// # Arguments
    ///
    /// * `i` - Argument position.
    pub(super) fn arg_class(&self, i: usize) -> Option<String> {
        let r = self.ctx.conv.args.get(i)?;
        self.class_of_expr(self.env.vals.get(&Key::Reg(*r))?)
    }

    /// Returns the class of the object a value points at: a variable's class
    /// ([`Exec::class_of_key`]), for a local's address the type of the object
    /// stored there and for the local's word the pointee of that smart
    /// pointer, for the word a smart-pointer variable holds
    /// (`*(word*)ptr` with `ptr` a `Core::Ptr<T>`) the class `T`, for the
    /// address of a field of a class-typed variable the embedded object's
    /// type, or for a word loaded from such a field the field's hinted class
    /// (the pointee of an embedded smart pointer included).
    ///
    /// # Arguments
    ///
    /// * `e` - The value.
    pub(super) fn class_of_expr(&self, e: &Expr) -> Option<String> {
        match e {
            Expr::Var(k) => self.class_of_key(*k).or_else(|| match k {
                Key::Slot(o) => smart_pointee(self.env.slot_types.get(o)?).map(str::to_owned),
                _ => None,
            }),
            Expr::Sp(k) => self.env.slot_types.get(k).cloned(),
            Expr::Bin(Op::Add, a, b) => match (&**a, &**b) {
                (Expr::Var(k), Expr::Const(off)) => {
                    let c = self.class_of_key(*k)?;
                    self.ctx
                        .analysis
                        .classes
                        .field_types
                        .get(&(c, *off))
                        .cloned()
                }
                _ => None,
            },
            Expr::Deref(inner, _) => match &**inner {
                Expr::Sp(k) => smart_pointee(self.env.slot_types.get(k)?).map(str::to_owned),
                Expr::Var(k) => {
                    let c = self.class_of_key(*k)?;
                    smart_pointee(&c)
                        .map(str::to_owned)
                        .or_else(|| self.ctx.analysis.classes.field_hints.get(&(c, 0)).cloned())
                }
                Expr::Bin(Op::Add, a, b) => match (&**a, &**b) {
                    (Expr::Var(k), Expr::Const(off)) => {
                        let c = self.class_of_key(*k)?;
                        let key = (c, *off);
                        self.ctx
                            .analysis
                            .classes
                            .field_hints
                            .get(&key)
                            .cloned()
                            .or_else(|| {
                                smart_pointee(self.ctx.analysis.classes.field_types.get(&key)?)
                                    .map(str::to_owned)
                            })
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Returns the class of the object variable `key` points at: a declared
    /// parameter class, a class carried from a call result, or the class a
    /// constructor registered at a TLS slot or global.
    ///
    /// # Arguments
    ///
    /// * `key` - The variable.
    pub(super) fn class_of_key(&self, key: Key) -> Option<String> {
        match key {
            Key::Param(i) => self.ctx.param_class.get(&i).cloned(),
            Key::Reg(_) | Key::Slot(_) | Key::A64(_) => self.env.classes.get(&key).cloned(),
            Key::Global(addr, _) => match crate::analysis::decompile::expr::tls_slot(addr) {
                Some(off) => self.ctx.analysis.classes.tls_slots.get(&off).cloned(),
                None => self.ctx.analysis.classes.global_hints.get(&addr).cloned(),
            },
            Key::Tmp(_) => None,
        }
    }

    /// Resolves an indirect call through the vtable of the receiver's class.
    ///
    /// `call [vptr + k]` (or through a register holding that load) with
    /// `vptr = *(word*)p`, where `p` is a parameter with a declared class
    /// (`this`, `Foo *`, `const Foo &`), a variable holding the result of a
    /// call declared to return `Foo *`, or the word a smart pointer `X<T>`
    /// variable holds (`p = *(word*)ptr`, class `T`), is that class's
    /// virtual method in slot `k / word` when the class's vtable is known.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    pub(super) fn virtual_target(&mut self, instr: &Instruction) -> Option<Virtual> {
        let (recv, slot) = self.vtable_shape(instr)?;
        let class = self.class_of_expr(&recv)?;
        let shown = match &recv {
            Expr::Var(key) => Some(*key),
            Expr::Deref(inner, _) => match &**inner {
                Expr::Var(key) => Some(*key),
                _ => None,
            },
            _ => None,
        };
        let info = self.ctx.analysis.classes.by_name.get(&class)?;
        let entry = *info.slots.get(slot)?;
        Some(Virtual {
            receiver: recv,
            shown,
            class,
            entry,
            slot,
            pure: self.pure_stub(entry),
        })
    }

    /// Decomposes a call through a vtable.
    ///
    /// `call [vptr + k]` (or through a register holding that load) with
    /// `vptr = *(word*)recv` is a call through slot `k / word` of the
    /// receiver's vtable.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call.
    ///
    /// # Returns
    ///
    /// The receiver expression and the slot index, or `None` when the
    /// operand has another shape or `k` is not a whole slot.
    pub(super) fn vtable_shape(&mut self, instr: &Instruction) -> Option<(Expr, usize)> {
        if !matches!(instr.op0_kind(), OpKind::Memory | OpKind::Register) {
            return None;
        }
        let Expr::Deref(addr, _) = self.val(instr, 0) else {
            return None;
        };
        let (vptr, k) = match *addr {
            Expr::Bin(Op::Add, a, b) => match (*a, *b) {
                (v, Expr::Const(k)) | (Expr::Const(k), v) => (v, k),
                _ => return None,
            },
            other => (other, 0),
        };
        let Expr::Deref(recv, _) = vptr else {
            return None;
        };
        if matches!(*recv, Expr::Sp(_)) {
            return None;
        }
        let word = u64::try_from(self.ctx.conv.word).ok()?;
        if k % word != 0 {
            return None;
        }
        Some((*recv, usize::try_from(k / word).ok()?))
    }
}

/// Most instructions [`reads_whole`] reads from a callee's entry.
const WHOLE_SCAN: usize = 16;

/// Tells whether a direct callee's first use of an argument register reads
/// all of it, its upper half included.
///
/// The entry's straight-line instructions are read up to the first that
/// touches the register, a branch, or [`WHOLE_SCAN`] of them: Rust's debug
/// code spills a `usize` it was handed whole (`mov [rsp+38h], rcx`), where a
/// 32-bit parameter is read or spilled as `ecx`.
///
/// # Arguments
///
/// * `ctx` - The program and the decoder.
/// * `target` - The callee's entry.
/// * `r` - The argument register.
fn reads_whole(ctx: &Ctx<'_>, target: u64, r: Register) -> bool {
    let full = r.full_register();
    let mut factory = InstructionInfoFactory::new();
    let mut va = target;
    for _ in 0..WHOLE_SCAN {
        let Some(i) = ctx.decode(va) else {
            return false;
        };
        if let Some(u) = factory
            .info(&i)
            .used_registers()
            .iter()
            .find(|u| u.register().full_register() == full)
        {
            return u.register() == full
                && matches!(
                    u.access(),
                    OpAccess::Read | OpAccess::ReadWrite | OpAccess::ReadCondWrite
                );
        }
        if i.flow_control() != FlowControl::Next {
            return false;
        }
        va = i.next_ip();
    }
    false
}

/// Tells whether any rendered argument names a variable, as a whole word.
///
/// # Arguments
///
/// * `args` - The rendered arguments.
/// * `name` - The variable's rendered name.
fn names_variable(args: &[String], name: &str) -> bool {
    args.iter().any(|a| {
        a.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .any(|w| w == name)
    })
}

/// Finds the functions that stand in vtables for a pure virtual slot.
///
/// The stub that reports a pure virtual call fills every pure slot of
/// every abstract class, so it sits at many slot indexes, and it never
/// returns; a real method shared by a hierarchy sits at one index, and a
/// folded `return 0` at many returns.
///
/// # Arguments
///
/// * `analysis` - The classes and their vtables.
///
/// # Returns
///
/// The entries of the functions found at two or more slot indexes that
/// no path returns from: no `ret`, no jump out of the function.
fn pure_stubs(analysis: &crate::analysis::Analysis) -> BTreeSet<u64> {
    use crate::analysis::BlockTerm;
    let mut indexes: BTreeMap<u64, BTreeSet<usize>> = BTreeMap::new();
    for info in analysis.classes.by_name.values() {
        for (i, e) in info.slots.iter().enumerate() {
            indexes.entry(*e).or_default().insert(i);
        }
    }
    indexes
        .into_iter()
        .filter(|(_, at)| at.len() >= 2)
        .map(|(e, _)| e)
        .filter(|e| {
            analysis.function(*e).is_some_and(|f| {
                let inside = |s: &u64| f.blocks.iter().any(|b| b.start == *s);
                !f.blocks.iter().any(|b| match b.term {
                    BlockTerm::Ret => true,
                    BlockTerm::Jmp => !b.successors.iter().all(inside),
                    BlockTerm::Indirect => b.successors.is_empty(),
                    BlockTerm::Cond | BlockTerm::Call | BlockTerm::Fall | BlockTerm::Invalid => {
                        false
                    }
                })
            })
        })
        .collect()
}
