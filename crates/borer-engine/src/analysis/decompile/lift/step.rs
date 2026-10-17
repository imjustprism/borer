//! One instruction at a time: the dispatcher, control transfers, flags, and the
//! instructions left unmodeled.

use super::*;

/// Tells whether a jump goes to `T + sext(*(int32_t*)(T + i * 4))`.
///
/// That is the entry of a table of 32-bit offsets from the table's own
/// address `T`, how a compiler spells a switch in position-independent
/// code. Its targets are code of the function the table serves.
///
/// # Arguments
///
/// * `target` - The jump's target.
fn relative_table_jump(target: &Expr) -> bool {
    let Expr::Bin(Op::Add, a, b) = target else {
        return false;
    };
    let (table, entry) = match (a.as_ref(), b.as_ref()) {
        (Expr::Const(t), e) | (e, Expr::Const(t)) => (*t, e),
        _ => return false,
    };
    let Expr::Sext(load, 32) = entry else {
        return false;
    };
    let Expr::Deref(addr, Ty::U32) = load.as_ref() else {
        return false;
    };
    let Expr::Bin(Op::Add, l, r) = addr.as_ref() else {
        return false;
    };
    match (l.as_ref(), r.as_ref()) {
        (Expr::Const(t), Expr::Bin(Op::Mul, _, n)) | (Expr::Bin(Op::Mul, _, n), Expr::Const(t)) => {
            *t == table && matches!(n.as_ref(), Expr::Const(4))
        }
        _ => false,
    }
}

impl<'a> Exec<'_, 'a> {
    /// Lifts `jmp target` leaving the function as a tail call.
    ///
    /// # Arguments
    ///
    /// * `target` - The jump target outside this function.
    pub(super) fn tail_call(&mut self, target: u64) {
        self.forwarding = true;
        let (mut args, rendered, mut values) = self.args_for(Some(target));
        let arity = self.callee_stack_args(Some(target));
        let written = self.before_call(arity, false, rendered, &values, &[]);
        if Self::reads_any(&values, &written) {
            (args, _, values) = self.args_for(Some(target));
        }
        self.forwarding = false;
        self.enter_call(false, &[]);
        let name = bare(&name_of(self.ctx.analysis, self.ctx.overlay, target)).to_owned();
        emit_line!(self, format!("return {name}({});", args.join(", ")));
        self.record_call(
            Callee::Direct(target),
            values,
            None,
            None,
            false,
            Shown::Tail,
        );
        self.after_call(false);
    }

    /// Lifts an indirect jump that is not a resolved jump table.
    ///
    /// A resolvable callee is a tail call; anything else is spelled as GCC's
    /// computed goto, `goto *target;`, and so is a jump to an entry of a
    /// table of offsets from the table's own address
    /// ([`relative_table_jump`]), as computed or as the variable a target
    /// too wide to carry was written out to: a switch the analysis could not
    /// bound, whose cases are this function's code, not a callee taking
    /// arguments.
    ///
    /// # Arguments
    ///
    /// * `instr` - The jump.
    pub(super) fn indirect_jump(&mut self, instr: &Instruction) {
        let reached = self
            .direct_target(instr)
            .or_else(|| Self::import_slot(instr));
        let switch = reached.is_none()
            && self.jump_target(instr).is_some_and(|t| match &t {
                Expr::Var(k) => self.big_written.get(k).is_some_and(relative_table_jump),
                other => relative_table_jump(other),
            });
        self.forwarding = reached.is_some();
        self.call_through = reached
            .is_none()
            .then(|| self.through_register(instr))
            .flatten();
        let (mut args, rendered, mut values) = self.args_for(reached);
        let arity = self.callee_stack_args(reached).or_else(|| {
            (self.bitness() == 32 && self.bodyless(reached)).then_some(self.args_pushed)
        });
        let held = self.target_registers(instr);
        let written = self.before_call(arity, false, rendered, &values, &held);
        if Self::reads_any(&values, &written) {
            (args, _, values) = self.args_for(reached);
        }
        self.call_through = None;
        self.forwarding = false;
        let callee = if switch { None } else { self.callee(instr) };
        let target = self.val(instr, 0);
        let through = self.emit.then(|| match self.direct_target(instr) {
            Some(t) => Callee::Direct(t),
            None => Callee::Through(self.call_target(instr)),
        });
        self.enter_call(false, &held);
        match callee {
            Some(c) => {
                emit_line!(self, format!("return {c}({});", args.join(", ")));
                if let Some(t) = through {
                    self.record_call(t, values, None, None, false, Shown::Tail);
                }
            }
            None => {
                let n = self.names();
                let shown = target.render(&n);
                emit_line!(
                    self,
                    match target {
                        Expr::Var(_) | Expr::Const(_) => format!("goto *{shown};"),
                        _ => format!("goto *({shown});"),
                    }
                );
                if self.emit {
                    self.record(EffectKind::Jump(target));
                }
            }
        }
        self.after_call(false);
    }

    /// Where an indirect jump goes, as an expression: the register's value,
    /// or the word its memory operand reads.
    ///
    /// # Arguments
    ///
    /// * `jmp` - The indirect jump.
    pub(super) fn jump_target(&mut self, jmp: &Instruction) -> Option<Expr> {
        match jmp.op0_kind() {
            OpKind::Register => Some(self.reg_read(jmp.op0_register())),
            OpKind::Memory => {
                let ty = if self.ctx.bitness == 64 {
                    Ty::U64
                } else {
                    Ty::U32
                };
                Some(Expr::Deref(Box::new(self.addr(jmp, 0)), ty))
            }
            _ => None,
        }
    }

    /// Recovers the switch index of a jump-table dispatch.
    ///
    /// The index is the expression the table lookup was indexed with (found
    /// inside the jump target `table + sext(*(table + idx * 4))`, or in the
    /// expression a too-wide target was written out as), else the register
    /// compared by the nearest preceding `cmp` in this block or the previous
    /// one, else the target itself so the dispatch stays explicit.
    ///
    /// # Arguments
    ///
    /// * `jmp` - The indirect jump.
    /// * `instrs` - This block's instructions.
    /// * `prev` - The previous block's instructions, if any.
    pub(super) fn switch_index(
        &mut self,
        jmp: &Instruction,
        instrs: &[Instruction],
        prev: Option<&[Instruction]>,
    ) -> Option<Expr> {
        let target = match jmp.op0_kind() {
            OpKind::Register => Some(self.reg_read(jmp.op0_register())),
            OpKind::Memory => Some(self.addr(jmp, 0)),
            _ => None,
        };
        if let Some(t) = &target
            && let Some(idx) = table_index(t)
        {
            return Some(self.byte_table_index(idx, jmp, instrs));
        }
        if let Some(Expr::Var(k)) = &target
            && let Some(idx) = self.big_written.get(k).and_then(table_index)
        {
            return Some(self.byte_table_index(idx, jmp, instrs));
        }
        if let Some(reg) = last_cmp_register(instrs).or_else(|| last_cmp_register(prev?)) {
            return Some(self.reg_read(reg));
        }
        target
    }

    /// The index a byte table is read at, for a jump table reached through
    /// one: what the switch switches on.
    ///
    /// Where several cases share a body, a compiler reads a jump table's
    /// slot from a table of bytes (`movzx eax, byte [eax+T]`): `jump[index
    /// [value]]`. The resolver expands both, so the case labels number the
    /// value, and the switch has to read the value too, not the byte, where
    /// `case 4` would mean the fifth slot of the jump table. The value is the
    /// byte read's address less the table's own: the read's displacement,
    /// plus, in 64-bit code, the image base its other register holds, which
    /// keeps any offset the code took from the value (`add eax, -2` before
    /// the read folds into its address as `x + (T - 2)`, and the cases count
    /// `x - 2`); an address that fits none of this gives its terms but the
    /// constant. The value is taken here, before anything at the block's end
    /// writes the byte out and the switch, reading the same expression, is
    /// moved onto the variable that then holds the byte.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index the jump table is read at.
    /// * `jmp` - The jump.
    /// * `instrs` - The block's instructions.
    fn byte_table_index(&self, idx: Expr, jmp: &Instruction, instrs: &[Instruction]) -> Expr {
        let Expr::Deref(addr, Ty::U8) = &idx else {
            return idx;
        };
        if !self.ctx.analysis.indexed_tables.contains(&jmp.ip()) {
            return idx;
        }
        let read = instrs.iter().rev().find(|i| {
            i.mnemonic() == Mnemonic::Movzx
                && i.op1_kind() == OpKind::Memory
                && i.memory_size() == MemorySize::UInt8
        });
        let base = read.and_then(|read| {
            let disp = crate::disasm::displacement(read, self.bitness()).cast_unsigned();
            match (read.memory_base(), read.memory_index()) {
                (_, Register::None) => Some(disp),
                (a, b) => match (self.reg_read(a), self.reg_read(b)) {
                    (Expr::Const(image), other) | (other, Expr::Const(image))
                        if !matches!(other, Expr::Const(_)) =>
                    {
                        Some(image.wrapping_add(disp))
                    }
                    _ => None,
                },
            }
        });
        match (base, addr.as_ref()) {
            (Some(base), _) => fold(
                Op::Add,
                (**addr).clone(),
                Expr::Const(base.wrapping_neg()),
                64,
            ),
            (None, Expr::Bin(Op::Add, l, r)) => match (l.as_ref(), r.as_ref()) {
                (Expr::Const(_), other) | (other, Expr::Const(_)) => other.clone(),
                _ => idx,
            },
            (None, _) => idx,
        }
    }

    /// Lifts `ret`.
    ///
    /// A byte or word written into rax before the return (`mov al, x`,
    /// `setcc al`) is what the caller reads, so the merge with the old upper
    /// bits is dropped and the function's return width recorded. A function
    /// whose return is floating point hands the value back in `xmm0`
    /// instead, or in `st0` on a 32-bit target, where the top of the x87
    /// stack is the result whatever wrote it, unless the function returns
    /// in `xmm0` there too ([`Ctx::ret_sse`]), whose width a `float` value
    /// returned sets.
    pub(super) fn ret(&mut self) {
        if !self.emit {
            return;
        }
        let x87 = self.ctx.ret_float && self.bitness() == 32 && !self.ctx.ret_sse;
        let rax = match (self.ctx.ret_float, x87) {
            (true, true) => Key::Reg(Register::ST0),
            (true, false) => Key::Reg(Register::XMM0),
            (false, _) => self.canon(self.rax()),
        };
        let (line, value) = match self.env.vals.get(&rax).cloned() {
            Some(v) if self.ctx.ret_sse => {
                let bits = match v {
                    Expr::Deref(_, Ty::F32) | Expr::Cast(_, Ty::F32) | Expr::FConst(_, Ty::F32) => {
                        32
                    }
                    Expr::Const(_) => 0,
                    _ => 64,
                };
                self.ctx.ret_bits = self.ctx.ret_bits.max(bits);
                (format!("return {};", v.render(&self.names())), Some(v))
            }
            Some(v) => {
                let (v, bits) = strip_partial_result(v);
                self.ctx.ret_bits = self.ctx.ret_bits.max(bits.min(self.ctx.ret_lane));
                (format!("return {};", v.render(&self.names())), Some(v))
            }
            None if (self.ctx.rax_written || self.env.result_in_rax || x87)
                && !self.ctx.unused_result =>
            {
                self.ctx.ret_bits = self.ctx.ret_bits.max(self.ctx.ret_lane);
                (
                    format!("return {};", self.names().key(rax)),
                    Some(Expr::Var(rax)),
                )
            }
            None => ("return;".to_owned(), None),
        };
        let rdx = self.canon(Register::RDX);
        let (line, value) = match self.env.vals.get(&rdx).cloned() {
            Some(second) if self.ctx.ret_rdx && second != Expr::Var(rdx) => {
                let (line, value) = match value {
                    Some(v) if v.mentions(rdx) => {
                        let t = self.tmp_of(&v, self.word_ty());
                        (format!("return {};", t.render(&self.names())), Some(t))
                    }
                    other => (line, other),
                };
                self.declare(rdx, self.word_ty());
                let n = self.names();
                emit_line!(self, format!("{} = {};", n.key(rdx), second.render(&n)));
                self.record(EffectKind::Assign(rdx, second, 64));
                (line, value)
            }
            Some(_) | None => (line, value),
        };
        emit_line!(self, line);
        self.record(EffectKind::Return(value));
    }

    /// Executes one non-control instruction.
    ///
    /// The one-operand multiply and divide come in two shapes: from 16 bits
    /// up they pair rdx with rax, while the byte forms keep everything in
    /// ax (`mul cl` is `ax = al * cl`, `div cl` is `al = ax / cl` with the
    /// remainder in `ah`).
    ///
    /// Notable idioms: `sub rsp, rax` right after a call that preserved the
    /// constant frame size in rax is the `__chkstk` frame adjustment;
    /// `xorps x, x` and friends zero a register; one-operand `mul`/`imul`
    /// produce `rdx:rax` with CF=OF meaning the high half is significant;
    /// `div`/`idiv` are modeled when rdx holds the zero/sign extension of
    /// rax (the `xor edx, edx` / `cqo` that precedes nearly every division)
    /// and left as asm when it holds a real high half; floating
    /// compares set CF/ZF like an unsigned compare of the operands (unordered
    /// results are not modeled); `leave` is `rsp = rbp; pop rbp`. Anything
    /// without a model goes to [`Exec::unmodeled`].
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    pub(super) fn step(&mut self, instr: &Instruction) {
        let mn = instr.mnemonic();
        let bits = op_bits(instr);
        let chkstk = self.env.chkstk.take();
        if self.entry {
            self.empty_x87_at_entry();
        }
        if self.x87(instr) {
            return;
        }
        match mn {
            Mnemonic::Nop
            | Mnemonic::Fnop
            | Mnemonic::Endbr64
            | Mnemonic::Endbr32
            | Mnemonic::Pause
            | Mnemonic::Prefetchw
            | Mnemonic::Prefetcht0
            | Mnemonic::Prefetcht1
            | Mnemonic::Prefetcht2
            | Mnemonic::Prefetchnta
            | Mnemonic::Lfence
            | Mnemonic::Mfence
            | Mnemonic::Sfence
            | Mnemonic::Vzeroupper => {}
            Mnemonic::Cld => self.env.df = Some(false),
            Mnemonic::Std => self.env.df = Some(true),
            Mnemonic::Movsb | Mnemonic::Movsw | Mnemonic::Movsd | Mnemonic::Movsq
                if matches!(instr.op0_kind(), OpKind::MemoryESRDI | OpKind::MemoryESEDI) =>
            {
                self.string_op(instr, false, bits);
            }
            Mnemonic::Movss | Mnemonic::Movsd | Mnemonic::Vmovss | Mnemonic::Vmovsd
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Register
                    && instr.op1_kind() == OpKind::Register =>
            {
                let ty = match mn {
                    Mnemonic::Movss | Mnemonic::Vmovss => Ty::F32,
                    _ => Ty::F64,
                };
                let dst = self.val(instr, 0);
                let src = self.val(instr, 1);
                let vex = matches!(mn, Mnemonic::Vmovss | Mnemonic::Vmovsd);
                if vex || !keeps_vector(&dst) {
                    let low = scalar_lane(src, ty);
                    if vex {
                        self.float_write(instr, low, ty);
                    } else {
                        self.write_scalar_lane(instr, low, ty, &dst);
                    }
                } else {
                    self.note_reg_ty(instr, ty);
                    let name = format!("{mn:?}").to_lowercase();
                    self.write_op0(instr, Expr::Call(name, vec![dst, float_bits(src, ty)]));
                }
            }
            Mnemonic::Vmovss | Mnemonic::Vmovsd
                if instr.op_count() == 3 && instr.op0_kind() == OpKind::Register =>
            {
                let ty = if mn == Mnemonic::Vmovss {
                    Ty::F32
                } else {
                    Ty::F64
                };
                let upper = self.val(instr, 1);
                let low = scalar_lane(self.val(instr, 2), ty);
                self.write_scalar_lane(instr, low, ty, &upper);
            }
            Mnemonic::Movlps | Mnemonic::Movlpd
                if instr.op_count() == 2 && instr.op0_kind() == OpKind::Register =>
            {
                if mn == Mnemonic::Movlpd {
                    self.note_reg_ty(instr, Ty::F64);
                }
                let dst = self.val(instr, 0);
                let src = self.val(instr, 1);
                let name = format!("{mn:?}").to_lowercase();
                self.write_op0(instr, Expr::Call(name, vec![dst, src]));
            }
            Mnemonic::Movlps | Mnemonic::Movlpd if instr.op_count() == 2 => {
                let v = self.val(instr, 1);
                self.write_op0(instr, v);
            }
            Mnemonic::Movss | Mnemonic::Vmovss | Mnemonic::Movsd | Mnemonic::Vmovsd
                if instr.op_count() == 2 && instr.op0_kind() == OpKind::Memory =>
            {
                let bits = if matches!(mn, Mnemonic::Movss | Mnemonic::Vmovss) {
                    32
                } else {
                    64
                };
                let src = self.val(instr, 1);
                let (ty, v) = if let Expr::Var(k) = &src
                    && self
                        .big_written
                        .get(k)
                        .is_some_and(|full| moved_lane_mask(full, bits).is_some())
                {
                    let ty = if bits <= 32 { Ty::U32 } else { Ty::U64 };
                    (ty, src)
                } else {
                    scalar_moved(src, bits)
                };
                let addr = self.tls_to_global(self.addr(instr, 0));
                self.store_at(addr, ty, v);
            }
            Mnemonic::Mov
            | Mnemonic::Movzx
            | Mnemonic::Movq
            | Mnemonic::Movd
            | Mnemonic::Movsd
            | Mnemonic::Movss
            | Mnemonic::Movaps
            | Mnemonic::Movups
            | Mnemonic::Movapd
            | Mnemonic::Movupd
            | Mnemonic::Movdqa
            | Mnemonic::Movdqu
            | Mnemonic::Movdq2q
            | Mnemonic::Movq2dq
            | Mnemonic::Lddqu
            | Mnemonic::Vmovaps
            | Mnemonic::Vmovups
            | Mnemonic::Vmovapd
            | Mnemonic::Vmovupd
            | Mnemonic::Vmovdqa
            | Mnemonic::Vmovdqu
            | Mnemonic::Vmovd
            | Mnemonic::Vmovq
            | Mnemonic::Vmovss
            | Mnemonic::Vmovsd
            | Mnemonic::Movntps
            | Mnemonic::Movntpd
            | Mnemonic::Movntdq
            | Mnemonic::Movntdqa
            | Mnemonic::Movnti
            | Mnemonic::Movntq
                if instr.op_count() == 2 =>
            {
                let v = self.val(instr, 1);
                let v = match mn {
                    Mnemonic::Movss | Mnemonic::Vmovss => {
                        self.note_reg_ty(instr, Ty::F32);
                        float_bits(v, Ty::F32)
                    }
                    Mnemonic::Movsd | Mnemonic::Vmovsd => {
                        self.note_reg_ty(instr, Ty::F64);
                        float_bits(v, Ty::F64)
                    }
                    Mnemonic::Movd | Mnemonic::Vmovd
                        if instr.op0_kind() == OpKind::Register
                            && instr.op0_register().is_vector_register() =>
                    {
                        mask(v, 0xffff_ffff)
                    }
                    _ => v,
                };
                self.write_op0(instr, v);
            }
            Mnemonic::Stmxcsr | Mnemonic::Vstmxcsr
                if instr.op_count() == 1 && instr.op0_kind() == OpKind::Memory =>
            {
                self.store(instr, Expr::Call("stmxcsr".to_owned(), Vec::new()));
            }
            Mnemonic::Ldmxcsr | Mnemonic::Vldmxcsr if instr.op_count() == 1 => {
                let v = self.val(instr, 0);
                let n = self.names();
                emit_line!(self, format!("ldmxcsr({});", v.render(&n)));
                self.record(EffectKind::Unmodeled);
            }
            Mnemonic::Addss
            | Mnemonic::Addsd
            | Mnemonic::Subss
            | Mnemonic::Subsd
            | Mnemonic::Mulss
            | Mnemonic::Mulsd
            | Mnemonic::Divss
            | Mnemonic::Divsd
            | Mnemonic::Minss
            | Mnemonic::Minsd
            | Mnemonic::Maxss
            | Mnemonic::Maxsd
                if instr.op_count() == 2 =>
            {
                let ty = scalar_ty(mn);
                let upper = self.val(instr, 0);
                let l = scalar_lane(upper.clone(), ty);
                let r = scalar_lane(self.val(instr, 1), ty);
                let v = fold(float_op(mn), l, r, bits);
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Vaddss
            | Mnemonic::Vaddsd
            | Mnemonic::Vsubss
            | Mnemonic::Vsubsd
            | Mnemonic::Vmulss
            | Mnemonic::Vmulsd
            | Mnemonic::Vdivss
            | Mnemonic::Vdivsd
            | Mnemonic::Vminss
            | Mnemonic::Vminsd
            | Mnemonic::Vmaxss
            | Mnemonic::Vmaxsd
                if instr.op_count() == 3 =>
            {
                let ty = scalar_ty(mn);
                let upper = self.val(instr, 1);
                let l = scalar_lane(upper.clone(), ty);
                let r = scalar_lane(self.val(instr, 2), ty);
                let v = fold(float_op(mn), l, r, bits);
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Sqrtss | Mnemonic::Sqrtsd if instr.op_count() == 2 => {
                let ty = scalar_ty(mn);
                let upper = self.val(instr, 0);
                let v = Expr::Un(UnOp::Sqrt, Box::new(scalar_lane(self.val(instr, 1), ty)));
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Vsqrtss | Mnemonic::Vsqrtsd if instr.op_count() == 3 => {
                let ty = scalar_ty(mn);
                let upper = self.val(instr, 1);
                let v = Expr::Un(UnOp::Sqrt, Box::new(scalar_lane(self.val(instr, 2), ty)));
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Vfmadd132ss
            | Mnemonic::Vfmadd132sd
            | Mnemonic::Vfmadd213ss
            | Mnemonic::Vfmadd213sd
            | Mnemonic::Vfmadd231ss
            | Mnemonic::Vfmadd231sd
            | Mnemonic::Vfmsub132ss
            | Mnemonic::Vfmsub132sd
            | Mnemonic::Vfmsub213ss
            | Mnemonic::Vfmsub213sd
            | Mnemonic::Vfmsub231ss
            | Mnemonic::Vfmsub231sd
                if instr.op_count() == 3 =>
            {
                let ty = scalar_ty(mn);
                let a = scalar_lane(self.val(instr, 0), ty);
                let b = scalar_lane(self.val(instr, 1), ty);
                let c = scalar_lane(self.val(instr, 2), ty);
                let (x, y, z) = match mn {
                    Mnemonic::Vfmadd132ss
                    | Mnemonic::Vfmadd132sd
                    | Mnemonic::Vfmsub132ss
                    | Mnemonic::Vfmsub132sd => (a, c, b),
                    Mnemonic::Vfmadd213ss
                    | Mnemonic::Vfmadd213sd
                    | Mnemonic::Vfmsub213ss
                    | Mnemonic::Vfmsub213sd => (b, a, c),
                    _ => (b, c, a),
                };
                let add = matches!(
                    mn,
                    Mnemonic::Vfmadd132ss
                        | Mnemonic::Vfmadd132sd
                        | Mnemonic::Vfmadd213ss
                        | Mnemonic::Vfmadd213sd
                        | Mnemonic::Vfmadd231ss
                        | Mnemonic::Vfmadd231sd
                );
                let prod = fold(Op::FMul, x, y, bits);
                let v = fold(if add { Op::FAdd } else { Op::FSub }, prod, z, bits);
                self.float_write(instr, v, ty);
            }
            Mnemonic::Cvtsi2ss | Mnemonic::Cvtsi2sd if instr.op_count() == 2 => {
                let ty = scalar_ty(mn);
                let upper = self.val(instr, 0);
                let src_bits = src_bits(instr, 1);
                let v = Expr::Cast(Box::new(sign_extend(self.val(instr, 1), src_bits)), ty);
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Vcvtsi2ss | Mnemonic::Vcvtsi2sd if instr.op_count() == 3 => {
                let ty = scalar_ty(mn);
                let upper = self.val(instr, 1);
                let src_bits = src_bits(instr, 2);
                let v = Expr::Cast(Box::new(sign_extend(self.val(instr, 2), src_bits)), ty);
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Cvttss2si
            | Mnemonic::Cvttsd2si
            | Mnemonic::Vcvttss2si
            | Mnemonic::Vcvttsd2si
                if instr.op_count() == 2 =>
            {
                let src = if matches!(mn, Mnemonic::Cvttss2si | Mnemonic::Vcvttss2si) {
                    Ty::F32
                } else {
                    Ty::F64
                };
                let v = Expr::Cast(
                    Box::new(scalar_lane(self.val(instr, 1), src)),
                    Ty::from_bits(bits),
                );
                self.write_op0(instr, v);
            }
            Mnemonic::Cvtss2si | Mnemonic::Cvtsd2si | Mnemonic::Vcvtss2si | Mnemonic::Vcvtsd2si
                if instr.op_count() == 2 =>
            {
                let src = if matches!(mn, Mnemonic::Cvtss2si | Mnemonic::Vcvtss2si) {
                    Ty::F32
                } else {
                    Ty::F64
                };
                let lane = scalar_lane(self.val(instr, 1), src);
                let v = Expr::Cast(
                    Box::new(Expr::Call("rint".to_owned(), vec![lane])),
                    Ty::from_bits(bits),
                );
                self.write_op0(instr, v);
            }
            Mnemonic::Cvtss2sd | Mnemonic::Cvtsd2ss if instr.op_count() == 2 => {
                let ty = scalar_ty(mn);
                let from = if ty == Ty::F64 { Ty::F32 } else { Ty::F64 };
                let upper = self.val(instr, 0);
                let v = Expr::Cast(Box::new(scalar_lane(self.val(instr, 1), from)), ty);
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Vcvtss2sd | Mnemonic::Vcvtsd2ss if instr.op_count() == 3 => {
                let ty = scalar_ty(mn);
                let from = if ty == Ty::F64 { Ty::F32 } else { Ty::F64 };
                let upper = self.val(instr, 1);
                let v = Expr::Cast(Box::new(scalar_lane(self.val(instr, 2), from)), ty);
                self.write_scalar_lane(instr, v, ty, &upper);
            }
            Mnemonic::Xorps | Mnemonic::Xorpd | Mnemonic::Andps | Mnemonic::Andpd
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Register
                    && instr.op1_kind() == OpKind::Memory
                    && self.float_mask(instr).is_some() =>
            {
                let Some((abs, ty, broadcast)) = self.float_mask(instr) else {
                    return;
                };
                let x = self.val(instr, 0);
                let v = masked_lanes(abs, ty, broadcast, x);
                if matches!(v, Expr::Un(..)) {
                    self.float_write(instr, v, ty);
                } else {
                    self.stamp_reg_ty(instr, Ty::U64);
                    self.write_op0(instr, v);
                }
            }
            Mnemonic::Movsx | Mnemonic::Movsxd if instr.op_count() == 2 => {
                let src_bits = src_bits(instr, 1);
                let v = sign_extend(self.val(instr, 1), src_bits);
                self.write_op0(instr, v);
            }
            Mnemonic::Movbe if instr.op_count() == 2 => {
                let v = unary(UnOp::Bswap, self.val(instr, 1), bits);
                self.write_op0(instr, v);
            }
            Mnemonic::Lea if instr.op_count() == 2 && instr.op0_kind() == OpKind::Register => {
                let a = self.addr(instr, 1);
                let v = match a {
                    Expr::Const(t) if !self.ctx.overlay.names.contains_key(&t) => {
                        literal_at(self.ctx.program, t, &self.ctx.own_name).map_or(a, Expr::Str)
                    }
                    other => other,
                };
                self.reg_write(instr.op0_register(), v);
            }
            Mnemonic::Add | Mnemonic::Sub | Mnemonic::And | Mnemonic::Or | Mnemonic::Xor
                if instr.has_lock_prefix()
                    && instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Memory =>
            {
                let v = self.val(instr, 1);
                self.locked(instr, bits, mn, &v);
            }
            Mnemonic::Inc | Mnemonic::Dec
                if instr.has_lock_prefix()
                    && instr.op_count() == 1
                    && instr.op0_kind() == OpKind::Memory =>
            {
                let op = if mn == Mnemonic::Inc {
                    Mnemonic::Add
                } else {
                    Mnemonic::Sub
                };
                self.locked(instr, bits, op, &Expr::Const(1));
            }
            Mnemonic::Add
            | Mnemonic::Sub
            | Mnemonic::And
            | Mnemonic::Or
            | Mnemonic::Xor
            | Mnemonic::Shl
            | Mnemonic::Sal
            | Mnemonic::Shr
            | Mnemonic::Sar
            | Mnemonic::Rol
            | Mnemonic::Ror
                if instr.op_count() == 2 =>
            {
                let op = match mn {
                    Mnemonic::Add => Op::Add,
                    Mnemonic::Sub => Op::Sub,
                    Mnemonic::And => Op::And,
                    Mnemonic::Or => Op::Or,
                    Mnemonic::Xor => Op::Xor,
                    Mnemonic::Shl | Mnemonic::Sal => Op::Shl,
                    Mnemonic::Shr => Op::Shr,
                    Mnemonic::Sar => Op::Sar,
                    Mnemonic::Rol => Op::Rol(bits),
                    _ => Op::Ror(bits),
                };
                if mn == Mnemonic::Sub
                    && instr.op0_kind() == OpKind::Register
                    && instr.op0_register() == self.rsp()
                    && instr.op1_kind() == OpKind::Register
                    && let Some(c) = chkstk
                    && !self
                        .env
                        .vals
                        .contains_key(&self.canon(instr.op1_register()))
                {
                    if let Some(sp) = self.env.sp {
                        self.env.sp = Some(sp.wrapping_sub_unsigned(c));
                    }
                    return;
                }
                let l = self.val(instr, 0);
                let l = match (op, bits) {
                    (Op::Shr, b) if b < 64 => mask(l, (1u64 << b) - 1),
                    (Op::Sar, b) if b < 64 => sign_extend(l, b),
                    _ => l,
                };
                let r = self.val(instr, 1);
                let r = match op {
                    Op::Shl | Op::Shr | Op::Sar if bits < 64 => {
                        fold(Op::And, r, Expr::Const(31), bits)
                    }
                    _ => r,
                };
                let (l, r) = if bits == 64 && self.bitness() == 64 {
                    (widen64(l), widen64(r))
                } else {
                    (l, r)
                };
                let v = fold(op, l.clone(), r.clone(), bits);
                let needed = self.flags_needed;
                let reads_overflow = needed & RflagsBits::OF != 0;
                self.flags = match (mn, &r) {
                    (Mnemonic::Sub | Mnemonic::Add, _) if self.zero_or_sign_only() => {
                        Flags::Result(v.clone(), bits)
                    }
                    (Mnemonic::Sub, _) => Flags::Cmp(l, r, bits),
                    (Mnemonic::Add, _) => Flags::Add(l, r, bits),
                    (Mnemonic::Shl | Mnemonic::Sal, Expr::Const(1)) if reads_overflow => {
                        Flags::Add(l.clone(), l, bits)
                    }
                    (Mnemonic::Shr, Expr::Const(1)) if reads_overflow && needed != u32::MAX => {
                        Flags::Unknown
                    }
                    (Mnemonic::Rol | Mnemonic::Ror, _) => self.rotate_flags(mn, &r, &v, bits),
                    (Mnemonic::And | Mnemonic::Or | Mnemonic::Xor, _) => {
                        Flags::Test(v.clone(), v.clone(), bits)
                    }
                    (
                        Mnemonic::Shl | Mnemonic::Sal | Mnemonic::Shr | Mnemonic::Sar,
                        Expr::Const(n),
                    ) if *n >= 1 && *n < u64::from(bits) => {
                        let pos = if matches!(mn, Mnemonic::Shr | Mnemonic::Sar) {
                            *n - 1
                        } else {
                            u64::from(bits) - *n
                        };
                        let out = fold(Op::Shr, l, Expr::Const(pos), bits);
                        Flags::Shift(v.clone(), bits, fold(Op::And, out, Expr::Const(1), bits))
                    }
                    _ => Flags::Result(v.clone(), bits),
                };
                self.write_op0(instr, v);
            }
            Mnemonic::Shld | Mnemonic::Shrd
                if instr.op_count() == 3
                    && !matches!(self.val(instr, 2), Expr::Const(n) if n >= 1 && n < u64::from(bits)) =>
            {
                let mask = if bits == 64 { 0x3f } else { 0x1f };
                let dst = self.val(instr, 0);
                let src = self.val(instr, 1);
                let cnt = fold(Op::And, self.val(instr, 2), Expr::Const(mask), bits);
                let rest = fold(Op::Sub, Expr::Const(u64::from(bits) - 1), cnt.clone(), bits);
                let (near, far) = if mn == Mnemonic::Shld {
                    (Op::Shl, Op::Shr)
                } else {
                    (Op::Shr, Op::Shl)
                };
                let v = fold(
                    Op::Or,
                    fold(near, dst, cnt, bits),
                    fold(far, fold(far, src, Expr::Const(1), bits), rest, bits),
                    bits,
                );
                self.flags = Flags::Result(v.clone(), bits);
                self.write_op0(instr, v);
            }
            Mnemonic::Xorps | Mnemonic::Xorpd | Mnemonic::Pxor | Mnemonic::Pandn
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Register
                    && instr.op1_kind() == OpKind::Register
                    && instr.op0_register() == instr.op1_register() =>
            {
                self.reg_write(instr.op0_register(), Expr::Const(0));
            }
            Mnemonic::Imul if instr.op_count() == 3 => {
                let a = self.val(instr, 1);
                let b = self.val(instr, 2);
                let v = fold(Op::Mul, a.clone(), b.clone(), bits);
                self.flags = Flags::Carry(fold(Op::SMulO(bits), a, b, bits));
                self.write_op0(instr, v);
            }
            Mnemonic::Imul if instr.op_count() == 2 => {
                let a = self.val(instr, 0);
                let b = self.val(instr, 1);
                let v = fold(Op::Mul, a.clone(), b.clone(), bits);
                self.flags = Flags::Carry(fold(Op::SMulO(bits), a, b, bits));
                self.write_op0(instr, v);
            }
            Mnemonic::Imul | Mnemonic::Mul if instr.op_count() == 1 && bits >= 16 => {
                let a = self.reg_read(sized_register(self.rax(), bits));
                let b = self.val(instr, 0);
                let v = fold(Op::Mul, a.clone(), b.clone(), bits);
                let ovf = if mn == Mnemonic::Mul {
                    Op::MulHi(bits)
                } else {
                    Op::SMulO(bits)
                };
                self.flags = Flags::Carry(fold(ovf, a.clone(), b.clone(), bits));
                let high = if mn == Mnemonic::Mul {
                    Op::MulHi(bits)
                } else {
                    Op::SMulHi(bits)
                };
                let hi = fold(high, a, b, bits);
                self.reg_write_all(vec![
                    (sized_register(self.rdx(), bits), hi),
                    (sized_register(self.rax(), bits), v),
                ]);
            }
            Mnemonic::Imul | Mnemonic::Mul if instr.op_count() == 1 && bits == 8 => {
                let a = self.reg_read(sized_register(self.rax(), 8));
                let b = self.val(instr, 0);
                let (wa, wb) = if mn == Mnemonic::Imul {
                    (sign_extend(a.clone(), 8), sign_extend(b.clone(), 8))
                } else {
                    (a.clone(), b.clone())
                };
                let v = fold(Op::Mul, wa, wb, 16);
                let ovf = if mn == Mnemonic::Mul {
                    Op::MulHi(8)
                } else {
                    Op::SMulO(8)
                };
                self.flags = Flags::Carry(fold(ovf, a, b, 8));
                self.reg_write(sized_register(self.rax(), 16), v);
            }
            Mnemonic::Div | Mnemonic::Idiv if instr.op_count() == 1 && bits == 8 => {
                let a = self.reg_read(sized_register(self.rax(), 16));
                let b = self.val(instr, 0);
                let signed = mn == Mnemonic::Idiv;
                let (a, b) = (widen(a, 16, signed), widen(b, 8, signed));
                let (q, r) = if mn == Mnemonic::Div {
                    (Op::Div, Op::Rem)
                } else {
                    (Op::SDiv, Op::SRem)
                };
                let quot = fold(q, a.clone(), b.clone(), 16);
                let rem = fold(r, a, b, 16);
                self.flags = Flags::Unknown;
                self.reg_write_all(vec![
                    (Register::AH, rem),
                    (sized_register(self.rax(), 8), quot),
                ]);
            }
            Mnemonic::Div | Mnemonic::Idiv if instr.op_count() == 1 && bits >= 16 => {
                let Some(spread) = self.dividend_high(mn, bits) else {
                    self.unmodeled(instr);
                    return;
                };
                let a = widen(
                    self.reg_read(sized_register(self.rax(), bits)),
                    bits,
                    spread,
                );
                let b = widen(self.val(instr, 0), bits, mn == Mnemonic::Idiv);
                let (q, r) = if mn == Mnemonic::Div {
                    (Op::Div, Op::Rem)
                } else {
                    (Op::SDiv, Op::SRem)
                };
                let quot = fold(q, a.clone(), b.clone(), bits);
                let rem = fold(r, a, b, bits);
                self.flags = Flags::Unknown;
                self.reg_write_all(vec![
                    (sized_register(self.rdx(), bits), rem),
                    (sized_register(self.rax(), bits), quot),
                ]);
            }
            Mnemonic::Inc | Mnemonic::Dec if instr.op_count() == 1 => {
                let op = if mn == Mnemonic::Inc {
                    Op::Add
                } else {
                    Op::Sub
                };
                let x = self.val(instr, 0);
                let v = fold(op, x.clone(), Expr::Const(1), bits);
                let others = RflagsBits::ZF | RflagsBits::SF | RflagsBits::OF | RflagsBits::PF;
                let needed = self.flags_needed;
                let carry_only = needed & RflagsBits::CF != 0 && needed & others == 0;
                self.flags = if carry_only && self.flags != Flags::Unknown {
                    let before = std::mem::replace(&mut self.flags, Flags::Unknown);
                    Flags::Carry(Expr::Cond(Box::new(Cond {
                        cc: Cc(ConditionCode::b),
                        flags: before,
                    })))
                } else if needed & RflagsBits::OF == 0 {
                    Flags::Result(v.clone(), bits)
                } else if needed & RflagsBits::CF != 0 && needed != u32::MAX {
                    Flags::Unknown
                } else if mn == Mnemonic::Inc {
                    Flags::Add(x, Expr::Const(1), bits)
                } else {
                    Flags::Cmp(x, Expr::Const(1), bits)
                };
                self.write_op0(instr, v);
            }
            Mnemonic::Neg if instr.op_count() == 1 => {
                let src = self.val(instr, 0);
                let v = unary(UnOp::Neg, src.clone(), bits);
                self.flags = Flags::Cmp(Expr::Const(0), src, bits);
                self.write_op0(instr, v);
            }
            Mnemonic::Not if instr.op_count() == 1 => {
                let v = unary(UnOp::Not, self.val(instr, 0), bits);
                self.write_op0(instr, v);
            }
            Mnemonic::Bswap if instr.op_count() == 1 => {
                let v = unary(UnOp::Bswap, self.lane_operand(instr, 0, bits), bits);
                self.write_op0(instr, v);
            }
            Mnemonic::Tzcnt
            | Mnemonic::Lzcnt
            | Mnemonic::Popcnt
            | Mnemonic::Bsf
            | Mnemonic::Bsr
                if instr.op_count() == 2 =>
            {
                let op = match mn {
                    Mnemonic::Tzcnt => UnOp::Tzcnt,
                    Mnemonic::Lzcnt => UnOp::Lzcnt,
                    Mnemonic::Popcnt => UnOp::Popcnt,
                    Mnemonic::Bsf => UnOp::Bsf,
                    _ => UnOp::Bsr,
                };
                let src = self.lane_operand(instr, 1, bits);
                let v = unary(op, src.clone(), bits);
                let counts = matches!(mn, Mnemonic::Tzcnt | Mnemonic::Lzcnt);
                self.flags = if counts && self.flags_needed & !RflagsBits::CF == 0 {
                    Flags::Truth(
                        Expr::Cond(Box::new(Cond {
                            cc: Cc(ConditionCode::e),
                            flags: Flags::Test(src.clone(), src, bits),
                        })),
                        Cc(ConditionCode::b),
                    )
                } else if counts {
                    Flags::Result(v.clone(), bits)
                } else {
                    Flags::Result(src, bits)
                };
                self.write_op0(instr, v);
            }
            Mnemonic::Cmp if instr.op_count() == 2 => {
                let l = self.val(instr, 0);
                let r = self.val(instr, 1);
                self.flags = Flags::Cmp(l, r, bits);
            }
            Mnemonic::Ucomisd
            | Mnemonic::Comisd
            | Mnemonic::Ucomiss
            | Mnemonic::Comiss
            | Mnemonic::Vucomisd
            | Mnemonic::Vcomisd
            | Mnemonic::Vucomiss
            | Mnemonic::Vcomiss
                if instr.op_count() == 2 =>
            {
                let fbits = if matches!(
                    mn,
                    Mnemonic::Ucomisd | Mnemonic::Comisd | Mnemonic::Vucomisd | Mnemonic::Vcomisd
                ) {
                    64
                } else {
                    32
                };
                let ty = if fbits == 64 { Ty::F64 } else { Ty::F32 };
                let l = scalar_lane(self.val(instr, 0), ty);
                let r = scalar_lane(self.val(instr, 1), ty);
                self.flags = Flags::Cmp(l, r, fbits);
            }
            Mnemonic::Cmpxchg if instr.op_count() == 2 && instr.op0_kind() == OpKind::Memory => {
                self.cmpxchg(instr, bits);
            }
            Mnemonic::Xadd
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Memory
                    && instr.op1_kind() == OpKind::Register =>
            {
                self.xadd(instr, bits);
            }
            Mnemonic::Shld | Mnemonic::Shrd
                if instr.op_count() == 3
                    && matches!(self.val(instr, 2), Expr::Const(n) if n >= 1 && n < u64::from(bits)) =>
            {
                let n = match self.val(instr, 2) {
                    Expr::Const(n) => n,
                    _ => 1,
                };
                let a = self.val(instr, 0);
                let b = self.val(instr, 1);
                let rest = Expr::Const(u64::from(bits) - n);
                let (v, out) = if mn == Mnemonic::Shld {
                    (
                        fold(
                            Op::Or,
                            fold(Op::Shl, a.clone(), Expr::Const(n), bits),
                            fold(Op::Shr, b, rest.clone(), bits),
                            bits,
                        ),
                        fold(Op::And, fold(Op::Shr, a, rest, bits), Expr::Const(1), bits),
                    )
                } else {
                    (
                        fold(
                            Op::Or,
                            fold(Op::Shr, a.clone(), Expr::Const(n), bits),
                            fold(Op::Shl, b, rest, bits),
                            bits,
                        ),
                        fold(
                            Op::And,
                            fold(Op::Shr, a, Expr::Const(n - 1), bits),
                            Expr::Const(1),
                            bits,
                        ),
                    )
                };
                self.flags = Flags::Shift(v.clone(), bits, out);
                self.write_op0(instr, v);
            }
            Mnemonic::Rcr | Mnemonic::Rcl
                if instr.op_count() == 2
                    && matches!(self.val(instr, 1), Expr::Const(1))
                    && matches!(
                        self.flags,
                        Flags::Cmp(..)
                            | Flags::Add(..)
                            | Flags::Carry(_)
                            | Flags::Shift(..)
                            | Flags::Truth(_, Cc(ConditionCode::b))
                    ) =>
            {
                let carry = Cond {
                    cc: Cc(ConditionCode::b),
                    flags: self.flags.clone(),
                };
                let cf = match carry.eval() {
                    Some(b) => Expr::Const(u64::from(b)),
                    None => Expr::Cond(Box::new(carry)),
                };
                let x = self.val(instr, 0);
                let top = Expr::Const(u64::from(bits) - 1);
                let (v, out) = if mn == Mnemonic::Rcr {
                    (
                        fold(
                            Op::Or,
                            fold(Op::Shl, cf, top, bits),
                            fold(Op::Shr, x.clone(), Expr::Const(1), bits),
                            bits,
                        ),
                        fold(Op::And, x, Expr::Const(1), bits),
                    )
                } else {
                    (
                        fold(
                            Op::Or,
                            fold(Op::Shl, x.clone(), Expr::Const(1), bits),
                            cf,
                            bits,
                        ),
                        fold(Op::And, fold(Op::Shr, x, top, bits), Expr::Const(1), bits),
                    )
                };
                self.flags = Flags::Truth(out, Cc(ConditionCode::b));
                self.write_op0(instr, v);
            }
            Mnemonic::Adc | Mnemonic::Sbb
                if instr.op_count() == 2
                    && matches!(
                        self.flags,
                        Flags::Cmp(..)
                            | Flags::Add(..)
                            | Flags::Carry(_)
                            | Flags::Shift(..)
                            | Flags::Truth(_, Cc(ConditionCode::b))
                    ) =>
            {
                let carry = Cond {
                    cc: Cc(ConditionCode::b),
                    flags: self.flags.clone(),
                };
                let cf = match carry.eval() {
                    Some(b) => Expr::Const(u64::from(b)),
                    None => Expr::Cond(Box::new(carry)),
                };
                let (op, ovf) = if mn == Mnemonic::Adc {
                    (Op::Add, Op::UAddO(bits))
                } else {
                    (Op::Sub, Op::USubO(bits))
                };
                let l = self.val(instr, 0);
                let r = self.val(instr, 1);
                let sum = fold(op, l.clone(), r.clone(), bits);
                let carry = fold(
                    Op::Or,
                    fold(ovf, l, r, bits),
                    fold(ovf, sum.clone(), cf.clone(), bits),
                    bits,
                );
                let v = fold(op, sum, cf, bits);
                self.flags = Flags::Truth(carry, Cc(ConditionCode::b));
                self.write_op0(instr, v);
            }
            Mnemonic::Test if instr.op_count() == 2 => {
                let l = self.val(instr, 0);
                let r = self.val(instr, 1);
                self.flags = self.status_test(&l, &r).unwrap_or(Flags::Test(l, r, bits));
            }
            Mnemonic::Bt if instr.op_count() == 2 => {
                let (v, n) = match self.bit_string(instr, bits) {
                    Some((addr, n)) => (self.read_at(addr, Self::mem_ty(instr)), n),
                    None => {
                        let n = self.val(instr, 1);
                        let n = fold(Op::And, n, Expr::Const(u64::from(bits - 1)), bits);
                        (self.val(instr, 0), n)
                    }
                };
                let bit = fold(Op::And, fold(Op::Shr, v, n, bits), Expr::Const(1), bits);
                self.flags = Flags::Carry(bit);
            }
            Mnemonic::Bts | Mnemonic::Btr | Mnemonic::Btc
                if instr.op_count() == 2
                    && matches!(instr.op0_kind(), OpKind::Register | OpKind::Memory) =>
            {
                let string = self.bit_string(instr, bits);
                let (v, n) = match &string {
                    Some((addr, n)) => (self.read_at(addr.clone(), Self::mem_ty(instr)), n.clone()),
                    None => {
                        let n = fold(
                            Op::And,
                            self.val(instr, 1),
                            Expr::Const(u64::from(bits - 1)),
                            bits,
                        );
                        (self.val(instr, 0), n)
                    }
                };
                let old = fold(
                    Op::And,
                    fold(Op::Shr, v.clone(), n.clone(), bits),
                    Expr::Const(1),
                    bits,
                );
                let bit = fold(Op::Shl, Expr::Const(1), n, bits);
                let result = match mn {
                    Mnemonic::Bts => fold(Op::Or, v, bit, bits),
                    Mnemonic::Btr => fold(Op::And, v, unary(UnOp::Not, bit, bits), bits),
                    _ => fold(Op::Xor, v, bit, bits),
                };
                self.flags = Flags::Carry(old);
                match string {
                    Some((addr, _)) => self.store_at(addr, Self::mem_ty(instr), result),
                    None => self.write_op0(instr, result),
                }
            }
            Mnemonic::Push if instr.op_count() == 1 => {
                let v = self.val(instr, 0);
                let word = self.ctx.conv.word;
                if let Some(sp) = self.env.sp {
                    let sp = sp - word;
                    self.env.sp = Some(sp);
                    if self.makes_room(&v) {
                        self.env.vals.remove(&Key::Slot(sp));
                        self.env.slot_bits.remove(&sp);
                        self.env.fresh.insert(Key::Slot(sp));
                    } else {
                        if self.seh_registered && !self.is_register_save(sp, self.word_ty(), &v) {
                            self.args_pushed += 1;
                        }
                        self.slot_write(sp, self.word_ty(), v);
                    }
                }
            }
            Mnemonic::Pop if instr.op_count() == 1 => {
                let word = self.ctx.conv.word;
                match self.env.sp {
                    Some(sp) => {
                        let v = self.slot_read(sp, self.word_ty());
                        self.env.sp = Some(sp + word);
                        self.args_pushed = self.args_pushed.saturating_sub(1);
                        self.write_op0(instr, v);
                    }
                    None if instr.op0_kind() == OpKind::Register
                        && self.dead_reg(self.canon(instr.op0_register())) =>
                    {
                        let k = self.canon(instr.op0_register());
                        self.clobber(k);
                    }
                    None => self.unmodeled(instr),
                }
            }
            Mnemonic::Leave => {
                let rbp = if self.bitness() == 32 {
                    Register::EBP
                } else {
                    Register::RBP
                };
                let frame = self.reg_read(rbp);
                self.env.sp = match frame {
                    Expr::Sp(k) => Some(k),
                    _ => None,
                };
                let word = self.ctx.conv.word;
                match self.env.sp {
                    Some(sp) => {
                        let v = self.slot_read(sp, self.word_ty());
                        self.env.sp = Some(sp + word);
                        self.reg_write(rbp, v);
                    }
                    None if self.dead_reg(self.canon(rbp)) => {
                        let k = self.canon(rbp);
                        self.clobber(k);
                    }
                    None => self.unmodeled(instr),
                }
            }
            Mnemonic::Xchg
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Register
                    && instr.op1_kind() == OpKind::Register =>
            {
                let a = self.val(instr, 0);
                let b = self.val(instr, 1);
                self.reg_write_all(vec![(instr.op0_register(), b), (instr.op1_register(), a)]);
            }
            Mnemonic::Xchg
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Memory
                    && instr.op1_kind() == OpKind::Register =>
            {
                let old = self.val(instr, 0);
                let old = self.tmp_if(old, &|_| true);
                let new = self.val(instr, 1);
                self.store(instr, new);
                self.reg_write(instr.op1_register(), old);
            }
            Mnemonic::Cdqe => {
                let v = sign_extend(self.reg_read(Register::EAX), 32);
                self.reg_write(Register::RAX, v);
            }
            Mnemonic::Cwde => {
                let v = sign_extend(self.reg_read(Register::AX), 16);
                self.reg_write(sized_register(self.rax(), 32), v);
            }
            Mnemonic::Cbw => {
                let v = sign_extend(self.reg_read(Register::AL), 8);
                self.reg_write(Register::AX, v);
            }
            Mnemonic::Cdq => {
                let v = fold(
                    Op::Sar,
                    sign_extend(self.reg_read(Register::EAX), 32),
                    Expr::Const(31),
                    64,
                );
                self.reg_write(sized_register(self.rdx(), 32), v);
            }
            Mnemonic::Cqo => {
                let v = fold(Op::Sar, self.reg_read(Register::RAX), Expr::Const(63), 64);
                self.reg_write(Register::RDX, v);
            }
            Mnemonic::Cwd => {
                let v = fold(
                    Op::Sar,
                    sign_extend(self.reg_read(Register::AX), 16),
                    Expr::Const(15),
                    64,
                );
                self.reg_write(Register::DX, v);
            }
            Mnemonic::Stosb | Mnemonic::Stosw | Mnemonic::Stosd | Mnemonic::Stosq => {
                self.string_op(instr, true, bits);
            }
            Mnemonic::Int3 => {
                emit_line!(self, "__debugbreak();".to_owned());
                self.record(EffectKind::Unmodeled);
            }
            Mnemonic::Ud2 => {
                emit_line!(self, "__builtin_trap();".to_owned());
                self.record(EffectKind::Unmodeled);
            }
            Mnemonic::Hlt => {
                emit_line!(self, "__halt();".to_owned());
                self.record(EffectKind::Unmodeled);
            }
            Mnemonic::Int if instr.op_count() == 1 => {
                let n = instr.immediate(0);
                emit_line!(self, format!("__interrupt({n});"));
                self.record(EffectKind::Unmodeled);
            }
            Mnemonic::Cpuid => {
                emit_line!(self, "cpuid();".to_owned());
                self.record(EffectKind::Unmodeled);
                for r in [Register::RAX, Register::RBX, Register::RCX, Register::RDX] {
                    let k = self.canon(r);
                    self.clobber(k);
                }
            }
            Mnemonic::Rdtsc | Mnemonic::Rdtscp => {
                emit_line!(self, format!("{mn:?}();").to_lowercase());
                self.record(EffectKind::Unmodeled);
                for r in [Register::RAX, Register::RDX, Register::RCX] {
                    let k = self.canon(r);
                    self.clobber(k);
                }
            }
            Mnemonic::Xgetbv => {
                let ecx = self.reg_read(Register::ECX);
                self.reg_write(
                    Register::EAX,
                    Expr::Call("xgetbv".to_owned(), vec![ecx.clone()]),
                );
                self.reg_write(Register::EDX, Expr::Call("xgetbv_hi".to_owned(), vec![ecx]));
                self.flags = Flags::Unknown;
            }
            Mnemonic::Syscall => {
                let (mut args, _, values) = self.args_for(None);
                let written = self.before_call(Some(0), false, 0, &values, &[]);
                if Self::reads_any(&values, &written) {
                    args = self.args();
                }
                self.enter_call(false, &[]);
                emit_line!(self, format!("syscall({});", args.join(", ")));
                self.record(EffectKind::Unmodeled);
                self.after_call(false);
            }
            Mnemonic::Ptest | Mnemonic::Vptest
                if instr.op_count() == 2
                    && instr.op0_kind() == OpKind::Register
                    && !instr.op0_register().is_ymm() =>
            {
                let a = self.val(instr, 0);
                let b = self.val(instr, 1);
                self.flags = if self.flags_needed & RflagsBits::CF == 0 {
                    Flags::Test(a, b, 128)
                } else if self.flags_needed & (RflagsBits::ZF | RflagsBits::SF) == 0 {
                    Flags::Truth(
                        Expr::Cond(Box::new(Cond {
                            cc: Cc(ConditionCode::e),
                            flags: Flags::Test(unary(UnOp::Not, a, 128), b, 128),
                        })),
                        Cc(ConditionCode::b),
                    )
                } else {
                    Flags::Unknown
                };
            }
            Mnemonic::Pextrb
            | Mnemonic::Pextrw
            | Mnemonic::Pextrd
            | Mnemonic::Pextrq
            | Mnemonic::Vpextrb
            | Mnemonic::Vpextrw
            | Mnemonic::Vpextrd
            | Mnemonic::Vpextrq
                if instr.op_count() == 3 && instr.op0_kind() == OpKind::Memory =>
            {
                self.vector_op(instr);
            }
            Mnemonic::Fnstsw | Mnemonic::Fstsw
                if instr.op0_kind() == OpKind::Register
                    && instr.op0_register() == Register::AX
                    && self.env.fpu_cmp.is_some() =>
            {
                self.reg_write(
                    Register::AX,
                    Expr::Call("fpu_status".to_owned(), Vec::new()),
                );
                self.status_ah = self
                    .env
                    .fpu_cmp
                    .clone()
                    .map(|(l, r)| (self.reg_read(Register::AH), Flags::Cmp(l, r, 64)));
            }
            Mnemonic::Lahf if self.float_flags && matches!(self.flags, Flags::Cmp(..)) => {
                let saved = self.flags.clone();
                self.reg_write(Register::AH, Expr::Call("lahf".to_owned(), Vec::new()));
                self.status_ah = Some((self.reg_read(Register::AH), saved));
            }
            Mnemonic::Sahf => {
                let ah = self.reg_read(Register::AH);
                self.flags = match (self.status_ah.clone(), self.env.fpu_cmp.clone()) {
                    (Some((held, saved)), _) if held == ah => saved,
                    (_, Some((l, r))) => Flags::Cmp(l, r, 64),
                    (_, None) => Flags::Unknown,
                };
            }
            _ if self.is_vector_op(instr) => self.vector_op(instr),
            _ if instr.condition_code() != ConditionCode::None && instr.op_count() == 1 => {
                self.setcc(instr);
            }
            _ if instr.condition_code() != ConditionCode::None && instr.op_count() == 2 => {
                self.cmovcc(instr, bits);
            }
            _ => self.unmodeled(instr),
        }
    }

    /// Re-expresses `cmp`/`test` flags before a join (see [`Rebase`]).
    ///
    /// [`Rebase::Registers`] writes every register the comparison names out
    /// and lifts the comparison again, so a byte or word operand reads
    /// `rax & 0xff` over the register itself. [`Rebase::Alias`] writes the
    /// aliasing register out and substitutes it for the value the operands
    /// computed. [`Rebase::Truth`] evaluates the join's condition over the
    /// current flags into the shared temporary (`tmp_N = x < y;`) and leaves
    /// flags that say the temporary is that truth. Nothing happens when the
    /// flags are unknown, when a register form has no comparison to relift,
    /// when the alias does not hold a compared value, or when another
    /// operand reads the old alias.
    ///
    /// # Arguments
    ///
    /// * `src` - The comparison that produced the flags, when one did.
    /// * `how` - The agreed form.
    pub(super) fn rebase_flags(&mut self, src: Option<&Instruction>, how: Rebase) {
        if let Rebase::Truth(cc, id) = how {
            if self.flags == Flags::Unknown {
                return;
            }
            let cond = Cond {
                cc,
                flags: std::mem::replace(&mut self.flags, Flags::Unknown),
            };
            let v = match cond.eval() {
                Some(b) => Expr::Const(u64::from(b)),
                None => Expr::Cond(Box::new(cond)),
            };
            let key = Key::Tmp(id);
            self.write_out(key, &v);
            self.flags = Flags::Truth(Expr::Var(key), cc);
            return;
        }
        let Some(src) = src else {
            return;
        };
        if !matches!(self.flags, Flags::Cmp(..) | Flags::Test(..)) {
            return;
        }
        let bitness = self.bitness();
        let regs: Vec<Key> = (0..src.op_count())
            .filter(|&i| src.op_kind(i) == OpKind::Register)
            .map(|i| Key::Reg(canon(src.op_register(i), bitness)))
            .collect();
        let k = match how {
            Rebase::Registers => {
                self.flags = Flags::Unknown;
                for &r in &regs {
                    self.materialize(r, &mut Vec::new(), None);
                }
                self.flags_needed = u32::MAX;
                self.step(src);
                return;
            }
            Rebase::Alias(k) => k,
            Rebase::Truth(..) => return,
        };
        let target = self.env.get(k);
        if !regs.iter().any(|&r| self.env.get(r) == target) {
            return;
        }
        let swap = |from: &Expr, to: &Expr| match &self.flags {
            Flags::Cmp(l, r, b) => Flags::Cmp(l.subst(from, to), r.subst(from, to), *b),
            Flags::Test(l, r, b) => Flags::Test(l.subst(from, to), r.subst(from, to), *b),
            other => other.clone(),
        };
        if swap(&target, &Expr::Const(0)).mentions(k) {
            return;
        }
        let rebased = swap(&target, &Expr::Var(k));
        self.flags = Flags::Unknown;
        self.materialize(k, &mut Vec::new(), None);
        self.flags = rebased;
    }

    /// The word and bit a bit-string instruction (`bt [m], r`, `bts`,
    /// `btr`, `btc`) addresses.
    ///
    /// With a memory base and a register offset the offset is a signed bit
    /// index into the string at the address, not into the operand: the
    /// processor touches the word `offset >> log2(width)` words from the
    /// address, at bit `offset & (width - 1)`, so `bts [esp+0x10], eax` on
    /// a 256-bit character set sets bit `eax & 31` of word `eax >> 5`.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `bits` - Operand width, 16, 32 or 64.
    ///
    /// # Returns
    ///
    /// The word's address and the bit within it, or `None` when the base is
    /// a register or the offset an immediate (which wraps at the width).
    fn bit_string(&mut self, instr: &Instruction, bits: u8) -> Option<(Expr, Expr)> {
        if instr.op0_kind() != OpKind::Memory || instr.op1_kind() != OpKind::Register {
            return None;
        }
        let n = self.val(instr, 1);
        let offset = if bits < 64 {
            sign_extend(n.clone(), bits)
        } else {
            n.clone()
        };
        let word = fold(
            Op::Sar,
            offset,
            Expr::Const(u64::from(bits.trailing_zeros())),
            64,
        );
        let base = self.addr(instr, 0);
        let addr = fold(
            Op::Add,
            base,
            fold(Op::Mul, word, Expr::Const(u64::from(bits / 8)), 64),
            64,
        );
        let bit = fold(Op::And, n, Expr::Const(u64::from(bits - 1)), bits);
        Some((addr, bit))
    }

    /// The flags a rotate leaves.
    ///
    /// `rol` and `ror` write CF (the bit rotated into the far end) and OF,
    /// and leave ZF, SF and PF as they were; a count that masks to zero
    /// changes no flag at all. A reader of the carry alone reads that bit,
    /// one of the untouched flags alone reads the flags from before, and
    /// anything else (a variable count, the overflow) is beyond the thunk.
    ///
    /// # Arguments
    ///
    /// * `mn` - `rol` or `ror`.
    /// * `count` - The rotate count operand.
    /// * `v` - The rotated value.
    /// * `bits` - Operand width.
    fn rotate_flags(&self, mn: Mnemonic, count: &Expr, v: &Expr, bits: u8) -> Flags {
        let count_mask = if bits == 64 { 0x3f } else { 0x1f };
        let needed = self.flags_needed;
        match count {
            Expr::Const(n) if n & count_mask == 0 => self.flags.clone(),
            Expr::Const(_) if needed & !RflagsBits::CF == 0 => {
                let at = if mn == Mnemonic::Rol {
                    0
                } else {
                    u64::from(bits) - 1
                };
                let bit = fold(
                    Op::And,
                    fold(Op::Shr, v.clone(), Expr::Const(at), bits),
                    Expr::Const(1),
                    bits,
                );
                Flags::Carry(bit)
            }
            Expr::Const(_) if needed & (RflagsBits::CF | RflagsBits::OF) == 0 => self.flags.clone(),
            _ => Flags::Unknown,
        }
    }

    /// Reads `test ah, mask` over a floating-point compare's status bits
    /// as the comparison it tests.
    ///
    /// After `ucomisd a, b; lahf` (or `fcom; fnstsw ax`) `ah` holds ZF (C3)
    /// at 0x40, PF (C2) at 0x04 and CF (C0) at 0x01, and the four outcomes
    /// set them as greater 000, less 001, equal 100 and unordered 111. The
    /// jump after the test reads the parity (`jp`) or the zero flag (`je`)
    /// of the masked bits, so it is taken on a set of outcomes; when that
    /// set or its complement is what a C comparison of the operands holds
    /// on (`a != b` on greater, less and unordered, `a < b` on less alone),
    /// the flags are that comparison's truth: `test ah, 0x44; jp` is
    /// `a != b`, `test ah, 5; jnp` is `a < b`. A comparison holding on less
    /// alone (or on less and equal) is the flags' `a` (`ae`) with the
    /// operands swapped, since the flags' `b` (`be`) holds on unordered too.
    ///
    /// # Arguments
    ///
    /// * `l` - One operand of the `test`: the status or the mask
    ///   (`test cl, ah` with `cl` loaded with 0x44).
    /// * `r` - The other.
    ///
    /// # Returns
    ///
    /// The flags, or `None` when `l` is not the status `ah` holds, the
    /// mask reaches other bits, the reader is not one parity or zero test,
    /// or no comparison holds on the set.
    pub(super) fn status_test(&self, l: &Expr, r: &Expr) -> Option<Flags> {
        /// ZF, PF and CF (C3, C2 and C0) in the byte.
        const STATUS: u64 = 0x45;
        /// The byte each outcome leaves, by bit of an outcome set: greater,
        /// less, equal, unordered.
        const OUTCOMES: [u64; 4] = [0x00, 0x01, 0x40, 0x45];
        /// The comparisons, by the outcomes they hold on: the condition
        /// code, whether it reads the operands swapped, and the set.
        const RELATIONS: [(ConditionCode, bool, u8); 6] = [
            (ConditionCode::a, false, 0b0001),
            (ConditionCode::a, true, 0b0010),
            (ConditionCode::e, false, 0b0100),
            (ConditionCode::ae, false, 0b0101),
            (ConditionCode::ae, true, 0b0110),
            (ConditionCode::ne, false, 0b1011),
        ];
        let (held, cmp) = self.status_ah.as_ref()?;
        let mask = match (l, r) {
            (l, &Expr::Const(m)) if l == held => m,
            (&Expr::Const(m), r) if r == held => m,
            _ => return None,
        };
        if mask & 0xff == 0 || mask & !STATUS != 0 {
            return None;
        }
        let parity = self.flags_needed & !RflagsBits::PF == 0;
        if !parity && self.flags_needed & !RflagsBits::ZF != 0 {
            return None;
        }
        let taken = OUTCOMES
            .iter()
            .enumerate()
            .filter(|(_, byte)| {
                let bits = *byte & mask;
                if parity {
                    bits.count_ones() % 2 == 0
                } else {
                    bits == 0
                }
            })
            .fold(0u8, |set, (i, _)| set | (1 << i));
        let reader = Cc(if parity {
            ConditionCode::p
        } else {
            ConditionCode::e
        });
        let (relation, swapped, reader) = RELATIONS.iter().find_map(|&(cc, swapped, set)| {
            if set == taken {
                Some((cc, swapped, reader))
            } else if set == !taken & 0b1111 {
                Some((cc, swapped, reader.invert()))
            } else {
                None
            }
        })?;
        let flags = match cmp {
            Flags::Cmp(l, r, b) if swapped => Flags::Cmp(r.clone(), l.clone(), *b),
            _ if swapped => return None,
            other => other.clone(),
        };
        Some(Flags::Truth(
            Expr::Cond(Box::new(Cond {
                cc: Cc(relation),
                flags,
            })),
            reader,
        ))
    }

    /// Lifts `setcc`: the 0/1 truth value of the current flags.
    ///
    /// Unknown flags leave the instruction unmodeled.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    pub(super) fn setcc(&mut self, instr: &Instruction) {
        if self.flags == Flags::Unknown {
            self.unmodeled(instr);
            return;
        }
        let cond = Cond {
            cc: Cc(instr.condition_code()),
            flags: self.flags.clone(),
        };
        let v = match cond.eval() {
            Some(b) => Expr::Const(u64::from(b)),
            None => Expr::Cond(Box::new(cond)),
        };
        self.write_op0(instr, v);
    }

    /// Lifts `cmovcc` as a ternary over the current flags.
    ///
    /// Unknown flags or a memory destination leave the instruction unmodeled.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `bits` - Operand width (unused; the ternary keeps the operands' shape).
    pub(super) fn cmovcc(&mut self, instr: &Instruction, bits: u8) {
        if self.flags == Flags::Unknown || instr.op0_kind() != OpKind::Register {
            self.unmodeled(instr);
            return;
        }
        let cond = Cond {
            cc: Cc(instr.condition_code()),
            flags: self.flags.clone(),
        };
        let taken = self.val(instr, 1);
        let kept = self.reg_read(instr.op0_register());
        let v = crate::analysis::decompile::expr::ternary(cond, taken, kept);
        let _ = bits;
        self.reg_write(instr.op0_register(), v);
    }

    /// Lifts the string instructions.
    ///
    /// `rep stos*` is `memset`, `rep movs*` is `memcpy`, and the pointers
    /// advance by the byte count; the single forms store or copy one element
    /// and advance by its size. With the direction flag set (`std`, the
    /// idiom of a copy between overlapping buffers) the pointers name the
    /// last element and step back, so the region starts `count - 1` elements
    /// below them and a copy is a `memmove`. Where the direction is not
    /// known the forward form is written under a comment that says so.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `is_stos` - A store (`stos`) rather than a copy (`movs`).
    /// * `bits` - Element width.
    pub(super) fn string_op(&mut self, instr: &Instruction, is_stos: bool, bits: u8) {
        let size = u64::from(bits / 8);
        let rdi = if self.bitness() == 32 {
            Register::EDI
        } else {
            Register::RDI
        };
        let rsi = if self.bitness() == 32 {
            Register::ESI
        } else {
            Register::RSI
        };
        let rcx = if self.bitness() == 32 {
            Register::ECX
        } else {
            Register::RCX
        };
        let mut dst = self.reg_read(rdi);
        let mut src_ptr = self.reg_read(rsi);
        let mut value = self.reg_read(sized_register(self.rax(), bits));
        let mut count = self.reg_read(rcx);
        let ty = Ty::from_bits(bits);
        let backward = self.env.df == Some(true);
        let step = if backward { Op::Sub } else { Op::Add };
        if self.env.df.is_none() {
            emit_line!(
                self,
                "// direction flag unknown here: forward assumed".to_owned()
            );
        }
        if instr.has_rep_prefix() {
            let total = fold(Op::Mul, count.clone(), Expr::Const(size), 64);
            self.settle_frame_region(&dst, Some(&total), backward, true);
            if !is_stos && !backward {
                self.settle_frame_region(&src_ptr, Some(&total), false, false);
            }
            let word = self.word_ty();
            self.protect_memory_around(&mut [
                (&mut dst, word),
                (&mut src_ptr, word),
                (&mut value, ty),
                (&mut count, word),
            ]);
            let n = self.names();
            let total = fold(Op::Mul, count, Expr::Const(size), 64);
            let low = |p: Expr| {
                if !backward {
                    return p;
                }
                match without_addend(&p, &total, 64) {
                    Some(rest) => fold(Op::Add, rest, Expr::Const(size), 64),
                    None => {
                        let end = fold(Op::Add, p, Expr::Const(size), 64);
                        fold(Op::Sub, end, total.clone(), 64)
                    }
                }
            };
            let region = self.emit.then(|| {
                let (routine, element, from) = match (is_stos, backward) {
                    (true, _) => (Routine::Memset, bits, value.clone()),
                    (false, true) => (Routine::Memmove, 8, low(src_ptr.clone())),
                    (false, false) => (Routine::Memcpy, 8, low(src_ptr.clone())),
                };
                let args = vec![
                    (ArgAt::Operand, low(dst.clone())),
                    (ArgAt::Operand, from),
                    (ArgAt::Operand, total.clone()),
                ];
                (Callee::Builtin(routine, element), args)
            });
            let line = if is_stos {
                let byte_value = if bits == 8 {
                    value.render(&n)
                } else {
                    format!("/*{}-bit pattern*/ {}", bits, value.render(&n))
                };
                format!(
                    "memset({}, {byte_value}, {});",
                    low(dst).render(&n),
                    total.render(&n)
                )
            } else {
                format!(
                    "{}({}, {}, {});",
                    if backward { "memmove" } else { "memcpy" },
                    low(dst).render(&n),
                    low(src_ptr).render(&n),
                    total.render(&n)
                )
            };
            emit_line!(self, line);
            if let Some((callee, args)) = region {
                self.record_call(callee, args, None, None, false, Shown::Statement);
            }
            if self.ctx.probe.is_some() {
                let (dst, src) = (low(self.reg_read(rdi)), low(self.reg_read(rsi)));
                if let Some(p) = &mut self.ctx.probe {
                    p.rep(dst, (!is_stos).then_some(src), value, bits, total);
                }
            }
            let advance = fold(Op::Mul, self.reg_read(rcx), Expr::Const(size), 64);
            let new_dst = fold(step, self.reg_read(rdi), advance.clone(), 64);
            self.reg_write(rdi, new_dst);
            if !is_stos {
                let new_src = fold(step, self.reg_read(rsi), advance, 64);
                self.reg_write(rsi, new_src);
            }
            self.reg_write(rcx, Expr::Const(0));
        } else {
            let v = if is_stos {
                value
            } else {
                self.read_at(src_ptr, ty)
            };
            self.store_at(dst, ty, v);
            let new_dst = fold(step, self.reg_read(rdi), Expr::Const(size), 64);
            self.reg_write(rdi, new_dst);
            if !is_stos {
                let new_src = fold(step, self.reg_read(rsi), Expr::Const(size), 64);
                self.reg_write(rsi, new_src);
            }
        }
    }

    /// Tells what rdx holds ahead of a `div` or `idiv` of `bits`.
    ///
    /// # Arguments
    ///
    /// * `mn` - `Div` or `Idiv`.
    /// * `bits` - The divisor's width, 16 or more.
    ///
    /// # Returns
    ///
    /// `Some(false)` for zero (`xor edx, edx`), `Some(true)` for the sign of
    /// rax spread over it (`cwd`, `cdq`, `cqo`, `idiv` only), `None` for
    /// anything else: a real high half, which a 64-bit expression cannot
    /// carry.
    fn dividend_high(&self, mn: Mnemonic, bits: u8) -> Option<bool> {
        let lane = u64::MAX >> (64 - u32::from(bits));
        let hi = match self.reg_read(sized_register(self.rdx(), bits)) {
            Expr::Bin(Op::And, x, m) if matches!(*m, Expr::Const(c) if c & lane == lane) => *x,
            other => other,
        };
        match hi {
            Expr::Const(0) => Some(false),
            Expr::Bin(Op::Sar, _, k)
                if mn == Mnemonic::Idiv && *k == Expr::Const(u64::from(bits) - 1) =>
            {
                Some(true)
            }
            _ => None,
        }
    }

    /// Lifts an instruction without a model: keeps the assembly as a comment
    /// and forgets every register, memory value and flag it may have changed,
    /// and, when it moves the x87 stack's top, which x87 registers are empty.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    pub(super) fn unmodeled(&mut self, instr: &Instruction) {
        let rsp = self.rsp();
        let bitness = self.bitness();
        let (written, sp_written, writes_memory) = {
            let info = self.info.info(instr);
            let mut written: Vec<Key> = Vec::new();
            let mut sp_written = false;
            for ur in info.used_registers() {
                if matches!(
                    ur.access(),
                    OpAccess::Write
                        | OpAccess::CondWrite
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                ) {
                    let r = ur.register();
                    if r == rsp {
                        sp_written = true;
                    } else {
                        written.push(Key::Reg(canon(r, bitness)));
                    }
                }
            }
            let writes_memory = info.used_memory().iter().any(|m| {
                matches!(
                    m.access(),
                    OpAccess::Write
                        | OpAccess::CondWrite
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                )
            });
            (written, sp_written, writes_memory)
        };
        if sp_written {
            self.env.sp = None;
            self.args_pushed = 0;
        }
        if writes_memory {
            if let Some(p) = &mut self.ctx.probe {
                p.asm();
            }
            self.protect_memory();
        }
        if !written.is_empty() || sp_written {
            self.unmodeled += 1;
        }
        if written.contains(&self.canon(self.rax())) {
            self.env.result_in_rax = false;
        }
        for k in &written {
            self.clobber(*k);
        }
        if instr.fpu_stack_increment_info().writes_top() {
            self.forget_empty_x87();
        }
        if instr.rflags_modified() != 0 {
            self.flags = Flags::Unknown;
        }
        if instr.rflags_modified() & RflagsBits::DF != 0 {
            self.env.df = None;
        }
        if self.emit {
            let mut fmt = NasmFormatter::new();
            let mut text = String::new();
            fmt.format(instr, &mut text);
            self.lines.push(format!("/* asm: {text} */"));
            self.record(EffectKind::Unmodeled);
        }
    }

    /// Tells whether `instr` reads canonical register `key` (the result-of-call peephole).
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction after a call.
    /// * `key` - The return register; a `ret` counts as reading it.
    pub(super) fn reads_register(&mut self, instr: &Instruction, key: Key) -> bool {
        let bitness = self.bitness();
        let info = self.info.info(instr);
        info.used_registers().iter().any(|ur| {
            Key::Reg(canon(ur.register(), bitness)) == key
                && matches!(
                    ur.access(),
                    OpAccess::Read
                        | OpAccess::CondRead
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                )
        }) || (matches!(instr.flow_control(), FlowControl::Return) && !self.ctx.unused_result)
    }
}

/// Returns `e` taken at its width: sign-extended from `bits` when `signed`,
/// zero-extended otherwise, unchanged at 64.
///
/// Division is not lane-safe: the low half of `rax / rcx` is not
/// `eax / ecx` when the upper halves hold anything, so a narrower
/// division's operands are widened before the 64-bit operation sees them.
///
/// # Arguments
///
/// * `e` - The operand.
/// * `bits` - Its width.
/// * `signed` - Whether it is read as signed.
fn widen(e: Expr, bits: u8, signed: bool) -> Expr {
    match (bits, signed) {
        (64, _) => e,
        (_, true) => sign_extend(e, bits),
        (_, false) => mask(e, (1u64 << bits) - 1),
    }
}

/// Widens an expression a 64-bit operation reads that a 32-bit one typed:
/// the machine's register holds the zero-extension, so the operation runs
/// over all 64 bits of it.
///
/// # Arguments
///
/// * `e` - The operand as the environment holds it.
fn widen64(e: Expr) -> Expr {
    match &e {
        Expr::Deref(_, ty) | Expr::Cast(_, ty) if ty.bits() == 32 => {
            Expr::Cast(Box::new(e), Ty::U64)
        }
        _ => e,
    }
}
