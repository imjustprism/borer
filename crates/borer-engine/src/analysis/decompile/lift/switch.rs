//! Jump-table dispatch: where an indirect jump through a table goes, and
//! the index the switch it ends reads.

use super::*;

impl Exec<'_, '_> {
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
    /// A compared register the block rewrote before the jump holds the
    /// byte its byte table gave (`cmp eax, 0x52; ja D; cdqe; movzx eax,
    /// byte [r9+rax+B]`), and the index is read off that byte's address
    /// ([`Exec::byte_table_index`]), as the case labels number it.
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
        let compared = match instrs.iter().rposition(is_register_cmp) {
            Some(at) => instrs
                .get(at)
                .map(|i| (i.op0_register(), instrs.get(at + 1..).unwrap_or(&[]))),
            None => prev.and_then(last_cmp_register).map(|r| (r, instrs)),
        };
        if let Some((reg, after)) = compared {
            let value = self.reg_read(reg);
            let key = Key::Reg(canon(reg, self.bitness()));
            if after.iter().any(|i| self.rewrites(i, key)) {
                return Some(self.byte_table_index(value, jmp, instrs));
            }
            return Some(value);
        }
        target
    }

    /// Tells whether an instruction writes canonical register `key` in any
    /// lane.
    ///
    /// # Arguments
    ///
    /// * `instr` - The instruction.
    /// * `key` - The register.
    fn rewrites(&mut self, instr: &Instruction, key: Key) -> bool {
        let bitness = self.bitness();
        self.info.info(instr).used_registers().iter().any(|ur| {
            Key::Reg(canon(ur.register(), bitness)) == key
                && matches!(
                    ur.access(),
                    OpAccess::Write | OpAccess::ReadWrite | OpAccess::ReadCondWrite
                )
        })
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
        let parts = match addr.as_ref() {
            Expr::Bin(Op::Add, l, r) => match (l.as_ref(), r.as_ref()) {
                (Expr::Const(c), other) | (other, Expr::Const(c)) => Some((*c, other)),
                _ => None,
            },
            _ => None,
        };
        match (base, parts) {
            (Some(base), Some((c, other))) => fold(
                Op::Add,
                other.clone(),
                Expr::Const(c.wrapping_sub(base)),
                64,
            ),
            (Some(base), None) => fold(
                Op::Add,
                (**addr).clone(),
                Expr::Const(base.wrapping_neg()),
                64,
            ),
            (None, Some((_, other))) => other.clone(),
            (None, None) => idx,
        }
    }
}
