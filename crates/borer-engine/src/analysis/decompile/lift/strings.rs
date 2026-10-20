//! The string instructions: `stos` and `movs`, repeated as `memset`,
//! `memcpy` and `memmove`, and `repe cmpsb` as `memcmp` or `strcmp`.

use super::*;

impl Exec<'_, '_> {
    /// Lifts `repe cmpsb` as the `memcmp` or `strcmp` it compiles from.
    ///
    /// `repe cmpsb` compares the bytes at `rsi` and `rdi` forward while they
    /// agree, at most `rcx` of them, and leaves the flags of the last pair
    /// compared: zero exactly when all agreed, which is `memcmp`'s answer
    /// being zero. A count set to a constant (a compiler expanding a
    /// compare with a literal) becomes `t = memcmp(rsi, rdi, n);` with the
    /// zero flag `t`'s: an equality test of the flags reads as one of `t`.
    /// The other flags are those of one byte's subtraction, which no test
    /// of `t` spells, so any other test is left undecided. With `rdi` a
    /// literal of `n - 1`
    /// characters the compare stops at the literal's end where `strcmp`
    /// does, and reads as `strcmp(rsi, literal)`. The pointers and the
    /// count are left wherever the compare stopped, which nothing models.
    ///
    /// # Arguments
    ///
    /// * `count` - The constant count ([`Exec::string_count`]).
    pub(super) fn compare_strings(&mut self, count: u64) {
        let (rsi, rdi, rcx) = self.string_registers();
        let (a, b) = (self.reg_read(rsi), self.reg_read(rdi));
        let literal = |e: &Expr| match e {
            Expr::Const(at) => crate::strings::cstr_at(self.ctx.program, *at, 0, 1)
                .is_some_and(|(len, _)| crate::num::from_usize(len) + 1 == count),
            Expr::Str(quoted) => {
                use crate::analysis::decompile::ctext::{Tok, tokens};
                matches!(tokens(quoted).as_deref(), Ok([Tok::Str(bytes)])
                    if crate::num::from_usize(bytes.len()) == count
                        && bytes.iter().position(|b| *b == 0) == bytes.len().checked_sub(1))
            }
            _ => false,
        };
        let strcmp = literal(&b);
        let t = self.fresh_tmp(Ty::U32);
        let n = self.names();
        let line = if strcmp {
            format!("{} = strcmp({}, {});", n.key(t), a.render(&n), b.render(&n))
        } else {
            format!(
                "{} = memcmp({}, {}, {});",
                n.key(t),
                a.render(&n),
                b.render(&n),
                crate::analysis::decompile::expr::render_const(count, true)
            )
        };
        emit_line!(self, line);
        self.record(EffectKind::Unmodeled);
        for r in [rsi, rdi, rcx] {
            let k = self.canon(r);
            self.clobber(k);
        }
        self.flags = Flags::Truth(Expr::Var(t), Cc(ConditionCode::ne));
    }

    /// The count a repeated string instruction runs for, when a nonzero
    /// constant gives it; a count of zero runs nothing and changes no flag.
    pub(super) fn string_count(&self) -> Option<u64> {
        match self.reg_read(self.string_registers().2) {
            Expr::Const(c) if c != 0 => Some(c),
            _ => None,
        }
    }

    /// The source, destination and count registers of a string
    /// instruction at the function's width: `rsi`, `rdi` and `rcx`.
    fn string_registers(&self) -> (Register, Register, Register) {
        if self.bitness() == 32 {
            (Register::ESI, Register::EDI, Register::ECX)
        } else {
            (Register::RSI, Register::RDI, Register::RCX)
        }
    }

    /// Steps a string instruction's pointers past what it read and wrote:
    /// the destination, and the source unless it stored.
    ///
    /// # Arguments
    ///
    /// * `step` - `Add` forward, `Sub` with the direction flag set.
    /// * `by` - The bytes to step.
    /// * `is_stos` - A store, which has no source.
    fn advance_strings(&mut self, step: Op, by: &Expr, is_stos: bool) {
        let (rsi, rdi, _) = self.string_registers();
        let new_dst = fold(step, self.reg_read(rdi), by.clone(), 64);
        self.reg_write(rdi, new_dst);
        if !is_stos {
            let new_src = fold(step, self.reg_read(rsi), by.clone(), 64);
            self.reg_write(rsi, new_src);
        }
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
        let (rsi, rdi, rcx) = self.string_registers();
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
            self.advance_strings(step, &advance, is_stos);
            self.reg_write(rcx, Expr::Const(0));
        } else {
            let v = if is_stos {
                value
            } else {
                self.read_at(src_ptr, ty)
            };
            self.store_at(dst, ty, v);
            self.advance_strings(step, &Expr::Const(size), is_stos);
        }
    }
}
