//! The statements a block's text makes, recorded as values beside its lines.
//!
//! The emission pass writes each statement as a line; the same statement
//! is recorded here as an [`Effect`], with the instruction it came from,
//! so a check can replay what the text says without parsing it back. An
//! effect says what the statement does, not how it renders: a compound
//! assignment is the assignment, a virtual call keeps its receiver among
//! its arguments, and a call the text leaves out or reads in place is
//! recorded as such, so no instruction's part in the text is silent.

use crate::isa::{Instruction, OpKind, Register};

use super::super::expr::{Cond, Expr, Key, Ty};
use super::Exec;

/// One statement the emission pass wrote, as a value.
#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::decompile) struct Effect {
    /// The instruction it came from; what a block writes at its end (the
    /// values a successor needs, its branch) comes from its last.
    pub(in crate::analysis::decompile) at: u64,
    /// What it does.
    pub(in crate::analysis::decompile) kind: EffectKind,
}

/// What a statement does.
#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::decompile) enum EffectKind {
    /// `name = value;`: the variable, the value, and the variable's
    /// declared width in bits, which the value is truncated to.
    Assign(Key, Expr, u8),
    /// `*(T *)addr = value;`: the address, the type stored, the value; a
    /// named global's `g = value;` stores at its constant address.
    Store(Box<(Expr, Ty, Expr)>),
    /// A call, whether the text shows it or not.
    Call(Box<Call>),
    /// `return value;`, or `return;`.
    Return(Option<Expr>),
    /// The block's conditional branch, taken when the condition holds.
    Branch(Cond),
    /// A jump-table dispatch: `switch (index)`.
    Switch(Expr),
    /// A computed jump: `goto *target;`.
    Jump(Expr),
    /// A statement no effect models: an intrinsic, an atomic
    /// read-modify-write, an instruction left as `/* asm */`.
    Unmodeled,
}

/// A call as a value.
#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::decompile) struct Call {
    /// What it calls.
    pub(in crate::analysis::decompile) callee: Callee,
    /// The arguments in order, each with where the callee finds it.
    pub(in crate::analysis::decompile) args: Vec<(ArgAt, Expr)>,
    /// The variable the result is assigned to (`rax = f(...);`), if any.
    pub(in crate::analysis::decompile) result: Option<Key>,
    /// The variable the second result, the one the callee leaves in `rdx`
    /// ([`Function::hands_back_rdx`](crate::analysis::Function::hands_back_rdx)),
    /// is assigned to (`rdx = f__rdx(...);`),
    /// if the call renders it.
    pub(in crate::analysis::decompile) result2: Option<Key>,
    /// The callee does not come back: nothing follows the call.
    pub(in crate::analysis::decompile) noreturn: bool,
    /// How the text shows it.
    pub(in crate::analysis::decompile) shown: Shown,
}

/// What a call calls.
#[derive(Debug, Clone, PartialEq)]
pub(in crate::analysis::decompile) enum Callee {
    /// The function at this entry.
    Direct(u64),
    /// The address this value holds: a register, a pointer in memory, an
    /// import slot's content.
    Through(Expr),
    /// A library routine the text names for an instruction (`memset` for
    /// `rep stos`), with the element width in bits a fill repeats.
    Builtin(Routine, u8),
}

/// A library routine the text names for a string instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::decompile) enum Routine {
    /// `memset(dst, value, bytes)`: `rep stos`.
    Memset,
    /// `memcpy(dst, src, bytes)`: `rep movs` stepping forward.
    Memcpy,
    /// `memmove(dst, src, bytes)`: `rep movs` stepping backward.
    Memmove,
}

/// Where a callee finds an argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::decompile) enum ArgAt {
    /// In this register, canonical.
    Reg(Register),
    /// In the stack word this many bytes above the stack pointer at the
    /// call (or the jump, for a tail call), of which the caller stored
    /// this many bits (`mov [rsp+0x30], di` stores 16).
    Stack(i64, u8),
    /// Nowhere in particular: the operand of a routine the text names for
    /// an instruction.
    Operand,
}

/// How the text shows a call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::decompile) enum Shown {
    /// As a statement: `f(args);` or `name = f(args);`.
    Statement,
    /// As a tail call: `return f(args);`.
    Tail,
    /// Not at all: the callee only returns, leads to a function that only
    /// returns, or builds or tears down the caller's frame, whose effect
    /// the lifter applies in its place.
    Elided,
    /// Read in place: the callee's register loads are lifted where the
    /// call stands, followed by the call it jumps on to, if any.
    InPlace,
}

impl Exec<'_, '_> {
    /// Records what the statement just written does, beside its line, in
    /// the emission pass only.
    ///
    /// # Arguments
    ///
    /// * `kind` - What it does.
    pub(super) fn record(&mut self, kind: EffectKind) {
        if self.emit {
            self.effects.push(Effect { at: self.at, kind });
        }
    }

    /// Records a call, in the emission pass only.
    ///
    /// # Arguments
    ///
    /// * `callee` - What it calls.
    /// * `args` - Its arguments, each with where the callee finds it.
    /// * `result` - The variable its result is assigned to.
    /// * `result2` - The variable its second result, in `rdx`, is assigned
    ///   to.
    /// * `noreturn` - Nothing follows it.
    /// * `shown` - How the text shows it.
    pub(super) fn record_call(
        &mut self,
        callee: Callee,
        args: Vec<(ArgAt, Expr)>,
        result: Option<Key>,
        result2: Option<Key>,
        noreturn: bool,
        shown: Shown,
    ) {
        self.record(EffectKind::Call(Box::new(Call {
            callee,
            args,
            result,
            result2,
            noreturn,
            shown,
        })));
    }

    /// The address a call or jump through a register or memory goes to,
    /// as the text reads it at the instruction.
    ///
    /// The value is read as the rendering reads it (a pending store to the
    /// slot, a named global for a data address) but records nothing: no
    /// slot read, no global declared.
    ///
    /// # Arguments
    ///
    /// * `instr` - The call or jump.
    pub(super) fn call_target(&self, instr: &Instruction) -> Expr {
        match instr.op0_kind() {
            OpKind::Register => self.reg_read(instr.op0_register()),
            OpKind::Memory => {
                let ty = Self::mem_ty(instr);
                match self.addr(instr, 0) {
                    Expr::Sp(k) if self.env.slot_bits.get(&k) == Some(&ty.bits()) => {
                        self.assumed(self.env.get(Key::Slot(k)))
                    }
                    Expr::Const(a) if self.is_data(a) => Expr::Var(Key::Global(a, ty.bits())),
                    a => self.assumed(Expr::deref(a, ty)),
                }
            }
            _ => Expr::Const(instr.near_branch_target()),
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use crate::isa::Register;

    use super::{ArgAt, Callee, EffectKind, Shown};
    use crate::analysis::decompile::decompile_plain_full;
    use crate::analysis::decompile::expr::Expr;
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// The kind of an effect, as a word, for comparing lists of them.
    ///
    /// # Arguments
    ///
    /// * `kind` - The effect's kind.
    fn word(kind: &EffectKind) -> &'static str {
        match kind {
            EffectKind::Assign(..) => "assign",
            EffectKind::Store(..) => "store",
            EffectKind::Call(..) => "call",
            EffectKind::Return(..) => "return",
            EffectKind::Branch(..) => "branch",
            EffectKind::Switch(..) => "switch",
            EffectKind::Jump(..) => "jump",
            EffectKind::Unmodeled => "unmodeled",
        }
    }

    /// Every statement a block's text makes is recorded beside it.
    ///
    /// In the text's order, with the instruction it came from: a store and
    /// then the branch that ends its block, each return with its value, and
    /// a call with its argument where the callee finds it.
    #[test]
    fn each_statement_the_text_makes_is_recorded() {
        let p = Program::raw_x64(&[
            0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
            0x83, 0xc2, 0x01, // ASM: add edx, 1
            0x83, 0xfa, 0x05, // ASM: cmp edx, 5
            0x7c, 0x03, // ASM: jl 0x100e
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let f = a.function(0x1000).expect("function");
        let d = decompile_plain_full(&p, &a, &Overlay::default(), 0x1000).expect("decompiles");
        let blocks: Vec<Vec<(u64, &str)>> = f
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let effects = d.effects.block(i, b.start).expect("block");
                effects.iter().map(|e| (e.at, word(&e.kind))).collect()
            })
            .collect();
        assert_eq!(
            blocks,
            [
                vec![(0x1000, "store"), (0x1009, "branch")],
                vec![(0x100d, "return")],
                vec![(0x1013, "return")],
            ]
        );
        let returned: Vec<EffectKind> = f
            .blocks
            .iter()
            .enumerate()
            .skip(1)
            .flat_map(|(i, b)| d.effects.block(i, b.start).expect("block"))
            .map(|e| e.kind)
            .collect();
        assert_eq!(
            returned,
            [
                EffectKind::Return(Some(Expr::Const(0))),
                EffectKind::Return(Some(Expr::Const(1)))
            ]
        );

        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
            0xe8, 0x12, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ];
        code.resize(0x20, 0xcc);
        code.extend([
            0x8d, 0x41, 0x01, // ASM: lea eax, [rcx+1]
            0xc3, // ASM: ret
        ]);
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let d = decompile_plain_full(&p, &a, &Overlay::default(), 0x1000).expect("decompiles");
        let first = d.effects.block(0, 0x1000).expect("block");
        let calls: Vec<_> = first
            .iter()
            .filter_map(|e| match &e.kind {
                EffectKind::Call(c) => Some((e.at, c.callee.clone(), c.args.clone(), c.shown)),
                _ => None,
            })
            .collect();
        assert_eq!(
            calls,
            [(
                0x1009,
                Callee::Direct(0x1020),
                vec![(ArgAt::Reg(Register::RCX), Expr::Const(7))],
                Shown::Statement
            )],
            "{first:?}"
        );
    }
}
